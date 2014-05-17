		関数的ストリームの tail を取る方法

つまり、関数的成功／失敗継続ストリームの最初の数要素を、最初に普通のCons/Nilストリームに変換せずに取得する方法である。
後者の変換は信用ならない ― 正格なモナドに対するモナディックな関数的ストリームについては発散するからだ。
以下のテクニックは後者の場合でも動作する。

> {-# LANGUAGE Rank2Types #-}
> module Streams where
> import Control.Monad.Identity

（無限になる可能性のある）ストリームを表す最も一般的な方法は、以下の「再帰的」型のデータ構造として表す方法だ。

> data Stream a = Nil | Cons a (() -> Stream a)

定義が正格な言語にも当てはまるように、サンク (thunking) は明示されている。
ストリームを純粋関数的に表現することもできる。以下は再帰的で「ない」が、ランク2の型である。

> newtype FStream a = SFK (forall ans. SK a ans -> FK ans -> ans)
> type FK ans = () -> ans            -- 失敗継続
> type SK a ans = a -> FK ans -> ans -- 成功継続
> unSFK (SFK a) = a

newtype のタグを無視すると（Haskell で適切に任意ランク型を扱う必要があるが）、FStream は2つの継続、成功継続と失敗継続の関数となる。
後者はストリームが要素を持たない際に呼び出される。
一要素以上持っている際にストリームは成功継続を呼び出す。
継続はその要素とほかの失敗継続を受け取って、更なる要素を求める。

明らかに、二つの表現の間には対応がある。たとえば：

> fstream_to_stream fstream = unSFK fstream sk fk
>    where fk () = Nil
>	   sk a fk' = Cons a fk'
>
> stream_to_fstream Nil = SFK( \sk fk -> fk () )
> stream_to_fstream (Cons a rest) = 
>     SFK(\sk fk ->
>           sk a (\ () -> unSFK (stream_to_fstream (rest ())) sk fk))

テスト用のストリーム

> s1  = Cons 'a' (\ () -> Cons 'b' (\ () -> Cons 'c' (\ () -> Nil)))
> f1  = stream_to_fstream s1
> s1' = fstream_to_stream f1
>
> test1 = unSFK f1 (\a k -> a:(k())) (\() -> [])

	*Streams> test1
	"abc"

Mitch Wand と D.Vaillancourt (ICFP'04 を見よ) はより形式的に対応を説明している。

とはいえ、二つの表現の間には明らかな違いがある。
Stream の初めの2要素は容易に求められる:

> stream_take:: Int -> Stream a -> [a]
> stream_take 0 _ = []
> stream_take n (Cons a r) = a : (stream_take (n-1) $ r ())

FStream を最初に全部 Stream に変換せずに最初の2要素を求めるのはほとんど不可能に見える。
この変換は、モナディックな関数的ストリームを持っている場合、扱いにくい。

> newtype MFStream m a = MSFK (forall ans. MSK m a ans -> MFK m ans -> m ans)
> type MFK m ans = m ans                     -- failure continuation
> type MSK m a ans = a -> MFK m ans -> m ans -- success continuation
> unMSFK (MSFK a) = a
>
>
> mfstream_to_stream:: (Monad m) => MFStream m a -> m (Stream a)
> mfstream_to_stream mfstream = unMSFK mfstream sk fk
>    where fk = return Nil
>	   sk a fk' = fk' >>= (\rest -> return (Cons a (\ () -> rest)))

もし m が正格なモナドで fstream が無限であったら、Stream への変換は発散する。実際、

> nats = nats' 0 where
>   nats' n = MSFK (\sk fk -> sk n (unMSFK (nats' (n+1)) sk fk))
>
> test2 = runIdentity (mfstream_to_stream nats >>= (return . stream_take 5))

  *Streams> test2
  [0,1,2,3,4]

しかし IO のような正格なモナドだと：

> test3 = mfstream_to_stream nats >>= (print . stream_take 5)

何も表示せずに発散する。
実は、nats の最初の要素を表示する前に、ストリームをすっかりすべて変換しなければならないのだ。

fstream をただのデータ構造であるかのように分割できると分かった。
以下の関数は1要素以上を持つ FStream を返す。
得られるのは、元のストリームの先頭と「残りのストリーム」のペアだ。

> split_fstream :: FStream a -> FStream (a, FStream a)
> split_fstream fstream = unSFK fstream ssk caseB 
>  where caseB () = SFK(\a b -> b ())
>        ssk v fk = SFK(\a b -> 
> 		      a (v, (SFK (\s' f' -> 
> 				  unSFK (fk ())
>				  (\ (v'',x) _ -> s' v'' 
>				   (\ () -> unSFK x s' f'))
>				  f')))
>		        (\ () -> b ()))
>
> f11 = split_fstream f1
> e1  = unSFK f11 (\ (a,_) _ -> a)  undefined
> f1r = unSFK f11 (\ (_,r) _ -> r)  undefined
> f1rs = split_fstream f1r
> e2   = unSFK f1rs (\ (a,_) _ -> a)  undefined

実際、無限ストリーム f1 の最初の二要素を取り出せるのだ。

	*Streams> e1
	'a'
	*Streams> e2
	'b'

モナディックな例（Chung-chieh Shan, Amr A. Sabry, Daniel P. Friedman の論文からほとんどそのまま引用した）

> split_mfstream :: Monad m => MFStream m a -> m (MFStream m (a, MFStream m a))
> split_mfstream m = unMSFK m ssk caseB
>  where caseB =    return $ MSFK(\a b -> b)
>        ssk v fk = return $ MSFK(\a b -> 
> 		      a (v, (MSFK (\s' f' -> 
> 				  fk >>= (\r -> unMSFK r
>				  (\ (v'',x) _ -> s' v'' (unMSFK x s' f'))
>				  f'))))
>		        b)


> mfstream_take:: Monad m => Int -> MFStream m a -> m [a]
> mfstream_take 0 _ = return []
> mfstream_take n m = do
>                     m' <- split_mfstream m
>                     (v,rs) <- unMSFK m' (\ (v,rs) _ -> return (v,rs) )
>                               undefined
>                     rl <- mfstream_take (n-1) rs
>                     return (v:rl)

> test2' = runIdentity (mfstream_take 5 nats)

	*Streams> test2'
	[0,1,2,3,4]


> test3' = mfstream_take 5 nats >>= print

しかし今やこの場合も

	*Streams> test3'
	[0,1,2,3,4]

