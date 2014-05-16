		How to take a TAIL of a functional stream

Or how to obtain the first few elements of a functional (success/failure
continuation stream) without first converting it to the regular
Cons/Nil stream. The latter conversion is unreliable: it diverges for
a monadic functional stream over a strict monad. Our technique works
even in the latter case.


$Id: car-fstream.lhs,v 1.3 2012/04/04 03:40:11 oleg Exp oleg $

> {-# LANGUAGE Rank2Types #-}
> module Streams where
> import Control.Monad.Identity

The most common way to represent (a potentially infinite) stream is as
a data structure of the following _recursive_ type:

> data Stream a = Nil | Cons a (() -> Stream a)

The thunking is explicit so the definition applies to strict
languages too. We can also represent a stream pure functionally.
The following is _not_ a recursive type, but a higher-ranked one.

> newtype FStream a = SFK (forall ans. SK a ans -> FK ans -> ans)
> type FK ans = () -> ans            -- failure continuation
> type SK a ans = a -> FK ans -> ans -- success continuation
> unSFK (SFK a) = a

If we ignore the newtype tagging (needed to properly deal with the
higher-ranked types in Haskell), an FStream is a function of two
continuations, success and failure continuations. The latter is
invoked if the stream has no elements. The stream invokes the success
continuation if the stream has at least one element. The continuation
receives that element and another failure continuation, to ask for
more elements. As an example of such a functional stream, see Ralf
Hinze's ``Deriving Backtracking Monad Transformers'' (ICFP'00).


Obviously there is a correspondence between the two
representations. For example:

> fstream_to_stream fstream = unSFK fstream sk fk
>    where fk () = Nil
>	   sk a fk' = Cons a fk'
>
> stream_to_fstream Nil = SFK( \sk fk -> fk () )
> stream_to_fstream (Cons a rest) = 
>     SFK(\sk fk ->
>           sk a (\ () -> unSFK (stream_to_fstream (rest ())) sk fk))

A test data stream

> s1  = Cons 'a' (\ () -> Cons 'b' (\ () -> Cons 'c' (\ () -> Nil)))
> f1  = stream_to_fstream s1
> s1' = fstream_to_stream f1
>
> test1 = unSFK f1 (\a k -> a:(k())) (\() -> [])

	*Streams> test1
	"abc"

Mitch Wand and D.Vaillancourt (see ICFP'04) have described the
correspondence in more formal terms.

There is an obvious difference between the two representations
however. It is easy to find the first two elements of a Stream:

> stream_take:: Int -> Stream a -> [a]
> stream_take 0 _ = []
> stream_take n (Cons a r) = a : (stream_take (n-1) $ r ())


It seems all but impossible to find the first two elements of an
FStream without first converting it all to Stream. That conversion
becomes problematic if we had a monadic functional stream:

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

if m is a strict monad and fstream is infinite, the conversion to Stream
diverges. Indeed,

> nats = nats' 0 where
>   nats' n = MSFK (\sk fk -> sk n (unMSFK (nats' (n+1)) sk fk))
>
> test2 = runIdentity (mfstream_to_stream nats >>= (return . stream_take 5))

  *Streams> test2
  [0,1,2,3,4]

but for a strict monad like IO:

> test3 = mfstream_to_stream nats >>= (print . stream_take 5)

it diverges without printing anything. Indeed, before we can print
even the first element from nats, we must convert it entirely to a
stream.


It turns out, we can split fstream as if it were just a data
structure. The following function returns an FStream of at most one item.
The item is a pair of the head of the original stream and of the 
_rest stream_

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

Indeed, we can obtain the first two elements from the finite stream f1

	*Streams> e1
	'a'
	*Streams> e2
	'b'

Monadic case (quoted almost directly from the paper with Chung-chieh Shan, 
Amr A. Sabry, Daniel P. Friedman)

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

But now also

	*Streams> test3'
	[0,1,2,3,4]



