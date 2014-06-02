{-# LANGUAGE PatternGuards #-}

-- ジッパーがいかなるトラヴァーサブルからも導き出せるということを実証する。
-- Haskell-Cafe, 2009/3/31

-- 私は Data.Map をジッパーに変えるトラヴァーサブルのデータ構造の例として使う。
-- Data.Map はとても豊かなインターフェイスを持っていて、ジッパーなんて要らないから、少し奇妙ではある。
-- しかし、Data.Map は標準ライブラリで定義されたトラヴァーサブルのインスタンスのうち唯一非自明なものなのだ。

module ZipperTraversable where

import qualified Data.Traversable as T
import qualified Data.Map as M


-- 変数 Z a k において、a は現在の注目している値である。
-- (k Nothing) を評価すると次に進み、
-- (k v) を評価すると現在の値を v で置き換えて次に進む。

data Zipper t a = ZDone (t a)
                | Z a (Maybe a -> Zipper t a)

make_zipper :: T.Traversable t => t a -> Zipper t a
make_zipper t = reset $ T.mapM f t >>= return . ZDone
 where
 f a = shift (\k -> return $ Z a (k . maybe a id))

-- 全ての道筋をジップして、走査したデータ構造を返す。
zip_up :: Zipper t a -> t a
zip_up (ZDone t) = t
zip_up (Z _ k)   = zip_up $ k Nothing



-- テスト

-- サンプルのコレクション

tmap = M.fromList [ (v,product [1..v]) | v <- [1..10] ]

-- extract a few sample elements from the collection
trav t =
    let (Z a1 k1) = make_zipper t
        (Z a2 k2) = k1 Nothing
        (Z a3 k3) = k2 Nothing
        (Z a4 k4) = k3 Nothing
     in [a1,a3,a4]

travm = trav tmap

-- Traverse and possibly modify elements of a collection
tmod t = loop (make_zipper t)
 where
 loop (ZDone t) = putStrLn $ "Done\n: " ++ show t
 loop (Z a k) = do
                putStrLn $ "Current element: " ++ show a
                ask k

 ask k =        do
                putStrLn "Enter Return, q or the replacement value: "
                getLine >>= check k

 check k ""   = loop $ k Nothing
 check k "\r" = loop $ k Nothing
 check k ('q':_) = loop . ZDone . zip_up $ k Nothing
 check k s  | [(n,_)] <- reads s = loop $ k (Just n) -- replace
 check k _    = putStrLn "Repeat" >> ask k

testm = tmod tmap


-- The Cont monad for delimited continuations, implemented here to avoid
-- importing conflicting monad transformer libraries

newtype Cont r a = Cont{runCont :: (a -> r) -> r}

instance Monad (Cont r) where
    return x = Cont $ \k -> k x
    m >>= f  = Cont $ \k -> runCont m (\v -> runCont (f v) k)

-- Two delimited control operators,
-- without answer-type polymorphism or modification
-- These features are not needed for the application at hand

reset :: Cont r r -> r
reset m = runCont m id

shift :: ((a -> r) -> Cont r r) -> Cont r a
shift e = Cont (\k -> reset (e k))
