{-# LANGUAGE Rank2Types #-}

-- The illustration of the Boehm-Berarducci encoding

-- We re-write an Algebraic Data Type example in BB_ADT.hs
-- using Boehm-Berarducci encoding to represent the
-- data type with lambda-terms.

-- Boehm-Berarducci encoding represents an inductive data type
-- as a non-recursive but higher-rank data type

module BB_LAM where

import BB_ADT (Exp(..))


-- We define the Boehm-Berarducci encoding of the data type
-- Exp from BB_ADT.hs in two steps.

-- First we clarify the signature of the Exp algebra: the
-- types of the algebra constructors. We represent the signature
-- as a Haskell record. It is NOT recursive.

data ExpDict a = ExpDict{ dlit :: Int -> a,
			  dneg :: a   -> a,
			  dadd :: a -> a -> a }

-- We can define (a version of) Boehm-Berarducci encoding as
type ExpBB1 = forall a. (ExpDict a -> a)


-- To use only applications and abstractions, we curry the record
-- argument ExpDict a.
-- The wrapper newtype is needed for the first-class polymorphism
-- (actually we can go some way without newtype wrapper but eventually
-- GHC becomes confused. After all, the source language of GHC is not
-- system F.)
newtype ExpBB 
    = ExpBB{unExpBB :: forall a. ((Int -> a) -> (a -> a) -> (a -> a -> a) -> a)}

-- A data type declaration defines type, constructors, deconstructors
-- and the induction principle (fold). We already have a new type ExpBB,
-- which represents fold, as will become clear soon. We need constructors:

lit :: Int -> ExpBB
lit x = ExpBB $ \dlit dneg dadd -> dlit x

neg :: ExpBB -> ExpBB
neg e = ExpBB $ \dlit dneg dadd -> dneg (unExpBB e dlit dneg dadd)

add :: ExpBB -> ExpBB -> ExpBB
add e1 e2 = ExpBB $ \dlit dneg dadd -> 
 dadd (unExpBB e1 dlit dneg dadd) (unExpBB e2 dlit dneg dadd)

-- A sample expression: our first running example
tbb1 = add (lit 8) (neg (add (lit 1) (lit 2)))

-- A sample consumer
-- viewBB: can be implemented simply via the induction principle
-- It is not recursive!
viewBB:: ExpBB -> String
viewBB e = unExpBB e dlit dneg dadd
 where
 dlit n = show n
 dneg e = "(-" ++ e ++ ")"
 dadd e1 e2 = "(" ++ e1 ++ " + " ++ e2 ++ ")"

tbb1v = viewBB tbb1
-- "(8 + (-(1 + 2)))"


-- How to define a deconstructor?

-- To give an intuition, we define the following functions roll and unroll.
-- The names meant to invoke terms witnessing the isomorphism between an 
-- iso-recursive type and its one-step unrolling.
-- The deconstructor will use a form of these functions.

{- The following shows that we can replace type-level induction
   (in BB_ADT.Exp) with a term-level induction.

  The following definitions of roll and unroll are actually present
  in Boehm-Berarducci's paper -- but in a very indirect way.

  The crucial part is Defn 7.1: sort of self-interpreter: v cons nil ~= v
  Informally, it shows that roll . unroll should be equivalent to the
  identity. The equivalence relation (~=) is strictly speaking not
  the equality; in modern terms, (~=) is contextual equivalence.
-}

-- First we re-write the signature of the Exp algebra, ExpDic,
-- in the form of a strictly-positive functor

data ExpF a = FLit Int 
	    | FNeg a
	    | FAdd a a

instance Functor ExpF where
    fmap f (FLit n) = FLit n
    fmap f (FNeg e) = FNeg (f e)
    fmap f (FAdd e1 e2) = FAdd (f e1) (f e2)

roll :: ExpF ExpBB -> ExpBB
roll (FLit n) = lit n
roll (FNeg e) = neg e
roll (FAdd e1 e2) = add e1 e2

-- The occurrence of roll below is the source of major inefficiency
-- as we do repeated pattern-matching.

unroll :: ExpBB -> ExpF ExpBB
unroll e = unExpBB e dlit dneg dadd
 where
 dlit :: Int -> ExpF ExpBB
 dlit n = FLit n
 dneg :: ExpF ExpBB -> ExpF ExpBB
 dneg e = FNeg (roll e)
 dadd :: ExpF ExpBB -> ExpF ExpBB -> ExpF ExpBB
 dadd e1 e2 = FAdd (roll e1) (roll e2)

-- Compare with the signature for ExpBB!
-- Informally, ExpBB unfolds all the way whereas ExpD unfolds only one step
newtype ExpD = 
 ExpD{unED :: 
      forall w. (Int -> w) -> (ExpBB -> w) -> (ExpBB -> ExpBB -> w) -> w}

decon :: ExpBB -> ExpD
decon e = unExpBB e dlit dneg dadd
 where
 dlit n = ExpD $ \onlit onneg onadd -> onlit n
 dneg e = ExpD $ \onlit onneg onadd -> onneg (unED e lit neg add)
 dadd e1 e2 = ExpD $ \onlit onneg onadd -> 
	      onadd (unED e1 lit neg add) (unED e2 lit neg add)


-- We redo viewBB, using pattern-matching this time, and recursion

viewBBd:: ExpBB -> String
viewBBd e = unED (decon e) dlit dneg dadd
 where
 dlit n = show n
 dneg e = "(-" ++ viewBBd e ++ ")"
 dadd e1 e2 = "(" ++ viewBBd e1 ++ " + " ++ viewBBd e2 ++ ")"

tbb1vd = viewBBd tbb1
-- "(8 + (-(1 + 2)))"

-- So, we can do any pattern-matching!
-- And do non-structurally--recursive processing on ExpBB

{-
push_neg :: Exp -> Exp
push_neg e@Lit{} = e
push_neg e@(Neg (Lit _)) = e
push_neg (Neg (Neg e)) = push_neg e
push_neg (Neg (Add e1 e2)) = Add (push_neg (Neg e1)) (push_neg (Neg e2))
push_neg (Add e1 e2) = Add (push_neg e1) (push_neg e2)
-}

push_negBB :: ExpBB -> ExpBB
push_negBB e = unED (decon e) dlit dneg dadd
 where
 dlit _ = e
 dneg e2 = unED (decon e2) dlit2 dneg2 dadd2
  where
  dlit2 n = e
  dneg2 e = push_negBB e
  dadd2 e1 e2 = add (push_negBB (neg e1)) (push_negBB (neg e2))
 dadd e1 e2 = add (push_negBB e1) (push_negBB e2)


tbb1_norm = push_negBB tbb1
tbb1_norm_viewBB = viewBBd tbb1_norm
-- "(8 + ((-1) + (-2)))"

-- Add an extra negation
tbb1n_norm_viewBB = viewBBd (push_negBB (neg tbb1))
-- "((-8) + (1 + 2))"


-- ------------------------------------------------------------------------
-- A bit of algebra

-- The types (ExpF a -> a) and ExpDict a are isomorphic.
-- Hence, the operations of an Exp algebra with the carrier U 
-- could be specified either in the form of a value of the type ExpDict U,
-- or in the form of a function ExpF U -> U.

sigma_dict :: (ExpF a -> a) -> ExpDict a
sigma_dict sigma = ExpDict{ dlit = \n -> sigma (FLit n),
			    dneg = \e -> sigma (FNeg e),
			    dadd = \e1 e2 -> sigma (FAdd e1 e2) }

dict_sigma :: ExpDict a -> (ExpF a -> a)
dict_sigma dict (FLit n) = dlit dict n
dict_sigma dict (FNeg e) = dneg dict e
dict_sigma dict (FAdd e1 e2) = dadd dict e1 e2


-- Recall ExpBB1 as an uncurried form of the Boehm-Berarducci encoding.
-- It follows then the encoding can be written in the equivalent form
newtype ExpC = ExpC{unExpC :: forall a. (ExpF a -> a) -> a}

-- ExpC is indeed fully equivalent to ExpBB, and inter-convertible
h :: ExpDict a -> ExpBB -> a
h dict e  = unExpBB e (dlit dict) (dneg dict) (dadd dict)

exp_BB_C :: ExpBB -> ExpC
exp_BB_C e = ExpC $ \f -> h (sigma_dict f) e

exp_C_BB :: ExpC -> ExpBB
exp_C_BB e = ExpBB $ \dlit dneg dadd -> 
  unExpC e (dict_sigma (ExpDict dlit dneg dadd))

-- Let us write the constructors explicitly:

sigma_expC :: ExpF ExpC -> ExpC
sigma_expC (FLit n) = ExpC $ \f -> f (FLit n)
sigma_expC (FNeg e) = ExpC $ \f -> f (FNeg (unExpC e f))
sigma_expC (FAdd e1 e2) = ExpC $ \f -> f (FAdd (unExpC e1 f) (unExpC e2 f))

-- Sample term
t1c = exp_BB_C tbb1

-- The advantage of ExpC is that functions roll and unroll take
-- a particularly elegant form
rollC :: ExpF ExpC -> ExpC
rollC = sigma_expC

unrollC :: ExpC -> ExpF ExpC
unrollC e = unExpC e (fmap sigma_expC)

-- (ExpC, sigma_ExpC) is the initial algebra of the functor ExpF.
-- (the same holds for ExpBB since it is isomorphic to ExpC)

-- Indeed, consider an arbitrary ExpF algebra with the carrier U
-- and the operations sigma :: ExpF U -> U.
-- We show that there exists a unique homomorphism 
-- (hc sigma) :: ExpC -> U such that the following holds
-- hc sigma . sigma_ExpC = sigma . fmap (hc sigma)

-- Consider x = FLit n :: ExpF ExpC.
-- Then (sigma . fmap (hc sigma)) x = sigma (FLit n)
-- Thus we obtain
-- hc sigma (ExpC $ \f -> f (FLit n)) = sigma (FLit n)
-- from which we get
-- hc sigma e = unExpC e sigma

-- Consider x = FNeg e :: ExpF ExpC.
-- Then (sigma . fmap (hc sigma)) x = sigma (FNeg (hc sigma e))
-- Thus we obtain
-- hc sigma (ExpC $ \f -> f (FNeg (unExpC e f))) = sigma (FNeg (hc sigma e))
-- Again, the only way to satisfy the equality for all sigma and e is to set
-- hc sigma e = unExpC e sigma

-- The case of x = FAdd e1 e2 :: ExpF ExpC is similar.

-- Thus we get the unique morphism from (ExpC, sigma_ExpC) to
-- any other ExpF algebra.

hc :: (ExpF a -> a) -> ExpC -> a
hc sigma e = unExpC e sigma


-- Here is the illustration of the morphism. 

-- Define an ExpF algebra, 
-- with Strings as the carrier and the following operations

sigma_view :: ExpF String -> String
sigma_view (FLit n) = show n
sigma_view (FNeg e) = "(-" ++ e ++ ")"
sigma_view (FAdd e1 e2) = "(" ++ e1 ++ " + " ++ e2 ++ ")"

-- We immediately get the function to view the values of ExpC type:

viewC :: ExpC -> String
viewC = hc sigma_view

t1c_view = viewC t1c
-- "(8 + (-(1 + 2)))"

-- (ExpBB, sigma_ExpBB) is also initial algebra: there is a unique 
-- homomorphism from it to any other Exp algebra. Here is this morphism
-- h dict . roll = (dict_sigma dict) . fmap (h dict)
