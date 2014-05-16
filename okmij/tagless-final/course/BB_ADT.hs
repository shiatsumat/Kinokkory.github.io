-- The illustration of the Boehm-Berarducci encoding

-- This file is the baseline: using ordinary algebraic
-- data type and operations of constructions, deconstructions
-- and transformation.
-- We use the running example of the Exp data type from
-- tagless-final lectures

module BB_ADT where

-- Sample data type of expressions
data Exp = Lit Int 
	 | Neg Exp
	 | Add Exp Exp


-- Constructing a sample expression
ti1 = Add (Lit 8) (Neg (Add (Lit 1) (Lit 2)))

-- A sample consumer
-- It is structurally recursive
view:: Exp -> String
view (Lit n) = show n
view (Neg e) = "(-" ++ view e ++ ")"
view (Add e1 e2) = "(" ++ view e1 ++ " + " ++ view e2 ++ ")"

ti1_view = view ti1
-- "(8 + (-(1 + 2)))"

-- Transformer
-- * Pushing the negation down
-- Previously, expressions were constructed according to this grammar:
-- * General grammar of expressions
-- *     e ::= int | neg e | add e e
-- *
-- * Restricted grammar:
-- *     e ::= factor | add e e
-- *     factor ::= int | neg int
-- Now, only integer literals can be negated, and only once.

-- This function is NOT structurally recursive
push_neg :: Exp -> Exp
push_neg e@Lit{} = e
push_neg e@(Neg (Lit _)) = e
push_neg (Neg (Neg e)) = push_neg e
push_neg (Neg (Add e1 e2)) = Add (push_neg (Neg e1)) (push_neg (Neg e2))
push_neg (Add e1 e2) = Add (push_neg e1) (push_neg e2)

-- A few sample transformations and their results
ti1_norm = push_neg ti1
ti1_norm_view = view ti1_norm
-- "(8 + ((-1) + (-2)))"

-- Add an extra negation
ti1n_norm_view = view (push_neg (Neg ti1))
-- "((-8) + (1 + 2))"
