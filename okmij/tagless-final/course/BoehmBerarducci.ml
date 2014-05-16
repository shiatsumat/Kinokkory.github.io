(*
 The illustration of the Boehm-Berarducci encoding

 The encoding has been introduced in the paper
   Corrado Boehm and Alessandro Berarducci
   Automatic Synthesis of Typed {$\Lambda$}-Programs on Term Algebras
   Theor. Comp. Sci., 1985, v39, pp. 135--154.

 However, the explanations in the paper may be a bit difficult to
 understand. The present file aims to clarify the encoding.

 Boehm-Berarducci encoding represents an inductive data type
 as a non-recursive but higher-rank data type.
 The Boehm-Berarducci approach applies only to `strictly positive'
 data types: there are no functions in the domain of constructors.
 (See Remark 1.1 (d) in Boehm-Berarducci's paper).

 The running example is from the first part of the Tagless lecture.
*)

(* We start with the conventional definition of an inductive data type 
  and write sample operations on it using pattern-matching.
*)

module InductiveDT = struct

  type exp = 				(* A sample inductive type *)
    | Lit of int
    | Neg of exp
    | Add of exp * exp

  (* Sample term *)
  let t1 = Add (Lit 8, Neg (Add (Lit 1, Lit 2)))

  (* The evaluator: case analysis on an expression *)
  let rec eval : exp -> int = function
    | Lit x -> x
    | Neg e -> - (eval e)
    | Add (e1,e2) -> eval e1 + eval e2
end;;

let 5 = InductiveDT.eval InductiveDT.t1;;

(* Boehm-Berarducci approach *)

(* First we clarify the signature of the exp algebra: the
   types of the algebra constructors. We represent the signature
   as a record. It is NOT recursive.
*)

type 'a exp_dic = 
    {lit : int -> 'a;
     neg : 'a -> 'a;
     add : 'a * 'a -> 'a};;

(* The datatype-less encoding of expressions.
   First-class polymorphism is needed. 
   We could have eliminated exp_dic as an argument by currying it.
*)
type exp = {expi : 'a . 'a exp_dic -> 'a};;

(* Constructors *)
let lit : int -> exp = fun x ->
  {expi = fun d -> d.lit x}
;;
let neg : exp -> exp = fun {expi = e} ->
  {expi = fun d -> d.neg (e d)}
;;
let add : (exp * exp) -> exp = fun ({expi = e1},{expi = e2}) ->
  {expi = fun d -> d.add (e1 d, e2 d)}
;;

(* Sample term: like InductiveDT.t1, but in the lower case *)
let t1 = add (lit 8, neg (add (lit 1, lit 2)));;

(* First evaluator: as fold. The function eval1 is not recursive *)
let eval1 : exp -> int = fun {expi = e} ->
  e {lit = (fun x -> x);
     neg = (fun e -> - e);
     add = (fun (e1,e2) -> e1 + e2)};;

let 5 = eval1 t1;;

(* Introspection and pattern-matching *)

(* The following shows that we can replace type-level recursion
   (in InductiveDT.exp) with term-level recursion.
   Everything that we can do with InductiveDT.exp we can do
   with Boehm-Berarducci's exp.

  The following definitions of roll and unroll are actually present
  in Boehm-Berarducci's paper -- but in a very indirect way.

  The crucial part is Defn 7.1: sort of self-interpreter: v cons nil ~= v
  Informally, it shows that roll . unroll should be equivalent to the
  identity. The equivalence relation (~=) is strictly speaking not
  the equality; in modern terms, (~=) is contextual equivalence.
*)

(* First we re-write the signature of the Exp algebra, ExpDic,
   in the form of a strictly-positive functor
*)

type 'a expF = 
  | Lit of int
  | Neg of 'a
  | Add of 'a * 'a
;;

let rec roll : exp expF -> exp = function
  | Lit x -> lit x
  | Neg e -> neg e
  | Add (e1,e2) -> add (e1,e2)
;;

(* The occurrence of roll: the source of major inefficiency
   when we do repeated pattern-matching.
*)
let unroll : exp -> exp expF = fun {expi = e} ->
  e {lit = (fun x -> Lit x);
     neg = (fun e -> Neg (roll e));
     add = (fun (e1,e2) -> Add (roll e1, roll e2))};;

(* We redo the evaluator, using pattern-matching this time.
   This evaluator is recursive 
*)

let rec eval2 : exp -> int = fun e ->
  match unroll e with
  | Lit x -> x
  | Neg e -> - (eval2 e)
  | Add (e1,e2) -> eval2 e1 + eval2 e2
;;

let 5 = eval2 t1;;
