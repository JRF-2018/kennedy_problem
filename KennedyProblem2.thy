(*
    File:        KennedyProblem2.thy
    Version:     0.0.1
    Time-stamp:  <2020-06-21T21:46:16Z>
    Author:      JRF
    Logic Image: HOL (of Isabelle2020)

    License:

    Public Domain (because these programs are as small as
    mathematical formulae).

    You can freely modify and re-publish them.
*)

theory KennedyProblem2
  imports Main
begin

typedecl env 

consts Paradise :: "bool"

datatype angel = Churchill | Hitler | Stalin

definition churchill :: "bool => bool" where
"churchill x == x"

definition hitler :: "bool => bool" where
"hitler x == ~x"

consts stalin :: "env => bool"

fun apply_angel :: "angel => env => bool => bool" where
"apply_angel Churchill e x = churchill x" |
"apply_angel Hitler e x = hitler x" |
"apply_angel Stalin e x = stalin e"

definition kennedy_problem ::
  "((bool => bool) => angel => angel => angel => bool) => 
   (bool => nat) => 
   ((bool => bool) => angel => angel => angel => bool) => 
   bool"
  where
"kennedy_problem Q1 C Q2 == 
ALL a::angel. ALL b::angel. ALL c::angel.
  a ~= b & b ~= c & c ~= a
-->
(ALL p1::bool. ALL y::angel.
  ALL e1::env. ALL e2::env. ALL e3::env. ALL e4::env.
  apply_angel a e1 (Q1 (apply_angel a e2) a b c) = p1
  & y = nth [a, b, c] (C p1)
  -->
  apply_angel y e3 (Q2 (apply_angel y e4) a b c) = Paradise)"

lemma kennedy_answer:
  shows "kennedy_problem (%f a b c. f (b = Stalin))
           (%p. if p then 2 else 1) (% f a b c. f Paradise)"
  apply (simp add: kennedy_problem_def)
  apply (rule allI)+
  apply (case_tac [!] a)
  apply (case_tac [!] b)
  apply (case_tac [!] c)
  apply (simp_all add: churchill_def hitler_def)
  done

end
