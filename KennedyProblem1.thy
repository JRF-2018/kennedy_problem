(*
    File:        KennedyProblem1.thy
    Version:     0.0.2
    Time-stamp:  <2020-06-22T11:04:41Z>
    Author:      JRF
    Logic Image: HOL (of Isabelle2020)

    License:

    Public Domain (because these programs are as small as
    mathematical formulae).

    You can freely modify and re-publish them.
*)

theory KennedyProblem1
  imports Main
begin

consts Paradise :: "bool"

datatype angel = Churchill | Hitler

definition churchill :: "bool => bool" where
"churchill x == x"

definition hitler :: "bool => bool" where
"hitler x == ~x"

fun apply_angel :: "angel => bool => bool" where
"apply_angel Churchill x = churchill x" |
"apply_angel Hitler x = hitler x"

definition kennedy_problem :: 
  "((bool => bool) => bool) => bool"
  where
    "kennedy_problem Q == 
ALL x::angel. apply_angel x (Q (apply_angel x)) = Paradise"

lemma kennedy_answer:
  shows "kennedy_problem (% f. f Paradise)"
  apply (unfold kennedy_problem_def)
  apply (intro allI)
  apply (case_tac x)
  apply (simp_all add: churchill_def hitler_def)
  done

end
