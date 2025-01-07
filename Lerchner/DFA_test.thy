(*  Title:      DFA_test.thy
    Author:     Manuel Lerchner
*)

theory DFA_test
  imports Main HOL.List DFA_to_RegExp
begin

 

definition N:"(N::nat) = 2"
definition S:"S = {1::nat,2}"
definition \<Sigma>:"\<Sigma> = [0::nat,1]"
definition t:"t= (\<lambda>i a. if i = 1 then (if a = 1 then 1 else 2) else 2)"
definition F:"F = {2::nat}"


 
 
interpretation  simple_dfa: dfa
  where n=N and S=S and nxt=t and sigma =\<Sigma>  and Fin = F
 proof (standard, goal_cases)
    case 1
    then show ?case 
      using S N
      by (metis Suc_1 atLeastAtMost_insertL atLeastAtMost_singleton fact_2 fact_ge_1)
  next
    case 2
    then show ?case 
      using F S by auto
  next
    case (3 i a)
    then show ?case 
      using t S
      by (metis insert_iff)   
  qed
 
(** Simple test of the R function. Somehow no code was generated inside the locale, so i copied the functions here **)

fun arcs_rexp :: "nat \<Rightarrow> nat \<Rightarrow> nat rexp" where
  "arcs_rexp i j =  List.foldr Plus 
                  (List.map Atom [ a \<leftarrow> [0::nat,1].  (if i = 1 then (if a = 1 then 1 else 2) else 2)= j ]) 
              Zero"


fun R :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat rexp " where
  "R i j 0 = (if i \<noteq> j then arcs_rexp i j else Plus One (arcs_rexp i j))" |
  "R i j (Suc k) = ( 
                   (  let R'= R    i       j    k in
                      let u = R    i    (Suc k) k in
                      let v = R (Suc k) (Suc k) k in
                      let w = R (Suc k)    j    k in
                    Plus  R' (Times u (Times (Star v) w))))"


fun simp_rexp:: "nat rexp \<Rightarrow> nat rexp" where
   "simp_rexp (Plus a Zero) = a" |
   "simp_rexp (Plus Zero a) = a" |
   "simp_rexp (Plus a b) = Plus (simp_rexp a) (simp_rexp b)" |
   "simp_rexp (Times One b) =  b"|
   "simp_rexp (Times Zero b) =  Zero"|
   "simp_rexp (Times a Zero) =  Zero"|
   "simp_rexp (Times a One) =  a"|
   "simp_rexp (Times a b) = ( Times (simp_rexp a) (simp_rexp b))"|
   "simp_rexp (Star (Plus a One)) =  (Star (simp_rexp a))"|
   "simp_rexp (Star (Plus One b)) =  (Star (simp_rexp b))"|
   "simp_rexp (Star x) =  (Star (simp_rexp x))"|
   "simp_rexp x = x"

 
value "simp_rexp (R 1 1 0) "
value "simp_rexp (R 1 2 0) "
value "simp_rexp (R 2 1 0) "
value "simp_rexp (R 2 2 0) "

value "simp_rexp (simp_rexp (simp_rexp (R 1 1 1)))"
value "simp_rexp (simp_rexp (simp_rexp (R 1 2 1)))"
value "simp_rexp (simp_rexp (simp_rexp (R 2 1 1)))"
value "simp_rexp (simp_rexp (simp_rexp (R 2 2 1)))"

value "simp_rexp (simp_rexp (simp_rexp (simp_rexp (simp_rexp  (R 1 1 2) ))))"
value "simp_rexp (simp_rexp (simp_rexp (simp_rexp (simp_rexp  (R 1 2 2) ))))"
value "simp_rexp (simp_rexp (simp_rexp (simp_rexp (simp_rexp  (R 2 1 2) ))))"
value "simp_rexp (simp_rexp (simp_rexp (simp_rexp (simp_rexp  (R 2 2 2) ))))"

end