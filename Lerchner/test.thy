theory test
  imports Main HOL.List DFA_to_RegExp2
begin

interpretation simple_dfa: dfa 
  2 (* Number of states *)
  "{1, 2}" (* Set of states *)
  "[0::nat,1]" (* Alphabet *)
  "\<lambda>i a. if i = 1 then (if a = 1 then 1 else 2) else 2 " (* Transition function *)
  "{2}" (* Set of accepting states *)
proof 
  show "(0::nat) < 2"
    by simp  
next
  show "{1::nat, 2} = {1..2}"
    by (metis Icc_eq_insert_lb_nat Suc_1 atLeastAtMost_singleton lessI less_or_eq_imp_le)
next
  show "\<And>i a. i \<in> {1::nat, 2} \<longrightarrow> (if i = 1 then if a = 1 then 1 else 2 else 2) \<in> {1::nat, 2}"
    by(auto)
next
  show "{2} \<subseteq> {1, 2}"
    by auto
next 
  show" \<And>i a. i \<in> {1, 2} \<Longrightarrow> a \<in> set [0, 1] \<Longrightarrow> (if i = 1 then if a = 1 then 1 else 2 else 2) \<in> {1, 2}"
    by auto
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
   "simp_rexp (Times Zero b) =  Zero"|
   "simp_rexp (Times a Zero) =  Zero"|
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