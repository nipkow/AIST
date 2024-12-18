theory DFA_to_RegExp

imports 
"$AFP/Regular-Sets/Regular_Exp"   
begin

locale dfa =
  fixes n :: nat
  and sigma :: "'a list"
  and nxt :: "nat \<Rightarrow> 'a \<Rightarrow> nat"
  (* initial state is 0 *)
  and Fin :: "nat set"
begin
  
  fun nxts :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "nxts [] q = q" |
  "nxts (a#w) q = nxts w (nxt q a)"
  
  definition accepted :: "'a list \<Rightarrow> bool" where
  "accepted w = (nxts w 0 \<in> Fin)"
  
(* Your work goes here: *)

definition rexp_of :: "'a rexp" where "rexp_of = undefined"

theorem "w \<in> lang (rexp_of) \<longleftrightarrow> accepted w"
  sorry

end