theory DFA_rlin2
imports
  Right_Linear
begin

definition nxt_rlin2 :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2 P A a = {B. (A, [Tm a, Nt B]) \<in> P}"

definition nxt_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2_set P M a = (\<Union>A\<in>M. {B. (A, [Tm a, Nt B]) \<in> P})"

definition nxts_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't list \<Rightarrow> 'n set" where
"nxts_rlin2_set P = foldl (nxt_rlin2_set P)"

theorem accepted_if_Lang:
assumes "rlin2 P"
shows "w \<in> Lang P A \<Longrightarrow> A \<in> M \<Longrightarrow> \<exists>Z \<in> nxts_rlin2_set P M w. (Z,[]) \<in> P"
sorry

theorem Lang_if_accepted: "Z \<in> nxts_rlin2_set P M w \<Longrightarrow> (Z,[]) \<in> P \<Longrightarrow> \<exists>A\<in>M. w \<in> Lang P A"
sorry

theorem Lang_if_accepted_if_rlin2:
assumes "rlin2 P"
shows "w \<in> Lang P A \<longleftrightarrow> (\<exists>Z \<in> nxts_rlin2_set P {A} w. (Z,[]) \<in> P)"
using accepted_if_Lang[OF assms] Lang_if_accepted
by (metis singleton_iff)

end