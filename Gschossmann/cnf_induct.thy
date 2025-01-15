theory cnf_induct
  imports "../Stimpfle/CNF" "derivel_nts"
begin

(* custom induction rule for leftmost derivations in CNF *)
lemma cnf_derivels_induct[consumes 2, case_names base step_nt_nt step_tm]:
  assumes "P \<turnstile> xs \<Rightarrow>l* ys"
  and cnf: "CNF P"
  and Base: "Q ys"
  and Step1: "\<And>u A v B C. \<lbrakk> P \<turnstile> map Tm u @ [Nt A] @ v \<Rightarrow>l* ys; Q (map Tm u @ [Nt B,Nt C] @ v); (A,[Nt B,Nt C]) \<in> P \<rbrakk> \<Longrightarrow> Q (map Tm u @ [Nt A] @ v)"
  and Step2: "\<And>u A v t. \<lbrakk> P \<turnstile> map Tm u @ [Nt A] @ v \<Rightarrow>l* ys; Q (map Tm u @ [Tm t] @ v); (A,[Tm t]) \<in> P \<rbrakk> \<Longrightarrow> Q (map Tm u @ [Nt A] @ v)"
  shows "Q xs"
  using assms(1)
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case using Base by fast
next
  case (step y z)
  then have "(\<exists> (A,w) \<in> P. \<exists>u1 u2. y = map Tm u1 @ Nt A # u2 \<and> z = map Tm u1 @ w @ u2)"
    by (simp only: derivel_iff)
  then obtain A w u1 u2 where split: "(A,w) \<in> P \<and> y = map Tm u1 @ Nt A # u2 \<and> z = map Tm u1 @ w @ u2"
    by fast
  with cnf have "(\<exists>B C. w = [Nt B, Nt C]) \<or> (\<exists>t. w = [Tm t])" unfolding CNF_def by fast
  then show ?case
  proof (elim disjE)
    assume "\<exists>B C. w = [Nt B, Nt C]"
    then obtain B C where "w = [Nt B, Nt C]" by fast
    with split step Step1 show "Q y" 
      by (simp add: converse_rtranclp_into_rtranclp derivels_imp_derives)
  next
    assume "\<exists>t. w = [Tm t]"
    then obtain t where "w = [Tm t]" by fast
    with split step Step2 show "Q y" 
      by (simp add: converse_rtranclp_into_rtranclp derivels_imp_derives)
  qed
qed

end