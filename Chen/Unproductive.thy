theory Unproductive
imports
  Closure
  Epsilon
  "../CFG"
begin

hide_const (open) Topological_Spaces.closed

text \<open>Unproductive Symbol Elimination\<close>

definition "rm_unproductive P = {(A,\<alpha>) |A \<alpha>. (A,\<alpha>) \<in> P \<and> Lang P A \<noteq> {}}"


lemma prefix_rm_unproductive: "rm_unproductive P \<subseteq> P"
  unfolding rm_unproductive_def by auto

lemma derivs_if_derives_unproductive: "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> rm_unproductive P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case
    oops


theorem "Lang (rm_unproductive P) A = Lang P A"
  proof
    show "Lang (rm_unproductive P) A \<subseteq> Lang P A"
      using prefix_rm_unproductive Lang_mono by metis
  next
    consider (LangEmpty) "Lang P A = {}" | (NotLangEmpty) "Lang P A \<noteq> {}"
      by auto
    then show "Lang P A \<subseteq> Lang (rm_unproductive P) A"
    proof (cases)
      case LangEmpty
      then show ?thesis by simp
    next
      case NotLangEmpty
      then show ?thesis
      unfolding rm_unproductive_def
      sorry
    qed
qed
end