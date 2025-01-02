theory Unreachable
imports
  Closure
  Epsilon
  "../CFG"
begin

hide_const (open) Topological_Spaces.closed

text \<open>Unreachable Symbol Elimination\<close>

definition "reachable P A = (\<exists> B \<alpha> \<beta>. (B,\<alpha> @ [Nt A] @ \<beta>) \<in> P)"

definition "rm_unreachable P = {(A,\<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P \<and> reachable P A}"

lemma prefix_rm_unreachable: "rm_unreachable P \<subseteq> P"
  unfolding rm_unreachable_def by auto

  text \<open>The main theorem:\<close>
theorem 
  assumes "reachable P A" 
  shows "Lang (rm_unreachable P) A = Lang P A"
  proof
    show "Lang (rm_unreachable P) A \<subseteq> Lang P A"
      using Lang_mono prefix_rm_unreachable by metis
  next
    show "Lang P A \<subseteq> Lang (rm_unreachable P) A"
      using assms unfolding reachable_def rm_unreachable_def
      sorry
qed
end