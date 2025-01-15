theory Unreachable
imports
  Closure
  Epsilon
  "../CFG"
begin

hide_const (open) Topological_Spaces.closed

text \<open>Unreachable Symbol Elimination\<close>

(* reachable P S is the set of nonterminals reachable from the set of production
rules P and set of start states S *)

(*not sure if the inductive definition or the closure definition is better,
I think both are correct, less confident about the closure definition being correct*)
inductive_set reachable :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 'n set" for P S where
"A \<in> S \<Longrightarrow> A \<in> reachable P S"
| "\<lbrakk> (A,\<alpha>) \<in> P; A \<in> reachable P S; B \<in> nts_of_syms \<alpha>\<rbrakk> \<Longrightarrow> B \<in> reachable P S"

definition reachable_one_step :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 'n set" where
"reachable_one_step P S = {A | A. \<exists>B \<alpha>. B \<in> S \<and> (B,\<alpha>) \<in> P \<and> A \<in> nts_of_syms \<alpha>}"

definition "reachable_closure P S = closure (reachable_one_step P) S"

definition "rm_unreachable P S = {(A,\<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P \<and> A \<in> reachable_closure P S}"

lemma mono_reachable_one_step: "mono reachable_one_step"
unfolding reachable_one_step_def mono_def by (smt (verit, ccfv_SIG) Collect_mono le_funI subset_eq)





lemma prefix_rm_unreachable: "rm_unreachable P S \<subseteq> P"
  unfolding rm_unreachable_def by auto

  text \<open>The main theorem:\<close>
theorem 
  shows "Lang (rm_unreachable P {A}) A = Lang P A"
  proof
    show "Lang (rm_unreachable P {A}) A \<subseteq> Lang P A"
      using Lang_mono prefix_rm_unreachable by metis
  next
    show "Lang P A \<subseteq> Lang (rm_unreachable P {A}) A"
      sorry
qed
end