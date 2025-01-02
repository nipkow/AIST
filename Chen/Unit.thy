theory Unit
imports
  Closure
  Epsilon
  "../CFG"
begin

hide_const (open) Topological_Spaces.closed

text \<open>Unit closure\<close>

definition unit_subst :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) Prods" where
"unit_subst P = {(A, \<alpha>) | A \<alpha>. \<exists> B. (A,[Nt B]) \<in> P \<and> (B,\<alpha>) \<in> P}"

definition "unit_closure P = closure unit_subst P"

lemma mono_unit_subst: "mono unit_subst"
unfolding unit_subst_def mono_def by fastforce

(* One direction is easy *)
lemma unit_closure_incr: "P \<subseteq> unit_closure P"
unfolding unit_closure_def by (simp add: closure_incr)

lemma Lang_unit_closure_incr: "Lang P A \<subseteq> Lang (unit_closure P) A"
by (simp add: unit_closure_incr Lang_mono)

(* This direction is slightly more interesting *)
theorem derivs_if_derives_unit_closure: "unit_closure P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
(* should work *)
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case
    by simp
next
  case (step u A v w)
  then show ?case
    sorry
qed

lemma Lang_unit_closure_subset: "Lang (unit_closure P) A \<subseteq> Lang P A"
unfolding Lang_def using derivs_if_derives_unit_closure by blast

(* The final theorem: *)
theorem Lang_unit_closure: "Lang (unit_closure P) A = Lang P A"
by (metis antisym[OF Lang_unit_closure_subset Lang_unit_closure_incr])

lemma closed_unit_subst_unit_closure: "closed unit_subst (unit_closure P)"
  unfolding unit_closure_def using closure_closed[OF mono_unit_subst] by blast

definition "rm_unit P = {p \<in> unit_closure P .\<forall>B. snd p \<noteq> [Nt B]}"

  text \<open>The main theorem:\<close>
  theorem "Lang (rm_unit P) A = Lang P A"
  proof
      show "Lang (rm_unit P) A \<subseteq> Lang P A"
        by (metis (mono_tags) Collect_subset Lang_mono Lang_unit_closure rm_unit_def)
  next
      show "Lang P A \<subseteq> Lang (rm_unit P) A"
      sorry
qed
end