theory Closure
imports
  "HOL-Library.While_Combinator" (* later for executability *)
begin

text \<open>This theory formalises Closure Operators \<^url>\<open>https://en.wikipedia.org/wiki/Closure_operator\<close>.
\<open>closure F S\<close> is the least superset \<open>T\<close> of \<open>S\<close> such that \<open>F T \<subseteq> T\<close>.
They are easily definable via the least fixed point operator \<open>lfp\<close>.

Used in many standard grammar transformations.

Later: implementation via the \<open>while\<close> combinator.
\<close>

definition "closure F S = lfp(\<lambda>T. S \<union> T \<union> F T)"

abbreviation "closed F S \<equiv> (F S \<subseteq> S)"

lemma mono_closure_fun: "mono F \<Longrightarrow> mono (\<lambda>T. S \<union> T \<union> F T)"
by (smt (verit, ccfv_threshold) monoI monoD sup.absorb_iff1 sup_ge2 sup_left_commute sup_mono)

theorem closure_incr: "S \<subseteq> closure F S"
unfolding closure_def by (meson le_sup_iff lfp_greatest)

theorem closure_mono: "mono F \<Longrightarrow> S \<subseteq> T \<Longrightarrow> closure F S \<subseteq> closure F T"
unfolding closure_def using lfp_mono[of "\<lambda>T. S \<union> T \<union> F T" "\<lambda>T'. T \<union> T' \<union> F T'"]
by blast

lemma closure_idem: assumes "mono F" shows "closure F (closure F S) = closure F S"
proof -
  let ?F = "\<lambda>S T. S \<union> T \<union> F T"
  have "\<forall>A. ?F S A \<subseteq> lfp (?F S) \<union> A \<union> F A"
    using lfp_fixpoint[OF mono_closure_fun[OF assms]] by blast
  then have *: "lfp (?F S) \<subseteq> lfp (?F (lfp (?F S)))"
    by (simp add: lfp_mono)
  have "lfp (?F (lfp (?F S))) \<subseteq> lfp (?F S)"
    by (smt (verit, best) lfp_greatest lfp_lowerbound sup.absorb_iff2 sup.boundedE)
  with * closure_incr show ?thesis
 unfolding closure_def by blast
qed

theorem closure_closed: assumes "mono F" shows "closed F (closure F S)"
unfolding closure_def using lfp_fixpoint [OF mono_closure_fun[OF assms]]
by auto

end