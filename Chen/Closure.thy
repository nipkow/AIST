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

unbundle lattice_syntax

context complete_lattice
begin

definition closure :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
"closure F S = lfp(\<lambda>T. S \<squnion> T \<squnion> F T)"

abbreviation "closed F S \<equiv> (F S \<le> S)"

end

lemma mono_closure_fun: "mono F \<Longrightarrow> mono (\<lambda>T::_::complete_lattice. S \<squnion> T \<squnion> F T)"
by (smt (verit, ccfv_threshold) monoI monoD sup.absorb_iff1 sup_ge2 sup_left_commute sup_mono)

theorem closure_incr: "(S::_::complete_lattice) \<le> closure F S"
unfolding closure_def by (meson le_sup_iff lfp_greatest)

theorem closure_mono:
shows "mono F \<Longrightarrow> S \<le> T \<Longrightarrow> closure F S \<le> closure F T"
unfolding closure_def using lfp_mono[of "\<lambda>T. S \<squnion> T \<squnion> F T" "\<lambda>T'. T \<squnion> T' \<squnion> F T'"]
by (meson order_refl sup.mono)

lemma closure_idem: assumes "mono F"
shows "closure F (closure F S) = closure F (S::_::complete_lattice)"
proof -
  let ?F = "\<lambda>S T. S \<squnion> T \<squnion> F T"
  have "\<forall>A. ?F S A \<le> lfp (?F S) \<squnion> A \<squnion> F A"
    by (meson le_sup_iff lfp_greatest order_refl sup.mono)
  then have *: "lfp (?F S) \<le> lfp (?F (lfp (?F S)))"
    by (simp add: lfp_mono)
  have "lfp (?F (lfp (?F S))) \<le> lfp (?F S)"
    by (smt (verit, best) lfp_greatest lfp_lowerbound sup.absorb_iff2 sup.boundedE)
  with * closure_incr show ?thesis
 unfolding closure_def by order
qed

theorem closure_closed: assumes "mono F" shows "closed F (closure F S)"
unfolding closure_def using lfp_fixpoint [OF mono_closure_fun[OF assms]]
by (simp add: order_eq_iff)

end