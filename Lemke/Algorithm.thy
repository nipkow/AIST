section\<open>Computing $pre^*(L)$\<close>

theory Algorithm
  imports Definition FiniteAutomaton
begin \<comment>\<open>begin-theory Algorithm\<close>

subsection\<open>Base Theorem\<close>

inductive_set (in CFG) prestar_nfa_transitions ::
    "('s \<times> ('n, 't) sym \<times> 's) set \<Rightarrow> ('s \<times> ('n, 't) sym \<times> 's) set" for T where
  "(q, c, q') \<in> T \<Longrightarrow> (q, c, q') \<in> prestar_nfa_transitions T" |
  "(A, \<beta>) \<in> P \<Longrightarrow> q' \<in> steps T \<beta> q \<Longrightarrow> (q, Nt A, q') \<in> prestar_nfa_transitions T"

definition (in CFG) prestar_nfa :: "('s, ('n, 't) sym) nfa \<Rightarrow> ('s, ('n, 't) sym) nfa" where
  "prestar_nfa M \<equiv> M \<lparr> transitions := prestar_nfa_transitions (transitions M) \<rparr>"

lemma (in CFG) step_starp_induct:
  assumes "w \<Rightarrow>\<^sup>* w'" and "Q w w" and "\<And>y z. w \<Rightarrow>\<^sup>* y \<Longrightarrow> y \<Rightarrow> z \<Longrightarrow> Q w y \<Longrightarrow> Q w z"
  shows "Q w w'"
  using assms(1) by (induction set: rtranclp; simp add: assms)

lemma (in CFG) prestar_regular:
  fixes M :: "('s, ('n, 't) sym) nfa"
  shows "pre_star (lang M) = lang (prestar_nfa M)"
proof -
  define L where "L \<equiv> lang M"
  define L' where "L' = lang (prestar_nfa M)"

  have "\<And>w. w \<in> pre_star L \<Longrightarrow> w \<in> L'"
  proof -
    fix w
    assume "w \<in> pre_star L"
    then obtain w' where "w \<Rightarrow>\<^sup>* w'"
      unfolding pre_star_def by blast
    then show "w \<in> L'"
      unfolding L'_def prestar_nfa_def
      sorry
  qed
  moreover have "\<And>w. w \<in> L' \<Longrightarrow> w \<in> pre_star L"
  proof -
    fix w
    assume "w \<in> L'"

    then have "\<exists>w' \<in> L. w \<Rightarrow>\<^sup>* w'"
      unfolding L'_def prestar_nfa_def
      sorry

    then show "w \<in> pre_star L"
      by (simp add: pre_star_def)
  qed
  ultimately have "pre_star L = L'"
    by blast
  then show ?thesis
    by (simp add: L_def L'_def)
qed

subsection\<open>Formalising the Algorithm\<close>

(* TODO *)

end \<comment>\<open>end-theory Algorithm\<close>
