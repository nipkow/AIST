section\<open>Computing $pre^*(L)$\<close>

theory Algorithm
  imports Definition FiniteAutomaton
begin \<comment>\<open>begin-theory Algorithm\<close>

context CFG
begin \<comment>\<open>begin-context CFG\<close>

fun prestar_nfa_t :: "('s \<times> ('n, 't) sym \<times> 's) set \<Rightarrow> nat \<Rightarrow> ('s \<times> ('n, 't) sym \<times> 's) set" where
  "prestar_nfa_t T (Suc n) = (
    let T' = prestar_nfa_t T n in
    T' \<union> { (q, Nt A, q') | q q' A. \<exists>\<beta>. (A, \<beta>) \<in> P \<and> q' \<in> steps T' \<beta> q }
  )" |
  "prestar_nfa_t T 0 = T"

lemma prestar_nfa_t_converges:
  fixes T :: "('s \<times> ('n, 't) sym \<times> 's) set"
  assumes "finite (UNIV::'s set)" \<comment>\<open>Only works if states are finite.\<close>
  shows "\<exists>n. \<forall>n'. prestar_nfa_t T n' = prestar_nfa_t T n"
  sorry

definition prestar_nfa :: "('s, ('n, 't) sym) nfa \<Rightarrow> ('s, ('n, 't) sym) nfa" where
  "prestar_nfa M \<equiv> (
    let n = THE n. \<forall>n'. prestar_nfa_t (transitions M) n' = prestar_nfa_t (transitions M) n in
    M \<lparr> transitions := prestar_nfa_t (transitions M) n \<rparr>
  )"

lemma nfa_transitions_mono:
  assumes "transitions M\<^sub>1 \<subseteq> transitions M\<^sub>2"
    and "start M\<^sub>1 = start M\<^sub>2"
    and "finals M\<^sub>1 \<subseteq> finals M\<^sub>2"
  shows "lang M\<^sub>1 \<subseteq> lang M\<^sub>2"
  sorry

lemma nfa_transitions_mono': "lang M \<subseteq> lang (M \<lparr> transitions := transitions M \<union> T \<rparr>)"
proof -
  define M' where "M' = M \<lparr> transitions := transitions M \<union> T \<rparr>"
  moreover have "transitions M \<subseteq> transitions M'" and "start M = start M'" and "finals M \<subseteq> finals M'"
    by (simp add: M'_def)+
  ultimately show ?thesis
    using nfa_transitions_mono by blast
qed

lemma prestar_nfa_mono:
  fixes M :: "('s, ('n, 't) sym) nfa"
  assumes "finite (UNIV::'s set)"
  shows "lang M \<subseteq> lang (prestar_nfa M)"
proof -
  let ?M = "\<lambda>n. M \<lparr> transitions := prestar_nfa_t (transitions M) n \<rparr>"

  define M' where "M' = prestar_nfa M"
  moreover obtain n where n_def: "\<forall>n'. prestar_nfa_t (transitions M) n' = prestar_nfa_t (transitions M) n"
    using assms prestar_nfa_t_converges by blast
  ultimately have M'_trans: "M' = ?M n"
    by (simp add: prestar_nfa_def)

  have "lang M \<subseteq> lang (?M n)"
  proof (induction "transitions M" n rule: prestar_nfa_t.induct)
    case (1 n)
    moreover have "lang (?M n) \<subseteq> lang (?M (Suc n))"
      by (metis n_def order_refl)
    ultimately show ?case by simp
  next
    case 2 thus ?case by simp
  qed
  then show ?thesis
    using M'_def M'_trans by simp
qed

lemma prestar_nfa_saturated:
  fixes M :: "('s, ('n, 't) sym) nfa"
  assumes "finite (UNIV::'s set)"
    and "(A, \<beta>) \<in> P" and "q' \<in> steps (transitions (prestar_nfa M)) \<beta> q"
  shows "(q, Nt A, q') \<in> transitions (prestar_nfa M)"
proof -
  define M' where "M' = prestar_nfa M"
  moreover obtain n where n_def: "\<forall>n'. prestar_nfa_t (transitions M) n' = prestar_nfa_t (transitions M) n"
    using assms prestar_nfa_t_converges by blast
  ultimately have M'_trans: "M' = M \<lparr> transitions := prestar_nfa_t (transitions M) n \<rparr>"
    by (simp add: prestar_nfa_def)

  have "\<And>n. q' \<in> steps (prestar_nfa_t (transitions M) n) \<beta> q \<Longrightarrow> (q, Nt A, q') \<in> prestar_nfa_t (transitions M) (Suc n)"
    subgoal for n
    proof (induction "transitions M" n rule: prestar_nfa_t.induct)
      case (1 n)
      then show ?case
        using assms(2) by (metis n_def)
    next
      case 2
      then show ?case
        using assms(2) sorry
    qed
    done

  show ?thesis sorry
qed

lemma prestar_nfa1:
  fixes M :: "('s, ('n, 't) sym) nfa"
  assumes "finite (UNIV::'s set)"
  shows "pre_star (lang M) \<subseteq> lang (prestar_nfa M)"
proof -
  define M' where "M' = prestar_nfa M"
  moreover obtain n where "\<forall>n'. prestar_nfa_t (transitions M) n' = prestar_nfa_t (transitions M) n"
    using assms prestar_nfa_t_converges by blast
  ultimately have M'_trans: "M' = M \<lparr> transitions := prestar_nfa_t (transitions M) n \<rparr>"
    by (simp add: prestar_nfa_def)

  have "\<And>\<alpha>. \<alpha> \<in> pre_star (lang M) \<Longrightarrow> \<alpha> \<in> lang (prestar_nfa M)"
  proof -
    fix \<alpha>
    assume "\<alpha> \<in> pre_star (lang M)"
    then obtain \<beta> where "\<alpha> \<Rightarrow>\<^sup>* \<beta>" and "\<beta> \<in> lang M"
      unfolding pre_star_def by blast
    then show "\<alpha> \<in> lang (prestar_nfa M)"
    proof (induction rule: converse_rtranclp_induct[where r="(\<Rightarrow>)"])
      case base
      then show ?case
        using assms prestar_nfa_mono by blast
    next
      case (step \<alpha> \<gamma>)

      define T where [simp add]: "T = transitions (prestar_nfa M)"
      define q\<^sub>0 where [simp add]: "q\<^sub>0 = start (prestar_nfa M)"

      obtain \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3 A where "\<alpha> = \<alpha>\<^sub>1@[Nt A]@\<alpha>\<^sub>3" and "\<gamma> = \<alpha>\<^sub>1@\<alpha>\<^sub>2@\<alpha>\<^sub>3" and "(A, \<alpha>\<^sub>2) \<in> P"
        using step(1) by (metis (mono_tags, opaque_lifting) prods_to_lts.simps step_relp_def transition_relation_def)

      have "\<gamma> \<in> lang (prestar_nfa M)"
        by (simp add: step)
      then have "accepts (prestar_nfa M) (\<alpha>\<^sub>1@\<alpha>\<^sub>2@\<alpha>\<^sub>3)"
        using \<open>\<gamma> = \<alpha>\<^sub>1@\<alpha>\<^sub>2@\<alpha>\<^sub>3\<close> lang_def by blast
      then obtain q q' q\<^sub>f where step1: "q \<in> steps T \<alpha>\<^sub>1 q\<^sub>0" and step2: "q' \<in> steps T \<alpha>\<^sub>2 q"
          and step3: "q\<^sub>f \<in> steps T \<alpha>\<^sub>3 q'" and [simp add]: "q\<^sub>f \<in> finals (prestar_nfa M)"
        using accepts_split3[of "prestar_nfa M" \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3] by fastforce

      have "(q, Nt A, q') \<in> T"
        using prestar_nfa_saturated assms \<open>(A, \<alpha>\<^sub>2) \<in> P\<close> step2 by fastforce
      then have "q' \<in> steps T [Nt A] q"
        by simp
      then have "q\<^sub>f \<in> steps T (\<alpha>\<^sub>1@[Nt A]@\<alpha>\<^sub>3) q\<^sub>0"
        using step1 step3 steps_join3 by fast
      then have "accepts (prestar_nfa M) (\<alpha>\<^sub>1@[Nt A]@\<alpha>\<^sub>3)"
        by fastforce
      then show ?case
        unfolding lang_def \<open>\<alpha> = \<alpha>\<^sub>1@[Nt A]@\<alpha>\<^sub>3\<close> by simp
    qed
  qed
  then show ?thesis
    using M'_def M'_trans by blast
qed

lemma prestar_nfa2:
  fixes M :: "('s, ('n, 't) sym) nfa"
  assumes "finite (UNIV::'s set)"
  shows "lang (prestar_nfa M) \<subseteq> pre_star (lang M)"
  sorry

theorem prestar_nfa:
  fixes M :: "('s, ('n, 't) sym) nfa"
  assumes "finite (UNIV::'s set)"
  shows "lang (prestar_nfa M) = pre_star (lang M)"
  using assms prestar_nfa1 prestar_nfa2 by blast

end \<comment>\<open>end-context CFG\<close>

end \<comment>\<open>end-theory Algorithm\<close>
