section\<open>Computing $pre^*(L)$\<close>

theory Algorithm
  imports Definition FiniteAutomaton "HOL-Library.While_Combinator"
begin \<comment>\<open>begin-theory Algorithm\<close>

context CFG
begin \<comment>\<open>begin-context CFG\<close>

subsection\<open>Preliminaries\<close>

definition prestar_step :: "('s \<times> ('n, 't) sym \<times> 's) set \<Rightarrow> ('s \<times> ('n, 't) sym \<times> 's) set" where
  "prestar_step T \<equiv> { (q, Nt A, q') | q q' A. \<exists>\<beta>. (A, \<beta>) \<in> P \<and> q' \<in> steps T \<beta> q }"

definition prestar_while :: "('s \<times> ('n, 't) sym \<times> 's) set \<Rightarrow> ('s \<times> ('n, 't) sym \<times> 's) set option" where
  "prestar_while \<equiv> while_option (\<lambda>T. T \<union> prestar_step T \<noteq> T) (\<lambda>T. T \<union> prestar_step T)"

subsection\<open>Monotonicity and Termination\<close>

lemma nfa_mono':
  assumes "T\<^sub>1 \<subseteq> T\<^sub>2" and "q\<^sub>1 \<subseteq> q\<^sub>2"
  shows "Steps T\<^sub>1 w q\<^sub>1 \<subseteq> Steps T\<^sub>2 w q\<^sub>2"
proof (insert assms(2); induction w arbitrary: q\<^sub>1 q\<^sub>2)
  case Nil thus ?case by (simp add: Steps_def)
next
  case (Cons w ws)
  have "Step T\<^sub>1 w q\<^sub>1 \<subseteq> Step T\<^sub>2 w q\<^sub>2"
    unfolding Step_def step_def using assms(1) Cons(2) by blast
  then have "Steps T\<^sub>1 ws (Step T\<^sub>1 w q\<^sub>1) \<subseteq> Steps T\<^sub>1 ws (Step T\<^sub>2 w q\<^sub>2)"
    by (rule Steps_mono)
  then have "Steps T\<^sub>1 ws (Step T\<^sub>1 w q\<^sub>1) \<subseteq> Steps T\<^sub>2 ws (Step T\<^sub>2 w q\<^sub>2)"
    using Cons(1) by blast
  then show ?case
    by (simp add: Steps_def)
qed

lemma nfa_mono: "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> steps T\<^sub>1 w q \<subseteq> steps T\<^sub>2 w q"
  using nfa_mono'[of T\<^sub>1 T\<^sub>2 "{q}" "{q}" w] by simp

lemma nfa_lang_mono: "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> lang' T\<^sub>1 s f \<subseteq> lang' T\<^sub>2 s f"
  unfolding lang'_def using nfa_mono[of T\<^sub>1 T\<^sub>2] by fast



lemma prestar_while_mono:
  assumes "prestar_while T\<^sub>0 = Some T'"
  shows "T\<^sub>0 \<subseteq> T'"
  unfolding prestar_while_def
proof (rule while_option_rule[where P = "\<lambda>T. T\<^sub>0 \<subseteq> T", OF _ assms[unfolded prestar_while_def]])
  show "T\<^sub>0 \<subseteq> T\<^sub>0"
    by blast
next
  fix T
  assume "T\<^sub>0 \<subseteq> T" and "T \<union> prestar_step T \<noteq> T"
  then show "T\<^sub>0 \<subseteq> T \<union> prestar_step T"
    by blast
qed

lemma prestar_step_mono: "mono (\<lambda>T. T \<union> prestar_step T)"
proof -
  have "\<And>A B. A \<subseteq> B \<Longrightarrow> prestar_step A \<subseteq> prestar_step B"
  proof (standard)
    fix A :: "('s \<times> ('n, 't) sym \<times> 's) set" and B and w
    assume assm1: "A \<subseteq> B" and assm2: "w \<in> prestar_step A"
    obtain q q' \<alpha> \<beta> where [simp]: "w = (q, Nt \<alpha>, q')" and [simp]: "(\<alpha>, \<beta>) \<in> P" and "q' \<in> steps A \<beta> q"
      using assm2 prestar_step_def by (smt (verit, best) mem_Collect_eq)
    then have "q' \<in> steps B \<beta> q"
      using nfa_mono[of A B] assm1 by blast
    then show "w \<in> prestar_step B"
      unfolding prestar_step_def by force
  qed
  then show ?thesis
    by (intro monoI, blast)
qed



lemma finite_univ_tuple[intro]:
  assumes "finite (UNIV::'a set)" and "finite (UNIV::'b set)"
  shows "finite (UNIV::('a \<times> 'b) set)"
  by (simp add: assms(1,2) finite_Prod_UNIV)

lemma prestar_while_terminates:
  fixes T\<^sub>0 :: "('s \<times> ('n, 't) sym \<times> 's) set"
  assumes "finite (UNIV::'s set)"
  shows "\<exists>T. prestar_while T\<^sub>0 = Some T"
proof -
  have "finite ({ Nt x | x::'n. True } \<union> { Tm x | x::'t. True })"
  proof (rule finite_UnI)
    have "inj_on (\<lambda>x. (Nt x::('n, 't) sym)) (UNIV::'n set)"
      by (rule injI, simp)
    moreover have "finite (UNIV::'n set)"
      using CFG_axioms by (simp add: CFG_def)
    ultimately show "finite ({ Nt x | x. True }::('n, 't) sym set)"
      using finite_image_iff by (simp add: full_SetCompr_eq)
  next
    have "inj_on (\<lambda>x. (Tm x::('n, 't) sym)) (UNIV::'t set)"
      by (rule injI, simp)
    moreover have "finite (UNIV::'t set)"
      using CFG_axioms by (simp add: CFG_def)
    ultimately show "finite ({ Tm x | x. True }::('n, 't) sym set)"
      using finite_image_iff by (simp add: full_SetCompr_eq)
  qed
  then have "finite (UNIV::('n, 't) sym set)"
    by (smt (verit, ccfv_threshold) UNIV_eq_I Un_def mem_Collect_eq sym.exhaust)
  then have "finite (UNIV::('s \<times> ('n, 't) sym \<times> 's) set)"
    using assms by blast
  then have "finite (UNIV::(('s \<times> ('n, 't) sym \<times> 's) set) set)"
    by (simp add: Finite_Set.finite_set)
  moreover have "T\<^sub>0 \<le> T\<^sub>0 \<union> prestar_step T\<^sub>0"
    by simp
  ultimately show ?thesis
    unfolding prestar_while_def
    using prestar_step_mono by (intro while_option_finite_increasing_Some; simp_all)
qed

lemma prestar_while_fixpoint:
  assumes "prestar_while T\<^sub>0 = Some T"
  shows "T \<union> prestar_step T = T"
proof -
  have "\<not> (T \<union> prestar_step T \<noteq> T)"
    by (insert assms[unfolded prestar_while_def], rule while_option_stop)
  then have "T \<union> prestar_step T = T"
    by simp
  then show ?thesis .
qed

subsection\<open>Saturation\<close>

lemma prestar_saturated_step:
  assumes "X\<^sub>1 \<Rightarrow> X\<^sub>2" and "q' \<in> steps T\<^sub>0 X\<^sub>2 q"
  shows "q' \<in> steps (T\<^sub>0 \<union> prestar_step T\<^sub>0) X\<^sub>1 q"
proof -
  define T where [simp]: "T \<equiv> T\<^sub>0 \<union> prestar_step T\<^sub>0"
  obtain \<alpha> w\<^sub>1 w\<^sub>2 \<beta> where X\<^sub>1_def: "X\<^sub>1 = \<alpha>@[Nt w\<^sub>1]@\<beta>" and X\<^sub>2_def: "X\<^sub>2 = \<alpha>@w\<^sub>2@\<beta>" and "(w\<^sub>1, w\<^sub>2) \<in> P"
    by (metis (mono_tags, opaque_lifting) assms(1) prods_to_lts.cases step_relp_def transition_relation_def)
  obtain s s' where "s \<in> steps T\<^sub>0 \<alpha> q" and "s' \<in> steps T\<^sub>0 w\<^sub>2 s" and "q' \<in> steps T\<^sub>0 \<beta> s'"
    using Steps_split3 assms(2) X\<^sub>2_def by fastforce
  then have "(s, Nt w\<^sub>1, s') \<in> prestar_step T\<^sub>0"
    unfolding prestar_step_def using \<open>(w\<^sub>1, w\<^sub>2) \<in> P\<close> by blast
  then have "(s, Nt w\<^sub>1, s') \<in> T"
    by simp
  then have "s' \<in> steps T [Nt w\<^sub>1] s"
    by (simp add: Steps_def Step_def step_def)
  moreover have "s \<in> steps T \<alpha> q"
    using \<open>s \<in> steps T\<^sub>0 \<alpha> q\<close> T_def nfa_mono[of T\<^sub>0 T] by blast
  moreover have "q' \<in> steps T \<beta> s'"
    using \<open>q' \<in> steps T\<^sub>0 \<beta> s'\<close> T_def nfa_mono[of T\<^sub>0 T] by blast
  ultimately have "q' \<in> steps T (\<alpha>@[Nt w\<^sub>1]@\<beta>) q"
    using Steps_join3 by fast
  then show ?thesis
    using X\<^sub>1_def by simp
qed

lemma prestar_saturated:
  assumes "X\<^sub>1 \<Rightarrow> X\<^sub>2" and "q' \<in> steps T X\<^sub>2 q"
    and "prestar_while T\<^sub>0 = Some T"
  shows "q' \<in> steps T X\<^sub>1 q"
proof -
  have "T \<union> prestar_step T = T"
    using prestar_while_fixpoint assms(3) by blast
  moreover have "q' \<in> steps (T \<union> prestar_step T) X\<^sub>1 q"
    using assms prestar_saturated_step by fast
  ultimately show ?thesis
    by simp
qed

lemma prestar_saturated_lang:
  assumes "prestar_while T\<^sub>0 = Some T"
  shows "pre_star (lang' T\<^sub>0 s F) \<subseteq> lang' T s F"
proof (standard)
  fix w
  assume "w \<in> pre_star (lang' T\<^sub>0 s F)"
  then obtain w' where "w \<Rightarrow>\<^sup>* w'" and "w' \<in> lang' T\<^sub>0 s F"
    unfolding pre_star_def by blast
  then show "w \<in> lang' T s F"
  proof (induction rule: converse_rtranclp_induct[where r="(\<Rightarrow>)"])
    case base
    moreover have "T\<^sub>0 \<subseteq> T"
      by (simp add: assms prestar_while_mono)
    ultimately show ?case
      using nfa_lang_mono[of T\<^sub>0 T s F] by blast
  next
    case (step y z)
    then have "z \<in> lang' T s F"
      by simp
    then obtain q\<^sub>f where "q\<^sub>f \<in> steps T z s" and "q\<^sub>f \<in> F"
      unfolding lang'_def by fastforce
    then have "q\<^sub>f \<in> steps T y s" and "q\<^sub>f \<in> F"
      using assms step(1) prestar_saturated[of y z q\<^sub>f T s] by simp+
    then show ?case
      unfolding lang'_def by fastforce
  qed
qed



lemma prestar_triple_trans[trans]:
  assumes "A \<subseteq> pre_star B"
    and "B \<subseteq> pre_star C"
  shows "A \<subseteq> pre_star C"
proof -
  have "\<forall>w \<in> A. \<exists>w' \<in> B. w \<Rightarrow>\<^sup>* w'"
    using assms(1) pre_star_def by blast
  moreover have "\<forall>w \<in> B. \<exists>w' \<in> C. w \<Rightarrow>\<^sup>* w'"
    using assms(2) pre_star_def by blast
  ultimately have "\<forall>w \<in> A. \<exists>w' \<in> C. w \<Rightarrow>\<^sup>* w'"
    using rtranclp_trans by fast
  then show ?thesis
    unfolding pre_star_def by blast
qed

lemma prestar_saturator: "lang' (T \<union> prestar_step T) s F \<subseteq> pre_star (lang' T s F)"
proof (standard)
  fix w
  assume "w \<in> lang' (T \<union> prestar_step T) s F"
  then show "w \<in> pre_star (lang' T s F)"
  proof (induction w arbitrary: s)
    case Nil
    then have "[] \<in> lang' T s F"
      by (simp add: lang'_def Steps_def)
    moreover have "[] \<Rightarrow>\<^sup>* []"
      by simp
    ultimately show ?case
      unfolding pre_star_def by blast
  next
    case (Cons w ws)
    then have "[w]@ws \<in> lang' (T \<union> prestar_step T) s F"
      by simp
    then obtain s' where s'_step: "s' \<in> steps (T \<union> prestar_step T) [w] s"
        and "ws \<in> lang' (T \<union> prestar_step T) s' F"
      by (rule nfa_lang_split, simp)
    then have "ws \<in> pre_star (lang' T s' F)"
      by (simp add: Cons(1))
    then obtain ws' where "ws \<Rightarrow>\<^sup>* ws'" and ws'_lang: "ws' \<in> lang' T s' F"
      unfolding pre_star_def by blast

    have "(s, w, s') \<in> T \<or> (s, w, s') \<in> prestar_step T"
      using s'_step by (simp add: Steps_def Step_def step_def)
    then show ?case
    proof (standard)
      assume "(s, w, s') \<in> T"
      then have "s' \<in> step T w s"
        by (simp add: step_def)
      then have "s' \<in> steps T [w] s"
        by (simp add: Steps_def Step_def)
      moreover note \<open>ws' \<in> lang' T s' F\<close>
      ultimately have "(w#ws') \<in> lang' T s F"
        using nfa_lang_trans by fastforce
      then show "(w#ws) \<in> pre_star (lang' T s F)"
        unfolding pre_star_def using \<open>ws \<Rightarrow>\<^sup>* ws'\<close> derives_Cons derives_eq by blast
    next
      assume "(s, w, s') \<in> prestar_step T"
      then obtain A \<beta> where "w = Nt A" and "(A, \<beta>) \<in> P" and "s' \<in> steps T \<beta> s"
        unfolding prestar_step_def by blast
      moreover note \<open>ws' \<in> lang' T s' F\<close>
      ultimately have "(\<beta>@ws') \<in> lang' T s F"
        using nfa_lang_trans by fastforce
      moreover have "(w#ws) \<Rightarrow>\<^sup>* (\<beta>@ws')"
        using \<open>w = Nt A\<close> \<open>(A, \<beta>) \<in> P\<close> \<open>ws \<Rightarrow>\<^sup>* ws'\<close>
        by (meson derives_Cons_rule derives_eq derives_prepend)
      ultimately show "(w#ws) \<in> pre_star (lang' T s F)"
        unfolding pre_star_def by blast
    qed
  qed
qed

lemma prestar_saturator_lang:
  assumes "prestar_while T\<^sub>0 = Some T"
  shows "lang' T s F \<subseteq> pre_star (lang' T\<^sub>0 s F)"
  unfolding prestar_while_def
proof (rule while_option_rule[where P = "\<lambda>T. lang' T s F \<subseteq> pre_star (lang' T\<^sub>0 s F)", OF _ assms[unfolded prestar_while_def]])
  show "lang' T\<^sub>0 s F \<subseteq> pre_star (lang' T\<^sub>0 s F)"
    unfolding pre_star_def by blast
next
  fix T
  assume "lang' T s F \<subseteq> pre_star (lang' T\<^sub>0 s F)"
    and "T \<union> prestar_step T \<noteq> T"
  moreover have "lang' (T \<union> prestar_step T) s F \<subseteq> pre_star (lang' T s F)"
    by (rule prestar_saturator)
  ultimately show "lang' (T \<union> prestar_step T) s F \<subseteq> pre_star (lang' T\<^sub>0 s F)"
    using prestar_triple_trans by blast
qed

subsection\<open>Correctness\<close>

lemma prestar_while_lang:
  assumes "prestar_while T\<^sub>0 = Some T"
  shows "lang' T s F = pre_star (lang' T\<^sub>0 s F)"
  using prestar_saturated_lang prestar_saturator_lang assms by fast

definition prestar_nfa :: "('s, ('n, 't) sym) nfa \<Rightarrow> ('s, ('n, 't) sym) nfa" where
  "prestar_nfa M \<equiv> (
    case prestar_while (transitions M) of
      Some t \<Rightarrow> M \<lparr> transitions := t \<rparr> |
      None \<Rightarrow> undefined
  )"

theorem prestar_nfa_lang:
  fixes M :: "('s, ('n, 't) sym) nfa"
  assumes "finite (UNIV::'s set)"
  shows "lang (prestar_nfa M) = pre_star (lang M)"
proof -
  define T\<^sub>0 where [simp]: "T\<^sub>0 = transitions M"
  define M' where [simp]: "M' = prestar_nfa M"
  define T where [simp]: "T = transitions M'"

  have "\<exists>T. prestar_while T\<^sub>0 = Some T"
    using assms by (rule prestar_while_terminates)
  then have "prestar_while T\<^sub>0 = Some T"
    by (auto simp: prestar_nfa_def)
  moreover have "start M = start M'" and "finals M = finals M'"
    unfolding M'_def prestar_nfa_def using calculation by simp+
  ultimately show ?thesis
    by (simp add: prestar_while_lang)
qed

end \<comment>\<open>end-context CFG\<close>

end \<comment>\<open>end-theory Algorithm\<close>
