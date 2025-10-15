section\<open>Reduced Complexity for Grammars in CNF\<close>

theory ImprovedAlgorithm
  imports Algorithm Context_Free_Grammar.Chomsky_Normal_Form
begin \<comment>\<open>begin-theory ImprovedAlgorithm\<close>

text\<open>
  Bouajjani et al. have proposed in \<^cite>\<open>bouajjani2000efficient\<close> an improved algorithm
  for grammars in extended Chomsky Normal Form.
\<close>

text\<open>
  This theory proves core properties (correctness and termination) of the algorithm.
\<close>

subsection\<open>Preliminaries\<close>

text \<open>Extended Chomsky Normal Form:\<close>

definition CNF1 :: "('n, 't) Prods \<Rightarrow> bool" where
  "CNF1 P \<equiv> (\<forall>(A, \<beta>) \<in> P.
    \<comment>\<open>1. \<open>A \<rightarrow> \<epsilon>\<close>\<close>
    (\<beta> = []) \<or>
    \<comment>\<open>2. \<open>A \<rightarrow> a\<close>\<close>
    (\<exists>a. \<beta> = [Tm a]) \<or>
    \<comment>\<open>3. \<open>A \<rightarrow> B\<close>\<close>
    (\<exists>B. \<beta> = [Nt B]) \<or>
    \<comment>\<open>4. \<open>A \<rightarrow> BC\<close>\<close>
    (\<exists>B C. \<beta> = [Nt B, Nt C])
  )"

type_synonym ('s, 'n, 't) tran = "'s \<times> ('n, 't) sym \<times> 's" \<comment>\<open>single transition\<close>
type_synonym ('s, 'n, 't) trans = "('s, 'n, 't) tran set" \<comment>\<open>set of transitions\<close>
type_synonym ('s, 'n, 't) directT = "('s, 'n, 't) tran \<Rightarrow> ('s, 'n, 't) trans"
type_synonym ('s, 'n, 't) implT = "('s, 'n, 't) tran \<Rightarrow> (('s, 'n, 't) tran \<times> ('s, 'n, 't) tran) set"

record ('s, 'n, 't) alg_state =
  rel :: "('s, 'n, 't) trans"
  trans :: "('s, 'n, 't) trans"
  direct :: "('s, 'n, 't) directT"
  impl :: "('s, 'n, 't) implT"

subsection\<open>Procedure\<close>

definition alg_state_new :: "('n, 't) Prods \<Rightarrow> 's set \<Rightarrow> ('s, 'n, 't) trans \<Rightarrow> ('s, 'n, 't) alg_state" where
  "alg_state_new P Q \<delta> \<equiv> \<lparr>                                                             
    rel = {},
    trans = \<delta>
      \<union> { (q, Nt A, q) | q A. (A, []) \<in> P \<and> q \<in> Q }
      \<union> { (q, Nt A, q') | q q' A. \<exists>a. (A, [Tm a]) \<in> P \<and> (q, Tm a, q') \<in> \<delta> \<and> q \<in> Q \<and> q' \<in> Q },
    direct = (\<lambda>(q, X, q'). case X of
      Nt B \<Rightarrow> { (q, Nt A, q') | A. (A, [Nt B]) \<in> P \<and> q \<in> Q \<and> q' \<in> Q } |
      Tm b \<Rightarrow> {}
    ),
    impl = (\<lambda>(q, X, q'). case X of
      Nt B \<Rightarrow> { ((q', Nt C, q''), (q, Nt A, q'')) | q'' A C. (A, [Nt B, Nt C]) \<in> P \<and> q \<in> Q \<and> q' \<in> Q \<and> q'' \<in> Q } |
      Tm b \<Rightarrow> {}
    )
  \<rparr>"

definition alg_inner_pre :: "('s, 'n, 't) alg_state \<Rightarrow> ('s, 'n, 't) tran \<Rightarrow> ('s, 'n, 't) alg_state" where
  "alg_inner_pre S t \<equiv> S \<lparr>
    \<comment>\<open>\<open>t\<close> is added to \<open>rel\<close>:\<close>
    rel := (rel S) \<union> {t},
    \<comment>\<open>\<open>t\<close> is removed, and \<open>direct(t)\<close> is added to \<open>trans\<close>:\<close>
    trans := ((trans S) - {t}) \<union> direct S t,
    \<comment>\<open>\<open>direct(t)\<close> is cleared:\<close>
    direct := (direct S) (t := {})
  \<rparr>"

definition alg_inner_post :: "('s, 'n, 't) alg_state \<Rightarrow> ('s, 'n, 't) tran \<Rightarrow> ('s, 'n, 't) alg_state" where
  "alg_inner_post S t \<equiv> (
    let i = impl S t in
    S \<lparr>
      \<comment>\<open>If \<open>(t', t'') \<in> impl(t)\<close> and \<open>t' \<in> rel\<close>, then \<open>t'' \<in> trans\<close>:\<close>
      trans := (trans S) \<union>
        snd ` { (t', t'') \<in> i. t' \<in> rel S },
      \<comment>\<open>If \<open>(t', t'') \<in> impl(t)\<close> and \<open>t' \<notin> rel\<close>, then \<open>t'' \<in> direct(t')\<close>:\<close>
      direct := (\<lambda>t'. direct S t' \<union>
        snd ` { (t'2, t'') \<in> i. t' = t'2 \<and> t' \<notin> rel S }
      ),
      \<comment>\<open>Inner while-loop removes everything from \<open>impl(t)\<close>:\<close>
      impl := (impl S) (t := {})
    \<rparr>
  )"

definition alg_outer_step :: "('s, 'n, 't) alg_state \<Rightarrow> ('s, 'n, 't) tran \<Rightarrow> ('s, 'n, 't) alg_state" where
  "alg_outer_step S t \<equiv> alg_inner_post (alg_inner_pre S t) t"

abbreviation "alg_outer_step_rel S t \<equiv> rel S \<union> {t}"
abbreviation "alg_outer_step_trans S t \<equiv> (trans S) - {t} \<union> direct S t \<union> snd ` { (t', t'') \<in> impl S t. t' \<in> rel S \<union> {t} }"
abbreviation "alg_outer_step_trans' S t \<equiv> (trans S) - {t} \<union> direct S t \<union> {t''. \<exists>t'. (t', t'') \<in> impl S t \<and> t' \<in> rel S \<union> {t} }"
abbreviation "alg_outer_step_direct S t \<equiv> (\<lambda>t'. ((direct S) (t := {})) t' \<union> snd ` { (t'2, t'') \<in> impl S t. t' = t'2 \<and> t' \<notin> (rel S) \<union> {t} })"
abbreviation "alg_outer_step_direct' S t \<equiv> (\<lambda>t'. ((direct S) (t := {})) t' \<union> {t''. (t', t'') \<in> impl S t \<and> t' \<notin> (rel S) \<union> {t} })"
abbreviation "alg_outer_step_impl S t \<equiv> (impl S) (t := {})"

lemma alg_outer_step_trans_eq[simp]:
  "alg_outer_step_trans S t = alg_outer_step_trans' S t"
  by (standard; force)

lemma alg_outer_step_direct_eq[simp]:
  "alg_outer_step_direct S t = alg_outer_step_direct' S t"
  by force

lemma alg_outer_step_simps[simp]:
  shows "rel (alg_outer_step S t) = alg_outer_step_rel S t"
    and "trans (alg_outer_step S t) = alg_outer_step_trans S t"
    and "direct (alg_outer_step S t) = alg_outer_step_direct S t"
    and "impl (alg_outer_step S t) = alg_outer_step_impl S t"
proof -
  define R where "R \<equiv> rel S \<union> {t}"
  define T where "T \<equiv> ((trans S) - {t}) \<union> direct S t" 
  define D where "D \<equiv> (direct S) (t := {})"
  define I where "I \<equiv> impl S"
  note defs = R_def T_def D_def I_def

  have R_subst: "rel (alg_inner_pre S t) = R"
    by (simp add: R_def alg_inner_pre_def)
  have T_subst: "trans (alg_inner_pre S t) = T"
    by (simp add: T_def alg_inner_pre_def)
  have D_subst: "direct (alg_inner_pre S t) = D"
    by (simp add: D_def alg_inner_pre_def)
  have I_subst: "impl (alg_inner_pre S t) = I"
    by (simp add: I_def alg_inner_pre_def)
  note substs = R_subst T_subst D_subst I_subst

  have "rel (alg_inner_post (alg_inner_pre S t) t) = R \<union> {t}"
    unfolding alg_inner_post_def substs
    by (metis (no_types, lifting) R_def R_subst Un_absorb Un_insert_right alg_state.select_convs(1) alg_state.surjective alg_state.update_convs(2,3,4) sup_bot.right_neutral)
  then show "rel (alg_outer_step S t) = rel S \<union> {t}"
    by (simp add: substs defs alg_outer_step_def)

  have "trans (alg_inner_post (alg_inner_pre S t) t) = T \<union> snd ` { (t', t'') \<in> I t. t' \<in> R }"
    unfolding alg_inner_post_def substs
    by (metis (no_types, lifting) alg_state.select_convs(2) alg_state.surjective alg_state.update_convs(2,3,4))
  then show "trans (alg_outer_step S t) = alg_outer_step_trans S t"
    by (simp add: substs defs alg_outer_step_def)

  have "direct (alg_inner_post (alg_inner_pre S t) t) = (\<lambda>t'. D t' \<union> snd ` { (t'2, t'') \<in> I t. t' = t'2 \<and> t' \<notin> R })"
    unfolding alg_inner_post_def substs
    using alg_state.select_convs(3) alg_state.surjective alg_state.update_convs(1,2,3,4)
  proof -
    have "\<forall>p. direct (alg_inner_pre S t \<lparr>trans := T \<union> snd ` {(pa, p). (pa, p) \<in> I t \<and> pa \<in> R}, direct := \<lambda>p. D p \<union> snd ` {(pb, pa). (pb, pa) \<in> I t \<and> p = pb \<and> p \<notin> R}, impl := I(t := {})\<rparr>) p = D p \<union> snd ` {(pb, pa). (pb, pa) \<in> I t \<and> p = pb \<and> p \<notin> R}"
      by simp
    then show "direct (let r = I t in alg_inner_pre S t \<lparr>trans := T \<union> snd ` {(pa, p). (pa, p) \<in> r \<and> pa \<in> R}, direct := \<lambda>p. D p \<union> snd ` {(pb, pa). (pb, pa) \<in> r \<and> p = pb \<and> p \<notin> R}, impl := I(t := {})\<rparr>) = (\<lambda>p. D p \<union> snd ` {(pb, pa). (pb, pa) \<in> I t \<and> p = pb \<and> p \<notin> R})"
      by meson
  qed
  then show "direct (alg_outer_step S t) = alg_outer_step_direct S t"
    by (simp add: substs defs alg_outer_step_def)

  have "impl (alg_inner_post (alg_inner_pre S t) t) = I (t := {})"
    unfolding alg_inner_post_def substs
    by (metis (no_types, lifting) alg_state.select_convs(4) alg_state.surjective alg_state.update_convs(4))
  then show "impl (alg_outer_step S t) = alg_outer_step_impl S t"
    by (simp add: substs defs alg_outer_step_def)
qed

definition alg_outer :: "('s, 'n, 't) alg_state \<Rightarrow> ('s, 'n, 't) alg_state option" where
  "alg_outer \<equiv> while_option (\<lambda>S. trans S \<noteq> {}) (\<lambda>S. alg_outer_step S (SOME x. x \<in> trans S))"

lemma alg_outer_rule:
  assumes "\<And>S x. P S \<Longrightarrow> x \<in> trans S \<Longrightarrow> P (alg_outer_step S x)"
    and "alg_outer S = Some S'"
  shows  "P S \<Longrightarrow> P S'"
proof -
  let ?b = "\<lambda>S. trans S \<noteq> {}"
  let ?c = "\<lambda>S. alg_outer_step S (SOME x. x \<in> trans S)"
  have "\<And>S. P S \<Longrightarrow> trans S \<noteq> {} \<Longrightarrow> P (alg_outer_step S (SOME x. x \<in> trans S))"
    by (simp add: assms some_in_eq)
  with assms(2) show "P S \<Longrightarrow> P S'"
    unfolding alg_outer_def using while_option_rule[where b="?b" and c="?c"] by blast
qed

subsection\<open>Correctness\<close>

subsubsection\<open>Subset\<close>

definition prestar_alg_sub_inv :: "('s, 'n, 't) trans \<Rightarrow> ('s, 'n, 't) alg_state \<Rightarrow> bool" where
  "prestar_alg_sub_inv \<delta>' S \<equiv> (
    (trans S) \<subseteq> \<delta>' \<and> (rel S) \<subseteq> \<delta>' \<and>
    (\<forall>t' \<in> \<delta>'. \<forall>t \<in> direct S t'. t \<in> \<delta>') \<and>
    (\<forall>t \<in> \<delta>'. \<forall>(t', t'') \<in> impl S t. t' \<in> \<delta>' \<longrightarrow> t'' \<in> \<delta>')
  )"

lemma alg_state_new_inv:
  assumes "prestar_while P Q \<delta> = Some \<delta>'"
  shows "prestar_alg_sub_inv \<delta>' (alg_state_new P Q \<delta>)"
proof -
  define S where "S = alg_state_new P Q \<delta>"

  have invR: "(rel S) \<subseteq> \<delta>'"
    by (simp add: S_def alg_state_new_def)

  have invT: "(trans S) \<subseteq> \<delta>'"
  proof (simp add: S_def alg_state_new_def, intro conjI)
    show "\<delta> \<subseteq> \<delta>'"
      using assms by (rule prestar_while_mono)
  next
    have "\<And>A q. (A, []) \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> (q, Nt A, q) \<in> \<delta>'"
      by (rule prestar_while_refl[of P Q \<delta>]; use assms in blast)
    then show "{(q, Nt A, q) |q A. (A, []) \<in> P \<and> q \<in> Q} \<subseteq> \<delta>'"
      by blast
  next
    have "\<And>A a q q'. (A, [Tm a]) \<in> P \<Longrightarrow> q \<in> Q \<Longrightarrow> q' \<in> Q \<Longrightarrow> (q, Tm a, q') \<in> \<delta> \<Longrightarrow> (q, Nt A, q') \<in> \<delta>'"
      by (rule prestar_while_singleton[of P]; use assms prestar_while_mono in blast)
    then show "{(q, Nt A, q') |q q' A. \<exists>a. (A, [Tm a]) \<in> P \<and> (q, Tm a, q') \<in> \<delta> \<and> q \<in> Q \<and> q' \<in> Q} \<subseteq> \<delta>'"
      by blast
  qed

  have "\<And>q q' X t. (q, X, q') \<in> \<delta>' \<Longrightarrow> t \<in> direct S (q, X, q') \<Longrightarrow> t \<in> \<delta>'"
  proof -
    fix t and q X q'
    assume "(q, X, q') \<in> \<delta>'" and t_in: "t \<in> direct S (q, X, q')"
    show "t \<in> \<delta>'" proof (cases X)
      case (Nt B)
      then have "direct S (q, X, q') = { (q, Nt A, q') | A. (A, [Nt B]) \<in> P \<and> q \<in> Q \<and> q' \<in> Q }"
        by (simp add: S_def alg_state_new_def)
      then obtain A where t_split: "t = (q, Nt A, q')"
          and "(A, [Nt B]) \<in> P"
          and inQ: "q \<in> Q \<and> q' \<in> Q"
        using prod_cases3 t_in by auto
      moreover have "(q, Nt B, q') \<in> \<delta>'"
        using \<open>(q, X, q') \<in> \<delta>'\<close> Nt by blast
      moreover note assms
      ultimately have "(q, Nt A, q') \<in> \<delta>'"
        by (intro prestar_while_singleton) (use inQ in blast)+
      then show ?thesis
        by (simp add: t_split)
    next
      case (Tm b)
      then have "direct S (q, X, q') = {}"
        by (simp add: S_def alg_state_new_def)
      then show ?thesis
        using t_in by blast
    qed
  qed
  then have invD: "\<forall>t' \<in> \<delta>'. \<forall>t \<in> direct S t'. t \<in> \<delta>'"
    by fast

  have "\<And>t t' t''. t \<in> \<delta>' \<Longrightarrow> (t', t'') \<in> impl S t \<Longrightarrow> t' \<in> \<delta>' \<Longrightarrow> t'' \<in> \<delta>'"
  proof -
    fix t t' t''
    assume "t \<in> \<delta>'" and "(t', t'') \<in> impl S t" and "t' \<in> \<delta>'"
    obtain q q' X\<^sub>1 where t_split: "t = (q, X\<^sub>1, q')"
      by (elim prod_cases3)
    show "t'' \<in> \<delta>'" proof (cases X\<^sub>1)
      case (Nt B)
      have "impl S t = {((q', Nt C, q''), (q, Nt A, q'')) |q'' A C.
          (A, [Nt B, Nt C]) \<in> P \<and> q \<in> Q \<and> q' \<in> Q \<and> q'' \<in> Q}"
        by (simp add: S_def t_split Nt alg_state_new_def)
      then obtain q'' A C where t'_split: "t' = (q', Nt C, q'')"
          and t''_split: "t'' = (q, Nt A, q'')" and "(A, [Nt B, Nt C]) \<in> P"
          and inQ: "q \<in> Q \<and> q' \<in> Q &   q'' \<in> Q"
        using \<open>(t', t'') \<in> impl S t\<close> by force

      note \<open>(A, [Nt B, Nt C]) \<in> P\<close> and assms
      moreover have "(q', Nt C, q'') \<in> \<delta>'"
        using \<open>t' \<in> \<delta>'\<close> by (simp add: t'_split)
      moreover have "(q, Nt B, q') \<in> \<delta>'"
        using \<open>t \<in> \<delta>'\<close> by (simp add: t_split Nt)
      ultimately have "(q, Nt A, q'') \<in> \<delta>'"
        by (intro prestar_while_impl) (use inQ in blast)+
      then show ?thesis
        unfolding t''_split by assumption
    next
      case (Tm b)
      have "impl S t = {}"
        by (simp add: S_def t_split Tm alg_state_new_def)
      then show ?thesis
        using \<open>(t', t'') \<in> impl S t\<close> by simp
    qed
  qed
  then have invI: "\<forall>t \<in> \<delta>'. \<forall>(t', t'') \<in> impl S t. t' \<in> \<delta>' \<longrightarrow> t'' \<in> \<delta>'"
    by fast

  from invR invT invD invI show ?thesis
    unfolding prestar_alg_sub_inv_def S_def by blast
qed

lemma alg_outer_step_inv:
  assumes "prestar_while P Q \<delta> = Some \<delta>'" and "t \<in> trans S" and "prestar_alg_sub_inv \<delta>' S"
  shows "prestar_alg_sub_inv \<delta>' (alg_outer_step S t)"
proof -
  note inv[simp] = assms(3)[unfolded prestar_alg_sub_inv_def]
  have [simp]: "t \<in> \<delta>'"
    using assms(2) assms(3) unfolding prestar_alg_sub_inv_def by blast
  moreover have invi: "\<forall>(t', t'') \<in> impl (alg_outer_step S t) t. t' \<in> \<delta>' \<longrightarrow> t'' \<in> \<delta>'"
    by simp
  moreover have invR: "rel (alg_outer_step S t) \<subseteq> \<delta>'"
    by simp
  moreover have invT: "trans (alg_outer_step S t) \<subseteq> \<delta>'"
    unfolding alg_outer_step_simps(2) alg_outer_step_trans_eq 
    using inv invi \<open>t \<in> \<delta>'\<close> by blast
  moreover have invD: "\<forall>t' \<in> \<delta>'. \<forall>t \<in> direct (alg_outer_step S t) t'. t \<in> \<delta>'"
    unfolding alg_outer_step_simps(3) alg_outer_step_direct_eq using inv invi \<open>t \<in> \<delta>'\<close>
    by (metis (no_types, lifting) Un_iff case_prod_conv empty_iff fun_upd_apply mem_Collect_eq)
  moreover have invI: "\<forall>t\<^sub>2 \<in> \<delta>'. \<forall>(t', t'') \<in> impl (alg_outer_step S t) t\<^sub>2. t' \<in> \<delta>' \<longrightarrow> t'' \<in> \<delta>'"
    by simp
  ultimately show ?thesis
    unfolding prestar_alg_sub_inv_def by blast
qed

lemma alg_outer_inv:
  assumes "prestar_while P Q \<delta> = Some \<delta>'" and "prestar_alg_sub_inv \<delta>' S"
    and "alg_outer S = Some S'"
  shows "prestar_alg_sub_inv \<delta>' S'"
proof -
  note assms' = assms(1,2) assms(3)[unfolded alg_outer_def]
  have "\<And>s. prestar_alg_sub_inv \<delta>' s \<Longrightarrow> trans s \<noteq> {} \<Longrightarrow>
      prestar_alg_sub_inv \<delta>' (alg_outer_step s (SOME x. x \<in> trans s))"
    by (rule alg_outer_step_inv; use assms someI_ex in fast)
  then show ?thesis
    by (rule while_option_rule[where P="prestar_alg_sub_inv \<delta>'"]) (use assms' in blast)+
qed

lemma prestar_alg_sub:
  fixes P and \<delta>
  assumes "alg_outer (alg_state_new P Q \<delta>) = Some S'" and "prestar_while P Q \<delta> = Some \<delta>'"
  shows "rel S' \<subseteq> \<delta>'"
proof -
  have "prestar_alg_sub_inv \<delta>' (alg_state_new P Q \<delta>)"
    using assms by (elim alg_state_new_inv)
  with assms have "prestar_alg_sub_inv \<delta>' S'"
    by (intro alg_outer_inv[where S="alg_state_new P Q \<delta>" and \<delta>'=\<delta>' and S'=S']; simp)
  then show ?thesis
    unfolding prestar_alg_sub_inv_def by blast
qed

subsubsection\<open>Super-Set\<close>

lemma alg_outer_fixpoint: "alg_outer S = Some S' \<Longrightarrow> alg_outer S' = Some S'"
  unfolding alg_outer_def by (metis (lifting) while_option_stop while_option_unfold)

lemma prestar_alg_trans_empty: "alg_outer S = Some S' \<Longrightarrow> trans S' = {}"
  using while_option_stop unfolding alg_outer_def by fast

lemma alg_outer_step_direct: "t \<noteq> t' \<Longrightarrow> direct S t' \<subseteq> direct (alg_outer_step S t) t'"
  by simp

lemma alg_outer_step_impl: "(impl S) (t := {}) = impl (alg_outer_step S t)"
  by simp

lemma alg_outer_step_impl_to_trans[intro]:
  assumes "(t', t'') \<in> impl S t" and "t' \<in> rel S \<or> t = t'"
  shows "t'' \<in> trans (alg_outer_step S t)"
  using assms unfolding alg_outer_step_simps alg_outer_step_trans_eq by blast

lemma alg_outer_step_impl_to_direct[intro]:
  assumes "(t', t'') \<in> impl S t" and "t' \<notin> rel S" and "t \<noteq> t'"
  shows "t'' \<in> direct (alg_outer_step S t) t'"
  using assms unfolding alg_outer_step_simps alg_outer_step_direct_eq by blast

\<comment>\<open>Everything from \<open>trans\<close> is eventually added to \<open>rel\<close>:\<close>
lemma prestar_alg_trans_to_rel:
  assumes "alg_outer S = Some S'"
  shows "trans S \<subseteq> rel S'"
proof
  fix x
  assume "x \<in> trans S"
  have "x \<in> trans S' \<or> x \<in> rel S'"
    by (rule alg_outer_rule[where P="\<lambda>S. x \<in> trans S \<or> x \<in> rel S"]; use assms \<open>x \<in> trans S\<close> in auto)
  then show "x \<in> rel S'"
    using assms prestar_alg_trans_empty by blast
qed

\<comment>\<open>If \<open>t\<close> is added to \<open>rel\<close>, then so is \<open>direct(t)\<close>:\<close>
lemma prestar_alg_direct_to_rel:
  fixes S\<^sub>0 :: "('s, 'n, 't) alg_state"
  assumes "alg_outer S\<^sub>0 = Some S'"
    and "t \<notin> rel S\<^sub>0" and "t \<in> rel S'"
  shows "direct S\<^sub>0 t \<subseteq> rel S'"
proof -
  let ?I = "\<lambda>S. (t \<notin> rel S \<and> direct S\<^sub>0 t \<subseteq> direct S t) \<or> (direct S\<^sub>0 t \<subseteq> rel S \<union> trans S)"
  have "\<And>S t. ?I S \<Longrightarrow> t \<in> trans S \<Longrightarrow> ?I (alg_outer_step S t)"
  proof -
    fix S :: "('s, 'n, 't) alg_state" and t'
    assume assm1: "(t \<notin> rel S \<and> direct S\<^sub>0 t \<subseteq> direct S t) \<or> (direct S\<^sub>0 t \<subseteq> rel S \<union> trans S)"
      and assm2: "t' \<in> trans S"
    
    show "?I (alg_outer_step S t')"
    proof (cases "t = t'")
      case True
      then show ?thesis
        using assm1 by auto
    next
      case False
      consider "t \<notin> rel S \<and> direct S\<^sub>0 t \<subseteq> direct S t" | "direct S\<^sub>0 t \<subseteq> rel S \<union> trans S"
        using assm1 by blast
      then show ?thesis
        by (cases; auto)
    qed
  qed
  with assms have "?I S'"
    by (elim alg_outer_rule[where P="?I"]) simp+
  then show ?thesis
    using assms prestar_alg_trans_empty by blast
qed

\<comment>\<open>If \<open>t\<close> and \<open>t'\<close> are added to \<open>rel\<close>, then so are all \<open>t''\<close> from \<open>(t', t'') \<in> impl(t)\<close>:\<close>
lemma prestar_alg_impl_to_rel:
  fixes S\<^sub>0 :: "('s, 'n, 't) alg_state"
  assumes "alg_outer S\<^sub>0 = Some S'"
    and "t \<notin> rel S\<^sub>0" and "t' \<notin> rel S\<^sub>0"
    and "(t', t'') \<in> impl S\<^sub>0 t"
    and "t \<in> rel S'" and "t' \<in> rel S'"
  shows "t'' \<in> rel S'"
proof -
  let ?I = "\<lambda>S. (t \<notin> rel S \<and> (t', t'') \<in> impl S t)
      \<or> (t' \<notin> rel S \<and> t'' \<in> direct S t')
      \<or> (t'' \<in> rel S \<union> trans S)"

  have "\<And>S x. ?I S \<Longrightarrow> x \<in> trans S \<Longrightarrow> ?I (alg_outer_step S x)"
  proof -
    fix S :: "('s, 'n, 't) alg_state" and x
    assume "?I S" and "x \<in> trans S"
    then show "?I (alg_outer_step S x)"
    proof (elim disjE)
      assume assm1: "x \<in> trans S" and assm2: "t \<notin> rel S \<and> (t', t'') \<in> impl S t"
      then show "?I (alg_outer_step S x)"
      proof (cases "x = t")
        case True
        then show ?thesis
        proof (cases "t' \<in> rel S \<or> t = t'")
          case True
          with assm2 have "t'' \<in> trans (alg_outer_step S t)"
            by (intro alg_outer_step_impl_to_trans[of t' t'' S t]; simp)
          then show ?thesis
            by (simp add: \<open>x = t\<close>)
        next
          case False
          then have "t' \<notin> rel S \<union> {t}"
            using False by blast
          then have "t' \<notin> rel (alg_outer_step S t)"
            by simp
          moreover with False assm2 have "t'' \<in> direct (alg_outer_step S t) t'"
            by (intro alg_outer_step_impl_to_direct[of t' t'' S t]; simp)
          ultimately show ?thesis
            by (simp add: \<open>x = t\<close>)
        qed
      next
        case False
        then show ?thesis
          using alg_outer_step_impl assm2 by simp
      qed
    next
      assume assm1: "x \<in> trans S" and assm2: "t' \<notin> rel S \<and> t'' \<in> direct S t'"
      then show "?I (alg_outer_step S x)"
        by (cases "x = t'"; simp)
    next
      assume "x \<in> trans S" and "t'' \<in> rel S \<union> trans S"
      then show "?I (alg_outer_step S x)"
        by force
    qed
  qed
  with assms have "?I S'"
    by (elim alg_outer_rule[where P="?I"]) simp+
  then show ?thesis proof (elim disjE)
    assume "t \<notin> rel S' \<and> (t', t'') \<in> impl S' t"
    then show "t'' \<in> rel S'"
      using assms(5) by blast
  next
    assume "t' \<notin> rel S' \<and> t'' \<in> direct S' t'"
    moreover have "alg_outer S' = Some S'"
      using assms(1) by (rule alg_outer_fixpoint)
    ultimately show "t'' \<in> rel S'"
      using prestar_alg_direct_to_rel assms(6) by blast
  next
    assume " t'' \<in> rel S' \<union> trans S'"
    then show "t'' \<in> rel S'"
      using assms(1) prestar_alg_trans_empty by blast
  qed
qed

\<comment>\<open>Reflexive transitions are eventually added to \<open>rel\<close>:\<close>
lemma prestar_alg_new_refl_to_trans:
  assumes "S = alg_state_new P Q \<delta>" and "(A, []) \<in> P" and "q \<in> Q"
  shows "(q, Nt A, q) \<in> trans S"
  using assms by (simp add: alg_state_new_def)

lemma prestar_alg_refl_to_rel:
  assumes "alg_outer (alg_state_new P Q \<delta>) = Some S'" and "(A, []) \<in> P" and "q \<in> Q"
  shows "(q, Nt A, q) \<in> rel S'"
  using assms prestar_alg_new_refl_to_trans prestar_alg_trans_to_rel by fast

\<comment>\<open>Lemmas for singleton productions, i.e. \<open>A \<rightarrow> B\<close> or \<open>A \<rightarrow> b\<close>:\<close>
lemma prestar_alg_singleton_nt_to_rel:
  assumes "alg_outer (alg_state_new P Q \<delta>) = Some S'"
    and "(A, [Nt B]) \<in> P" and "q \<in> Q" and "q' \<in> Q"
  shows "(q, Nt B, q') \<in> rel S' \<Longrightarrow> (q, Nt A, q') \<in> rel S'"
proof -
  have "(q, Nt A, q') \<in> direct (alg_state_new P Q \<delta>) (q, Nt B, q')"
    using assms by (simp add: alg_state_new_def)
  moreover have "(q, Nt B, q') \<notin> rel (alg_state_new P Q \<delta>)"
    by (simp add: alg_state_new_def)
  ultimately show "(q, Nt B, q') \<in> rel S' \<Longrightarrow> (q, Nt A, q') \<in> rel S'"
    using assms(1) prestar_alg_direct_to_rel by blast
qed

lemma prestar_alg_tm_only_from_delta:
  fixes S' :: "('s, 'n, 't) alg_state"
  assumes "alg_outer (alg_state_new P Q \<delta>) = Some S'"
    and "(q, Tm b, q') \<in> rel S'" and "q \<in> Q" and "q' \<in> Q"
  shows "(q, Tm b, q') \<in> \<delta>"
proof -
  define i where "i \<equiv> (\<lambda>t. t = (q, Tm b::('n, 't) sym, q') \<longrightarrow> t \<in> \<delta>)"
  define I :: "('s, 'n, 't) alg_state \<Rightarrow> bool"
    where "I \<equiv> (\<lambda>S. (\<forall>t \<in> rel S. i t) \<and> (\<forall>t \<in> trans S. i t)
      \<and> (\<forall>t. \<forall>t' \<in> direct S t. i t') \<and> (\<forall>t. \<forall>(t', t'') \<in> impl S t. i t' \<and> i t''))"

  have "I (alg_state_new P Q \<delta>)"
    unfolding alg_state_new_def I_def i_def
    by (auto split: sym.splits intro: sym.exhaust)
  moreover have "\<And>S t. I S \<Longrightarrow> t \<in> trans S \<Longrightarrow> I (alg_outer_step S t)"
    unfolding I_def i_def alg_outer_step_simps
    by (auto split: sym.splits; blast)
  ultimately have "I S'"
    using assms(1) by (elim alg_outer_rule)
  then show ?thesis
    using assms(2) by (simp add: I_def i_def)
qed

lemma prestar_alg_singleton_tm_to_rel:
  assumes "alg_outer (alg_state_new P Q \<delta>) = Some S'" and "(A, [Tm b]) \<in> P"
    and "(q, Tm b, q') \<in> rel S'" and "q \<in> Q" and "q' \<in> Q"
  shows "(q, Nt A, q') \<in> rel S'"
proof -
  have "(q, Tm b, q') \<in> \<delta>"
    using assms prestar_alg_tm_only_from_delta by fast
  then have "(q, Nt A, q') \<in> trans (alg_state_new P Q \<delta>)"
    by (auto simp: alg_state_new_def assms)
  then show ?thesis
    using prestar_alg_trans_to_rel assms(1) by blast
qed

lemma prestar_alg_singleton_to_rel:
  assumes "alg_outer (alg_state_new P Q \<delta>) = Some S'"
    and "(A, [X]) \<in> P" and "q \<in> Q" and "q' \<in> Q"
  shows "(q, X, q') \<in> rel S' \<Longrightarrow> (q, Nt A, q') \<in> rel S'"
  using assms prestar_alg_singleton_nt_to_rel prestar_alg_singleton_tm_to_rel by (cases X; fast)

\<comment>\<open>Lemmas for dual productions, i.e. \<open>A \<rightarrow> AB\<close>:\<close>
lemma prestar_alg_dual_to_rel:
  assumes "alg_outer (alg_state_new P Q \<delta>) = Some S'" and "(A, [Nt B, Nt C]) \<in> P"
    and "(q, Nt B, q') \<in> rel S'" and "(q', Nt C, q'') \<in> rel S'"
    and "q \<in> Q" and "q' \<in> Q" and "q'' \<in> Q"
  shows "(q, Nt A, q'') \<in> rel S'"
proof -
  define S where [simp]: "S \<equiv> alg_state_new P Q \<delta>"
  have "(q, Nt B, q') \<notin> rel S" and "(q', Nt C, q'') \<notin> rel S"
    by (simp add: alg_state_new_def)+
  moreover have "((q', Nt C, q''), (q, Nt A, q'')) \<in> impl S (q, Nt B, q')"
    using assms by (simp add: alg_state_new_def)
  moreover have "alg_outer S = Some S'"
    by (simp add: assms(1))
  ultimately show ?thesis
    using assms(3,4) by (elim prestar_alg_impl_to_rel; force)
qed

lemma prestar_alg_sup:
  fixes P and \<delta> :: "('s, 'n, 't) trans" and q\<^sub>0
  defines "Q \<equiv> {q\<^sub>0} \<union> (snd ` snd ` \<delta>)"
  defines "S \<equiv> alg_state_new P Q \<delta>"
  assumes "alg_outer S = Some S'"
    and "prestar_while P Q \<delta> = Some \<delta>'"
    and "CNF1 P"
  shows "\<delta>' \<subseteq> rel S'"
proof -
  \<comment>\<open>If \<open>t \<in> \<delta>\<close>, then \<open>t\<close> is eventually added to \<open>rel\<close>:\<close>
  have base: "\<delta> \<subseteq> rel S'" and "Q = {q\<^sub>0} \<union> (snd ` snd ` \<delta>)"
  proof
    fix t 
    assume "t \<in> \<delta>"
    then have "t \<in> trans S"
      by (simp add: S_def alg_state_new_def)
    then show "t \<in> rel S'"
      using assms(3) prestar_alg_trans_to_rel by blast
  next
    show "Q = {q\<^sub>0} \<union> (snd ` snd ` \<delta>)"
      by (simp add: Q_def)
  qed

  define b where "b \<equiv> (\<lambda>\<delta>::('s, 'n, 't) trans. \<delta> \<union> prestar_step P Q \<delta> \<noteq> \<delta>)"
  define c where "c \<equiv> (\<lambda>\<delta>::('s, 'n, 't) trans. \<delta> \<union> prestar_step P Q \<delta>)"

  have "\<And>t \<delta>. Q = {q\<^sub>0} \<union> (snd ` snd ` \<delta>) \<Longrightarrow> \<delta> \<subseteq> rel S' \<Longrightarrow> t \<in> prestar_step P Q \<delta> \<Longrightarrow> t \<in> rel S'"
  proof -
    fix \<delta> and t
    assume q_reach: "Q = {q\<^sub>0} \<union> (snd ` snd ` \<delta>)" "\<delta> \<subseteq> rel S'" and t_src: "t \<in> prestar_step P Q \<delta>"
    then obtain q q' A \<beta> where t_split: "t = (q, Nt A, q')" and "(A, \<beta>) \<in> P" and "q' \<in> steps \<delta> \<beta> q"
      unfolding prestar_step_def by blast
    moreover have q_in: "q \<in> Q \<and> q' \<in> Q"
      using t_src calculation by (auto simp: prestar_step_def)
    ultimately consider "\<beta> = []" | "\<exists>X. \<beta> = [X]" | "\<exists>B C. \<beta> = [Nt B, Nt C]"
      using assms(5)[unfolded CNF1_def] by fast
    then have "(q, Nt A, q') \<in> rel S'" proof (cases)
      case 1
      then have "q = q'"
        using \<open>q' \<in> steps \<delta> \<beta> q\<close> by (simp add: Steps_def)
      moreover have "(A, []) \<in> P"
        using \<open>(A, \<beta>) \<in> P\<close>[unfolded 1] by assumption
      ultimately show ?thesis
        using assms(2,3) q_in prestar_alg_refl_to_rel by fast
    next
      case 2
      then obtain X where \<beta>_split: "\<beta> = [X]"
        by blast
      then have "(q, X, q') \<in> rel S'"
        using \<open>q' \<in> steps \<delta> \<beta> q\<close> \<open>\<delta> \<subseteq> rel S'\<close> by (auto simp: Steps_def Step_def step_def)
      moreover have "(A, [X]) \<in> P"
        using \<open>(A, \<beta>) \<in> P\<close>[unfolded \<beta>_split] by assumption
      ultimately show ?thesis
        using assms(2,3) q_in prestar_alg_singleton_to_rel by fast
    next
      case 3
      then obtain B C where \<beta>_split: "\<beta> = [Nt B, Nt C]"
        by blast
      then obtain q'' where  "q' \<in> steps \<delta> [Nt C] q''" and "q'' \<in> steps \<delta> [Nt B] q"
        using \<beta>_split \<open>q' \<in> steps \<delta> \<beta> q\<close> Steps_split by force
      then have "(q, Nt B, q'') \<in> rel S'" and "(q'', Nt C, q') \<in> rel S'"
        using \<open>q' \<in> steps \<delta> \<beta> q\<close> \<open>\<delta> \<subseteq> rel S'\<close> by (auto simp: Steps_def Step_def step_def)
      moreover have "(q, Nt B, q'') \<in> \<delta>"
        using \<open>q'' \<in> steps \<delta> [Nt B] q\<close> by (auto simp: Steps_def Step_def step_def)
      moreover have "q'' \<in> Q"
        using calculation unfolding q_reach by force
      moreover have "(A, [Nt B, Nt C]) \<in> P"
        using \<open>(A, \<beta>) \<in> P\<close>[unfolded \<beta>_split] by assumption
      ultimately show ?thesis
        using assms(2,3) q_in prestar_alg_dual_to_rel by fast
    qed
    then show "t \<in> rel S'"
      by (simp add: t_split)
  qed
  moreover have "\<And>\<delta>. Q = {q\<^sub>0} \<union> (snd ` snd ` \<delta>) \<Longrightarrow> Q = {q\<^sub>0} \<union> (snd ` snd ` (\<delta> \<union> prestar_step P Q \<delta>))"
    unfolding prestar_step_def by (auto split: prod.splits) force+
  ultimately have step: "\<And>\<delta>. (\<delta> \<subseteq> rel S' \<and> Q = {q\<^sub>0} \<union> (snd ` snd ` \<delta>)) \<Longrightarrow> \<delta> \<union> prestar_step P Q \<delta> \<noteq> \<delta>
      \<Longrightarrow> (\<delta> \<union> prestar_step P Q \<delta> \<subseteq> rel S' \<and> Q = {q\<^sub>0} \<union> (snd ` snd ` (\<delta> \<union> prestar_step P Q \<delta>)))"
    by (smt (verit, del_insts) Un_iff subset_eq)

  note base step
  moreover note assms(4)[unfolded prestar_while_def] b_def c_def
  ultimately have "\<delta>' \<subseteq> rel S' \<and> Q = {q\<^sub>0} \<union> (snd ` snd ` \<delta>')"
    by (elim prestar_while_rule; use assms in simp)
  then show "\<delta>' \<subseteq> rel S'"
    by simp
qed

subsection\<open>Termination\<close>

definition "alg_state_m_d S \<equiv> ({t. direct S t \<noteq> {}})"
definition "alg_state_m_i S \<equiv> ({t. impl S t \<noteq> {}})"

lemma alg_state_m_i_step_weak:
  assumes "t \<in> trans S"
  shows "alg_state_m_i (alg_outer_step S t) \<subseteq> alg_state_m_i S"
  by (auto simp: alg_state_m_i_def)

lemma alg_state_m_i_step:
  assumes "t \<in> trans S" and "impl S t \<noteq> {}"
  shows "alg_state_m_i (alg_outer_step S t) \<subset> alg_state_m_i S"
  using assms by (auto simp: alg_state_m_i_def)

lemma alg_state_m_d_step_weak:
  assumes "t \<in> trans S" and "impl S t = {}"
  shows "alg_state_m_d (alg_outer_step S t) \<subseteq> alg_state_m_d S"
  using assms by (auto simp: alg_state_m_d_def)

lemma alg_state_m_d_step:
  assumes "t \<in> trans S" and "impl S t = {}" and "direct S t \<noteq> {}"
  shows "alg_state_m_d (alg_outer_step S t) \<subset> alg_state_m_d S"
  using assms by (auto simp: alg_state_m_d_def)

lemma alg_state_m_trans_step:
  assumes "t \<in> trans S" and "impl S t = {}" and "direct S t = {}"
  shows "trans (alg_outer_step S t) \<subset> trans S"
  using assms by auto

lemmas alg_state_m_intros = alg_state_m_i_step_weak alg_state_m_i_step
  alg_state_m_d_step_weak alg_state_m_d_step alg_state_m_trans_step

definition "alg_state_comp \<equiv> lex_prod less_than (lex_prod less_than less_than)"

definition alg_state_measure :: "('s, 'n, 't) alg_state \<Rightarrow> (nat \<times> nat \<times> nat)" where
  "alg_state_measure S \<equiv> (card (alg_state_m_i S), card (alg_state_m_d S), card (trans S))"

lemma wf_alg_state_comp: "wf (inv_image alg_state_comp alg_state_measure)"
  unfolding alg_state_comp_def by (intro wf_inv_image) blast

definition alg_state_fin_inv :: "('s, 'n, 't) alg_state \<Rightarrow> bool" where
  "alg_state_fin_inv S \<equiv> (
    finite (rel S) \<and> finite (trans S) \<and>
    (\<forall>t. finite (direct S t)) \<and> finite (alg_state_m_d S) \<and>
    (\<forall>t. finite (impl S t)) \<and> finite (alg_state_m_i S)
  )"

lemma alg_state_fin_inv_step:
  assumes "alg_state_fin_inv S"
    and "t \<in> trans S"
  shows "alg_state_fin_inv (alg_outer_step S t)"
  unfolding alg_state_fin_inv_def
proof (intro conjI)
  show "finite (rel (alg_outer_step S t))"
    by (simp add: assms[unfolded alg_state_fin_inv_def])
next
  have "{t''. \<exists>t'. (t', t'') \<in> impl S t \<and> t' \<in> alg_outer_step_rel S t} \<subseteq> snd ` impl S t"
    by force
  moreover have "finite (snd ` impl S t)"
    using assms[unfolded alg_state_fin_inv_def] by blast
  ultimately have "finite {t''. \<exists>t'. (t', t'') \<in> impl S t \<and> t' \<in> alg_outer_step_rel S t}"
    by (elim finite_subset)
  then show "finite (trans (alg_outer_step S t))"
    using assms[unfolded alg_state_fin_inv_def]
    unfolding alg_outer_step_simps alg_outer_step_trans_eq by blast
next
  have "\<And>t'. {t''. (t', t'') \<in> impl S t \<and> t' \<notin> alg_outer_step_rel S t} \<subseteq> snd ` impl S t"
    by force
  moreover have "finite (snd ` impl S t)"
    using assms[unfolded alg_state_fin_inv_def] by blast
  ultimately have "\<And>t'. finite {t''. (t', t'') \<in> impl S t \<and> t' \<notin> alg_outer_step_rel S t}"
    using finite_subset by blast
  moreover have "\<And>t'. finite (((direct S)(t := {})) t')"
    using assms[unfolded alg_state_fin_inv_def] by (auto simp: alg_state_m_d_def)
  ultimately show "\<forall>t'. finite (direct (alg_outer_step S t) t')"
    unfolding alg_outer_step_simps alg_outer_step_direct_eq by blast
next
  have "alg_state_m_d (alg_outer_step S t) \<subseteq> alg_state_m_d S \<union> fst ` impl S t"
    unfolding alg_outer_step_simps alg_state_m_d_def by (auto, force)
  moreover have "finite (alg_state_m_d S \<union> fst ` impl S t)"
    using assms[unfolded alg_state_fin_inv_def] by blast
  ultimately show "finite (alg_state_m_d (alg_outer_step S t))"
    using finite_subset by blast
next
  show "\<forall>t'. finite (impl (alg_outer_step S t) t')"
    by (simp add: assms[unfolded alg_state_fin_inv_def])
next
  have "finite (alg_state_m_i S)"
    by (simp add: assms(1)[unfolded alg_state_fin_inv_def])
  moreover have "alg_state_m_i (alg_outer_step S t) \<subseteq> alg_state_m_i S"
    using assms(2) by (rule alg_state_m_i_step_weak)
  ultimately show "finite (alg_state_m_i (alg_outer_step S t))"
    by (elim finite_subset)
qed

lemma alg_state_fin_inv_step':
  assumes "alg_state_fin_inv s" and "trans s \<noteq> {}"
  shows "alg_state_fin_inv (alg_outer_step s (SOME x. x \<in> trans s))"
  using assms alg_state_fin_inv_step by (metis some_in_eq)

lemma wf_alg_outer_step:
  defines "b \<equiv> (\<lambda>S. trans S \<noteq> {})"
    and "c \<equiv> (\<lambda>S. alg_outer_step S (SOME x. x \<in> trans S))"
  shows "wf {(t, s). (alg_state_fin_inv s \<and> b s) \<and> t = c s}"
proof -
  have "\<And>S t. t \<in> trans S \<Longrightarrow> alg_state_fin_inv S \<Longrightarrow> b S \<Longrightarrow> (alg_outer_step S t, S) \<in> inv_image alg_state_comp alg_state_measure"
  proof -
    fix S and t
    assume "t \<in> trans S" and inv: "alg_state_fin_inv S" and "b S"

    obtain n1 n2 n3 where n_def: "alg_state_measure S = (n1, n2, n3)"
      using prod_cases3 by blast
    then have n1_def: "n1 = card (alg_state_m_i S) \<and> finite (alg_state_m_i S)"
        and n2_def: "n2 = card (alg_state_m_d S) \<and> finite (alg_state_m_d S)"
        and n3_def: "n3 = card (trans S) \<and> finite (trans S)"
      using inv by (simp add: alg_state_measure_def alg_state_fin_inv_def)+

    define S' where "S' \<equiv> alg_outer_step S t"

    obtain m1 m2 m3 where m_def: "alg_state_measure S' = (m1, m2, m3)"
      using prod_cases3 by blast
    moreover have "alg_state_fin_inv S'"
      using inv \<open>t \<in> trans S\<close> alg_state_fin_inv_step unfolding S'_def b_def by blast
    ultimately have m1_def: "m1 = card (alg_state_m_i S') \<and> finite (alg_state_m_i S')"
        and m2_def: "m2 = card (alg_state_m_d S') \<and> finite (alg_state_m_d S')"
        and m3_def: "m3 = card (trans S') \<and> finite (trans S')"
      by (simp add: S'_def alg_state_measure_def alg_state_fin_inv_def)+

    consider (red1) "impl S t \<noteq> {}"
      | (red2) "impl S t = {} \<and> direct S t \<noteq> {}"
      | (red3) "impl S t = {} \<and> direct S t = {}"
      by blast
    then have "((m1, m2, m3), (n1, n2, n3)) \<in> alg_state_comp"
    proof (cases)
      case red1
      with \<open>t \<in> trans S\<close> have "alg_state_m_i S' \<subset> alg_state_m_i S"
        by (simp add: alg_state_m_intros[where t=t and S=S] S'_def)+
      then have "m1 < n1"
        using m1_def n1_def by (simp add: psubset_card_mono)
      then show ?thesis
        by (simp add: alg_state_comp_def)
    next
      case red2
      with \<open>t \<in> trans S\<close> have "alg_state_m_i S' \<subseteq> alg_state_m_i S"
          and "alg_state_m_d S' \<subset> alg_state_m_d S"
        by (simp add: alg_state_m_intros[where t=t and S=S] S'_def)+
      then have "m1 \<le> n1" and "m2 < n2"
        using m1_def m2_def n1_def n2_def
        by (simp add: psubset_card_mono card_mono)+
      then show ?thesis
        by (auto simp: alg_state_comp_def)
    next
      case red3
      then have "alg_state_m_i S' \<subseteq> alg_state_m_i S"
        and "alg_state_m_d S' \<subseteq> alg_state_m_d S"
        and "trans S' \<subset> trans S"
        using \<open>t \<in> trans S\<close> alg_state_m_intros[where t=t and S=S] by (simp add: S'_def)+
      then have "m1 \<le> n1" and "m2 \<le> n2" and "m3 < n3"
        using m1_def m2_def m3_def n1_def n2_def n3_def
        by (simp add: psubset_card_mono card_mono)+
      then show ?thesis
        by (auto simp: alg_state_comp_def)
    qed
    then show "(alg_outer_step S t, S) \<in> inv_image alg_state_comp alg_state_measure"
      using m_def n_def by (simp add: S'_def)
  qed
  then have "{(t, s). (alg_state_fin_inv s \<and> b s) \<and> t = c s} \<subseteq> inv_image alg_state_comp alg_state_measure"
    unfolding c_def b_def
    by (smt (verit, ccfv_SIG) all_not_in_conv mem_Collect_eq old.prod.case some_eq_imp subrelI)
  with wf_alg_state_comp show ?thesis
    by (rule wf_subset)
qed

lemma alg_outer_terminates:
  assumes "alg_state_fin_inv S"
  shows "\<exists>S'. alg_outer S = Some S'"
  unfolding alg_outer_def
  by (intro wf_while_option_Some; use wf_alg_outer_step alg_state_fin_inv_step' assms in fast)

lemma alg_state_new_fin_inv:
  fixes \<delta> :: "('s, 'n, 't) trans"
  assumes "finite P" and "finite Q" and "finite \<delta>"
  shows "alg_state_fin_inv (alg_state_new P Q \<delta>)"
  unfolding alg_state_fin_inv_def
proof (intro conjI)
  show "finite (rel (alg_state_new P Q \<delta>))"
    by (simp add: alg_state_new_def)
next
  note assms(3)
  moreover have "finite {(q, Nt A, q) |q A. (A, []) \<in> P \<and> q \<in> Q}"
    by (rule finite_subset[where B="Q \<times> (Nt ` fst ` P) \<times> Q"]; use assms in force)
  moreover have "finite {(q, Nt A, q') |q q' A. \<exists>a. (A, [Tm a]) \<in> P \<and> (q, Tm a, q') \<in> \<delta> \<and> q \<in> Q \<and> q' \<in> Q}"
    by (rule finite_subset[where B="Q \<times> (Nt ` fst ` P) \<times> Q"]; use assms in force)
  ultimately show "finite (trans (alg_state_new P Q \<delta>))"
    by (simp add: alg_state_new_def)
next
  have "\<And>q q' B. finite {(q, Nt A, q') |A. (A, [Nt B]) \<in> P \<and> q \<in> Q \<and> q' \<in> Q}"
    by (rule finite_subset[where B="Q \<times> (Nt ` fst ` P) \<times> Q"]; use assms in force)
  then show "\<forall>t. finite (direct (alg_state_new P Q \<delta>) t)"
    unfolding alg_state_new_def by (auto split: sym.split)
next
  have "alg_state_m_d (alg_state_new P Q \<delta>) \<subseteq> Q \<times> hd ` snd ` P \<times> Q"
    unfolding alg_state_new_def alg_state_m_d_def by (auto split: sym.splits) force
  moreover have "finite (hd ` snd ` P )"
    using assms(1) by simp
  ultimately show "finite (alg_state_m_d (alg_state_new P Q \<delta>))"
    using assms(2) finite_subset by blast
next
  have "\<And>t. impl (alg_state_new P Q \<delta>) t \<subseteq> (Q \<times> hd ` tl ` snd ` P \<times> Q) \<times> (Q \<times> Nt ` fst ` P \<times> Q)"
    unfolding alg_state_new_def by (auto split: sym.splits) force+
  moreover have "finite ((Q \<times> hd ` tl ` snd ` P \<times> Q) \<times> (Q \<times> Nt ` fst ` P \<times> Q))"
    using assms(1,2) by simp
  ultimately show "\<forall>t. finite (impl (alg_state_new P Q \<delta>) t)"
    using finite_subset by blast
next
  have "alg_state_m_i (alg_state_new P Q \<delta>) \<subseteq> Q \<times> hd ` snd ` P \<times> Q"
    unfolding alg_state_new_def alg_state_m_i_def by (auto split: sym.splits) force
  moreover have "finite (hd ` snd ` P )"
    using assms(1) by simp
  ultimately show "finite (alg_state_m_i (alg_state_new P Q \<delta>))"
    using assms(2) finite_subset by blast
qed

subsection\<open>Final Algorithm\<close>

definition prestar_code_cnf :: "('n, 't) Prods \<Rightarrow> ('s, ('n, 't) sym) nfa \<Rightarrow> ('s, ('n, 't) sym) nfa" where
  "prestar_code_cnf P M \<equiv> (
    \<comment>\<open>Construct the set of ``interesting'' states:\<close>
    let Q = {start M} \<union> (snd ` snd ` (transitions M)) in
    let S = alg_state_new P Q (transitions M) in
    case alg_outer S of
      Some S' \<Rightarrow> M \<lparr> transitions := (rel S') \<rparr>
  )"

lemma prestar_code_cnf_correct:
  assumes "finite P" and "finite (transitions M)" and cnf: "CNF1 P"
  shows "lang_nfa (prestar_code_cnf P M) = pre_star P (lang_nfa M)"
proof -
  define Q where "Q \<equiv> {start M} \<union> (snd ` snd ` (transitions M))"
  have "finite Q"
    using assms(2) by (simp add: Q_def)

  define S where "S \<equiv> alg_state_new P Q (transitions M)"
  have "alg_state_fin_inv S"
    using alg_state_new_fin_inv assms(1,2) \<open>finite Q\<close> by (simp add: S_def)
  then obtain S' where S'_def: "alg_outer S = Some S'"
    using alg_outer_terminates by blast

  obtain \<delta>' where \<delta>'_def: "prestar_while P Q (transitions M) = Some \<delta>'"
    using prestar_while_terminates assms(1,2) \<open>finite Q\<close> by blast
  moreover have "rel S' \<subseteq> \<delta>'"
    using S'_def \<delta>'_def prestar_alg_sub unfolding S_def by blast
  moreover have "\<delta>' \<subseteq> rel S'"
    using S'_def \<delta>'_def cnf prestar_alg_sup unfolding S_def Q_def by fast
  ultimately have "rel S' = \<delta>'"
    by simp

  have "prestar_code P M = prestar_code_cnf P M"
    unfolding prestar_code_def prestar_code_cnf_def
    using \<delta>'_def S'_def \<open>rel S' = \<delta>'\<close> unfolding S_def Q_def by simp
  then show ?thesis
    using prestar_code_correct assms(1,2) by metis
qed

end \<comment>\<open>end-theory ImprovedAlgorithm\<close>
