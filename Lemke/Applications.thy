section\<open>Applications\<close>
text\<open>\label{sec:applications}\<close>

text\<open>
  The algorithm to compute \<open>pre\<^sup>*\<close> of a regular language can be used to construct
  decision procedures for various different problems regarding context-free grammars.
\<close>

theory Applications
  imports Definition FiniteAutomaton Algorithm "HOL.Finite_Set"
begin \<comment>\<open>begin-theory Applications\<close>

subsection\<open>Preliminaries\<close>

text\<open>
  The following code equations are necessary to make \texttt{nts\_syms} and \texttt{tms\_syms}
  (and its dependents) automatically executable:
\<close>

lemma nts_syms_code[code]:
  "nts_syms w = \<Union>((\<lambda>A. case A of Nt X \<Rightarrow> {X} | _ \<Rightarrow> {}) ` set w)"
  by (auto simp: nts_syms_def split: sym.splits)

lemma tms_syms_code[code]:
  "tms_syms w = \<Union>((\<lambda>A. case A of Tm x \<Rightarrow> {x} | _ \<Rightarrow> {}) ` set w)"
  by (auto simp: tms_syms_def split: sym.splits)

subsection\<open>Derivability\<close>

text\<open>
  Particularly, a decision procedure for derivability can be constructed.
\<close>

definition "is_derivable P \<alpha> \<beta> \<equiv> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"

declare is_derivable_def[simp]
declare is_derivable_def[symmetric, code_unfold]

theorem pre_star_derivability:
  shows "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<longleftrightarrow> \<alpha> \<in> pre_star P {\<beta>}"
  by (simp add: Lang_def pre_star_def)

lemma pre_star_derivability_code[code]:
  fixes P :: "('n, 't) prods"
  shows "is_derivable (set P) \<alpha> \<beta> = (\<alpha> \<in> lang_nfa (prestar_code (set P) (nfa_word \<beta>)))"
proof -
  define M where [simp]: "M \<equiv> nfa_word \<beta>"
  have "lang_nfa (prestar_code (set P) M) = pre_star (set P) (lang_nfa M)"
    by (intro prestar_code_correct; simp add: nfa_word_finite_trans)
  then show ?thesis
    using pre_star_derivability by force
qed

subsection\<open>Membership Problem\<close>

\<comment> \<open>Directly follows from derivability:\<close>
lemma pre_star_membership[code_unfold]: "(w \<in> Lang P S) = (P \<turnstile> [Nt S] \<Rightarrow>* map Tm w)"
  by (simp add: Lang_def)

subsection\<open>Nullable Variables\<close>

\<comment> \<open>Directly follows from derivability:\<close>
lemma pre_star_nullable[code]: "is_nullable P X = (P \<turnstile> [Nt X] \<Rightarrow>* [])"
  by (simp add: is_nullable_def)

subsection\<open>Emptiness Problem\<close>

definition "is_empty P S \<equiv> Lang P S = {}"

declare is_empty_def[simp]

lemma cfg_derives_Syms:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>* \<beta>" and "set \<alpha> \<subseteq> Syms P"
  shows "set \<beta> \<subseteq> Syms P"
  using assms proof (induction rule: converse_rtranclp_induct[where r="derive P"])
  case base
  then show ?case
    by simp
next
  case (step y z)
  then have "set z \<subseteq> Syms P"
    using derives_set_subset by blast
  then show ?case
    using step by simp
qed

lemma cfg_lang_univ: "P \<turnstile> [Nt X] \<Rightarrow>* map Tm \<beta> \<Longrightarrow> set \<beta> \<subseteq> Tms P"
proof -
  assume "P \<turnstile> [Nt X] \<Rightarrow>* map Tm \<beta>"
  moreover have "Nt X \<in> Syms P"
    using Syms_def calculation derives_start1 by fastforce
  ultimately have "set (map Tm \<beta>) \<subseteq> Syms P"
    using cfg_derives_Syms by force
  moreover have "\<And>t. (t \<in> Tms P) \<longleftrightarrow> Tm t \<in> Syms P"
    unfolding Tms_def Syms_def tms_syms_def by blast
  ultimately show "set \<beta> \<subseteq> Tms P"
    by force
qed

lemma inj_Tm: "inj Tm"
  by (simp add: inj_def)

lemma finite_tms_syms: "finite (tms_syms w)"
proof -
  have "Tm ` {A. Tm A \<in> set w} \<subseteq> set w"
    by auto
  from finite_inverse_image[OF _ inj_Tm] show ?thesis
    unfolding tms_syms_def using finite_inverse_image[OF _ inj_Tm] by auto
qed

lemma finite_Tms: "finite P \<Longrightarrow> finite (Tms P)"
  unfolding Tms_def by (rule finite_Union; auto simp: finite_tms_syms)

definition pre_star_emptiness_nfa :: "('n, 't) Prods \<Rightarrow> (unit, ('n, 't) sym) nfa" where
  "pre_star_emptiness_nfa P \<equiv>
    let T = Tm ` \<Union>((\<lambda>A. case A of Nt X \<Rightarrow> {} | Tm x \<Rightarrow> {x}) ` \<Union>(set ` snd ` P)) :: ('n, 't) sym set in
    \<lparr> transitions = {()} \<times> T \<times> {()}, start = (), finals = {()} \<rparr>"

theorem pre_star_emptiness:
  fixes P :: "('n, 't) Prods"
  shows "Lang P S = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P {w. set w \<subseteq> Tm ` Tms P}"
proof -
  have "Lang P S = {} \<longleftrightarrow> (\<nexists>w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w)"
    by (simp add: Lang_def)
  also have "... \<longleftrightarrow> (\<nexists>w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w \<and> set w \<subseteq> Tms P)"
    using cfg_lang_univ by fast
  also have "... \<longleftrightarrow> (\<nexists>w. P \<turnstile> [Nt S] \<Rightarrow>* w \<and> set w \<subseteq> Tm ` Tms P)"
    by (smt (verit, best) cfg_lang_univ ex_map_conv imageE image_mono list.set_map subset_iff)
  also have "... \<longleftrightarrow> [Nt S] \<notin> pre_star P {w. set w \<subseteq> Tm ` Tms P}"
    unfolding pre_star_def by blast
  finally show ?thesis .
qed

lemma pre_star_emptiness_code[code]:
  fixes P :: "('n, 't) prods"
  shows "is_empty (set P) S = ([Nt S] \<notin> lang_nfa (prestar_code (set P) (nfa_univ (Tm ` Tms (set P)))))"
proof -
  define M :: "(unit, ('n, 't) sym) nfa" where [simp]: "M \<equiv> nfa_univ (Tm ` Tms (set P))"
  have "finite (Tm ` Tms (set P))"
    using finite_Tms by blast
  then have "lang_nfa (prestar_code (set P) M) = pre_star (set P) (lang_nfa M)"
    by (intro prestar_code_correct; auto simp: nfa_univ_def intro: nfa_univ_trans_fin)
  then show ?thesis
    using pre_star_emptiness unfolding M_def nfa_univ_lang by fastforce
qed

subsection\<open>Useless Variables\<close>

definition pre_star_reachable_nfa :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> (nat, ('n, 't) sym) nfa" where
  "pre_star_reachable_nfa P X \<equiv> (
    let T = \<Union>(set ` snd ` P) in
    \<lparr> transitions = ({0} \<times> T \<times> {0}) \<union> ({1} \<times> T \<times> {1}) \<union> {(0, Nt X, 1)}, start = 0, finals = {1} \<rparr>
  )"

theorem pre_star_reachable:
  fixes P :: "('n, 't) Prods"
  shows "(P \<turnstile> S \<Rightarrow>\<^sup>? X) \<longleftrightarrow> [Nt S] \<in> pre_star P { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P }"
proof -
  define L where "L \<equiv> { (\<alpha>::('n, 't) syms)@[Nt X]@\<beta> | \<alpha> \<beta>. set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P }"
  have "[Nt S] \<in> pre_star P L  \<longleftrightarrow> (\<exists>w. w \<in> L \<and> P \<turnstile> [Nt S] \<Rightarrow>* w)"
    by (simp add: pre_star_term)
  also have "... \<longleftrightarrow> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt S] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>) \<and> set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P)"
    unfolding L_def by blast
  also have "... \<longleftrightarrow> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt S] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>))"
  proof -
    have "\<And>w. P \<turnstile> [Nt S] \<Rightarrow> w \<Longrightarrow> set w \<subseteq> Syms P"
      by (smt (verit, best) Syms_def UN_I UnCI case_prod_conv derive_singleton subset_eq)
    then have "\<And>w. w \<noteq> [Nt S] \<Longrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w \<Longrightarrow> set w \<subseteq> Syms P"
      by (metis cfg_derives_Syms converse_rtranclpE)
    then have "\<And>\<alpha> \<beta>. P \<turnstile> [Nt S] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>) \<Longrightarrow> set \<alpha> \<subseteq> Syms P \<and> set \<beta> \<subseteq> Syms P"
      by (smt (verit) Cons_eq_append_conv append_is_Nil_conv empty_set empty_subsetI le_supE list.discI set_append)
    then show ?thesis
      by blast
  qed
  finally show ?thesis
    by (simp add: is_reachable_from_def L_def)
qed

lemma pre_star_reachable_code[code]:
  fixes P :: "('n, 't) prods"
  shows "((set P) \<turnstile> S \<Rightarrow>\<^sup>? X) = ([Nt S] \<in> lang_nfa (prestar_code (set P) (nfa_fixc_ps (Nt X) (Syms (set P)))))"
proof -
  define M :: "(nat, ('n, 't) sym) nfa" where [simp]: "M \<equiv> nfa_fixc_ps (Nt X) (Syms (set P))"
  have "finite (Syms (set P))"
    unfolding Syms_def by fast
  then have "lang_nfa (prestar_code (set P) M) = pre_star (set P) (lang_nfa M)"
    by (intro prestar_code_correct; auto simp: nfa_fixc_ps_def intro: nfa_fixc_ps_trans_fin)
  then show ?thesis
    using pre_star_reachable unfolding M_def nfa_fixc_ps_lang by fastforce
qed

theorem pre_star_productive:
  fixes P :: "('n, 't) Prods"
  shows "is_productive P X \<longleftrightarrow> [Nt X] \<in> pre_star P (map Tm ` UNIV)"
proof -
  define L :: "('n, 't) sym list set" where "L \<equiv> map Tm ` UNIV"
  have "[Nt X] \<in> pre_star P L \<longleftrightarrow> (\<exists>w. w \<in> L \<and> P \<turnstile> [Nt X] \<Rightarrow>* w)"
    by (simp add: pre_star_term)
  also have "... \<longleftrightarrow> (\<exists>w. P \<turnstile> [Nt X] \<Rightarrow>* map Tm w)"
    unfolding L_def by blast
  finally show ?thesis
    by (simp add: is_productive_def L_def)
qed

subsection\<open>Disjointness and Subset Problem\<close>

theorem pre_star_disjointness: "Lang P S \<inter> L = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map Tm ` L)"
  by (simp add: pre_star_lang)

theorem pre_star_subset: "Lang P S \<subseteq> L \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map Tm ` (-L))"
proof -
  have "Lang P S \<subseteq> L \<longleftrightarrow> Lang P S \<inter> -L = {}"
    by blast
  then show ?thesis
    by (simp add: pre_star_disjointness)
qed

end \<comment>\<open>end-theory Applications\<close>
