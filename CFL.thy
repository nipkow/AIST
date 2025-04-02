(* Author: Tobias Nipkow *)

section "Context-Free Languages"

theory CFL
imports
  "$AFP/Regular-Sets/Regular_Set"
  CFG
  "AFP/CFG_Renaming"
  "AFP/CFG_Disjoint_Union"
begin

text \<open>This definition is tricky to use because one needs to supply a type of nonterminals.\<close>

definition CFL :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"CFL (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> finite P)"

text \<open>Ideally one would existentially quantify over 'n on the right-hand side, but we cannot
quantify over types in HOL.\<close>

text \<open>This is a demo how to use the definition.\<close>

lemma derive_from_isolated_fork:
  "\<lbrakk> A \<notin> Lhss P;  {(A,\<alpha>1),(A,\<alpha>2)} \<union> P \<turnstile> [Nt A] \<Rightarrow> \<beta> \<rbrakk> \<Longrightarrow> \<beta> = \<alpha>1 \<or> \<beta> = \<alpha>2"
unfolding derive_singleton by(auto simp: Lhss_def)

lemma in_Nts_rename_Prods: "B \<in> Nts (rename_Prods f P) = (\<exists>A \<in> Nts P. f A = B)"
unfolding Nts_def nts_syms_def by(force split: prod.splits elim!: rename_sym.elims[OF sym])

lemma derives_fork_if_derives1:
  assumes "P \<turnstile> [Nt B1] \<Rightarrow>* map Tm w"
  shows "{(A,[Nt B1]), (A,[Nt B2])} \<union> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w" (is "?P \<turnstile> _ \<Rightarrow>* _")
proof -
  have "?P \<turnstile> [Nt A] \<Rightarrow> [Nt B1]" using derive_singleton by auto
  also have "?P \<turnstile> [Nt B1] \<Rightarrow>* map Tm w" using assms
    by (meson derives_mono sup_ge2)
  finally show ?thesis .
qed

lemma derives_disj_if_derives_fork:
  assumes "A \<notin> Nts P" "A \<noteq> B1" "A \<noteq> B2"
  and "{(A,[Nt B1]), (A,[Nt B2])} \<union> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w" (is "?P \<turnstile> _ \<Rightarrow>* _")
  shows "P \<turnstile> [Nt B1] \<Rightarrow>* map Tm w \<or> P \<turnstile> [Nt B2] \<Rightarrow>* map Tm w"
proof -
  obtain \<beta> where steps: "?P \<turnstile> [Nt A] \<Rightarrow> \<beta>" "?P \<turnstile> \<beta> \<Rightarrow>* map Tm w"
    using converse_rtranclpE[OF assms(4)] by blast
  have "\<beta> = [Nt B1] \<or> \<beta> = [Nt B2]"
    using steps(1) derive_from_isolated_fork[of A P] assms(1) by(auto simp: Nts_Lhss_Rhs_Nts)
  then show ?thesis
    using steps(2) derives_disj_Un_iff[of P "{(A,[Nt B1]), (A,[Nt B2])}" \<beta>] assms
    by(auto simp: Nts_Lhss_Rhs_Nts)
qed

lemma Lang_distrib_eq_Un_Lang2:
  assumes "A \<notin> Nts P" "A \<noteq> B1" "A \<noteq> B2"
  shows "Lang ({(A,[Nt B1]),(A,[Nt B2])} \<union> P) A = (Lang P B1 \<union> Lang P B2)"
    (is "Lang ?P _ = _" is "?L1 = ?L2")
proof
  show "?L2 \<subseteq> ?L1" unfolding Lang_def
    using derives_fork_if_derives1[of P B1 _ A B2] derives_fork_if_derives1[of P B2 _ A B1]
    by (auto simp add: insert_commute)
next
  show "?L1 \<subseteq> ?L2"
    unfolding Lang_def using derives_disj_if_derives_fork[OF assms] by auto
qed

lemma CFL_disj_Un:
  assumes "CFL TYPE('t1) L1 \<and> CFL TYPE('t2) L2"
  shows "CFL TYPE(('t1+'t2)option) (L1 \<union> L2)"
proof -
  from assms obtain P1 P2 and S1 :: 't1 and S2 :: 't2
    where L: "L1 = Lang P1 S1" "L2 = Lang P2 S2" and fin: "finite P1" "finite P2"
    unfolding CFL_def by blast
  let ?f1 = "Some o (Inl:: 't1 \<Rightarrow> 't1 + 't2)"
  let ?f2 = "Some o (Inr:: 't2 \<Rightarrow> 't1 + 't2)"
  let ?P1 = "rename_Prods ?f1 P1"
  let ?P2 = "rename_Prods ?f2 P2"
  let ?S1 = "?f1 S1"
  let ?S2 = "?f2 S2"
  let ?P = "{(None, [Nt ?S1]), (None, [Nt ?S2])} \<union> (?P1 \<union> ?P2)"
  have *: "None \<notin> Nts (?P1 \<union> ?P2)"
    by (auto simp: Nts_Un in_Nts_rename_Prods)
  have "Lang ?P None = Lang ?P1 ?S1 \<union> Lang ?P2 ?S2"
  proof -
    have 0: "Lang ?P None = Lang (?P1 \<union> ?P2) ?S1 \<union> Lang (?P1 \<union> ?P2) ?S2"
      using Lang_distrib_eq_Un_Lang2[OF *, of ?S1 ?S2] by simp
    have 3: "Lang (?P1 \<union> ?P2) ?S1 = Lang ?P1 ?S1"
      apply(subst Lang_disj_Un[of ?P1 ?P2 ?S1])
      unfolding Lhss_def Nts_def nts_syms_def Rhs_Nts_def
      by (auto elim!: rename_sym.elims[OF sym])
    have 4: "Lang (?P2 \<union> ?P1) ?S2 = Lang ?P2 ?S2"
      apply(subst Lang_disj_Un[of ?P2 ?P1 ?S2])
      unfolding Lhss_def Rhs_Nts_def Nts_def nts_syms_def 
      by (auto elim!: rename_sym.elims[OF sym])
    show ?thesis
      by (metis "0" "3" "4" sup_commute)
  qed
  moreover have "\<dots> = Lang P1 S1 \<union> Lang P2 S2"
  proof -
    have 1: "Lang ?P1 ?S1 = L1" unfolding \<open>L1 = _\<close>
      by (meson Lang_rename_Prods comp_inj_on inj_Inl inj_Some)
    have 2: "Lang ?P2 ?S2 = L2" unfolding \<open>L2 = _\<close>
      by (meson Lang_rename_Prods comp_inj_on inj_Inr inj_Some)
    show ?thesis
      using "1" "2" L(1,2) by argo
  qed
  moreover have "finite ?P" using fin by auto
  ultimately show ?thesis
    unfolding CFL_def using L by blast 
qed

(* TODO: mv to HOL-Library.Infinite_Typeclass*)
lemma arb_inj_on_finite_infinite: "finite(A :: 'a set) \<Longrightarrow> \<exists>f :: 'a \<Rightarrow> 'b::infinite. inj_on f A"
by (meson arb_finite_subset card_le_inj infinite_imp_nonempty)

lemma CFL_change_Nt_type: assumes "CFL TYPE('t1::infinite) L" shows "CFL TYPE('t2::infinite) L"
proof -
  from assms obtain P and S :: 't1 where "L = Lang P S" and "finite P"
    unfolding CFL_def by blast
  have fin: "finite(Nts P \<union> {S})" using \<open>finite P\<close>
    by(simp add: finite_Nts)
  obtain f :: "'t1 \<Rightarrow> 't2" where "inj_on f (Nts P \<union> {S})"
    using arb_inj_on_finite_infinite[OF fin] by blast
  from Lang_rename_Prods[OF this] \<open>L = _\<close> have "Lang (rename_Prods f P) (f S) = L"
    by blast
  moreover have "finite(rename_Prods f P)" using \<open>finite P\<close>
    by blast
  ultimately show ?thesis unfolding CFL_def by blast
qed

unused_thms

definition cfl :: "'t list set \<Rightarrow> bool" where
"cfl L = (\<exists>P S::nat. L = Lang P S \<and> finite P)"

lemma cfl_iff_CFL: "cfl L \<longleftrightarrow> CFL TYPE('t::infinite) L"
by (metis cfl_def CFL_def CFL_change_Nt_type)



definition inst :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) sym \<Rightarrow> 't lang" where
"inst L s = (case s of Tm a \<Rightarrow> {[a]} | Nt A \<Rightarrow> L A)"

definition concats :: "'a lang list \<Rightarrow> 'a lang" where
"concats = foldl (@@) {[]}"

definition insts :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) syms \<Rightarrow> 't lang" where
"insts L w = concats (map (inst L) w)"

definition subst_lang :: "('n,'t)Prods \<Rightarrow> ('n \<Rightarrow> 't lang) \<Rightarrow> ('n \<Rightarrow> 't lang)" where
"subst_lang P L = (\<lambda>A. \<Union>w \<in> Rhss P A. insts L w)"

definition Lang :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't lang" where
"Lang P = lfp (subst_lang P)"

hide_const (open) CFL.Lang

lemma derives_if_CFL_Lang: "w \<in> CFL.Lang P A \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
sorry

lemma CFL_Lang_if_derives: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w \<Longrightarrow> w \<in> CFL.Lang P A"
sorry

theorem CFL_Lang_eq_CFG_Lang: "CFL.Lang P A = Lang P A"
unfolding CFG.Lang_def by(blast intro: CFL_Lang_if_derives derives_if_CFL_Lang)


end