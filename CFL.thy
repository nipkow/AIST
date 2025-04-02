(* Author: Tobias Nipkow *)

section "Context-Free Languages"

theory CFL
imports
  "Regular-Sets.Regular_Set"
  CFG
  "AFP/CFG_Renaming"
  "AFP/CFG_Disjoint_Union"
begin

text \<open>This definition is tricky to use because one needs to supply a type of nonterminals.\<close>

definition CFL :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"CFL (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> finite P)"

text \<open>Ideally one would existentially quantify over 'n on the right-hand side, but we cannot
quantify over types in HOL.\<close>

text \<open>CFLs are closed under union:\<close>

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
  have "Lang ?P None = Lang ?P1 ?S1 \<union> Lang ?P2 ?S2"
    by (rule Lang_disj_Un2)(auto simp: Nts_Un in_Nts_rename_Prods)
  moreover have "\<dots> = Lang P1 S1 \<union> Lang P2 S2"
  proof -
    have "Lang ?P1 ?S1 = L1" unfolding \<open>L1 = _\<close>
      by (meson Lang_rename_Prods comp_inj_on inj_Inl inj_Some)
    moreover have "Lang ?P2 ?S2 = L2" unfolding \<open>L2 = _\<close>
      by (meson Lang_rename_Prods comp_inj_on inj_Inr inj_Some)
    ultimately show ?thesis using L by argo
  qed
  moreover have "finite ?P" using fin by auto
  ultimately show ?thesis
    unfolding CFL_def using L by blast 
qed

(* TODO: rm with next release *)
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