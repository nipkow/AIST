(* Author: Tobias Nipkow *)

section "Context-Free Languages"

theory CFL
imports
  "Regular-Sets.Regular_Set"
  CFG
  "AFP/CFG_Renaming"
  "AFP/CFG_Disjoint_Union"
begin

subsection \<open>Auxiliary: \<open>lfp\<close> as Kleene Fixpoint\<close>

definition omega_chain :: "(nat \<Rightarrow> ('a::complete_lattice)) \<Rightarrow> bool" where
"omega_chain C = (\<forall>i. C i \<le> C(Suc i))"

definition omega_cont :: "(('a::complete_lattice) \<Rightarrow> ('b::complete_lattice)) \<Rightarrow> bool" where
"omega_cont f = (\<forall>C. omega_chain C \<longrightarrow> f(SUP n. C n) = (SUP n. f(C n)))"

lemma omega_chain_mono: "omega_chain C \<Longrightarrow> i \<le> j \<Longrightarrow> C i \<le> C j"
unfolding omega_chain_def using lift_Suc_mono_le[of C]  
by(induction "j-i" arbitrary: i j)auto

lemma mono_if_omega_cont: fixes f :: "('a::complete_lattice) \<Rightarrow> ('b::complete_lattice)"
  assumes "omega_cont f" shows "mono f"
proof
  fix a b :: "'a" assume "a \<le> b"
  let ?C = "\<lambda>n::nat. if n=0 then a else b"
  have "omega_chain ?C" using \<open>a \<le> b\<close> by(auto simp: omega_chain_def)
  hence "f(SUP n. ?C n) = (SUP n. f(?C n))"
    using assms by (simp add: omega_cont_def del: if_image_distrib)
  moreover have "(SUP n. ?C n) = b"
    using \<open>a \<le> b\<close> by (auto simp add: gt_ex sup.absorb2 split: if_splits)
  moreover have "(SUP n. f(?C n)) = sup (f a) (f b)"
    by (smt (verit, best) SUP_absorb UNIV_I calculation(1,2))
  ultimately show "f a \<le> f b"
    by (metis sup.cobounded1)
qed

lemma omega_chain_iterates: fixes f :: "('a::complete_lattice) \<Rightarrow> 'a"
  assumes "mono f" shows "omega_chain(\<lambda>n. (f^^n) bot)"
proof-
  have "(f ^^ n) bot \<le> (f ^^ Suc n) bot" for n
  proof (induction n)
    case 0 show ?case by simp
  next
    case (Suc n) thus ?case using assms by (auto simp: mono_def)
  qed
  thus ?thesis by(auto simp: omega_chain_def assms)
qed

theorem lfp_if_omega_cont:
  assumes "omega_cont f" shows "lfp f = (SUP n. (f^^n) bot)" (is "_ = ?U")
proof(rule Orderings.antisym)
  from assms mono_if_omega_cont
  have mono: "(f ^^ n) bot \<le> (f ^^ Suc n) bot" for n
    using funpow_decreasing [of n "Suc n"] by auto
  show "lfp f \<le> ?U"
  proof (rule lfp_lowerbound)
    have "f ?U = (SUP n. (f^^Suc n) bot)"
      using omega_chain_iterates[OF mono_if_omega_cont[OF assms]] assms
      by(simp add: omega_cont_def)
    also have "\<dots> = ?U"
      using mono by (meson SUP_le_iff SUP_mono' Sup_upper antisym rangeI)
    finally show "f ?U \<le> ?U" by simp
  qed
next
  have "(f^^n) bot \<le> p" if "f p \<le> p" for n p
  proof -
    show ?thesis
    proof(induction n)
      case 0 show ?case by simp
    next
      case Suc
      from monoD[OF mono_if_omega_cont[OF assms] Suc] \<open>f p \<le> p\<close>
      show ?case by simp
    qed
  qed
  thus "?U \<le> lfp f"
    using lfp_unfold[OF mono_if_omega_cont[OF assms]] [[metis_instantiate]]
    by (simp add: SUP_le_iff)
qed


subsection \<open>Basic Definitions\<close>

text \<open>This definition depends on the a type of nonterminals of the grammar.\<close>

definition CFL :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"CFL (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> finite P)"

text \<open>Ideally one would existentially quantify over \<open>'n\<close> on the right-hand side, but we cannot
quantify over types in HOL. But we can prove that the type is irrelevant because we can always
use another type via renaming.\<close>

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

text \<open>For hiding the infinite type of nonterminals:\<close>

abbreviation cfl :: "'a lang \<Rightarrow> bool" where
"cfl L \<equiv> CFL (TYPE(nat)) L"


subsection \<open>Closure Properties\<close>

lemma CFL_Un_closed:
  assumes "CFL TYPE('n1) L1" "CFL TYPE('n2) L2"
  shows "CFL TYPE(('n1+'n2)option) (L1 \<union> L2)"
proof -
  from assms obtain P1 P2 and S1 :: 'n1 and S2 :: 'n2
    where L: "L1 = Lang P1 S1" "L2 = Lang P2 S2" and fin: "finite P1" "finite P2"
    unfolding CFL_def by blast
  let ?f1 = "Some o (Inl:: 'n1 \<Rightarrow> 'n1 + 'n2)"
  let ?f2 = "Some o (Inr:: 'n2 \<Rightarrow> 'n1 + 'n2)"
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

lemma CFL_concat_closed: 
assumes "CFL TYPE('n1) L1" and "CFL TYPE('n2) L2"
shows "CFL TYPE(('n1 + 'n2) option) (L1 @@ L2)"
proof -
  obtain P1 S1 where L1_def: "L1 = Lang P1 (S1::'n1)" "finite P1"
    using assms(1) CFL_def[of L1] by auto 
  obtain P2 S2 where L2_def: "L2 = Lang P2 (S2::'n2)" "finite P2"
    using assms(2) CFL_def[of L2] by auto
  let ?f1 = "Some o (Inl:: 'n1 \<Rightarrow> 'n1 + 'n2)"
  let ?f2 = "Some o (Inr:: 'n2 \<Rightarrow> 'n1 + 'n2)"
  let ?P1 = "rename_Prods ?f1 P1"
  let ?P2 = "rename_Prods ?f2 P2"
  let ?S1 = "?f1 S1"
  let ?S2 = "?f2 S2"
  let ?S = "None :: ('n1+'n2)option"
  let ?P = "{(None, [Nt ?S1, Nt ?S2])} \<union> (?P1 \<union> ?P2)"
  have "inj ?f1" by (simp add: inj_on_def) 
  then have L1r_def: "L1 = Lang ?P1 ?S1" 
    using L1_def Lang_rename_Prods[of ?f1 P1 S1] inj_on_def by force
  have "inj ?f2" by (simp add: inj_on_def) 
  then have L2r_def: "L2 = Lang ?P2 ?S2" 
    using L2_def Lang_rename_Prods[of ?f2 P2 S2] inj_on_def by force
  have "Lang ?P ?S = L1 @@ L2" unfolding L1r_def L2r_def  
    by(rule Lang_concat_disj) (auto simp add: disjoint_iff in_Nts_rename_Prods)
  moreover have "finite ?P" using \<open>finite P1\<close> \<open>finite P2\<close> by auto
  ultimately show ?thesis unfolding CFL_def by blast
qed


subsection \<open>CFG as an Equation System, \<open>Lang\<close> as a Solution\<close>

definition inst :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) sym \<Rightarrow> 't lang" where
"inst L s = (case s of Tm a \<Rightarrow> {[a]} | Nt A \<Rightarrow> L A)"

definition concats :: "'a lang list \<Rightarrow> 'a lang" where
"concats Ls = foldr (@@) Ls {[]}"

definition insts :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) syms \<Rightarrow> 't lang" where
"insts L w = concats (map (inst L) w)"

definition subst_lang :: "('n,'t)Prods \<Rightarrow> ('n \<Rightarrow> 't lang) \<Rightarrow> ('n \<Rightarrow> 't lang)" where
"subst_lang P L = (\<lambda>A. \<Union>w \<in> Rhss P A. insts L w)"

definition Lang :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't lang" where
"Lang P = lfp (subst_lang P)"

hide_const (open) CFL.Lang

lemma inst_Sup_range:  "inst (Sup(range F)) = (\<lambda>s. UN i. inst (F i) s)"
  by(auto simp: inst_def fun_eq_iff split: sym.splits)

lemma foldr_map_mono: "F \<le> G \<Longrightarrow> foldr (@@) (map F xs) Ls \<subseteq> foldr (@@) (map G xs) Ls"
by(induction xs)(auto simp add: le_fun_def subset_eq)

lemma inst_mono: "F \<le> G \<Longrightarrow> inst F s \<subseteq> inst G s"
by (auto simp add: inst_def le_fun_def subset_iff split: sym.splits)

lemma foldr_conc_map_inst:
  assumes "omega_chain L"
  shows "foldr (@@) (map (\<lambda>s. \<Union>i. inst (L i) s) xs) Ls = (\<Union>i. foldr (@@) (map (inst (L i)) xs) Ls)"
proof(induction xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  show ?case (is "?l = ?r")
  proof
    show "?l \<subseteq> ?r"
    proof
      fix w assume "w \<in> ?l"
      with Cons obtain u v i j
        where "w = u @ v" "u \<in> inst (L i) a" "v \<in> foldr (@@) (map (inst (L j)) xs) Ls" by(auto)
      then show "w \<in> ?r"
        using omega_chain_mono[OF assms, of i "max i j"] omega_chain_mono[OF assms, of j "max i j"]
          inst_mono foldr_map_mono[of "inst (L j)" "inst (L (max i j))" xs Ls] concI
        unfolding le_fun_def by(simp) blast
    qed
  next
    show "?r \<subseteq> ?l" using Cons by(fastforce)
  qed
qed

lemma omega_cont_CFL_Lang: "omega_cont (subst_lang P)"
proof (clarsimp simp add: omega_cont_def subst_lang_def)
  fix L :: "nat \<Rightarrow> 'a \<Rightarrow> 'b lang"
  assume o: "omega_chain L"
  show "(\<lambda>A. \<Union> (insts (Sup (range L)) ` Rhss P A)) = (SUP i. (\<lambda>A. \<Union> (insts (L i) ` Rhss P A)))"
    (is "(\<lambda>A. ?l A) = (\<lambda>A. ?r A)")
  proof
    fix A :: 'a
    have "?l A = \<Union>(\<Union>i. (insts (L i) ` Rhss P A))"
      by(auto simp: insts_def inst_Sup_range concats_def foldr_conc_map_inst[OF o])
    also have "\<dots> = ?r A"
      by(auto)
    finally show "?l A = ?r A" .
  qed
qed

theorem CFL_Lang_SUP: "CFL.Lang P = (SUP n. ((subst_lang P)^^n) (\<lambda>A. {}))"
using lfp_if_omega_cont[OF omega_cont_CFL_Lang] unfolding CFL.Lang_def bot_fun_def by blast


subsection \<open>Connecting Equation Solution and Derivations: \<open>CFL.Lang = Lang\<close>\<close>

text \<open>A parallel reduction step of all Nts in a word:\<close>

abbreviation par_step :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n,'t)syms \<Rightarrow> 't list \<Rightarrow> bool" where
"par_step R \<alpha> w \<equiv>
  (\<exists>g. (\<forall>i < length \<alpha>. case \<alpha>!i of Tm a \<Rightarrow> g i = [a] | Nt A \<Rightarrow> g i \<in> R A)
       \<and> w = concat (map g [0..<length \<alpha>]))"

lemma par_step_mono: "(\<And>A. R A \<subseteq> R' A) \<Longrightarrow> par_step R \<alpha> w \<Longrightarrow> par_step R' \<alpha> w"
by (auto split: sym.splits) blast

lemma in_subst_langD_insts: "w \<in> subst_lang P L A \<Longrightarrow> \<exists>\<alpha>. (A,\<alpha>)\<in>P \<and> w \<in> insts L \<alpha>"
unfolding subst_lang_def insts_def Rhss_def by (auto split: prod.splits)

lemma foldr_conc_conc: "foldr (@@) xs {[]} @@ A = foldr (@@) xs A"
by (induction xs)(auto simp: conc_assoc)
  
lemma par_step_if_insts: "w \<in> insts L \<alpha> \<Longrightarrow> par_step L \<alpha> w"
  (is "_ \<Longrightarrow> \<exists>g. ?P \<alpha> w g")
proof (induction \<alpha> arbitrary: w rule: rev_induct)
  case Nil
  then show ?case by (auto simp: insts_def concats_def)
next
  case (snoc s \<alpha>)
  from snoc.prems obtain w1 w2 where "w = w1 @ w2" "w1 \<in> insts L \<alpha>" "w2 \<in> inst L s"
    unfolding insts_def concats_def by (auto simp add: foldr_conc_conc[where A = "inst L s",symmetric])
  from snoc.IH[OF \<open>w1 \<in> insts L \<alpha>\<close>] obtain g where IH: "?P \<alpha> w1 g" by blast
  show ?case
  proof (cases s)
    case (Nt A)
    let ?g = "\<lambda>i. if i < length \<alpha> then g i else w2"
    have "map ?g [0..<length \<alpha>] = map g [0..<length \<alpha>]" by(simp)
    then have "?P (\<alpha> @ [s]) w ?g" using IH \<open>w=_\<close> \<open>s = _\<close> \<open>w2 \<in> _\<close>
      by (simp add: nth_append inst_def del: map_eq_conv)
    from exI[of "?P (\<alpha> @ [s]) w", OF this] show ?thesis .
  next
    case (Tm a)
    let ?g = "\<lambda>i. if i < length \<alpha> then g i else [a]"
    have "map ?g [0..<length \<alpha>] = map g [0..<length \<alpha>]" by(simp)
    then have "?P (\<alpha> @ [s]) w ?g" using IH \<open>s = _\<close> \<open>w=_\<close> \<open>w2\<in>_\<close>
      by (simp add: nth_append inst_def del: map_eq_conv)
    from exI[of "?P (\<alpha> @ [s]) w", OF this] show ?thesis .
  qed
qed

lemma derives_if_par_step:
  assumes "par_step (\<lambda>A. {w. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w}) \<alpha> w" (is "\<exists>g. ?P g")
  shows "P \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
proof -
  from assms obtain g where "?P g" by blast
  then have "i \<in> {0..<length \<alpha>} \<Longrightarrow> P \<turnstile> [\<alpha> ! i] \<Rightarrow>* map Tm (g i)" for i
    by(cases "\<alpha>!i")auto
  with \<open>?P g\<close> show ?thesis
    using derives_concat[of "[0..<length \<alpha>]" P "\<lambda>i. [\<alpha>!i]" "\<lambda>i. map Tm (g i)"]
    by(auto simp: map_nth map_concat o_def)
qed

lemma derives_if_in_subst_lang: "w \<in> ((subst_lang P)^^n) (\<lambda>A. {}) A \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
proof(induction n arbitrary: w A)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?L = "((subst_lang P)^^n) (\<lambda>A. {})"
  have *: "?L A \<subseteq> {w. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w}" for A
    using Suc.IH by blast
  obtain \<alpha> where \<alpha>: "(A,\<alpha>) \<in> P" "w \<in> insts ?L \<alpha>"
    using in_subst_langD_insts[OF Suc.prems[simplified]] by blast
  have "P \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
    using par_step_if_insts[OF \<alpha>(2)] derives_if_par_step par_step_mono[OF *, of _ "\<lambda>A. A"] by metis 
  then show ?case using \<alpha>(1)
    by (simp add: derives_Cons_rule)
qed

lemma derives_if_CFL_Lang: "w \<in> CFL.Lang P A \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
  unfolding CFL_Lang_SUP using derives_if_in_subst_lang
  by (metis (mono_tags, lifting) SUP_apply UN_E)

lemma CFL_Lang_subset_CFG_Lang: "CFL.Lang P A \<subseteq> Lang P A"
unfolding CFG.Lang_def by(blast intro:derives_if_CFL_Lang)

(* Other direction *)

(* needed/useful? *)
lemma decomp_syms_splice: "\<exists>(nts::'n list) (tms::'a list list).
  \<alpha> = concat (splice (map (map Tm) tms) (map (\<lambda>A. [Nt A]) nts))"
proof (induction \<alpha>)
  case Nil
  then show ?case
    by (metis concat.simps(1) list.simps(8) splice_Nil2)
next
  let ?ftm = "(map Tm)" let ?fnt = "(\<lambda>A. [Nt A])"
  case (Cons s \<alpha>)
  then obtain nts tms where "\<alpha> = concat (splice (map ?ftm tms) (map ?fnt nts))" by blast
  show ?case
  proof (cases s)
    case [simp]: (Nt A)
    let ?tms = "[] # tms" let ?nts = "A # nts"
    have "s # \<alpha> = concat (splice (map ?ftm ?tms) (map ?fnt ?nts))" using \<open>\<alpha> = _\<close> by simp
    then show ?thesis by blast
  next
    case [simp]: (Tm a)
    let ?tms = "case tms of [] \<Rightarrow> [[a]] | as#ass \<Rightarrow> (a#as) # ass"
    have "s # \<alpha> = concat (splice (map ?ftm ?tms) (map ?fnt nts))"
      using \<open>\<alpha> = _\<close> by (simp split: list.split)
    then show ?thesis by blast
  qed
qed

(* really neded: with \<Rightarrow>(n) ! *)
lemma "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow>
  \<exists>\<beta>s. \<beta> = concat \<beta>s \<and> length \<alpha> = length \<beta>s \<and> (\<forall>i < length \<beta>s. P \<turnstile> [\<alpha> ! i] \<Rightarrow>* \<beta>s ! i)"
proof (induction \<alpha> arbitrary: \<beta>)
next
  case (Cons s \<alpha>)
  from derives_Cons_decomp[THEN iffD1, OF Cons.prems]
  show ?case
  proof (elim disjE exE conjE)
    fix \<gamma> assume "\<beta> = s # \<gamma>" "P \<turnstile> \<alpha> \<Rightarrow>* \<gamma>"
    from Cons.IH[OF this(2)] obtain \<beta>s
      where *: "\<gamma> = concat \<beta>s \<and> length \<alpha> = length \<beta>s \<and> (\<forall>i<length \<beta>s. P \<turnstile> [\<alpha> ! i] \<Rightarrow>* \<beta>s ! i)"
      by blast
    let ?\<beta>s = "[s]#\<beta>s"
    have "\<beta> = concat ?\<beta>s \<and> length(s#\<alpha>) = length ?\<beta>s \<and> (\<forall>i < length ?\<beta>s. P \<turnstile> [(s#\<alpha>) ! i] \<Rightarrow>* ?\<beta>s ! i)"
      using \<open>\<beta> = _\<close> * by (auto simp: nth_Cons')
    then show ?thesis by blast
  next
    fix A w \<beta>1 \<beta>2
    assume *: "\<beta> = \<beta>1 @ \<beta>2" "s = Nt A" "(A, w) \<in> P" "P \<turnstile> w \<Rightarrow>* \<beta>1" "P \<turnstile> \<alpha> \<Rightarrow>* \<beta>2"
    from Cons.IH[OF this(5)] obtain \<beta>s
      where **: "\<beta>2 = concat \<beta>s \<and> length \<alpha> = length \<beta>s \<and> (\<forall>i<length \<beta>s. P \<turnstile> [\<alpha> ! i] \<Rightarrow>* \<beta>s ! i)"
      by blast
    let ?\<beta>s = "\<beta>1#\<beta>s"
    have "\<beta> = concat ?\<beta>s \<and> length(s#\<alpha>) = length ?\<beta>s \<and> (\<forall>i < length ?\<beta>s. P \<turnstile> [(s#\<alpha>) ! i] \<Rightarrow>* ?\<beta>s ! i)"
      using * ** by (auto simp: nth_Cons' derives_Cons_rule)
    then show ?thesis by blast
  qed
qed simp

(*
lemma CFL_Lang_if_derives: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w \<Longrightarrow> w \<in> CFL.Lang P A"
sorry

theorem CFL_Lang_eq_CFG_Lang: "CFL.Lang P A = Lang P A"
unfolding CFG.Lang_def by(blast intro: CFL_Lang_if_derives derives_if_CFL_Lang)
*)

end