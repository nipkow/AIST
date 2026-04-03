theory Extended_Cfg
  imports 
    Context_Free_Grammar.Context_Free_Grammar 
    Pushdown_Automata.Pushdown_Automata
    Finite_Automata_HF.Finite_Automata_HF
begin

section \<open>Context-Free Items\<close>

datatype ('n, 't) item = Item 'n  "('n, 't) syms"  "('n, 't) syms"

notation Item  ("[_ \<rightarrow> _ . _]" 100) 

definition items_of_Prods :: "('n, 't) Prods \<Rightarrow> ('n, 't) item set" where
  "items_of_Prods P = {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> P}"

definition It :: "('n, 't) Cfg \<Rightarrow> ('n, 't) item set" where
  "It G = items_of_Prods (Prods G)"

(* Intro breaks proofs

lemma ItI[intro]:
  assumes "P (items_of_Prods (Prods G))"
  shows "P (It G)"
  using assms unfolding It_def by presburger

*)
declare It_def[simp]

lemma prod_items_finite:
  "finite {[A \<rightarrow> \<alpha> . \<beta>] | \<alpha> \<beta>. (A, \<alpha>@\<beta>) = (A, w)}"
proof (induction w)
  case (Cons a w)
  let ?it = "{[A \<rightarrow> \<alpha> . \<beta>] |\<alpha> \<beta>. (A, \<alpha> @ \<beta>) = (A, w)}"
  have "{[A \<rightarrow> \<alpha> . \<beta>] |\<alpha> \<beta>. (A, \<alpha> @ \<beta>) = (A, a # w)} 
        = {[A \<rightarrow> (a#\<alpha>) . \<beta>]|\<alpha> \<beta>. [A \<rightarrow> \<alpha> . \<beta>]\<in>?it} \<union> {[A \<rightarrow> [] . (a#\<beta>)]|\<beta>. [A \<rightarrow> [] . \<beta>]\<in>?it}" 
    (is "?cons = ?app_\<alpha> \<union> ?app_\<beta>")
  proof
    show "?cons \<subseteq> ?app_\<alpha> \<union> ?app_\<beta>"
    proof
      fix i
      assume in_cons: "i \<in> ?cons"
      then obtain \<alpha> \<beta> where \<alpha>\<beta>: "i = [A \<rightarrow> \<alpha> . \<beta>]" "\<alpha> @ \<beta> = a # w"
        by blast
      show "i \<in> ?app_\<alpha> \<union> ?app_\<beta>" using \<alpha>\<beta> by (cases \<alpha>) auto
    qed
  next
    show "?app_\<alpha> \<union> ?app_\<beta> \<subseteq> ?cons" 
    proof
      fix i 
      assume in_apps: "i \<in> ?app_\<alpha> \<union> ?app_\<beta>"
      then consider (in_app_\<alpha>) "i \<in> ?app_\<alpha>" | (in_app_\<beta>) "i \<in> ?app_\<beta>" by blast
      then show "i \<in> ?cons" by cases fastforce+
    qed
  qed
  moreover have "bij_betw (\<lambda>i. case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> [A \<rightarrow> (a#\<alpha>) . \<beta>]) ?it ?app_\<alpha>" 
    (is "bij_betw ?f _ _")
  proof -
    have "inj_on ?f ?it" 
      by (smt (verit, del_insts) inj_onCI item.case item.exhaust item.inject list.inject)
    moreover have "?f ` ?it = ?app_\<alpha>" by force
    ultimately show ?thesis unfolding bij_betw_def by simp
  qed
  moreover have "finite ?app_\<beta>" 
  proof -
    have "{[A \<rightarrow> [] . \<beta>]|\<beta>. [A \<rightarrow> [] . \<beta>]\<in>?it} \<subseteq> ?it" by blast
    moreover have 
      "bij_betw (\<lambda>i. case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> [A \<rightarrow> \<alpha> . a#\<beta>]) {[A \<rightarrow> [] . \<beta>]|\<beta>. [A \<rightarrow> [] . \<beta>]\<in>?it} ?app_\<beta>"
      by simp
    ultimately show ?thesis using Cons by simp
  qed
  ultimately show ?case using local.Cons bij_betw_finite by fastforce
qed simp

lemma items_of_Prods_finite:
  assumes "finite P"
shows "finite (items_of_Prods P)"
proof -
  have "items_of_Prods P = (\<Union>(A,w)\<in>P. {[A \<rightarrow> \<alpha> . \<beta>] | \<alpha> \<beta>. (A, \<alpha>@\<beta>) = (A, w)})" 
    unfolding items_of_Prods_def by auto
  with prod_items_finite show ?thesis using assms by fastforce
qed


corollary It_finite:
  assumes "finite (Prods G)"
shows "finite (It G)"
  using assms items_of_Prods_finite by auto


section \<open>Finite/Pushdown Automata\<close>

(* Problem when defining \<Delta>: IPDA uses \<Delta> :: 'q list \<Rightarrow> 'a \<Rightarrow> 'q list
                              (defined as \<Delta>: Q\<^sup>+ \<times> V\<^sub>T \<Rightarrow> Q\<^sup>* in the book)
Possible solutions: 
  1. Make Q ('n, 't) item list
  2. Since state = top of stack: instead of state q and stack q#qs do state q and stack qs
      \<Longrightarrow> problems with empty stack? (IPDA accepts with final state)

A definition with variant 2, using [S' \<rightarrow> [] . []] as a dummy starting stack symbol:
*)


(* TODO mv *)
lemma reduced_impl_restrict_useful_id: 
  assumes "\<forall>A \<in> Nts (Prods G). useful (Prods G) (Start G) A" 
  shows  "restrict_Nts (useful (Prods G) (Start G)) (Prods G) = Prods G" (is "?R = ?P")
proof 
  show "?R \<subseteq> ?P"
    by (metis restrict_Nts_subset)
  show "?P \<subseteq> ?R"
    unfolding restrict_Nts_def using assms Nts_def by fast
qed

lemma restrict_useful_id_impl_reduced:
  assumes "restrict_Nts (useful (Prods G) (Start G)) (Prods G) = Prods G" 
  shows "\<forall>A \<in> Nts (Prods G). useful (Prods G) (Start G) A"
  using assms unfolding restrict_Nts_def 
  by (metis (no_types, lifting) Nts_def Product_Type.Collect_case_prodD UN_E fst_conv mem_case_prodE
      prod.sel(2))


locale Extended_Cfg = 
    fixes G G' :: "('n::fresh0, 't) Cfg"
      and S S' :: 'n
  assumes G_finite: "finite (Prods G)"
      and G_reduced[simp]: "\<forall>A \<in> Nts (Prods G). useful (Prods G) (Start G) A"
  defines "S \<equiv> Start G"
      and "S' \<equiv> fresh0 (Nts (Prods G) \<union> {S})"
      and "G' \<equiv> Cfg (Prods G \<union> {(S', [Nt S])}) S'"
begin

lemma G'_finite:
  "finite (Prods G')"
  using G_finite G'_def by simp

lemmas S_defs[simp] = S_def S'_def

lemma S_neq_S'[simp]:
  "S \<noteq> S'" 
  by (metis G_finite ID.set_finite S'_def Un_iff finite_Nts finite_Un fresh0_notIn singletonI)

lemma G_Prods_subset_G':
  "Prods G \<subseteq> Prods G'"
  using G'_def by auto

lemma G_derives_impl_G'_derives:
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>* w"
  shows "Prods G' \<turnstile> \<alpha> \<Rightarrow>* w"
  using assms G_Prods_subset_G' by (simp add: derives_mono)

lemma S'_derives_S:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow> \<alpha>"
  shows "\<alpha> = [Nt S]"
proof -
  from assms have in_P': "(S', \<alpha>) \<in> Prods G'" 
    by (simp add: derive_singleton)
  show ?thesis
  proof -
    have "(S', \<alpha>) = (S', [Nt S])"
    proof (rule ccontr)
      assume "(S', \<alpha>) \<noteq> (S', [Nt S])"
      with in_P' have "(S', \<alpha>) \<in> Prods G" unfolding G'_def by auto
      with S'_def show False 
        by (metis G_finite ID.set_finite Nts_Lhss_Rhs_Nts finite_Nts fresh0_notIn in_LhssI 
            infinite_Un rev_contra_hsubsetD sup_ge1)
    qed
    thus ?thesis by simp
  qed
qed

lemma G'_derive_impl_G_derive_if_no_S':
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow> \<gamma>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow> \<gamma>"
  using G'_def by (simp add: derive_iff in_set_conv_decomp)

lemma G'_derives_impl_G_derives_if_no_S':
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow>* \<gamma>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow>* \<gamma>"
proof (induction rule: rtranclp_induct)
  case (step \<beta> \<gamma>)
  note G_derives_\<beta> = step(3)[OF step(4)]
  have "Nt S' \<notin> set \<beta>" 
  proof -
    have "S' \<notin> (Nts (Prods G))" 
      by (metis G_finite S'_def Un_iff finite.emptyI finite_Nts finite_Un finite_insert
          fresh0_notIn)
    with G_derives_\<beta> show ?thesis 
      using derives_set_subset in_Nts_iff_in_Syms step.prems by fastforce
  qed
  from step(3)[OF step(4)] G'_derive_impl_G_derive_if_no_S'[OF step(2) this] show ?case
    by simp
qed simp

lemma Lang_preserved:
  "LangS G' = LangS G"
proof
  show "LangS G' \<subseteq> LangS G"
  proof
    fix w
    assume "w \<in> LangS G'"
    hence "Prods G' \<turnstile> [Nt S'] \<Rightarrow>* map Tm w" unfolding Lang_def G'_def by simp
    then obtain \<alpha> where "Prods G' \<turnstile> [Nt S'] \<Rightarrow> \<alpha>" "Prods G' \<turnstile> \<alpha> \<Rightarrow>* map Tm w" 
      by (meson derive_singleton derives_Nt_map_TmD)
    from S'_derives_S[OF this(1)] this(2) show "w \<in> LangS G" 
      using G'_derives_impl_G_derives_if_no_S' S_neq_S' unfolding Lang_def by simp
  qed
next
  show "LangS G \<subseteq> LangS G'"
  proof
    fix w
    assume "w \<in> LangS G"
    hence "Prods G \<turnstile> [Nt S] \<Rightarrow>* map Tm w" unfolding Lang_def by simp
    with G_derives_impl_G'_derives have "Prods G' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
      by simp
    moreover have "Prods G' \<turnstile> [Nt S'] \<Rightarrow> [Nt S]" unfolding G'_def 
      by (simp add: derive_singleton)
    ultimately show "w \<in> LangS G'" 
      by (simp add: G'_def Lang_def)
  qed
qed

end

end
