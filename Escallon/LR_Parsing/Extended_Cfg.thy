theory Extended_Cfg
  imports 
    Context_Free_Grammar.Context_Free_Grammar 
begin

section \<open>Context-Free Items\<close>

datatype ('n, 't) item = Item 'n  "('n, 't) syms"  "('n, 't) syms"

notation Item  ("[_ \<rightarrow> _ . _]" 100) 

definition history :: "('n, 't) item \<Rightarrow> ('n, 't) syms" where
  "history i \<equiv> case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> \<alpha>"

lemma history_unfold [simp]: "history ([A \<rightarrow> \<alpha> . \<beta>]) = \<alpha>"
  unfolding history_def by simp

(* As defined in book *)
definition hist :: "('n, 't) item list \<Rightarrow> ('n,'t) syms" where
  "hist \<rho> \<equiv> concat (map history \<rho>)"

(* Needed? (top of stack is hd, not last) *)
definition hist_rev :: "('n, 't) item list \<Rightarrow> ('n,'t) syms" where
  "hist_rev \<rho> \<equiv> concat (map history (rev \<rho>))"

lemma hist_singleton [simp]:
  "hist ([[A \<rightarrow> \<alpha> . \<beta>]]) = \<alpha>"
  unfolding hist_def by simp

lemma hist_Cons[simp]:
  "hist (i#\<rho>) = history i @ hist \<rho>"
  unfolding hist_def by simp

lemmas hist_defs = hist_def hist_rev_def history_def

definition items_of_Prods :: "('n, 't) Prods \<Rightarrow> ('n, 't) item set" where
  "items_of_Prods P = {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> P}"

definition It :: "('n, 't) Cfg \<Rightarrow> ('n, 't) item set" where
  "It G = items_of_Prods (Prods G)"

lemmas It_defs = It_def items_of_Prods_def

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

definition reduced :: "('n,'t) Cfg \<Rightarrow> bool" where
  "reduced G \<equiv> \<forall>A \<in> Nts (Prods G). useful (Prods G) (Start G) A"

lemma Lang_nempty_impl_useful_S:
  assumes "LangS G \<noteq> {}"
  shows "useful (Prods G) (Start G) (Start G)"
  using assms unfolding useful_def Lang_def by fastforce

(* TODO mv *)
lemma reduced_impl_restrict_useful_id: 
  assumes "reduced G" 
  shows  "restrict_Nts (useful (Prods G) (Start G)) (Prods G) = Prods G" (is "?R = ?P")
proof 
  show "?R \<subseteq> ?P"
    by (metis restrict_Nts_subset)
  show "?P \<subseteq> ?R"
    unfolding restrict_Nts_def using assms Nts_def reduced_def by fastforce
qed

lemma restrict_useful_id_impl_reduced:
  assumes "restrict_Nts (useful (Prods G) (Start G)) (Prods G) = Prods G" 
  shows "reduced G"
  using assms unfolding restrict_Nts_def reduced_def Nts_def by fast

lemma reduced_impl_derives_singleton:
  assumes "reduced G"
    "A \<in> Nts (Prods G)"
  obtains v where "Prods G \<turnstile> [Nt A] \<Rightarrow>* map Tm v"
  using assms productive_if_useful unfolding reduced_def 
  by metis

lemma reduced_impl_derives:
  assumes  "Nts_syms \<alpha> \<subseteq> Nts (Prods G)"
    "reduced G"
    "LangS G \<noteq> {}"
  obtains v where "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm v"
  using assms(1) proof (induction \<alpha> arbitrary: thesis)
  case (Cons a as)
  from Cons(1,3) obtain v where as_derives: "Prods G \<turnstile> as \<Rightarrow>* map Tm v" by auto
  then show ?case 
  proof (cases a)
    case (Nt A)
    with \<open>reduced G\<close> obtain u where A_derives: "Prods G \<turnstile> [Nt A] \<Rightarrow>* map Tm u"
      using reduced_impl_derives_singleton[OF assms(2)] Cons(3) by auto
    from derives_append[OF this] have "Prods G \<turnstile> Nt A#as \<Rightarrow>* map Tm u @ as" 
      by simp
    also from derives_prepend[OF as_derives] have "Prods G \<turnstile> ... \<Rightarrow>* map Tm (u@v)" 
      by simp
    finally show ?thesis using Nt Cons(2) by blast
  next
    case (Tm x) 
    then show ?thesis using derives_prepend[OF as_derives] Cons(2) 
      by (metis append_Cons append_Nil list.simps(9))
  qed
qed simp

lemma derived_impl_in_Prods:
  assumes "Start G \<in> Nts (Prods G)"
  shows "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>*\<alpha> \<Longrightarrow> Nts_syms \<alpha> \<subseteq> Nts (Prods G)"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case using assms by simp
next
  case (step \<alpha> \<beta>)
  then obtain u A \<gamma> v where "\<alpha> = u@Nt A#v" "(A,\<gamma>) \<in> Prods G" "\<beta> = u@\<gamma>@v"
    using derive.cases[OF step(2)] by (metis append_Cons append_Nil)
  moreover from this have "Nts_syms \<gamma> \<subseteq> Nts (Prods G)" unfolding Nts_def by blast
  ultimately show ?case using step(3) by auto
qed


corollary reduced_derived_impl_derives:
  assumes  "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<alpha>"
    "reduced G"
    "LangS G \<noteq> {}"
  obtains v where "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm v"
proof - 
  from Lang_nempty_impl_useful_S[OF assms(3)] have "Start G \<in> Nts (Prods G)"
    unfolding useful_def 
    by (metis Lang_empty_if_notin_Lhss Nts_Lhss_Rhs_Nts Un_iff assms(3))
  from derived_impl_in_Prods[OF this assms(1)] show thesis 
    using assms(2,3) reduced_impl_derives that by blast
qed

corollary reduced_derived_substring_impl_derives:
  assumes  "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* u@\<alpha>@v"
    "reduced G"
    "LangS G \<noteq> {}"
  obtains w where "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
proof -
  from Lang_nempty_impl_useful_S[OF assms(3)] have "Start G \<in> Nts (Prods G)"
    unfolding useful_def 
    by (metis Lang_empty_if_notin_Lhss Nts_Lhss_Rhs_Nts Un_iff assms(3))
  from derived_impl_in_Prods[OF this assms(1)] have "Nts_syms \<alpha> \<subseteq> Nts (Prods G)" by simp
  from reduced_impl_derives[OF this assms(2,3)] show thesis using that by blast
qed



locale Extended_Cfg = 
    fixes G G' :: "('n::fresh0, 't) Cfg"
      and S S' :: 'n
  assumes G_finite: "finite (Prods G)"
      and G_reduced: "reduced G"
      and G_not_empty: "LangS G \<noteq> {}"
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

lemma G'_derive_S:
  "Prods G' \<turnstile> [Nt S'] \<Rightarrow> [Nt S]"
  unfolding G'_def using derive_singleton by auto

lemma G_derives_impl_G'_derives:
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>* w"
  shows "Prods G' \<turnstile> \<alpha> \<Rightarrow>* w"
  using assms G_Prods_subset_G' by (simp add: derives_mono)


lemma S'_notin_Nts_Prods_G [simp]:
  "S' \<notin> (Nts (Prods G))" 
  unfolding S'_def using fresh0_notIn G_finite finite_Nts
  by (metis Un_insert_right sup_bot_right finite_insert insertCI)

corollary S'_Prod_notin_G [simp]:
  "(S', \<alpha>) \<notin> Prods G"
  using S'_notin_Nts_Prods_G unfolding Nts_def Nts_syms_def by blast

lemma S'_derive_impl_S:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow> \<alpha>"
  shows "\<alpha> = [Nt S]"
proof -
  from assms have in_P': "(S', \<alpha>) \<in> Prods G'" 
    by (simp add: derive_singleton)
  have "(S', \<alpha>) = (S', [Nt S])"
  proof (rule ccontr)
    assume "\<not>?thesis"
    then show False
    using S'_Prod_notin_G in_P' unfolding G'_def 
    by simp
  qed
  thus ?thesis by simp
qed

lemma G_derives_from_S_impl_G'_derives_from_S':
  assumes "Prods G \<turnstile> [Nt S] \<Rightarrow>* w"
  shows "Prods G' \<turnstile> [Nt S'] \<Rightarrow>* w"
  using assms G_derives_impl_G'_derives G'_derive_S
  by fastforce

lemma G'_derive_impl_G_derive_if_no_S':
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow> \<gamma>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow> \<gamma>"
  using G'_def by (simp add: derive_iff in_set_conv_decomp)

lemma G'_derives_impl_G_derives_if_no_S':
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow>* \<gamma>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow>* \<gamma>"
proof (induction rule: rtranclp_induct)
  case (step \<beta> \<gamma>)
  note step(3)[OF step(4)]
  moreover from this have "Nt S' \<notin> set \<beta>" 
    using S'_notin_Nts_Prods_G derives_set_subset in_Nts_iff_in_Syms step.prems 
    by fastforce
  ultimately  show ?case using step G'_derive_impl_G_derive_if_no_S'[OF step(2)]
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
    from S'_derive_impl_S[OF this(1)] this(2) show "w \<in> LangS G" 
      using G'_derives_impl_G_derives_if_no_S' S_neq_S' unfolding Lang_def by simp
  qed
next
  show "LangS G \<subseteq> LangS G'" using G_derives_from_S_impl_G'_derives_from_S'
    unfolding Lang_def G'_def by auto
qed

corollary G'_not_empty: 
  "LangS G' \<noteq> {}" using Lang_preserved G_not_empty by simp

lemma Nts_G'_is_union[simp]: "Nts (Prods G) \<union> {S',S} = Nts (Prods G')"
  using G'_def in_Nts_iff_in_Syms by force


lemma G'_reduced:
   "reduced G'"
proof - 
  have "\<forall>A \<in> Nts (Prods G) \<union> {S}. useful (Prods G') S' A"
    using G_reduced G_not_empty Lang_preserved G_derives_impl_G'_derives Lang_nempty_impl_useful_S
    unfolding reduced_def useful_def Lang_def 
    by (metis G_derives_from_S_impl_G'_derives_from_S' S_def Un_iff singleton_iff) 
  moreover have "useful (Prods G') S' S'" 
    using Lang_nempty_impl_useful_S G_not_empty Lang_preserved G'_def by fastforce
  ultimately have "\<forall>A \<in> Nts (Prods G'). useful (Prods G') S' A"
    using Nts_G'_is_union by blast
  moreover from Nts_G'_is_union have "Nts (Prods G') = Nts (Prods G') \<union> {S'}" by blast
  ultimately show ?thesis unfolding reduced_def G'_def by auto 
qed

end

end
