theory Extended_Cfg
  imports Auxiliary
begin

section \<open>Context-Free Items\<close>

datatype ('n, 't) item = Item 'n  "('n, 't) syms"  "('n, 't) syms" ("[_ \<rightarrow> _ . _]")

abbreviation prod_of_item :: "('n, 't) item \<Rightarrow> ('n, 't) prod" where
  "prod_of_item i \<equiv> case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> (A, \<alpha>@\<beta>)"

definition history :: "('n, 't) item \<Rightarrow> ('n, 't) syms" where
  "history i \<equiv> case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> \<alpha>"

lemma history_unfold [simp]: "history [A \<rightarrow> \<alpha> . \<beta>] = \<alpha>"
  unfolding history_def by simp

definition hist :: "('n, 't) item list \<Rightarrow> ('n,'t) syms" where
  "hist \<rho> \<equiv> concat (map history (rev \<rho>))"

lemma hist_Nil [simp]:
  "hist [] = []" 
  unfolding hist_def by simp

lemma hist_singleton [simp]:
  "hist ([[A \<rightarrow> \<alpha> . \<beta>]]) = \<alpha>"
  unfolding hist_def by simp

lemma hist_Cons[simp]:
  "hist (i#\<rho>) = hist \<rho> @ history i"
  unfolding hist_def by simp

lemmas hist_defs = hist_def history_def

definition items_of_Prods :: "('n, 't) Prods \<Rightarrow> ('n, 't) item set" where
  "items_of_Prods P \<equiv> {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> P}"

definition It :: "('n, 't) Cfg \<Rightarrow> ('n, 't) item set" where
  "It G = items_of_Prods (Prods G)"

definition Nts_of_items :: "('n, 't) item set \<Rightarrow> 'n set" where
  "Nts_of_items I \<equiv> (\<lambda>i. case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> A) ` I"

definition Hists_of_items :: "('n, 't) item set \<Rightarrow> ('n, 't) syms set" where
  "Hists_of_items I \<equiv> (\<lambda>i. case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> \<alpha>) ` I"

lemma in_items_imp_in_Nts [intro]:
  assumes "[A \<rightarrow> \<alpha> . \<beta>] \<in> I"
  shows "A \<in> Nts_of_items I"
  using assms unfolding Nts_of_items_def by force

lemma in_items_imp_in_Hists [intro]:
  assumes "[A \<rightarrow> \<alpha> . \<beta>] \<in> I"
  shows "\<alpha> \<in> Hists_of_items I"
  using assms unfolding Hists_of_items_def by force

lemmas It_defs = It_def items_of_Prods_def

lemma in_Prods_imp_in_It:
  "prod_of_item i \<in> Prods G \<Longrightarrow> i \<in> It G"
  unfolding It_defs by (metis (mono_tags, lifting) item.case item.exhaust mem_Collect_eq)

lemma in_It_imp_in_Prods:
  "i \<in> It G \<Longrightarrow> prod_of_item i \<in> Prods G"
  unfolding It_defs by auto

lemma in_Prods_iff_in_It:
  "prod_of_item i \<in> Prods G = (i \<in> It G)"
  using in_Prods_imp_in_It in_It_imp_in_Prods by auto

lemma prod_of_item_eq_imp_in_Prods_eq:
  "prod_of_item i = prod_of_item j \<Longrightarrow> i \<in> It G' \<longleftrightarrow> j \<in> It G'"
  by (cases i, cases j) (metis in_Prods_iff_in_It)

lemma hd_in_prods_imp_derives_expanded_hist:
  assumes "(Y, \<alpha>) \<in> P"
  shows "P \<turnstile> hist ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>] # \<rho>) \<Rightarrow>*  hist ([Y \<rightarrow> \<alpha> . []] # [X \<rightarrow> \<beta> . Nt Y # \<gamma>] # \<rho>)"         
    (is "P \<turnstile> ?h1 \<Rightarrow>* ?h2")
  using assms by (auto simp: derive_prepend derive_singleton r_into_rtranclp)

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

lemma finite_items_of_Prods:
  assumes "finite P"
shows "finite (items_of_Prods P)"
proof -
  have "items_of_Prods P = (\<Union>(A,w)\<in>P. {[A \<rightarrow> \<alpha> . \<beta>] | \<alpha> \<beta>. (A, \<alpha>@\<beta>) = (A, w)})" 
    unfolding items_of_Prods_def by auto
  with prod_items_finite show ?thesis using assms by fastforce
qed

corollary finite_It:
  assumes "finite (Prods G)"
shows "finite (It G)"
  using assms finite_items_of_Prods unfolding It_def by auto

lemma finite_items_imp_finite_Nts:
  assumes "finite I"
  shows "finite (Nts_of_items I)"
  using assms unfolding Nts_of_items_def by blast

lemma finite_items_imp_finite_Hists:
  assumes "finite I"
  shows "finite (Hists_of_items I)"
  using assms unfolding Hists_of_items_def by blast

lemma finite_lists_length_eq_Hists:
  assumes "finite I" "finite A"
  shows "finite {xs |xs \<alpha>. set xs \<subseteq> A \<and> length xs = length \<alpha> \<and> \<alpha> \<in> (Hists_of_items I)}"
proof -
  note finite_Hists = finite_items_imp_finite_Hists[OF assms(1)]
  have "{xs|xs \<alpha>. set xs \<subseteq> A \<and> length xs = length \<alpha> \<and> \<alpha> \<in> (Hists_of_items I)}
        = {xs|xs n. set xs \<subseteq> A \<and> length xs = n \<and> n \<in> length ` (Hists_of_items I)}"
    by blast
  with finite_lists_length_eq_set finite_Hists assms(2) show ?thesis by auto
qed

(* mv? *)
section \<open>Reduced Grammars\<close>

definition reduced :: "('n,'t) Cfg \<Rightarrow> bool" where
  "reduced G \<equiv> \<forall>A \<in> Nts (Prods G). useful (Prods G) (Start G) A"

lemma Lang_nempty_imp_useful_S:
  assumes "LangS G \<noteq> {}"
  shows "useful (Prods G) (Start G) (Start G)"
  using assms unfolding useful_def Lang_def by fastforce

(* TODO mv *)
lemma reduced_imp_restrict_useful_id: 
  assumes "reduced G" 
  shows  "restrict_Nts (useful (Prods G) (Start G)) (Prods G) = Prods G" (is "?R = ?P")
proof 
  show "?R \<subseteq> ?P"
    by (metis restrict_Nts_subset)
  show "?P \<subseteq> ?R"
    unfolding restrict_Nts_def using assms Nts_def reduced_def by fastforce
qed

lemma restrict_useful_id_imp_reduced:
  assumes "restrict_Nts (useful (Prods G) (Start G)) (Prods G) = Prods G" 
  shows "reduced G"
  using assms unfolding restrict_Nts_def reduced_def Nts_def by fast

lemma reduced_imp_derives_Tms_singleton:
  assumes "reduced G"
    "A \<in> Nts (Prods G)"
  obtains v where "Prods G \<turnstile> [Nt A] \<Rightarrow>* map Tm v"
  using assms productive_if_useful unfolding reduced_def 
  by metis

lemma reduced_imp_Nts_subset_derives_Tms:
  assumes  "Nts_syms \<alpha> \<subseteq> Nts (Prods G)"
    "reduced G"
  obtains v where "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm v"
  using assms(1) proof (induction \<alpha> arbitrary: thesis)
  case (Cons a as)
  from Cons(1,3) obtain v where as_derives: "Prods G \<turnstile> as \<Rightarrow>* map Tm v" by auto
  then show ?case 
  proof (cases a)
    case (Nt A)
    with \<open>reduced G\<close> obtain u where A_derives: "Prods G \<turnstile> [Nt A] \<Rightarrow>* map Tm u"
      using reduced_imp_derives_Tms_singleton[OF assms(2)] Cons(3) by auto
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

lemma reduced_imp_prod_substring_derives_Tms:
  assumes "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G"
    "reduced G"
  obtains v where "Prods G \<turnstile> \<beta> \<Rightarrow>* map Tm v"
  using reduced_imp_Nts_subset_derives_Tms[OF _ assms(2)]
   prod_substring_imp_Nts_subset[OF assms(1)] by blast

lemma reduced_imp_prod_singleton_derives_Tms:
  assumes "(A, \<alpha> @ Nt B # \<gamma>) \<in> Prods G"
    "reduced G"
  obtains v where "Prods G \<turnstile> [Nt B] \<Rightarrow>* map Tm v"
  using reduced_imp_prod_substring_derives_Tms[of A \<alpha> "[Nt B]" \<gamma>] assms by auto

lemma reduced_imp_prod_derives_Tms:
  assumes "(A, \<alpha>) \<in> Prods G"
    "reduced G"
  obtains v where "Prods G \<turnstile> [Nt A] \<Rightarrow> \<alpha>"
    "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm v"
  using reduced_imp_prod_substring_derives_Tms[of A "[]" \<alpha> "[]"] assms derive.intros 
  by (metis append.right_neutral append_Nil)

lemma reduced_imp_prod_distinct:
  assumes "(A, \<alpha>) \<in> Prods G"
    "reduced G"
  obtains \<beta> where "(A, \<beta>) \<in> Prods G" "Nt A \<notin> set \<beta>"
proof -
  from assms obtain w n where "Prods G \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w"
    using rtranclp_imp_relpowp by (metis append.right_neutral append_Nil derives_Cons_rule
        reduced_imp_prod_substring_derives_Tms)
  then show thesis using that
  proof (induction n arbitrary: A w thesis rule: less_induct)
    case (less n)
    then obtain m \<alpha> where m_steps: "n = Suc m" "Prods G \<turnstile> [Nt A] \<Rightarrow> \<alpha>" "Prods G \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w" 
      using relpowp_Suc_D2 by (metis deriven_Nt_map_TmD)
    then show ?case proof (cases "Nt A \<in> set \<alpha>")
      case True
      with m_steps obtain \<beta> \<gamma> where "\<alpha> = \<beta> @ [Nt A] @ \<gamma>" using split_list by fastforce
      then obtain i v where "Prods G \<turnstile> [Nt A] \<Rightarrow>(i) map Tm v" "i < n" using deriven_leq
          m_steps(1,3) by (metis le_imp_less_Suc)
      then show ?thesis using less.IH less.prems(2) by blast
    next
      case False
      then show ?thesis using m_steps less.prems(2)[of \<alpha>] by (simp add: derive_singleton)
    qed
  qed
qed

lemma derives_imp_in_Prods:
  assumes "Start G \<in> Nts (Prods G)"
  shows "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<alpha> \<Longrightarrow> Nts_syms \<alpha> \<subseteq> Nts (Prods G)"
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

lemma reduced_derives_imp_substring_derives_Tms:
  assumes  "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* u@\<alpha>@v"
    "reduced G"
    "LangS G \<noteq> {}"
  obtains w where "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
proof -
  from Lang_nempty_imp_useful_S[OF assms(3)] have "Start G \<in> Nts (Prods G)"
    unfolding useful_def 
    by (metis Lang_empty_if_notin_Lhss Nts_Lhss_Rhs_Nts Un_iff assms(3))
  from derives_imp_in_Prods[OF this assms(1)] have "Nts_syms \<alpha> \<subseteq> Nts (Prods G)" by simp
  from reduced_imp_Nts_subset_derives_Tms[OF this assms(2)] show thesis using that by blast
qed

lemma reduced_derives_imp_derives_Tms:
  assumes  "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<alpha>"
    "reduced G"
    "LangS G \<noteq> {}"
  obtains v where "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm v"
  using reduced_derives_imp_substring_derives_Tms[of _ "[]" _ "[]"] assms 
  by (metis append.right_neutral append_Nil)

lemma reduced_Nts_in_It:
  assumes "A \<in> Nts (Prods G)" "reduced G"
  obtains \<alpha> \<beta> where "[A \<rightarrow> \<alpha> . \<beta>] \<in> It G"
  using assms unfolding It_defs 
  by (metis (mono_tags, lifting) append.right_neutral derives_Nt_map_TmD mem_Collect_eq
      reduced_imp_derives_Tms_singleton)

lemma reduced_reachable_imp_rsentential_reachable:
  assumes "reduced G"
    "LangS G \<noteq> {}"
    "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<alpha> @ Nt A # \<beta>"
  obtains \<gamma> v where "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* \<gamma> @ Nt A # map Tm v"
  using assms(3) proof (induction "\<alpha> @ Nt A # \<beta>" arbitrary: \<alpha> A \<beta> thesis rule: derives_induct)
  case base
  then show ?case using base(2)[of "[]" "[]"] 
    by (simp add: Cons_eq_append_conv)
next
  case (step \<delta> X \<zeta> \<eta>)
  from this(4) show ?case proof (cases rule: list_append_cases)
    case (left \<alpha>')
    with step(2)[of \<alpha> A "\<alpha>' @ Nt X # \<zeta>"] show thesis using step(5) by auto
  next
    case (right \<zeta>')
    from this(2) show ?thesis 
    proof (cases rule: list_append_cases)
      case (left \<eta>')
      from step(2)[of \<delta> X \<zeta>] obtain \<gamma> v where "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* \<gamma> @ Nt X # map Tm v" 
        by auto
      also from left step have "Prods G \<turnstile> ... \<Rightarrow>r (\<gamma> @ \<zeta>') @ Nt A # \<eta>' @ map Tm v"
        using deriver.intros by fastforce
      also obtain u where "Prods G \<turnstile> ... \<Rightarrow>r* (\<gamma> @ \<zeta>') @ Nt A # map Tm (u@v)"
      proof -
        from reduced_derives_imp_substring_derives_Tms
            [OF _ assms(1,2), of "\<gamma> @ \<zeta>' @ [Nt A]" \<eta>' "map Tm v"] calculation derivers_imp_derives
        obtain u where "Prods G \<turnstile> \<eta>' \<Rightarrow>r* map Tm u" 
          by (metis append.assoc append_Cons append_Nil derivers_iff_derives)
        from this[THEN derivers_append_map_Tm, THEN derivers_prepend, of "\<gamma> @ \<zeta>' @ [Nt A]" v] 
          show thesis using that by simp
      qed
      finally show ?thesis using step(5) right by blast 
    next
      case (right \<theta>)
      with step(2)[of "\<delta> @ Nt X # \<theta>" A \<beta>] show ?thesis using step(5) by auto
    qed
  qed
qed

lemma reduced_Nt_imp_rsentential_reachable:
  assumes "reduced G"
    "LangS G \<noteq> {}"
    "A \<in> Nts (Prods G)"
  obtains \<gamma> v where "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* \<gamma> @ Nt A # map Tm v"
proof -
  from assms obtain \<alpha> \<beta> where "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<alpha> @ Nt A # \<beta>"
    unfolding reduced_def useful_def by (metis split_list)
  from reduced_reachable_imp_rsentential_reachable[OF assms(1,2) this] 
  show thesis using that by blast
qed

lemma reduced_in_Prods_imp_rsentential_reachable:
  assumes "reduced G"
    "LangS G \<noteq> {}"
    "(A, \<alpha>) \<in> Prods G"
  obtains \<gamma> v where "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* \<gamma> @ Nt A # map Tm v"
  using reduced_Nt_imp_rsentential_reachable[OF assms(1,2)] assms(3) 
  by (metis Nts_Lhss_Rhs_Nts Un_iff in_LhssI)

    

section \<open>Extending a reduced CFG by a new starting symbol S'\<close>

locale Extended_Cfg = 
    fixes G :: "('n::fresh0, 't) Cfg"
  assumes G_finite: "finite (Prods G)"
      and G_reduced: "reduced G"
      and G_not_empty: "LangS G \<noteq> {}"
begin

definition "S \<equiv> Start G"
definition "S' \<equiv> fresh0 (Nts (Prods G) \<union> {S})"
definition "G' \<equiv> Cfg (Prods G \<union> {(S', [Nt S])}) S'"

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

lemma G'_Prod_cases[consumes 1, case_names init prod_G]:
  assumes "p \<in> Prods G'"
    and "p = (S', [Nt S]) \<Longrightarrow> P" "p \<in> Prods G \<Longrightarrow> P"
  shows P
proof -
  from assms(1) have "p \<in> Prods G \<union> {(S', [Nt S])}"
    unfolding G'_def by auto
  then show P
    by standard (use assms(2-) in auto)
qed

lemma G'_derive_S:
  "Prods G' \<turnstile> [Nt S'] \<Rightarrow> [Nt S]"
  unfolding G'_def using derive_singleton by auto

lemma G_derives_imp_G'_derives:
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>* w"
  shows "Prods G' \<turnstile> \<alpha> \<Rightarrow>* w"
  using assms G_Prods_subset_G' by (simp add: derives_mono)

lemma S'_notin_Nts_Prods_G [simp]:
  "S' \<notin> (Nts (Prods G))" 
  unfolding S'_def using fresh0_notIn G_finite finite_Nts
  by (metis Un_insert_right sup_bot_right finite_insert insertCI)

lemma S'_Prod_notin_G:
  "(S', \<alpha>) \<notin> Prods G"
  "Nt S' \<in> set \<alpha> \<Longrightarrow> (X, \<alpha>) \<notin> Prods G"
  using S'_notin_Nts_Prods_G unfolding Nts_def Nts_syms_def by blast+

lemma S'_Prod_notin_G':
  assumes "Nt S' \<in> set \<alpha>"
  shows "(X, \<alpha>) \<notin> Prods G'"
  using assms proof (rule contrapos_pn)
  assume "(X, \<alpha>) \<in> Prods G'"
  then show "Nt S' \<notin> set \<alpha>"
    using S_neq_S' S'_Prod_notin_G(2) 
    by (cases rule: G'_Prod_cases) auto
qed


lemma S'_derive_imp_S:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow> \<alpha>"
  shows "\<alpha> = [Nt S]"
proof -
  from assms have in_P': "(S', \<alpha>) \<in> Prods G'" 
    by (simp add: derive_singleton)
  have "(S', \<alpha>) = (S', [Nt S])"
  proof (rule ccontr)
    assume "\<not>?thesis"
    then show False
    using S'_Prod_notin_G in_P' unfolding G'_def by simp
  qed
  thus ?thesis by simp
qed

lemma G_derives_from_S_imp_G'_derives_from_S':
  assumes "Prods G \<turnstile> [Nt S] \<Rightarrow>* w"
  shows "Prods G' \<turnstile> [Nt S'] \<Rightarrow>* w"
  using assms G_derives_imp_G'_derives G'_derive_S
  by fastforce

lemma G'_derives_from_S_imp_derives_from_S':
  assumes "Prods G' \<turnstile> [Nt S] \<Rightarrow>* \<alpha>"
  shows "Prods G' \<turnstile> [Nt S'] \<Rightarrow>* \<alpha>"
  using assms G'_derive_S by simp

lemma G'_derives_from_S_imp_in_Lang:
  assumes "Prods G' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
  shows "w \<in> LangS G'"
  using G'_derives_from_S_imp_derives_from_S'[OF assms]
  unfolding Lang_def G'_def by simp

lemma G'_derive_imp_G_derive_if_no_S':
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow> \<gamma>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow> \<gamma>"
  using G'_def by (simp add: derive_iff in_set_conv_decomp)

lemma G'_derives_imp_G_derives_if_no_S':
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow>* \<gamma>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow>* \<gamma>"
proof (induction rule: rtranclp_induct)
  case (step \<beta> \<gamma>)
  note step(3)[OF step(4)]
  moreover from this have "Nt S' \<notin> set \<beta>" 
    using S'_notin_Nts_Prods_G derives_set_subset in_Nts_iff_in_Syms step.prems 
    by fastforce
  ultimately  show ?case using step G'_derive_imp_G_derive_if_no_S'[OF step(2)]
    by simp
qed simp

lemma G'_derivern_Suc_imp_G_derivern:
  "Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) \<beta> \<Longrightarrow> Prods G \<turnstile> [Nt S] \<Rightarrow>(n) \<beta>"
proof (induction n arbitrary: \<beta>)
  case 0
  then show ?case using S'_derive_imp_S by auto
next
  case (Suc n)
  then obtain \<alpha> where step_Sucn: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) \<alpha>" "Prods G' \<turnstile> \<alpha> \<Rightarrow> \<beta>"
    by (meson relpowp_Suc_E)
  with Suc.IH have stepn: "Prods G \<turnstile> [Nt S] \<Rightarrow>(n) \<alpha>" 
    by presburger
  also with step_Sucn have "Prods G \<turnstile> ... \<Rightarrow> \<beta>" 
    by (metis G'_derive_imp_G_derive_if_no_S' G_not_empty Lang_empty_if_notin_Lhss Nts_Lhss_Rhs_Nts
        S'_notin_Nts_Prods_G S_def Un_iff derives_imp_in_Prods in_Nts_syms relpowp_imp_rtranclp
        subsetD)
  finally show ?case .
qed
  
  
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
    from S'_derive_imp_S[OF this(1)] this(2) show "w \<in> LangS G" 
      using G'_derives_imp_G_derives_if_no_S' S_neq_S' unfolding Lang_def by simp
  qed
next
  show "LangS G \<subseteq> LangS G'" using G_derives_from_S_imp_G'_derives_from_S'
    unfolding Lang_def G'_def by auto
qed

corollary G'_not_empty: 
  "LangS G' \<noteq> {}" using Lang_preserved G_not_empty by simp


lemma Nts_G'_is_union[simp]: "Nts (Prods G) \<union> {S',S} = Nts (Prods G')"
  using G'_def in_Nts_iff_in_Syms by force

lemma in_Lang_imp_S_derives:
  assumes "w \<in> LangS G'"
  shows "Prods G' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
  using assms unfolding Lang_def 
  by (metis G_derives_imp_G'_derives Lang_def Lang_preserved S_def mem_Collect_eq)


lemma G'_reduced:
   "reduced G'"
proof - 
  have "\<forall>A \<in> Nts (Prods G) \<union> {S}. useful (Prods G') S' A"
    using G_reduced G_not_empty Lang_preserved G_derives_imp_G'_derives Lang_nempty_imp_useful_S
    unfolding reduced_def useful_def Lang_def 
    by (metis G_derives_from_S_imp_G'_derives_from_S' S_def Un_iff singleton_iff) 
  moreover have "useful (Prods G') S' S'" 
    using Lang_nempty_imp_useful_S G_not_empty Lang_preserved G'_def by fastforce
  ultimately have "\<forall>A \<in> Nts (Prods G'). useful (Prods G') S' A"
    using Nts_G'_is_union by blast
  moreover from Nts_G'_is_union have "Nts (Prods G') = Nts (Prods G') \<union> {S'}" by blast
  ultimately show ?thesis unfolding reduced_def G'_def by auto 
qed

end

end
