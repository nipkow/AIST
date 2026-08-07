theory Extended_Cfg
  imports Auxiliary
begin

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
  from this(4) show ?case proof (cases rule: list_app_eq_nempty_cases)
    case (left \<alpha>')
    with step(2)[of \<alpha> A "\<alpha>' @ Nt X # \<zeta>"] show thesis using step(5) by auto
  next
    case (right \<zeta>')
    from this(2) show ?thesis 
    proof (cases rule: list_app_eq_nempty_cases)
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

abbreviation "S \<equiv> Start G"
definition "S' \<equiv> fresh0 (Nts (Prods G) \<union> {S})"
definition "G' \<equiv> Cfg (Prods G \<union> {(S', [Nt S])}) S'"

declare S'_def[simp]

(* TODO: rename to finite_G' *)
lemma G'_finite:
  "finite (Prods G')"
  using G_finite G'_def by simp

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
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
  shows "Prods G' \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
  using assms G_Prods_subset_G' by (simp add: derives_mono)

lemma G_deriver_imp_G'_deriver:
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>r \<beta>"
  shows "Prods G' \<turnstile> \<alpha> \<Rightarrow>r \<beta>"
  using assms G_Prods_subset_G' deriver.intros deriver.cases 
  by (smt (verit, best) subset_eq)

lemma G_derivers_imp_G'_derivers:
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>r* \<beta>"
  shows "Prods G' \<turnstile> \<alpha> \<Rightarrow>r* \<beta>"
  using assms G_Prods_subset_G' 
  by (smt (verit, best) deriver.cases deriver.intros mono_rtranclp subset_eq)


lemma S'_notin_Nts_Prods_G [simp]:
  "S' \<notin> (Nts (Prods G))" 
  unfolding S'_def using fresh0_notIn G_finite finite_Nts
  by (metis Un_insert_right sup_bot_right finite_insert insertCI)

lemma S'_Prod_notin_G:
  "(S', \<alpha>) \<notin> Prods G"
  "Nt S' \<in> set \<beta> \<Longrightarrow> (X, \<beta>) \<notin> Prods G"
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

lemma S'_deriver_imp_S:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r \<alpha>"
  shows "\<alpha> = [Nt S]"
  using S'_derive_imp_S assms deriver_imp_derive by blast

lemma G_derives_from_S_imp_G'_derives_from_S':
  assumes "Prods G \<turnstile> [Nt S] \<Rightarrow>* w"
  shows "Prods G' \<turnstile> [Nt S'] \<Rightarrow>* w"
  using assms G_derives_imp_G'_derives G'_derive_S
  by fastforce

lemma G_derivers_from_S_imp_G'_derivers_from_S':
  assumes "Prods G \<turnstile> [Nt S] \<Rightarrow>r* w"
  shows "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* w"
proof -
  from G'_derive_S have "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r [Nt S]" 
    by (simp add: derive_singleton deriver_singleton)
  with assms G_derivers_imp_G'_derivers show ?thesis 
    by fastforce
qed


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
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow> \<beta>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow> \<beta>"
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

lemma G'_deriver_imp_G_deriver_if_no_S':
  assumes "Prods G' \<turnstile> \<alpha> \<Rightarrow>r \<gamma>"
  shows "Nt S' \<notin> set \<alpha> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow>r \<gamma>"
  by (smt (verit, ccfv_threshold) Extended_Cfg.G'_Prod_cases Extended_Cfg_axioms assms deriver.cases
      deriver.intros in_set_conv_decomp prod.inject)

lemma G'_derivers_imp_G_derivers_if_no_S':
  "\<lbrakk>Prods G' \<turnstile> \<alpha> \<Rightarrow>r* \<gamma>; Nt S' \<notin> set \<alpha>\<rbrakk> \<Longrightarrow> Prods G \<turnstile> \<alpha> \<Rightarrow>r* \<gamma>"
proof (induction rule: rtranclp_induct)
  case (step \<beta> \<gamma>)
  note step(3)[OF step(4)]
  moreover from this have "Nt S' \<notin> set \<beta>" 
    using S'_notin_Nts_Prods_G derivers_imp_derives derives_set_subset in_Nts_iff_in_Syms step.prems
    by fastforce
  ultimately  show ?case using step G'_deriver_imp_G_deriver_if_no_S'[OF step(2)]
    by simp
qed simp

lemma G'_deriven_Suc_imp_G_deriven:
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
  proof -
    from stepn have "S' \<notin> Nts_syms \<alpha>"  
      using S_neq_S' S_deriven_Suc_imp_all_nts_in_Nts S'_notin_Nts_Prods_G 
      by (cases n) fastforce+
    with G'_derive_imp_G_derive_if_no_S' step_Sucn(2) show ?thesis 
      unfolding Nts_syms_def by blast
  qed
  finally show ?case .
qed


lemma G'_deriven_Suc_imp_no_S':
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) \<beta>"
  shows "S' \<notin> Nts_syms \<beta>"
proof -
  note G_derives = assms[THEN G'_deriven_Suc_imp_G_deriven, THEN relpowp_imp_rtranclp]
  then show ?thesis 
    using S_deriven_Suc_imp_all_nts_in_Nts S'_notin_Nts_Prods_G S_neq_S' 
    by (cases rule: stepcnt_cases) fastforce+
qed 

lemma G'_derivern_Suc_imp_G_derivern:
  "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<beta> \<Longrightarrow> Prods G \<turnstile> [Nt S] \<Rightarrow>r(n) \<beta>"
proof (induction n arbitrary: \<beta>)
  case 0
  then show ?case using S'_deriver_imp_S by auto
next
  case (Suc n)
  then obtain \<alpha> where step_Sucn: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<alpha>" "Prods G' \<turnstile> \<alpha> \<Rightarrow>r \<beta>"
    by (meson relpowp_Suc_E)
  with Suc.IH have stepn: "Prods G \<turnstile> [Nt S] \<Rightarrow>r(n) \<alpha>" 
    by presburger
  also with step_Sucn have "Prods G \<turnstile> ... \<Rightarrow>r \<beta>" 
  proof -
    from stepn have no_S': "S' \<notin> Nts_syms \<alpha>"
      using G'_deriven_Suc_imp_no_S' derivern_imp_deriven step_Sucn(1) by blast
    from step_Sucn(2) show ?thesis proof cases
      case (1 A \<alpha> u v)
      from this(3) show ?thesis using 1 no_S' 
        by (cases rule: G'_Prod_cases) (auto intro: deriver.intros) 
    qed
  qed
  finally show ?case .
qed

lemma G_into_G'_derivers:
  assumes "Prods G \<turnstile> \<alpha> \<Rightarrow>r* \<beta>" "S' \<notin> Nts_syms \<alpha>" "Prods G' \<turnstile> \<beta> \<Rightarrow>r \<gamma>" 
  shows "Prods G \<turnstile> \<beta> \<Rightarrow>r \<gamma>"
proof -
  from assms(1,2) have S'_notin_\<beta>: "S' \<notin> Nts_syms \<beta>" 
    using S'_notin_Nts_Prods_G Nts_Lhss_Rhs_Nts derivers_imp_derives derives_Nts_syms_subset 
    by fastforce
  from assms(3) show ?thesis
  proof cases
    case (1 A \<alpha> u v)
    from this(3) show ?thesis proof (cases rule: G'_Prod_cases)
      case init
      then show ?thesis using 1 S'_notin_\<beta> by simp
    next
      case prod_G
      then show ?thesis using 1 
        by (blast intro: deriver.intros)
    qed
  qed
qed


lemma S'_derives_S'_imp_refl:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>* \<alpha> @ Nt S' # \<beta>"
  shows "\<alpha> = [] \<and> \<beta> = []"
  using assms proof cases
  case (rtrancl_into_rtrancl b)
  then show ?thesis using G'_deriven_Suc_imp_no_S' 
    by (metis Nts_syms_append Un_iff in_Nts_syms list.set_intros(1) relpowp_Suc_I
        rtranclp_imp_relpowp)
qed (simp add: append_eq_Cons_conv)
  
theorem Lang_preserved:
  "LangS G' = LangS G"
proof
  show "LangS G' \<subseteq> LangS G"
  proof
    fix w
    assume "w \<in> LangS G'"
    hence "Prods G' \<turnstile> [Nt S'] \<Rightarrow>* map Tm w" unfolding Lang_def G'_def by simp
    then obtain n where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) map Tm w"
      by (metis G'_derive_S not_derive_map_Tm stepcnt_cases)
    with G'_deriven_Suc_imp_G_deriven have "Prods G \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
      using relpowp_imp_rtranclp by meson
    then show "w \<in> LangS G" unfolding Lang_def by simp
  qed
next
  show "LangS G \<subseteq> LangS G'" using G_derives_from_S_imp_G'_derives_from_S'
    unfolding Lang_def G'_def by auto
qed

corollary G'_not_empty: 
  "LangS G' \<noteq> {}" 
  using Lang_preserved G_not_empty by simp


lemma Nts_G'_is_union[simp]: "Nts (Prods G) \<union> {S',S} = Nts (Prods G')"
  using G'_def in_Nts_iff_in_Syms by force

lemma in_Lang_imp_S_derives:
  assumes "w \<in> LangS G'"
  shows "Prods G' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
  using assms unfolding Lang_def 
  by (metis G_derives_imp_G'_derives Lang_def Lang_preserved mem_Collect_eq)


lemma G'_reduced:
   "reduced G'"
proof - 
  have S_in_Nts_G: "S \<in> Nts (Prods G)"
    using G_not_empty by (metis Lang_empty_if_notin_Lhss Nts_Lhss_Rhs_Nts Un_iff)
  then have "\<forall>A \<in> Nts (Prods G). useful (Prods G') S' A"
    using G_reduced G_derives_imp_G'_derives unfolding reduced_def useful_def Lang_def 
    by (metis G_derives_from_S_imp_G'_derives_from_S') 
  moreover have "useful (Prods G') S' S'" 
    using Lang_nempty_imp_useful_S G_not_empty Lang_preserved G'_def by fastforce
  ultimately show ?thesis using Nts_G'_is_union S_in_Nts_G unfolding reduced_def G'_def by force
qed

end
end
