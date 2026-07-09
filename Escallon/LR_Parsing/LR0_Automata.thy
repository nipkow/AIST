theory LR0_Automata
  imports 
    Item_Pushdown_Automata
    Rightmost_Chain
begin

section \<open>The Canonical LR(0) Parser's Underlying Automata\<close>

context Extended_Cfg
begin

interpretation I: ipda G IPDA 
  by standard simp

corollary ipda_IPDA: 
  "ipda G IPDA"
  by (rule I.ipda_axioms)

abbreviation IPDA_step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>I\<close> 55) where
  "(\<turnstile>I) \<equiv> (ipda.step IPDA)"

abbreviation IPDA_steps :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>I*\<close> 55) where
  "(\<turnstile>I*) \<equiv> (ipda.steps IPDA)"

abbreviation IPDA_stepn :: "('n,'t) item list \<times> 't list \<Rightarrow> nat \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" ( \<open>_ \<turnstile>I'(_') _\<close> 55) where
  "c0 \<turnstile>I(n) c1 \<equiv> (ipda.stepn IPDA) c0 n c1"

subsection \<open>The Characteristic Finite Automaton to a Context-Free Grammar\<close>

definition char_fa :: "(('n, 't) sym, ('n, 't) item) nfa" where
  "char_fa \<equiv> let 
      P = Prods G';
      \<Delta> = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>]  \<Rightarrow> if a = Y \<and> (X, \<alpha>@Y#\<beta>) \<in> P then {[X \<rightarrow> \<alpha>@[Y] \<cdot> \<beta>]} else {}| 
         _ \<Rightarrow> {}); 
      \<E> = {([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @Nt Y#\<beta>) \<in> P \<and> (Y, \<gamma>) \<in> P} in
    \<lparr>nfa.states = It G', nfa.init = {[S' \<rightarrow> [] \<cdot> [Nt S]]}, nfa.final = completes (It G'), 
      nfa.nxt = \<Delta>, nfa.eps = \<E>\<rparr>"

subsubsection \<open>Basic Properties\<close>

lemma states_char_fa [simp]: 
  "nfa.states char_fa = It G'"
  unfolding char_fa_def by (meson nfa.select_convs(1))

lemma init_char_fa [simp]:
  "nfa.init char_fa = {[S' \<rightarrow> [] \<cdot> [Nt S]]}"
  unfolding char_fa_def by (meson nfa.select_convs(2))

lemma final_char_fa [simp]:
  "nfa.final char_fa = completes (It G')"
  unfolding char_fa_def by (meson nfa.select_convs(3))

lemma nxt_char_fa [simp]:
  "nfa.nxt char_fa = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>]  \<Rightarrow> if a = Y \<and> ((X, \<alpha> @ Y # \<beta>) \<in> Prods G') then {[X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>]} 
  else {} | _ \<Rightarrow> {})"
  unfolding char_fa_def by (meson nfa.select_convs(4))

lemma nxt_char_fa_neq_or_not_Prod_imp_empty:
  assumes "Y \<noteq> a \<or> (X, \<alpha> @ Y # \<beta>) \<notin> Prods G'"
  shows "nfa.nxt char_fa [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] a = {}" 
  using assms by auto

lemma nxt_char_fa_in_Prods_imp_singleton:
  assumes "(X, \<alpha> @ Y # \<beta>) \<in> Prods G'"
  shows "nfa.nxt char_fa [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] Y = {[X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>]}"
  using assms by simp

lemma nxt_char_fa_nempty_imp_hd:
  assumes "nfa.nxt char_fa [X \<rightarrow> \<alpha> \<cdot> \<beta>] a \<noteq> {}" 
  obtains \<gamma> where "\<beta> = a # \<gamma>" "(X, \<alpha>@\<beta>) \<in> Prods G'"
  using assms 
  by (metis (lifting) nxt_char_fa_neq_or_not_Prod_imp_empty item.case list.exhaust list.simps(4)
      nxt_char_fa)

lemma in_nxt_char_fa_imp_shift:
  assumes "q \<in> nfa.nxt char_fa p a"
  obtains X \<alpha> \<beta> where "p = [X \<rightarrow> \<alpha> \<cdot> a # \<beta>]" "q = [X \<rightarrow> \<alpha> @ [a] \<cdot> \<beta>]"
proof -
  obtain X \<alpha> \<beta> Y \<gamma> \<delta> where pq_defs: "p = [X \<rightarrow> \<alpha> \<cdot> \<beta>]" "q = [Y \<rightarrow> \<gamma> \<cdot> \<delta>]" 
    using item.exhaust by meson
  moreover with nxt_char_fa_nempty_imp_hd assms obtain \<zeta> where "\<beta> = a # \<zeta>" "(X, \<alpha>@\<beta>) \<in> Prods G'" 
    by blast
  moreover with nxt_char_fa_in_Prods_imp_singleton have "q = [X \<rightarrow> \<alpha> @ [a] \<cdot> \<zeta>]"
    using assms pq_defs(1) by blast
  ultimately show thesis using that by presburger
qed

lemma char_fa_nxts_is_shifts:
  assumes "Q \<subseteq> It G'"
  shows "(\<Union>i \<in> Q. nfa.nxt char_fa i A) = {[X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q}"
  (is "?Un = ?S")
proof (standard; standard)
  fix i
  assume Un: "i \<in> ?Un"
  then obtain j where in_nxt: "i \<in> nfa.nxt char_fa j A" by blast
  consider X \<alpha> where "j = [X \<rightarrow> \<alpha> \<cdot> []]" | X \<alpha> \<beta> where "j = [X \<rightarrow> \<alpha> \<cdot> A # \<beta>]" | 
    X \<alpha> B \<beta> where "j = [X \<rightarrow> \<alpha> \<cdot> B # \<beta>]" "B \<noteq> A" 
    by (metis item.exhaust neq_Nil_conv)
  thus "i \<in> ?S" using in_nxt Un in_nxt_char_fa_imp_shift by cases force+
next
  fix i 
  assume S: "i \<in> ?S"
  then obtain X \<alpha> \<beta> where "i = [X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]" "[X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q" by blast
  moreover then have "nfa.nxt char_fa [X \<rightarrow> \<alpha> \<cdot> A # \<beta>] A = {i}" 
    using assms in_It_imp_in_Prods by force
  ultimately show "i \<in> ?Un" by blast
qed

lemma eps_char_fa [simp]:
  "nfa.eps char_fa 
    = {([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G' \<and> (Y, \<gamma>) \<in> Prods G'}"
  unfolding char_fa_def by (meson nfa.select_convs(5))

lemma eps_char_faE [elim]:
  assumes "(i, j) \<in> nfa.eps char_fa"
  obtains X \<alpha> Y \<beta> \<gamma> where "(X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G'" "(Y, \<gamma>) \<in> Prods G'"
    "i = [X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>]" "j = [Y \<rightarrow> [] \<cdot> \<gamma>]"
  using assms unfolding eps_char_fa by blast

lemma eps_char_fa_subst_states:
  "nfa.eps char_fa \<subseteq> nfa.states char_fa \<times> nfa.states char_fa"
  using in_Prods_imp_in_It by force

lemma deriver_singleton_imp_eps:
  assumes "Prods G' \<turnstile> [Nt A] \<Rightarrow>r \<alpha>"
    "[X \<rightarrow> \<beta> \<cdot> Nt A # \<gamma>] \<in> It G'"
  shows "([X \<rightarrow> \<beta> \<cdot> Nt A # \<gamma>], [A \<rightarrow> [] \<cdot> \<alpha>]) \<in> nfa.eps char_fa"
  unfolding eps_char_fa using assms deriver_singleton in_It_imp_in_Prods
  by fastforce

lemma prod_imp_eps:
  assumes "(A, \<alpha>) \<in> Prods G'"
    "[X \<rightarrow> \<beta> \<cdot> Nt A # \<gamma>] \<in> It G'"
  shows "([X \<rightarrow> \<beta> \<cdot> Nt A # \<gamma>], [A \<rightarrow> [] \<cdot> \<alpha>]) \<in> nfa.eps char_fa"
  using deriver_singleton_imp_eps deriver_singleton assms by metis

sublocale char_fa: nfa char_fa 
proof (unfold_locales, goal_cases 1 2 nxt_closed 3)
  case 2
  then show ?case 
    using G'_def It_defs finite_It[OF G'_finite] completes_subset by force
next
  case (nxt_closed q x)
  then obtain X \<alpha> \<beta> where q_def: "q = [X \<rightarrow> \<alpha> \<cdot> \<beta>]" by (metis item.exhaust)
  consider (empty) "\<beta> = []" | (eq) xs where "\<beta> = x # xs" | (neq) y ys where "\<beta> = y # ys" "y \<noteq> x"
    by (metis list.exhaust)
  then show ?case 
  proof cases
    case eq
    then show ?thesis 
      using nxt_closed q_def by (auto simp: It_defs)
  qed (use nxt_closed q_def in fastforce)+
qed (use G'_def It_defs finite_It[OF G'_finite] in fastforce)+

subsubsection \<open>Properties of \<epsilon>-transitions and the \<epsilon>-closure\<close>

lemma in_eps_char_imp_in_It:
  assumes "(p,q) \<in> nfa.eps char_fa"
  shows "p \<in> It G' \<and> q \<in> It G'"
  using assms in_Prods_imp_in_It unfolding eps_char_fa by force

lemma in_eps_char_star_imp_in_It:
  assumes "(p,q) \<in> (nfa.eps char_fa)\<^sup>*"
    "p \<in> It G'"
  shows "q \<in> It G'"
  using assms in_eps_char_imp_in_It 
    by (induction rule: rtrancl_induct) simp_all

lemma char_fa_epsclo_It_intersect_eq [simp]:
  "char_fa.epsclo (Q \<inter> It G') = char_fa.epsclo Q"
proof 
  show "char_fa.epsclo Q \<subseteq> char_fa.epsclo (Q \<inter> It G')"
  proof
    fix q
    assume q_in_epsclo: "q \<in> char_fa.epsclo Q"
    then obtain p where "q \<in> It G'" "p \<in> Q" "(p, q) \<in> (nfa.eps char_fa)\<^sup>*" 
      unfolding char_fa.epsclo_def states_char_fa by blast
    moreover then have "p \<in> It G'" by (metis converse_rtranclE in_eps_char_imp_in_It)
    ultimately show "q \<in> char_fa.epsclo (Q \<inter> It G')" 
       using q_in_epsclo char_fa.epsclo_def by blast
  qed
qed (auto simp add: char_fa.epsclo_def)

lemma eps_star_of_char_state_subset_states:
  "q \<in> nfa.states char_fa \<Longrightarrow> {q'. (q, q') \<in> (nfa.eps char_fa)\<^sup>*} \<subseteq> nfa.states char_fa"
  using in_eps_char_star_imp_in_It in_eps_char_imp_in_It by auto

lemma subset_states_char_imp_epsclo_eq_UN_eps_star:
  assumes "Q \<subseteq> nfa.states char_fa"
  shows "char_fa.epsclo Q = (\<Union>q\<in>Q. {q'. (q, q') \<in> (nfa.eps char_fa)\<^sup>*})"
proof -
  let ?Qc = "nfa.states char_fa"
  have "char_fa.epsclo Q = ?Qc \<inter> (\<Union>q\<in>Q. {q'. (q, q') \<in> (nfa.eps char_fa)\<^sup>*})"
    unfolding char_fa.epsclo_def by presburger
  also have "... = (\<Union>q\<in>Q. {q'. (q, q') \<in> (nfa.eps char_fa)\<^sup>*} \<inter> ?Qc) " by blast
  also from assms eps_star_of_char_state_subset_states have 
    "... = (\<Union>q\<in>Q. {q'. (q, q') \<in> (nfa.eps char_fa)\<^sup>*})" by fast
  finally show ?thesis .
qed

lemma in_It_imp_eps_char_fa:
  assumes "[X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] \<in> It G'"
  obtains \<gamma> where "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>]) \<in> nfa.eps char_fa"
proof -
  from assms have X_prod: "(X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G'" using in_It_imp_in_Prods by fastforce
  with reduced_imp_prod_substring_derives_Tms[of X \<alpha> "[Nt Y]" \<beta>, OF _ G'_reduced] 
  obtain \<gamma> where "(Y, \<gamma>) \<in> Prods G'" by (metis derives_Nt_Cons_map_Tm append_Cons eq_Nil_appendI)
  with that X_prod show thesis unfolding eps_char_fa by blast
qed

lemma in_It_imp_eps_char_fa_distinct:
  assumes "[X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] \<in> It G'"
  obtains \<gamma> where "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>]) \<in> nfa.eps char_fa" 
    "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>]) \<noteq> ([Y \<rightarrow> [] \<cdot> \<gamma>])"
proof -
  from in_It_imp_eps_char_fa obtain \<gamma> where 
    \<gamma>_def: "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>]) \<in> nfa.eps char_fa"
    using assms by blast
  show thesis
  proof (cases "[X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] = [Y \<rightarrow> [] \<cdot> \<gamma>]")
    case True
    with reduced_imp_prod_distinct[OF _ G'_reduced] obtain \<gamma>' where "(Y, \<gamma>') \<in> Prods G'"
      "Nt Y \<notin> set \<gamma>'" using assms[THEN in_It_imp_in_Prods] by auto
    moreover with True have "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>']) \<in> nfa.eps char_fa"
      unfolding eps_char_fa using assms[THEN in_It_imp_in_Prods] by fastforce
    ultimately show ?thesis using that unfolding eps_char_fa by force
  qed (use that \<gamma>_def in presburger)
qed

lemma derivern_non_word_imp_hd_eps_reachable:
  assumes "Prods G' \<turnstile> [Nt A] \<Rightarrow>r(Suc n) Y # \<gamma>"
    "Nts_syms (Y # \<gamma>) \<noteq> {}"
  obtains \<alpha> X \<beta> where "[A \<rightarrow> [] \<cdot> \<alpha>] \<in> It G'" 
    "([A \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> [] \<cdot> Y # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
  using assms proof (induction n arbitrary: Y \<gamma> thesis)
  case 0
  then show ?case using 0(1)[of "Y # \<gamma>" A \<gamma>] in_Prods_imp_in_It deriver_singleton 
    by (metis append_Nil item.case relpowp_Suc_0 rtrancl.rtrancl_refl)
next
  case (Suc n)
  then obtain X \<delta> where step_Sucn:"Prods G' \<turnstile> [Nt A] \<Rightarrow>r(Suc n) X # \<delta>" "Prods G' \<turnstile> X # \<delta> \<Rightarrow>r Y # \<gamma>" 
    by (metis deriven_from_empty deriver_imp_derive list.exhaust relpowp_Suc_0 relpowp_Suc_E)
  hence Nts_X\<delta>: "Nts_syms (X # \<delta>) \<noteq> {}" 
    by (metis Nts_syms_empty_iff deriver_imp_derive not_derive_map_Tm)
  from Suc.IH[OF _ step_Sucn(1) this] obtain \<alpha> W \<beta> where ih:
    "[A \<rightarrow> [] \<cdot> \<alpha>] \<in> It G'" "([A \<rightarrow> [] \<cdot> \<alpha>], [W \<rightarrow> [] \<cdot> X # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
    by blast
  consider (Tms) w where "\<delta> = map Tm w" | (rightmost) \<zeta> Z w where "\<delta> = \<zeta> @ Nt Z # map Tm w"
    by (meson Tms_iff_no_Nts syms_split_rightmost)
  then show ?case proof cases
    case Tms
    with step_Sucn obtain X' where NtX': "X = Nt X'" using Nts_X\<delta> 
      by (metis Nts_syms_map_Tm destTm.cases list.simps(9))
    then obtain \<chi> where X'_Prod: "(X', \<chi>) \<in> Prods G'" "\<chi> @ \<delta> = Y # \<gamma>" 
      using Tms step_Sucn(2) deriver.cases 
      by (smt (verit) append_self_conv2 rm_eq_imp_eq)
    have "\<chi> \<noteq> []"
      by standard (use X'_Prod Tms Suc.prems(3) in auto)
    with X'_Prod obtain \<zeta> where \<zeta>_def: "\<chi> = Y # \<zeta>" by (metis Cons_eq_append_conv)
    note ih(2)[unfolded NtX']
    also from this have "([W \<rightarrow> [] \<cdot> Nt X' # \<beta>], [X' \<rightarrow> [] \<cdot> Y # \<zeta>]) \<in> nfa.eps char_fa"
      using in_eps_char_star_imp_in_It ih(1) X'_Prod[unfolded \<zeta>_def]
        NtX' prod_imp_eps by blast
    finally show ?thesis using Suc.prems(1) ih(1) by fast
  next
    case rightmost
    obtain \<eta> where "X # \<zeta> @ \<eta> @ map Tm w = Y # \<gamma>"
    proof -
      from deriver.cases[OF step_Sucn(2)] rightmost obtain \<eta> where
        "X # \<delta> = (X # \<zeta>) @ Nt Z # map Tm w" "Y # \<gamma> = (X # \<zeta>) @ \<eta> @ map Tm w" "(Z, \<eta>) \<in> Prods G'"
        by (smt (verit) append_Cons rm_eq_imp_eq) 
      thus thesis using that append.assoc by simp
    qed
    then show ?thesis using ih Suc.prems(1) by fast
  qed
qed

lemma produced_imp_in_eps_star:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) Nt A # map Tm w"
  obtains X \<beta> where "([S' \<rightarrow> [] \<cdot> [Nt S]], [X \<rightarrow> [] \<cdot> Nt A # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
proof -
  from derivern_non_word_imp_hd_eps_reachable[OF assms] obtain 
    X \<beta> where "([S' \<rightarrow> [] \<cdot> [Nt S]], [X \<rightarrow> [] \<cdot> Nt A # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*" 
  proof -
    from derivern_non_word_imp_hd_eps_reachable[OF assms] obtain 
    X \<alpha> \<beta> where "([S' \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> [] \<cdot> Nt A # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*" 
      "[S' \<rightarrow> [] \<cdot> \<alpha>] \<in> It G'" 
      by (metis all_not_in_conv in_Nts_syms list.set_intros(1))
    moreover from this have "\<alpha> = [Nt S]" using in_It_imp_in_Prods 
      using S'_derive_imp_S derive_singleton by fastforce
    ultimately show thesis using that by blast
  qed
  thus ?thesis using that by blast
qed 

lemma in_eps_S'_imp_left_Nil:
   "([S' \<rightarrow> [] \<cdot> [Nt S]], [A \<rightarrow> \<alpha> \<cdot> \<beta>]) \<in> (nfa.eps char_fa)\<^sup>* \<Longrightarrow> \<alpha> = []"
  by (induction "[A \<rightarrow> \<alpha> \<cdot> \<beta>]" rule: rtrancl_induct) auto

lemma in_eps_S'_imp_produced:
  assumes "([S' \<rightarrow> [] \<cdot> [Nt S]], [A \<rightarrow> \<alpha> \<cdot> \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
  obtains w where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* Nt A # map Tm w"
  using assms proof (induction "[A \<rightarrow> \<alpha> \<cdot> \<beta>]" arbitrary: A \<alpha> \<beta> thesis rule: rtrancl_induct)
  case base
  from this[of "[]"] show ?case by simp
next
  case (step i)
  hence Nil: "\<alpha> = []" by fastforce
  from step(2) obtain B \<delta> where i_def: "i = [B \<rightarrow> [] \<cdot> Nt A # \<delta>]" using item.exhaust 
    using in_eps_S'_imp_left_Nil step.hyps(1) by auto
  then obtain x where \<delta>_derivers: "Prods G' \<turnstile> \<delta> \<Rightarrow>r* map Tm x"
  proof -
    from step(1) have "(B, Nt A # \<delta>) \<in> Prods G'"
      using i_def step.hyps(2) by force
    with reduced_imp_prod_substring_derives_Tms[of B "[Nt A]" \<delta> "[]", OF _ G'_reduced]
    show thesis using derivers_iff_derives 
      by (metis append.right_neutral append_Cons append_Nil that)
  qed
  from i_def step obtain w where B_steps: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* Nt B # map Tm w" by blast
  also from step(2) have "Prods G' \<turnstile> ... \<Rightarrow>r Nt A # \<delta> @ map Tm w" unfolding i_def 
    using deriver.intros[of _ _ _ "[]"] by fastforce
  also have "Prods G' \<turnstile> ... \<Rightarrow>r* Nt A # map Tm x @ map Tm w"
    using derivers_append_map_Tm[OF \<delta>_derivers, of w, THEN derivers_prepend[of _ _ _ "[Nt A]"]]
    by simp
  finally show ?case using step.prems[of "x@w"] by auto
qed

lemma in_char_eps_imp_IPDA_reachable:
  assumes "(i, j) \<in> (nfa.eps char_fa)\<^sup>*"
  obtains \<sigma> where "(i # \<rho>, w) \<turnstile>I* (j # \<sigma> @ \<rho>, w)"
  using assms proof (induction arbitrary: thesis rule: rtrancl_induct)
  case base
  from base[of "[]"] show ?case by simp
next
  case (step j k)
  from step.hyps(2) obtain A \<alpha> X \<beta> \<gamma> where eps: "j = [A \<rightarrow> \<alpha> \<cdot> Nt X # \<beta>]" "k = [X \<rightarrow> [] \<cdot> \<gamma>]"
    "(A, \<alpha> @ Nt X # \<beta>) \<in> Prods G'" "(X, \<gamma>) \<in> Prods G'" by blast
  from step.IH obtain \<sigma> where "(i # \<rho>, w) \<turnstile>I* (j # \<sigma> @ \<rho>, w)" by blast
  also from eps have "... \<turnstile>I (k # j # \<sigma> @ \<rho>, w)" 
    using I.expanding by presburger
  finally show ?case using step.prems[of "j # \<sigma>"] by simp
qed

subsubsection \<open>Properties of \<open>char(G)\<close> computations\<close>

notation char_fa.step (infix \<open>\<turnstile>c\<close> 55)
notation char_fa.steps (infix \<open>\<turnstile>c*\<close> 55)
notation char_fa.stepn (\<open>_ \<turnstile>c'(_') _\<close> 55)

lemma char_step_cases[consumes 1, case_names nxt eps, cases set: char_fa.step]:
  assumes "c0 \<turnstile>c c1"
  obtains 
    X \<alpha> Y \<beta> \<gamma> where "c0 = ([X \<rightarrow> \<alpha> \<cdot> Y # \<beta>], Y # \<gamma>)" "c1 = ([X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>], \<gamma>)" 
                      "(X, \<alpha> @ Y # \<beta>) \<in> Prods G'" |
    X \<alpha> Y \<beta> \<delta> \<gamma> where "c0 = ([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], \<delta>)" "c1 = ([Y \<rightarrow> [] \<cdot> \<gamma>], \<delta>)" "(Y, \<gamma>) \<in> Prods G'"
                      "(X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G'"
  using assms proof cases
  case (step_nxt q p a u)
  then show ?thesis using that(1) in_nxt_char_fa_imp_shift nxt_char_fa_neq_or_not_Prod_imp_empty 
    by (metis emptyE)
next
  case (step_eps p q w)
  then show ?thesis unfolding eps_char_fa using that(2) by blast
qed

lemma char_step_imp_in_Prods [dest]:
  assumes "(p, \<alpha>) \<turnstile>c (q, \<beta>)"
  shows "prod_of_item p \<in> Prods G' \<and> prod_of_item q \<in> Prods G'"
  using assms by cases auto

lemma char_stepn_Suc_imp_in_Prods:
  "(p, \<alpha>) \<turnstile>c(Suc n) (q, \<beta>) \<Longrightarrow> prod_of_item p \<in> Prods G' \<and> prod_of_item q \<in> Prods G'"
  using char_step_imp_in_Prods by (induction n) 
    (force, metis (lifting) relpowp_Suc_E relpowp_Suc_E2 surj_pair)

lemma char_steps_in_Prods_imp_in_Prods:
  assumes "prod_of_item p \<in> Prods G'"
   "(p, \<alpha>) \<turnstile>c* (q, \<beta>)" 
 shows "prod_of_item p \<in> Prods G' \<and> prod_of_item q \<in> Prods G'"
  using assms rtranclp_imp_relpowp char_stepn_Suc_imp_in_Prods
  by (metis (no_types, lifting) prod.inject relpowp_E)

lemma char_reachable_imp_substring:
  assumes "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], \<delta>)"
  obtains \<zeta> where "\<gamma> = \<zeta> @ \<alpha> @ \<delta>"
  using assms proof (induction "([A \<rightarrow> \<alpha> \<cdot> \<beta>], \<delta>)" arbitrary: A \<alpha> \<beta> \<delta> thesis rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step c)
  from this(2) show ?case 
  proof cases
    case (eps X \<alpha>' Y \<beta>' \<zeta> \<gamma>')
    from step(3)[OF this(1)] obtain \<eta> where "\<gamma> = \<eta> @ \<alpha>' @ \<zeta>" .
    then show ?thesis using eps step by auto
  qed (use step in force)   
qed

lemma char_steps_append:
  "(p, \<alpha> @ \<beta>) \<turnstile>c* (q, \<beta>) \<Longrightarrow> (p, \<alpha> @ \<gamma>) \<turnstile>c* (q, \<gamma>)"
proof (induction p "\<alpha> @ \<beta>" arbitrary: \<alpha> rule: converse_rtranclp_induct2)
  case (step p q \<delta>)
  show ?case 
  proof (cases \<alpha>)
    case Nil
    then show ?thesis using step 
      by (meson char_fa.stepn_append converse_rtranclp_into_rtranclp rtranclp_power)
  next
    case (Cons X \<alpha>')
    then show ?thesis using step 
      by (meson char_fa.stepn_append relpowp_Suc_I2 rtranclp_power)
  qed
qed simp

lemma char_consumes_last_imp_butlast_reaches:
  assumes "([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha> @ [X]) \<turnstile>c* ([A \<rightarrow> \<alpha> @ [X] \<cdot> \<gamma>], [])"
  shows "([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> [X] @ \<gamma>], [])"
proof -
  from assms obtain n where n_steps: 
    "([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha> @ [X]) \<turnstile>c(n) ([A \<rightarrow> \<alpha> @ [X] \<cdot> \<gamma>], [])"
    using rtranclp_imp_relpowp by fast
  show ?thesis
  proof (cases n)
    case (Suc m)
    then obtain i \<zeta> where m_steps: "([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha> @ [X]) \<turnstile>c(m) (i, \<zeta>)"
      "(i, \<zeta>) \<turnstile>c ([A \<rightarrow> \<alpha> @ [X] \<cdot> \<gamma>], [])"
      using n_steps by auto
    from this(2) show ?thesis proof cases
      case (nxt Y \<alpha> Z \<beta> \<gamma>)
      then show ?thesis using m_steps char_fa.steps_append[of _ "\<delta> @ \<alpha>" "[X]" _ "[]"]
        by (simp add: relpowp_imp_rtranclp) 
    qed fast
  qed (use n_steps in simp)
qed

lemma char_steps_consume:
  "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G' \<Longrightarrow> ([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>], \<beta> @ \<delta>) \<turnstile>c* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>], \<delta>)"
proof (induction \<beta> arbitrary: \<alpha>)
  case (Cons X \<beta>)
  hence "([A \<rightarrow> \<alpha> \<cdot> (X # \<beta>) @ \<gamma>], (X # \<beta>) @ \<delta>) \<turnstile>c ([A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta> @ \<gamma>], \<beta> @ \<delta>)" by auto
  also from Cons.IH[of "\<alpha> @ [X]"] have "... \<turnstile>c* ([A \<rightarrow> \<alpha> @ X # \<beta> \<cdot> \<gamma>], \<delta>)" 
    using Cons.prems by simp
  finally show ?case .
qed simp

lemma char_steps_unchanged_imp_in_eps_star:
  "(p, \<zeta>) \<turnstile>c* (q, \<zeta>) \<Longrightarrow> (p, q) \<in> (nfa.eps char_fa)\<^sup>*"
proof (induction "(p, \<zeta>)" arbitrary: p rule: converse_rtranclp_induct)
  case (step c)
  from this(1) show ?case 
  proof cases
    case (eps X \<alpha> Y \<beta> \<delta> \<gamma>)
    then obtain r where "c = (r, \<zeta>)" by blast
    with step have "(p, r) \<in> nfa.eps char_fa" by blast
    also note eps_star = step(3)[OF \<open>c = (r, \<zeta>)\<close>]
    finally show ?thesis .
  qed (use step(2) char_fa.steps_len_dec in fastforce)
qed simp

lemma in_eps_star_imp_char_steps_unchanged: 
  "(p, q) \<in> (nfa.eps char_fa)\<^sup>* \<Longrightarrow> (p, \<zeta>) \<turnstile>c* (q, \<zeta>)"
proof (induction rule: converse_rtrancl_induct)
  case (step y z)
  with char_fa.step_eps[OF this(1), of \<zeta>] show ?case by simp
qed simp

lemma char_step_left_nonempty_imp_not_eps:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>], X # \<gamma>) \<turnstile>c ([B \<rightarrow> \<delta> @ [Y] \<cdot> \<zeta>], \<eta>)"
  obtains \<beta>' where "\<beta> = X # \<beta>'" "([B \<rightarrow> \<delta> @ [Y] \<cdot> \<zeta>], \<eta>) = ([A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>'], \<gamma>)"
  using assms by cases fast+

lemma char_eps_impossible:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>], []) \<turnstile>c ([B \<rightarrow> \<delta> @ [Y] \<cdot> \<zeta>], \<eta>)"
  shows False using assms by cases auto

lemma char_reaches_left_empty_imp_expanded_last:
  assumes "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c* ([A \<rightarrow> [] \<cdot> \<beta>], [])"
  obtains Y \<delta> \<zeta> where "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c* ([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], [])"
    "([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], []) \<turnstile>c* ([A \<rightarrow> [] \<cdot> \<beta>], [])"
proof -
  from assms obtain n where "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c(n) ([A \<rightarrow> [] \<cdot> \<beta>], [])"
    using rtranclp_imp_relpowp by fast
  with that show thesis proof (induction n arbitrary: A \<beta> thesis)
    case (Suc n)
    note Suc_n = this
    then obtain Y \<delta> \<zeta> \<eta> where step: "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c(n) ([Y \<rightarrow> \<delta> \<cdot> \<zeta>], \<eta>)"
      "([Y \<rightarrow> \<delta> \<cdot> \<zeta>], \<eta>) \<turnstile>c ([A \<rightarrow> [] \<cdot> \<beta>], [])"    
      by (metis item.exhaust relpowp_Suc_E surj_pair)
    from this(2) show ?case proof cases
      case (nxt)
      then show ?thesis using Suc by fast
    next
      case (eps)
      show ?thesis proof (cases n)
        case 0
        then show ?thesis using Suc step eps by auto
      next
        case (Suc m)
        show ?thesis proof (cases \<delta> rule: rev_cases)
          case Nil
          then show ?thesis using Suc_n step 
            by (smt (verit, best) eps(1,2) prod.inject rtranclp.rtrancl_into_rtrancl)
        next
          case (snoc \<delta>' Z)
          with Suc step have
            "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c(m) ([Y \<rightarrow> \<delta>' \<cdot> Z # \<zeta>], [Z])"
            "([Y \<rightarrow> \<delta>' \<cdot> Z # \<zeta>], [Z]) \<turnstile>c ([Y \<rightarrow> \<delta>' @ [Z] \<cdot> \<zeta>], [])" 
            using char_step_left_nonempty_imp_not_eps char_eps_impossible
            by (smt (verit, del_insts) Extended_Cfg.char_step_cases Extended_Cfg_axioms 
                append1_eq_conv eps(1,2) item.inject prod.inject relpowp_Suc_E,
            use eps(1,4) snoc in force)
          moreover with char_reachable_imp_substring have "X = Z" 
            by (metis append1_eq_conv append_assoc relpowp_imp_rtranclp)
          ultimately show ?thesis using Suc_n(2) snoc step 
            by (metis Pair_inject eps(1,2) r_into_rtranclp relpowp_imp_rtranclp)
        qed
      qed
    qed
  qed simp
qed

subsection \<open>Equivalences between \<open>char(G)\<close>, \<open>IPDA\<close>, and rightmost derivations\<close>

text \<open>Step 1: If \<open>char(G)\<close> reaches \<open>([A \<rightarrow> \<alpha>.\<beta>], \<epsilon>)\<close> with input \<open>\<gamma>\<close>, 
      \<open>\<gamma>\<close>  is a reliable prefix of G for \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close>.\<close>

lemma char_imp_derivers:
  assumes "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])"
  obtains \<gamma>' w where 
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w"
    "\<gamma> = \<gamma>' @ \<alpha>"
proof -
  from assms obtain n where "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c(n) ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])"
    using rtranclp_imp_relpowp by fast
  with that show thesis
  proof (induction n arbitrary: \<gamma> A \<alpha> \<beta> thesis)
    case 0
    then show ?case using 0(1)[of "[]" "[]"] G'_derive_S 
      by (simp add: G'_def deriver_singleton)
  next
    case (Suc n)
    then obtain c where n_steps: "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c(n) c" "c \<turnstile>c ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])" 
      by auto
    from this(2) show ?case 
    proof cases
      case (nxt X \<alpha>' Y \<beta>' \<gamma>')
      moreover with n_steps obtain \<delta> where \<delta>_def: "\<gamma> = \<delta> @ \<alpha>' @ [Y]" 
        using char_reachable_imp_substring[of \<gamma> X \<alpha>' "Y # \<beta>'" "[Y]"] relpowp_imp_rtranclp 
        by (metis prod.inject)
      ultimately have "([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha>') \<turnstile>c(n) ([X \<rightarrow> \<alpha>' \<cdot> Y # \<beta>'], [])"
        using n_steps nfa.stepn_append[OF char_fa.nfa_axioms, of _ _ "\<delta> @ \<alpha>'" "[Y]" _ "[]"] 
        by auto
      from Suc.IH[OF _ this] obtain \<zeta> w where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<zeta> @ Nt A # map Tm w"
        "Prods G' \<turnstile> \<zeta> @ Nt A # map Tm w \<Rightarrow>r \<zeta> @ \<alpha>' @ Y # \<beta> @ map Tm w" "\<delta> @ \<alpha>' = \<zeta> @ \<alpha>'"
        using nxt by auto
      then show ?thesis using nxt Suc.prems(1) by (simp add: \<delta>_def)
    next
      case (eps X \<alpha>' Y \<beta>' \<delta> \<gamma>')
      with n_steps Suc.IH[of X \<alpha>' "Nt Y # \<beta>'"] obtain \<zeta> w where X_deriv:
        "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<zeta> @ Nt X # map Tm w"
        "Prods G' \<turnstile> \<zeta> @ Nt X # map Tm w \<Rightarrow>r \<zeta> @ \<alpha>' @ Nt A # \<beta>' @ map Tm w" "\<gamma> = \<zeta> @ \<alpha>'"
        by auto
      moreover from this obtain v where \<beta>_deriv: "Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm v"
        using reduced_derives_imp_substring_derives_Tms[OF _ G'_reduced G'_not_empty, of "\<zeta>@\<alpha>'@[Nt A]" \<beta>']
          derivers_imp_derives
        by (metis (no_types, opaque_lifting) Cfg.sel(2) G'_def append.assoc append_Cons append_Nil
            derivers_iff_derives rtranclp.rtrancl_into_rtrancl)
      have "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm (v@w)"
      proof -
        note X_deriv(1)
        also note X_deriv(2)
        also from \<beta>_deriv have 
          "Prods G' \<turnstile>  \<zeta> @ \<alpha>' @ Nt A # \<beta>' @ map Tm w \<Rightarrow>r*  \<zeta> @ \<alpha>' @ Nt A # map Tm (v@w)"
          by (metis append_Cons append_Nil derivers_append_map_Tm derivers_prepend map_append)
        finally show ?thesis using X_deriv(3) by simp
      qed
      moreover have "Prods G' \<turnstile> ... \<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm (v@w)"
        using eps(2,3) deriver.intros[of A "\<alpha>@\<beta>" _ \<gamma> "v@w"] by simp
      ultimately show ?thesis using Suc.prems(1)[of \<gamma> "v@w"] eps by blast  
    qed
  qed
qed

text \<open>Step 2: For every rightmost derivation \<open>S' \<Rightarrow>r* \<gamma>'Aw \<Rightarrow>r \<gamma>'\<alpha>\<beta>w\<close> there exists a \<open>\<rho> \<in> It\<^sub>G\<^sup>*\<close> 
      such that the configuration \<open>([A \<rightarrow> \<alpha>.\<beta>]\<rho>, vw)\<close> is accepted by the \<open>IPDA\<close> for any \<open>v \<in> V\<^sub>T\<^sup>*\<close> 
      such that \<open>\<beta> \<Rightarrow>r* v\<close>.\<close>

lemma derivers_imp_ipda:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma> @ Nt A # map Tm w \<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm w"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v"
  obtains \<rho> where 
    "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v@w) \<turnstile>I* ([I.final_state], [])" 
    "hist (rev \<rho>) = \<gamma>"
  using assms(1) proof cases
  case rtrancl_refl
  with assms have eqs: "\<gamma> = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S]" 
    using S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
  then show thesis using S'_derive_imp_S I.deriver_imp_IPDA_comp assms that 
    by (metis append.right_neutral hist_Nil local.rtrancl_refl map_Tm_Nt_eq_map_Tm_Nt rev.simps(1)
        self_append_conv2)
next
  case (rtrancl_into_rtrancl b)
  then obtain n where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<gamma> @ Nt A # map Tm w" 
    by (meson relpowp_Suc_I rtranclp_imp_relpowp)
  from derivern_Suc_singleton_imp_rm_chain[OF this] obtain \<rho> where 
    "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma> @ Nt A # map Tm w"
    using Nts_G'_is_union by blast
  then show ?thesis using assms that proof (induction \<rho> arbitrary: \<gamma> A w \<alpha> \<beta> v thesis)
    case Nil
    then have eqs: "\<gamma> = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S] \<and> A = S'" 
      using S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
    then show thesis using S'_derive_imp_S I.deriver_imp_IPDA_comp Nil
      by (metis append.right_neutral hist_Nil list.simps(8) rev.simps(1) self_append_conv2)
  next
    case (Cons i \<rho>)
    then obtain X \<alpha>' \<beta>' where X_defs:
      "i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']" 
      using rm_chain_imp_hd_prod_rightmost[OF Cons(2)]
      by (metis list.distinct(1) list.inject)
    with rm_chain_stepE Cons(2) obtain \<alpha>'' u v' where X_chain:
      "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha>'' @ Nt X # map Tm v'"
      "Prods G' \<turnstile> \<alpha>'' @ Nt X # map Tm v' \<Rightarrow>r \<alpha>'' @ \<alpha>' @ Nt A # \<beta>' @ map Tm v'"
      "Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm u" "u @ v' = w" "\<alpha>'' @ \<alpha>' = \<gamma>"
      by (smt (verit, best) append.assoc map_append rm_eq_imp_eq)
    then obtain \<rho>' where \<rho>'_def:
      "([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<rho>', u@v') 
          \<turnstile>I* ([I.final_state], [])"
      "hist (rev \<rho>') = \<alpha>''" 
      using Cons(1)[OF X_chain(1) rm_chain_imp_derivers[OF X_chain(1)], of "\<alpha>' @ [Nt A]" \<beta>']
      by (metis append.assoc append_Cons append_Nil derivers_imp_derives)
    from X_defs have X_in_prods: "(X, \<alpha>' @ Nt A # \<beta>') \<in> Prods G'"
      by (metis Cons.prems(1) rm_chain_imp_prod)
    let ?\<rho> = "[X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'] # \<rho>'"
    have hist_\<rho>: "hist (rev ?\<rho>) = \<gamma>" using X_chain(5) \<rho>'_def(2) by simp
    from Cons(4) have A_in_prods: "(A, \<alpha> @ \<beta>) \<in> Prods G'" 
      by (simp add: deriver_imp_in_Prods)
    with I.derives_imp_completes[OF Cons(5)] have 
      "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # ?\<rho>, v @ w) \<turnstile>I* ([A \<rightarrow> \<alpha>@\<beta> \<cdot> []] # ?\<rho>, w)"
      by (metis append.right_neutral)
    also have "... \<turnstile>I ([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<rho>', u@v')"
      using X_chain(4) A_in_prods X_in_prods by simp
    also have "... \<turnstile>I* ([I.final_state], [])" using \<rho>'_def by presburger
    finally show ?case using hist_\<rho> Cons(6) by presburger
  qed
qed 

text \<open>Towards step 3\<close>

lemma ipda_reaches_final_imp_rm_chain:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])"
  obtains "\<rho> = []" |
    \<sigma> X \<alpha>' \<beta>' \<gamma> where "\<rho> = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'] # \<sigma>" "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  using assms proof (induction "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w)" arbitrary: A \<alpha> \<beta> \<rho> w thesis
                      rule: converse_rtranclp_induct)
  case (step z)
  from I.step_imp_in_It this(1) have A_in_It: "[A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> It G'" 
    using I.step_imp_not_Nil by (smt (verit, ccfv_SIG) I.step_cases)
  from step(1) obtain B \<gamma> \<delta> \<tau> v where z\<tau>_def:
    "z = ([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v)" using prod.exhaust 
    by (metis I.step_imp_not_Nil item.exhaust list.exhaust)
  note step(3)[OF this] 
  then show thesis
  proof (cases, goal_cases Nil chain)
    case Nil
    with z\<tau>_def have z_B_init: "z = ([[B \<rightarrow> \<gamma> \<cdot> \<delta>]], v)" by blast
    with step(2) I.reaches_without_stack_imp_S' consider 
      "[B \<rightarrow> \<gamma> \<cdot> \<delta>] = init IPDA" |
      "[B \<rightarrow> \<gamma> \<cdot> \<delta>] = I.final_state" by blast
    then show thesis
    proof cases
      case 2
      note step(1)[unfolded z_B_init this] 
      with I.step_reaches_final_imp_S[of _ _ _ \<rho> "[]"] show ?thesis using step(5) G'_derive_S 
          derive_singleton_imp_singleton_chain 
        by (metis I.init_ipda append.right_neutral item.inject list.inject prod.inject)
    qed (use step(1) in cases, use step z_B_init in auto)
  next
    case (chain X \<alpha>' \<beta>' \<sigma> \<zeta>)
    from step(1)[unfolded z\<tau>_def] show ?thesis proof cases
      case (reduce Y \<eta> X' \<theta> \<iota> \<upsilon> x)
      hence BA_in_prods: "(B, \<theta> @ Nt A # \<delta>) \<in> Prods G'"
        using step(1) z\<tau>_def I.step_imp_in_Prods by force 
      from rm_chain_Cons_imp_prod_rightmost chain obtain \<zeta>' u where \<zeta>_rm: "\<zeta> = \<zeta>' @ Nt B # map Tm u"
        by meson
      note chain(2)[unfolded chain(1) this]
      from prod_imp_rm_chain_step[OF this BA_in_prods G'_reduced] step.prems(2) reduce chain(1)
      show thesis by fastforce       
    next
      case (expand Y \<eta> X' \<theta> \<iota> \<upsilon> x)
      show ?thesis
      proof (cases \<rho>)
        case (Cons i \<xi>)
        from Cons expand have "\<tau> = [A \<rightarrow> \<theta> \<cdot> Nt B # \<iota>] # i # \<xi>"  by auto
        from rm_chain_second_produces_hd[OF chain(2)[unfolded this]] obtain Z \<gamma>' \<delta>' where
          "\<rho> = [Z \<rightarrow> \<gamma>' \<cdot> Nt A # \<delta>'] # \<xi>" using Cons expand by auto
        moreover obtain \<zeta>' where "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<zeta>'"
          using expand Cons rm_chain_decomp chain(2) by fastforce
        ultimately show thesis using step.prems(2) by blast
      qed (rule step.prems(1))
    qed (use step(5) chain in fastforce)
  qed
qed simp

text \<open>Step 3: If the configuration \<open>([A \<rightarrow> \<alpha>.\<beta>]\<rho>, w)\<close> is accepted by the \<open>IPDA\<close>, the configuration
     \<open>([A \<rightarrow> \<alpha>.\<beta>], \<epsilon>)\<close> is reachable by \<open>char(G)\<close> with input \<open>hist(\<rho>)\<alpha>\<close>.\<close>

lemma ipda_imp_char:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])"
  shows "([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])"
using assms proof (induction \<rho> arbitrary: A \<alpha> \<beta> w)
  case Nil
  with I.reaches_without_stack_imp_S' consider (init) "[A \<rightarrow> \<alpha> \<cdot> \<beta>] = [S' \<rightarrow> [] \<cdot> [Nt S]]" | 
    (final) "[A \<rightarrow> \<alpha> \<cdot> \<beta>] = [S' \<rightarrow> [Nt S] \<cdot> []]" by auto
  then show ?case 
    by cases (fastforce simp: G'_def)+
next
  case (Cons i \<rho>)
  with ipda_reaches_final_imp_rm_chain obtain X \<alpha>' \<beta>' \<gamma> where chain:
    "i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']" "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* i # \<rho> \<Rightarrow>r* \<gamma>" by blast
  hence X_in_Prods: "(X, \<alpha>' @ Nt A # \<beta>') \<in> Prods G'" 
    by (simp add: rm_chain_imp_prod)
  from I.reaches_final_imp_completes[OF Cons(2)] obtain v where A_complete:
    "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<rho>, w) 
      \<turnstile>I* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<rho>, v)"
    "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<rho>, v) 
      \<turnstile>I* ([I.final_state], [])" by blast
  have A_in_Prods: "(A, \<alpha>@\<beta>) \<in> Prods G'"
    using I.steps_neq_in_It[OF A_complete(2)] in_Prods_iff_in_It by force
  have "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<rho>, v)
       \<turnstile>I ([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<rho>, v)"
    using chain A_in_Prods X_in_Prods by auto
  with I.step_not_expanding_imp_reaches[OF this] A_complete have 
    "... \<turnstile>I* ([I.final_state], [])" 
    by (metis (no_types, lifting) I.complete_S'_step_impossible I.step_not_expanding_unique
        converse_rtranclpE list.sel(1))
  note X_comp = Cons.IH[OF this]
  hence "([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ \<alpha>') \<turnstile>c* ([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], [])"
    using char_consumes_last_imp_butlast_reaches by fastforce
  hence "([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev (i # \<rho>)) @ \<alpha>) \<turnstile>c* ([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], \<alpha>)"
    using char_fa.steps_append[of _ "hist (rev (i # \<rho>))" "[]" _ \<alpha>] chain by simp
  also have "... \<turnstile>c ([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>], \<alpha>)" 
    using A_in_Prods X_in_Prods by force
  also from this have "... \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])" 
    using char_steps_consume char_step_imp_in_Prods 
    by (metis append.right_neutral item.case self_append_conv2)
  finally show ?case .
qed

corollary derivers_imp_char:
  assumes
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w"
  shows "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>' @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])"
proof -
  note rtranclp.rtrancl_into_rtrancl[OF assms]
  with reduced_derives_imp_substring_derives_Tms obtain v where
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v" 
    using G'_reduced G'_not_empty G'_def derivers_imp_derives by (metis Cfg.sel(2) append.assoc)
  from derivers_imp_ipda[OF assms this] ipda_imp_char show ?thesis by metis
qed

subsection \<open>Reliable Prefixes\<close>

text \<open>\<open>\<gamma>\<close> is a reliable prefix to \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> (or equivalently, \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> is valid for \<open>\<gamma>\<close>) 
      if there exists a rightmost derivation \<open>S' \<Rightarrow>r* \<gamma>'Aw \<Rightarrow>r \<gamma>'\<alpha>\<beta>w\<close> with \<open>\<gamma> = \<gamma>'\<alpha>\<close>:\<close>

inductive reliable_prefix :: "('n, 't) item \<Rightarrow> ('n, 't) syms \<Rightarrow> bool" where
  "\<lbrakk>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w;  
    Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<rbrakk> 
    \<Longrightarrow> reliable_prefix [A \<rightarrow> \<alpha> \<cdot> \<beta>] (\<gamma>' @ \<alpha>)"

inductive_cases reliable_prefixE [consumes 1]: "reliable_prefix [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<gamma>"

lemma reliable_prefixI [intro]:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma> @ \<beta> @ map Tm w" "\<gamma> = \<gamma>' @ \<alpha>"
  shows "reliable_prefix [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<gamma>"
  using assms reliable_prefix.intros by auto

lemma reliable_app [simp]:
  "reliable_prefix [A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] \<gamma>' \<Longrightarrow> reliable_prefix [A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] (\<gamma>' @ \<beta>)"
  by (elim reliable_prefixE) auto

lemma reliable_app2 [simp]:
  "reliable_prefix [A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] (\<gamma>' @ \<beta>) \<Longrightarrow> reliable_prefix [A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] \<gamma>'"
  by (elim reliable_prefixE) auto

lemma reliable_imp_in_It:
  assumes "reliable_prefix [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<gamma>" shows "[A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> It G'"
using assms proof (cases rule: reliable_prefixE)
  case (1 \<gamma>' w)
  from this(3) have "(A, \<alpha> @ \<beta>) \<in> Prods G'" 
    by (simp add: deriver_imp_in_Prods)
  then show ?thesis using in_Prods_imp_in_It by force
qed


text \<open>The words on which \<open>char(G)\<close> reaches \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> are exactly the reliable 
     prefixes for \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close>:\<close>

theorem char_eq_reliable_prefix:
  "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], []) = reliable_prefix [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<gamma>"
  using char_imp_derivers derivers_imp_char by (smt (verit, best) reliable_prefix.simps)

text \<open>\<open>char(G)\<close> accepts the set of reliable prefixes to complete items:\<close>

theorem char_lang_is_realiables_of_complete_items:
  "char_fa.language = {\<gamma>. \<exists>i \<in> completes (It G'). reliable_prefix i \<gamma>}"
proof -
  note char_fa.eps_subst_states_imp_language_eq_init_final_reachable[OF eps_char_fa_subst_states]
  thus ?thesis
    using char_eq_reliable_prefix final_char_fa 
    by (smt (verit, del_insts) Collect_cong completesE init_char_fa insertCI singletonD)
qed

lemma char_fa_init_valid_for_Nil [simp]:
  "reliable_prefix [S' \<rightarrow> [] \<cdot> [Nt S]] []"
  using char_eq_reliable_prefix by fast

lemma char_fa_init_valid_imp_Nil:
  assumes "reliable_prefix [S' \<rightarrow> [] \<cdot> [Nt S]] \<gamma>"
  shows "\<gamma> = []"
  using assms S'_derives_S'_imp_refl derivers_imp_derives 
  by cases blast

lemma S'_complete_reliable_imp_S:
  assumes "reliable_prefix [S' \<rightarrow> [Nt S] \<cdot> []] \<gamma>" 
  shows "\<gamma> = [Nt S]"
  using assms S'_derives_S'_imp_refl derivers_imp_derives 
  by cases blast

definition valids :: "('n, 't) syms \<Rightarrow> ('n, 't) item set" where
  "valids \<gamma> \<equiv> {i. reliable_prefix i \<gamma>}"

lemma validD:
  "i \<in> valids \<gamma> \<Longrightarrow> reliable_prefix i \<gamma>"
  unfolding valids_def by simp

lemma validI [intro]:
  "reliable_prefix i \<gamma> \<Longrightarrow> i \<in> valids \<gamma>"
  unfolding valids_def by blast

lemma char_fa_nextl_is_valids:
  "nfa.nextl char_fa (nfa.init char_fa) w = valids w"
proof -
  have "valids w = {i. ([S' \<rightarrow> [] \<cdot> [Nt S]], w) \<turnstile>c* (i, [])}"
    using char_eq_reliable_prefix unfolding valids_def by (metis item.exhaust)
  also have "... = nfa.nextl char_fa (nfa.init char_fa) w"
    using char_fa.eps_subst_states_imp_nextl_eq_reachable[OF eps_char_fa_subst_states]
    by auto
  finally show ?thesis by order
qed

lemma eps_reliable_preserved:
  assumes "(i, k) \<in> (nfa.eps char_fa)\<^sup>*"
    "reliable_prefix i \<gamma>"
  shows "reliable_prefix k \<gamma>"
  using assms proof (induction rule: converse_rtrancl_induct)
  case (step i j)
  then obtain A \<alpha> X \<beta> \<delta> where ij_eq: "i = [A \<rightarrow> \<alpha> \<cdot> Nt X # \<beta>]" "j = [X \<rightarrow> [] \<cdot> \<delta>]"
    by blast
  from step(4) show ?case unfolding ij_eq proof cases
    case (1 \<gamma>' w)
    hence "reliable_prefix j \<gamma>" using ij_eq 
      by (metis (no_types, lifting) char_eq_reliable_prefix char_fa.step_eps
          rtranclp.rtrancl_into_rtrancl step.hyps(1) step.prems)
    then show ?thesis using step by argo
  qed
qed satx

lemma derivern_Suc_imp_reliable:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm w"
  obtains A \<alpha>' \<beta> v where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha>' @ Nt A # map Tm v"
    "Prods G' \<turnstile> \<alpha>' @ Nt A # map Tm v \<Rightarrow>r \<alpha> @ \<beta> @ map Tm v"
    "Prods G' \<turnstile> \<alpha> @ \<beta> @ map Tm v \<Rightarrow>r* \<alpha> @ Nt X # map Tm w"
proof -
  from assms obtain A \<alpha>'' \<beta> \<rho> where 
    "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* [A \<rightarrow> \<alpha>'' \<cdot> Nt X # \<beta>] # \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm w"
    by (meson derivern_Suc_singleton_imp_rm_chain)
  then show thesis proof cases
    case (step \<alpha>' v u)
    hence derivers_A: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha>' @ Nt A # map Tm v" 
      using rm_chain_imp_derivers by blast
    from step(1) have "\<alpha> = \<alpha>' @ \<alpha>''" "w = u @ v"
      using rm_eq_imp_eq[of \<alpha> X w "\<alpha>' @ \<alpha>''" X "u@v"] by auto
    with that[OF derivers_A] step show ?thesis 
      by (metis append.assoc append_Cons append_Nil derivers_append_map_Tm derivers_prepend)
  qed
qed

lemma derivern_Suc_substring_reliable:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<alpha> @ \<beta> @ Nt X # map Tm w"
  obtains A \<alpha>' Y \<beta>' w' where "reliable_prefix [A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>'] \<alpha>"
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Y # \<beta>' @ map Tm w'"
    "Prods G' \<turnstile> Y # \<beta>' @ map Tm w' \<Rightarrow>r* \<beta> @ Nt X # map Tm w"
proof -
  from G'_derivern_Suc_imp_no_S'[OF assms[THEN derivern_imp_deriven]] have 
    "[Nt S'] \<noteq> \<alpha> @ \<beta> @ Nt X # map Tm w" 
      by (metis in_Nts_syms list.set_intros(1))
  moreover from assms obtain  \<rho> where 
   "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ \<beta> @ Nt X # map Tm w"
   using derivern_Suc_singleton_imp_rm_chain by (metis append.assoc)
  ultimately show thesis using that 
  proof (induction \<rho> arbitrary: thesis X \<alpha> \<beta> w)
    case Nil
    then show ?case using append_eq_Cons_conv by auto
  next
    case (Cons i \<rho>)
    note that = Cons.prems(3)
    from Cons(3) show ?case proof cases
      case (step \<alpha>' A v \<alpha>'' Y \<beta>' u)
      note i_step = this
      from this(2) have eqs [simp]: "\<alpha>' @ \<alpha>'' = \<alpha> @ \<beta> \<and> Y = X \<and> u @ v = w"
        using rm_eq_imp_eq[of "\<alpha> @ \<beta>" X w "\<alpha>' @ \<alpha>''" Y "u @ v"]  
        by (metis append_eq_appendI map_append)
      from step(3) show ?thesis proof cases
        case refl
        with eqs i_step have is_S: "\<alpha> @ \<beta> @ Nt Y # \<beta>' @ map Tm v = [Nt S] \<and> \<alpha> = []"
          using S'_derive_imp_S deriver_imp_derive append.assoc 
          by (smt (verit, best) Cons_eq_append_conv Nil_is_append_conv list.discI)
        moreover then have "\<beta> @ Nt X # map Tm w = [Nt S] \<and> w = []" 
          using i_step(5) eqs by (auto simp: append_eq_Cons_conv derivers_iff_derives)
        ultimately show ?thesis using refl that[of S' "[]" "Nt S" "[]" w] 
          using char_fa_init_valid_for_Nil eqs step(4) by force
      next
        case (step _ _ _ _ _ _ _ _)
        with rm_chain_S'_Cons_imp_neq have neq_S': "[Nt S'] \<noteq> \<alpha>' @ Nt A # map Tm v" by auto
        from eqs consider (\<alpha>_in_\<alpha>') \<gamma> where "\<alpha>' = \<alpha> @ \<gamma>" "\<beta> = \<gamma> @ \<alpha>''" | 
          (\<alpha>'_in_\<alpha>) \<gamma> where "\<alpha> = \<alpha>' @ \<gamma>" "\<alpha>'' = \<gamma> @ \<beta>" 
        by (metis append_eq_append_conv2[of \<alpha>' \<alpha>'' \<alpha> \<beta>])
        then show ?thesis proof cases
          case \<alpha>_in_\<alpha>'
          hence "Prods G' \<turnstile> \<gamma> @ Nt A # map Tm v \<Rightarrow>r \<beta> @ Nt X # \<beta>' @ map Tm v"
            using i_step(4) deriver_prefix_indep
              [of _ \<alpha> "\<gamma> @ Nt A # map Tm v" "\<gamma> @ \<alpha>'' @ Nt Y # \<beta>' @ map Tm v" _ _ _ "[]"] 
            by auto
          also have "Prods G' \<turnstile> ... \<Rightarrow>r* \<beta> @ Nt X # map Tm w"
            using i_step(5)[THEN derivers_append_map_Tm, THEN derivers_prepend, of "\<beta> @ [Nt X]" v]
              append.assoc eqs by (metis append_Cons append_Nil map_append)
          finally have A_derivers: "Prods G' \<turnstile> \<gamma> @ Nt A # map Tm v \<Rightarrow>r* \<beta> @ Nt X # map Tm w" .
          from \<alpha>_in_\<alpha>' neq_S' have "[Nt S'] \<noteq> \<alpha> @ \<gamma> @ Nt A # map Tm v" by simp
          from Cons.IH[OF this] i_step(3)[unfolded \<alpha>_in_\<alpha>'] show ?thesis 
            using Cons.prems(1) append.assoc that A_derivers 
            by (metis (no_types, lifting) rtranclp_trans)
        next
          case \<alpha>'_in_\<alpha>
          with i_step(4) have A_deriver: "Prods G' \<turnstile> \<alpha>' @ Nt A # map Tm v \<Rightarrow>r \<alpha> @ (\<beta> @ Nt X # \<beta>') @ map Tm v"
            by simp
          with rm_chain_imp_derivers[OF i_step(3)] have 1: "reliable_prefix [A \<rightarrow> \<gamma> \<cdot> \<beta> @ Nt X # \<beta>'] \<alpha>"
            using \<alpha>'_in_\<alpha>(1) by standard
          have 2: "Prods G' \<turnstile> \<beta> @ Nt X # \<beta>' @ map Tm v \<Rightarrow>r* \<beta> @ Nt X # map Tm w"
            using i_step(5)[THEN derivers_append_map_Tm, THEN derivers_prepend, of "\<beta> @ [Nt X]" v]
              eqs by (metis append.assoc append_Cons append_Nil map_append)  
          show ?thesis  proof -
            obtain X' \<xi> where X'_def: "\<beta> @ Nt X # \<beta>' = X' # \<xi>" 
              by (metis Nil_is_append_conv neq_Nil_conv)
            with 2 have "Prods G' \<turnstile> X' # \<xi> @ map Tm v \<Rightarrow>r* \<beta> @ Nt X # map Tm w"   
              by (metis append.assoc append_Cons)
            note 1[unfolded X'_def] rm_chain_imp_derivers[OF i_step(3), THEN rtranclp.rtrancl_into_rtrancl, 
              OF A_deriver, unfolded X'_def] this
            with that show thesis by force
          qed
        qed
      qed
    qed
  qed
qed


lemma derivers_substring_reliable:
assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ \<beta> @ Nt X # map Tm w"
  obtains A \<alpha>' \<gamma> Y \<beta>' w' where "reliable_prefix [A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>'] \<alpha>" 
proof -
  from assms obtain n where derivern: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(n) \<alpha> @ \<beta> @ Nt X # map Tm w"
    using rtranclp_imp_relpowp by fast
  then show thesis proof (cases n)
  case 0
  have "reliable_prefix ([S' \<rightarrow> [] \<cdot> [Nt S]]) []" 
    using char_eq_reliable_prefix by blast
  then show ?thesis using 0 assms 
    by (metis (mono_tags, lifting) Nil_is_append_conv append_eq_Cons_conv derivern 
        list.distinct(1) relpowp_0_E that)
  next
    case (Suc m)
    with derivern_Suc_substring_reliable show thesis using derivern that by meson
  qed
qed

lemma derivers_imp_reliable [case_names rm_valid nc_valid]:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm y"
    "Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm y \<Rightarrow>r \<gamma> @ \<delta> @ map Tm y"
    "\<gamma> @ \<delta> @ map Tm y = \<alpha> @ \<beta> @ map Tm (y'@y)"
  obtains \<delta>\<^sub>1 \<delta>\<^sub>2 where "reliable_prefix [Y \<rightarrow> \<delta>\<^sub>1 \<cdot> \<delta>\<^sub>2] (\<alpha> @ \<beta>)" "\<gamma> @ \<delta>\<^sub>1 = \<alpha> @ \<beta>" "\<delta>\<^sub>1 @ \<delta>\<^sub>2 = \<delta>" | 
    A \<zeta> B \<eta> where "reliable_prefix [A \<rightarrow> \<zeta> \<cdot> B # \<eta>] (\<alpha> @ \<beta>)" 
proof -
  from assms(3) have "\<gamma> @ \<delta> = \<alpha> @ \<beta> @ map Tm y'" by simp
  thus thesis 
  proof (cases rule: app_eq_rm_cases)
    case (1 u v)
    then show ?thesis using assms derivers_substring_reliable that(2) 
      by (metis append_assoc)
  next
    case (2 \<delta>')
    from assms(1) have "reliable_prefix [Y \<rightarrow> \<delta>' \<cdot> map Tm y'] (\<alpha> @ \<beta>)"
      using "2"(1,2) assms(2) reliable_prefix.intros by fastforce
    then show ?thesis using that(1) 2 by blast
  qed
qed



lemma in_states_imp_valid:
  assumes "[X \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> nfa.states char_fa"
  obtains \<gamma> where "reliable_prefix [X \<rightarrow> \<alpha> \<cdot> \<beta>] \<gamma>"
proof -
  from assms have prod: "(X, \<alpha>@\<beta>) \<in> Prods G'"
    using in_It_imp_in_Prods by fastforce
  then obtain \<gamma> w where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt X # map Tm w"
    using reduced_in_Prods_imp_rsentential_reachable[OF G'_reduced G'_not_empty]
    by (metis Cfg.sel(2) G'_def)
  hence "reliable_prefix [X \<rightarrow> \<alpha> \<cdot> \<beta>] (\<gamma> @ \<alpha>)"
    using prod deriver.intros by fastforce
  thus thesis using that by blast
qed


subsection \<open>The Canonical LR(0) Automaton\<close>

definition LR\<^sub>0 :: "(('n, 't) sym, ('n, 't) item set) dfa" where
  "LR\<^sub>0 \<equiv> dfa.Accessible_dfa char_fa.Power_dfa"

sublocale dfa_LR0: dfa LR\<^sub>0
  unfolding LR\<^sub>0_def using dfa.dfa_Accessible char_fa.dfa_Power by blast

lemma states_dfa_LR0 [simp]:
  "dfa.states LR\<^sub>0 = dfa.accessible char_fa.Power_dfa"
  unfolding LR\<^sub>0_def by (simp add: char_fa.dfa_Power dfa.states_Accessible_dfa)

lemma init_dfa_LR0 [simp]:
  "dfa.init LR\<^sub>0 = {q. ([S' \<rightarrow> [] \<cdot> [Nt S]], q) \<in> (nfa.eps char_fa)\<^sup>*}"
proof -
  have "dfa.init LR\<^sub>0 = char_fa.epsclo {[S' \<rightarrow> [] \<cdot> [Nt S]]}"
    by (simp add: LR\<^sub>0_def char_fa.dfa_Power dfa.init_Accessible_dfa)
  also have "... = nfa.states char_fa \<inter> {q. ([S' \<rightarrow> [] \<cdot> [Nt S]], q) \<in> (nfa.eps char_fa)\<^sup>*}"
    unfolding char_fa.epsclo_def by fast
  also have "... = {q. ([S' \<rightarrow> [] \<cdot> [Nt S]], q) \<in> (nfa.eps char_fa)\<^sup>*}"
    by (standard, simp, standard, standard)
    (use in_eps_char_star_imp_in_It states_char_fa char_fa.init init_char_fa 
      in blast)+
  finally show ?thesis .
qed
    

lemma dfa_LR0_states_subset [dest]:
  "q \<in> dfa.states LR\<^sub>0 \<Longrightarrow> q \<in> dfa.states char_fa.Power_dfa"
  using char_fa.dfa_Power dfa.accessible_imp_states by fastforce 

lemma dfa_LR0_nxt [simp]:
  "dfa.nxt LR\<^sub>0 = dfa.nxt char_fa.Power_dfa"
  unfolding LR\<^sub>0_def using char_fa.dfa_Power dfa.nxt_Accessible_dfa by metis

lemma dfa_LR0_nextl [simp]:
  "dfa.nextl LR\<^sub>0 (dfa.init LR\<^sub>0) = dfa.nextl char_fa.Power_dfa (dfa.init char_fa.Power_dfa)"
  unfolding LR\<^sub>0_def using char_fa.dfa_Power dfa.init_Accessible
    dfa.init_Accessible_dfa dfa.nextl_Accessible_dfa by fastforce

lemma in_states_dfa_LR0_imp_eps_star_in_state:
  assumes "i \<in> q"
    "q \<in> dfa.states LR\<^sub>0"
    "(i,j) \<in> (nfa.eps char_fa)\<^sup>*"
  shows "j \<in> q"
proof -
  from assms(2) have "q \<in> dfa.states char_fa.Power_dfa" 
    by blast 
  then obtain Q where "Q \<in> Pow (It G')" "q = nfa.states char_fa 
    \<inter> (\<Union>p\<in>Q. {q'. (p, q') \<in> (nfa.eps char_fa)\<^sup>*})" unfolding char_fa.states_Power_dfa 
    char_fa.epsclo_def by auto
  moreover then obtain k where "k \<in> Q" "(k, i) \<in> (nfa.eps char_fa)\<^sup>*" using assms by blast
  moreover with assms have "(k,j) \<in> (nfa.eps char_fa)\<^sup>*" by auto
  ultimately show ?thesis using in_eps_char_star_imp_in_It unfolding states_char_fa by blast
qed

lemma in_states_imp_epsclo_eq:
  assumes "q \<in> dfa.states LR\<^sub>0"
  shows "char_fa.epsclo q = q"
  using assms char_fa.epsclo_idem by fastforce 

lemma in_states_dfa_LR0_imp_eps_in_state:
  assumes "i \<in> q"
    "q \<in> dfa.states LR\<^sub>0"
    "(i,j) \<in> (nfa.eps char_fa)"
  shows "j \<in> q"
  using assms in_states_dfa_LR0_imp_eps_star_in_state by blast

lemma in_state_imp_in_It:
  assumes "Q \<in> dfa.states LR\<^sub>0" "i \<in> Q"
  shows "i \<in> It G'"
  using assms states_dfa_LR0 states_char_fa char_fa.epsclo_subset by fastforce

lemma finite_dfa_LR0_nempty_syms:
  "finite {a. dfa.nxt LR\<^sub>0 q a \<noteq> {}}"
proof -
  have "{a. dfa.nxt LR\<^sub>0 q a \<noteq> {}} = {a. dfa.nxt LR\<^sub>0 (q \<inter> It G') a \<noteq> {}}"
    by simp
  moreover have "... \<subseteq> (\<lambda>i. case i of [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<Rightarrow> Y) ` char_fa.epsclo (q \<inter> It G')"
    (is "?A \<subseteq> ?f ` ?Q'")
  proof 
    fix a
    assume "a \<in> ?A"
    then obtain p where "p \<in> ?Q'" "nfa.nxt char_fa p a \<noteq> {}"
      by fastforce
    moreover with nxt_char_fa_nempty_imp_hd obtain X \<alpha> \<beta> where "p = [X \<rightarrow> \<alpha> \<cdot> a # \<beta>]"
      using item.exhaust by metis
    ultimately show "a \<in> ?f ` ?Q'" by force
  qed
  ultimately show ?thesis using finite_surj char_fa.finite_epsclo by metis
qed

corollary finite_dfa_LR0_nempty_Tms:
  "finite {a. dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}}"
proof -
  have "{a. dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}} \<subseteq> destTm ` {a. dfa.nxt LR\<^sub>0 q a \<noteq> {}}"
    by force
  with finite_dfa_LR0_nempty_syms finite_surj show ?thesis by blast
qed

lemma nextl_dfa_LR0_is_valids:
  "dfa.nextl LR\<^sub>0 (dfa.init LR\<^sub>0) \<gamma> = valids \<gamma>"
  using LR\<^sub>0_def char_fa.Power_nextl_eq_nfa_nextl char_fa_nextl_is_valids 
   dfa_LR0_nextl by presburger

lemma state_imp_valids:
  "p \<in> dfa.states LR\<^sub>0 \<Longrightarrow> \<exists>\<gamma>. p = valids \<gamma>"
  using nextl_dfa_LR0_is_valids dfa.path_to_left_lang[OF char_fa.dfa_Power]
    dfa.nextl_path_to[OF char_fa.dfa_Power] by (metis dfa_LR0_nextl states_dfa_LR0)

lemma dfa_LR0_nxt_is_epsclo_of_shift:
  assumes "Q \<in> dfa.states LR\<^sub>0"
  shows "dfa.nxt LR\<^sub>0 Q Y = char_fa.epsclo {[X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> Q}"
proof -
  from dfa_LR0_states_subset[OF assms(1)] char_fa.epsclo_idem
  have "dfa.nxt LR\<^sub>0 Q Y = (\<Union>i \<in> Q. char_fa.epsclo (nfa.nxt char_fa i Y))"
    unfolding dfa_LR0_nxt char_fa.nxt_Power_dfa char_fa.states_Power_dfa by blast
  also have "... = char_fa.epsclo (\<Union>i \<in> Q. (nfa.nxt char_fa i Y))"
    by auto
  finally show ?thesis using char_fa_nxts_is_shifts 
    by (metis (lifting) assms in_state_imp_in_It subsetI)
qed


lemma nxt_dfa_LR0_shift_is_valids_app:
  assumes "valids \<gamma> \<in> dfa.states LR\<^sub>0"
  shows "dfa.nxt LR\<^sub>0 (valids \<gamma>) X = valids (\<gamma> @ [X])"
proof (simp only: dfa_LR0_nxt_is_epsclo_of_shift[OF assms], standard)
  show " char_fa.epsclo {[Xa \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>] |Xa \<alpha> \<beta>. [Xa \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> valids \<gamma>} 
    \<subseteq> valids (\<gamma> @ [X])" (is "?\<delta> \<subseteq> _")
  proof
    fix i
    assume "i \<in> ?\<delta>" 
    then obtain Y \<alpha> \<beta> where "[Y \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> valids \<gamma>" 
      "([Y \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>], i) \<in> (nfa.eps char_fa)\<^sup>*"
      unfolding char_fa.epsclo_def using assms by blast
    moreover from validD[OF this(1)] have "reliable_prefix [Y \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>] (\<gamma> @ [X])"
      by cases auto
    ultimately show "i \<in> valids (\<gamma> @ [X])"
      by (intro validI) (use eps_reliable_preserved in blast)
  qed
  show "valids (\<gamma> @ [X]) \<subseteq> ?\<delta>"
  proof 
    fix i
    assume i_valid: "i \<in> valids (\<gamma> @ [X])"
    consider (noncomp) A \<alpha> \<beta> where "i = [A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]" |(complete) A \<beta> where "i = [A \<rightarrow> [] \<cdot> \<beta>]"
    proof -
      obtain A \<alpha> \<beta> where i_A: "i = [A \<rightarrow> \<alpha> \<cdot> \<beta>]" using item.exhaust by blast
      show thesis proof (cases \<alpha> rule: rev_cases)
        case (snoc \<alpha>' Y)
        then show ?thesis using i_A i_valid validD that(1) 
          by (metis append.assoc append1_eq_conv reliable_prefixE)
      qed (use that i_A in blast)
    qed
    then show "i \<in> ?\<delta>" proof cases
      case noncomp
      with i_valid[THEN validD] have "reliable_prefix [A \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<gamma>"
        by (fastforce elim: reliable_prefixE)
      then show ?thesis using noncomp char_fa.in_states_imp_in_epsclo reliable_imp_in_It
        by (metis (mono_tags, lifting) \<open>reliable_prefix i (\<gamma> @ [X])\<close> 
            mem_Collect_eq states_char_fa validI)
    next
      case complete
      from i_valid[THEN validD] obtain Y \<delta> \<zeta> where 
        "([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c* ([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], [])"
        "([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], []) \<turnstile>c* (i, [])"
        unfolding complete using char_eq_reliable_prefix char_reaches_left_empty_imp_expanded_last
        by blast
      moreover then have "reliable_prefix [Y \<rightarrow> \<delta> \<cdot> X # \<zeta>] \<gamma>"   
        by (metis append_Cons append_Nil char_eq_reliable_prefix reliable_app2)
      moreover from calculation(2) have "([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], i) \<in> (nfa.eps char_fa)\<^sup>*"
        using char_steps_unchanged_imp_in_eps_star by blast
      ultimately show ?thesis unfolding char_fa.epsclo_def 
        using \<open>reliable_prefix i (\<gamma> @ [X])\<close> complete reliable_imp_in_It by fastforce
    qed
  qed
qed

lemma nxt_dfa_LR0_nempty_imp_ex_shift:
  assumes "Q \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 Q Y \<noteq> {}"
  obtains X \<alpha> \<beta> where "[X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> Q" "[X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>] \<in> dfa.nxt LR\<^sub>0 Q Y"
proof -
  from dfa_LR0_nxt_is_epsclo_of_shift[OF assms(1)] assms(2) obtain X \<alpha> \<beta> where
    "[X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> Q" by fastforce
  moreover from this assms in_state_imp_in_It have "[X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> nfa.states char_fa" 
    by auto
  moreover from this have "[X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>] \<in> nfa.states char_fa"  
    using char_fa.nxt in_It_imp_in_Prods by fastforce
  moreover have "([X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>], [X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*" by blast
  ultimately show thesis using that dfa_LR0_nxt_is_epsclo_of_shift[OF assms(1)] 
    unfolding char_fa.epsclo_def by blast
qed

lemma in_nxt_dfa_LR0_imp_shift_or_left_empty:
  assumes "Q \<in> dfa.states LR\<^sub>0" "i \<in> dfa.nxt LR\<^sub>0 Q X"
  obtains A \<alpha> where "i = [A \<rightarrow> [] \<cdot> \<alpha>]" |
    A \<alpha> \<beta> where "i = [A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]"
proof -
  note nxt_shifts = dfa_LR0_nxt_is_epsclo_of_shift[OF assms(1), of X]
  from assms obtain A \<alpha> \<beta> where eps: "[A \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> Q" 
    "([A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>], i) \<in> (nfa.eps char_fa)\<^sup>*"
    unfolding nxt_shifts char_fa.epsclo_def by fast
  from eps(2) show thesis by cases (use that in blast)+
qed
    
lemma dfa_LR0_nxt_final_impossible:
  assumes "p \<in> dfa.states LR\<^sub>0"
  shows "dfa.nxt LR\<^sub>0 p X = {[S' \<rightarrow> [] \<cdot> []]} \<Longrightarrow> False"
proof (simp only: dfa_LR0_nxt_is_epsclo_of_shift[OF assms])
  let ?q = "char_fa.epsclo {[Xa \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>] |Xa \<alpha> \<beta>. [Xa \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> p}"
  assume eq: "?q = {[S' \<rightarrow> [] \<cdot> []]}"
  show False
  proof (cases "?q = {}")
    case False
    then obtain Y \<alpha> \<beta> where "[Y \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>] \<in> ?q" using char_fa.in_states_imp_in_epsclo
        assms in_state_imp_in_It
      by (smt (verit, del_insts) S'_derive_imp_S S'_derives_S'_imp_refl append_self_conv2
          char_fa.epsclo_subset deriver_imp_derive derivers_imp_derives eq in_states_imp_valid
          insert_subset item.inject list.distinct(1) reliable_prefix.simps)
    then show ?thesis using eq by auto
  qed (use eq in simp)
qed

lemma inj_nxt_dfa_LR0_if_nempty:
  assumes "q \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 q X = dfa.nxt LR\<^sub>0 q Y"
    "dfa.nxt LR\<^sub>0 q X \<noteq> {}"
  shows "X = Y"
proof -
  obtain A \<alpha> \<beta> where "[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>] \<in> dfa.nxt LR\<^sub>0 q X" "[A \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> q"
    using nxt_dfa_LR0_nempty_imp_ex_shift assms by metis
  moreover from this have "[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>] \<in> dfa.nxt LR\<^sub>0 q Y"
    using assms by argo
  ultimately show ?thesis using in_nxt_dfa_LR0_imp_shift_or_left_empty
      dfa_LR0.nxt assms by blast
qed

lemma dfa_LR0_init_reliable_Nil:
  assumes "dfa.init LR\<^sub>0 = valids \<gamma>"
  shows "\<gamma> = []"
proof -
  from assms have "reliable_prefix [S' \<rightarrow> [] \<cdot> [Nt S]] \<gamma>"   
    by (metis char_fa_init_valid_for_Nil dfa_LR0.nextl.simps(1) mem_Collect_eq
        nextl_dfa_LR0_is_valids valids_def)
  with char_fa_init_valid_imp_Nil show ?thesis by simp
qed

end
end
