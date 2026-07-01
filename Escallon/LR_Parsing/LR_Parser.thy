theory LR_Parser 
  imports
    Generalized_Pushdown_Automata
    Item_Pushdown_Automata
    Rightmost_Chain
    Wlog.Wlog
begin

context Extended_Cfg
begin

section \<open>The Characteristic Finite Automaton to a Context-Free Grammar\<close>

definition char_fa :: "(('n, 't) sym, ('n, 't) item) nfa" where
  "char_fa \<equiv> let 
      P = Prods G';
      \<Delta> = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>]  \<Rightarrow> if a = Y \<and> (X, \<alpha>@Y#\<beta>) \<in> P then {[X \<rightarrow> \<alpha>@[Y] \<cdot> \<beta>]} else {}| 
         _ \<Rightarrow> {}); 
      \<E> = {([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @Nt Y#\<beta>) \<in> P \<and> (Y, \<gamma>) \<in> P} in
    \<lparr>nfa.states = It G', nfa.init = {[S' \<rightarrow> [] \<cdot> [Nt S]]}, nfa.final = completes (It G'), 
      nfa.nxt = \<Delta>, nfa.eps = \<E>\<rparr>"

subsection \<open>Basic Properties\<close>

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

subsection \<open>Properties of \<epsilon>-transitions and the \<epsilon>-closure\<close>

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



end
 

section \<open>NFA Configurations and Steps\<close>

context nfa 
begin

type_synonym ('b,'c) config = "'b \<times> 'c list"

inductive step :: "('s,'a) config \<Rightarrow> ('s,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
step_nxt[intro]:  "q \<in> nfa.nxt M p a \<Longrightarrow> (p,a#u) \<turnstile> (q,u)" |
step_eps[intro]:  "(p,q) \<in> nfa.eps M \<Longrightarrow> (p,w) \<turnstile> (q,w)"

inductive_cases step_nxtE[elim]: "(q,a#u) \<turnstile> (r,u)"
inductive_cases step_epsE[elim]: "(q,w) \<turnstile> (r,w)"

lemma step_equal_or_Cons:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_Cons[OF assms] by fastforce

abbreviation stepn  (\<open>_ \<turnstile>'(_') _\<close> 55) where
  "c0 \<turnstile>(n) c1 \<equiv> (step ^^ n) c0 c1"

abbreviation steps (infix \<open>\<turnstile>*\<close> 55) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by (induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct)
  (use step_len_dec surj_pair le_trans in fastforce)+

lemma nxt_indep:
  assumes "(p, a # u) \<turnstile> (q, u)"
  shows "(p, a # v) \<turnstile> (q, v)"
  using assms by auto

lemma eps_indep:
  assumes "(p, u) \<turnstile> (q, u)"
  shows "(p, v) \<turnstile> (q, v)"
  using assms by blast

lemma step_imp_nempty_or_eq:
  assumes "(p, u) \<turnstile> (q, v)"
  shows "u \<noteq> [] \<or> u = v"
  using assms by cases auto

lemma stepn_append:
  assumes "(p, u@v) \<turnstile>(n) (q, v)"
  shows "(p, u@w) \<turnstile>(n) (q, w)"
  using assms proof (induction n arbitrary: p u q)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain r x where n_steps: "(p, u@v) \<turnstile> (r, x)" "(r, x) \<turnstile>(n) (q, v)" 
    by (metis eq_fst_iff relpowp_Suc_D2)
  from this(1) show ?case 
  proof cases
    case (step_nxt a)
    then obtain y where u_decomp: "u = a # y" "x = y @ v" using n_steps 
      by (metis append_eq_Cons_conv impossible_Cons relpowp_imp_rtranclp steps_len_dec)
    hence "(p, u @ w) \<turnstile> (r, y @ w)" by (auto simp: step_nxt(2))
    also note Suc.IH[OF n_steps(2)[unfolded u_decomp(2)]]
    finally show ?thesis .
  next
    case step_eps
    with Suc.IH n_steps(2) have "(r, u @ w) \<turnstile>(n) (q, w)" by blast
    then show ?thesis using eps_indep[OF n_steps(1)[unfolded step_eps(1)], of "u @ w"] 
      by (meson relpowp_Suc_I2)
  qed
qed

lemma steps_append:
  "(p, u @ v) \<turnstile>* (q, v) \<Longrightarrow> (p, u @ w) \<turnstile>* (q, w)"
  using stepn_append[THEN relpowp_imp_rtranclp] rtranclp_imp_relpowp by metis

lemma in_epsclo_imp_reachable:
  assumes "q \<in> epsclo Q"
  obtains p where "p \<in> Q" "(p, w) \<turnstile>* (q, w)"
proof -
  from assms obtain p where "p \<in> Q" "(p, q) \<in> (nfa.eps M)\<^sup>*"
    unfolding epsclo_def by blast
  from this(2) show thesis
    using that by (induction arbitrary: thesis) 
      (use \<open>p \<in> Q\<close> in simp, metis step_eps rtranclp.simps)
qed 

lemma in_nextl_imp_reaches:
  assumes "q \<in> nextl Q w"
  obtains p where "p \<in> Q" "(p, w) \<turnstile>* (q, [])"
  using assms proof (induction w arbitrary: Q thesis)
  case Nil
  hence "q \<in> epsclo Q" by auto
  then show ?case using Nil(1) in_epsclo_imp_reachable by blast
next
  case (Cons a w) 
  then obtain p where p_defs: "p \<in> (\<Union>q \<in> epsclo Q. nfa.nxt M q a)" "(p, w) \<turnstile>* (q, [])"
    using nextl.simps(2) by metis
  then obtain r where r_defs: "r \<in> epsclo Q" "p \<in> nfa.nxt M r a" by blast
  with in_epsclo_imp_reachable obtain s where "s \<in> Q" "(s, a#w) \<turnstile>* (r, a#w)" by blast
  note this(2)
  also from r_defs have "(r, a#w) \<turnstile> (p, w)" by blast
  also note p_defs(2)
  finally show ?case using \<open>s \<in> Q\<close> Cons by fast
qed

lemma reachable_imp_in_nextl:
  assumes "p \<in> nfa.states M"
    "nfa.eps M \<subseteq> nfa.states M \<times> nfa.states M"
    "(p, w) \<turnstile>* (q, [])"
  shows "q \<in> nextl {p} w"
  using assms(3,1) proof (induction rule: converse_rtranclp_induct2)
  case refl
  then show ?case using epsclo_def by simp
next
  case (step p u r v)
  from step(1) show ?case
  proof cases
    case (step_nxt a)
    with nfa.nxt[OF nfa_axioms step(4)] step have q_in_nextl_r: "q \<in> nextl {r} v" 
      by blast                                            
    have "nextl {p} u = nextl (\<Union>q\<in>epsclo {p}. nfa.nxt M q a) v"    
      using step_nxt(1) nextl.simps(2) by blast
    with step_nxt have "nextl {r} v \<subseteq> nextl {p} u" 
      by (metis (mono_tags, lifting) Int_insert_left_if1 UN_I empty_subsetI insert_subset nextl_mono
          nfa.epsclo_increasing nfa_axioms step.prems)
    then show ?thesis using q_in_nextl_r by blast 
  next
    case step_eps
    hence r_subst_p: "epsclo {r} \<subseteq> epsclo {p}"
      unfolding epsclo_def by auto
    from step_eps step(3) assms have q_in_nextl_r: "q \<in> nextl {r} u" by blast
    also have "... = nextl (epsclo {r}) u" by simp
    also from r_subst_p have "... \<subseteq> nextl (epsclo {p}) u" 
      using nextl_mono by presburger
    also have "... = nextl {p} u" by simp
    finally show ?thesis .
  qed
qed

lemma eps_subst_states_imp_nextl_eq_reachable:
  assumes "nfa.eps M \<subseteq> nfa.states M \<times> nfa.states M"
  shows "i \<in> nextl (nfa.init M) w = (\<exists>q \<in> nfa.init M. (q, w) \<turnstile>* (i, []))"
proof
  show "i \<in> nextl (nfa.init M) w \<Longrightarrow> \<exists>q\<in>nfa.init M. (q, w) \<turnstile>* (i, [])"
    using in_nextl_imp_reaches by metis
next
  show "\<exists>q\<in>nfa.init M. (q, w) \<turnstile>* (i, []) \<Longrightarrow> i \<in> nextl (nfa.init M) w"
    using reachable_imp_in_nextl[OF _ assms] 
    by (metis Set.set_insert empty_subsetI insert_subset nextl_mono nfa.init nfa_axioms)
qed


lemma eps_subst_states_imp_language_eq_init_final_reachable:
  assumes "nfa.eps M \<subseteq> nfa.states M \<times> nfa.states M"
  shows "language = {w. \<exists>q\<^sub>0 \<in> nfa.init M. \<exists>f \<in> nfa.final M. (q\<^sub>0, w) \<turnstile>* (f, [])}"
  (is "_ = ?r")
  using eps_subst_states_imp_nextl_eq_reachable[OF assms] unfolding language_def
  by blast


end

section \<open>Properties of \<open>char(G)\<close> computations\<close>

context Extended_Cfg
begin

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

section \<open>Equivalences between \<open>char(G)\<close>, \<open>IPDA\<close>, and rightmost derivations\<close>

interpretation I: ipda G IPDA 
  by standard simp

corollary ipda_IPDA: 
  "ipda G IPDA"
  by (rule I.ipda_axioms)

type_synonym ('q,'s) ipda_config = "('q,'s) item list \<times> 's list"

abbreviation IPDA_step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>I\<close> 55) where
  "(\<turnstile>I) \<equiv> (ipda.step IPDA)"

abbreviation IPDA_steps :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>I*\<close> 55) where
  "(\<turnstile>I*) \<equiv> (ipda.steps IPDA)"

abbreviation IPDA_stepn :: "('n,'t) item list \<times> 't list \<Rightarrow> nat \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" ( \<open>_ \<turnstile>I'(_') _\<close> 55) where
  "c0 \<turnstile>I(n) c1 \<equiv> (ipda.stepn IPDA) c0 n c1"


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

section \<open>Reliable Prefixes\<close>

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


section \<open>The Canonical LR(0) Automaton\<close>

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

section \<open>The Canonical LR(0) Parser\<close>

definition P\<^sub>0 :: "(('n, 't) item set, 't) gpda" where
  "P\<^sub>0 \<equiv> let 
  \<Delta>\<^sub>G = dfa.nxt LR\<^sub>0;
  q\<^sub>0 = dfa.init LR\<^sub>0;
  Q = dfa.states LR\<^sub>0;
  f = {[S' \<rightarrow> [] \<cdot> []]};
  \<Delta>\<^sub>0 = {([q], a, \<Delta>\<^sub>G q (Tm a) # [q])|q a. q \<in> dfa.states LR\<^sub>0 \<and> \<Delta>\<^sub>G q (Tm a) \<noteq> {}};
  \<E> = {let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, \<Delta>\<^sub>G q (Nt X) # [q])| 
       q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> Q \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q\<^sub>n \<and> length \<alpha> = length qs \<and> X \<noteq> S'} \<union>
      {([q, q\<^sub>0], [f])|q. q \<in> Q \<and> [S' \<rightarrow> [Nt S] \<cdot> []] \<in> q}
 in \<lparr>gpda.states = Q \<union> {f}, init = q\<^sub>0, final = {f}, nxt = \<Delta>\<^sub>0, eps = \<E>\<rparr>"

lemma states_P0: 
  "gpda.states P\<^sub>0 = dfa.states LR\<^sub>0 \<union> {{[S' \<rightarrow> [] \<cdot> []]}}"
  unfolding P\<^sub>0_def by (meson gpda.select_convs(1))

lemma init_P0: 
  "gpda.init P\<^sub>0 = dfa.init LR\<^sub>0"
  unfolding P\<^sub>0_def by (meson gpda.select_convs(2))

lemma init_P0_is_valids_empty:
  "gpda.init P\<^sub>0 = {i. reliable_prefix i []}"
  by (metis dfa_LR0.nextl.simps(1) init_P0 nextl_dfa_LR0_is_valids valids_def)


abbreviation "P0_final \<equiv> {[S' \<rightarrow> [] \<cdot> []]}"

lemma final_P0 [simp]:
  "gpda.final P\<^sub>0 = {P0_final}"
  unfolding P\<^sub>0_def by (meson gpda.select_convs(3))

lemma init_P0_contains_S'S [simp]:
  "[S' \<rightarrow> [] \<cdot> [Nt S]] \<in> gpda.init P\<^sub>0"
  unfolding init_P0 init_dfa_LR0 
  using char_fa.epsclo_increasing char_fa.init by auto

lemma P0_init_not_final [simp]:
  "gpda.init P\<^sub>0 \<notin> gpda.final P\<^sub>0"
  unfolding final_P0 init_dfa_LR0 using init_P0_contains_S'S by fast


lemma P0_final_item_notin_It [simp]:
  "[S' \<rightarrow> [] \<cdot> []] \<notin> It G'"
  using Extended_Cfg.S'_Prod_notin_G(1) Extended_Cfg_axioms G'_def in_It_imp_in_Prods
  by fastforce

lemma dfa_LR0_nxt_final_impossible_P0:
  assumes "p \<in> gpda.states P\<^sub>0"
  shows "dfa.nxt LR\<^sub>0 p X = {[S' \<rightarrow> [] \<cdot> []]} \<Longrightarrow> False"
proof -
  assume eq: "dfa.nxt LR\<^sub>0 p X = {[S' \<rightarrow> [] \<cdot> []]}"
  from assms consider "p \<in> dfa.states LR\<^sub>0" | "p = {[S' \<rightarrow> [] \<cdot> []]}"
    using states_P0 by blast
  thus False proof cases
    case 1
    then show ?thesis using dfa_LR0_nxt_final_impossible eq by presburger 
  next
    case 2
    hence no_states: "p \<inter> nfa.states char_fa = {}" using P0_final_item_notin_It
      by simp
    hence epsclo_empty: "char_fa.epsclo p = {}" unfolding char_fa.epsclo_def 
      by (metis char_fa.epsclo_def char_fa.epsclo_empty char_fa_epsclo_It_intersect_eq
          states_char_fa)
    have "dfa.nxt LR\<^sub>0 p X = (\<Union>i \<in> char_fa.epsclo p. char_fa.epsclo (nfa.nxt char_fa i X))"
      by auto
    also from no_states epsclo_empty have "... = {}"
      by blast
    finally show ?thesis using eq by blast
  qed
qed

lemma nxt_P0:
  "gpda.nxt P\<^sub>0 = 
    {([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q])|q a. q \<in> dfa.states LR\<^sub>0 \<and> dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}}"
  unfolding P\<^sub>0_def by (meson gpda.select_convs(4))

lemma eps_P0:
  "gpda.eps P\<^sub>0 = 
  {let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, dfa.nxt LR\<^sub>0 q (Nt X) # [q])|
    q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q\<^sub>n \<and> length \<alpha> = length qs \<and> X \<noteq> S'} \<union>
  {([q, dfa.init LR\<^sub>0], [P0_final])|q. q \<in> dfa.states LR\<^sub>0 \<and> [S' \<rightarrow> [Nt S] \<cdot> []] \<in> q}"
  unfolding P\<^sub>0_def by (meson gpda.select_convs(5))

lemmas P\<^sub>0_simps [simp] = states_P0 init_P0 final_P0 nxt_P0 eps_P0

lemma nxt_P0E [elim]:
  assumes "(qs, a, qs') \<in> gpda.nxt P\<^sub>0"
  obtains q where "qs = [q]" "qs' = dfa.nxt LR\<^sub>0 q (Tm a) # [q]"
    "q \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}"
  using assms by auto


lemma eps_P0E [elim, consumes 1, case_names reduce finish]:
  assumes "(ps, qs) \<in> gpda.eps P\<^sub>0"
  obtains 
    p ps' X \<alpha> where "ps = p # ps'" "qs = [dfa.nxt LR\<^sub>0 (last ps) (Nt X), last ps]"
    "set ps \<subseteq> dfa.states LR\<^sub>0" "[X \<rightarrow> \<alpha> \<cdot> []] \<in> p" "length \<alpha> = length ps'" "X \<noteq> S'"  |
    p where "ps = [p, dfa.init LR\<^sub>0]" "qs = [P0_final]" "p \<in> dfa.states LR\<^sub>0" "[S' \<rightarrow> [Nt S] \<cdot> []] \<in> p"
  using assms unfolding eps_P0 proof (standard, goal_cases reduce finish)
  case reduce
  from this(3) obtain p ps' X \<alpha> where 
    "(ps, qs) = (p # ps', [dfa.nxt LR\<^sub>0 (last ps) (Nt X), last ps])"
    "set ps \<subseteq> dfa.states LR\<^sub>0" "[X \<rightarrow> \<alpha> \<cdot> []] \<in> p" "length \<alpha> = length ps'" "X \<noteq> S'"
    by (smt (verit, ccfv_SIG) mem_Collect_eq prod.inject)
  then show ?case using reduce(1) by simp
qed blast


lemma finite_lists_complete_length_eq:
  "finite {q # qs| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q \<and> 
            length \<alpha> = length qs \<and> X \<noteq> S'}"
  (is "finite ?L")
proof (rule finite_surj)
  show "?L \<subseteq> (\<lambda>(q, qs, X, \<alpha>). q # qs) ` {(q, qs, X, \<alpha>)| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 
    \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q \<and> length \<alpha> = length qs \<and> X \<noteq> S'}" (is "_ \<subseteq> ?f ` ?F") 
  proof
    fix x
    assume "x \<in> ?L"
    then obtain q qs X \<alpha> where x_defs: "x = q # qs" "set (q # qs) \<subseteq> dfa.states LR\<^sub>0" 
      "[X \<rightarrow> \<alpha> \<cdot> []] \<in> q" "length \<alpha> = length qs" "X \<noteq> S'" by blast
    hence "x = ?f (q, qs, X, \<alpha>)" by fast
    thus "x \<in> ?f ` ?F" by standard (use x_defs in blast)
  qed
  show "finite ?F" 
  proof -
    note finite_It = finite_It[OF G'_finite]
    have "?F \<subseteq> dfa.states LR\<^sub>0 \<times> {xs |xs \<alpha>. set xs \<subseteq> dfa.states LR\<^sub>0 \<and> length xs = length \<alpha> 
        \<and> \<alpha> \<in> (Hists_of_items (It G'))} \<times> Nts_of_items (It G') \<times> Hists_of_items (It G')"
    (is "_ \<subseteq> _ \<times> ?xs \<times> _")
    proof
      fix x
      assume "x \<in> ?F"
      then obtain q qs X \<alpha> where x_defs: "x = (q, qs, X, \<alpha>)" "set (q # qs) \<subseteq> dfa.states LR\<^sub>0" 
        "[X \<rightarrow> \<alpha> \<cdot> []] \<in> q" "length \<alpha> = length qs" by blast
      with in_state_imp_in_It have X\<alpha>_It: "X \<in> Nts_of_items (It G')" "\<alpha> \<in> Hists_of_items (It G')"
        by auto
      with x_defs show "x \<in> dfa.states LR\<^sub>0 \<times> ?xs \<times> Nts_of_items (It G') \<times> Hists_of_items (It G')"
        by force
    qed
    with finite_lists_length_eq_Hists finite_items_imp_finite_Nts finite_items_imp_finite_Hists
    show ?thesis using finite_subset dfa_LR0.finite finite_It by fast
  qed
qed


lemma finite_eps_P0_reduce:
  "finite {let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, dfa.nxt LR\<^sub>0 q (Nt X) # [q])|
    q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q\<^sub>n \<and> length \<alpha> = length qs \<and> X \<noteq> S'}"
  (is "finite ?R")
proof (rule finite_subset)
  show "?R \<subseteq> {q # qs| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q 
    \<and> length \<alpha> = length qs \<and> X \<noteq> S'} \<times> {[p, q]|p q. p \<in> dfa.states LR\<^sub>0 \<and> q \<in> dfa.states LR\<^sub>0}"
  (is "_ \<subseteq> ?L \<times> ?T")
  proof
    fix e
    assume "e \<in> ?R"
    then obtain q\<^sub>n qs q X \<alpha> where e_defs: 
      "q = last (q\<^sub>n#qs)" "e = (q\<^sub>n # qs, dfa.nxt LR\<^sub>0 q (Nt X) # [q])"
      "set (q\<^sub>n#qs) \<subseteq> dfa.states LR\<^sub>0" "[X \<rightarrow> \<alpha> \<cdot> []] \<in> q\<^sub>n" "length \<alpha> = length qs" "X \<noteq> S'"
      by (smt (verit, ccfv_SIG) mem_Collect_eq)
    then show "e \<in> ?L \<times> ?T" 
      by (smt (verit, ccfv_threshold) dfa_LR0.nxt last_in_set list.discI mem_Collect_eq 
          mem_Sigma_iff subset_code(1))
  qed
  have "finite ?T" 
  proof -
    have "bij_betw (\<lambda>(p,q). [p,q]) (dfa.states LR\<^sub>0 \<times> dfa.states LR\<^sub>0) ?T" (is "bij_betw ?f ?P _")
      unfolding bij_betw_def by (fastforce intro: inj_onI)
    with dfa_LR0.finite show ?thesis using bij_betw_finite by fast
  qed
  with finite_lists_complete_length_eq show "finite (?L \<times> ?T)" by blast
qed

lemma finite_eps_P0_finish: 
  "finite {([q, dfa.init LR\<^sub>0], [P0_final])|q. q \<in> dfa.states LR\<^sub>0 \<and> [S' \<rightarrow> [Nt S] \<cdot> []] \<in> q}"
  (is "finite ?F")
proof (rule finite_surj)
  show "?F \<subseteq> (\<lambda>q. ([q, dfa.init LR\<^sub>0], [P0_final])) ` dfa.states LR\<^sub>0"
    by blast
qed (rule dfa_LR0.finite)

lemma eps_P0_cases[consumes 1, case_names reduce finish]:
  assumes "(ps, qs) \<in> gpda.eps P\<^sub>0"
  obtains r rs X \<alpha> where 
    "ps = r # rs" "qs = (let q = last (r # rs) in dfa.nxt LR\<^sub>0 q (Nt X) # [q])"
    "set (r # rs) \<subseteq> dfa.states LR\<^sub>0" "[X \<rightarrow> \<alpha> \<cdot> []] \<in> r" "length \<alpha> = length rs" |
    q where "q \<in> dfa.states LR\<^sub>0" "ps = [q, dfa.init LR\<^sub>0]" "qs = [P0_final]"
  using assms unfolding eps_P0 by standard (smt (verit, best) mem_Collect_eq prod.inject)+

interpretation P0: gpda P\<^sub>0
proof (unfold_locales, goal_cases _ _ nxt eps _ finite_nxt finite_eps)
  case (nxt ps a qs)
  with nxt_P0E obtain p where "ps = [p]"
  "p \<in> dfa.states LR\<^sub>0" "qs = [dfa.nxt LR\<^sub>0 p (Tm a), p]" "dfa.nxt LR\<^sub>0 p (Tm a) \<noteq> {}"
    by force
  with dfa_LR0.nxt show ?case by simp
next
  case (eps ps qs)
  then show ?case 
  proof (cases rule: eps_P0_cases, intro conjI)
    case (reduce r rs X \<alpha>)
    then show "qs \<noteq> []" "set ps \<subseteq> gpda.states P\<^sub>0" and ps_Cons: "ps \<noteq> []"
      by (metis list.distinct(1), auto)
    from reduce(3) have "dfa.nxt LR\<^sub>0 (last (r # rs)) (Nt X) \<in> dfa.states LR\<^sub>0"
      using dfa_LR0.nxt last_in_set by blast
    with reduce(1-3) ps_Cons show "set qs \<subseteq> gpda.states P\<^sub>0" 
      by (metis (no_types, lifting) Un_iff empty_set insert_subset last_in_set list.simps(15) 
          states_P0 subset_code(1))
  qed (use dfa_LR0.init in simp)
next
  case finite_nxt
  have "finite {(q, a)|q a. q \<in> dfa.states LR\<^sub>0 \<and> dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}}" (is "finite ?R")
  proof -
    have "?R = (\<Union>q \<in> dfa.states LR\<^sub>0. {(q,a)| a. dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}})" 
      by blast
    with finite_dfa_LR0_nempty_Tms dfa_LR0.finite show ?thesis by auto
  qed
  moreover have "bij_betw (\<lambda>(q, a). ([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q])) ?R (gpda.nxt P\<^sub>0)"
    (is "bij_betw ?f _ _")
  proof -
    have "inj_on ?f ?R" by standard auto
  moreover have "?f ` ?R = (gpda.nxt P\<^sub>0)" unfolding nxt_P0 by fastforce
  ultimately show ?thesis unfolding bij_betw_def by satx
  qed
  ultimately show ?case using bij_betw_finite by blast
next
  case finite_eps
  then show ?case using finite_eps_P0_reduce finite_eps_P0_finish by fastforce
qed (use dfa_LR0.init dfa_LR0.finite in simp_all)

lemma P0_read_iff_in_q:
"([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q]) \<in> gpda.nxt P\<^sub>0 
  = (\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] \<in> q \<and> q \<in> dfa.states LR\<^sub>0)"
proof 
  assume "([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q]) \<in> gpda.nxt P\<^sub>0"
  with nxt_P0 have q_nxt: "q \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}" by auto
  with char_fa.nxt_Power_dfa obtain i where i_defs:
    "i \<in> char_fa.epsclo q" "char_fa.epsclo (nfa.nxt char_fa i (Tm a)) \<noteq> {}"
      by fastforce
  hence "nfa.nxt char_fa i (Tm a) \<noteq> {}" by fastforce
  with nxt_char_fa obtain X \<alpha> \<beta> where "i = [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]" 
    by (meson all_not_in_conv in_nxt_char_fa_imp_shift)
  then show "\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] \<in> q \<and> q \<in> dfa.states LR\<^sub>0" 
    using i_defs in_states_imp_epsclo_eq[OF q_nxt(1)] q_nxt(1) by blast
next 
  assume "\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] \<in> q \<and> q \<in> dfa.states LR\<^sub>0"
  hence ex: "\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] \<in> q" and q_state: "q \<in> dfa.states LR\<^sub>0" 
    "q \<in> dfa.states char_fa.Power_dfa" by fastforce+
  then obtain X \<alpha> \<beta> where X_q: "[X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] \<in> q" (is "?i \<in> _") by blast
  then have X_epsclo: "?i \<in> char_fa.epsclo q"
    using char_fa.epsclo_increasing q_state by fastforce
  from X_q q_state have "(X, \<alpha> @ Tm a # \<beta>) \<in> Prods G'" using in_state_imp_in_It in_It_imp_in_Prods
    by (metis item.case)
  hence "nfa.nxt char_fa ?i (Tm a) \<noteq> {}" unfolding nxt_char_fa by simp
  moreover from X_q have "?i \<in> nfa.states char_fa" using in_state_imp_in_It q_state by simp
  ultimately have "char_fa.epsclo (nfa.nxt char_fa [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] (Tm a)) \<noteq> {}" 
    using char_fa.epsclo_increasing char_fa.nxt by fast
  hence "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}" using X_epsclo by fastforce
  thus "([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q]) \<in> gpda.nxt P\<^sub>0" using nxt_P0 q_state by blast
qed

lemma P0_complete_imp_reduce:
  assumes "[X \<rightarrow> \<alpha> \<cdot> []] \<in> q"
    "X \<noteq> S'"
    "q \<in> dfa.states LR\<^sub>0"
  obtains qs where "(q#qs, [dfa.nxt LR\<^sub>0 (last (q#qs)) (Nt X), last (q#qs)]) \<in> gpda.eps P\<^sub>0"
    "length qs = length \<alpha>"
proof -
  obtain qs where "set qs \<subseteq> dfa.states LR\<^sub>0" "length qs = length \<alpha>"
    using list_of_subset[of "dfa.states LR\<^sub>0" "length \<alpha>"] assms(3) by blast
  moreover then have "set (q#qs) \<subseteq> dfa.states LR\<^sub>0"
    using assms(3) by auto
  ultimately show thesis using that assms(2) unfolding eps_P0 
    by (smt (verit, ccfv_threshold) Un_iff assms(1) mem_Collect_eq)
qed

lemma P0_completes_nempty_imp_eps:
  assumes "completes p \<noteq> {}" "p \<in> dfa.states LR\<^sub>0"
  obtains ps qs where "(p#ps, qs) \<in> gpda.eps P\<^sub>0"
proof -
  from assms obtain X \<alpha> where X_def: "[X \<rightarrow> \<alpha> \<cdot> []] \<in> p" by blast
  thus thesis proof (cases "X = S'")
    case True
    with X_def assms(2) have "\<alpha> = [Nt S]" 
      using S'_derive_imp_S derive_singleton in_It_imp_in_Prods in_state_imp_in_It by fastforce
    then show ?thesis 
      using True X_def assms(2) that by auto
  next
    case False
    then show ?thesis using P0_complete_imp_reduce[OF X_def False assms(2)] that by meson
  qed
qed

notation P0.step (infix \<open>\<turnstile>P\<close> 55)
notation P0.steps (infix \<open>\<turnstile>P*\<close> 55)
notation P0.stepn (\<open>_ \<turnstile>P'(_') _\<close> 55)

section \<open>LR(0)-Adequate and Inadequate States\<close>

inductive shift_reduce :: "('n, 't) item set \<Rightarrow> bool" where
  "\<lbrakk>([p], a, ps) \<in> gpda.nxt P\<^sub>0; (p#ps', qs) \<in> gpda.eps P\<^sub>0\<rbrakk> \<Longrightarrow> shift_reduce p"

lemma shift_reduceE [elim]:
  assumes "shift_reduce q"
  obtains X \<alpha> a \<beta> Y \<gamma> where "[X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] \<in> q" "[Y \<rightarrow> \<gamma> \<cdot> []] \<in> q"
  using assms shift_reduce.cases 
  by (smt (verit, ccfv_threshold) Extended_Cfg.P0_read_iff_in_q Extended_Cfg_axioms Un_iff eps_P0
      list.sel(1) mem_Collect_eq nxt_P0 prod.inject)

definition reduce_reduce :: "('n, 't) item set \<Rightarrow> bool" where
  "reduce_reduce q \<equiv> card (completes q) > Suc 0"

lemma reduce_reduceE [elim]:
  assumes "reduce_reduce q"
  obtains X \<alpha> Y \<beta> where "[X \<rightarrow> \<alpha> \<cdot> []] \<in> q" "[Y \<rightarrow> \<beta> \<cdot> []] \<in> q" "[X \<rightarrow> \<alpha> \<cdot> []] \<noteq> [Y \<rightarrow> \<beta> \<cdot> []]"
proof -
  from assms obtain n where cardq: "card (completes q) = Suc (Suc n)" unfolding reduce_reduce_def 
    by (metis Suc_less_eq2 Suc_pred)
  moreover from this have nempty: "completes q \<noteq> {}" by fastforce
  ultimately obtain X \<alpha> where Xq: "[X \<rightarrow> \<alpha> \<cdot> []] \<in> q" 
    using completes_subset by blast
  let ?p = "completes q - {[X \<rightarrow> \<alpha> \<cdot> []]}"
  from cardq have cardp: "card ?p = Suc n" using Xq 
    by (metis DiffI card_Diff_singleton diff_Suc_1 item.inject neq_Nil_conv noncompletesE)
  moreover from this have "?p \<noteq> {}" by fastforce
  moreover from completes_subset[of q] have "?p \<subseteq> q" by blast
  ultimately obtain Y \<beta> where "[Y \<rightarrow> \<beta> \<cdot> []] \<in> q" "[X \<rightarrow> \<alpha> \<cdot> []] \<noteq> [Y \<rightarrow> \<beta> \<cdot> []]" by blast
  with Xq show thesis using that by presburger
qed

definition "LR0_inadequate q \<equiv> shift_reduce q \<or> reduce_reduce q"

abbreviation "LR0_adequate q \<equiv> \<not>LR0_inadequate q"

lemma complete_noncomplete_Tm_imp_inadequate:
  assumes "completes q \<noteq> {}" "[X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] \<in> q" "q \<in> dfa.states LR\<^sub>0"
  shows "LR0_inadequate q"
proof -
  from assms P0_read_iff_in_q have nxt: "([q], a, [dfa.nxt LR\<^sub>0 q (Tm a), q]) \<in> gpda.nxt P\<^sub>0" 
    by metis
  moreover from assms P0_completes_nempty_imp_eps[OF assms(1,3)] 
  obtain qs rs where "(q#qs, rs) \<in> gpda.eps P\<^sub>0" by blast
  ultimately show ?thesis unfolding LR0_inadequate_def using shift_reduce.intros by blast
qed


lemma LR0_adequate_complete_cases[consumes 2, case_names empty singleton]:
  assumes "LR0_adequate q"
    "q \<in> gpda.states P\<^sub>0"
  obtains "completes q = {}" |
    A \<alpha> where "completes q = {[A \<rightarrow> \<alpha> \<cdot> []]}"
proof -
  from assms(2) consider (final) "q = {[S' \<rightarrow> [] \<cdot> []]}" | (LR0) "q \<in> dfa.states LR\<^sub>0"
    by force
  thus thesis proof cases
    case LR0
    hence "finite q" by fastforce
    hence finite: "finite (completes q)" using completes_subset finite_subset by blast
    from assms consider "card (completes q) = 0" | "card (completes q) = Suc 0" 
      unfolding LR0_inadequate_def reduce_reduce_def by linarith
    thus thesis proof cases
      case 1
      then show ?thesis using 1 card_0_eq that finite by meson
    next
      case 2
      then show ?thesis using card_1_singleton_iff completesE that 
        by (metis singletonI)
    qed
  qed (use that in blast)
qed

lemma complete_in_adequate_imp_singleton:
  assumes "i \<in> completes q"
    "LR0_adequate q"
    "q \<in> gpda.states P\<^sub>0"
  shows "completes q = {i}"
  using assms(2-) by (cases rule: LR0_adequate_complete_cases) (use assms in auto)


lemma LR_adequate_completes_singleton_imp_derivern_Suc:
  assumes "LR0_adequate q"
    "q \<in> dfa.states LR\<^sub>0"
    "completes q = {[A \<rightarrow> \<alpha>\<^sub>0 \<cdot> []]}"
    "[X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] \<in> noncompletes q"
    and Y_derivers: "Prods G' \<turnstile> [Nt Y] \<Rightarrow>r(Suc n) \<gamma>" "Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w"
  shows "\<gamma> = Nt A # map Tm w \<and> \<alpha>\<^sub>0 = []"
proof -
  from Y_derivers(2) obtain  Z \<delta> where Z\<delta>: "\<gamma> = Z # \<delta>" 
    using deriver.cases by (metis append_is_Nil_conv neq_Nil_conv)
  moreover from Y_derivers(2) have "Nts_syms \<gamma> \<noteq> {}" 
    by (metis Nts_syms_empty_iff deriver_imp_derive not_derive_map_Tm)
  ultimately obtain \<gamma>' B \<zeta> where reachable:
    "[Y \<rightarrow> [] \<cdot> \<gamma>'] \<in> It G'" "([Y \<rightarrow> [] \<cdot> \<gamma>'], [B \<rightarrow> [] \<cdot> Z # \<zeta>]) \<in> (nfa.eps char_fa)\<^sup>*" 
    using derivern_non_word_imp_hd_eps_reachable[OF Y_derivers(1)[unfolded Z\<delta>]] by blast
  show ?thesis 
  proof (cases Z)
    case (Nt C)
    with Z\<delta> Y_derivers obtain u where C_prod: "(C, map Tm u) \<in> Prods G'" 
      by (metis derivers_last_step_single_Nt list.simps(8) map_Tm_Nt_eq_map_Tm_Nt 
          relpowp_imp_rtranclp self_append_conv2)
    from reachable have XY: "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>']) \<in> nfa.eps char_fa"
      using assms by (metis DiffE append.left_neutral in_It_imp_in_Prods in_state_imp_in_It 
          item.case prod_imp_eps)
    also note YB = reachable(2)[unfolded Nt]
    also have BCu: "([B \<rightarrow> [] \<cdot> Nt C # \<zeta>], [C \<rightarrow> [] \<cdot> map Tm u]) \<in> nfa.eps char_fa"
      using C_prod prod_imp_eps calculation in_eps_char_star_imp_in_It
        in_state_imp_in_It assms by blast
    finally have XC: "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [C \<rightarrow> [] \<cdot> map Tm u]) \<in> (nfa.eps char_fa)\<^sup>*" .
    show ?thesis
    proof (cases u)
      case Nil
      with XC have "[C \<rightarrow> [] \<cdot> map Tm u] = [A \<rightarrow> \<alpha>\<^sub>0 \<cdot> []]" using assms completes_singleton_imp_eq
        in_states_dfa_LR0_imp_eps_star_in_state by (metis Diff_iff list.simps(8))
      moreover have "\<delta> = map Tm w"
      proof -
        from Y_derivers(2)[unfolded Z\<delta> Nt] obtain \<eta> where C_prod2: 
          "(C, \<eta>) \<in> Prods G'" "\<eta> @ \<delta> = map Tm w"
          using deriver.cases by (smt (verit, ccfv_SIG) Nil_is_append_conv append_Nil hd_append2 
              list.map_disc_iff list.map_sel(1) list.sel(1) map_Tm_Nt_eq_map_Tm_Nt sym.distinct(1))
        moreover have "\<eta> = []" proof (cases \<eta>)
          case (Cons D \<theta>)
          with C_prod2 obtain a where "D = Tm a" by auto
          note XY also note YB
          also from C_prod2(1)[unfolded Cons this] have  
            "([B \<rightarrow> [] \<cdot> Nt C # \<zeta>], [C \<rightarrow> [] \<cdot> Tm a # \<theta>]) \<in> nfa.eps char_fa"
            unfolding eps_char_fa using calculation in_eps_char_star_imp_in_It assms BCu 
              \<open>D = Tm a\<close> by auto
          finally show ?thesis using in_states_dfa_LR0_imp_eps_star_in_state assms 
            by (metis Diff_iff complete_noncomplete_Tm_imp_inadequate empty_iff insertCI)
        qed simp
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis using Z\<delta> Nt by fast
    next
      case (Cons a v)
      then show ?thesis using XC complete_noncomplete_Tm_imp_inadequate assms 
        by (metis (mono_tags, lifting) Diff_iff in_states_dfa_LR0_imp_eps_star_in_state 
            insert_not_empty list.simps(9))
    qed
  next
    case (Tm a)
    from reachable have "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>']) \<in> nfa.eps char_fa"
      using assms in_state_imp_in_It eps_char_fa 
      by (metis (lifting) DiffE append_Nil in_It_imp_in_Prods item.case prod_imp_eps)
    also note reachable(2)[unfolded Tm]
    finally  show ?thesis using reachable complete_noncomplete_Tm_imp_inadequate assms 
        in_states_dfa_LR0_imp_eps_star_in_state by blast
  qed
qed

lemma LR_adequate_completes_singleton_imp_derivers:
  assumes "LR0_adequate q"
    "q \<in> dfa.states LR\<^sub>0"
    "completes q = {[A \<rightarrow> \<alpha>\<^sub>0 \<cdot> []]}"
    "[X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] \<in> q"
    and Y_derivers: "Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* \<gamma>" "Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w"
  shows "\<gamma> = Nt A # map Tm w \<and> \<alpha>\<^sub>0 = []"
  using Y_derivers(1) proof cases
  case rtrancl_refl
  with Y_derivers(2) have step: "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> map Tm w]) \<in> nfa.eps char_fa"
    using deriver_singleton_imp_eps assms(2,4) completes_subset in_state_imp_in_It 
    by blast
  show ?thesis 
  proof (cases w)
    case Nil
    with step assms have "[Y \<rightarrow> [] \<cdot> []] = [A \<rightarrow> \<alpha>\<^sub>0 \<cdot> []]" using completes_singleton_imp_eq
      by (metis in_states_dfa_LR0_imp_eps_star_in_state list.map_disc_iff
          r_into_rtrancl)
    then show ?thesis using Nil rtrancl_refl by simp
  next
    case (Cons a v)
    then show ?thesis 
      using step complete_noncomplete_Tm_imp_inadequate in_states_dfa_LR0_imp_eps_in_state assms 
      by (metis (mono_tags, lifting) empty_not_insert list.simps(9))
  qed
next
  case (rtrancl_into_rtrancl b)
  then obtain n where "Prods G' \<turnstile> [Nt Y] \<Rightarrow>r(n) b" using rtranclp_imp_relpowp by fast
  also note rtrancl_into_rtrancl(2)
  finally show ?thesis using LR_adequate_completes_singleton_imp_derivern_Suc assms
    by blast
qed

text \<open>For every LR(0)-adequate state \<open>q\<close>, one of the following holds:
\begin{itemize}
\item \<open>q\<close> contains no complete items
\item \<open>q\<close> consists of exactly one complete item
\item \<open>q\<close> contains exactly one complete item @{term "[A \<rightarrow> [] \<cdot> []]"} and all noncomplete items in \<open>q\<close>
are of the form @{term "[A \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>]"} where all rightmost derivations for Y leading to a word \<open>w\<close>
are of the form \<open>Y \<Rightarrow>r* Aw \<Rightarrow>r w\<close>.
\end{itemize}\<close>

lemma LR0_adequate_dfa_cases:
  assumes "LR0_adequate q"
    "q \<in> dfa.states LR\<^sub>0"
  obtains "completes q = {}" |
    A \<alpha> where "q = {[A \<rightarrow> \<alpha> \<cdot> []]}" |
      A where "completes q = {[A \<rightarrow> [] \<cdot> []]}" 
      "\<And>i. i \<in> noncompletes q \<Longrightarrow> \<exists>X \<alpha> Y \<beta>. i = [X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>]"
      "\<And>X \<alpha> Y \<beta> w \<gamma>. \<lbrakk>[X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] \<in> q; 
      Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* \<gamma>; Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w\<rbrakk> \<Longrightarrow> \<gamma> = Nt A # map Tm w"
proof -
  from assms(2) have "finite q" by fastforce
  with assms consider 
    (empty) "completes q = {}" | 
    (singleton) A \<alpha> where "completes q = {[A \<rightarrow> \<alpha> \<cdot> []]}"
    unfolding LR0_inadequate_def by (metis Suc_lessI card_1_singleton_iff 
        card_gt_0_iff completesE completes_subset finite_subset singletonI reduce_reduce_def)
  thus ?thesis
  proof cases
    case empty
    then show ?thesis using that by linarith
  next
    case singleton
    show ?thesis proof (cases "q = completes q")
      case False 
      { 
        fix X \<alpha> Y \<beta> assume "[X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> noncompletes q"
        hence "\<exists>Z. Y = Nt Z" using singleton complete_noncomplete_Tm_imp_inadequate assms(1,2) 
          by (cases Y) simp_all
      } 
      note in_nc_imp_Nt = this
      moreover with LR_adequate_completes_singleton_imp_derivers[OF assms singleton] have 
        "\<And>X \<alpha> Y \<beta> w \<gamma>. \<lbrakk>[X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> q;
          Prods G' \<turnstile> [Y] \<Rightarrow>r* \<gamma>; Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w\<rbrakk> \<Longrightarrow> \<gamma> = Nt A # map Tm w"
        by blast
      moreover have "\<alpha> = []" 
      proof -
        from False in_nc_imp_Nt obtain X \<alpha>' Y \<beta> where It: "[X \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>] \<in> q"     
          by (metis DiffD1 completes_subset noncompletesE psubsetI psubset_imp_ex_mem)
        hence "(X, \<alpha>' @ Nt Y # \<beta>) \<in> Prods G'" 
          by (metis Extended_Cfg.in_state_imp_in_It Extended_Cfg_axioms assms(2) 
              in_It_imp_in_Prods item.case)
        with reduced_imp_prod_singleton_derives_Tms[OF _ G'_reduced] obtain v where
          "Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* map Tm v" using derivers_iff_derives by metis
        with LR_adequate_completes_singleton_imp_derivers[OF assms singleton It] show ?thesis
          by (smt (verit, best) Cons_eq_map_D rtranclp.simps sym.distinct(1))
      qed
      ultimately show thesis using that(3) singleton by (metis noncompletesE)
    qed (use singleton that in simp)
  qed
qed

lemma LR0_adequate_cases[consumes 2, case_names completes_empty singleton comp_unique, 
      cases set: LR0_adequate]:
  assumes "LR0_adequate q"
    "q \<in> gpda.states P\<^sub>0"
  obtains "completes q = {}" |
    A \<alpha> where "q = {[A \<rightarrow> \<alpha> \<cdot> []]}" |
      A where "completes q = {[A \<rightarrow> [] \<cdot> []]}" 
      "\<And>i. i \<in> noncompletes q \<Longrightarrow> \<exists>X \<alpha> Y \<beta>. i = [X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>]"
      "\<And>X \<alpha> Y \<beta> w \<gamma>. \<lbrakk>[X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] \<in> q; 
      Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* \<gamma>; Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w\<rbrakk> \<Longrightarrow> \<gamma> = Nt A # map Tm w"
proof -
  from assms consider "q = {[S' \<rightarrow> [] \<cdot> []]}" | "q \<in> dfa.states LR\<^sub>0"
    by auto
  thus ?thesis proof cases
    case 1
    then show ?thesis using that(2) by auto
  next
    case 2
    show ?thesis using LR0_adequate_dfa_cases[OF assms(1) 2] that by auto
  qed
qed

section \<open>LR(k) Grammars\<close>

definition is_LR :: "nat \<Rightarrow> bool" where
  "is_LR k \<equiv> \<forall>\<alpha> X \<beta> w \<gamma> Y x y. 
    Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w \<and> 
                        Prods G' \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w \<and> 
    Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x \<and> 
                        Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y \<and> 
    take k w = take k y \<longrightarrow> \<alpha> = \<gamma> \<and> X = Y \<and> x = y"

lemma is_LRI [intro]:
  assumes 
    "\<And>\<alpha> X \<beta> w \<gamma> Y x y. \<lbrakk>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w; 
      Prods G' \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w; 
      Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x; 
      Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y; take k w = take k y\<rbrakk> 
      \<Longrightarrow> \<alpha> = \<gamma> \<and> X = Y \<and> x = y"
  shows "is_LR k"
  unfolding is_LR_def using assms by blast

lemma LR0_impossible:
  assumes "is_LR 0"
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w"
    "Prods G' \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w"
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x"
    "Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y"
  shows "\<alpha> \<noteq> \<gamma> \<Longrightarrow> False" "X \<noteq> Y \<Longrightarrow> False" "x \<noteq> y \<Longrightarrow> False"
  using assms unfolding is_LR_def by auto

lemma shift_reduce_imp_not_LR0:
  assumes "q \<in> dfa.states LR\<^sub>0"
    "shift_reduce q"
  shows "\<not>is_LR 0"
proof
  assume LR0: "is_LR 0"
  from assms(2) obtain X \<beta> Y \<delta> a \<alpha> where "[X \<rightarrow> \<beta> \<cdot> []] \<in> q" "[Y \<rightarrow> \<delta> \<cdot> Tm a # \<alpha>] \<in> q" by fast 
  then obtain \<gamma> where "reliable_prefix ([X \<rightarrow> \<beta> \<cdot> []]) \<gamma>"
    "reliable_prefix [Y \<rightarrow> \<delta> \<cdot> Tm a # \<alpha>] \<gamma>" using state_imp_valids assms(1) 
    by (blast dest: validD)
  then obtain \<gamma>' w \<nu> y where X_reliable:
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt X # map Tm w"
    "Prods G' \<turnstile>  \<gamma>' @ Nt X # map Tm w \<Rightarrow>r \<gamma>' @ \<beta> @ map Tm w" 
    "\<gamma> = \<gamma>' @ \<beta>"  
    and Y_reliable:
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<nu> @ Nt Y # map Tm y" 
    "Prods G' \<turnstile> \<nu> @ Nt Y # map Tm y \<Rightarrow>r \<nu> @ \<delta> @ Tm a # \<alpha> @ map Tm y"
    "\<gamma> = \<nu> @ \<delta>" 
    by (fastforce elim: reliable_prefixE)
  obtain v where "Prods G' \<turnstile> \<alpha> \<Rightarrow>* map Tm v"
  proof -
    note rtranclp.rtrancl_into_rtrancl[OF Y_reliable(1,2), THEN derivers_imp_derives]
    with reduced_derives_imp_substring_derives_Tms
      [OF _ G'_reduced G'_not_empty, of "\<nu> @ \<delta> @ [Tm a]" \<alpha> "map Tm y"]
    show thesis using that  G'_def by auto
  qed
  then show False proof (cases rule: derives_map_Tm_rm_cases)
    case Tms
    with X_reliable Y_reliable have "Prods G' \<turnstile> \<nu> @ Nt Y # map Tm y \<Rightarrow>r \<gamma>' @ \<beta> @ map Tm (a#v@y)"
      by (metis append.assoc list.simps(9) map_append)
    with X_reliable Y_reliable LR0 show False unfolding is_LR_def by force
  next
    case (Nt n u v' x Z)
    have final_step: "Prods G' \<turnstile> \<gamma>' @ \<beta> @ Tm a # map Tm u @ Nt Z # map Tm x @ map Tm y 
      \<Rightarrow>r \<gamma>' @ \<beta> @ map Tm (a#u@v'@x@y)"
    proof -
      from Nt(2) have "Prods G' \<turnstile> map Tm u @ Nt Z # map Tm x @ map Tm y 
        \<Rightarrow>r map Tm u @ map Tm v' @ map Tm x @ map Tm y"
        by (metis deriver.intros deriver_imp_in_Prods map_append)
      from deriver_prepend[OF this, of "\<gamma>' @ \<beta> @ [Tm a]"] show ?thesis by simp 
    qed
    note Y_reliable(1) also note Y_reliable(2)
    also have "Prods G' \<turnstile> \<nu> @ \<delta> @ Tm a # \<alpha> @ map Tm y 
      \<Rightarrow>r* \<gamma>' @ \<beta> @ Tm a # map Tm u @ Nt Z # map Tm x @ map Tm y"
    proof -
      note derivers_append_map_Tm[OF Nt(1)[THEN relpowp_imp_rtranclp], of y]
      note derivers_prepend[OF this, of "\<gamma>' @ \<beta> @ [Tm a]"]
      with Y_reliable(3) X_reliable(3) show ?thesis 
        by (metis append.assoc append_Cons append_Nil)
    qed
    finally show False using final_step X_reliable 
        LR0_impossible(3)[OF LR0 X_reliable(1,2), 
          of "\<gamma>' @ \<beta> @ Tm a # map Tm u" Z "x@y" "a#u@v'@x@y"] 
      by simp
  qed
qed

lemma is_LR0_imp_no_LR0_inadequate_states:
  assumes LR0: "is_LR 0"
  shows "\<forall>q\<in>gpda.states P\<^sub>0. LR0_adequate q"
proof (rule ccontr)
  assume "\<not>(\<forall>q\<in>gpda.states P\<^sub>0. LR0_adequate q)"
  then obtain q where q_inadequate: "q \<in> gpda.states P\<^sub>0" "LR0_inadequate q" by blast
  from this(2) show False unfolding LR0_inadequate_def
  proof (standard, goal_cases shift_reduce reduce_reduce)
    case reduce_reduce
    then obtain X \<beta> Y \<delta> where conflict: "[X \<rightarrow> \<beta> \<cdot> []] \<in> q" "[Y \<rightarrow> \<delta> \<cdot> []] \<in> q" 
      "[X \<rightarrow> \<beta> \<cdot> []] \<noteq> [Y \<rightarrow> \<delta> \<cdot> []]" by fastforce
    then obtain \<gamma> where "reliable_prefix ([X \<rightarrow> \<beta> \<cdot> []]) \<gamma>"
      "reliable_prefix ([Y \<rightarrow> \<delta> \<cdot> []]) \<gamma>" using state_imp_valids q_inadequate 
      by (auto simp: valids_def)
    then obtain \<gamma>' w \<nu> y where
      "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt X # map Tm w"
      "Prods G' \<turnstile> \<gamma>' @ Nt X # map Tm w \<Rightarrow>r \<gamma>' @ \<beta> @ map Tm w"
      "\<gamma> = \<gamma>' @ \<beta>"
      and
      "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<nu> @ Nt Y # map Tm y"
      "Prods G' \<turnstile> \<nu> @ Nt Y # map Tm y \<Rightarrow>r \<nu> @ \<delta> @ map Tm y"
      "\<gamma> = \<nu> @ \<delta>" 
      by (fastforce elim: reliable_prefixE)
    then show False using conflict(3) 
      by (metis LR0 LR0_impossible(1,2) append_assoc same_append_eq)
  qed (use shift_reduce_imp_not_LR0 LR0 q_inadequate in auto)
qed

lemma derivers_leftmost_derivers_last_step:
  assumes "Prods G' \<turnstile> Nt A # \<alpha> \<Rightarrow>r* \<beta>"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r map Tm w"
  obtains \<gamma> u v where "Prods G' \<turnstile> [Nt A] \<Rightarrow>r* \<gamma>" "Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm u"
    "\<beta> = \<gamma> @ map Tm v" "Prods G' \<turnstile> \<alpha> \<Rightarrow>r* map Tm v" "w = u @ v"
proof -
  from assms have "Prods G' \<turnstile> [Nt A] @ \<alpha> \<Rightarrow>r* \<beta>" by simp
  then show thesis proof (cases rule: derivers_append_cases)
    case (suffix \<alpha>')
    from assms(2) show thesis unfolding suffix proof (cases, goal_cases deriver)
      case (deriver A' \<gamma> u' v')
      hence eqs [simp]: "u' = []" "A' = A" "map Tm v' = \<alpha>'"  
      proof -
        from deriver have "u' = [] \<and> A' = A \<and> map Tm v' = \<alpha>'" 
          by (metis Tms_iff_no_Nt append_Cons append_Nil list.inject neq_Nil_conv sym.inject(1))
        thus "u' = []" "A' = A" "map Tm v' = \<alpha>'"  by blast+
      qed
      moreover from deriver obtain u where "\<gamma> = map Tm u" "Prods G' \<turnstile> [Nt A] \<Rightarrow>r map Tm u"
        unfolding eqs by (metis append_eq_map_conv deriver_singleton)
      ultimately show ?thesis using that[of "[Nt A]" u v'] suffix deriver 
        by (metis append_Cons append_Nil map_Tm_Nt_eq_map_Tm_Nt map_append rtranclp.rtrancl_refl)
    qed 
  next
    case (prefix \<gamma> v)
    from assms(2) obtain u where "Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm u" "w = u @ v"
      unfolding prefix(3) by (smt (verit, ccfv_threshold) append_eq_map_conv deriver_append_map_Tm
          map_Tm_inject_iff)
    with prefix show thesis using that by blast
  qed
qed

lemma prefix_comp_unique_imp_eps:
  assumes "LR0_adequate (valids \<alpha>)" (is "LR0_adequate ?p")
    "[X \<rightarrow> [] \<cdot> []] \<in> valids \<alpha>"
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt Y # map Tm x"
    "Prods G' \<turnstile> \<alpha> @ \<alpha>' @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ map Tm y"
  shows "\<alpha>' = [] \<and> Y = X \<and> x = y"
proof -
  from assms(2) obtain w where X_derivers: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w"
    "Prods G' \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ map Tm w" 
    using reliable_prefixE unfolding valids_def by force
  from assms(3) show ?thesis proof (cases rule: stepcnt_cases)
    case refl
    with assms(4) have "\<alpha> @ map Tm y = [Nt S]" 
      using S'_derive_imp_S deriver_imp_derive by auto
    moreover then have"y = []" 
      by (metis Nil_is_append_conv list.map_disc_iff syms_split_tl)
    ultimately show ?thesis using refl by auto
  next
    case (step n)
    from derivern_Suc_substring_reliable[OF this] obtain A \<beta> Z' \<gamma> z where
      A_reliable: "reliable_prefix [A \<rightarrow> \<beta> \<cdot> Z' # \<gamma>] \<alpha>" 
        "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Z' # \<gamma> @ map Tm z"
        "Prods G' \<turnstile> Z' # \<gamma> @ map Tm z \<Rightarrow>r* \<alpha>' @ Nt Y # map Tm x"
      by blast
    from assms(3,4) have deriver_y: "Prods G' \<turnstile> \<alpha>' @ Nt Y # map Tm x \<Rightarrow>r map Tm y"
      by (metis append_Nil deriver_prefix_indep)
    have "?p \<in> gpda.states P\<^sub>0" 
      using dfa_LR0.nextl_init_state nextl_dfa_LR0_is_valids by force
    with assms(1) show ?thesis proof (cases rule: LR0_adequate_cases)
      case (comp_unique B)
      with assms(2) have AX [simp]: "B = X"
        by auto
      from A_reliable obtain Z'' where Z''_def [simp]: "Z' = Nt Z''" using comp_unique 
         by (auto simp: valids_def)
      from A_reliable(3) deriver_y obtain \<gamma>' u v  where decomp: 
        "Prods G' \<turnstile> [Nt Z''] \<Rightarrow>r* \<gamma>'" "Prods G' \<turnstile> \<gamma>' \<Rightarrow>r map Tm u" 
        "Prods G' \<turnstile> \<gamma> @ map Tm z \<Rightarrow>r* map Tm v"
        "\<gamma>' @ map Tm v = \<alpha>' @ Nt Y # map Tm x" "y = u @ v"
        using derivers_leftmost_derivers_last_step[of Z'' "\<gamma> @ map Tm z" "\<alpha>' @ Nt Y # map Tm x" y] 
        unfolding Z''_def by metis
      with comp_unique have "\<gamma>' = Nt X # map Tm u" using A_reliable 
        by (simp add: valids_def)
      with decomp show ?thesis 
        by (metis (no_types, lifting) append_Cons map_append rm_eq_imp_eq self_append_conv2)
    qed (use assms(2) completes_def in fastforce, use A_reliable assms(2) valids_def in auto)
  qed
qed

lemma LRk_wlog:
  assumes "\<And>\<alpha> X \<beta> w \<gamma> Y x y \<delta>. \<lbrakk>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w; 
    Prods G' \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w; 
    Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x; 
    Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y; take k w = take k y;
    \<gamma> @ \<delta> @ map Tm x = \<alpha> @ \<beta> @ map Tm y; (Y, \<delta>) \<in> Prods G'; length (\<alpha> @ \<beta>) \<le> length (\<gamma> @ \<delta>)\<rbrakk> 
    \<Longrightarrow> \<alpha> = \<gamma> \<and> X = Y \<and> x = y"
  shows "is_LR k"
proof (standard, goal_cases LR)
  case (LR \<alpha> X \<beta> w \<gamma> Y x y)
  from this(4) show ?case proof (cases, goal_cases deriver)
    case (deriver A \<delta> u v)
    hence eqs [simp]: "u = \<gamma>" "A = Y" "v = x" using rm_eq_imp_eq by fastforce+
    show ?thesis proof (cases "length (\<alpha> @ \<beta>)" "length (\<gamma> @ \<delta>)" rule: le_cases)
      case le
      then show ?thesis using assms deriver LR unfolding eqs by metis
    next
      case ge
      with deriver(2) obtain z where \<alpha>\<beta>_eq: "\<alpha> @ \<beta> = \<gamma> @ \<delta> @ map Tm z" "x = z@y" unfolding eqs 
        using eq_hd_lt_imp_substring[of "\<gamma> @ \<delta>" "map Tm x" "\<alpha> @ \<beta>" "map Tm y"] append.assoc 
      by (metis (no_types, opaque_lifting) append_eq_map_conv map_Tm_inject_iff)
      from this(2) LR(5) have take_eq: "take k x = take k (z@w)" 
      proof -
        have "take k x = take k z @ take (k - length z) y" 
          using \<alpha>\<beta>_eq take_append by blast
        also have "... = take k z @ take (k - length z) w" using LR(5) take_diff by metis
        finally show ?thesis using take_append by metis
      qed
      note LR(1)
      from LR(2) have Xw_zw: "Prods G' \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<gamma> @ \<delta> @ map Tm (z@w)"
        by (metis \<alpha>\<beta>_eq(1) append.assoc map_append)
      note LR(3)
      from deriver have Y\<delta>: "Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<gamma> @ \<delta> @ map Tm x"
        using LR(4) by auto
      have X_prod: "(X, \<beta>) \<in> Prods G'" 
        by (meson LR(2) deriver_imp_in_Prods)
       from \<alpha>\<beta>_eq have "\<alpha> @ \<beta> @ map Tm w = \<gamma> @ \<delta> @ map Tm (z@w)"
        using append.assoc map_append by simp
      from assms[OF LR(3) Y\<delta> LR(1) Xw_zw take_eq this X_prod ge] 
       show ?thesis using \<alpha>\<beta>_eq(2) by simp
    qed
  qed
qed

lemma no_LR0_inadequate_states_imp_is_LR0:  
  assumes adequates: "\<forall>q\<in>gpda.states P\<^sub>0. LR0_adequate q"
  shows "is_LR 0" 
proof (rule LRk_wlog, goal_cases LR)
  case (LR \<alpha> X \<beta> w \<gamma> Y x y \<delta>)
  obtain p where p_nextl: "dfa.nextl LR\<^sub>0 (dfa.init LR\<^sub>0) (\<alpha>@\<beta>) = p" by presburger
  with adequates have p_adequate: "LR0_adequate p" "p \<in> dfa.states LR\<^sub>0" using states_P0 
    using dfa_LR0.nextl_init_state by (metis Un_iff, metis)
  hence p_P0: "p \<in> gpda.states P\<^sub>0"
    by auto
  from p_nextl have p_valids: "p = valids (\<alpha>@\<beta>)"
    using nextl_dfa_LR0_is_valids by auto
  from LR have X_reliable: "reliable_prefix ([X \<rightarrow> \<beta> \<cdot> []]) (\<alpha>@\<beta>)" 
    using char_eq_reliable_prefix derivers_imp_char by auto
  from p_adequate(1) p_P0 show ?case proof cases
    case (singleton A \<alpha>')
    with X_reliable have singleton: "p = {[X \<rightarrow> \<beta> \<cdot> []]}" 
      using p_nextl nextl_dfa_LR0_is_valids unfolding valids_def by force
    from LR(6,8) obtain z where z_defs: "\<gamma> @ \<delta> = \<alpha> @ \<beta> @ map Tm z" "z @ x = y"
      using eq_hd_lt_imp_substring[of "\<alpha> @ \<beta>" "map Tm y" "\<gamma> @ \<delta>" "map Tm x"] append.assoc 
      by (metis (no_types, opaque_lifting) append_eq_map_conv map_Tm_inject_iff)
    from this show ?thesis proof (cases rule: app_eq_rm_cases)
      case (1 u v)
      with derivers_substring_reliable[of "\<alpha> @ \<beta>" "map Tm u" Y x] LR(3)
      obtain B \<alpha>'' C \<beta>'' where "reliable_prefix [B \<rightarrow> \<alpha>'' \<cdot> C # \<beta>''] (\<alpha> @ \<beta>)" by fastforce
      then show ?thesis using singleton p_valids unfolding valids_def by blast
    next
      case (2 \<delta>')
      from LR(3) have "reliable_prefix [Y \<rightarrow> \<delta>' \<cdot> map Tm z] (\<alpha> @ \<beta>)" 
        using 2 LR(4,6) z_defs by fastforce
      with singleton p_valids have "z = [] \<and> \<delta>' = \<beta> \<and> X = Y" 
        by (metis item.inject map_is_Nil_conv mem_Collect_eq singletonD valids_def)
      with 2 z_defs show ?thesis by simp
    qed
  next
    case (comp_unique A)
    with p_valids X_reliable have comp_X: "completes p = {[X \<rightarrow> \<beta> \<cdot> []]}" "\<beta> = []"
      unfolding completes_def by (auto simp: valids_def) 
    from LR(6) have eq: "(\<alpha> @ \<beta>) @ map Tm y = \<gamma> @ \<delta> @ map Tm x" by simp
    show ?thesis proof (cases rule: substring_app_cases[OF eq LR(8)])
      case (1 _ _)
      with prefix_comp_unique_imp_eps[OF p_adequate(1)[unfolded p_valids]] X_reliable comp_X LR 
      show ?thesis by (metis append.assoc append.right_neutral completesD insertCI p_valids)
    next
      case (2 \<delta>\<^sub>1 x')
      from LR(3) have Y_reliable: "reliable_prefix [Y \<rightarrow> \<delta>\<^sub>1 \<cdot> map Tm x'] (\<alpha> @ \<beta>)" 
      proof
        from LR(4,6) 2 show "Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r (\<alpha> @ \<beta>) @ map Tm x' @ map Tm x"          
          by (metis eq map_append)
      qed (rule 2)
      show ?thesis proof (cases x')
        case Nil
        with Y_reliable p_valids have "[Y \<rightarrow> \<delta>\<^sub>1 \<cdot> map Tm x'] \<in> completes p" unfolding completes_def 
          by (simp add: valids_def)
        with comp_X have "[Y \<rightarrow> \<delta>\<^sub>1 \<cdot> map Tm x'] = [X \<rightarrow> [] \<cdot> []]" by simp
        with 2 show ?thesis using comp_X by simp
      next
        case (Cons a x'')
        from Y_reliable p_valids have "[Y \<rightarrow> \<delta>\<^sub>1 \<cdot> Tm a # map Tm x''] \<in> noncompletes p"
          unfolding Cons by (auto simp: valids_def)
        then show ?thesis using comp_unique(2) sym.exhaust by blast
      qed
    qed
  qed (use p_valids X_reliable completes_def valids_def in fastforce)
qed
    

theorem is_LR0_iff_no_LR0_inadequates:
  "is_LR 0 = (\<forall>q\<in>gpda.states P\<^sub>0. LR0_adequate q)"
  using is_LR0_imp_no_LR0_inadequate_states no_LR0_inadequate_states_imp_is_LR0 by metis

section \<open>Determinism of \<open>P\<^sub>0\<close> and Language Equivalence\<close>

lemma LR_adequate_imp_P0_nxt_unique:
  assumes "p \<in> gpda.states P\<^sub>0" "LR0_adequate p"
    "p # ps = ps' @ rs" "(ps', a, qs) \<in> gpda.nxt P\<^sub>0" "(p # ps, a # w) \<turnstile>P c1"
  shows "(qs @ rs, w) = c1"
  using assms(5) proof (cases, goal_cases qs'_nxt _)
  case (qs'_nxt ps'' qs' _)
  with assms nxt_P0E have eq: "(ps', a, qs) = (ps'', a, qs')" 
    by (smt (verit, best) append_Cons list.inject)
  with assms qs'_nxt show ?thesis by auto
next
  case (step_eps _ _ _)
  then show ?thesis using assms(4) shift_reduce.intros assms(2) eps_P0E
    unfolding LR0_inadequate_def 
    by (smt (verit, ccfv_threshold) P0.eps append_eq_Cons_conv list.inject nxt_P0E
        assms(3))
qed

lemma LR_adequate_eps_tl_eq_imp_P0_eps_unique:
  assumes "p \<in> gpda.states P\<^sub>0" "LR0_adequate p"
    "p # ps = p # ps0 @ rs0" "(p # ps0, qs0) \<in> gpda.eps P\<^sub>0" "(p # ps0, qs1) \<in> gpda.eps P\<^sub>0"
  shows "qs0 @ rs0 = qs1 @ rs0"
  using assms(4) proof (cases rule: eps_P0E)
  case (reduce p'' ps'' X \<alpha>)
  note qs_reduce = this
  hence qs_eqs [simp]: "p'' = p" "ps'' = ps0" by auto
  have comp_singleton: "completes p = {[X \<rightarrow> \<alpha> \<cdot> []]}" 
    using complete_in_adequate_imp_singleton[OF _ assms(2,1)]
      qs_reduce unfolding completes_def by auto
  from assms(5) show ?thesis proof (cases rule: eps_P0E)
    case (reduce _ _ Y \<beta>)
    with assms(2) qs_reduce have "[X \<rightarrow> \<alpha> \<cdot> []] = [Y \<rightarrow> \<beta> \<cdot> []]"
      using comp_singleton unfolding completes_def 
      by (metis (mono_tags, lifting) item.case list.inject mem_Collect_eq singletonD)
    then show ?thesis using qs_reduce reduce 
      using assms(4-) by fastforce
  next
    case (finish _)
    with assms(2) qs_reduce have "[X \<rightarrow> \<alpha> \<cdot> []] = [S' \<rightarrow> [Nt S] \<cdot> []]"
      using comp_singleton unfolding completes_def 
      by (metis (mono_tags, lifting) item.case list.inject mem_Collect_eq singletonD)
    then show ?thesis using qs_reduce by blast
  qed
next
  case (finish _)
  note qs_finish = this
  hence comp_singleton: "completes p = {[S' \<rightarrow> [Nt S] \<cdot> []]}" 
    using complete_in_adequate_imp_singleton[OF _ assms(2,1)]
       unfolding completes_def by auto
  from assms(5) show ?thesis proof (cases rule: eps_P0E)
    case (reduce p ps' X \<alpha>)
    with assms(2) qs_finish comp_singleton show ?thesis 
      by (metis (no_types, lifting) completes_singleton_imp_eq item.inject list.inject)
  next
    case finish
    then show ?thesis using qs_finish assms(4-) by fastforce
  qed
qed

lemma LR_adequate_imp_P0_eps_unique:
  assumes "p \<in> gpda.states P\<^sub>0" "LR0_adequate p"
    and qs_eps: "p # ps = p # ps0 @ rs0" "(p # ps0, qs0) \<in> gpda.eps P\<^sub>0"
    and qs'_eps: "p # ps = p # ps1 @ rs1" "(p # ps1, qs1) \<in> gpda.eps P\<^sub>0"
  shows "qs0 @ rs0 = qs1 @ rs1"
proof (cases "ps0 = ps1")
  case True
  with qs_eps qs'_eps have rs_eq: "rs0 = rs1" by auto
  with True LR_adequate_eps_tl_eq_imp_P0_eps_unique[OF assms(1,2)] qs_eps qs'_eps
  show ?thesis by metis
next
  case False
  with qs_eps qs'_eps have neq: "length ps0 \<noteq> length ps1" 
    by fastforce
  from qs_eps(2) show ?thesis 
  proof (cases rule: eps_P0E)
    case (reduce p'' ps'' X \<alpha>)
    have comp_singleton: "completes p = {[X \<rightarrow> \<alpha> \<cdot> []]}" 
      using complete_in_adequate_imp_singleton[OF _ assms(2,1)]
        reduce unfolding completes_def by auto
    from qs'_eps(2) show ?thesis 
      using comp_singleton reduce neq by (cases rule: eps_P0E) 
        (metis completes_singleton_imp_eq item.inject list.inject)+
  next
    case (finish p)
    have comp_singleton: "completes p = {[S' \<rightarrow> [Nt S] \<cdot> []]}" 
      using complete_in_adequate_imp_singleton[OF _ assms(2,1)]
        finish unfolding completes_def by auto          
    from qs'_eps(2) show ?thesis 
      using comp_singleton finish neq by (cases rule: eps_P0E) 
        (metis completes_singleton_imp_eq item.inject list.inject, metis list.inject)
  qed
qed



text \<open>If a state of \<open>P\<^sub>0\<close> is LR(0)-adequate, it behaves deterministically on that state:\<close>

lemma LR0_adequate_imp_P0_step_unique:
  assumes "p \<in> gpda.states P\<^sub>0" "LR0_adequate p"
    "(p # ps, u) \<turnstile>P c0" "(p # ps, u) \<turnstile>P c1"
  shows "c0 = c1"
using assms(3) proof (cases, goal_cases qs_nxt qs_eps)
  case (qs_eps ps0 qs0 rs0)
  with eps_P0E obtain ps0' where ps0_eq: "ps0 = p # ps0'" 
    by (metis Cons_eq_append_conv P0.eps)
  from assms(4) show ?thesis
  proof (cases, goal_cases qs'_nxt qs'_eps)
    case (qs'_eps ps1 qs1 rs1)
    with eps_P0E obtain ps1' where ps1_eq: "ps1 = p # ps1'" 
      by (metis Cons_eq_append_conv P0.eps)
    from LR_adequate_imp_P0_eps_unique[OF assms(1,2)] qs_eps qs'_eps show ?thesis 
      unfolding ps0_eq ps1_eq by (smt (verit, ccfv_SIG) Cons_eq_appendI)
  qed (use assms LR_adequate_imp_P0_nxt_unique in blast)
qed (use assms LR_adequate_imp_P0_nxt_unique in blast)

theorem no_LR0_inadequates_imp_P0_stepn_unique:
  assumes "\<forall>p \<in> gpda.states P\<^sub>0. LR0_adequate p"
    "set ps \<subseteq> gpda.states P\<^sub>0"
    "(ps, u) \<turnstile>P(n) c0" "(ps, u) \<turnstile>P(n) c1"
  shows "c0 = c1"
  using assms(3-,2) proof (induction n arbitrary: ps u)
  case (Suc n)
  then obtain p qs where Cons [simp]: "ps = p # qs"  
    by (metis P0.step_imp_Cons relpowp_Suc_E2 surj_pair)
  obtain ps' u' where "(p # qs, u) \<turnstile>P (ps', u')" "(ps', u') \<turnstile>P(n) c0" "(ps', u') \<turnstile>P(n) c1"
  proof -
    from Suc obtain p0 ps0 u0 p1 ps1 u1 where 
      "(ps, u) \<turnstile>P (p0 # ps0, u0)" "(p0 # ps0, u0) \<turnstile>P(n) c0"
      "(ps, u) \<turnstile>P (p1 # ps1, u1)" "(p1 # ps1, u1) \<turnstile>P(n) c1"
      using relpowp_Suc_D2 P0.step_imp_Cons by (smt (verit, ccfv_SIG) surj_pair)
    moreover from Suc.prems(3) assms(1) have "p \<in> gpda.states P\<^sub>0" "LR0_adequate p"
      by auto
    ultimately show thesis using that LR0_adequate_imp_P0_step_unique Cons by metis
  qed
  moreover from this(1) Suc.prems(3) have "set ps' \<subseteq> gpda.states P\<^sub>0"
    using P0.step_states_imp_states by simp
  ultimately show ?case using Suc.IH by presburger
qed simp

text \<open>If \<open>P\<^sub>0\<close> has no LR(0)-inadequate states, it is deterministic:\<close>

corollary no_LR0_inadequates_imp_P0_deterministic:
  assumes "\<forall>p \<in> gpda.states P\<^sub>0. LR0_adequate p"
    "([gpda.init P\<^sub>0], w) \<turnstile>P(n) c0" "([gpda.init P\<^sub>0], w) \<turnstile>P(n) c1"
  shows "c0 = c1"
  using assms no_LR0_inadequates_imp_P0_stepn_unique[OF assms(1) _ assms(2-)] P0.init by simp


subsection \<open>Language Equivalence of \<open>P\<^sub>0\<close> and its Grammar\<close>

lemma P0_step_cases [consumes 1, case_names shift reduce finish, cases set: P0.step]:
  assumes "c\<^sub>0 \<turnstile>P c\<^sub>1"
  obtains q qs a w where "c\<^sub>0 = (q # qs, a # w)" "c\<^sub>1 = (dfa.nxt LR\<^sub>0 q (Tm a) # q # qs, w)"
    "q \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}" |
    p\<^sub>n ps p\<^sub>0 qs X \<alpha> w where "p\<^sub>0 = last (p\<^sub>n # ps)" "c\<^sub>0 = (p\<^sub>n # ps @ qs, w)" 
    "c\<^sub>1 = (dfa.nxt LR\<^sub>0 p\<^sub>0 (Nt X) # p\<^sub>0 # qs, w)" "set (p\<^sub>n # ps) \<subseteq> dfa.states LR\<^sub>0"
    "[X \<rightarrow> \<alpha> \<cdot> []] \<in> p\<^sub>n" "length \<alpha> = length ps" "X \<noteq> S'" |
    q qs w where "c\<^sub>0 = (q # dfa.init LR\<^sub>0 # qs, w)" "c\<^sub>1 = ({[S' \<rightarrow> [] \<cdot> []]} # qs, w)"
      "q \<in> dfa.states LR\<^sub>0" "[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q"
  using assms proof cases
  case (step_nxt ps a qs rs w)
  then show ?thesis using that(1) by fastforce
next
  case (step_eps ps qs rs w)
  from this(3,1,2) show ?thesis using step_eps that(2-) 
      by (cases rule: eps_P0E) auto
qed

lemma P0_final_step_is_finish:
  assumes "(qs, u) \<turnstile>P ([{[S' \<rightarrow> [] \<cdot> []]}], [])" 
  obtains q where "q \<in> dfa.states LR\<^sub>0" "(qs, u) = ([q, dfa.init LR\<^sub>0], [])" "[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q"
  using assms by cases auto

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

(* TODO refactor *)
lemma P0_stack_substr_reachable:
  assumes "([gpda.init P\<^sub>0], u) \<turnstile>P(n) (p # ps @ q # qs, v)" "p \<in> dfa.states LR\<^sub>0"
  obtains m u' where "m < n" "([gpda.init P\<^sub>0], u) \<turnstile>P(m) (q # qs, u')"
    "(q # qs, u') \<turnstile>P(n - m) (p # ps @ q # qs, v)"
  using assms proof (induction n arbitrary: p ps q qs v thesis)
  case (Suc n)
  note that = Suc.prems(1)
  from Suc obtain c where n_steps: "([gpda.init P\<^sub>0], u) \<turnstile>P(n) c" "c \<turnstile>P (p # ps @ q # qs, v)"
    by auto
  from this(2) show ?case proof cases
    case (shift r rs a w)
    show ?thesis proof (cases ps)
      case Nil
      with shift have "r # rs = q # qs" by auto
      note n_steps[unfolded shift this]
      from Suc.prems(1)[OF _ this(1)] show thesis 
        using shift n_steps(2) \<open>r # rs = q # qs\<close> by auto
    next
      case (Cons s ss)
      with Suc.IH[of q qs s ss] obtain m u' where "m < n" "([gpda.init P\<^sub>0], u) \<turnstile>P(m) (q # qs, u')"
        "(q # qs, u') \<turnstile>P(n - m) c" using n_steps shift by auto
      then show ?thesis using n_steps(2) that 
        using Suc_diff_le le_eq_less_or_eq less_Suc_eq by auto
    qed
  next
    case (reduce r\<^sub>n rs r\<^sub>0 ss X \<alpha> w)
    show ?thesis proof (cases ss)
      case Nil
      note ss_Nil = this
      from reduce(3) have eqs [simp]: "p # ps = [dfa.nxt LR\<^sub>0 r\<^sub>0 (Nt X)]" "q # qs = [r\<^sub>0]" 
        unfolding Nil by (simp_all add: append_eq_Cons_conv)
      show ?thesis proof (cases rs rule: rev_cases)
        case Nil
        with reduce ss_Nil have "c = (q # qs, w)" by force
        then show ?thesis using that[of n] n_steps by auto
      next
        case (snoc rs')
        with ss_Nil reduce have "c = (r\<^sub>n # rs' @ q # qs, w)" by auto
        with Suc.IH[OF _ n_steps(1)[unfolded this]] show ?thesis 
          using that n_steps(2) Suc_diff_le le_eq_less_or_eq less_Suc_eq 
            list.set_intros(1) reduce(4) relpowp_Suc_I subsetD by auto
      qed
    next
      case (Cons a as)
      note ss_Cons = this
      show ?thesis proof (cases ps)
        case Nil
        with reduce(3) have rss[simp]: "r\<^sub>0 # ss = q # qs" by auto
        show ?thesis proof (cases rs rule: rev_cases)
          case Nil
          with reduce rss have "c = (q # qs, w)" by force
          then show ?thesis using n_steps that by fastforce
        next
          case (snoc rs' _)
          with reduce rss have "c = (r\<^sub>n # rs' @ q # qs, w)" by fastforce
          moreover from reduce have "r\<^sub>n \<in> dfa.states LR\<^sub>0" by fastforce
          ultimately show ?thesis using that Suc.IH[of q qs r\<^sub>n rs' w] n_steps      
            by (metis (no_types, lifting) Suc_diff_le less_Suc_eq_le less_or_eq_imp_le relpowp_Suc_I)
        qed
      next
        case (Cons b bs)
        with reduce(3) obtain ss' where q_substr: "ss = ss' @ q # qs" 
          by auto
        hence "c = (r\<^sub>n # (rs @ ss') @ q # qs, w)" using reduce by fastforce
        moreover from reduce have "r\<^sub>n \<in> dfa.states LR\<^sub>0" by force
        ultimately obtain m u' where 
          "m < n" "([gpda.init P\<^sub>0], u) \<turnstile>P(m) (q # qs, u')" "(q # qs, u') \<turnstile>P(n - m) c"
          using  Suc.IH[of q qs r\<^sub>n "rs @ ss'" w] n_steps reduce by blast
        then show ?thesis using n_steps that Suc_diff_le le_eq_less_or_eq less_Suc_eq by auto
      qed
    qed
  qed (use Suc(4) P0_final_item_notin_It in_state_imp_in_It in blast)
qed simp

lemma P0_stack_inc_Suc_0_or_dec:
  assumes "(ps, u) \<turnstile>P (qs, v)" "length ps \<noteq> length qs"
  shows "length ps > length qs \<or> length qs = Suc (length ps)"
  using assms proof cases
  case (reduce _ ps')
  show ?thesis using assms(2) reduce by (cases ps') auto
qed simp_all

lemma tl_of_stack_contains_no_empty:
  "\<lbrakk>([gpda.init P\<^sub>0], u) \<turnstile>P* (q # qs, v); q \<in> dfa.states LR\<^sub>0\<rbrakk> \<Longrightarrow> {} \<notin> set qs"
proof (induction "q # qs" v arbitrary: q qs rule: rtranclp_induct2)
  case (step ps v w)
  from this(2) show ?case proof cases
    case (shift r rs a x)
    then show ?thesis using step by fastforce
  next
    case (reduce r\<^sub>n rs r\<^sub>0 ss X \<alpha> x)
    then show ?thesis using step 
      by (metis (no_types, lifting) ext Un_iff empty_iff last_in_set list.distinct(1) list.inject
          list.set_intros(1) prod.inject set_ConsD set_append subset_eq)
  next
    case (finish r rs x)
    then show ?thesis using step(4) step.hyps(3) by fastforce
  qed
qed simp


  
inductive stack_word :: "('n, 't) syms \<Rightarrow> ('n, 't) item set list \<times> 't list 
  \<Rightarrow> ('n, 't) item set list \<times> 't list \<Rightarrow> bool" (\<open>_ \<Turnstile> _ \<turnstile>P* _\<close> 55)  where
sw_refl [intro]: "[] \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>0" |
sw_step: "\<lbrakk>\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* (ps @ q # qs, u); (ps @ q # qs, u) \<turnstile>P (dfa.nxt LR\<^sub>0 q X # q # qs, v)\<rbrakk> 
  \<Longrightarrow> X # drop (length ps) \<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* (dfa.nxt LR\<^sub>0 q X # q # qs, v)"

inductive_cases stack_word_reflE [elim]: "[] \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1"
inductive_cases stack_word_stepE [elim]: "X # \<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1"

lemma sw_stepI [intro]:
  assumes "\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1" "c\<^sub>1 \<turnstile>P c\<^sub>2"  
    "c\<^sub>1 = (ps @ q # qs, u)" "c\<^sub>2 = (dfa.nxt LR\<^sub>0 q X # q # qs, v)" "\<alpha>' = drop (length ps) \<alpha>"
  shows "X # \<alpha>' \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>2"
  using assms sw_step by blast

lemma stack_word_imp_P0_steps:
  "\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1 \<Longrightarrow> c\<^sub>0 \<turnstile>P* c\<^sub>1"
  by (induction rule: stack_word.induct) auto

lemma P0_steps_imp_stack_word:
  assumes "c0 \<turnstile>P* (q # qs, w)" "q \<in> dfa.states LR\<^sub>0"
  obtains \<alpha> where "\<alpha> \<Turnstile> c0 \<turnstile>P* (q # qs, w)"
  using assms proof (induction "(q # qs, w)" arbitrary: thesis q qs w)
  case (step c1)
  note that = step.prems
  note IH = step.hyps(3)
  from step(2) show ?case proof cases
    case (shift p ps a v)
    with step obtain \<alpha> where sw: "\<alpha> \<Turnstile> c0 \<turnstile>P* ([] @ p # ps, a # w)" 
      by auto
    note step_unfolded = step[unfolded shift]
    from sw have "Tm a # \<alpha> \<Turnstile> c0 \<turnstile>P* (q # qs, w)" unfolding shift
      by standard (use step_unfolded shift(2) in auto)
    then show ?thesis using that by simp
  next
    case (reduce p\<^sub>n ps p\<^sub>0 rs X \<alpha> v)
    from reduce(1,2) obtain ps' where c1_snoc: "c1 = (ps' @ p\<^sub>0 # rs, v)" 
      by (metis (no_types, lifting) append_Cons append_eq_append_conv2 list.distinct(1)
          snoc_eq_iff_butlast)
    with reduce step obtain \<alpha> where sw: "\<alpha> \<Turnstile> c0 \<turnstile>P* (ps' @ p\<^sub>0 # rs, v)" 
      by (metis list.set_intros(1) subset_code(1))
    note step_unfolded = step[unfolded reduce(3-) c1_snoc]
    from sw have "Nt X # drop (length ps') \<alpha> \<Turnstile> c0 \<turnstile>P* (q # qs, w)" unfolding reduce(3)
      by standard (use step_unfolded in simp_all)
    then show ?thesis using that by simp
  qed (use P0_final_item_notin_It in_state_imp_in_It that(2) in auto)
qed fast
      

lemma P0_hd_is_valids_of_stack_word:
  "\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (q # qs, v) \<Longrightarrow> 
    \<forall>n < length (q # qs). (q # qs) ! n  = valids (rev (drop n \<alpha>))"
proof (induction "([gpda.init P\<^sub>0], u)" "(q # qs, v)" arbitrary: q qs u v rule: stack_word.induct)
  case (sw_step \<alpha> ps q qs v X w)
  from sw_step(3) show ?case proof cases
    case (shift r rs a x)
    with sw_step have ih: "\<forall>n < length (r # rs). (r # rs) ! n = valids (rev (drop n \<alpha>))" by blast
    hence r_valids: "r = valids (rev \<alpha>)" by auto
    from shift have drop_eq: "drop (length ps) \<alpha> = \<alpha>" by simp
    from r_valids nxt_dfa_LR0_shift_is_valids_app shift(3) have 
      "dfa.nxt LR\<^sub>0 q X = valids (rev (X # \<alpha>))"  
      by (metis list.inject prod.inject rev.simps(2) shift(2))
    hence "(dfa.nxt LR\<^sub>0 q X # q # qs) ! 0 = valids (rev (drop 0 (X # \<alpha>)))"
      by simp
    moreover from ih have "\<forall>n < length (q # qs). (q # qs) ! n = valids (rev (drop (Suc n) (X # \<alpha>)))"
      using shift by auto
    ultimately show ?thesis unfolding drop_eq        
      by (smt (verit, ccfv_threshold) length_Suc_conv less_Suc_eq_0_disj nth_Cons_Suc)
  next
    case (reduce r\<^sub>n rs p\<^sub>0 ss Y \<beta> x)
    from reduce(2) sw_step(2)[of r\<^sub>n "rs @ ss"] have ih_qqs:
      "\<forall>n<length (q # qs). (q # qs) ! n = valids (rev (drop (length ps + n) \<alpha>))"
        by (simp add: append_eq_conv_conj)
    from reduce(1)[THEN last_of_Cons_idx_len_tl] have "p\<^sub>0 = (r\<^sub>n # rs @ ss) ! (length \<beta>)" 
      using reduce(6) by (metis append_Cons length_Cons lessI nth_append_left)
    with sw_step(2)[of r\<^sub>n "rs @ ss"] reduce(2,6) have p0_valids:
      "p\<^sub>0 = valids (rev (drop (length ps) \<alpha>))"
      by (metis add_Suc_right length_Cons length_append less_add_Suc1 list.inject nth_append_length
          prod.inject reduce(3))
    hence "dfa.nxt LR\<^sub>0 p\<^sub>0 X = valids (rev (X # drop (length ps) \<alpha>))"
      using nxt_dfa_LR0_shift_is_valids_app reduce 
      by (metis dfa_LR0.nextl_init_state nextl_dfa_LR0_is_valids rev.simps(2))
    hence "(dfa.nxt LR\<^sub>0 q X # q # qs) ! 0 = valids (rev (drop 0 (X # drop (length ps) \<alpha>)))"
      using reduce(3) by auto
    moreover from ih_qqs have 
      "\<forall>n<length (q # qs). (q # qs) ! n = valids (rev (drop (Suc n) (X # drop (length ps) \<alpha>)))" 
      by (simp add: add.commute)
    ultimately show ?thesis 
      by (smt (verit, ccfv_threshold) length_Suc_conv less_Suc_eq_0_disj nth_Cons_Suc)
  next
    case (finish q qs w)
    then show ?thesis using dfa_LR0_nxt_final_impossible_P0 
      by (metis P0.steps_init_imp_states insert_subset list.inject list.simps(15) prod.inject
          stack_word_imp_P0_steps sw_step.hyps(1))
  qed
qed (use init_P0_is_valids_empty valids_def in force)


lemma P0_invariant:
  "\<lbrakk>\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u @ v) \<turnstile>P* (q # qs, v); q \<noteq> {}\<rbrakk> \<Longrightarrow> Prods G' \<turnstile> rev \<alpha> \<Rightarrow>r* map Tm u"
proof (induction "([gpda.init P\<^sub>0], u @ v)" "(q # qs, v)" arbitrary: q qs u v rule: stack_word.induct)
  case (sw_step \<alpha> ps q qs w X v)
  with stack_word_imp_P0_steps P0.reachable_imp_substring obtain u' where w_app: "u @ v = u' @ w"
    by metis
  with sw_step have \<alpha>_derivers: "Prods G' \<turnstile> rev \<alpha> \<Rightarrow>r* map Tm u'" 
    by (smt (verit, ccfv_threshold) P0_step_cases empty_iff nxt_dfa_LR0_nempty_imp_ex_shift
        prod.inject)
  from sw_step(3) show ?case proof cases
    case (shift r rs a x)
    hence ps_Nil [simp]: "ps = []" and Xa [simp]: "X = Tm a" 
      using inj_nxt_dfa_LR0_if_nempty by blast+ 
    moreover from w_app shift have "u = u' @ [a]" by auto
    ultimately show ?thesis
      by (metis (no_types, lifting) \<alpha>_derivers derivers_append_map_Tm drop0 list.simps(8,9)
          list.size(3) map_append rev.simps(2)) 
  next
    case (reduce p\<^sub>n rs p\<^sub>0 ss Y \<beta> x)
    moreover from this obtain \<alpha>' where "\<alpha> = rev \<beta> @ \<alpha>'"
    proof -
      have "p\<^sub>n = (p\<^sub>n # rs @ ss) ! 0" by simp
      with P0_hd_is_valids_of_stack_word[of _ _ p\<^sub>n "rs @ ss"] reduce sw_step have 
        "reliable_prefix [Y \<rightarrow> \<beta> \<cdot> []] (rev \<alpha>)"
        by (metis drop0 length_greater_0_conv list.distinct(1) validD)
      then obtain \<alpha>' where "rev \<alpha> = \<alpha>' @ \<beta>"  
        by (blast elim: reliable_prefixE)
      thus thesis using that rev_eq_append_conv by blast
    qed
    moreover have "length ps = length rs" 
      by (cases rs rule: rev_cases) (use reduce in auto)
    ultimately have \<alpha>_app: "\<alpha> = rev \<beta> @ drop (length ps) \<alpha>" 
      by simp
    from reduce have Y_deriver: "Prods G' \<turnstile> [Nt Y] \<Rightarrow>r \<beta>" 
      using in_state_imp_in_It in_It_imp_in_Prods deriver_singleton by fastforce
    from reduce have XY: "X = Nt Y" using
        inj_nxt_dfa_LR0_if_nempty[OF _ _ sw_step(4), of "Nt Y"] last_in_set by blast
    with \<alpha>_app have "rev (X # drop (length ps) \<alpha>) = rev (drop (length ps) \<alpha>) @ [Nt Y]" 
      by simp
    also from Y_deriver have "Prods G' \<turnstile> rev (drop (length ps) \<alpha>) @ [Nt Y] 
      \<Rightarrow>r rev (drop (length ps) \<alpha>) @ \<beta>" by (simp add: deriver_singleton deriver_snoc_Nt)
    also have "... = rev \<alpha>" using \<alpha>_app 
      by (metis rev_append rev_rev_ident)
    also note \<alpha>_derivers
    finally show ?thesis using w_app reduce by fast
  next
    case (finish r rs x)
    moreover from sw_step(1) P0.steps_init_imp_states have "q \<in> gpda.states P\<^sub>0" 
      using stack_word_imp_P0_steps by (meson in_mono in_set_conv_decomp)
    ultimately show ?thesis using dfa_LR0_nxt_final_impossible_P0 by blast
  qed
qed simp

lemma P0_init_stack_word_length_inv:
  "\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (qs, v) \<Longrightarrow> Suc (length \<alpha>) = length qs"
  by (induction "([gpda.init P\<^sub>0], u)" "(qs, v)" arbitrary: qs v rule: stack_word.induct) auto


lemma P0_init_reaches_S'S_comp_imp_derivers:
  assumes "([gpda.init P\<^sub>0], w) \<turnstile>P* ([q, dfa.init LR\<^sub>0], [])"
    "q \<in> dfa.states LR\<^sub>0" "[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q"
  shows "Prods G' \<turnstile> [Nt S] \<Rightarrow>r* map Tm w"
using assms(1,2) proof (cases rule: P0_steps_imp_stack_word)
  case (1 \<alpha>)
  from P0_init_stack_word_length_inv[OF 1] obtain X where "\<alpha> = [X]" 
  proof -
    note P0_init_stack_word_length_inv[OF 1]
    hence "length \<alpha> = Suc 0" by simp
    then show thesis using that 
      by (metis Suc_length_conv length_0_conv)
  qed
  note stack_word = 1[unfolded this]
  then show ?thesis proof cases
    case (sw_step \<alpha> ps u)
    hence "X = Nt S" 
      by (metis S'_complete_reliable_imp_S assms(3) dfa_LR0.init dfa_LR0_init_reliable_Nil list.inject
          nxt_dfa_LR0_shift_is_valids_app self_append_conv2 state_imp_valids validD)
    with P0_invariant[of "[Nt S]" w "[]"] show ?thesis using stack_word assms(3) by auto
  qed
qed


lemma P0_Lang_subset_Lang_G:
  "P0.Lang \<subseteq> LangS G'"
proof
  fix w
  assume "w \<in> P0.Lang"
  hence "([gpda.init P\<^sub>0], w) \<turnstile>P* ([{[S' \<rightarrow> [] \<cdot> []]}], [])"
    unfolding P0.Lang_def by auto
  then obtain q where "([gpda.init P\<^sub>0], w) \<turnstile>P* ([q, dfa.init LR\<^sub>0], [])"
    "q \<in> dfa.states LR\<^sub>0" "[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q"
    by cases (use P0_init_not_final in force, use P0_final_step_is_finish in force)
  then show "w \<in> LangS G'" 
    using P0_init_reaches_S'S_comp_imp_derivers 
      G'_derives_from_S_imp_in_Lang derivers_imp_derives by blast
qed

theorem P0_Lang_eq_Lang_G:
  "P0.Lang = LangS G'"
proof
  show "P0.Lang \<subseteq> LangS G'"
    by (rule P0_Lang_subset_Lang_G)
  show "LangS G' \<subseteq> P0.Lang"
    sorry
qed

end
end
