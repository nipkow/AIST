theory LR_Parser 
  imports
    N_Pushdown_Automata
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
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> if a = Y \<and> (X, \<alpha>@Y#\<beta>) \<in> P then {[X \<rightarrow> \<alpha>@[Y] . \<beta>]} else {}| 
         _ \<Rightarrow> {}); 
      \<E> = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @Nt Y#\<beta>) \<in> P \<and> (Y, \<gamma>) \<in> P} in
    \<lparr>nfa.states = It G', nfa.init = {[S' \<rightarrow> [] . [Nt S]]}, nfa.final = completes (It G'), 
      nfa.nxt = \<Delta>, nfa.eps = \<E>\<rparr>"

subsection \<open>Basic Properties\<close>

lemma states_char_fa [simp]: 
  "nfa.states char_fa = It G'"
  unfolding char_fa_def by (meson nfa.select_convs(1))

lemma init_char_fa [simp]:
  "nfa.init char_fa = {[S' \<rightarrow> [] . [Nt S]]}"
  unfolding char_fa_def by (meson nfa.select_convs(2))

lemma final_char_fa [simp]:
  "nfa.final char_fa = completes (It G')"
  unfolding char_fa_def by (meson nfa.select_convs(3))

lemma nxt_char_fa [simp]:
  "nfa.nxt char_fa = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> if a = Y \<and> ((X, \<alpha> @ Y # \<beta>) \<in> Prods G') then {[X \<rightarrow> \<alpha> @ [Y] . \<beta>]} 
  else {} | _ \<Rightarrow> {})"
  unfolding char_fa_def by (meson nfa.select_convs(4))

lemma nxt_char_fa_neq_or_not_Prod_imp_empty:
  assumes "Y \<noteq> a \<or> (X, \<alpha> @ Y # \<beta>) \<notin> Prods G'"
  shows "nfa.nxt char_fa [X \<rightarrow> \<alpha> . Y # \<beta>] a = {}" 
  using assms by auto

lemma nxt_char_fa_in_Prods_imp_singleton:
  assumes "(X, \<alpha> @ Y # \<beta>) \<in> Prods G'"
  shows "nfa.nxt char_fa [X \<rightarrow> \<alpha> . Y # \<beta>] Y = {[X \<rightarrow> \<alpha> @ [Y] . \<beta>]}"
  using assms by simp

lemma nxt_char_fa_nempty_imp_hd:
  assumes "nfa.nxt char_fa [X \<rightarrow> \<alpha> . \<beta>] a \<noteq> {}" 
  obtains \<gamma> where "\<beta> = a # \<gamma>" "(X, \<alpha>@\<beta>) \<in> Prods G'"
  using assms 
  by (metis (lifting) nxt_char_fa_neq_or_not_Prod_imp_empty item.case list.exhaust list.simps(4)
      nxt_char_fa)

lemma in_nxt_char_fa_imp_shift:
  assumes "q \<in> nfa.nxt char_fa p a"
  obtains X \<alpha> \<beta> where "p = [X \<rightarrow> \<alpha> . a # \<beta>]" "q = [X \<rightarrow> \<alpha> @ [a] . \<beta>]"
proof -
  obtain X \<alpha> \<beta> Y \<gamma> \<delta> where pq_defs: "p = [X \<rightarrow> \<alpha> . \<beta>]" "q = [Y \<rightarrow> \<gamma> . \<delta>]" 
    using item.exhaust by meson
  moreover with nxt_char_fa_nempty_imp_hd assms obtain \<zeta> where "\<beta> = a # \<zeta>" "(X, \<alpha>@\<beta>) \<in> Prods G'" 
    by blast
  moreover with nxt_char_fa_in_Prods_imp_singleton have "q = [X \<rightarrow> \<alpha> @ [a] . \<zeta>]"
    using assms pq_defs(1) by blast
  ultimately show thesis using that by presburger
qed

lemma eps_char_fa [simp]:
  "nfa.eps char_fa 
    = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G' \<and> (Y, \<gamma>) \<in> Prods G'}"
  unfolding char_fa_def by (meson nfa.select_convs(5))

lemma eps_char_fa_subst_states:
  "nfa.eps char_fa \<subseteq> nfa.states char_fa \<times> nfa.states char_fa"
  using in_Prods_imp_in_It by force

lemma deriver_singleton_imp_eps:
  assumes "Prods G' \<turnstile> [Nt A] \<Rightarrow>r \<alpha>"
    "[X \<rightarrow> \<beta> . Nt A # \<gamma>] \<in> It G'"
  shows "([X \<rightarrow> \<beta> . Nt A # \<gamma>], [A \<rightarrow> [] . \<alpha>]) \<in> nfa.eps char_fa"
  unfolding eps_char_fa using assms deriver_singleton in_It_imp_in_Prods
  by fastforce

lemma prod_imp_eps:
  assumes "(A, \<alpha>) \<in> Prods G'"
    "[X \<rightarrow> \<beta> . Nt A # \<gamma>] \<in> It G'"
  shows "([X \<rightarrow> \<beta> . Nt A # \<gamma>], [A \<rightarrow> [] . \<alpha>]) \<in> nfa.eps char_fa"
  using deriver_singleton_imp_eps deriver_singleton assms by metis

sublocale char_fa: nfa char_fa 
proof (unfold_locales, goal_cases 1 2 nxt_closed 3)
  case 2
  then show ?case 
    using G'_def It_defs finite_It[OF G'_finite] completes_subset by force
next
  case (nxt_closed q x)
  then obtain X \<alpha> \<beta> where q_def: "q = [X \<rightarrow> \<alpha> . \<beta>]" by (metis item.exhaust)
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
  assumes "[X \<rightarrow> \<alpha> . Nt Y # \<beta>] \<in> It G'"
  obtains \<gamma> where "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) \<in> nfa.eps char_fa"
proof -
  from assms have X_prod: "(X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G'" using in_It_imp_in_Prods by fastforce
  with reduced_imp_prod_substring_derives_Tms[of X \<alpha> "[Nt Y]" \<beta>, OF _ G'_reduced] 
  obtain \<gamma> where "(Y, \<gamma>) \<in> Prods G'" by (metis derives_Nt_Cons_map_Tm append_Cons eq_Nil_appendI)
  with that X_prod show thesis unfolding eps_char_fa by blast
qed

lemma in_It_imp_eps_char_fa_distinct:
  assumes "[X \<rightarrow> \<alpha> . Nt Y # \<beta>] \<in> It G'"
  obtains \<gamma> where "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) \<in> nfa.eps char_fa" 
    "([X \<rightarrow> \<alpha> . Nt Y # \<beta>]) \<noteq> ([Y \<rightarrow> [] . \<gamma>])"
proof -
  from in_It_imp_eps_char_fa obtain \<gamma> where 
    \<gamma>_def: "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) \<in> nfa.eps char_fa"
    using assms by blast
  show thesis
  proof (cases "[X \<rightarrow> \<alpha> . Nt Y # \<beta>] = [Y \<rightarrow> [] . \<gamma>]")
    case True
    with reduced_imp_prod_distinct[OF _ G'_reduced] obtain \<gamma>' where "(Y, \<gamma>') \<in> Prods G'"
      "Nt Y \<notin> set \<gamma>'" using assms[THEN in_It_imp_in_Prods] by auto
    moreover with True have "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>']) \<in> nfa.eps char_fa"
      unfolding eps_char_fa using assms[THEN in_It_imp_in_Prods] by fastforce
    ultimately show ?thesis using that unfolding eps_char_fa by force
  qed (use that \<gamma>_def in presburger)
qed

lemma derivern_non_word_imp_hd_eps_reachable:
  assumes "Prods G' \<turnstile> [Nt A] \<Rightarrow>r(Suc n) Y # \<gamma>"
    "Nts_syms (Y # \<gamma>) \<noteq> {}"
  obtains \<alpha> X \<beta> where "[A \<rightarrow> [] . \<alpha>] \<in> It G'" 
    "([A \<rightarrow> [] . \<alpha>], [X \<rightarrow> [] . Y # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
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
    "[A \<rightarrow> [] . \<alpha>] \<in> It G'" "([A \<rightarrow> [] . \<alpha>], [W \<rightarrow> [] . X # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
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
    also from this have "([W \<rightarrow> [] . Nt X' # \<beta>], [X' \<rightarrow> [] . Y # \<zeta>]) \<in> nfa.eps char_fa"
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
  obtains X \<beta> where "([S' \<rightarrow> [] . [Nt S]], [X \<rightarrow> [] . Nt A # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
proof -
  from derivern_non_word_imp_hd_eps_reachable[OF assms] obtain 
    X \<beta> where "([S' \<rightarrow> [] . [Nt S]], [X \<rightarrow> [] . Nt A # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*" 
  proof -
    from derivern_non_word_imp_hd_eps_reachable[OF assms] obtain 
    X \<alpha> \<beta> where "([S' \<rightarrow> [] . \<alpha>], [X \<rightarrow> [] . Nt A # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*" 
      "[S' \<rightarrow> [] . \<alpha>] \<in> It G'" 
      by (metis all_not_in_conv in_Nts_syms list.set_intros(1))
    moreover from this have "\<alpha> = [Nt S]" using in_It_imp_in_Prods 
      using S'_derive_imp_S derive_singleton by fastforce
    ultimately show thesis using that by blast
  qed
  thus ?thesis using that by blast
qed 

lemma in_eps_S'_imp_left_Nil:
   "([S' \<rightarrow> [] . [Nt S]], [A \<rightarrow> \<alpha> . \<beta>]) \<in> (nfa.eps char_fa)\<^sup>* \<Longrightarrow> \<alpha> = []"
  by (induction "[A \<rightarrow> \<alpha> . \<beta>]" rule: rtrancl_induct) auto

lemma in_eps_S'_imp_produced:
  assumes "([S' \<rightarrow> [] . [Nt S]], [A \<rightarrow> \<alpha> . \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*"
  obtains w where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* Nt A # map Tm w"
  using assms proof (induction "[A \<rightarrow> \<alpha> . \<beta>]" arbitrary: A \<alpha> \<beta> thesis rule: rtrancl_induct)
  case base
  from this[of "[]"] show ?case by simp
next
  case (step i)
  hence Nil: "\<alpha> = []" by fastforce
  from step(2) obtain B \<delta> where i_def: "i = [B \<rightarrow> [] . Nt A # \<delta>]" using item.exhaust 
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
    X \<alpha> Y \<beta> \<gamma> where "c0 = ([X \<rightarrow> \<alpha> . Y # \<beta>], Y # \<gamma>)" "c1 = ([X \<rightarrow> \<alpha> @ [Y] . \<beta>], \<gamma>)" 
                      "(X, \<alpha> @ Y # \<beta>) \<in> Prods G'" |
    X \<alpha> Y \<beta> \<delta> \<gamma> where "c0 = ([X \<rightarrow> \<alpha> . Nt Y # \<beta>], \<delta>)" "c1 = ([Y \<rightarrow> [] . \<gamma>], \<delta>)" "(Y, \<gamma>) \<in> Prods G'"
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
  assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], \<delta>)"
  obtains \<zeta> where "\<gamma> = \<zeta> @ \<alpha> @ \<delta>"
  using assms proof (induction "([A \<rightarrow> \<alpha> . \<beta>], \<delta>)" arbitrary: A \<alpha> \<beta> \<delta> thesis rule: rtranclp_induct)
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
  assumes "([S' \<rightarrow> [] . [Nt S]], \<delta> @ \<alpha> @ [X]) \<turnstile>c* ([A \<rightarrow> \<alpha> @ [X] . \<gamma>], [])"
  shows "([S' \<rightarrow> [] . [Nt S]], \<delta> @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> . [X] @ \<gamma>], [])"
proof -
  from assms obtain n where n_steps: 
    "([S' \<rightarrow> [] . [Nt S]], \<delta> @ \<alpha> @ [X]) \<turnstile>c(n) ([A \<rightarrow> \<alpha> @ [X] . \<gamma>], [])"
    using rtranclp_imp_relpowp by fast
  show ?thesis
  proof (cases n)
    case (Suc m)
    then obtain i \<zeta> where m_steps: "([S' \<rightarrow> [] . [Nt S]], \<delta> @ \<alpha> @ [X]) \<turnstile>c(m) (i, \<zeta>)"
      "(i, \<zeta>) \<turnstile>c ([A \<rightarrow> \<alpha> @ [X] . \<gamma>], [])"
      using n_steps by auto
    from this(2) show ?thesis proof cases
      case (nxt Y \<alpha> Z \<beta> \<gamma>)
      then show ?thesis using m_steps char_fa.steps_append[of _ "\<delta> @ \<alpha>" "[X]" _ "[]"]
        by (simp add: relpowp_imp_rtranclp) 
    qed fast
  qed (use n_steps in simp)
qed

lemma char_steps_consume:
  "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G' \<Longrightarrow> ([A \<rightarrow> \<alpha> . \<beta> @ \<gamma>], \<beta> @ \<delta>) \<turnstile>c* ([A \<rightarrow> \<alpha> @ \<beta> . \<gamma>], \<delta>)"
proof (induction \<beta> arbitrary: \<alpha>)
  case (Cons X \<beta>)
  hence "([A \<rightarrow> \<alpha> . (X # \<beta>) @ \<gamma>], (X # \<beta>) @ \<delta>) \<turnstile>c ([A \<rightarrow> \<alpha> @ [X] . \<beta> @ \<gamma>], \<beta> @ \<delta>)" by auto
  also from Cons.IH[of "\<alpha> @ [X]"] have "... \<turnstile>c* ([A \<rightarrow> \<alpha> @ X # \<beta> . \<gamma>], \<delta>)" 
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
  assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
  obtains \<gamma>' w where 
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w"
    "\<gamma> = \<gamma>' @ \<alpha>"
proof -
  from assms obtain n where "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c(n) ([A \<rightarrow> \<alpha> . \<beta>], [])"
    using rtranclp_imp_relpowp by fast
  with that show thesis
  proof (induction n arbitrary: \<gamma> A \<alpha> \<beta> thesis)
    case 0
    then show ?case using 0(1)[of "[]" "[]"] G'_derive_S 
      by (simp add: G'_def deriver_singleton)
  next
    case (Suc n)
    then obtain c where n_steps: "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c(n) c" "c \<turnstile>c ([A \<rightarrow> \<alpha> . \<beta>], [])" 
      by auto
    from this(2) show ?case 
    proof cases
      case (nxt X \<alpha>' Y \<beta>' \<gamma>')
      moreover with n_steps obtain \<delta> where \<delta>_def: "\<gamma> = \<delta> @ \<alpha>' @ [Y]" 
        using char_reachable_imp_substring[of \<gamma> X \<alpha>' "Y # \<beta>'" "[Y]"] relpowp_imp_rtranclp 
        by (metis prod.inject)
      ultimately have "([S' \<rightarrow> [] . [Nt S]], \<delta> @ \<alpha>') \<turnstile>c(n) ([X \<rightarrow> \<alpha>' . Y # \<beta>'], [])"
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
    "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], v@w) \<turnstile>I* ([I.final_state, init_symbol IPDA], [])" 
    "hist \<rho> = \<gamma>"
  using assms(1) proof cases
  case rtrancl_refl
  with assms have eqs: "\<gamma> = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S]" 
    using S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
  then show thesis using S'_derive_imp_S I.deriver_imp_IPDA_comp assms that 
    by (metis I.hist_init I.init_symbol_ipda append.right_neutral append_Nil hist_singleton list.inject
        rtrancl_refl sym.inject(1))
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
    by (metis I.hist_init I.init_symbol_ipda append.right_neutral append_Nil hist_singleton
        list.simps(8))
  next
    case (Cons i \<rho>)
    then obtain X \<alpha>' \<beta>' where X_defs:
      "i = [X \<rightarrow> \<alpha>' . Nt A # \<beta>']" 
      using rm_chain_imp_hd_prod_rightmost[OF Cons(2)]
      by (metis list.distinct(1) list.inject)
    with rm_chain_stepE Cons(2) obtain \<alpha>'' u v' where X_chain:
      "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha>'' @ Nt X # map Tm v'"
      "Prods G' \<turnstile> \<alpha>'' @ Nt X # map Tm v' \<Rightarrow>r \<alpha>'' @ \<alpha>' @ Nt A # \<beta>' @ map Tm v'"
      "Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm u" "u @ v' = w" "\<alpha>'' @ \<alpha>' = \<gamma>"
      by (smt (verit, best) append.assoc map_append rm_eq_imp_eq)
    then obtain \<rho>' where \<rho>'_def:
      "([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho>' @ [init_symbol IPDA], u@v') 
          \<turnstile>I* ([I.final_state, init_symbol IPDA], [])"
      "hist \<rho>' = \<alpha>''" 
      using Cons(1)[OF X_chain(1) rm_chain_imp_derivers[OF X_chain(1)], of "\<alpha>' @ [Nt A]" \<beta>']
      by (metis append.assoc append_Cons append_Nil derivers_imp_derives)
    from X_defs have X_in_prods: "(X, \<alpha>' @ Nt A # \<beta>') \<in> Prods G'"
      by (metis Cons.prems(1) rm_chain_imp_prod)
    let ?\<rho> = "[X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<rho>'"
    have hist_\<rho>: "hist ?\<rho> = \<gamma>" using X_chain(5) \<rho>'_def(2) by simp
    from Cons(4) have A_in_prods: "(A, \<alpha> @ \<beta>) \<in> Prods G'" 
      by (simp add: deriver_imp_in_Prods)
    with I.derives_imp_completes[OF Cons(5)] have 
      "([A \<rightarrow> \<alpha> . \<beta>] # ?\<rho> @ [init_symbol IPDA], v @ w) \<turnstile>I* ([A \<rightarrow> \<alpha>@\<beta> . []] # ?\<rho> @ [init_symbol IPDA], w)"
      by (metis append.right_neutral)
    also have "... \<turnstile>I ([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho>' @ [init_symbol IPDA], u@v')"
      using X_chain(4) A_in_prods X_in_prods by simp
    also have "... \<turnstile>I* ([I.final_state, init_symbol IPDA], [])" using \<rho>'_def by presburger
    finally show ?case using hist_\<rho> Cons(6) by presburger
  qed
qed 

text \<open>Towards step 3\<close>

lemma ipda_reaches_final_imp_rm_chain:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>I* ([I.final_state, init_symbol IPDA], [])"
  obtains "\<rho> = []" |
    \<sigma> X \<alpha>' \<beta>' \<gamma> where "\<rho> = [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<sigma>" "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  using assms proof (induction "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w)" arbitrary: A \<alpha> \<beta> \<rho> w thesis
                      rule: converse_rtranclp_induct)
  case (step z)
  from I.step_imp_in_It this(1) have A_in_It: "[A \<rightarrow> \<alpha> . \<beta>] \<in> It G'" 
    using I.step_imp_not_Nil by (smt (verit, ccfv_SIG) I.step_cases)
  from I.step_app_init_symbol_preserved step(1) obtain B \<gamma> \<delta> \<tau> v where z\<tau>_def:
    "z = ([B \<rightarrow> \<gamma> . \<delta>] # \<tau> @ [init_symbol IPDA], v)" using prod.exhaust by metis
  note step(3)[OF this] 
  then show thesis
  proof (cases, goal_cases Nil chain)
    case Nil
    with z\<tau>_def have z_B_init: "z = ([[B \<rightarrow> \<gamma> . \<delta>], init_symbol IPDA], v)" by blast
    with step(2) I.reaches_without_stack_imp_S' consider 
      "[B \<rightarrow> \<gamma> . \<delta>] = init_state IPDA" |
      "[B \<rightarrow> \<gamma> . \<delta>] = I.final_state" by blast
    then show thesis
    proof cases
      case 2
      note step(1)[unfolded z_B_init this] 
      note I.step_reaches_final_imp_S[OF this]
      then show ?thesis using step(5) G'_derive_S derive_singleton_imp_singleton_chain by force
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
      case (expand Y \<eta> X' \<theta> \<iota> i \<upsilon> x)
      show ?thesis
      proof (cases \<rho>)
        case (Cons j \<xi>)
        from Cons expand have "\<tau> = [A \<rightarrow> \<theta> . Nt B # \<iota>] # i # \<xi>" by auto
        from rm_chain_second_produces_hd[OF chain(2)[unfolded this]] obtain Z \<gamma>' \<delta>' where
          "\<rho> = [Z \<rightarrow> \<gamma>' . Nt A # \<delta>'] # \<xi>" using Cons expand by auto
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
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>I* ([I.final_state, init_symbol IPDA], [])"
  shows "([S' \<rightarrow> [] . [Nt S]], hist \<rho> @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
using assms proof (induction \<rho> arbitrary: A \<alpha> \<beta> w)
  case Nil
  with I.reaches_without_stack_imp_S' consider (init) "[A \<rightarrow> \<alpha> . \<beta>] = [S' \<rightarrow> [] . [Nt S]]" | 
    (final) "[A \<rightarrow> \<alpha> . \<beta>] = [S' \<rightarrow> [Nt S] . []]" by auto
  then show ?case 
    by cases (metis hist_Cons hist_singleton history_unfold rtranclp.rtrancl_refl,
    use G'_def char_fa.step.simps hist_singleton in auto)
next
  case (Cons i \<rho>)
  with ipda_reaches_final_imp_rm_chain obtain X \<alpha>' \<beta>' \<gamma> where chain:
    "i = [X \<rightarrow> \<alpha>' . Nt A # \<beta>']" "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* i # \<rho> \<Rightarrow>r* \<gamma>" by blast
  hence X_in_Prods: "(X, \<alpha>' @ Nt A # \<beta>') \<in> Prods G'" 
    by (simp add: rm_chain_imp_prod)
  from I.reaches_final_imp_completes[OF Cons(2)] obtain v where A_complete:
    "([A \<rightarrow> \<alpha> . \<beta>] # (i # \<rho>) @ [init_symbol IPDA], w) 
      \<turnstile>I* ([A \<rightarrow> \<alpha> @ \<beta> . []] # (i # \<rho>) @ [init_symbol IPDA], v)"
    "([A \<rightarrow> \<alpha> @ \<beta> . []] # (i # \<rho>) @ [init_symbol IPDA], v) 
      \<turnstile>I* ([I.final_state, init_symbol IPDA], [])" by blast
  have A_in_Prods: "(A, \<alpha>@\<beta>) \<in> Prods G'"
    using I.steps_neq_in_It[OF A_complete(2)] in_Prods_iff_in_It by force
  have "([A \<rightarrow> \<alpha> @ \<beta> . []] # (i # \<rho>) @ [init_symbol IPDA], v)
       \<turnstile>I ([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho> @ [init_symbol IPDA], v)"
    using chain A_in_Prods X_in_Prods by auto
  with I.step_not_expanding_imp_reaches[OF this] A_complete have 
    "... \<turnstile>I* ([I.final_state, init_symbol IPDA], [])" 
    by (metis (no_types, lifting) I.complete_S'_step_impossible I.step_not_expanding_unique
        converse_rtranclpE list.sel(1))
  note X_comp = Cons.IH[OF this]
  hence "([S' \<rightarrow> [] . [Nt S]], hist \<rho> @ \<alpha>') \<turnstile>c* ([X \<rightarrow> \<alpha>' . Nt A # \<beta>'], [])"
    using char_consumes_last_imp_butlast_reaches by fastforce
  hence "([S' \<rightarrow> [] . [Nt S]], hist (i # \<rho>) @ \<alpha>) \<turnstile>c* ([X \<rightarrow> \<alpha>' . Nt A # \<beta>'], \<alpha>)"
    using char_fa.steps_append[of _ "hist (i # \<rho>)" "[]" _ \<alpha>] chain by simp
  also have "... \<turnstile>c ([A \<rightarrow> [] . \<alpha> @ \<beta>], \<alpha>)" 
    using A_in_Prods X_in_Prods by force
  also from this have "... \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])" 
    using char_steps_consume char_step_imp_in_Prods 
    by (metis append.right_neutral item.case self_append_conv2)
  finally show ?case .
qed

corollary derivers_imp_char:
  assumes
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w"
  shows "([S' \<rightarrow> [] . [Nt S]], \<gamma>' @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
proof -
  note rtranclp.rtrancl_into_rtrancl[OF assms]
  with reduced_derives_imp_substring_derives_Tms obtain v where
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v" 
    using G'_reduced G'_not_empty G'_def derivers_imp_derives by (metis Cfg.sel(2) append.assoc)
  from derivers_imp_ipda[OF assms this] ipda_imp_char show ?thesis by metis
qed

text \<open>\<open>\<gamma>\<close> is a reliable prefix to \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> (or equivalently, \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> is valid for \<open>\<gamma>\<close>) 
      if there exists a rightmost derivation \<open>S' \<Rightarrow>r* \<gamma>'Aw \<Rightarrow>r \<gamma>'\<alpha>\<beta>w\<close> with \<open>\<gamma> = \<gamma>'\<alpha>\<close>:\<close>

inductive reliable_prefix :: "('n, 't) item \<Rightarrow> ('n, 't) syms \<Rightarrow> bool" where
  "\<lbrakk>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w;  
    Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<rbrakk> 
    \<Longrightarrow> reliable_prefix [A \<rightarrow> \<alpha> . \<beta>] (\<gamma>' @ \<alpha>)"

inductive_cases reliable_prefixE: "reliable_prefix [A \<rightarrow> \<alpha> . \<beta>] \<gamma>"

lemma reliable_prefixI [intro]:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma> @ \<beta> @ map Tm w" "\<gamma> = \<gamma>' @ \<alpha>"
  shows "reliable_prefix [A \<rightarrow> \<alpha> . \<beta>] \<gamma>"
  using assms reliable_prefix.intros by auto

text \<open>The words on which \<open>char(G)\<close> reaches \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> are exactly the reliable 
     prefixes for \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close>:\<close>

theorem char_eq_reliable_prefix:
  "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], []) = reliable_prefix [A \<rightarrow> \<alpha> . \<beta>] \<gamma>"
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
  "reliable_prefix [S' \<rightarrow> [] . [Nt S]] []"
  using char_eq_reliable_prefix by fast

lemma char_fa_nextl_is_valids:
  "nfa.nextl char_fa (nfa.init char_fa) w = {i. reliable_prefix i w}"
proof -
  have "{i. reliable_prefix i w} = {i. ([S' \<rightarrow> [] . [Nt S]], w) \<turnstile>c* (i, [])}"
    using char_eq_reliable_prefix by (metis item.exhaust)
  also have "... = nfa.nextl char_fa (nfa.init char_fa) w"
    using char_fa.eps_subst_states_imp_nextl_eq_reachable[OF eps_char_fa_subst_states]
    by auto
  finally show ?thesis by order
qed

lemma derivern_Suc_imp_reliable:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm w"
  obtains A \<alpha>' \<beta> v where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha>' @ Nt A # map Tm v"
    "Prods G' \<turnstile> \<alpha>' @ Nt A # map Tm v \<Rightarrow>r \<alpha> @ \<beta> @ map Tm v"
    "Prods G' \<turnstile> \<alpha> @ \<beta> @ map Tm v \<Rightarrow>r* \<alpha> @ Nt X # map Tm w"
proof -
  from assms obtain A \<alpha>'' \<beta> \<rho> where 
    "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* [A \<rightarrow> \<alpha>'' . Nt X # \<beta>] # \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm w"
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
  obtains A \<alpha>' Y \<beta>' w' where "reliable_prefix [A \<rightarrow> \<alpha>' . Y # \<beta>'] \<alpha>"
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
      hence eqs [simp]: "\<alpha>' @ \<alpha>'' = \<alpha> @ \<beta> \<and> Y = X \<and> u @ v = w"
        by (metis Cons.prems(2) append.assoc append_eq_map_conv hist_Cons history_unfold list.inject
            map_Tm_inject_iff rm_chain_singleton_left_is_hist same_append_eq sym.inject(1))
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
          by (metis append_eq_append_conv2)
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
          with rm_chain_imp_derivers[OF i_step(3)] have 1: "reliable_prefix [A \<rightarrow> \<gamma> . \<beta> @ Nt X # \<beta>'] \<alpha>"
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
  obtains A \<alpha>' \<gamma> Y \<beta>' w' where "reliable_prefix [A \<rightarrow> \<alpha>' . Y # \<beta>'] \<alpha>" 
proof -
  from assms obtain n where derivern: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(n) \<alpha> @ \<beta> @ Nt X # map Tm w"
    using rtranclp_imp_relpowp by fast
  then show thesis proof (cases n)
  case 0
  have "reliable_prefix ([S' \<rightarrow> [] . [Nt S]]) []" 
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
  obtains \<delta>\<^sub>1 \<delta>\<^sub>2 where "reliable_prefix [Y \<rightarrow> \<delta>\<^sub>1 . \<delta>\<^sub>2] (\<alpha> @ \<beta>)" "\<gamma> @ \<delta>\<^sub>1 = \<alpha> @ \<beta>" "\<delta>\<^sub>1 @ \<delta>\<^sub>2 = \<delta>" | 
    A \<zeta> B \<eta> where "reliable_prefix [A \<rightarrow> \<zeta> . B # \<eta>] (\<alpha> @ \<beta>)" 
proof -
  from assms(3) have "\<gamma> @ \<delta> = \<alpha> @ \<beta> @ map Tm y'" by simp
  thus thesis 
  proof (cases rule: app_eq_rm_cases)
    case (1 u v)
    then show ?thesis using assms derivers_substring_reliable that(2) 
      by (metis append_assoc)
  next
    case (2 \<delta>')
    from assms(1) have "reliable_prefix [Y \<rightarrow> \<delta>' . map Tm y'] (\<alpha> @ \<beta>)"
      using "2"(1,2) assms(2) reliable_prefix.intros by fastforce
    then show ?thesis using that(1) 2 by blast
  qed
qed



lemma in_states_imp_valid:
  assumes "[X \<rightarrow> \<alpha> . \<beta>] \<in> nfa.states char_fa"
  obtains \<gamma> where "reliable_prefix [X \<rightarrow> \<alpha> . \<beta>] \<gamma>"
proof -
  from assms have prod: "(X, \<alpha>@\<beta>) \<in> Prods G'"
    using in_It_imp_in_Prods by fastforce
  then obtain \<gamma> w where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt X # map Tm w"
    using reduced_in_Prods_imp_rsentential_reachable[OF G'_reduced G'_not_empty]
    by (metis Cfg.sel(2) G'_def)
  hence "reliable_prefix [X \<rightarrow> \<alpha> . \<beta>] (\<gamma> @ \<alpha>)"
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


lemma dfa_LR0_state_imp_char_fa_Power_state [dest]:
  "q \<in> dfa.states LR\<^sub>0 \<Longrightarrow> q \<in> dfa.states char_fa.Power_dfa"
  using char_fa.dfa_Power dfa.accessible_imp_states by fastforce 

lemma dfa_LR0_nxt_eq_char_fa_Power_nxt [simp]:
  "dfa.nxt LR\<^sub>0 = dfa.nxt char_fa.Power_dfa"
  unfolding LR\<^sub>0_def using char_fa.dfa_Power dfa.nxt_Accessible_dfa by metis

lemma dfa_LR0_nextl_eq_char_fa_Power_nextl [simp]:
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

lemma nxt_LR0_eq_intersect:
  "dfa.nxt LR\<^sub>0 Q a = dfa.nxt LR\<^sub>0 (Q \<inter> It G') a"
  unfolding LR\<^sub>0_def by (simp add: char_fa.dfa_Power dfa.nxt_Accessible_dfa)

lemma finite_dfa_LR0_nempty_syms:
  "finite {a. dfa.nxt LR\<^sub>0 q a \<noteq> {}}"
proof -
  have "{a. dfa.nxt LR\<^sub>0 q a \<noteq> {}} = {a. dfa.nxt LR\<^sub>0 (q \<inter> It G') a \<noteq> {}}"
    using nxt_LR0_eq_intersect by presburger
  moreover have "... \<subseteq> (\<lambda>i. case i of [X \<rightarrow> \<alpha> . Y # \<beta>] \<Rightarrow> Y) ` char_fa.epsclo (q \<inter> It G')"
    (is "?A \<subseteq> ?f ` ?Q'")
  proof 
    fix a
    assume "a \<in> ?A"
    then obtain p where "p \<in> ?Q'" "nfa.nxt char_fa p a \<noteq> {}"
      by fastforce
    moreover with nxt_char_fa_nempty_imp_hd obtain X \<alpha> \<beta> where "p = [X \<rightarrow> \<alpha> . a # \<beta>]"
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
  "dfa.nextl LR\<^sub>0 (dfa.init LR\<^sub>0) \<gamma> = {i. reliable_prefix i \<gamma>}"
  using LR\<^sub>0_def char_fa.Power_nextl_eq_nfa_nextl char_fa_nextl_is_valids 
   dfa_LR0_nextl_eq_char_fa_Power_nextl by presburger

lemma state_imp_valids:
  "p \<in> dfa.states LR\<^sub>0 \<Longrightarrow> \<exists>\<gamma>. p = {i. reliable_prefix i \<gamma>}"
  using nextl_dfa_LR0_is_valids dfa.path_to_left_lang[OF char_fa.dfa_Power]
    dfa.nextl_path_to[OF char_fa.dfa_Power] by fastforce

section \<open>The Canonical LR(0) Parser\<close>

definition P\<^sub>0 :: "(('n, 't) item set, 't) npda" where
  "P\<^sub>0 \<equiv> let 
  \<Delta>\<^sub>G = dfa.nxt LR\<^sub>0;
  q\<^sub>0 = dfa.init LR\<^sub>0;
  Q = dfa.states LR\<^sub>0;
  f = {[S' \<rightarrow> [] . []]};
  \<Delta>\<^sub>0 = {([q], a, \<Delta>\<^sub>G q (Tm a) # [q])|q a. q \<in> dfa.states LR\<^sub>0 \<and> \<Delta>\<^sub>G q (Tm a) \<noteq> {}};
  \<E> = {let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, \<Delta>\<^sub>G q (Nt X) # [q])| 
       q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> Q \<and> [X \<rightarrow> \<alpha> . []] \<in> q\<^sub>n \<and> length \<alpha> = length qs} \<union>
      {([q, q\<^sub>0], [f])|q. q \<in> Q \<and> [S' \<rightarrow> [Nt S] . []] \<in> q}
 in \<lparr>npda.states = Q \<union> {f}, init = q\<^sub>0, final = {f}, nxt = \<Delta>\<^sub>0, eps = \<E>\<rparr>"

lemma states_P0: 
  "npda.states P\<^sub>0 = dfa.states LR\<^sub>0 \<union> {{[S' \<rightarrow> [] . []]}}"
  unfolding P\<^sub>0_def by (meson npda.select_convs(1))

lemma init_P0: 
  "npda.init P\<^sub>0 = dfa.init LR\<^sub>0"
  unfolding P\<^sub>0_def by (meson npda.select_convs(2))

abbreviation "P0_final \<equiv> {[S' \<rightarrow> [] . []]}"

lemma final_P0:
  "npda.final P\<^sub>0 = {P0_final}"
  unfolding P\<^sub>0_def by (meson npda.select_convs(3))

lemma nxt_P0:
  "npda.nxt P\<^sub>0 = 
    {([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q])|q a. q \<in> dfa.states LR\<^sub>0 \<and> dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}}"
  unfolding P\<^sub>0_def by (meson npda.select_convs(4))

lemma eps_P0:
  "npda.eps P\<^sub>0 = 
  {let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, dfa.nxt LR\<^sub>0 q (Nt X) # [q])|
    q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> . []] \<in> q\<^sub>n \<and> length \<alpha> = length qs} \<union>
  {([q, dfa.init LR\<^sub>0], [P0_final])|q. q \<in> dfa.states LR\<^sub>0 \<and> [S' \<rightarrow> [Nt S] . []] \<in> q}"
  unfolding P\<^sub>0_def by (meson npda.select_convs(5))

lemmas P\<^sub>0_simps [simp] = states_P0 init_P0 final_P0 nxt_P0 eps_P0

lemma nxt_P0_nempty_imp_nxt_LR0_set:
  assumes "(qs, a, qs') \<in> npda.nxt P\<^sub>0"
  obtains q where "qs = [q]" "qs' = dfa.nxt LR\<^sub>0 q (Tm a) # [q]"
    "q \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}"
  using assms by auto

lemma finite_lists_complete_length_eq:
  "finite {q # qs| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> . []] \<in> q \<and> 
            length \<alpha> = length qs}"
  (is "finite ?L")
proof (rule finite_surj)
  show "?L \<subseteq> (\<lambda>(q, qs, X, \<alpha>). q # qs) ` {(q, qs, X, \<alpha>)| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 
    \<and> [X \<rightarrow> \<alpha> . []] \<in> q \<and> length \<alpha> = length qs}" (is "_ \<subseteq> ?f ` ?F") 
  proof
    fix x
    assume "x \<in> ?L"
    then obtain q qs X \<alpha> where x_defs: "x = q # qs" "set (q # qs) \<subseteq> dfa.states LR\<^sub>0" 
      "[X \<rightarrow> \<alpha> . []] \<in> q" "length \<alpha> = length qs" by blast
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
        "[X \<rightarrow> \<alpha> . []] \<in> q" "length \<alpha> = length qs" by blast
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
    q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> . []] \<in> q\<^sub>n \<and> length \<alpha> = length qs}"
  (is "finite ?R")
proof (rule finite_subset)
  show "?R \<subseteq> {q # qs| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> . []] \<in> q 
                \<and> length \<alpha> = length qs} \<times> {[p, q]|p q. p \<in> dfa.states LR\<^sub>0 \<and> q \<in> dfa.states LR\<^sub>0}"
  (is "_ \<subseteq> ?L \<times> ?T")
  proof
    fix e
    assume "e \<in> ?R"
    then obtain q\<^sub>n qs q X \<alpha> where e_defs: 
      "q = last (q\<^sub>n#qs)" "e = (q\<^sub>n # qs, dfa.nxt LR\<^sub>0 q (Nt X) # [q])"
      "set (q\<^sub>n#qs) \<subseteq> dfa.states LR\<^sub>0" "[X \<rightarrow> \<alpha> . []] \<in> q\<^sub>n" "length \<alpha> = length qs"
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
  "finite {([q, dfa.init LR\<^sub>0], [P0_final])|q. q \<in> dfa.states LR\<^sub>0 \<and> [S' \<rightarrow> [Nt S] . []] \<in> q}"
  (is "finite ?F")
proof (rule finite_surj)
  show "?F \<subseteq> (\<lambda>q. ([q, dfa.init LR\<^sub>0], [P0_final])) ` dfa.states LR\<^sub>0"
    by blast
qed (rule dfa_LR0.finite)

lemma eps_P0_cases[consumes 1, case_names reduce finish]:
  assumes "(ps, qs) \<in> npda.eps P\<^sub>0"
  obtains r rs X \<alpha> where 
    "ps = r # rs" "qs = (let q = last (r # rs) in dfa.nxt LR\<^sub>0 q (Nt X) # [q])"
    "set (r # rs) \<subseteq> dfa.states LR\<^sub>0" "[X \<rightarrow> \<alpha> . []] \<in> r" "length \<alpha> = length rs" |
    q where "q \<in> dfa.states LR\<^sub>0" "ps = [q, dfa.init LR\<^sub>0]" "qs = [P0_final]"
  using assms unfolding eps_P0 by standard (smt (verit, best) mem_Collect_eq prod.inject)+

interpretation P0: npda P\<^sub>0
proof (unfold_locales, goal_cases _ _ nxt eps _ finite_nxt finite_eps)
  case (nxt ps a qs)
  with nxt_P0_nempty_imp_nxt_LR0_set obtain p where "ps = [p]"
  "p \<in> dfa.states LR\<^sub>0" "qs = [dfa.nxt LR\<^sub>0 p (Tm a), p]" "dfa.nxt LR\<^sub>0 p (Tm a) \<noteq> {}"
    by force
  with dfa_LR0.nxt show ?case by simp
next
  case (eps ps qs)
  then show ?case 
  proof (cases rule: eps_P0_cases, intro conjI)
    case (reduce r rs X \<alpha>)
    then show "qs \<noteq> []" "set ps \<subseteq> npda.states P\<^sub>0" and ps_Cons: "ps \<noteq> []"
      by (metis list.distinct(1), auto)
    from reduce(3) have "dfa.nxt LR\<^sub>0 (last (r # rs)) (Nt X) \<in> dfa.states LR\<^sub>0"
      using dfa_LR0.nxt last_in_set by blast
    with reduce(1-3) ps_Cons show "set qs \<subseteq> npda.states P\<^sub>0" 
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
  moreover have "bij_betw (\<lambda>(q, a). ([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q])) ?R (npda.nxt P\<^sub>0)"
    (is "bij_betw ?f _ _")
  proof -
    have "inj_on ?f ?R" by standard auto
  moreover have "?f ` ?R = (npda.nxt P\<^sub>0)" unfolding nxt_P0 by fastforce
  ultimately show ?thesis unfolding bij_betw_def by satx
  qed
  ultimately show ?case using bij_betw_finite by blast
next
  case finite_eps
  then show ?case using finite_eps_P0_reduce finite_eps_P0_finish by simp
qed (use dfa_LR0.init dfa_LR0.finite in simp_all)

lemma P0_read_iff_in_q:
"([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q]) \<in> npda.nxt P\<^sub>0 
  = (\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> . Tm a # \<beta>] \<in> q \<and> q \<in> dfa.states LR\<^sub>0)"
proof 
  assume "([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q]) \<in> npda.nxt P\<^sub>0"
  with nxt_P0 have q_nxt: "q \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}" by auto
  with char_fa.nxt_Power_dfa obtain i where i_defs:
    "i \<in> char_fa.epsclo q" "char_fa.epsclo (nfa.nxt char_fa i (Tm a)) \<noteq> {}"
      by fastforce
  hence "nfa.nxt char_fa i (Tm a) \<noteq> {}" by fastforce
  with nxt_char_fa obtain X \<alpha> \<beta> where "i = [X \<rightarrow> \<alpha> . Tm a # \<beta>]" 
    by (meson all_not_in_conv in_nxt_char_fa_imp_shift)
  then show "\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> . Tm a # \<beta>] \<in> q \<and> q \<in> dfa.states LR\<^sub>0" 
    using i_defs in_states_imp_epsclo_eq[OF q_nxt(1)] q_nxt(1) by blast
next 
  assume "\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> . Tm a # \<beta>] \<in> q \<and> q \<in> dfa.states LR\<^sub>0"
  hence ex: "\<exists>X \<alpha> \<beta>. [X \<rightarrow> \<alpha> . Tm a # \<beta>] \<in> q" and q_state: "q \<in> dfa.states LR\<^sub>0" 
    "q \<in> dfa.states char_fa.Power_dfa" by fastforce+
  then obtain X \<alpha> \<beta> where X_q: "[X \<rightarrow> \<alpha> . Tm a # \<beta>] \<in> q" (is "?i \<in> _") by blast
  then have X_epsclo: "?i \<in> char_fa.epsclo q"
    using char_fa.epsclo_increasing q_state by fastforce
  from X_q q_state have "(X, \<alpha> @ Tm a # \<beta>) \<in> Prods G'" using in_state_imp_in_It in_It_imp_in_Prods
    by (metis item.case)
  hence "nfa.nxt char_fa ?i (Tm a) \<noteq> {}" unfolding nxt_char_fa by simp
  moreover from X_q have "?i \<in> nfa.states char_fa" using in_state_imp_in_It q_state by simp
  ultimately have "char_fa.epsclo (nfa.nxt char_fa [X \<rightarrow> \<alpha> . Tm a # \<beta>] (Tm a)) \<noteq> {}" 
    using char_fa.epsclo_increasing char_fa.nxt by fast
  hence "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}" using X_epsclo by fastforce
  thus "([q], a, dfa.nxt LR\<^sub>0 q (Tm a) # [q]) \<in> npda.nxt P\<^sub>0" using nxt_P0 q_state by blast
qed

lemma P0_complete_imp_reduce:
  assumes "[X \<rightarrow> \<alpha> . []] \<in> q"
    "q \<in> dfa.states LR\<^sub>0"
  obtains qs where "(q#qs, [dfa.nxt LR\<^sub>0 (last (q#qs)) (Nt X), last (q#qs)]) \<in> npda.eps P\<^sub>0"
    "length qs = length \<alpha>"
proof -
  obtain qs where "set qs \<subseteq> dfa.states LR\<^sub>0" "length qs = length \<alpha>"
    using list_of_subset[of "dfa.states LR\<^sub>0" "length \<alpha>"] assms(2) by blast
  moreover then have "set (q#qs) \<subseteq> dfa.states LR\<^sub>0"
    using assms(2) by auto
  ultimately show thesis using that unfolding eps_P0 
    by (smt (verit, ccfv_threshold) Un_iff assms(1) mem_Collect_eq)
qed

notation P0.step (infix \<open>\<turnstile>P\<close> 55)
notation P0.steps (infix \<open>\<turnstile>P*\<close> 55)
notation P0.stepn (\<open>_ \<turnstile>P'(_') _\<close> 55)

section \<open>LR(0)-Adequate and Inadequate States\<close>

inductive shift_reduce :: "('n, 't) item set \<Rightarrow> bool" where
  "\<lbrakk>([p], a, ps) \<in> npda.nxt P\<^sub>0; (p#ps', qs) \<in> npda.eps P\<^sub>0\<rbrakk> \<Longrightarrow> shift_reduce p"

lemma shift_reduceE [elim]:
  assumes "shift_reduce q"
  obtains X \<alpha> a \<beta> Y \<gamma> where "[X \<rightarrow> \<alpha> . Tm a # \<beta>] \<in> q" "[Y \<rightarrow> \<gamma> . []] \<in> q"
  using assms shift_reduce.cases 
  by (smt (verit, ccfv_threshold) Extended_Cfg.P0_read_iff_in_q Extended_Cfg_axioms Un_iff eps_P0
      list.sel(1) mem_Collect_eq nxt_P0 prod.inject)

definition reduce_reduce :: "('n, 't) item set \<Rightarrow> bool" where
  "reduce_reduce q \<equiv> card (completes q) > Suc 0"

lemma reduce_reduceE [elim]:
  assumes "reduce_reduce q"
  obtains X \<alpha> Y \<beta> where "[X \<rightarrow> \<alpha> . []] \<in> q" "[Y \<rightarrow> \<beta> . []] \<in> q" "[X \<rightarrow> \<alpha> . []] \<noteq> [Y \<rightarrow> \<beta> . []]"
proof -
  from assms obtain n where cardq: "card (completes q) = Suc (Suc n)" unfolding reduce_reduce_def 
    by (metis Suc_less_eq2 Suc_pred)
  moreover from this have nempty: "completes q \<noteq> {}" by fastforce
  ultimately obtain X \<alpha> where Xq: "[X \<rightarrow> \<alpha> . []] \<in> q" 
    using completes_subset by blast
  let ?p = "completes q - {[X \<rightarrow> \<alpha> . []]}"
  from cardq have cardp: "card ?p = Suc n" using Xq 
    by (metis DiffI card_Diff_singleton diff_Suc_1 item.inject neq_Nil_conv noncompletesE)
  moreover from this have "?p \<noteq> {}" by fastforce
  moreover from completes_subset[of q] have "?p \<subseteq> q" by blast
  ultimately obtain Y \<beta> where "[Y \<rightarrow> \<beta> . []] \<in> q" "[X \<rightarrow> \<alpha> . []] \<noteq> [Y \<rightarrow> \<beta> . []]" by blast
  with Xq show thesis using that by presburger
qed

definition "LR0_inadequate q \<equiv> shift_reduce q \<or> reduce_reduce q"

abbreviation "LR0_adequate q \<equiv> \<not>LR0_inadequate q"

lemma complete_noncomplete_Tm_imp_inadequate:
  assumes "completes q \<noteq> {}" "[X \<rightarrow> \<alpha> . Tm a # \<beta>] \<in> q" "q \<in> dfa.states LR\<^sub>0"
  shows "LR0_inadequate q"
proof -
  from assms P0_read_iff_in_q have nxt: "([q], a, [dfa.nxt LR\<^sub>0 q (Tm a), q]) \<in> npda.nxt P\<^sub>0" 
    by metis
  moreover from assms P0_complete_imp_reduce obtain qs rs where "(q#qs, rs) \<in> npda.eps P\<^sub>0"
    by (metis (no_types, lifting) completesE completes_subset empty_subsetI subset_antisym subset_eq)
  ultimately show ?thesis unfolding LR0_inadequate_def using shift_reduce.intros by blast
qed


lemma LR0_adequate_complete_cases[consumes 1, case_names empty singleton]:
  assumes "LR0_adequate q"
    "q \<in> dfa.states LR\<^sub>0"
  obtains "completes q = {}" |
    A \<alpha> where "completes q = {[A \<rightarrow> \<alpha> . []]}"
proof -
  from assms(2) have "finite q" by fastforce
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
qed

lemma LR_adequate_completes_singleton_imp_derivern_Suc:
  assumes "LR0_adequate q"
    "q \<in> dfa.states LR\<^sub>0"
    "completes q = {[A \<rightarrow> \<alpha>\<^sub>0 . []]}"
    "[X \<rightarrow> \<alpha> . Nt Y # \<beta>] \<in> noncompletes q"
    and Y_derivers: "Prods G' \<turnstile> [Nt Y] \<Rightarrow>r(Suc n) \<gamma>" "Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w"
  shows "\<gamma> = Nt A # map Tm w \<and> \<alpha>\<^sub>0 = []"
proof -
  from Y_derivers(2) obtain  Z \<delta> where Z\<delta>: "\<gamma> = Z # \<delta>" 
    using deriver.cases by (metis append_is_Nil_conv neq_Nil_conv)
  moreover from Y_derivers(2) have "Nts_syms \<gamma> \<noteq> {}" 
    by (metis Nts_syms_empty_iff deriver_imp_derive not_derive_map_Tm)
  ultimately obtain \<gamma>' B \<zeta> where reachable:
    "[Y \<rightarrow> [] . \<gamma>'] \<in> It G'" "([Y \<rightarrow> [] . \<gamma>'], [B \<rightarrow> [] . Z # \<zeta>]) \<in> (nfa.eps char_fa)\<^sup>*" 
    using derivern_non_word_imp_hd_eps_reachable[OF Y_derivers(1)[unfolded Z\<delta>]] by blast
  show ?thesis 
  proof (cases Z)
    case (Nt C)
    with Z\<delta> Y_derivers obtain u where C_prod: "(C, map Tm u) \<in> Prods G'" 
      by (metis derivers_last_step_single_Nt list.simps(8) map_Tm_Nt_eq_map_Tm_Nt 
          relpowp_imp_rtranclp self_append_conv2)
    from reachable have XY: "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>']) \<in> nfa.eps char_fa"
      using assms by (metis DiffE append.left_neutral in_It_imp_in_Prods in_state_imp_in_It 
          item.case prod_imp_eps)
    also note YB = reachable(2)[unfolded Nt]
    also have BCu: "([B \<rightarrow> [] . Nt C # \<zeta>], [C \<rightarrow> [] . map Tm u]) \<in> nfa.eps char_fa"
      using C_prod prod_imp_eps calculation in_eps_char_star_imp_in_It
        in_state_imp_in_It assms by blast
    finally have XC: "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [C \<rightarrow> [] . map Tm u]) \<in> (nfa.eps char_fa)\<^sup>*" .
    show ?thesis
    proof (cases u)
      case Nil
      with XC have "[C \<rightarrow> [] . map Tm u] = [A \<rightarrow> \<alpha>\<^sub>0 . []]" using assms completes_singleton_imp_eq
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
            "([B \<rightarrow> [] . Nt C # \<zeta>], [C \<rightarrow> [] . Tm a # \<theta>]) \<in> nfa.eps char_fa"
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
    from reachable have "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>']) \<in> nfa.eps char_fa"
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
    "completes q = {[A \<rightarrow> \<alpha>\<^sub>0 . []]}"
    "[X \<rightarrow> \<alpha> . Nt Y # \<beta>] \<in> q"
    and Y_derivers: "Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* \<gamma>" "Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w"
  shows "\<gamma> = Nt A # map Tm w \<and> \<alpha>\<^sub>0 = []"
  using Y_derivers(1) proof cases
  case rtrancl_refl
  with Y_derivers(2) have step: "([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . map Tm w]) \<in> nfa.eps char_fa"
    using deriver_singleton_imp_eps assms(2,4) completes_subset in_state_imp_in_It 
    by blast
  show ?thesis 
  proof (cases w)
    case Nil
    with step assms have "[Y \<rightarrow> [] . []] = [A \<rightarrow> \<alpha>\<^sub>0 . []]" using completes_singleton_imp_eq
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
\item \<open>q\<close> contains exactly one complete item @{term "[A \<rightarrow> [] . []]"} and all noncomplete items in \<open>q\<close>
are of the form @{term "[A \<rightarrow> \<alpha> . Nt Y # \<beta>]"} where all rightmost derivations for Y leading to a word \<open>w\<close>
are of the form \<open>Y \<Rightarrow>r* Aw \<Rightarrow>r w\<close>.
\end{itemize}\<close>

lemma LR0_adequate_cases[consumes 2, case_names completes_empty singleton comp_unique, 
      cases set: LR0_adequate]:
  assumes "LR0_adequate q"
    "q \<in> dfa.states LR\<^sub>0"
  obtains "completes q = {}" |
    A \<alpha> where "q = {[A \<rightarrow> \<alpha> . []]}" |
      A where "completes q = {[A \<rightarrow> [] . []]}" 
      "\<And>i. i \<in> noncompletes q \<Longrightarrow> \<exists>X \<alpha> Y \<beta>. i = [X \<rightarrow> \<alpha> . Nt Y # \<beta>]"
      "\<And>X \<alpha> Y \<beta> w \<gamma>. \<lbrakk>[X \<rightarrow> \<alpha> . Nt Y # \<beta>] \<in> q; 
      Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* \<gamma>; Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w\<rbrakk> \<Longrightarrow> \<gamma> = Nt A # map Tm w"
proof -
  from assms(2) have "finite q" by fastforce
  with assms consider 
    (empty) "completes q = {}" | 
    (singleton) A \<alpha> where "completes q = {[A \<rightarrow> \<alpha> . []]}"
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
        fix X \<alpha> Y \<beta> assume "[X \<rightarrow> \<alpha> . Y # \<beta>] \<in> noncompletes q"
        hence "\<exists>Z. Y = Nt Z" using singleton complete_noncomplete_Tm_imp_inadequate assms(1,2) 
          by (cases Y) simp_all
      } 
      note in_nc_imp_Nt = this
      moreover with LR_adequate_completes_singleton_imp_derivers[OF assms singleton] have 
        "\<And>X \<alpha> Y \<beta> w \<gamma>. \<lbrakk>[X \<rightarrow> \<alpha> . Y # \<beta>] \<in> q;
          Prods G' \<turnstile> [Y] \<Rightarrow>r* \<gamma>; Prods G' \<turnstile> \<gamma> \<Rightarrow>r map Tm w\<rbrakk> \<Longrightarrow> \<gamma> = Nt A # map Tm w"
        by blast
      moreover have "\<alpha> = []" 
      proof -
        from False in_nc_imp_Nt obtain X \<alpha>' Y \<beta> where It: "[X \<rightarrow> \<alpha>' . Nt Y # \<beta>] \<in> q"     
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
  from assms(2) obtain X \<beta> Y \<delta> a \<alpha> where "[X \<rightarrow> \<beta> . []] \<in> q" "[Y \<rightarrow> \<delta> . Tm a # \<alpha>] \<in> q" by fast 
  then obtain \<gamma> where "reliable_prefix ([X \<rightarrow> \<beta> . []]) \<gamma>"
    "reliable_prefix [Y \<rightarrow> \<delta> . Tm a # \<alpha>] \<gamma>" using state_imp_valids assms(1) by auto
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
  shows "\<forall>q\<in>npda.states P\<^sub>0. LR0_adequate q"
proof (rule ccontr)
  assume "\<not>(\<forall>q\<in>npda.states P\<^sub>0. LR0_adequate q)"
  then obtain q where q_inadequate: "q \<in> npda.states P\<^sub>0" "LR0_inadequate q" by blast
  from this(2) show False unfolding LR0_inadequate_def
  proof (standard, goal_cases shift_reduce reduce_reduce)
    case reduce_reduce
    then obtain X \<beta> Y \<delta> where conflict: "[X \<rightarrow> \<beta> . []] \<in> q" "[Y \<rightarrow> \<delta> . []] \<in> q" 
      "[X \<rightarrow> \<beta> . []] \<noteq> [Y \<rightarrow> \<delta> . []]" by fastforce
    then obtain \<gamma> where "reliable_prefix ([X \<rightarrow> \<beta> . []]) \<gamma>"
      "reliable_prefix ([Y \<rightarrow> \<delta> . []]) \<gamma>" using state_imp_valids q_inadequate by auto
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

lemma derivers_appendD:
  "(P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma>) = 
    ((\<exists>\<beta>'. P \<turnstile> \<beta> \<Rightarrow>r* \<beta>' \<and> \<gamma> = \<alpha> @ \<beta>') \<or> (\<exists>\<alpha>' v. P \<turnstile> \<alpha> \<Rightarrow>r* \<alpha>' \<and> P \<turnstile> \<beta> \<Rightarrow>r* map Tm v \<and> \<gamma> = \<alpha>' @ map Tm v))" 
  (is "_ = ?EX")
proof
  show "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma> \<Longrightarrow> ?EX"
  proof (induction "\<alpha> @ \<beta>" arbitrary: \<alpha> \<beta> rule: converse_rtranclp_induct)
    case (step z)
      show ?case proof (cases \<beta> rule: syms_rm_cases)
        case (Tms w)
        then show ?thesis using step(3)[of _ "map Tm w"] 
          by (metis (no_types, lifting) derivern_append_map_Tm rtranclp.simps rtranclp_power 
              rtranclp_trans step.hyps(1,2))
      next
        case (Nt \<beta>' A w)
        with step obtain \<delta> where z_app: "P \<turnstile> \<beta> \<Rightarrow>r \<beta>' @ \<delta> @ map Tm w"  "z = \<alpha> @ \<beta>' @ \<delta> @ map Tm w"   
          by (smt (verit, best) append.assoc deriver.cases deriver.intros rm_eq_imp_eq)
        from step(3)[OF this(2)] consider 
          \<beta>'' where "P \<turnstile> \<beta>' @ \<delta> @ map Tm w \<Rightarrow>r* \<beta>''" "\<gamma> = \<alpha> @ \<beta>''" |
          \<alpha>'' v where "P \<turnstile> \<alpha>  \<Rightarrow>r* \<alpha>''" "P \<turnstile> \<beta>' @ \<delta> @ map Tm w \<Rightarrow>r* map Tm v"  "\<gamma> = \<alpha>'' @ map Tm v"  
          using derivers_imp_derives derives_map_Tm_iff by blast
        thus ?thesis using z_app by cases fastforce+
      qed
    qed simp
next
  assume ?EX
  then show "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma>" by standard 
      (use derivers_prepend in blast, metis derivers_prepend derivers_append_map_Tm rtranclp_trans)
qed

lemma derivers_append_cases [consumes 1, case_names suffix prefix]:
  assumes "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma>"
  obtains \<beta>' where "P \<turnstile> \<beta> \<Rightarrow>r* \<beta>'" "\<gamma> = \<alpha> @ \<beta>'" |
    \<alpha>' v where "P \<turnstile> \<alpha> \<Rightarrow>r* \<alpha>'" "P \<turnstile> \<beta> \<Rightarrow>r* map Tm v" "\<gamma> = \<alpha>' @ map Tm v"
  using derivers_appendD[THEN iffD1, OF assms] by blast


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
  assumes "LR0_adequate {i. reliable_prefix i \<alpha>}" (is "LR0_adequate ?p")
    "reliable_prefix [X \<rightarrow> [] . []] \<alpha>"
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt Y # map Tm x"
    "Prods G' \<turnstile> \<alpha> @ \<alpha>' @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ map Tm y"
  shows "\<alpha>' = [] \<and> Y = X \<and> x = y"
proof -
  from assms(2) obtain w where X_derivers: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w"
    "Prods G' \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ map Tm w" 
    using reliable_prefixE by force
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
      A_reliable: "reliable_prefix [A \<rightarrow> \<beta> . Z' # \<gamma>] \<alpha>" 
        "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Z' # \<gamma> @ map Tm z"
        "Prods G' \<turnstile> Z' # \<gamma> @ map Tm z \<Rightarrow>r* \<alpha>' @ Nt Y # map Tm x"
      by blast
    from assms(3,4) have deriver_y: "Prods G' \<turnstile> \<alpha>' @ Nt Y # map Tm x \<Rightarrow>r map Tm y"
      by (metis append_Nil deriver_prefix_indep)
    have "?p \<in> dfa.states LR\<^sub>0" 
      by (metis dfa_LR0.nextl_init_state nextl_dfa_LR0_is_valids)
    with assms(1) show ?thesis proof (cases rule: LR0_adequate_cases)
      case (comp_unique B)
      with assms(2) have AX [simp]: "B = X"
        by auto
      from A_reliable obtain Z'' where Z''_def [simp]: "Z' = Nt Z''" using comp_unique by auto
      from A_reliable(3) deriver_y obtain \<gamma>' u v  where decomp: 
        "Prods G' \<turnstile> [Nt Z''] \<Rightarrow>r* \<gamma>'" "Prods G' \<turnstile> \<gamma>' \<Rightarrow>r map Tm u" 
        "Prods G' \<turnstile> \<gamma> @ map Tm z \<Rightarrow>r* map Tm v"
        "\<gamma>' @ map Tm v = \<alpha>' @ Nt Y # map Tm x" "y = u @ v"
        using derivers_leftmost_derivers_last_step[of Z'' "\<gamma> @ map Tm z" "\<alpha>' @ Nt Y # map Tm x" y] 
        unfolding Z''_def by metis
      with comp_unique have "\<gamma>' = Nt X # map Tm u" using A_reliable by simp
      with decomp show ?thesis 
        by (metis (no_types, lifting) append_Cons map_append rm_eq_imp_eq self_append_conv2)
    qed (use assms(2) completes_def in fastforce, use A_reliable assms(2) in auto)
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
  assumes adequates: "\<forall>q\<in>npda.states P\<^sub>0. LR0_adequate q"
  shows "is_LR 0" 
proof (rule LRk_wlog, goal_cases LR)
  case (LR \<alpha> X \<beta> w \<gamma> Y x y \<delta>)
  obtain p where p_nextl: "dfa.nextl LR\<^sub>0 (dfa.init LR\<^sub>0) (\<alpha>@\<beta>) = p" by presburger
  with adequates have p_adequate: "LR0_adequate p" "p \<in> dfa.states LR\<^sub>0" using states_P0 
    using dfa_LR0.nextl_init_state by (metis Un_iff, metis)
  from p_nextl have p_valids: "p = {i. reliable_prefix i (\<alpha>@\<beta>)}"
    using nextl_dfa_LR0_is_valids by auto
  from LR have X_reliable: "reliable_prefix ([X \<rightarrow> \<beta> . []]) (\<alpha>@\<beta>)" 
    using char_eq_reliable_prefix derivers_imp_char by auto
  from p_adequate show ?case proof cases
    case (singleton A \<alpha>')
    with X_reliable have singleton: "p = {[X \<rightarrow> \<beta> . []]}" 
      using p_nextl nextl_dfa_LR0_is_valids by force
    from LR(6,8) obtain z where z_defs: "\<gamma> @ \<delta> = \<alpha> @ \<beta> @ map Tm z" "z @ x = y"
      using eq_hd_lt_imp_substring[of "\<alpha> @ \<beta>" "map Tm y" "\<gamma> @ \<delta>" "map Tm x"] append.assoc 
      by (metis (no_types, opaque_lifting) append_eq_map_conv map_Tm_inject_iff)
    from this show ?thesis proof (cases rule: app_eq_rm_cases)
      case (1 u v)
      with derivers_substring_reliable[of "\<alpha> @ \<beta>" "map Tm u" Y x] LR(3)
      obtain B \<alpha>'' C \<beta>'' where "reliable_prefix [B \<rightarrow> \<alpha>'' . C # \<beta>''] (\<alpha> @ \<beta>)" by fastforce
      then show ?thesis using singleton p_valids by blast
    next
      case (2 \<delta>')
      from LR(3) have "reliable_prefix [Y \<rightarrow> \<delta>' . map Tm z] (\<alpha> @ \<beta>)" 
        using 2 LR(4,6) z_defs by fastforce
      with singleton p_valids have "z = [] \<and> \<delta>' = \<beta> \<and> X = Y" 
        by (metis item.inject map_is_Nil_conv mem_Collect_eq singletonD)
      with 2 z_defs show ?thesis by simp
    qed
  next
    case (comp_unique A)
    with p_valids X_reliable have comp_X: "completes p = {[X \<rightarrow> \<beta> . []]}" "\<beta> = []"
      unfolding completes_def by auto 
    from LR(6) have eq: "(\<alpha> @ \<beta>) @ map Tm y = \<gamma> @ \<delta> @ map Tm x" by simp
    show ?thesis proof (cases rule: substring_app_cases[OF eq LR(8)])
      case (1 _ _)
      with prefix_comp_unique_imp_eps[OF p_adequate(1)[unfolded p_valids]] X_reliable
        comp_X LR show ?thesis by (metis append.assoc append.right_neutral)
    next
      case (2 \<delta>\<^sub>1 x')
      from LR(3) have Y_reliable: "reliable_prefix [Y \<rightarrow> \<delta>\<^sub>1 . map Tm x'] (\<alpha> @ \<beta>)" 
      proof
        from LR(4,6) 2 show "Prods G' \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r (\<alpha> @ \<beta>) @ map Tm x' @ map Tm x"          
          by (metis eq map_append)
      qed (rule 2)
      show ?thesis proof (cases x')
        case Nil
        with Y_reliable p_valids have "[Y \<rightarrow> \<delta>\<^sub>1 . map Tm x'] \<in> completes p" unfolding completes_def 
          by simp
        with comp_X have "[Y \<rightarrow> \<delta>\<^sub>1 . map Tm x'] = [X \<rightarrow> [] . []]" by simp
        with 2 show ?thesis using comp_X by simp
      next
        case (Cons a x'')
        from Y_reliable p_valids have "[Y \<rightarrow> \<delta>\<^sub>1 . Tm a # map Tm x''] \<in> noncompletes p"
          unfolding Cons by auto
        then show ?thesis using comp_unique(2) sym.exhaust by blast
      qed
    qed
  qed (use p_valids X_reliable completes_def in fastforce)
qed
    

theorem is_LR0_iff_no_LR0_inadequate_states:
  "is_LR 0 = (\<forall>q\<in>npda.states P\<^sub>0. LR0_adequate q)"
  using is_LR0_imp_no_LR0_inadequate_states no_LR0_inadequate_states_imp_is_LR0 by metis

end

end
