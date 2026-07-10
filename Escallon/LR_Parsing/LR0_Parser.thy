theory LR0_Parser 
  imports 
    LR0_Automata
    Shift_Reduce_PDA
begin

context Extended_Cfg
begin

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
  "gpda.init P\<^sub>0 = valids []"
  by (metis dfa_LR0.nextl.simps(1) init_P0 nextl_dfa_LR0_is_valids)


abbreviation "P0_final \<equiv> {[S' \<rightarrow> [] \<cdot> []]}"

lemma S'_eps_not_reliable:
  assumes "reliable_prefix [S' \<rightarrow> [] \<cdot> []] \<gamma>"
  shows False
  using assms proof cases
  case (1 \<gamma>' w)
  from this(3) have "(S', []) \<in> Prods G'" 
    using deriver_imp_in_Prods by force
  then show False 
    using G'_Prod_cases S'_Prod_notin_G(1) by auto
qed

lemma P0_final_not_valids:
  "P0_final \<noteq> valids \<gamma>"
  using S'_eps_not_reliable unfolding valids_def by blast

lemma valids_in_states_imp_in_dfa_LR0_states [dest]:
  "valids \<gamma> \<in> gpda.states P\<^sub>0 \<Longrightarrow> valids \<gamma> \<in> dfa.states LR\<^sub>0"
  unfolding states_P0 using P0_final_not_valids by blast

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

lemma eps_P0_reduceI:
  assumes "qs = [dfa.nxt LR\<^sub>0 (last (p#ps)) (Nt X), last (p#ps)]" 
    "set (p#ps) \<subseteq> dfa.states LR\<^sub>0" "[X \<rightarrow> \<alpha> \<cdot> []] \<in> p" "length \<alpha> = length ps" "X \<noteq> S'" 
  shows "(p#ps, qs) \<in> gpda.eps P\<^sub>0"
  unfolding eps_P0 proof (rule UnI1, standard, intro exI, intro conjI)
  show "(p # ps, qs) = (let q = last (p # ps) in (p # ps, [dfa.nxt LR\<^sub>0 q (Nt X), q]))"
    using assms(1) by metis
qed (use assms in auto)

lemmas P\<^sub>0_simps [simp] = states_P0 init_P0 nxt_P0 eps_P0

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

notation P0.step (infix \<open>\<turnstile>P\<close> 55)
notation P0.steps (infix \<open>\<turnstile>P*\<close> 55)
notation P0.stepn (\<open>_ \<turnstile>P'(_') _\<close> 55)

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
  assumes "(qs, u) \<turnstile>P ([P0_final], v)" 
  obtains q where "q \<in> dfa.states LR\<^sub>0" "(qs, u) = ([q, dfa.init LR\<^sub>0], v)" "[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q"
  using assms by cases auto

lemma P0_nxtI [intro]:
  assumes "ps = p # ps'" "qs = dfa.nxt LR\<^sub>0 p (Tm a) # p # ps'" 
    "p \<in> dfa.states LR\<^sub>0" "dfa.nxt LR\<^sub>0 p (Tm a) \<noteq> {}"
  shows "(ps, a # w) \<turnstile>P (qs, w)"
proof
  show "ps = [p] @ ps'" using assms by simp
  show "qs  = [dfa.nxt LR\<^sub>0 p (Tm a), p] @ ps'" using assms by simp
  from assms show "([p], a, [dfa.nxt LR\<^sub>0 p (Tm a), p]) \<in> gpda.nxt P\<^sub>0" 
    by simp
qed

lemma P0_valids_nxtI:
  assumes "valids (\<gamma> @ [Tm a]) \<noteq> {}" "valids \<gamma> \<in> dfa.states LR\<^sub>0"
  shows "(valids \<gamma> # qs, a # w) \<turnstile>P (valids (\<gamma> @ [Tm a]) # valids \<gamma> # qs, w)"
proof
  show "valids (\<gamma> @ [Tm a]) # valids \<gamma> # qs = dfa.nxt LR\<^sub>0 (valids \<gamma>) (Tm a) # valids \<gamma>  # qs"
    using nxt_dfa_LR0_shift_is_valids_app[OF assms(2)] by presburger
  from nxt_dfa_LR0_shift_is_valids_app[OF assms(2)] show "dfa.nxt LR\<^sub>0 (valids \<gamma>) (Tm a) \<noteq> {}"
    using assms by simp
qed (use assms in simp_all) 
thm eps_P0

lemma P0_valids_reduceI:
  assumes 
    "[A \<rightarrow> \<beta> \<cdot> []] \<in> valids (\<gamma> @ \<beta>)" (is "_ \<in> ?\<gamma>\<beta>")  
    "set (take (Suc (length \<beta>)) (valids (\<gamma> @ \<beta>) # ps)) \<subseteq> dfa.states LR\<^sub>0"
    "A \<noteq> S'"
    "(valids (\<gamma> @ \<beta>) # ps) ! (length \<beta>) = valids \<gamma>"
    "length (valids (\<gamma> @ \<beta>) # ps) > length \<beta>"
  shows "(valids (\<gamma> @ \<beta>) # ps, w) \<turnstile>P (valids (\<gamma> @ [Nt A]) # drop (length \<beta>) (valids (\<gamma> @ \<beta>) # ps), w)"
proof 
  from assms obtain qs where qs_def: "qs = take (length \<beta>) ps"
    by presburger
  let ?q = "last (?\<gamma>\<beta> # take (length \<beta>) ps)"
  show "(?\<gamma>\<beta> # take (length \<beta>) ps, [dfa.nxt LR\<^sub>0 ?q (Nt A), ?q]) \<in> gpda.eps P\<^sub>0"
    by (rule eps_P0_reduceI) (use qs_def assms in auto)
  show "valids (\<gamma> @ \<beta>) # ps = (valids (\<gamma> @ \<beta>) # take (length \<beta>) ps) @ drop (length \<beta>) ps" 
    by simp
  from assms have last_eq_\<gamma>: "(last (valids (\<gamma> @ \<beta>) # take (length \<beta>) ps)) = valids \<gamma>"  
    by (metis last_snoc length_Cons take_Suc_Cons take_Suc_conv_app_nth)
  show "valids (\<gamma> @ [Nt A]) # drop (length \<beta>) (valids (\<gamma> @ \<beta>) # ps) =
    [dfa.nxt LR\<^sub>0 (last (valids (\<gamma> @ \<beta>) # take (length \<beta>) ps)) (Nt A),
     last (valids (\<gamma> @ \<beta>) # take (length \<beta>) ps)] @
    drop (length \<beta>) ps"
    unfolding last_eq_\<gamma> 
    by (smt (verit, ccfv_SIG) append.assoc append_Cons append_take_drop_id assms(4,5)
        dfa_LR0.nextl_init_state length_Cons less_SucI nextl_dfa_LR0_is_valids
        nxt_dfa_LR0_shift_is_valids_app same_append_eq take_Suc_Cons
        take_Suc_conv_app_nth)
qed

lemma P0_finishI:
  assumes "q \<in> dfa.states LR\<^sub>0" "[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q"
  shows "(q # gpda.init P\<^sub>0 # qs, w) \<turnstile>P (P0_final # qs, w)"
proof -
  from assms have "([q, dfa.init LR\<^sub>0], [P0_final]) \<in> gpda.eps P\<^sub>0"
    by simp
  thus ?thesis using P0.step_eps[of "[q, dfa.init LR\<^sub>0]" "[P0_final]" qs w] by fastforce
qed

lemma valids_S_Nil_step_finish:
  "(valids [Nt S] # valids [] # qs, w) \<turnstile>P (P0_final # qs, w)"
  unfolding init_P0_is_valids_empty[symmetric] 
  by (rule P0_finishI) (use dfa_LR0.nextl_init_state nextl_dfa_LR0_is_valids in force,
      metis Extended_Cfg.in_states_imp_valid Extended_Cfg.validI Extended_Cfg_axioms
      S'_complete_reliable_imp_S ipda.final_state_in_It ipda_IPDA states_char_fa)

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

lemma sw_shift:
  assumes "\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* (ps, a # w)" "(ps, a # w) \<turnstile>P (qs, w)"
  shows "Tm a # \<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* (qs, w)"
  using assms(2) proof cases
  case (shift r rs a w)
  from assms show ?thesis 
    by standard (use shift in auto)
qed simp_all

lemma stack_word_imp_P0_steps:
  "\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1 \<Longrightarrow> c\<^sub>0 \<turnstile>P* c\<^sub>1"
  by (induction rule: stack_word.induct) auto

lemma P0_init_stack_word_length_inv:
  "\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (qs, v) \<Longrightarrow> Suc (length \<alpha>) = length qs"
  by (induction "([gpda.init P\<^sub>0], u)" "(qs, v)" arbitrary: qs v rule: stack_word.induct) auto

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

lemma P0_nth_is_valids_of_nth_stack_word:
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

lemma sw_last_is_init:
  assumes "\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (q # qs, v)"
  shows "last (q # qs) = gpda.init P\<^sub>0"
proof -
  note len_qqs_Suc_len_\<alpha> = P0_init_stack_word_length_inv[OF assms]
  hence "last (q # qs) = (q # qs) ! (length \<alpha>)"
    by (simp add: last_of_Cons_idx_len_tl)
  also with P0_nth_is_valids_of_nth_stack_word[OF assms] have 
    "... = valids (rev (drop (length \<alpha>) \<alpha>))" using len_qqs_Suc_len_\<alpha> by force
  finally show ?thesis using init_P0_is_valids_empty by auto
qed

lemma sw_second_is_valids_tl:
  assumes "\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (p # q # qs, v)"
  shows "q = valids (rev (tl \<alpha>))"
proof -
  note len_pqqs_Suc_len_\<alpha> = P0_init_stack_word_length_inv[OF assms]
  have "q = (p # q # qs) ! Suc 0" by simp
  also from P0_nth_is_valids_of_nth_stack_word[OF assms] have 
    "... = valids (rev (drop (Suc 0) \<alpha>))" by auto
  finally show ?thesis by (simp add: drop_Suc)
qed

lemma P0_invariant1:
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
      with P0_nth_is_valids_of_nth_stack_word[of _ _ p\<^sub>n "rs @ ss"] reduce sw_step have 
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
    with P0_invariant1[of "[Nt S]" w "[]"] show ?thesis using stack_word assms(3) by auto
  qed
qed

lemma P0_sound:
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


(*TODO: Formalize the shift-reduce parser M\<^sub>G and prove (roughly)

    Prods G' \<turnstile> \<alpha> \<Rightarrow>r* map Tm u \<Longrightarrow> (q\<^sub>0\<^sub>,\<^sub>M, u @ v) \<turnstile>M\<^sub>G* (\<alpha> @ [q\<^sub>0], v)

    (q\<^sub>0\<^sub>,\<^sub>M, u @ v) \<turnstile>M\<^sub>G* (\<alpha> @ [q\<^sub>0], v) \<Longrightarrow> \<exists>qs. \<alpha> \<Turnstile> (q\<^sub>0\<^sub>,\<^sub>P, u @ v) \<turnstile>P* (valids \<alpha> # qs, v)
    
 *)

abbreviation "M\<^sub>G \<equiv> SRPDA G"

interpretation MG: srpda G M\<^sub>G 
   by unfold_locales auto

notation MG.step (infix \<open>\<turnstile>M\<close> 55)
notation MG.steps (infix \<open>\<turnstile>M*\<close> 55)
notation MG.stepn (\<open>_ \<turnstile>M'(_') _\<close> 55)

lemma P0_final_not_dfa_LR0_state:
  "P0_final \<notin> dfa.states LR\<^sub>0"
  using Extended_Cfg.state_imp_valids Extended_Cfg_axioms P0_final_not_valids by blast

lemma hd_not_final_imp_stack_is_dfa_LR0_states:
  "\<lbrakk>([gpda.init P\<^sub>0], u) \<turnstile>P* (q#qs, v); q \<noteq> P0_final\<rbrakk> \<Longrightarrow> set (q#qs) \<subseteq> dfa.states LR\<^sub>0"
proof (induction "q#qs" v arbitrary: q qs rule: rtranclp_induct2)
  case (step ps v w)
  from this(2) show ?case proof cases
    case (shift r rs a x)
    then show ?thesis 
      using step P0_final_not_dfa_LR0_state dfa_LR0.nxt by auto
  next
    case (reduce r\<^sub>n rs r\<^sub>0 ss X \<alpha> x)
    with step(3) P0_final_not_dfa_LR0_state have rn_rs_ss_states: 
      "set (r\<^sub>n # rs @ ss) \<subseteq> dfa.states LR\<^sub>0" 
      by blast
    with reduce have "set (r\<^sub>0 # ss) \<subseteq> dfa.states LR\<^sub>0" by auto
    moreover with dfa_LR0.nxt have "dfa.nxt LR\<^sub>0 r\<^sub>0 (Nt X) \<in> dfa.states LR\<^sub>0"
      by auto
    ultimately show ?thesis using reduce(3) by simp
  qed (use step in fast)
qed (use dfa_LR0.init in simp)
  

lemma MG_steps_imp_stack_word:
  assumes "([gpda.init M\<^sub>G], u) \<turnstile>M* (map Sym \<alpha> @ [gpda.init M\<^sub>G], v)" "valids (rev \<alpha>) \<noteq> {}"
  obtains qs where "\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<alpha>) # qs, v)"
  using assms proof (induction "(map Sym \<alpha> @ [gpda.init M\<^sub>G], v)" arbitrary: \<alpha> v thesis rule: rtranclp_induct)
  case base
  then show ?case using base(2)[of "[]"] init_P0_is_valids_empty by force
next
  case (step c)
  from this(2) show ?case proof cases
    case (shift x xs a w)
    show ?thesis proof (cases xs rule: rev_cases)
      case Nil
      with shift step(1) have eq: 
        "(map Sym \<alpha> @ [gpda.init M\<^sub>G], v) = ([Sym (Tm a), gpda.init M\<^sub>G], w)" "u = a # w"
        using MG.reaches_Init_imp_refl by auto
      have "[Tm a] \<Turnstile> ([gpda.init P\<^sub>0], a # w) \<turnstile>P* ([valids [Tm a], gpda.init P\<^sub>0], w)"
      proof (rule sw_shift)
        show "([gpda.init P\<^sub>0], a # w) \<turnstile>P ([valids [Tm a], gpda.init P\<^sub>0], w)" 
        proof
          show "[valids [Tm a], gpda.init P\<^sub>0] = dfa.nxt LR\<^sub>0 (gpda.init P\<^sub>0) (Tm a) # [gpda.init P\<^sub>0]"
            using init_P0_is_valids_empty nxt_dfa_LR0_shift_is_valids_app dfa_LR0.init by simp
          from step(5) eq show "dfa.nxt LR\<^sub>0 (gpda.init P\<^sub>0) (Tm a) \<noteq> {}"
            using nxt_dfa_LR0_shift_is_valids_app init_P0_is_valids_empty dfa_LR0.init by auto
        qed (use dfa_LR0.init in auto)
      qed blast 
      then show ?thesis using step(4) eq by auto
    next
      case (snoc ys y)
      with shift step have \<alpha>_eq: "map Sym \<alpha> = Sym (Tm a) # x # ys" "y = gpda.init M\<^sub>G" by auto
      with snoc shift obtain \<beta> where c_eq: "c = (map Sym \<beta> @ [gpda.init M\<^sub>G], a # w)" "\<beta> = tl \<alpha>"
        using Cons_eq_map_conv by fastforce
      with nempty_valids_imp_nempty_valids_prefix[] step(5) have 
        valids_\<beta>_nempty: "valids (rev \<beta>) \<noteq> {}" using \<alpha>_eq(1) by force
      with step(3)[OF c_eq(1)] obtain qs where sw_\<beta>:
        "\<beta> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<beta>) # qs, a # w)" 
        by metis
      hence "Tm a # \<beta> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<alpha>) # valids (rev \<beta>) # qs, w)"
      proof (rule sw_shift)
        show "(valids (rev \<beta>) # qs, a # w) \<turnstile>P (valids (rev \<alpha>) # valids (rev \<beta>) # qs, w)"
        proof -
          from c_eq \<alpha>_eq have rev_\<alpha>_app: "rev \<alpha> = rev \<beta> @ [Tm a]" by fastforce
          show ?thesis unfolding rev_\<alpha>_app proof (rule P0_valids_nxtI)
            from sw_\<beta> have "([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<beta>) # qs, a # w)"
              using stack_word_imp_P0_steps by blast
            thus "valids (rev \<beta>) \<in> dfa.states LR\<^sub>0"  
              by (metis dfa_LR0.nextl_init_state nextl_dfa_LR0_is_valids)
          qed (use rev_\<alpha>_app step(5) in simp)
        qed
      qed
      then show ?thesis using step \<alpha>_eq c_eq shift by fastforce
    qed
  next
    case (reduce A \<beta> xs w)
    show ?thesis proof (cases xs rule: rev_cases)
      case (snoc ys y)
      with reduce obtain \<gamma> where \<gamma>_def: "map Sym \<gamma> = ys" by auto
      with snoc reduce have \<alpha>_Cons: "\<alpha> = Nt A # \<gamma>" by auto
      have A\<beta>_valid_for_\<gamma>\<beta>: "[A \<rightarrow> \<beta> \<cdot> []] \<in> valids (rev \<gamma> @ \<beta>)"
      proof -
        from step(5) \<gamma>_def reduce snoc have "valids (rev \<gamma> @ [Nt A]) \<noteq> {}" by force
        from valids_prod_imp_complete_in_valids_derive[OF this] reduce(1) show ?thesis 
          using G_Prods_subset_G' by blast
      qed  
      with snoc reduce step(3)[of "rev \<beta> @ \<gamma>" w] obtain qs where sw_\<beta>\<gamma>:
        "rev \<beta> @ \<gamma> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<gamma> @ \<beta>) # qs, w)"
        using \<gamma>_def by auto
      then have "Nt A # \<gamma> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<gamma> @ [Nt A]) # drop (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs), w)"
      proof
        from A\<beta>_valid_for_\<gamma>\<beta>
        show "(valids (rev \<gamma> @ \<beta>) # qs, w) \<turnstile>P (valids (rev \<gamma> @ [Nt A]) # drop (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs), w)"
        proof (rule P0_valids_reduceI)
          show "set (take (Suc (length \<beta>)) (valids (rev \<gamma> @ \<beta>) # qs)) \<subseteq> dfa.states LR\<^sub>0"
                (is "?Q \<subseteq> _")
          proof -
            have "?Q \<subseteq> set (valids (rev \<gamma> @ \<beta>) # qs)" 
              by (meson set_take_subset)
            also from sw_\<beta>\<gamma>[THEN stack_word_imp_P0_steps] have "... \<subseteq> dfa.states LR\<^sub>0" 
              using hd_not_final_imp_stack_is_dfa_LR0_states P0_final_not_valids by metis
            finally show ?thesis .
          qed
          from reduce(1) show "A \<noteq> S'" using S'_Prod_notin_G G_Prods_subset_G'
            by blast
          from P0_init_stack_word_length_inv[OF sw_\<beta>\<gamma>] 
          show "length \<beta> < length (valids (rev \<gamma> @ \<beta>) # qs)" by auto
          with P0_nth_is_valids_of_nth_stack_word[OF sw_\<beta>\<gamma>] show 
            "(valids (rev \<gamma> @ \<beta>) # qs) ! length \<beta> = valids (rev \<gamma>)"
            by simp
        qed
        show valids_take_drop:
          "(valids (rev \<gamma> @ \<beta>) # qs, w) 
            = (take (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs) @ valids (rev \<gamma>) # drop (Suc (length \<beta>)) (valids (rev \<gamma> @ \<beta>) # qs), w)"
        proof -
          from P0_init_stack_word_length_inv[OF sw_\<beta>\<gamma>] have "length \<beta> < length (valids (rev \<gamma> @ \<beta>) # qs)"
            by simp
          moreover with P0_nth_is_valids_of_nth_stack_word[OF sw_\<beta>\<gamma>]
          have "(valids (rev \<gamma> @ \<beta>) # qs) ! (length \<beta>) = valids (rev (drop (length \<beta>) (rev \<beta> @ \<gamma>)))"
            by simp
          moreover have "... = valids (rev \<gamma>)" by simp
          ultimately show ?thesis using id_take_nth_drop by metis
        qed
        show "(valids (rev \<gamma> @ [Nt A]) # drop (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs), w) =
    (dfa.nxt LR\<^sub>0 (valids (rev \<gamma>)) (Nt A) # valids (rev \<gamma>) # drop (Suc (length \<beta>)) (valids (rev \<gamma> @ \<beta>) # qs), w)"
        proof -
          have "valids (rev \<gamma> @ [Nt A]) = dfa.nxt LR\<^sub>0 (valids (rev \<gamma>)) (Nt A)"
          proof -
            from valids_take_drop have "valids (rev \<gamma>) \<in> set (valids (rev \<gamma> @ \<beta>) # qs)"
              by (metis Pair_inject in_set_conv_decomp)
            with P0.steps_init_imp_states sw_\<beta>\<gamma>[THEN stack_word_imp_P0_steps] 
            have "valids (rev \<gamma>) \<in> gpda.states P\<^sub>0" by blast
            thus ?thesis 
              using nxt_dfa_LR0_shift_is_valids_app by blast
          qed
          with valids_take_drop show ?thesis 
            by (metis append_take_drop_id prod.inject same_append_eq)
        qed
      qed (use P0_init_stack_word_length_inv[OF sw_\<beta>\<gamma>] in simp)
     then show ?thesis using snoc reduce \<alpha>_Cons step(4) by auto
    qed (use reduce in simp)
  qed (cases \<alpha>, auto)
qed



lemma P0_complete:
  "LangS G' \<subseteq> P0.Lang"
proof
  fix w
  assume "w \<in> LangS G'"
  hence "w \<in> LangS G" using Lang_preserved by blast
  note in_Lang_MG = set_mp[OF MG.srpda_complete this]
  note MG_reaches_S = this[THEN MG.in_Lang_imp_reaches_S]
  hence "([gpda.init P\<^sub>0], w) \<turnstile>P* ([valids [Nt S], gpda.init P\<^sub>0], [])"
  proof -
    obtain qs where
      "[Nt S] \<Turnstile> ([gpda.init P\<^sub>0], w) \<turnstile>P* (valids [Nt S] # qs, [])" 
    proof -
      have "valids (rev [Nt S]) \<noteq> {}" 
        by (metis (no_types, lifting) S'_complete_reliable_imp_S empty_iff in_states_imp_valid
            ipda.final_state_in_It ipda_IPDA rev_singleton_conv states_char_fa validI)
      with MG_reaches_S MG_steps_imp_stack_word[of w "[Nt S]" "[]"] show thesis 
        using that by auto
    qed
    moreover from this obtain q where qs_singleton: "qs = [q]"
      using P0_init_stack_word_length_inv by fastforce
    moreover with sw_last_is_init[OF calculation(1)] have "q = gpda.init P\<^sub>0"
      by auto
    ultimately show ?thesis using stack_word_imp_P0_steps by blast
  qed
  also have "... \<turnstile>P ([P0_final], [])"
    using valids_S_Nil_step_finish[of "[]"] init_P0_is_valids_empty by presburger
  finally show "w \<in> P0.Lang" unfolding P0.Lang_def by fastforce
qed
 
theorem P0_Lang_eq_Lang_G:
  "P0.Lang = LangS G'"
  using P0_sound P0_complete by standard

end
end
