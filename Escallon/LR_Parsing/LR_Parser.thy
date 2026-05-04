theory LR_Parser 
  imports 
    Item_Pushdown_Automata
    Finite_Automata_HF.Finite_Automata_HF
    Rightmost_Chain
begin

context Extended_Cfg
begin



section \<open>char(G), \<open>LR\<^sub>0(G)\<close>\<close>

definition char_fa :: "(('n, 't) sym, ('n, 't) item) nfa" where
  "char_fa \<equiv> let 
      P = Prods G';
      Q = It G';
      F = {[X \<rightarrow> \<alpha> . []] |X \<alpha>. [X \<rightarrow> \<alpha> . []] \<in> It G'};
      \<Delta> = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> if a = Y \<and> (X, \<alpha>@Y#\<beta>) \<in> P then {[X \<rightarrow> \<alpha>@[Y] . \<beta>]} else {}| 
         _ \<Rightarrow> {}); 
      \<E> = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @Nt Y#\<beta>) \<in> P \<and> (Y, \<gamma>) \<in> P} in
    \<lparr>nfa.states = Q, nfa.init = {[S' \<rightarrow> [] . [Nt S]]}, nfa.final = F, nfa.nxt = \<Delta>, nfa.eps = \<E>\<rparr>"

lemma states_char_fa [simp]: 
  "nfa.states char_fa = It G'"
  unfolding char_fa_def by (meson nfa.select_convs(1))

lemma init_char_fa [simp]:
  "nfa.init char_fa = {[S' \<rightarrow> [] . [Nt S]]}"
  unfolding char_fa_def by (meson nfa.select_convs(2))

lemma final_char_fa [simp]:
  "nfa.final char_fa = {[X \<rightarrow> \<alpha> . []] |X \<alpha>. [X \<rightarrow> \<alpha> . []] \<in> It G'}"
  unfolding char_fa_def by (meson nfa.select_convs(3))

lemma nxt_char_fa [simp]:
  "nfa.nxt char_fa = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> if a = Y \<and> ((X, \<alpha> @ Y # \<beta>) \<in> Prods G') then {[X \<rightarrow> \<alpha> @ [Y] . \<beta>]} 
  else {} | _ \<Rightarrow> {})"
  unfolding char_fa_def by (meson nfa.select_convs(4))

lemma char_fa_nxt_neq_or_not_Prod_imp_empty:
  assumes "Y \<noteq> a \<or> (X, \<alpha> @ Y # \<beta>) \<notin> Prods G'"
  shows "nfa.nxt char_fa ([X \<rightarrow> \<alpha> . Y # \<beta>]) a = {}" 
  using assms by auto

lemma char_fa_nxt_in_Prods_imp_singleton:
  assumes "(X, \<alpha> @ Y # \<beta>) \<in> Prods G'"
  shows "nfa.nxt char_fa ([X \<rightarrow> \<alpha> . Y # \<beta>]) Y = {[X \<rightarrow> \<alpha> @ [Y] . \<beta>]}"
  using assms by simp

lemma char_fa_nxt_nempty_imp_hd:
  assumes "nfa.nxt char_fa ([X \<rightarrow> \<alpha> . \<beta>]) a \<noteq> {}" 
  obtains \<gamma> where "\<beta> = a # \<gamma>" "(X, \<alpha>@\<beta>) \<in> Prods G'"
  using assms 
  by (metis (lifting) char_fa_nxt_neq_or_not_Prod_imp_empty item.case list.exhaust list.simps(4)
      nxt_char_fa)

lemma in_char_fa_nxt_imp_shift:
  assumes "q \<in> nfa.nxt char_fa p a"
  obtains X \<alpha> \<beta> where "p = [X \<rightarrow> \<alpha> . a # \<beta>]" "q = [X \<rightarrow> \<alpha> @ [a] . \<beta>]"
proof -
  obtain X \<alpha> \<beta> Y \<gamma> \<delta> where pq_defs: "p = [X \<rightarrow> \<alpha> . \<beta>]" "q = [Y \<rightarrow> \<gamma> . \<delta>]" 
    using item.exhaust by meson
  moreover with char_fa_nxt_nempty_imp_hd assms obtain \<zeta> where "\<beta> = a # \<zeta>" "(X, \<alpha>@\<beta>) \<in> Prods G'" 
    by blast
  moreover with char_fa_nxt_in_Prods_imp_singleton have "q = [X \<rightarrow> \<alpha> @ [a] . \<zeta>]"
    using assms pq_defs(1) by blast
  ultimately show thesis using that by presburger
qed

lemma eps_char_fa [simp]:
  "nfa.eps char_fa 
    = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G' \<and> (Y, \<gamma>) \<in> Prods G'}"
  unfolding char_fa_def by (meson nfa.select_convs(5))



sublocale char_fa: nfa char_fa 
proof (unfold_locales, goal_cases 1 2 nxt_closed 3)
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
qed (use G'_def It_defs It_finite[OF G'_finite] in fastforce)+



definition LR\<^sub>0 :: "(('n, 't) sym, ('n, 't) item set) dfa" where
  "LR\<^sub>0 \<equiv> nfa.Power_dfa char_fa"

sublocale canon_LR0: dfa LR\<^sub>0
  unfolding LR\<^sub>0_def by (rule char_fa.dfa_Power)

end


 

section \<open>NFA Configurations and Steps\<close>

context nfa 
begin

type_synonym ('b,'c) config = "'b \<times> 'c list"

inductive step :: "('s,'a) config \<Rightarrow> ('s,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 70) where
nxt[intro]:  "q \<in> nxt M p a \<Longrightarrow> (p,a#u) \<turnstile> (q,u)" |
eps[intro]:  "(p,q) \<in> eps M \<Longrightarrow> (p,w) \<turnstile> (q,w)"

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

abbreviation stepn  (\<open>_ \<turnstile>'(_') _\<close> 70) where
  "c0 \<turnstile>(n) c1 \<equiv> (step ^^ n) c0 c1"

abbreviation steps (infix \<open>\<turnstile>*\<close> 70) where
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

lemma stepn_indep:
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
    case (nxt a)
    then obtain y where u_decomp: "u = a # y" "x = y @ v" using n_steps 
      by (metis append_eq_Cons_conv impossible_Cons relpowp_imp_rtranclp steps_len_dec)
    hence "(p, u @ w) \<turnstile> (r, y @ w)" by (simp add: nxt(2) step.nxt)
    also note Suc.IH[OF n_steps(2)[unfolded u_decomp(2)]]
    finally show ?thesis .
  next
    case eps
    with Suc.IH n_steps(2) have "(r, u @ w) \<turnstile>(n) (q, w)" by blast
    then show ?thesis using eps_indep[OF n_steps(1)[unfolded eps(1)], of "u @ w"] 
      by (meson relpowp_Suc_I2)
  qed
qed


section \<open>\<epsilon>-Transitions\<close>

inductive eps_stepn :: "('s,'a) config \<Rightarrow> nat \<Rightarrow> ('s,'a) config \<Rightarrow> bool" (\<open>_ \<turnstile>\<epsilon>'(_') _\<close> 70) where
refl[intro]:  "(q,w) \<turnstile>\<epsilon>(0) (q,w)" |
nxt[intro]:  "\<lbrakk>(p,u) \<turnstile>\<epsilon>(n) (q,a#v); (q,a#v) \<turnstile> (r,v)\<rbrakk> \<Longrightarrow> (p,u) \<turnstile>\<epsilon>(n) (r,v)" |
eps[intro]:  "\<lbrakk>(p,u) \<turnstile>\<epsilon>(n) (q,v); (q,v) \<turnstile> (r,v)\<rbrakk> \<Longrightarrow> (p,u) \<turnstile>\<epsilon>(Suc n) (r,v)"


inductive_cases eps_stepn_reflE[elim]: "(q,w) \<turnstile>\<epsilon>(0) (q,w)"
inductive_cases eps_stepn_nxtE[elim]: "(q,a#u) \<turnstile>\<epsilon>(n) (r,u)"
inductive_cases eps_stepn_epsE[elim]: "(q,u) \<turnstile>\<epsilon>(n) (p,u)"


lemma step_is_eps_stepn:
  assumes "c0 \<turnstile> c1"
  shows "(c0 \<turnstile>\<epsilon>(0) c1) \<or> (c0 \<turnstile>\<epsilon>(Suc 0) c1)"
  using assms by cases auto


lemma steps_imp_eps_stepn:
  assumes "c0 \<turnstile>* c1"
  obtains n where "c0 \<turnstile>\<epsilon>(n) c1"
  using assms proof (induction arbitrary: thesis)
  case base
  then show ?case using eps_stepn.refl surj_pair by metis
next
  case (step c1 c2)
  then obtain n where "c0 \<turnstile>\<epsilon>(n) c1" by blast
  from step(2) show ?case 
    by cases
      ((smt (verit, best) eps_stepn.simps step_is_eps_stepn step),
     (metis step(2,3,4) nfa.eps_stepn.eps nfa_axioms old.prod.exhaust))
qed

lemma eps_stepn_imp_steps: "c0 \<turnstile>\<epsilon>(n) c1 \<Longrightarrow> c0 \<turnstile>* c1" 
  by (induction rule: eps_stepn.induct) auto

(* To be used in proof of Theorem 3.4.1 *)
lemma last_eps_step:
  assumes "(p,u) \<turnstile>\<epsilon>(Suc n) (s,w)"
  obtains q r v where "(p, u) \<turnstile>\<epsilon>(n) (q,v)" "(q,v) \<turnstile> (r,v)" "(r,v) \<turnstile>\<epsilon>(0) (s,w)"
  using assms proof (induction "length u - length w" arbitrary: s w rule: less_induct)
  case less 
  from less(3) show ?case 
  proof cases
    case (nxt q a)
    with steps_len_dec eps_stepn_imp_steps have  "length u \<ge> length (a#w)" by blast
    then have "length u - length (a#w) < length u - length w" by auto
    then show ?thesis using less nxt by blast
  qed (use less in blast)
qed


lemma noeps_eps_stepn_eq:
  "\<lbrakk>c1 \<turnstile>\<epsilon>(n) c2; c0 \<turnstile>\<epsilon>(0) c1\<rbrakk> \<Longrightarrow> c0 \<turnstile>\<epsilon>(n) c2"
proof (induction rule: eps_stepn.induct)
  case (refl q w)
  then show ?case .
next
  case (nxt p u n q a v r)
  show ?case using nxt(3)[OF nxt(4)] nxt(2) eps_stepn.nxt surj_pair by metis
next
  case (eps p u n q v r)
  show ?case using eps(3)[OF eps(4)] eps(2) eps_stepn.eps surj_pair by metis
qed

 
lemma eps_stepn_suc:
  "\<lbrakk>c1 \<turnstile>\<epsilon>(n) c2; c0 \<turnstile>\<epsilon>(Suc 0) c1\<rbrakk> \<Longrightarrow> c0 \<turnstile>\<epsilon>(Suc n) c2"
proof (induction rule: eps_stepn.induct)
  case (refl q w)
  then show ?case .
next
  case (nxt p u n q a v r)
  then show ?case by (metis nfa.eps_stepn.nxt nfa_axioms surj_pair) 
next
  case (eps p u n q v r)
  then show ?case using eps_stepn.cases by blast
qed


lemma eps_stepn_trans:
  "\<lbrakk>c0 \<turnstile>\<epsilon>(n) c1; c1 \<turnstile>\<epsilon>(m) c2\<rbrakk> \<Longrightarrow> c0 \<turnstile>\<epsilon>(n+m) c2"
proof (induction arbitrary: m rule: eps_stepn.induct)
  case (refl q w)
  then show ?case by simp
next
  case (nxt p u n q a v r)
  from nxt(2) have "(q, a # v) \<turnstile>\<epsilon>(0) (r,v)" by auto
  with nxt show ?case using noeps_eps_stepn_eq by blast
next
  case (eps p u n q v r)
  hence "(q,v) \<turnstile>\<epsilon>(Suc 0) (r,v)" by blast
  with eps(4) have "(q,v) \<turnstile>\<epsilon>(Suc m) c2" using eps_stepn_suc by presburger
  with eps show ?case by fastforce
qed

end

section \<open>Proving 3.4.1\<close>

context Extended_Cfg
begin

interpretation P: ipda G IPDA 
  by standard simp

corollary ipda_IPDA: 
  "ipda G IPDA"
  by (rule P.ipda_axioms)

notation char_fa.step (infix \<open>\<turnstile>c\<close> 70)
notation char_fa.steps (infix \<open>\<turnstile>c*\<close> 70)
notation char_fa.stepn (\<open>_ \<turnstile>c'(_') _\<close> 70)
notation char_fa.eps_stepn (\<open>_ \<turnstile>c\<epsilon>'(_') _\<close> 70)

type_synonym ('q,'s) ipda_config = "('q,'s) item list \<times> 's list"

abbreviation IPDA_step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>P\<close> 70) where
  "(\<turnstile>P) \<equiv> (ipda.step IPDA)"

abbreviation IPDA_steps :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>P*\<close> 70) where
  "(\<turnstile>P*) \<equiv> (ipda.steps IPDA)"

abbreviation IPDA_stepn :: "('n,'t) item list \<times> 't list \<Rightarrow> nat \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" ( \<open>_ \<turnstile>P'(_') _\<close> 70) where
  "c0 \<turnstile>P(n) c1 \<equiv> (ipda.stepn IPDA) c0 n c1"

lemma char_step_cases[consumes 1, case_names nxt eps, cases set: char_fa.step]:
  assumes "c0 \<turnstile>c c1"
  obtains 
    X \<alpha> Y \<beta> \<gamma> where "c0 = ([X \<rightarrow> \<alpha> . Y # \<beta>], Y # \<gamma>)" "c1 = ([X \<rightarrow> \<alpha> @ [Y] . \<beta>], \<gamma>)" 
                      "(X, \<alpha> @ Y # \<beta>) \<in> Prods G'" |
    X \<alpha> Y \<beta> \<delta> \<gamma> where "c0 = ([X \<rightarrow> \<alpha> . Nt Y # \<beta>], \<delta>)" "c1 = ([Y \<rightarrow> [] . \<gamma>], \<delta>)" "(Y, \<gamma>) \<in> Prods G'"
                      "(X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G'"
  using assms proof cases
  case (nxt q p a u)
  then show ?thesis using that(1) in_char_fa_nxt_imp_shift char_fa_nxt_neq_or_not_Prod_imp_empty 
    by (metis emptyE)
next
  case (eps p q w)
  then show ?thesis unfolding eps_char_fa using that(2) by blast
qed

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


lemma char_comp_imp_derivers:
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
        using n_steps nfa.stepn_indep[OF char_fa.nfa_axioms, of _ _ "\<delta> @ \<alpha>'" "[Y]" _ "[]"] 
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
        using reduced_derived_substring_imp_derives[OF _ G'_reduced G'_not_empty, of "\<zeta>@\<alpha>'@[Nt A]" \<beta>']
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



lemma derivers_imp_ipda_comp:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>@Nt A#map Tm w"
    "Prods G' \<turnstile> \<gamma>@Nt A#map Tm w \<Rightarrow>r \<gamma>@\<alpha>@\<beta>@map Tm w"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v"
  obtains \<rho> where 
    "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], v@w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])" 
    "hist \<rho> = \<gamma>"
  using assms(1) proof cases
  case rtrancl_refl
  with assms have eqs: "\<gamma> = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S]" 
    using S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
  then show thesis using S'_derive_imp_S P.deriver_imp_IPDA_comp assms that 
    by (metis P.hist_init P.init_symbol_ipda append.right_neutral append_Nil hist_singleton list.inject
        rtrancl_refl sym.inject(1))
next
  case (rtrancl_into_rtrancl b)
  then obtain n where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<gamma> @ Nt A # map Tm w" 
    by (meson relpowp_Suc_I rtranclp_imp_relpowp)
  from derivers_singleton_imp_rm_chain[OF this _ G'_reduced G'_not_empty] obtain \<rho> where 
    "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma> @ Nt A # map Tm w"
    using Nts_G'_is_union by blast
  then show ?thesis using assms that proof (induction \<rho> arbitrary: \<gamma> A w \<alpha> \<beta> v thesis)
    case Nil
    then have eqs: "\<gamma> = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S] \<and> A = S'" 
      using S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
    then show thesis using S'_derive_imp_S P.deriver_imp_IPDA_comp Nil
    by (metis P.hist_init P.init_symbol_ipda append.right_neutral append_Nil hist_singleton
        list.simps(8))
  next
    case (Cons i \<rho>)
    then obtain X \<alpha>' \<beta>' where 
      "i = [X \<rightarrow> \<alpha>' . Nt A # \<beta>']" 
      using rm_chain_imp_hd_prod_rightmost[OF Cons(2)]
      by (metis list.distinct(1) list.inject)
    with rm_chain_stepE Cons(2) obtain \<alpha>'' u v' where X_chain:
      "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha>'' @ Nt X # map Tm v'"
      "Prods G' \<turnstile> \<alpha>'' @ Nt X # map Tm v' \<Rightarrow>r \<alpha>'' @ \<alpha>' @ Nt A # \<beta>' @ map Tm v'"
      "Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm u" "u @ v' = w" "\<alpha>'' @ \<alpha>' = \<gamma>"
      by (smt (verit, best) append.assoc append_same_eq map_append right_derivs_eq_imp_eq_tl)
    then obtain \<rho>' where \<rho>'_def:
      "([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho>' @ [init_symbol IPDA], u@v') 
          \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
      "hist \<rho>' = \<alpha>''" 
      using Cons(1)[OF X_chain(1) rm_chain_imp_derivers[OF X_chain(1)], of "\<alpha>' @ [Nt A]" \<beta>']
      by (metis append.assoc append_Cons append_Nil derivers_imp_derives)
    let ?\<rho> = "[X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<rho>'"
    have hist_\<rho>: "hist ?\<rho> = \<gamma>" using X_chain(5) \<rho>'_def(2) by simp
    from P.derives_imp_completes[OF Cons(5)] have 
      "([A \<rightarrow> \<alpha> . \<beta>] # ?\<rho> @ [init_symbol IPDA], v @ w) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []] # ?\<rho> @ [init_symbol IPDA], w)"
      by (metis append.right_neutral)
    also have "... \<turnstile>P ([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho>' @ [init_symbol IPDA], u@v')"
      using X_chain(4) by auto
    also have "... \<turnstile>P* ([P.final_state, init_symbol IPDA], [])" using \<rho>'_def by presburger
    finally show ?case using hist_\<rho> Cons(6) by presburger
  qed
qed 


lemma ipda_reaches_final_imp_rm_chain:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
  obtains "\<rho> = []" |
    \<sigma> X \<alpha>' \<beta>' \<gamma> where "\<rho> = [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<sigma>" "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  sorry


lemma ipda_comp_imp_char_comp:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
  shows "([S' \<rightarrow> [] . [Nt S]], hist \<rho> @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
proof -
  from ipda_reaches_final_imp_rm_chain[OF assms(1)] show ?thesis
  proof cases
    case 1
    then show ?thesis using assms sorry
  next
    case (2 \<sigma> X \<alpha>' \<beta>' \<gamma>)
    then show ?thesis sorry
  qed

qed

corollary ipda_comp_imp_derivers:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
  obtains v where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* hist \<rho> @ Nt A # map Tm v" 
    "Prods G' \<turnstile> hist \<rho> @ Nt A # map Tm v \<Rightarrow>r hist \<rho> @ \<alpha> @ \<beta> @ map Tm v"
proof -
  note ipda_comp_imp_char_comp[OF assms(1)]
  from char_comp_imp_derivers[OF this] show thesis using that by blast
qed


corollary char_comp_imp_ipda_comp:
  assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
  obtains w \<rho> where 
    "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
    "\<gamma> = hist \<rho> @ \<alpha>"
proof -
  from char_comp_imp_derivers[OF assms(1)] obtain \<gamma>' w where deriv:
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w"
    "\<gamma> = \<gamma>' @ \<alpha>" by metis
  moreover from this obtain v where "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v" 
    using reduced_derived_substring_imp_derives[of G' "\<gamma>' @ \<alpha>" \<beta> "map Tm w", 
                                        OF _ G'_reduced G'_not_empty] G'_def append.assoc
    by (metis (no_types, lifting) Cfg.sel(2) derivers_imp_derives rtranclp.rtrancl_into_rtrancl)
  ultimately show thesis using derivers_imp_ipda_comp that by metis
qed




end

end
