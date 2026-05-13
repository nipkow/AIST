theory LR_Parser 
  imports 
    Item_Pushdown_Automata
    N_Pushdown_Automata
    Finite_Automata_HF.Finite_Automata_HF
    Rightmost_Chain
begin

context Extended_Cfg
begin

section \<open>char(G)\<close>

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

lemma char_fa_eps_subst_states:
  "nfa.eps char_fa \<subseteq> nfa.states char_fa \<times> nfa.states char_fa"
  using in_Prods_imp_in_It by force

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

end


 

section \<open>NFA Configurations and Steps\<close>

context nfa 
begin

type_synonym ('b,'c) config = "'b \<times> 'c list"

inductive step :: "('s,'a) config \<Rightarrow> ('s,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
nxt[intro]:  "q \<in> nfa.nxt M p a \<Longrightarrow> (p,a#u) \<turnstile> (q,u)" |
eps[intro]:  "(p,q) \<in> nfa.eps M \<Longrightarrow> (p,w) \<turnstile> (q,w)"

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

lemma steps_append:
  "(p, u @ v) \<turnstile>* (q, v) \<Longrightarrow> (p, u @ w) \<turnstile>* (q, w)"
  using stepn_append[THEN relpowp_imp_rtranclp] rtranclp_imp_relpowp by metis

lemma in_epsclo_imp_reachable:
  assumes "q \<in> epsclo Q"
  obtains p where "p \<in> Q" "(p, w) \<turnstile>* (q, w)"
proof -
  from assms obtain p where "p \<in> Q" "(p, q) \<in> (eps M)\<^sup>*"
    unfolding epsclo_def by blast
  from this(2) show thesis
    using that by (induction arbitrary: thesis) 
      (use \<open>p \<in> Q\<close> in simp, metis eps rtranclp.simps)
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
  then obtain p where p_defs: "p \<in> (\<Union>q \<in> epsclo Q. nxt M q a)" "(p, w) \<turnstile>* (q, [])"
    using nextl.simps(2) by metis
  then obtain r where r_defs: "r \<in> epsclo Q" "p \<in> nxt M r a" by blast
  with in_epsclo_imp_reachable obtain s where "s \<in> Q" "(s, a#w) \<turnstile>* (r, a#w)" by blast
  note this(2)
  also from r_defs have "(r, a#w) \<turnstile> (p, w)" by blast
  also note p_defs(2)
  finally show ?case using \<open>s \<in> Q\<close> Cons by fast
qed

lemma reachable_imp_in_nextl:
  assumes "p \<in> states M"
    "eps M \<subseteq> states M \<times> states M"
    "(p, w) \<turnstile>* (q, [])"
  shows "q \<in> nextl {p} w"
  using assms(3,1) proof (induction rule: converse_rtranclp_induct2)
  case refl
  then show ?case using epsclo_def by simp
next
  case (step p u r v)
  from step(1) show ?case
  proof cases
    case (nxt a)
    with nfa.nxt[OF nfa_axioms step(4)] step have q_in_nextl_r: "q \<in> nextl {r} v" 
      by blast                                            
    have "nextl {p} u = nextl (\<Union>q\<in>epsclo {p}. nxt M q a) v"    
      using nxt(1) nextl.simps(2) by blast
    with nxt have "nextl {r} v \<subseteq> nextl {p} u" 
      by (metis (mono_tags, lifting) Int_insert_left_if1 UN_I empty_subsetI insert_subset nextl_mono
          nfa.epsclo_increasing nfa_axioms step.prems)
    then show ?thesis using q_in_nextl_r by blast 
  next
    case eps
    hence r_subst_p: "epsclo {r} \<subseteq> epsclo {p}"
      unfolding epsclo_def by auto
    from eps step(3) assms have q_in_nextl_r: "q \<in> nextl {r} u" by blast
    also have "... = nextl (epsclo {r}) u" by simp
    also from r_subst_p have "... \<subseteq> nextl (epsclo {p}) u" 
      using nextl_mono by presburger
    also have "... = nextl {p} u" by simp
    finally show ?thesis .
  qed
qed


lemma eps_states_imp_language_eq_init_final_reachable:
  assumes "eps M \<subseteq> states M \<times> states M"
  shows "language = {w. \<exists>q\<^sub>0 \<in> nfa.init M. \<exists>f \<in> nfa.final M. (q\<^sub>0, w) \<turnstile>* (f, [])}"
  (is "_ = ?r")
proof 
  show "language \<subseteq> ?r"
    using in_nextl_imp_reaches unfolding language_def by force
  show "?r \<subseteq> language"
    using reachable_imp_in_nextl[OF _ assms] unfolding language_def 
    by (smt (verit, del_insts) Collect_mono IntI Set.set_insert empty_subsetI init insert_subset
        nextl_mono) 
qed

end

section \<open>Equivalences between \<open>char(G)\<close>, \<open>IPDA\<close>, and rightmost derivations\<close>

context Extended_Cfg
begin

interpretation P: ipda G IPDA 
  by standard simp

corollary ipda_IPDA: 
  "ipda G IPDA"
  by (rule P.ipda_axioms)

notation char_fa.step (infix \<open>\<turnstile>c\<close> 55)
notation char_fa.steps (infix \<open>\<turnstile>c*\<close> 55)
notation char_fa.stepn (\<open>_ \<turnstile>c'(_') _\<close> 55)

type_synonym ('q,'s) ipda_config = "('q,'s) item list \<times> 's list"

abbreviation IPDA_step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>P\<close> 55) where
  "(\<turnstile>P) \<equiv> (ipda.step IPDA)"

abbreviation IPDA_steps :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>P*\<close> 55) where
  "(\<turnstile>P*) \<equiv> (ipda.steps IPDA)"

abbreviation IPDA_stepn :: "('n,'t) item list \<times> 't list \<Rightarrow> nat \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" ( \<open>_ \<turnstile>P'(_') _\<close> 55) where
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
  from derivers_singleton_imp_rm_chain[OF this] obtain \<rho> where 
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
    then obtain X \<alpha>' \<beta>' where X_defs:
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
    from X_defs have X_in_prods: "(X, \<alpha>' @ Nt A # \<beta>') \<in> Prods G'"
      by (metis Cons.prems(1) rm_chain_imp_prod)
    let ?\<rho> = "[X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<rho>'"
    have hist_\<rho>: "hist ?\<rho> = \<gamma>" using X_chain(5) \<rho>'_def(2) by simp
    from Cons(4) have A_in_prods: "(A, \<alpha> @ \<beta>) \<in> Prods G'" 
      by (simp add: deriver_imp_in_Prods)
    with P.derives_imp_completes[OF Cons(5)] have 
      "([A \<rightarrow> \<alpha> . \<beta>] # ?\<rho> @ [init_symbol IPDA], v @ w) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []] # ?\<rho> @ [init_symbol IPDA], w)"
      by (metis append.right_neutral)
    also have "... \<turnstile>P ([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho>' @ [init_symbol IPDA], u@v')"
      using X_chain(4) A_in_prods X_in_prods by simp
    also have "... \<turnstile>P* ([P.final_state, init_symbol IPDA], [])" using \<rho>'_def by presburger
    finally show ?case using hist_\<rho> Cons(6) by presburger
  qed
qed 

text \<open>Towards step 3\<close>

lemma ipda_reaches_final_imp_rm_chain:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
  obtains "\<rho> = []" |
    \<sigma> X \<alpha>' \<beta>' \<gamma> where "\<rho> = [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<sigma>" "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  using assms proof (induction "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w)" arbitrary: A \<alpha> \<beta> \<rho> w thesis
                      rule: converse_rtranclp_induct)
  case (step z)
  from P.step_imp_in_It this(1) have A_in_It: "[A \<rightarrow> \<alpha> . \<beta>] \<in> It G'" 
    using P.step_imp_not_Nil by (smt (verit, ccfv_SIG) P.step_cases)
  from P.step_app_init_symbol_preserved step(1) obtain B \<gamma> \<delta> \<tau> v where z\<tau>_def:
    "z = ([B \<rightarrow> \<gamma> . \<delta>] # \<tau> @ [init_symbol IPDA], v)" using prod.exhaust by metis
  note step(3)[OF this] 
  then show thesis
  proof (cases, goal_cases Nil chain)
    case Nil
    with z\<tau>_def have z_B_init: "z = ([[B \<rightarrow> \<gamma> . \<delta>], init_symbol IPDA], v)" by blast
    with step(2) P.reaches_without_stack_imp_S' consider 
      "[B \<rightarrow> \<gamma> . \<delta>] = init_state IPDA" |
      "[B \<rightarrow> \<gamma> . \<delta>] = P.final_state" by blast
    then show thesis
    proof cases
      case 2
      note step(1)[unfolded z_B_init this] 
      note P.step_reaches_final_imp_S[OF this]
      then show ?thesis using step(5) G'_derive_S derive_singleton_imp_singleton_chain by force
    qed (use step(1) in cases, use step z_B_init in auto)
  next
    case (chain X \<alpha>' \<beta>' \<sigma> \<zeta>)
    from step(1)[unfolded z\<tau>_def] show ?thesis proof cases
      case (reduce Y \<eta> X' \<theta> \<iota> \<upsilon> x)
      hence BA_in_prods: "(B, \<theta> @ Nt A # \<delta>) \<in> Prods G'"
        using step(1) z\<tau>_def P.step_imp_in_Prods by force 
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


lemma char_steps_consume:
  "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G' \<Longrightarrow> ([A \<rightarrow> \<alpha> . \<beta> @ \<gamma>], \<beta> @ \<delta>) \<turnstile>c* ([A \<rightarrow> \<alpha> @ \<beta> . \<gamma>], \<delta>)"
proof (induction \<beta> arbitrary: \<alpha>)
  case (Cons X \<beta>)
  hence "([A \<rightarrow> \<alpha> . (X # \<beta>) @ \<gamma>], (X # \<beta>) @ \<delta>) \<turnstile>c ([A \<rightarrow> \<alpha> @ [X] . \<beta> @ \<gamma>], \<beta> @ \<delta>)" by auto
  also from Cons.IH[of "\<alpha> @ [X]"] have "... \<turnstile>c* ([A \<rightarrow> \<alpha> @ X # \<beta> . \<gamma>], \<delta>)" 
    using Cons.prems by simp
  finally show ?case .
qed simp


text \<open>Step 3: If the configuration \<open>([A \<rightarrow> \<alpha>.\<beta>]\<rho>, w)\<close> is accepted by the \<open>IPDA\<close>, the configuration
     \<open>([A \<rightarrow> \<alpha>.\<beta>], \<epsilon>)\<close> is reachable by \<open>char(G)\<close> with input \<open>hist(\<rho>)\<alpha>\<close>.\<close>

lemma ipda_imp_char:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
  shows "([S' \<rightarrow> [] . [Nt S]], hist \<rho> @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
using assms proof (induction \<rho> arbitrary: A \<alpha> \<beta> w)
  case Nil
  with P.reaches_without_stack_imp_S' consider (init) "[A \<rightarrow> \<alpha> . \<beta>] = [S' \<rightarrow> [] . [Nt S]]" | 
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
  from P.reaches_final_imp_completes[OF Cons(2)] obtain v where A_complete:
    "([A \<rightarrow> \<alpha> . \<beta>] # (i # \<rho>) @ [init_symbol IPDA], w) 
      \<turnstile>P* ([A \<rightarrow> \<alpha> @ \<beta> . []] # (i # \<rho>) @ [init_symbol IPDA], v)"
    "([A \<rightarrow> \<alpha> @ \<beta> . []] # (i # \<rho>) @ [init_symbol IPDA], v) 
      \<turnstile>P* ([P.final_state, init_symbol IPDA], [])" by blast
  have A_in_Prods: "(A, \<alpha>@\<beta>) \<in> Prods G'"
    using P.steps_neq_in_It[OF A_complete(2)] in_Prods_eq_in_It by force
  have "([A \<rightarrow> \<alpha> @ \<beta> . []] # (i # \<rho>) @ [init_symbol IPDA], v)
       \<turnstile>P ([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho> @ [init_symbol IPDA], v)"
    using chain A_in_Prods X_in_Prods by auto
  with P.step_not_expanding_imp_reaches[OF this] A_complete have 
    "... \<turnstile>P* ([P.final_state, init_symbol IPDA], [])" 
    by (metis (no_types, lifting) P.complete_S'_step_impossible P.step_not_expanding_unique
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

lemma char_imp_ipda:
  assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
  obtains w \<rho> where 
    "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
    "\<gamma> = hist \<rho> @ \<alpha>"
proof -
  from char_imp_derivers[OF assms(1)] obtain \<gamma>' w where deriv:
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w"
    "Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w"
    "\<gamma> = \<gamma>' @ \<alpha>" by metis
  moreover from this obtain v where "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v" 
    using reduced_derives_imp_substring_derives_Tms[of G' "\<gamma>' @ \<alpha>" \<beta> "map Tm w", 
                                        OF _ G'_reduced G'_not_empty] G'_def append.assoc
    by (metis (no_types, lifting) Cfg.sel(2) derivers_imp_derives rtranclp.rtrancl_into_rtrancl)
  ultimately show thesis using derivers_imp_ipda that by metis
qed

corollary char_eq_ipda:
  "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], []) 
  = (\<exists>w \<rho>. ([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], []) \<and>
    \<gamma> = hist \<rho> @ \<alpha>)"
  using char_imp_ipda ipda_imp_char by metis

lemma derivers_imp_char:
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


text \<open>\<open>\<gamma>\<close> is a reliable prefix to \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> if there exists a rightmost derivation
      \<open>S' \<Rightarrow>r* \<gamma>'Aw \<Rightarrow>r \<gamma>'\<alpha>\<beta>w\<close> with \<open>\<gamma> = \<gamma>'\<alpha>\<close>:\<close>

definition reliable_prefix :: "('n, 't) item \<Rightarrow> ('n, 't) syms \<Rightarrow> bool" where
  "reliable_prefix i \<gamma> \<equiv> case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> 
      \<exists>\<gamma>' w. Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w \<and> 
             Prods G' \<turnstile> \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w \<and>
      \<gamma> = \<gamma>' @ \<alpha>"

text \<open>The words on which \<open>char(G)\<close> reaches \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close> are exactly the reliable 
     prefixes for \<open>[A \<rightarrow> \<alpha>.\<beta>]\<close>:\<close>

corollary char_eq_reliable_prefix:
  "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], []) = reliable_prefix ([A \<rightarrow> \<alpha> . \<beta>]) \<gamma>"
  using char_imp_derivers derivers_imp_char 
  unfolding reliable_prefix_def by fastforce

text \<open>\<open>char(G)\<close> accepts the set of reliable prefixes to complete items:\<close>

corollary char_lang_is_realiable_prefixes_of_complete_items:
  "char_fa.language = {\<gamma>. \<exists>A \<alpha>. [A \<rightarrow> \<alpha> . []] \<in> It G' \<and> reliable_prefix ([A \<rightarrow> \<alpha> . []]) \<gamma>}"
proof -
  note char_fa.eps_states_imp_language_eq_init_final_reachable[OF char_fa_eps_subst_states]
  thus ?thesis
    using char_eq_reliable_prefix by fastforce
qed

(* Attempts to prove equivalence of IPDA and derivers for fixed w (needed?) *)

lemma ipda_comp_imp_derivers:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
  obtains u v where "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u" "w = u @ v" 
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* hist \<rho> @ Nt A # map Tm v" 
proof (cases \<rho>)
  case Nil
  with P.reaches_without_stack_imp_S' assms have 
    "[A \<rightarrow> \<alpha> . \<beta>] = init_state IPDA \<or> [A \<rightarrow> \<alpha> . \<beta>] = P.final_state" 
    by simp
  then show ?thesis 
  proof (standard, goal_cases init final)
    case init
    with assms have "w \<in> P.Lang"using Nil 
      by (simp add: P.Lang_def)
    with P.Lang_eq_Lang_G Lang_preserved have "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w"
      unfolding Lang_def using init G_derives_imp_G'_derives by simp
    then show ?case using that[of _ "[]"] init  by (simp add: Nil)
  next
    case final
    then show ?case using that Nil P.complete_S'_steps_refl assms by force
  qed
next
  case (Cons i \<sigma>)
  then show ?thesis oops

lemma ipda_reaches_final_imp_rm_chain_new:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<sigma> @ [init_symbol IPDA], w) 
    \<turnstile>P* ([P.final_state, init_symbol IPDA], [])"
  shows  "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<sigma> \<Rightarrow>r* hist \<sigma> @ \<alpha>' @ Nt A # map Tm w"
  using assms proof (induction "([A \<rightarrow> \<alpha> . \<beta>] # [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<sigma> @ [init_symbol IPDA], w)" 
    arbitrary: A \<alpha> \<beta> X \<alpha>' \<beta>' \<sigma> w rule: converse_rtranclp_induct)
  case (step z)
  from P.step_imp_in_It this(1) have A_in_It: "[A \<rightarrow> \<alpha> . \<beta>] \<in> It G'" 
    using P.step_imp_not_Nil by (smt (verit, ccfv_SIG) P.step_cases)
  note step(1)
  then show ?case
  proof cases
    case (shift A' \<gamma> a \<delta> i \<rho> u)
    hence "z = ([A \<rightarrow> \<alpha> @ [Tm a] . \<delta>] # [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<sigma> @ [init_symbol IPDA], u)"
      by blast
    note step(3)[OF this] 
    then show ?thesis using step \<proof>
  next
    case (reduce Y \<alpha> X \<beta> \<gamma> \<rho> w)
    then show ?thesis \<proof>
  next
    case (expand Y \<alpha> X \<beta> \<gamma> i \<rho> w)
    then show ?thesis oops
(* qed simp *)

lemma ipda_comp_eq_derivers:
  "(\<exists>\<rho>. ([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* ([P.final_state, init_symbol IPDA], []) \<and>
    hist \<rho> = \<gamma>)
  = (\<exists>u v. w = u @ v \<and> Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u 
    \<and> Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm v
    \<and> Prods G' \<turnstile> \<gamma> @ Nt A # map Tm v \<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm v)" (is "?ipda = ?derivers")
proof
  assume ipda: ?ipda
  hence "(A, \<alpha> @ \<beta>) \<in> Prods G'"
    by (metis append.assoc char_imp_derivers deriver_imp_in_Prods ipda_imp_char)
  hence "\<forall> \<gamma> w. Prods G' \<turnstile> \<gamma> @ Nt A # map Tm w \<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm w"
    using deriver.intros by fastforce
  with ipda show ?derivers (* using ipda_comp_imp_derivers *) \<proof>
next
  assume ?derivers
  then obtain u v where "w = u @ v" 
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm v" 
    "Prods G' \<turnstile> \<gamma> @ Nt A # map Tm v \<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    by blast
  from this(1) derivers_imp_ipda[OF this(2-)] show ?ipda oops 

section \<open>The Canonical LR(0) Automaton and Parser\<close>

definition LR\<^sub>0 :: "(('n, 't) sym, ('n, 't) item set) dfa" where
  "LR\<^sub>0 \<equiv> nfa.Power_dfa char_fa"

sublocale dfa_LR0: dfa LR\<^sub>0
  unfolding LR\<^sub>0_def by (rule char_fa.dfa_Power)

definition P\<^sub>0 :: "(('n, 't) item set, 't) npda" where
  "P\<^sub>0 \<equiv> let 
  \<Delta>\<^sub>G = dfa.nxt LR\<^sub>0;
  q\<^sub>0 = dfa.init LR\<^sub>0;
  f = {[S' \<rightarrow> [] . []]};
  \<Delta>\<^sub>0 = (\<lambda>qs a. case qs of [q] \<Rightarrow> if \<Delta>\<^sub>G q (Tm a) \<noteq> {} then {\<Delta>\<^sub>G q (Tm a) # [q]} else {} | _ \<Rightarrow> {});
  \<E> = {let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, \<Delta>\<^sub>G q (Nt X) # [q])| 
       q\<^sub>n qs X \<alpha>. [X \<rightarrow> \<alpha> . []] \<in> q\<^sub>n \<and> length \<alpha> = length qs} \<union>
      {([q, q\<^sub>0], [f])|q. [S' \<rightarrow> [Nt S] . []] \<in> q}
 in
  \<lparr>npda.states = dfa.states LR\<^sub>0 \<union> {f}, init = q\<^sub>0,  
    final = {f}, nxt = \<Delta>\<^sub>0, eps = \<E>\<rparr>"

lemma states_P0: 
  "npda.states P\<^sub>0 = dfa.states LR\<^sub>0 \<union> {{[S' \<rightarrow> [] . []]}}"
  unfolding P\<^sub>0_def by (meson npda.select_convs(1))

lemma init_P0: 
  "npda.init P\<^sub>0 = dfa.init LR\<^sub>0"
  unfolding P\<^sub>0_def by (meson npda.select_convs(2))

lemma final_P0:
  "npda.final P\<^sub>0 = {{[S' \<rightarrow> [] . []]}}"
  unfolding P\<^sub>0_def by (meson npda.select_convs(3))

lemma nxt_P0:
  "npda.nxt P\<^sub>0 = (\<lambda>qs a. case qs of [q] \<Rightarrow> if dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {} 
    then {dfa.nxt LR\<^sub>0 q (Tm a) # [q]} else {} | _ \<Rightarrow> {})"
  unfolding P\<^sub>0_def by (meson npda.select_convs(4))



lemma eps_P0:
  "npda.eps P\<^sub>0 = 
  {let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, dfa.nxt LR\<^sub>0 q (Nt X) # [q])|
    q\<^sub>n qs X \<alpha>. [X \<rightarrow> \<alpha> . []] \<in> q\<^sub>n \<and> length \<alpha> = length qs} \<union>
  {([q, dfa.init LR\<^sub>0], [{[S' \<rightarrow> [] . []]}])|q. [S' \<rightarrow> [Nt S] . []] \<in> q}"
  unfolding P\<^sub>0_def by (meson npda.select_convs(5))

lemmas P\<^sub>0_simps [simp] = states_P0 init_P0 final_P0 nxt_P0 eps_P0

lemma P0_nxt_nempty_imp_LR0_nxt_set:
  assumes "npda.nxt P\<^sub>0 qs a \<noteq> {}"
  obtains q where "qs = [q]" "npda.nxt P\<^sub>0 qs a = {dfa.nxt LR\<^sub>0 q (Tm a) # [q]}"
    "dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}"
proof -
  consider "qs = []" | q where "qs = [q]" | p q qs' where "qs = p#q#qs'"
    using list.exhaust by metis
  then show thesis
    using that assms by cases (auto split: if_splits)
qed

interpretation P0: npda P\<^sub>0
proof (unfold_locales, goal_cases _ _ nxt eps _)
  case (nxt ps qs a)
  with P0_nxt_nempty_imp_LR0_nxt_set obtain p where p_def: "ps = [p]"
    "npda.nxt P\<^sub>0 ps a = {[dfa.nxt LR\<^sub>0 p (Tm a), p]}" "dfa.nxt LR\<^sub>0 p (Tm a) \<noteq> {}"
    by force
  let ?q = "dfa.nxt LR\<^sub>0 p (Tm a)"
  from dfa_LR0.nxt nxt p_def have "?q \<in> dfa.states LR\<^sub>0"
    sorry
(* Needs case distinction. Prove that if final nxt is empty, therefore p must be in Q\<^sub>G. *)
    
  then show ?case using P0_nxt_nempty_imp_LR0_nxt_set dfa_LR0.nxt 
next
  case (eps ps qs)
  then show ?case sorry
qed (simp add: dfa_LR0.finite)+

end


section \<open>LR(k) Grammars\<close>

(* TODO: P\<^sub>0, LR(0)-(in)adequate states *)

definition LR :: "nat \<Rightarrow> ('n::fresh0, 't) Cfg \<Rightarrow> bool" where
  "LR k G \<equiv> \<forall>\<alpha> X \<beta> w \<gamma> Y x y. 
    Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w \<and> 
                        Prods G \<turnstile> \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w \<and> 
    Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x \<and> 
                        Prods G \<turnstile> \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y \<and> 
    take k w = take k y \<longrightarrow> \<alpha> = \<gamma> \<and> X = Y \<and> x = y"
  

end
