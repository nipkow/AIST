theory Item_Pushdown_Automata
  imports 
    Extended_Cfg
    Pushdown_Automata.Pushdown_Automata
begin

 (* Better? *)
(* locale ipda = Extended_Cfg G for G :: "('n::fresh0, 't) Cfg" +
  fixes M :: "(('n, 't) item, 't, ('n, 't) item) pda"
  assumes init_state:   "init_state M = [S' \<rightarrow> [] . [Nt S]]"
      and init_symbol:  "init_symbol M = [S' \<rightarrow> [] . []]"
      and final_states: "final_states M = {[S' \<rightarrow> [Nt S] . []]}"
      and delta:        "delta M = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
           if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {})"
      and delta_eps:    "delta_eps M = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> Prods G'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})" *)



context Extended_Cfg
begin

definition IPDA :: "(('n, 't) item, 't, ('n, 't) item) pda" where
  "IPDA \<equiv> let
    P = Prods G';
    \<delta> = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {});
    \<E> = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> P} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})         
in
  \<lparr>init_state = [S' \<rightarrow> [] . [Nt S]], init_symbol = [S' \<rightarrow> [] . []], 
    final_states = {[S' \<rightarrow> [Nt S] . []]}, delta = \<delta>, delta_eps = \<E>\<rparr>"

lemma init_state_IPDA [simp]:
  "init_state IPDA = [S' \<rightarrow> [] . [Nt S]]"
  unfolding IPDA_def by simp

lemma init_symbol_IPDA [simp]:
  "init_symbol IPDA = [S' \<rightarrow> [] . []]"
  unfolding IPDA_def by simp

lemma final_states_IPDA [simp]:
  "final_states IPDA = {[S' \<rightarrow> [Nt S] . []]}"
  unfolding IPDA_def by simp

lemma delta_IPDA [simp]:
  "delta IPDA = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {})"
  unfolding IPDA_def by auto

lemma delta_eps_IPDA [simp]:
  "delta_eps IPDA = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> Prods G'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})"
  unfolding IPDA_def by simp

lemma delta_complete_empty [simp]:
  "delta IPDA ([X \<rightarrow> \<alpha> . []]) a q = {}"
  unfolding IPDA_def by simp

lemma delta_Nt_empty [simp]:
  "delta IPDA ([X \<rightarrow> \<alpha> . Nt A # \<gamma>]) a q = {}"
  unfolding IPDA_def by auto

lemma delta_Tm_neq_empty [simp]:
  assumes "a \<noteq> b"
  shows "delta IPDA ([X \<rightarrow> \<alpha> . Tm a # \<gamma>]) b q = {}"
  using assms unfolding IPDA_def by simp

lemma delta_nempty_impl_Tm_eq:
  assumes "delta IPDA p a q \<noteq> {}"
  obtains X \<beta> \<gamma> where "p = [X \<rightarrow> \<beta> . Tm a # \<gamma>]"
proof -
  obtain X \<beta> \<alpha> where p_def: "p = [X \<rightarrow> \<beta> . \<alpha>]" using item.exhaust by blast
  then consider (Nil) "\<alpha> = []" | (Tm_eq) \<gamma> where "\<alpha> = Tm a # \<gamma>" | 
   (Tm_neq) a' \<gamma> where "\<alpha> = Tm a' # \<gamma>" "a' \<noteq> a" | (Nt) A \<gamma> where "\<alpha> = Nt A # \<gamma>"
    using list.exhaust sym.exhaust by metis
  then show thesis using p_def assms that by cases auto
qed

lemma delta_eps_Tm_empty [simp]:
   "delta_eps IPDA ([X \<rightarrow> \<alpha> . Tm a # \<gamma>]) q = {}"
  unfolding IPDA_def by simp

lemma delta_eps_Nt_neq_empty [simp]:
  assumes "Y \<noteq> Y'"
  shows "delta_eps IPDA ([Y \<rightarrow> \<alpha> . []]) ([X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) = {}"
  using assms unfolding IPDA_def by simp

(* TODO: case nempty? *)
lemma delta_eps_nempty_impl_expanding_or_reducing:
  assumes "delta_eps IPDA "


type_synonym ('q,'s) ipda_config = "'q list \<times> 's list"

lemmas init_defs = init_state_def init_symbol_def

abbreviation "final_state \<equiv> [S' \<rightarrow> [Nt S] . []]"

lemma in_final_impl_final_state:
  assumes "q \<in> final_states IPDA"
  shows "q = final_state"
  using assms unfolding IPDA_def S'_def S_def by simp

lemma final_state_in_final[simp]:
  "final_state \<in> final_states IPDA"
  unfolding IPDA_def S'_def S_def by simp



lemma delta_init_empty:
  "delta IPDA (init_state IPDA) a (init_symbol IPDA) = {}"
proof -
  let ?\<delta> = "(\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {})"
  have delta: "?\<delta> = delta IPDA"  unfolding IPDA_def by simp
  from init_state_def have "?\<delta> (init_state IPDA) a (init_symbol IPDA) = {}" 
    by auto
  with ext delta show ?thesis  by (metis (lifting))
qed

inductive step :: "(('n,'t) item,'t) ipda_config \<Rightarrow> (('n,'t) item,'t) ipda_config \<Rightarrow> bool" (infix \<open>\<turnstile>P\<close> 70) where
delta[intro]: "\<lbrakk>\<alpha> = [p0, p1]; \<alpha>' = q#qs; (q,qs) \<in> delta IPDA p0 a p1\<rbrakk> 
                \<Longrightarrow> (\<alpha>@\<beta>,a#w) \<turnstile>P (\<alpha>'@\<beta>,w)" |
eps[intro]: "\<lbrakk>\<alpha> = [p0, p1]; \<alpha>' = q#qs; (q,qs) \<in> delta_eps IPDA p0 p1\<rbrakk> 
                \<Longrightarrow> (\<alpha>@\<beta>, w) \<turnstile>P (\<alpha>'@\<beta>, w)"

inductive_cases step_deltaE[elim]: "(s, x#w) \<turnstile>P (s', w)"
inductive_cases step_epsE[elim]: "(s, w) \<turnstile>P (s', w)"

lemma step_equal_or_Cons:
  assumes "(p,u) \<turnstile>P (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile>P (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_Cons[OF assms] by fastforce



lemma shifting[simp]:
  "([A \<rightarrow> \<alpha> . Tm a # \<beta>]#\<rho>#\<rho>s, a#u) \<turnstile>P ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#\<rho>#\<rho>s, u)"
proof -
  have "([A \<rightarrow> \<alpha>@[Tm a] . \<beta>], [\<rho>]) \<in> delta IPDA ([A \<rightarrow> \<alpha> . Tm a # \<beta>]) a \<rho>"
    using IPDA_def by simp
  then show ?thesis using delta 
    by (metis Cons_eq_appendI append.left_neutral)
qed


lemma reducing[simp]:
  "([Y \<rightarrow> \<alpha> . []]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>, w) \<turnstile>P ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]#\<rho>, w)"
proof -
  have "([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>], []) \<in> delta_eps IPDA ([Y \<rightarrow> \<alpha> . []]) ([X \<rightarrow> \<beta> . Nt Y#\<gamma>])"
    unfolding IPDA_def by simp
  thus ?thesis using eps by (metis Cons_eq_appendI append.left_neutral)
qed

lemma expanding_in_delta_eps:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([Y \<rightarrow> [] . \<alpha>], [[X \<rightarrow> \<beta> . Nt Y#\<gamma>], i]) \<in> delta_eps IPDA ([X \<rightarrow> \<beta> . Nt Y#\<gamma>]) i"
  using assms unfolding G'_def S'_def S_def IPDA_def by auto

lemma expanding[simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w) \<turnstile>P ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
  using expanding_in_delta_eps[OF assms] eps 
  by (metis eq_Nil_appendI Cons_eq_appendI)

lemma in_delta_impl_shifting:
  assumes "(q, qs) \<in> delta IPDA p0 a p1"
  obtains X \<beta> \<gamma> where "p0 = [X \<rightarrow> \<beta> . Tm a # \<gamma>]"
    "(q,qs) = ([X \<rightarrow> \<beta> @ [Tm a] . \<gamma>], [p1])"
proof -
  from assms have nempty: "delta IPDA p0 a p1 \<noteq> {}" by auto
  let ?\<delta> = "(\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {})"
  have \<delta>_def: "?\<delta> = delta IPDA" unfolding IPDA_def by simp
  from delta_nempty_impl_Tm_eq[OF nempty] 
    obtain X \<beta> \<gamma> where p0_def: "p0 = [X \<rightarrow> \<beta> . Tm a # \<gamma>]" 
    by blast
  hence "?\<delta> p0 a p1 = {([X \<rightarrow> \<beta> @ [Tm a] . \<gamma>], [p1])}" by simp
  with assms show thesis using \<delta>_def that p0_def 
    by (metis (lifting) singletonD)
qed

lemma eps_cases[consumes 1, case_names reducing expanding]:
  assumes "(q0,q1) \<in> delta_eps IPDA p0 p1"
  obtains Y \<alpha> X \<beta> \<gamma> where
    "p0 = [Y \<rightarrow> \<alpha> . []]" "p1 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "q0 = [X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]" "q1 = []" |
    X \<beta> Y \<gamma> \<alpha> where
    "p0 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(Y, \<alpha>) \<in> Prods G'" "q0 = [Y \<rightarrow> [] . \<alpha>]" "q1 = [p0]" 
proof -
  let ?\<delta> = "(\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> Prods G'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})"
  have "delta_eps IPDA = ?\<delta>"
    using delta_eps_IPDA S_def S'_def G'_def by fastforce
  with assms
  show thesis sorry
qed

lemma step_cases[consumes 1, case_names shifting reducing expanding]:
  assumes "c0 \<turnstile>P c1"
obtains A \<alpha> a \<beta> i \<rho> u where 
    "c0 = ([A \<rightarrow> \<alpha> . Tm a # \<beta>]#i#\<rho>, a#u)" "c1 = ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#i#\<rho>, u)" |
    Y \<alpha> X \<beta> \<gamma> \<rho> w where
      "c0 = ([Y \<rightarrow> \<alpha> . []]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>, w)"  "c1 = ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]#\<rho>, w)" |
    Y \<alpha> X \<beta> \<gamma> i \<rho> w where 
    "c0 = ([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"  "c1 = ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
      "(Y, \<alpha>) \<in> Prods G'"
  using assms proof cases
  case (delta \<alpha> p0 p1 \<alpha>' q qs a \<beta> w)
  thm IPDA_def
  from in_delta_impl_shifting[OF delta(5)] obtain X \<beta>' \<gamma> where "p0 = [X \<rightarrow> \<beta>' . Tm a # \<gamma>]" 
    "(q,qs) = ([X \<rightarrow> \<beta>' @ [Tm a] . \<gamma>], [p1])" by blast
  then show ?thesis using that delta by simp 
next
  case (eps \<alpha> p0 p1 \<alpha>' q qs \<beta> w)
  from eps(5) show ?thesis 
    by (cases rule: eps_cases) 
      (use eps that in simp, 
        use expanding_in_delta_eps eps_cases in blast)
qed

lemma step_impl_in_It:
  assumes "i \<in> It G'"
    "(i#is, u) \<turnstile>P (j#js, v)"
  shows "j \<in> It G'"
  using [[simp_trace]]
  using assms(2) apply (cases rule: step_cases)
  using assms apply (simp_all add: items_of_Prods_def)[2]
  using assms sorry 


lemma 
  assumes "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>, u) \<turnstile>P c"
  shows "Prods G' \<turnstile> [Nt A] \<Rightarrow> \<alpha>@\<beta>"
  using assms apply cases
  sorry


abbreviation steps (infix \<open>\<turnstile>P*\<close> 70) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

abbreviation stepn ( \<open>_ \<turnstile>P'(_') _\<close> 70) where
  "stepn c0 n c1 \<equiv> (step ^^ n) c0 c1"

lemma steps_len_dec:
  "(p,u) \<turnstile>P* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by ((induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct),
  (use step_len_dec surj_pair le_trans in fastforce)+)

lemma syms_complete:
  "([A \<rightarrow> \<alpha> . map Tm u @ \<beta>]#i#is, u@v) \<turnstile>P* ([A \<rightarrow> \<alpha> @ map Tm u . \<beta>]#i#is, v)"
proof (induction u arbitrary: \<alpha>)
  case (Cons a u)
  have "([A \<rightarrow> \<alpha> . map Tm (a # u) @ \<beta>] # i # is, (a # u) @ v) 
        \<turnstile>P ([A \<rightarrow> \<alpha> @ [Tm a] . map Tm u @ \<beta>] # i # is, u @ v)"
    by simp
  also note Cons[of "\<alpha>@[Tm a]"] 
  finally show ?case by auto
qed simp

lemma reachable_impl_in_It:
  assumes "(init_state IPDA#\<rho>0, u) \<turnstile>P* (\<rho>1, v)"
  shows "\<forall>i \<in> set \<rho>1. i \<in> It G'"
  sorry


lemma steps_substring:
  assumes "(\<rho>0, w) \<turnstile>P* (\<rho>2, v)"
  obtains u where "w = u@v"
  sorry

lemma list_app_last_is_next_hd:
  assumes "w = u@v@y"
    "w = xs@a#y"
    "v \<noteq> []"
  shows "last v = a"
  using assms 
  by (metis append.assoc append_Cons append_Nil append_same_eq last_append last_snoc)

lemma reachable_impl_reachable_substring:
  assumes "(\<rho>0, u) \<turnstile>P* (\<rho>2, y)"
    "u = v@w@y"
  obtains \<rho>1 where "(\<rho>0, u) \<turnstile>P* (\<rho>1, w@y)"
proof -
  from assms(1) obtain n where "(\<rho>0, u) \<turnstile>P(n) (\<rho>2, y)"
    by (metis rtranclp_imp_relpowp)
  with assms(2) obtain \<rho>1 where "(\<rho>0, u) \<turnstile>P* (\<rho>1, w@y)"
  proof (induction n arbitrary: \<rho>2 v w y thesis rule: less_induct)
    case (less n)
    show ?case 
    proof (cases n)
      case (Suc m)
      with less(4) obtain \<rho>1 z where msteps: "(\<rho>0, u) \<turnstile>P(m) (\<rho>1, z)" "(\<rho>1, z) \<turnstile>P (\<rho>2, y)" by auto
      from msteps(2) consider "z = y" | a where "z = a#y" using step.cases by blast
      then show ?thesis
      proof cases
        case 1
        with less(1,3) msteps(1) Suc obtain \<rho>' where "(\<rho>0, u) \<turnstile>P* (\<rho>', w @ y)" by blast
        then show ?thesis using less(2) by blast
      next
        case 2
        with msteps steps_substring obtain as where as: "u = as@a#y" 
          by (meson rtranclp_power)
        show ?thesis 
        proof (cases w)
          case (Cons b bs)
          then obtain cs where cs_def: "w = cs @ [a]" 
            using as list_app_last_is_next_hd[OF less(3)] 
            by (metis list.distinct(1) snoc_eq_iff_butlast)
          hence "u = v @ cs @ z" using less 2 by simp
          from less(1)[OF _ _ this msteps(1)] obtain \<rho>' where "(\<rho>0, u) \<turnstile>P* (\<rho>', cs @ z)"
            using Suc by blast
          then show ?thesis using cs_def 2 less(2) by simp
        qed (use less rtranclp_power append_Nil in metis)
      qed
    qed (use less that in auto)
  qed
  then show thesis using that by blast
qed


lemma syms_tl_impl_substring:
  assumes "([A \<rightarrow> \<alpha> . \<beta> @ map Tm u]#\<rho>, v) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta>@map Tm u . []]#\<rho>', w)"
  obtains v' where "v = v'@u"
  sorry

lemma reaches_final_impl_reaches_complete:
  assumes "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>, v) \<turnstile>P* ([[S' \<rightarrow> [Nt S] . []], init_symbol IPDA], [])"
  obtains w where "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>, v) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []]#\<rho>', w)"
  sorry

corollary reaches_final_impl_substring:
  assumes "([A \<rightarrow> \<alpha> . \<beta> @ map Tm u]#\<rho>, v) \<turnstile>P* ([[S' \<rightarrow> [Nt S] . []], init_symbol IPDA], [])"
  obtains v' where "v = v'@u"
  using reaches_final_impl_reaches_complete[OF assms, THEN syms_tl_impl_substring]
  by metis

lemma reaches_final_impl_interm_reaches_final:
  assumes "c0 \<turnstile>P* ([[S' \<rightarrow> [Nt S] . []], init_symbol IPDA], [])"
    "c0 \<turnstile>P* c1"
  shows "c1 \<turnstile>P* ([[S' \<rightarrow> [Nt S] . []], init_symbol IPDA], [])"
  sorry



definition ipda_Lang :: "'t list set" where
  "ipda_Lang \<equiv> {w. ([init_state IPDA, init_symbol IPDA], w)
             \<turnstile>P* ([[S' \<rightarrow> [Nt S] . []], init_symbol IPDA], [])}"


lemma hist_singleton_init [simp]:
  "hist ([[A \<rightarrow> \<alpha> . \<beta>], init_symbol IPDA]) = \<alpha>"
  unfolding IPDA_def using hist_singleton by auto

lemma hist_init [simp]:
  "hist (\<rho>@[init_symbol IPDA]) = hist \<rho>"
  using IPDA_def by (induction \<rho>) auto

lemma invariant: 
  assumes "([init_state IPDA, init_symbol IPDA], u@v) \<turnstile>P* (\<rho>, v)"
  shows "Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u"
  sorry

corollary ipda_Lang_subst_Lang_G:
  "ipda_Lang \<subseteq> LangS G"
  unfolding ipda_Lang_def Context_Free_Grammar.Lang_def S_def 
  by (standard, metis invariant append.right_neutral hist_singleton_init mem_Collect_eq)

lemma derives_impl_completes:
  assumes "Prods G \<turnstile> [Nt A] \<Rightarrow> \<alpha>"
    "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
  shows "([A \<rightarrow> [] . \<alpha>]#\<rho>, w@v) \<turnstile>P* ([A \<rightarrow> \<alpha> . []]#\<rho>, v)"
  sorry


lemma ipda_Lang_eq_Lang_G:
  "ipda_Lang = LangS G"
  sorry


lemma first_step_is_eps:
  assumes "([init_state IPDA, init_symbol IPDA], u) \<turnstile>P* (qs, v)"
    "([init_state IPDA, init_symbol IPDA], u) \<noteq> (qs, v)"
  obtains \<alpha> where 
    "([init_state IPDA, init_symbol IPDA], u) \<turnstile>P ([[S \<rightarrow> [] . \<alpha>], init_state IPDA, init_symbol IPDA], u)"
    "([[S \<rightarrow> [] . \<alpha>], init_state IPDA, init_symbol IPDA], u) \<turnstile>P* (qs, v)"
proof -
  from assms obtain ps u' where step: "([init_state IPDA, init_symbol IPDA], u) \<turnstile>P (ps, u')"
    and steps: "(ps, u') \<turnstile>P* (qs, v)"
    by (metis converse_rtranclpE2)
  moreover have "u = u'" 
    by (rule ccontr, use step delta_init_empty step_equal_or_Cons in fastforce)
  moreover with step obtain r rs where 
    "ps = r#rs" "(r, rs) \<in> delta_eps IPDA (init_state IPDA) (init_symbol IPDA)"
    using step_epsE by fastforce 
  ultimately show thesis using that by auto
qed

end

end
