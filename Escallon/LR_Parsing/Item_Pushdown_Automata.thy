theory Item_Pushdown_Automata
  imports 
    Extended_Cfg
    Generalized_Pushdown_Automata
begin

(* Problem when defining \<Delta>: IPDA uses \<Delta> :: 'q list \<Rightarrow> 'a \<Rightarrow> 'q list
                              (defined as \<Delta>: Q\<^sup>+ \<times> V\<^sub>T \<Rightarrow> Q\<^sup>* in the book)
Possible solutions: 
  1. Make Q ('n, 't) item list
  2. Since state = top of stack: instead of state q and stack q#qs do state q and stack qs
      \<Longrightarrow> problems with empty stack? (IPDA accepts with final state)

A definition with variant 2, using [S' \<rightarrow> [] \<cdot> []] as a dummy starting stack symbol:
*)

print_record "(('n, 't) item, 't) gpda"

definition (in Extended_Cfg) IPDA :: "(('n, 't) item, 't) gpda" where
  "IPDA \<equiv> let
    P = Prods G';
    \<Delta> = {([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], a, [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]])|X \<beta> a \<gamma>. (X, \<beta> @ Tm a # \<gamma>) \<in> P};
    \<E> = {([[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[Y \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]])
        | X \<beta> Y \<gamma> \<alpha>. (X, \<beta> @ Nt Y # \<gamma>) \<in> P \<and> (Y, \<alpha>) \<in> P} \<union> 
        {([[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]])
        | Y \<alpha> X \<beta> \<gamma>. (X, \<beta> @ Nt Y # \<gamma>) \<in> P \<and> (Y, \<alpha>) \<in> P}     
  in \<lparr>gpda.states = It G', init = [S' \<rightarrow> [] \<cdot> [Nt S]], final = {[S' \<rightarrow> [Nt S] \<cdot> []]}, nxt = \<Delta>, eps = \<E>\<rparr>"

(* \<lparr>init = [S' \<rightarrow> [] \<cdot> [Nt S]], init_symbol = [S' \<rightarrow> [] \<cdot> []], 
      final = {[S' \<rightarrow> [Nt S] \<cdot> []]}, nxt = \<Delta>, eps = \<E>\<rparr> *)

locale ipda = Extended_Cfg G for G :: "('n::fresh0, 't) Cfg" +
  fixes M :: "(('n, 't) item, 't) gpda"
  assumes ipda: "M = Extended_Cfg.IPDA G"
begin

section \<open>Basic Properties\<close>

lemma init_ipda [simp]:
  "init M = [S' \<rightarrow> [] \<cdot> [Nt S]]"
  using ipda unfolding IPDA_def by (meson gpda.select_convs(2))

abbreviation "final_state \<equiv> [S' \<rightarrow> [Nt S] \<cdot> []]"

lemma final_ipda [simp]:
  "final M = {final_state}"
  using ipda unfolding IPDA_def by (meson select_convs(3))

lemma final_state_in_It [simp]:
  "final_state \<in> It G'"
  unfolding It_defs G'_def by auto

lemma nxt_ipda [simp]:
  "nxt M = {([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], a, [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]])|X \<beta> a \<gamma>. (X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'}"
  using ipda unfolding IPDA_def by (meson select_convs(4))

lemma nxt_Tm_neq_empty [simp]:
  assumes "a \<noteq> b"
  shows "([X \<rightarrow> \<alpha> \<cdot> Tm a # \<gamma>] # ps, b, q) \<notin> nxt M"
  using assms unfolding IPDA_def by simp

lemma nxt_nempty_imp_Tm_eq:
  assumes "(ps, a, qs) \<in> nxt M"
  obtains X \<beta> \<gamma> where "ps = [[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]]" "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'"
    "qs = [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]]"
  using assms by auto

lemma nxt_nempty_imp_Tm_eq_Item:
  assumes "([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], b, q) \<in>  nxt M"
  shows "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'" "a = b"
  using nxt_nempty_imp_Tm_eq[OF assms] by blast+

lemma eps_ipda [simp]:
  "eps M =  {([[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [Y \<rightarrow> [] \<cdot> \<alpha>] # [[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]])
        | X \<beta> Y \<gamma> \<alpha>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'} \<union> 
        {([[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]])
        | Y \<alpha> X \<beta> \<gamma>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'}"
  using ipda unfolding IPDA_def by (meson select_convs(5))

lemma eps_cases [consumes 1, case_names expand reduce]:
  assumes "(ps, qs) \<in> eps M" 
  obtains X \<beta> Y \<gamma> \<alpha> where "ps = [[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]]" "qs = [[Y \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]]"
    "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" "(Y, \<alpha>) \<in> Prods G'" |
    Y \<alpha> X \<beta> \<gamma> where "ps = [[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]]" "qs =  [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]]"
     "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" "(Y, \<alpha>) \<in> Prods G'"
  using assms unfolding eps_ipda by auto

lemma in_eps_imp_prods:
  assumes "(p # ps, q # qs) \<in> eps M"
  shows "prod_of_item p \<in> Prods G'" "prod_of_item q \<in> Prods G'"
  using assms by auto

lemma in_final_imp_final_state:
  assumes "q \<in> final M"
  shows "q = final_state"
  using assms unfolding IPDA_def S'_def S_def by simp

section \<open>Step\<close>

inductive step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
step_nxt[intro]: "(\<alpha>, a, \<alpha>') \<in> nxt M \<Longrightarrow> (\<alpha>@\<beta>,a#w) \<turnstile> (\<alpha>'@\<beta>,w)" |
step_eps[intro]: "(\<alpha>, \<alpha>') \<in> eps M \<Longrightarrow> (\<alpha>@\<beta>, w) \<turnstile> (\<alpha>'@\<beta>, w)"

inductive_cases step_nxtE[elim]: "(s, x#w) \<turnstile> (s', w)"
inductive_cases step_epsE[elim]: "(s, w) \<turnstile> (s', w)"

lemma step_equal_or_Cons:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_Cons[OF assms] by fastforce


lemma shifting [simp]:
  assumes "(A, \<alpha> @ Tm a # \<beta>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]#\<rho>s, a#u) \<turnstile> ([A \<rightarrow> \<alpha>@[Tm a] \<cdot> \<beta>]#\<rho>s, u)"
proof -
  have "([[A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]], a, [[A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>]]) \<in> nxt M"
    using IPDA_def assms by auto
  then show ?thesis using step_nxt 
    by (metis Cons_eq_appendI append.left_neutral)
qed

lemma reducing [simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([Y \<rightarrow> \<alpha> \<cdot> []]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]#\<rho>, w)"
proof -
  have "([[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]] @ \<rho>, w) \<turnstile> ([[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]] @ \<rho>, w)"
    by (rule step_eps) (use assms in fastforce)
  thus ?thesis by simp
qed

lemma expanding_in_eps:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" 
  shows "([[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]], [[Y \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]]) \<in> eps M"
  using assms by auto

lemma expanding:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] \<cdot> \<alpha>]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"
proof -
  have "([[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]] @ \<rho>, w) \<turnstile> ([[Y \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]] @ \<rho>, w)"
    using assms by fastforce
  thus ?thesis by simp
qed

lemma expanding_singleton:
  assumes "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<alpha>" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] \<cdot> \<alpha>]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"
  using assms expanding by (simp add: derive_singleton)

lemma step_cases[consumes 1, case_names shift reduce expand, cases set: step]:
  assumes "c0 \<turnstile> c1"
obtains A \<alpha> a \<beta> \<rho> u where 
    "c0 = ([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]#\<rho>, a#u)" "c1 = ([A \<rightarrow> \<alpha>@[Tm a] \<cdot> \<beta>]#\<rho>, u)" |
    Y \<alpha> X \<beta> \<gamma> \<rho> w where
      "c0 = ([Y \<rightarrow> \<alpha> \<cdot> []]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"  "c1 = ([X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]#\<rho>, w)" |
    Y \<alpha> X \<beta> \<gamma> \<rho> w where 
    "c0 = ([X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"  "c1 = ([Y \<rightarrow> [] \<cdot> \<alpha>]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"
  using assms by cases auto

lemma step_imp_in_Prods:
  assumes "(i # \<rho>, u) \<turnstile> (j # \<sigma>, v)"
  shows "prod_of_item i \<in> Prods G' \<and> prod_of_item j \<in> Prods G'"
  using assms by cases (use assms in fastforce)+

corollary step_imp_in_It:
  assumes "(i # \<rho>, u) \<turnstile> (j # \<sigma>, v)"
  shows "i \<in> It G'" "j \<in> It G'"
  using step_imp_in_Prods[OF assms] in_Prods_iff_in_It by auto

lemma step_imp_not_Nil:
  assumes "(\<rho>, u) \<turnstile> (\<sigma>, v)"
  shows "\<rho> \<noteq> [] \<and> \<sigma> \<noteq> []"
  using assms by cases auto

lemma expanding_imp_in_Prods_G:
  assumes "([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] # \<rho>, u) \<turnstile> ([Y \<rightarrow> [] \<cdot> \<gamma>] # [X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>] # \<rho>, v)"
  shows "(Y, \<gamma>) \<in> Prods G"
proof -
  from assms have "(Y, \<gamma>) \<in> Prods G'" using step_imp_in_Prods by fastforce
  then show ?thesis
  proof (cases rule: G'_Prod_cases)
    case init
    with assms have "(X, \<alpha> @ Nt S' # \<beta>) \<in> Prods G'"
      using step_imp_in_Prods by fastforce
    then show ?thesis using S'_Prod_notin_G' by simp
  qed simp
qed

lemma step_not_expanding_unique:
  assumes "(\<rho>, u) \<turnstile> c0" "(\<rho>, u) \<turnstile> c1"
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]"
  shows "c0 = c1"
  using assms(1) by (cases; use assms(2) in cases, use assms(3) in auto)


lemma step_reaches_final_imp_S:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> @ \<sigma>, u) \<turnstile> (final_state # \<sigma>, v)"
  shows "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> @ \<sigma>, u) = ([S \<rightarrow> \<alpha> \<cdot> \<beta>] # init M # \<sigma>, v)"
  using assms(1) by cases auto


section \<open>Steps\<close>

abbreviation steps (infix \<open>\<turnstile>*\<close> 50) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

abbreviation stepn ( \<open>_ \<turnstile>'(_') _\<close> 50) where
  "stepn c0 n c1 \<equiv> (step ^^ n) c0 c1"

lemma step_not_expanding_imp_reaches:
  assumes "(\<rho>, u) \<turnstile> c0" "(\<rho>, u) \<turnstile>(Suc n) c1"
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]"
  shows "c0 \<turnstile>(n) c1"
  using step_not_expanding_unique assms by (metis relpowp_Suc_D2)

lemma stepn_neq_imp_not_expanding_reaches:
  assumes "(\<rho>, u) \<turnstile> c0" "(\<rho>, u) \<turnstile>(n) c1" "(\<rho>, u) \<noteq> c1"
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]"
  obtains m where "n = Suc m" "c0 \<turnstile>(m) c1"
  using assms step_not_expanding_imp_reaches by (metis relpowp_E2)

                                                         
lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by (induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct)
  (use step_len_dec surj_pair le_trans in fastforce)+

lemma completes_Tms:
  "(A, \<alpha> @ map Tm u @ \<beta>) \<in> Prods G' 
    \<Longrightarrow> ([A \<rightarrow> \<alpha> \<cdot> map Tm u @ \<beta>]#is, u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u \<cdot> \<beta>]#is, v)"
proof (induction u arbitrary: \<alpha>)
  case (Cons a u)
  hence "([A \<rightarrow> \<alpha> \<cdot> map Tm (a # u) @ \<beta>] #  is, (a # u) @ v) 
        \<turnstile> ([A \<rightarrow> \<alpha> @ [Tm a] \<cdot> map Tm u @ \<beta>] # is, u @ v)"
    by simp
  also note Cons(1)[of "\<alpha>@[Tm a]"] 
  finally show ?case using Cons by auto
qed simp

lemma steps_in_It:
  "\<lbrakk>(i # \<rho>, u) \<turnstile>* (j # \<sigma>, v); i \<in> It G'\<rbrakk> \<Longrightarrow> j \<in> It G'"
  by (induction "j # \<sigma>" v arbitrary: j \<sigma> rule: rtranclp_induct2)
    (simp, metis neq_Nil_conv step_imp_in_It(2) step_imp_not_Nil)

lemma steps_Suc_in_It:
  assumes "(i # \<rho>, u) \<turnstile>(Suc n) (j # \<sigma>, v)"
  shows  "i \<in> It G'" "j \<in> It G'"
proof -
  from assms obtain c where "(i # \<rho>, u) \<turnstile> c" 
    by (metis relpowp_Suc_D2)
  with step_imp_in_It(1) show "i \<in> It G'" 
    by (smt (verit, ccfv_threshold) step_cases)
  with assms[THEN relpowp_imp_rtranclp] show "j \<in> It G'"
    using steps_in_It by simp
qed


lemma steps_neq_in_It:
  assumes "(i # \<rho>, u) \<turnstile>* (j # \<sigma>, v)" "(i # \<rho>, u) \<noteq> (j # \<sigma>, v)"
  shows "i \<in> It G' \<and> j \<in> It G'"
  using assms(1) proof (cases rule: converse_rtranclpE)
  case (step y)
  from this(1) step_imp_in_It(1) have "i \<in> It G'" 
    by (metis list.exhaust old.prod.exhaust step_imp_not_Nil)
  then show ?thesis using steps_in_It step assms(1) by blast
qed (use assms(2) in simp)

lemma reaches_final_imp_in_It:
  assumes "(i # \<rho>, u) \<turnstile>* (final_state # \<sigma>, v)"
  shows "i \<in> It G'"
  using final_state_in_It steps_neq_in_It assms by (cases "i = final_state") blast+

lemma reachable_imp_in_It:
  "\<lbrakk>([init M], u) \<turnstile>* (\<rho>, v); i \<in> set \<rho>\<rbrakk> 
    \<Longrightarrow> i \<in> It G'"
proof (induction arbitrary: i rule: rtranclp_induct2)
  case (step \<rho>0 u \<rho>1 v)
  from step(2) show ?case 
    using steps_in_It step step_imp_in_It(2) by cases auto
qed (auto simp: It_defs G'_def)

lemma reachable_imp_not_Nil:
  "\<lbrakk>(\<rho>, u) \<turnstile>* (\<sigma>, v); \<rho> \<noteq> []\<rbrakk> \<Longrightarrow> \<sigma> \<noteq> []"
  by (induction rule: rtranclp_induct2)
    (simp, use step.cases in blast)

lemma reachable_imp_substring:
  assumes "(\<rho>, w) \<turnstile>* (\<sigma>, v)"
  obtains u where "w = u @ v"
  using assms proof (induction arbitrary: thesis rule: rtranclp_induct2)
  case (step \<sigma> v \<tau> x)
  then obtain u where "w = u @ v" by blast
  then show thesis using step_equal_or_Cons[OF step(2)] step(4) by auto
qed simp

corollary steps_shift_decomp:
  assumes "(\<rho>, u @ v) \<turnstile>* ([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<sigma>, a # v)"
    "([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<sigma>, a # v) \<turnstile> (\<tau>, v)"
  obtains x where "u = x @ [a]"
  using reachable_imp_substring[OF assms(1)] by auto

lemma init_expands[elim]:
  assumes "(init M # \<rho>, u) \<turnstile> (\<sigma>, v)"
  obtains \<alpha> where "(\<sigma>, v) = ([S \<rightarrow> [] \<cdot> \<alpha>] # init M # \<rho>, u)"
    "(S, \<alpha>) \<in> Prods G"
  using assms proof cases
  case (expand Y \<alpha> X \<beta> \<gamma> \<rho> w)
  then show ?thesis 
    using G'_def S_neq_S' that assms by auto
qed auto

lemma complete_S'_step_impossible:
  assumes "([S' \<rightarrow> \<alpha> \<cdot> []] # \<rho>, w) \<turnstile> c"
  shows False
  using assms S'_Prod_notin_G' assms step_imp_in_Prods by cases force+

lemma second_notin_It_imp_complete_step_impossible:
  assumes "([A \<rightarrow> \<alpha> \<cdot> []] # i # \<rho>, w) \<turnstile> c"
    "i \<notin> It G'"
  shows False
  using assms proof cases
  case (reduce Y \<alpha> X \<beta> \<gamma> \<rho> w)
  then show False using assms 
      prod_of_item_eq_imp_in_Prods_eq[of "[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]" "[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]"] 
      step_imp_in_It by auto
qed simp_all

lemma complete_S'_steps_refl:
  assumes "([[S' \<rightarrow> \<alpha> \<cdot> []]], w) \<turnstile>* c"
  shows "([[S' \<rightarrow> \<alpha> \<cdot> []]], w) = c"
  using assms complete_S'_step_impossible by (cases rule: converse_rtranclpE) blast+

lemma reachable_imp_init_or_in_G:
  assumes "([init M], u) \<turnstile>* (\<rho>, v)"
  obtains \<sigma> \<alpha> \<beta> where "\<rho> = \<sigma> @ [[S' \<rightarrow> \<alpha> \<cdot> \<beta>]]" "\<alpha> @ \<beta> = [Nt S]"
    "\<forall>i \<in> set \<sigma>. case i of [X \<rightarrow> \<gamma> \<cdot> \<delta>] \<Rightarrow> (X, \<gamma>@\<delta>) \<in> Prods G"
proof -
  from assms obtain n where "([init M], u) \<turnstile>(n) (\<rho>, v)"
    using rtranclp_imp_relpowp by fast
  then show thesis using that proof (induction n arbitrary: thesis \<rho> v)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then obtain \<sigma> w where n_steps: "([init M], u) \<turnstile>(n) (\<sigma>, w)" 
      "(\<sigma>, w) \<turnstile> (\<rho>, v)" by auto
    from Suc.IH[OF this(1)] obtain \<tau> \<alpha> \<beta> where \<tau>_def:
      "\<sigma> = \<tau> @ [[S' \<rightarrow> \<alpha> \<cdot> \<beta>]]" "\<alpha> @ \<beta> = [Nt S]" 
      "\<forall>i \<in> set \<tau>. case i of [X \<rightarrow> \<gamma> \<cdot> \<delta>] \<Rightarrow> (X, \<gamma>@\<delta>) \<in> Prods G" (is "\<forall>i \<in> _. ?in_Prods i")
      by blast
    from n_steps(2) show ?case 
    proof (cases \<tau>)
      case Nil
      with \<tau>_def n_steps(2) have \<sigma>_init: "\<sigma> = [init M]"
        using complete_S'_step_impossible[of "[Nt S]"] append_eq_Cons_conv by fastforce 
      with n_steps init_expands show ?thesis 
        using Suc.prems(2)[of _ "[]" "[Nt S]"] \<sigma>_init by force
    next
      case (Cons i \<upsilon>)
      hence \<sigma>_def: "\<sigma> = i # \<upsilon> @ [[S' \<rightarrow> \<alpha> \<cdot> \<beta>]]" using \<tau>_def by simp
      from n_steps(2)[unfolded this] show ?thesis 
      proof cases
        case (expand Y \<alpha>' X \<beta>' \<gamma> \<rho>' w')
        moreover with Cons have
          "\<rho> = [Y \<rightarrow> [] \<cdot> \<alpha>'] # \<tau> @ [[S' \<rightarrow> \<alpha> \<cdot> \<beta>]]" by simp
        moreover from expand \<tau>_def Cons have "\<forall>i\<in>set ([Y \<rightarrow> [] \<cdot> \<alpha>'] # \<tau>). ?in_Prods i" 
          using \<sigma>_def  expanding_imp_in_Prods_G expand n_steps(2) \<tau>_def(3) by auto
        ultimately show ?thesis using Suc.prems(2) \<tau>_def Cons by fastforce
      qed (cases \<upsilon>, (use \<tau>_def Cons Suc in auto))+
    qed
  qed 
qed

lemma first_step_is_eps:
  assumes "([init M], u) \<turnstile>(Suc n) (qs, v)"
  obtains \<alpha> where 
    "([init M], u) \<turnstile> ([[S \<rightarrow> [] \<cdot> \<alpha>], init M], u)"
    "([[S \<rightarrow> [] \<cdot> \<alpha>], init M], u) \<turnstile>* (qs, v)"
proof -
  from assms obtain ps u' where step: "([init M], u) \<turnstile> (ps, u')"
    and steps: "(ps, u') \<turnstile>* (qs, v)"
    by (metis relpowp_Suc_D2 rtranclp_power surj_pair)
  moreover have "u = u'"
    using step_equal_or_Cons step by fast
  moreover with step have "([init M], ps) \<in> eps M" by auto
  ultimately show thesis using that by blast
qed

lemma reachable_snd_not_empty_imp_hd_in_G:
  assumes "([init M], u) \<turnstile>* ([A \<rightarrow> \<alpha> \<cdot> \<beta>] # [B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<rho>, v)"
    "\<gamma>@\<delta> \<noteq> []"
  shows "(A, \<alpha>@\<beta>) \<in> Prods G"
proof -
  from reachable_imp_init_or_in_G[OF assms(1)] obtain \<sigma> \<alpha>' \<beta>' where \<sigma>_def:
    "[A \<rightarrow> \<alpha> \<cdot> \<beta>] # [B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<rho> = \<sigma> @ [[S' \<rightarrow> \<alpha>' \<cdot> \<beta>']]" "\<alpha>' @ \<beta>' = [Nt S]"
    "\<forall>i\<in>set \<sigma>. case i of [X \<rightarrow> \<gamma> \<cdot> \<delta>] \<Rightarrow> (X, \<gamma> @ \<delta>) \<in> Prods G"
    by blast
  have "\<sigma> \<noteq> []" 
    by standard (use assms(2) \<sigma>_def in auto)
  from this show ?thesis using \<sigma>_def Cons_eq_append_conv 
    by fastforce
qed

lemma singleton_derive_imp_completes:
  assumes "Prods G' \<turnstile> [Nt X] \<Rightarrow> map Tm u"
    "(A, \<alpha> @ Nt X # \<beta>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> \<cdot> [Nt X] @ \<beta>] # \<rho>, u @ v) 
          \<turnstile>* ([A \<rightarrow> \<alpha> @ [Nt X] \<cdot> \<beta>] # \<rho>, v)"
proof -
  note deriv = derive_singleton[of "Prods G'" "Nt X" "map Tm u"]
  with assms expanding have 
    "([A \<rightarrow> \<alpha> \<cdot> [Nt X] @ \<beta>] # \<rho>, u @ v) 
      \<turnstile> ([X \<rightarrow> [] \<cdot> map Tm u] # [A \<rightarrow> \<alpha> \<cdot> [Nt X] @ \<beta>] # \<rho>, u @ v)"
    by auto
  also with completes_Tms step_imp_in_Prods have 
    "... \<turnstile>* ([X \<rightarrow> map Tm u \<cdot> []] # [A \<rightarrow> \<alpha> \<cdot> [Nt X] @ \<beta>] # \<rho>, v)" 
    by (metis deriv append.right_neutral append_Nil assms(1) completes_Tms sym.inject(1))
  also  have "... \<turnstile> ([A \<rightarrow> \<alpha> @ [Nt X] \<cdot> \<beta>] # \<rho>, v)"
    using assms deriv by auto
  finally show ?thesis .
qed

section \<open>Language Equivalence\<close>

lemma derive_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow> map Tm w"
    "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> \<cdot> \<beta>@\<gamma>] # \<rho>, w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> \<cdot> \<gamma>] # \<rho>, x)"
proof -
  from derive_word_imp_single_Nt[OF assms(1)] obtain u v X y where \<beta>_decomp:
    "\<beta> = map Tm u @ Nt X # map Tm y" "Prods G' \<turnstile> [Nt X] \<Rightarrow> map Tm v" "w = u @ v @ y" by metis
  with completes_Tms[of A \<alpha> u "Nt X # map Tm y @ \<gamma>" _ "v @ y @ x"] have 
    "([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] # \<rho>, w @ x) 
      \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, v @ y @ x)" 
    using assms by simp
  also from singleton_derive_imp_completes[OF \<beta>_decomp(2), of _ "\<alpha> @ map Tm u" _ _ "y@x"] have 
    "... \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u @ [Nt X] \<cdot> map Tm y @ \<gamma>] # \<rho>, y @ x)"
    using \<beta>_decomp(1) assms(2) by auto
  also from completes_Tms have "... \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] # \<rho>, x)"
    using \<beta>_decomp by (smt (verit) append.assoc append_Cons append_Nil assms(2))
  finally show ?thesis .
qed


lemma derives_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w"
    "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> \<cdot> \<beta>@\<gamma>] # \<rho>, w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> \<cdot> \<gamma>] # \<rho>, x)"
proof -
  from assms obtain n where "Prods G' \<turnstile> \<beta> \<Rightarrow>(n) map Tm w" 
    using rtranclp_imp_relpowp by fast
  with assms(2) show ?thesis
  proof (induction n arbitrary: \<beta> w A \<alpha> \<gamma> \<rho> x rule: less_induct)
    case (less n)
    then show ?case 
    proof (cases n)
      case (Suc m)
      note Suc_m = this
      with derives_decomp_less obtain \<delta>\<^sub>1 i u X j v \<delta>\<^sub>2 k y where
        \<beta>_decomp:
        "\<beta> = \<delta>\<^sub>1 @ Nt X # \<delta>\<^sub>2"
        "Prods G' \<turnstile> \<delta>\<^sub>1 \<Rightarrow>(i) map Tm u" "Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v" "Prods G' \<turnstile> \<delta>\<^sub>2 \<Rightarrow>(k) map Tm y"
        "w = u @ v @ y" "i + j + k = n" "j > 0" 
        using less(3)  by (smt (verit, best))
      hence leqs: "i < n" "k < n" by auto
      have first: "([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] # \<rho>, w @ x) 
              \<turnstile>* ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 \<cdot> Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho>, v @ y @ x)"
        (is "_ \<turnstile>* (?\<sigma>, _)")
        using less(1)[OF leqs(1) _ \<beta>_decomp(2), of _ _ "Nt X # \<delta>\<^sub>2 @ \<gamma>" _ "v @ y @ x"]
          \<beta>_decomp less.prems(1) by simp
      have last: "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] \<cdot> \<delta>\<^sub>2 @ \<gamma>] # \<rho>, y @ x) 
                  \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] # \<rho>, x)"
        using less(1)[OF leqs(2) _ \<beta>_decomp(4), of _ "\<alpha> @ \<delta>\<^sub>1 @ [Nt X]"] \<beta>_decomp(1) less.prems(1) by simp
      show ?thesis 
      proof (cases "j = n")
        case True
        with \<beta>_decomp have Tms: "i = 0" "k = 0" "\<delta>\<^sub>1 = map Tm u" "\<delta>\<^sub>2 = map Tm y"
          by auto
        from True \<beta>_decomp(6,7) Suc obtain \<beta>' where m_steps:
          "Prods G' \<turnstile> [Nt X] \<Rightarrow> \<beta>'" "Prods G' \<turnstile> \<beta>' \<Rightarrow>(m) map Tm v"
          using \<beta>_decomp(3) by (meson relpowp_Suc_D2)
        show ?thesis 
        proof (cases m)
          case (Suc m')
          from derives_decomp_less[OF m_steps(2)[unfolded Suc]] obtain \<xi>\<^sub>1 i' u' Y j' v' \<xi>\<^sub>2 k' y' 
            where \<beta>'_decomp:
            "\<beta>' = \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2" "Prods G' \<turnstile> \<xi>\<^sub>1 \<Rightarrow>(i') map Tm u'" "Prods G' \<turnstile> [Nt Y] \<Rightarrow>(j') map Tm v'"
            "Prods G' \<turnstile> \<xi>\<^sub>2 \<Rightarrow>(k') map Tm y'" "v = u' @ v' @ y'" "i' < n" "j' < n" "k' < n"
            using Suc Suc_m 
            by (smt (verit, ccfv_threshold) add.commute add_lessD1 lessI)
          from derivern_singleton_imp_prod[OF \<beta>'_decomp(3)] obtain \<gamma>' j'' where Y_prod: 
            "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<gamma>'" "Prods G' \<turnstile> \<gamma>' \<Rightarrow>(j'') map Tm v'"
            "j'' < n"
            using \<beta>'_decomp(7) by (metis Suc_lessD)
          hence Y_prod': "(Y, \<gamma>') \<in> Prods G'" using derive_singleton 
            by (metis sym.inject(1))
          from m_steps \<beta>'_decomp(1) have X_step: "(X, \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2) \<in> Prods G'" 
            "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 \<cdot> Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho>, v @ y @ x) 
              \<turnstile> ([X \<rightarrow> [] \<cdot> \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v @ y @ x)" 
            using expanding_singleton \<beta>_decomp(1) less.prems(1) by 
              (metis derive_singleton sym.inject(1), force)
          note first
          also note X_step(2)
          also from less(1)[OF \<beta>'_decomp(6) _ \<beta>'_decomp(2), of _ _ _ _ "v' @ y' @ y @ x"] 
          have "... \<turnstile>* ([X \<rightarrow> \<xi>\<^sub>1 \<cdot> Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v' @ y' @ y @ x)" 
               (is "_ \<turnstile>* (?\<tau>, _)")
          using \<beta>'_decomp(5) append.assoc append_Nil X_step(1)
            by (metis \<beta>'_decomp(5) append_Nil)
          also with Y_prod' have "... \<turnstile> ([Y \<rightarrow> [] \<cdot> \<gamma>'] # ?\<tau>, v' @ y' @ y @ x)" 
             using X_step(1) expanding by presburger
          also from less(1)[OF Y_prod(3) _ Y_prod(2), of Y "[]" "[]" _ "y' @ y @ x"]
          have "... \<turnstile>* ([Y \<rightarrow> \<gamma>' \<cdot> []] # ?\<tau>, y' @ y @ x)" 
            using Y_prod' by simp
          also have "... \<turnstile> ([X \<rightarrow> \<xi>\<^sub>1 @ [Nt Y] \<cdot> \<xi>\<^sub>2] # ?\<sigma>, y' @ y @ x)"
            using reducing Y_prod' X_step(1) by presburger
          also from less(1)[OF \<beta>'_decomp(8) _ \<beta>'_decomp(4), of X _ "[]" _ "y @ x"] have
            "... \<turnstile>* ([X \<rightarrow> \<beta>' \<cdot> []] # ?\<sigma>, y @ x)"
            using \<beta>'_decomp(1) append.assoc X_step(1) 
            by (metis append.right_neutral append_Cons append_Nil)
          finally show ?thesis using reducing last X_step(1) \<beta>'_decomp less.prems(1) \<beta>_decomp
            by (smt (verit) append.assoc append_Cons converse_rtranclp_into_rtranclp 
                derive_singleton m_steps(1) rtranclp_trans sym.inject(1))
        qed (use derive_imp_completes \<beta>_decomp Tms Suc_m less.prems relpowp_Suc_0 in metis)
      next
        case False
        hence "j < n" using \<beta>_decomp by linarith
        then show ?thesis
          using first last derivern_singleton_imp_prod[OF \<beta>_decomp(3)] less.prems(1)
          by (smt (verit, ccfv_threshold) \<beta>_decomp(1,3) append.assoc append_Cons append_self_conv2 less.IH
              rtranclp_trans)
      qed
    qed (use completes_Tms in simp)
  qed
qed

lemma reaches_final_imp_complete_reaches_final:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>(n) ([final_state], [])"
  obtains u v m k where
    "m + k = n"
    "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>(m) ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v)"
    "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v) \<turnstile>(k) ([final_state], [])"
  using assms proof (induction n arbitrary: A \<alpha> \<beta> \<rho> w thesis rule: less_induct)
  case (less n)
  show ?case 
  proof (cases n)
    case (Suc m)
    then obtain \<sigma> x where step: "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile> (\<sigma>, x)"
      "(\<sigma>, x) \<turnstile>(m) ([final_state], [])"
      using less.prems(2) by (metis relpowp_Suc_D2 surj_pair)
    from step obtain B \<gamma> \<delta> \<tau> u v j k where \<sigma>_complete:
      "\<sigma> = [B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>" "x = u @ v" "Prods G' \<turnstile> \<delta> \<Rightarrow>* map Tm u"
      "([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, u @ v) \<turnstile>(j) ([B \<rightarrow> \<gamma> @ \<delta> \<cdot> []] # \<tau>, v)"
      "([B \<rightarrow> \<gamma> @ \<delta> \<cdot> []] # \<tau>, v) \<turnstile>(k) ([final_state], [])"
      "j + k = m" using less.IH 
      by (smt (verit, ccfv_SIG) Suc ipda.step_cases ipda_axioms lessI prod.inject)
    from this(5) reaches_final_imp_in_It have B_in_Prods: "(B, \<gamma> @ \<delta>) \<in> Prods G'"
      using relpowp_imp_rtranclp in_It_imp_in_Prods by fastforce
    from step(1) show ?thesis
    proof cases
      case (shift A' \<alpha>' a \<beta>' \<rho>' y)
      with \<sigma>_complete have eqs: "w = a # u @ v" "B = A" "\<gamma> = \<alpha> @ [Tm a]" "\<delta> = \<beta>'" by auto
      with shift have 
        "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile> ([A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>'] # \<rho>, u @ v)"
        using step by auto
      also have "... \<turnstile>(j) ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v)" 
        using eqs \<sigma>_complete shift by simp
      finally show ?thesis using less.prems(1)[of "Suc j" k "a # u" v] \<sigma>_complete[unfolded eqs] Suc
        using derives_Cons shift by auto
    next
      case (reduce Y \<alpha>' X \<beta>' \<gamma>' \<rho>' y)
      then show ?thesis using less.prems(1)[of 0 n "[]" w] less.prems(2) by force
    next
      case (expand Y \<gamma>' X \<alpha>' \<beta>' \<rho>' y)
      with \<sigma>_complete have eqs: "B = Y" "w = u @ v" "X = A" "\<delta> = \<gamma>'" "\<beta> = Nt Y # \<beta>'" by auto
      with expand step step_imp_in_Prods have Y_derives: "Prods G' \<turnstile> [Nt Y] \<Rightarrow>* map Tm u" 
        using \<sigma>_complete(3) by (metis append.right_neutral append_Nil derives_Cons_rule item.case)
      from eqs expand have exp_step:
        "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) 
          \<turnstile> ([Y \<rightarrow> [] \<cdot> \<gamma>'] # [A \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>'] # \<rho>, u @ v)"
        using step by auto
      moreover with \<sigma>_complete eqs have j_steps: 
        "... \<turnstile>(j) ([Y \<rightarrow> \<gamma>' \<cdot> []] # [A \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>'] # \<rho>, v)"
        using expand by simp
      moreover have reduct_step: "... \<turnstile> ([A \<rightarrow> \<alpha> @ [Nt Y] \<cdot> \<beta>'] # \<rho>, v)"
        using expand step step_imp_in_Prods by force
      moreover with less.IH obtain v' x' j' k' l where complete_reaches: "v = v' @ x'" "Prods G' \<turnstile> \<beta>' \<Rightarrow>* map Tm v'"
        "... \<turnstile>(j') ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, x')"
        "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, x') \<turnstile>(k') ([final_state], [])"
        "k = Suc l"
        "j' + k' = l"
      proof - (* TODO refactor *)
        from expand step \<sigma>_complete eqs have 
          "([Y \<rightarrow> \<gamma>' \<cdot> []] # [A \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>'] # \<rho>, v) 
            \<turnstile>(k) ([final_state], [])"
          by auto
        moreover have "[Y \<rightarrow> \<gamma>' \<cdot> []] # [A \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>'] # \<rho> 
          \<noteq> [final_state]"  by auto
        ultimately obtain l where l_steps: "k = Suc l"
          "([A \<rightarrow> \<alpha> @ [Nt Y] \<cdot> \<beta>'] # \<rho>, v) \<turnstile>(l) ([final_state], [])"
          using eqs step \<sigma>_complete reducing stepn_neq_imp_not_expanding_reaches reduct_step 
          by (metis list.sel(1) prod.inject)
        moreover with \<sigma>_complete(6) Suc have lt: "l < n" by linarith
        ultimately show thesis using less.IH[OF lt _ l_steps(2)] that expand eqs
          by (smt (verit, best) Cons_eq_append_conv append.assoc append_self_conv2)
      qed
      ultimately have A_completes: "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) 
          \<turnstile>(Suc (Suc j) + j') ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, x')"
        by (meson relpowp_Suc_I relpowp_Suc_I2 relpowp_trans)
      from complete_reaches(2) Y_derives eqs(5) have "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm (u @ v')"
        by (metis derives_Cons_iff derives_Nt_map_TmD map_append)
      from less.prems(1)[OF _ _ this A_completes complete_reaches(4)] show thesis
        using eqs(2)[unfolded complete_reaches(1)] \<sigma>_complete(6) complete_reaches(5-) Suc
        by force
    qed  
  qed (use less in simp)
qed


lemma reaches_final_imp_completes:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>* ([final_state], [])"
  obtains u v where 
    "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v)"
    "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v) \<turnstile>* ([final_state], [])"
proof -
  from assms have A_in_Prods: "(A, \<alpha> @ \<beta>) \<in> Prods G'" 
    using reaches_final_imp_in_It in_It_imp_in_Prods by fastforce
  from reaches_final_imp_complete_reaches_final assms rtranclp_imp_relpowp obtain u v where complete:
    "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v) \<turnstile>* ([final_state], [])" 
    using relpowp_imp_rtranclp by metis
  with derives_imp_completes[OF this(2), of A \<alpha> "[]"] A_in_Prods show thesis using that
    by simp
qed

lemma reaches_final_imp_second_is_chain:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<rho>, w) \<turnstile>* ([final_state], [])"
  obtains X \<alpha>' \<beta>' where "i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']"
proof -
  from assms reaches_final_imp_completes obtain x where 
    "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<rho>, x) \<turnstile>* ([final_state], [])"
    by metis
  then show thesis
  proof (cases rule: converse_rtranclpE)
    case (step y)
    from this(1) show ?thesis 
      using that by cases auto
  qed force
qed

lemma reaches_without_stack_imp_S':
  assumes "([[A \<rightarrow> \<alpha> \<cdot> \<beta>]], w) \<turnstile>* ([final_state], [])"
  shows "[A \<rightarrow> \<alpha> \<cdot> \<beta>] = init M \<or> [A \<rightarrow> \<alpha> \<cdot> \<beta>] = final_state"
proof -
  from reaches_final_imp_completes[of _ _ _ "[]"] assms obtain u v where "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([[A \<rightarrow> \<alpha> \<cdot> \<beta>]], w) \<turnstile>* ([[A \<rightarrow> \<alpha> @ \<beta> \<cdot> []]], v)"
    "([[A \<rightarrow> \<alpha> @ \<beta> \<cdot> []]], v) \<turnstile>* ([final_state], [])"
    (is "?complete \<turnstile>* ?final")
    by metis
  from this(4) have "?complete = ?final"
    using ipda.step_cases ipda_axioms by (cases rule: converse_rtranclpE) blast+
  thus ?thesis by (simp add: append_eq_Cons_conv)
qed

lemma reachable_Cons_imp_expanded:
  assumes "([init M], u) \<turnstile>(n) ([A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<rho>, v)"
  obtains u' m k where "([init M], u) \<turnstile>(m) (i # \<rho>, u')"
    "(i # \<rho>, u') \<turnstile> ([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>] # i # \<rho>, u')"
    "([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>] # i # \<rho>, u') \<turnstile>(k) ([A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<rho>, v)" "Suc m + k = n"
  using assms proof (induction n arbitrary: A \<alpha> \<beta> i \<rho> v thesis rule: less_induct)
  case (less n)
  note that = less.prems(1)
  from less(3) obtain m c where m_steps: "n = Suc m" 
    "([init M], u) \<turnstile>(m) c" "c \<turnstile> ([A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<rho>, v)" 
    by (metis list.distinct(1) list.inject prod.inject relpowp_E)
  from m_steps(3) show ?case proof cases
    case (shift _ \<alpha>' a _ \<sigma> _)
    then show ?thesis using less.IH[of m i \<rho> A \<alpha>' "Tm a # \<beta>" "a # v"] m_steps that 
      by (smt (verit, best) add_Suc_right append.assoc append_Cons append_Nil item.inject lessI
          list.inject prod.inject relpowp_Suc_I)
  next
    case (reduce Y \<gamma>' X \<alpha>' _ \<sigma> w)
    with less.IH[of m "[A \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>]" \<sigma> Y \<gamma>' "[]" w] m_steps obtain k j u' where k_steps:
      "([gpda.init M], u) \<turnstile>(k) ([A \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>] # i # \<rho>, u')"
      "([A \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>] # i # \<rho>, u') \<turnstile>(Suc j) c" "k + Suc j = m"
      by (smt (verit, ccfv_threshold) add_Suc_shift item.inject lessI list.inject old.prod.inject
          relpowp_Suc_I2)
    with less.IH[OF _ _ this(1)] obtain m' k' v' where m'_steps: "([gpda.init M], u) \<turnstile>(m') (i # \<rho>, v')"
      "(i # \<rho>, v') \<turnstile> ([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>] # i # \<rho>, v')"
      "([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>] # i # \<rho>, v') \<turnstile>(k') ([A \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>] # i # \<rho>, u')"
      "Suc m' + k' = k" using reduce m_steps(1) by auto
    note this(1,2)
    moreover have "([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>] # i # \<rho>, v') \<turnstile>(Suc k' + Suc j) ([A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<rho>, v)"
      using m'_steps(3)[THEN relpowp_trans, OF k_steps(2), THEN relpowp_Suc_I, OF m_steps(3)]
      by simp
    moreover have "Suc m' + (Suc k' + Suc j) = n" 
      using k_steps(3) m'_steps(4) m_steps(1) by simp
    ultimately show ?thesis using that by presburger
  next
    case (expand _ _ X _ \<gamma> \<sigma> w)
    then show ?thesis using that[of m w 0] m_steps by auto
  qed
qed


lemma reaches_final_imp_no_stack:
  assumes "([init M], u) \<turnstile>* (final_state # \<rho>, v)"
  shows "\<rho> = []" 
  using assms proof (cases \<rho>)
  case (Cons i \<sigma>)
  obtain w where
    "([init M], u) \<turnstile>* (i # \<sigma>, w)" "(i # \<sigma>, w) \<turnstile> (init M # i # \<sigma>, w)"
  proof -
    from assms obtain n where "([init M], u) \<turnstile>(n) (final_state # i # \<sigma>, v)"
      using rtranclp_imp_relpowp unfolding Cons by metis
    from reachable_Cons_imp_expanded[OF this] show ?thesis using that relpowp_imp_rtranclp  
      by (metis append.right_neutral init_ipda)
  qed
  from this(2) show ?thesis proof cases
    case (expand Y \<alpha> X \<beta> \<gamma> \<rho> w)
    then show ?thesis 
    using S'_Prod_notin_G(1) assms local.Cons reachable_snd_not_empty_imp_hd_in_G by fastforce
  qed simp_all
qed

definition Lang :: "'t list set" where
  "Lang \<equiv> {w. ([init M], w) \<turnstile>* ([final_state], [])}"

lemma invariant: 
  assumes "([init M], u@v) \<turnstile>* (rev \<rho>, v)"
  shows "Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u"
proof -
  from assms obtain n where "([init M], u@v) \<turnstile>(n) (rev \<rho>, v)"
    using rtranclp_imp_relpowp by fast
  then show ?thesis
  proof (induction n arbitrary:u v \<rho>)
    case (Suc n)
    then obtain \<sigma> w where n_steps: "([init M], u @ v) \<turnstile>(n) (rev \<sigma>, w)" "(rev \<sigma>, w) \<turnstile> (rev \<rho>, v)"
      by (metis relpowp_Suc_E rev_swap surj_pair)
    from this(2) show ?case 
    proof (cases rule: step_cases)
      case (shift A \<alpha> a \<beta> i \<tau>)
      with steps_shift_decomp n_steps(1)[THEN relpowp_imp_rtranclp]
      obtain x where u_decomp: "u = x @ [a]" "w = a # v" 
        using n_steps(2) by (metis prod.inject)
      with Suc.IH[of x "a#v"] n_steps(1) have derives_x: "Prods G \<turnstile> hist \<sigma> \<Rightarrow>* map Tm x"
        by simp
      moreover have "hist \<rho> = hist \<sigma> @ [Tm a]" using shift unfolding hist_defs by simp
      ultimately show ?thesis using derives_append[OF derives_x] u_decomp by simp
    next
      case (reduce Y \<alpha> X \<beta> \<gamma> \<tau> x)
      have "Prods G \<turnstile> hist \<rho> \<Rightarrow>* hist \<sigma>"
      proof -
        from n_steps reduce have Y_prod: "(Y, \<alpha>) \<in> Prods G" 
          using reachable_snd_not_empty_imp_hd_in_G 
            relpowp_imp_rtranclp by fastforce
        from reduce have "hist \<rho> = hist (rev \<tau>) @ \<beta> @ [Nt Y]" by simp
        also have "Prods G \<turnstile> ... \<Rightarrow>* hist (rev \<tau>) @ \<beta> @ \<alpha>"
          using Y_prod derives_prepend by (metis derive_singleton r_into_rtranclp) 
        also have "... = hist \<sigma>" using reduce by auto
        finally show ?thesis .
      qed
      also from reduce n_steps(1) Suc.IH have "Prods G \<turnstile> ... \<Rightarrow>* map Tm u" by blast
      finally show ?thesis .
    next
      case (expand Y \<alpha> X \<beta> \<gamma> \<tau> x)
      with n_steps(1) Suc.IH show ?thesis by fastforce
    qed
  qed (simp add: hist_defs)
qed

lemma Lang_subst_Lang_G:
  "Lang \<subseteq> LangS G"
proof 
  fix w
  assume "w \<in> Lang"
  hence "([gpda.init M], w) \<turnstile>* ([final_state], [])" unfolding Lang_def
    by blast
  with invariant[of w "[]" "[final_state]"] show "w \<in> LangS G" 
    using G'_derives_from_S_imp_in_Lang G_derives_imp_G'_derives Lang_preserved by force
qed

lemma Lang_G_subst_Lang: 
  "LangS G \<subseteq> Lang"
  using Lang_preserved G'_def G_derives_imp_G'_derives 
    derives_imp_completes[of _ _ S' "[]" "[]" "[]" "[]"] 
  unfolding Lang_def Context_Free_Grammar.Lang_def by auto

corollary Lang_eq_Lang_G:
  "Lang = LangS G"
  using Lang_subst_Lang_G Lang_G_subst_Lang by order

lemma deriver_imp_IPDA_comp:
  assumes
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r \<alpha>@\<beta>"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v"
  shows
    "([[S' \<rightarrow> \<alpha> \<cdot> \<beta>]], v) \<turnstile>* ([final_state], [])"
proof -
  from assms have eq_S: "\<alpha>@\<beta> = [Nt S]" 
    using S'_derive_imp_S append_eq_Cons_conv 
    by (simp add: deriver_imp_derive)
  then consider (left) "\<alpha> = [Nt S]" "\<beta> = []" | (right) "\<alpha> = []" "\<beta> = [Nt S]"
    by (metis (no_types, opaque_lifting) Cons_eq_append_conv append_is_Nil_conv)
  then show ?thesis 
  proof cases
    case left
    with assms(2) have v_empty: "v = []" 
      by (simp add: derivers_iff_derives)
    then show ?thesis using eq_S left by simp
  next
    case right
    with assms have "v \<in> LangS G'"  
      using G'_derives_from_S_imp_in_Lang derivers_imp_derives by blast
    then show ?thesis using eq_S Lang_def right 
        Lang_eq_Lang_G Lang_preserved hist_singleton rtrancl_refl init_ipda ipda by force
  qed
qed

 

end
end
