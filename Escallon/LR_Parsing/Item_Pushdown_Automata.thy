theory Item_Pushdown_Automata
  imports 
    Extended_Cfg
    Pushdown_Automata.Pushdown_Automata
begin

(* Problem when defining \<Delta>: IPDA uses \<Delta> :: 'q list \<Rightarrow> 'a \<Rightarrow> 'q list
                              (defined as \<Delta>: Q\<^sup>+ \<times> V\<^sub>T \<Rightarrow> Q\<^sup>* in the book)
Possible solutions: 
  1. Make Q ('n, 't) item list
  2. Since state = top of stack: instead of state q and stack q#qs do state q and stack qs
      \<Longrightarrow> problems with empty stack? (IPDA accepts with final state)

A definition with variant 2, using [S' \<rightarrow> [] . []] as a dummy starting stack symbol:
*)
definition (in Extended_Cfg) IPDA :: "(('n, 't) item, 't, ('n, 't) item) pda" where
  "IPDA \<equiv> let
    P = Prods G';
    \<Delta> = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a \<and> (X, \<beta> @ Tm a' # \<gamma>) \<in> P then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} 
        else {} | _ \<Rightarrow> {});
    \<E> = (\<lambda>q s. if prod_of_item q \<notin> P then {} else case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> 
        {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> P} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' \<and> prod_of_item s \<in> P then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})         
  in \<lparr>init_state = [S' \<rightarrow> [] . [Nt S]], init_symbol = [S' \<rightarrow> [] . []], 
      final_states = {[S' \<rightarrow> [Nt S] . []]}, delta = \<Delta>, delta_eps = \<E>\<rparr>"


locale ipda = Extended_Cfg G for G :: "('n::fresh0, 't) Cfg" +
  fixes M :: "(('n, 't) item, 't, ('n, 't) item) pda"
  assumes ipda: "M = Extended_Cfg.IPDA G"
begin

section \<open>Basic Properties\<close>

lemma init_state_ipda [simp]:
  "init_state M = [S' \<rightarrow> [] . [Nt S]]"
  using ipda unfolding IPDA_def by (meson select_convs(1))

lemma init_symbol_ipda [simp]:
  "init_symbol M = [S' \<rightarrow> [] . []]"
  using ipda unfolding IPDA_def by (meson select_convs(2))

lemma init_symbol_notin_It: 
  "init_symbol M \<notin> It G'"
proof 
  assume "init_symbol M \<in> It G'"
  hence "(S', []) \<in> Prods G \<or> (S', []) = (S',[Nt S])"
    unfolding G'_def It_defs by fastforce
  then show False
    using S'_Prod_notin_G by simp
qed

lemma in_Prods_imp_item_neq_init_symbol:
  assumes "(Y, \<alpha>) \<in> Prods G'"
    "\<alpha> = \<beta> @ \<gamma>"
  shows "[Y \<rightarrow> \<beta> . \<gamma>] \<noteq> init_symbol M"
  using assms init_symbol_notin_It unfolding It_defs by auto

abbreviation "final_state \<equiv> [S' \<rightarrow> [Nt S] . []]"

lemma final_states_ipda [simp]:
  "final_states M = {final_state}"
  using ipda unfolding IPDA_def by (meson select_convs(3))

lemma final_state_in_It [simp]:
  "final_state \<in> It G'"
  unfolding It_defs G'_def by auto

lemma delta_ipda [simp]:
  "delta M = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a \<and> (X, \<beta> @ Tm a' # \<gamma>) \<in> Prods G' then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} 
  else {} | _ \<Rightarrow> {})"
  using ipda unfolding IPDA_def by (meson select_convs(4))


lemma delta_Tm_neq_empty [simp]:
  assumes "a \<noteq> b"
  shows "delta M ([X \<rightarrow> \<alpha> . Tm a # \<gamma>]) b q = {}"
  using assms unfolding IPDA_def by simp

lemma delta_nempty_imp_Tm_eq:
  assumes "delta M p a q \<noteq> {}"
  obtains X \<beta> \<gamma> where "p = [X \<rightarrow> \<beta> . Tm a # \<gamma>]" "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'"
proof -
  obtain X \<beta> \<alpha> where p_def: "p = [X \<rightarrow> \<beta> . \<alpha>]" using item.exhaust by blast
  then consider (Nil) "\<alpha> = []" | (Tm_eq) \<gamma> where "\<alpha> = Tm a # \<gamma>" | 
   (Tm_neq) a' \<gamma> where "\<alpha> = Tm a' # \<gamma>" "a' \<noteq> a" | (Nt) A \<gamma> where "\<alpha> = Nt A # \<gamma>"
    using list.exhaust sym.exhaust by metis
  then show thesis using p_def assms that by cases fastforce+
qed

lemma delta_nempty_imp_Tm_eq_Item:
  assumes "delta M ([X \<rightarrow> \<beta> . Tm a # \<gamma>]) b q \<noteq> {}"
  shows "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'" "a = b"
  using delta_nempty_imp_Tm_eq[OF assms] by blast+

lemma in_prods_imp_delta_singleton [simp]:
  assumes "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'"
  shows "delta M ([X \<rightarrow> \<beta> . Tm a # \<gamma>]) a q = {([X \<rightarrow> \<beta> @ [Tm a] . \<gamma>], [q])}"
  using assms by auto

lemma in_delta_imp_unchanged_prod:
  assumes "(p, s) \<in> delta M q a r"
  shows "prod_of_item p = prod_of_item q"
proof (cases q)
  case (Item X \<beta> \<gamma>)
  then show ?thesis 
  proof (cases \<gamma>)
    case (Cons b \<delta>)
    with assms Item have "(X, \<beta> @ Tm a # \<delta>) \<in> Prods G'" "Tm a = b"
      using delta_nempty_imp_Tm_eq by blast+
    then show ?thesis using in_prods_imp_delta_singleton Item Cons 
      assms by auto
  qed (use assms in simp)
qed

lemma delta_eps_ipda [simp]:
  "delta_eps M = (\<lambda>q s. if prod_of_item q \<notin> Prods G' then {} else 
    case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> Prods G'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' \<and> (prod_of_item s \<in> Prods G')
        then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})"
  using ipda unfolding IPDA_def by (meson select_convs(5))

lemma delta_eps_ipda_prods [simp]:
  assumes "prod_of_item q \<in> Prods G'"
  shows "delta_eps M q s = (case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> Prods G'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' \<and> prod_of_item s \<in> Prods G' 
        then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})"
  using assms by auto

lemma delta_eps_nempty_imp_prod:
  assumes "delta_eps M q s \<noteq> {}"
  shows "prod_of_item q \<in> Prods G'"
  using assms by auto

lemma delta_eps_Nt_neq_empty [simp]:
  assumes "Y \<noteq> Y'"
  shows "delta_eps M ([Y \<rightarrow> \<alpha> . []]) ([X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) = {}"
  using assms by simp

lemma delta_eps_complete_imp_snd_in_prods:
  assumes "delta_eps M ([Y \<rightarrow> \<alpha> . []]) q \<noteq> {}"
  shows "prod_of_item q \<in> Prods G'"
proof -
  note Y\<alpha>_prod = delta_eps_nempty_imp_prod[OF assms]
  obtain X \<beta> \<gamma> where q_def: "q = [X \<rightarrow> \<beta> . \<gamma>]" using item.exhaust by metis
  then show ?thesis
  proof (cases \<gamma>)
    case Nil
    then show ?thesis using q_def assms 
      by (smt (verit, ccfv_threshold) delta_eps_ipda_prods delta_eps_nempty_imp_prod item.case
          list.simps(4) old.prod.case)
  next
    case (Cons a \<delta>)
    then show ?thesis 
    proof (cases a)
      case (Nt A)
      with Cons q_def have 
        "delta_eps M ([Y \<rightarrow> \<alpha> . []]) q 
          = (if Y = A \<and> prod_of_item q \<in> Prods G' then {([X \<rightarrow> \<beta> @ [Nt A] . \<delta>], [])} else {})"
        using Y\<alpha>_prod by force
      then show ?thesis using Cons q_def assms by argo
    next
      case (Tm b)
      then show ?thesis using Cons q_def assms using Y\<alpha>_prod by auto
    qed
  qed
qed


lemma delta_eps_complete_imp_reducing:
  assumes "delta_eps M [Y \<rightarrow> \<alpha> . []] q \<noteq> {}"
  obtains X \<beta> \<gamma> where "q = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" "(Y, \<alpha>) \<in> Prods G'"
proof -
  obtain X \<beta> \<gamma> where q_def: "q = [X \<rightarrow> \<beta> . \<gamma>]" using item.exhaust by metis
  then show thesis
  proof (cases \<gamma>)
    case Nil
    then show ?thesis using assms q_def 
      by (smt (verit, best) delta_eps_ipda item.case list.case(1) old.prod.case)
  next
    case (Cons a as)
    then show ?thesis       
      using assms q_def Cons that delta_eps_ipda_prods delta_eps_complete_imp_snd_in_prods  
      by (cases a)
        (metis (lifting) append.right_neutral delta_eps_Nt_neq_empty delta_eps_ipda item.case,
          smt (verit) case_prod_conv delta_eps_ipda item.case list.simps(4,5) sym.simps(6))
  qed
qed

lemma delta_eps_nempty_imp_expanding_or_reducing[consumes 1, case_names expanding reducing]:
  assumes "delta_eps M p q \<noteq> {}"
  obtains X \<beta> Y \<gamma> where "p = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" |
    Y \<alpha> X \<beta>  \<gamma> where "p = [Y \<rightarrow> \<alpha> . []]" "q = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(Y, \<alpha>) \<in> Prods G'" 
      "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
proof -
  obtain X \<alpha> \<beta> where p_def: "p = [X \<rightarrow> \<alpha> . \<beta>]" using item.exhaust by blast
  then show thesis
  proof (cases \<beta>)
    case Nil
    then show ?thesis 
      using delta_eps_complete_imp_reducing assms that p_def by metis
  next
    case (Cons a as)
    then show ?thesis 
      using p_def assms delta_eps_nempty_imp_prod that by (cases a)
      (metis item.case, smt (verit, ccfv_threshold) case_prod_conv delta_eps_ipda item.case 
        list.simps(5) sym.simps(6))
  qed
qed

lemma in_delta_eps_imp_in_prods:
  assumes "(p, q) \<in> delta_eps M r s"
  shows "prod_of_item p \<in> Prods G'"
proof -
  from assms have "delta_eps M r s \<noteq> {}" by blast
  then show ?thesis
    using assms by (cases rule: delta_eps_nempty_imp_expanding_or_reducing) auto
qed

lemmas init_defs = init_state_def init_symbol_def

lemma in_final_imp_final_state:
  assumes "q \<in> final_states M"
  shows "q = final_state"
  using assms unfolding IPDA_def S'_def S_def by simp

section \<open>Step\<close>

inductive step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
delta[intro]: "\<lbrakk>\<alpha> = [p0, p1]; \<alpha>' = q#qs; (q,qs) \<in> delta M p0 a p1\<rbrakk> 
                \<Longrightarrow> (\<alpha>@\<beta>,a#w) \<turnstile> (\<alpha>'@\<beta>,w)" |
eps[intro]: "\<lbrakk>\<alpha> = [p0, p1]; \<alpha>' = q#qs; (q,qs) \<in> delta_eps M p0 p1\<rbrakk> 
                \<Longrightarrow> (\<alpha>@\<beta>, w) \<turnstile> (\<alpha>'@\<beta>, w)"

inductive_cases step_deltaE[elim]: "(s, x#w) \<turnstile> (s', w)"
inductive_cases step_epsE[elim]: "(s, w) \<turnstile> (s', w)"

lemma step_equal_or_Cons:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_Cons[OF assms] by fastforce


lemma shifting_Cons [simp]:
  assumes "(A, \<alpha> @ Tm a # \<beta>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> . Tm a # \<beta>]#\<rho>#\<rho>s, a#u) \<turnstile> ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#\<rho>#\<rho>s, u)"
proof -
  have "([A \<rightarrow> \<alpha>@[Tm a] . \<beta>], [\<rho>]) \<in> delta M ([A \<rightarrow> \<alpha> . Tm a # \<beta>]) a \<rho>"
    using IPDA_def assms by simp
  then show ?thesis using delta 
    by (metis Cons_eq_appendI append.left_neutral)
qed

lemma shifting [simp]:
  assumes "(A, \<alpha> @ Tm a # \<beta>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> . Tm a # \<beta>]#\<rho>@[init_symbol M], a#u) \<turnstile> ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#\<rho>@[init_symbol M], u)"
  by (cases \<rho>) (use assms in auto)


lemma reducing [simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([Y \<rightarrow> \<alpha> . []]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]#\<rho>, w)"
proof -
  have "([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>], []) \<in> delta_eps M ([Y \<rightarrow> \<alpha> . []]) ([X \<rightarrow> \<beta> . Nt Y#\<gamma>])"
    unfolding IPDA_def using assms by simp
  thus ?thesis using eps by (metis Cons_eq_appendI append.left_neutral)
qed


lemma expanding_in_delta_eps:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" 
  shows "([Y \<rightarrow> [] . \<alpha>], [[X \<rightarrow> \<beta> . Nt Y#\<gamma>], i]) \<in> delta_eps M ([X \<rightarrow> \<beta> . Nt Y#\<gamma>]) i"
  using assms ipda delta_eps_ipda_prods unfolding G'_def S'_def S_def IPDA_def  
    by fastforce
  

lemma expanding_Cons [simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" 
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
  using expanding_in_delta_eps[OF assms] eps by (simp add: step.simps)

lemma expanding:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w)"
  using assms by (cases \<rho>) (auto simp: step.simps)

lemma expanding_singleton:
  assumes "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<alpha>" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w)"
  using assms expanding by (simp add: derive_singleton)

lemma expanding_singleton_Cons:
  assumes "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<alpha>" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
  using assms expanding_Cons by (simp add: derive_singleton)

lemma in_delta_imp_shifting:
  assumes "(q, qs) \<in> delta M p0 a p1"
  obtains X \<beta> \<gamma> where "p0 = [X \<rightarrow> \<beta> . Tm a # \<gamma>]"
    "(q,qs) = ([X \<rightarrow> \<beta> @ [Tm a] . \<gamma>], [p1])"
proof -
  from assms have "delta M p0 a p1 \<noteq> {}" by auto
  from delta_nempty_imp_Tm_eq[OF this] 
    obtain X \<beta> \<gamma> where p0_def: "p0 = [X \<rightarrow> \<beta> . Tm a # \<gamma>]" "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'" by blast
  hence "delta M p0 a p1 = {([X \<rightarrow> \<beta> @ [Tm a] . \<gamma>], [p1])}" by simp
  with assms show thesis using delta_ipda that p0_def 
    by (metis (lifting) singletonD)
qed

lemma eps_cases[consumes 1, case_names reducing expand]:
  assumes "(q0,qs) \<in> delta_eps M p0 p1"
  obtains Y \<alpha> X \<beta> \<gamma> where
    "p0 = [Y \<rightarrow> \<alpha> . []]" "p1 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "q0 = [X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]" "qs = []" 
    "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" |
    X \<beta> Y \<gamma> \<alpha> where
    "p0 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(Y, \<alpha>) \<in> Prods G'" "q0 = [Y \<rightarrow> [] . \<alpha>]" "qs = p0#[p1]" 
proof -
  from delta_eps_nempty_imp_expanding_or_reducing consider 
    X \<beta> Y \<gamma> where "p0 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" |
    Y \<alpha> X \<beta> \<gamma> where "p0 = [Y \<rightarrow> \<alpha> . []]" "p1 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(Y, \<alpha>) \<in> Prods G'" 
       "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
    using assms by blast
  then show thesis
    by cases (use that assms in auto) 
qed

lemma step_cases[consumes 1, case_names shift reduce expand, cases set: step]:
  assumes "c0 \<turnstile> c1"
obtains A \<alpha> a \<beta> i \<rho> u where 
    "c0 = ([A \<rightarrow> \<alpha> . Tm a # \<beta>]#i#\<rho>, a#u)" "c1 = ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#i#\<rho>, u)" |
    Y \<alpha> X \<beta> \<gamma> \<rho> w where
      "c0 = ([Y \<rightarrow> \<alpha> . []]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>, w)"  "c1 = ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]#\<rho>, w)" |
    Y \<alpha> X \<beta> \<gamma> i \<rho> w where 
    "c0 = ([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"  "c1 = ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
  using assms proof cases
  case (delta \<alpha> p0 p1 \<alpha>' q qs a \<beta> w)
  from in_delta_imp_shifting[OF delta(5)] obtain X \<beta>' \<gamma> where "p0 = [X \<rightarrow> \<beta>' . Tm a # \<gamma>]" 
    "(q,qs) = ([X \<rightarrow> \<beta>' @ [Tm a] . \<gamma>], [p1])" by blast
  then show ?thesis using that delta by simp 
next
  case (eps \<alpha> p0 p1 \<alpha>' q qs \<beta> w)
  from eps(5) expanding_in_delta_eps eps_cases eps that show ?thesis 
    by (cases rule: eps_cases) force+
qed

lemma step_imp_in_Prods:
  assumes "(i # \<rho>, u) \<turnstile> (j # \<sigma>, v)"
  shows "prod_of_item i \<in> Prods G' \<and> prod_of_item j \<in> Prods G'"
  using assms proof (cases rule: step.cases)
  case (delta \<alpha> p0 p1 \<alpha>' q qs a \<beta>)
  then show ?thesis using delta_nempty_imp_Tm_eq in_delta_imp_unchanged_prod 
    by (smt (verit, best) append_Cons empty_iff item.case list.inject)
next
  case (eps \<alpha> p0 p1 \<alpha>' q qs \<beta>)
  then show ?thesis using in_delta_eps_imp_in_prods delta_eps_nempty_imp_prod 
    by (metis (no_types, lifting) append_Cons equals0D list.inject)
qed

corollary step_imp_in_It:
  assumes "(i # \<rho>, u) \<turnstile> (j # \<sigma>, v)"
  shows "i \<in> It G'" "j \<in> It G'"
  using step_imp_in_Prods[OF assms] in_Prods_iff_in_It by auto

lemma step_imp_not_Nil:
  assumes "(\<rho>, u) \<turnstile> (\<sigma>, v)"
  shows "\<rho> \<noteq> [] \<and> \<sigma> \<noteq> []"
  using assms by cases auto

lemma step_imp_two_items:
  assumes "(\<rho>, u) \<turnstile> (\<sigma>, v)"
  obtains i1 i2 \<tau> where "\<rho> = i1 # i2 # \<tau>" 
  using assms by cases auto


lemma step_app_init_symbol_preserved:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], u) \<turnstile> (\<sigma>, v)"
  obtains B \<gamma> \<delta> \<tau> where "\<sigma> = [B \<rightarrow> \<gamma> . \<delta>] # \<tau> @ [init_symbol M]"
  using assms proof cases
  case (shift A \<alpha> a \<beta> i \<tau> u)
  then show ?thesis using that[of A "\<alpha> @ [Tm a]" \<beta> \<rho>] 
    by simp
next
  case (reduce Y \<alpha> X \<beta> \<gamma> \<tau> w)
  then show ?thesis 
    using init_symbol_notin_It that[of X "\<beta> @ [Nt Y]" \<gamma> "tl \<rho>"] 
    by (cases \<rho>) auto
next
  case (expand Y \<alpha>' X \<beta>' \<gamma> i \<tau> w)
  then show ?thesis using that[of Y "[]" \<alpha>' "[A \<rightarrow> \<alpha> . \<beta>] # \<rho>"] 
    by auto
qed
 

lemma expanding_imp_in_Prods_G:
  assumes "([X \<rightarrow> \<alpha> . Nt Y # \<beta>] # \<rho>, u) \<turnstile> ([Y \<rightarrow> [] . \<gamma>] # [X \<rightarrow> \<alpha> . Nt Y # \<beta>] # \<rho>, v)"
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
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> . []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> . Tm a # \<beta>]"
  shows "c0 = c1"
  using assms(1) by (cases; use assms(2) in cases, use assms(3) in auto)


lemma step_reaches_final_imp_S:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ \<sigma>, u) \<turnstile> (final_state # \<sigma>, v)"
  shows "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ \<sigma>, u) = ([S \<rightarrow> \<alpha> . \<beta>] # init_state M # \<sigma>, v)"
  using assms(1) by cases auto



section \<open>Steps\<close>

abbreviation steps (infix \<open>\<turnstile>*\<close> 50) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

abbreviation stepn ( \<open>_ \<turnstile>'(_') _\<close> 50) where
  "stepn c0 n c1 \<equiv> (step ^^ n) c0 c1"

lemma step_not_expanding_imp_reaches:
  assumes "(\<rho>, u) \<turnstile> c0" "(\<rho>, u) \<turnstile>(Suc n) c1"
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> . []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> . Tm a # \<beta>]"
  shows "c0 \<turnstile>(n) c1"
  using step_not_expanding_unique assms by (metis relpowp_Suc_D2)

lemma stepn_neq_imp_not_expanding_reaches:
  assumes "(\<rho>, u) \<turnstile> c0" "(\<rho>, u) \<turnstile>(n) c1" "(\<rho>, u) \<noteq> c1"
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> . []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> . Tm a # \<beta>]"
  obtains m where "n = Suc m" "c0 \<turnstile>(m) c1"
  using assms step_not_expanding_imp_reaches by (metis relpowp_E2)

                                                         
lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by (induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct)
  (use step_len_dec surj_pair le_trans in fastforce)+

lemma completes_Tms_Cons:
  "(A, \<alpha> @ map Tm u @ \<beta>) \<in> Prods G' 
    \<Longrightarrow> ([A \<rightarrow> \<alpha> . map Tm u @ \<beta>]#i#is, u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . \<beta>]#i#is, v)"
proof (induction u arbitrary: \<alpha>)
  case (Cons a u)
  hence "([A \<rightarrow> \<alpha> . map Tm (a # u) @ \<beta>] # i # is, (a # u) @ v) 
        \<turnstile> ([A \<rightarrow> \<alpha> @ [Tm a] . map Tm u @ \<beta>] # i # is, u @ v)"
    by simp
  also note Cons(1)[of "\<alpha>@[Tm a]"] 
  finally show ?case using Cons by auto
qed simp

lemma stepn_Suc_imp_x:
  assumes "(\<rho>, u) \<turnstile>(Suc n) (\<sigma>, v)"
  obtains i j \<tau> where "\<rho> = i # j # \<tau>"
proof -
  from assms obtain c where "(\<rho>, u) \<turnstile> c" 
    by (meson relpowp_Suc_D2)
  then show thesis
    using that by cases auto
qed

lemma steps_neq_imp_two_items:
  assumes "(\<rho>, u) \<turnstile>* (\<sigma>, v)" "\<rho> \<noteq> \<sigma>"
  obtains i j \<tau> where "\<rho> = i # j # \<tau>"
proof -
  from assms obtain c where "(\<rho>, u) \<turnstile> c" 
    by (metis converse_rtranclpE prod.inject)
  then show thesis
    using that step_imp_two_items prod.exhaust by metis
qed

lemma completes_Tms:
  "(A, \<alpha> @ map Tm u @ \<beta>) \<in> Prods G' \<Longrightarrow> ([A \<rightarrow> \<alpha> . map Tm u @ \<beta>]#\<rho>@[init_symbol M], u@v) 
                                          \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . \<beta>]#\<rho>@[init_symbol M], v)"
  using completes_Tms_Cons by (cases \<rho>) auto

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
  "\<lbrakk>([init_state M, init_symbol M], u) \<turnstile>* (\<rho>, v); i \<in> set \<rho> - {init_symbol M}\<rbrakk> 
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

lemma reachable_imp_hd_not_init_symbol:
  assumes "([init_state M, init_symbol M], u) \<turnstile>* (i#\<rho>, v)"
  shows "i \<noteq> init_symbol M"
  using assms steps_Suc_in_It init_symbol_notin_It  
    by (cases rule: rtranclp.cases) (simp, meson relpowp_Suc_I rtranclp_power)

lemma reachable_imp_head_in_It:
  "([init_state M, init_symbol M], u) \<turnstile>* (i#\<rho>, v) \<Longrightarrow> i \<in> It G'"
  using reachable_imp_hd_not_init_symbol reachable_imp_in_It
  by auto


lemma reachable_imp_substring:
  assumes "(\<rho>, w) \<turnstile>* (\<sigma>, v)"
  obtains u where "w = u @ v"
  using assms proof (induction arbitrary: thesis rule: rtranclp_induct2)
  case (step \<sigma> v \<tau> x)
  then obtain u where "w = u @ v" by blast
  then show thesis using step_equal_or_Cons[OF step(2)] step(4) by auto
qed simp

corollary steps_shift_decomp:
  assumes "(\<rho>, u @ v) \<turnstile>* ([A \<rightarrow> \<alpha> . Tm a # \<beta>] # \<sigma>, a # v)"
    "([A \<rightarrow> \<alpha> . Tm a # \<beta>] # \<sigma>, a # v) \<turnstile> (\<tau>, v)"
  obtains x where "u = x @ [a]"
  using reachable_imp_substring[OF assms(1)] by auto

lemma init_state_expands[elim]:
  assumes "(init_state M # \<rho>, u) \<turnstile> (\<sigma>, v)"
  obtains \<alpha> where "(\<sigma>, v) = ([S \<rightarrow> [] . \<alpha>] # init_state M # \<rho>, u)"
    "(S, \<alpha>) \<in> Prods G"
  using assms proof cases
  case (expand Y \<alpha> X \<beta> \<gamma> i \<rho> w)
  then show ?thesis 
    using G'_def S_neq_S' that assms by auto
qed auto

lemma complete_S'_step_impossible:
  assumes "([S' \<rightarrow> \<alpha> . []] # \<rho>, w) \<turnstile> c"
  shows False
  using assms S'_Prod_notin_G' assms step_imp_in_Prods by cases force+

lemma second_notin_It_imp_complete_step_impossible:
  assumes "([A \<rightarrow> \<alpha> . []] # i # \<rho>, w) \<turnstile> c"
    "i \<notin> It G'"
  shows False
  using assms proof cases
  case (reduce Y \<alpha> X \<beta> \<gamma> \<rho> w)
  then show False using assms 
      prod_of_item_eq_imp_in_Prods_eq[of "[X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "[X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]"] 
      step_imp_in_It by auto
qed simp_all

lemma complete_S'_steps_refl:
  assumes "([[S' \<rightarrow> \<alpha> . []], init_symbol M], w) \<turnstile>* c"
  shows "([[S' \<rightarrow> \<alpha> . []], init_symbol M], w) = c"
  using assms complete_S'_step_impossible by (cases rule: converse_rtranclpE) blast+

lemma reachable_imp_init_or_in_G:
  assumes "([init_state M, init_symbol M], u) \<turnstile>* (\<rho>, v)"
  obtains \<sigma> \<alpha> \<beta> where "\<rho> = \<sigma> @ [[S' \<rightarrow> \<alpha> . \<beta>], init_symbol M]" "\<alpha> @ \<beta> = [Nt S]"
    "\<forall>i \<in> set \<sigma>. case i of [X \<rightarrow> \<gamma> . \<delta>] \<Rightarrow> (X, \<gamma>@\<delta>) \<in> Prods G"
proof -
  from assms obtain n where "([init_state M, init_symbol M], u) \<turnstile>(n) (\<rho>, v)"
    using rtranclp_imp_relpowp by fast
  then show thesis using that proof (induction n arbitrary: thesis \<rho> v)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then obtain \<sigma> w where n_steps: "([init_state M, init_symbol M], u) \<turnstile>(n) (\<sigma>, w)" 
      "(\<sigma>, w) \<turnstile> (\<rho>, v)" by auto
    from Suc.IH[OF this(1)] obtain \<tau> \<alpha> \<beta> where \<tau>_def:
      "\<sigma> = \<tau> @ [[S' \<rightarrow> \<alpha> . \<beta>], init_symbol M]" "\<alpha> @ \<beta> = [Nt S]" 
      "\<forall>i \<in> set \<tau>. case i of [X \<rightarrow> \<gamma> . \<delta>] \<Rightarrow> (X, \<gamma>@\<delta>) \<in> Prods G" (is "\<forall>i \<in> _. ?in_Prods i")
      by blast
    from n_steps(2) show ?case 
    proof (cases \<tau>)
      case Nil
      with \<tau>_def n_steps(2) have \<sigma>_init: "\<sigma> = [init_state M, init_symbol M]"
        using complete_S'_step_impossible[of "[Nt S]"] append_eq_Cons_conv by fastforce 
      with n_steps init_state_expands show ?thesis 
        using Suc.prems(2)[of _ "[]" "[Nt S]"] \<sigma>_init by force
    next
      case (Cons i \<upsilon>)
      hence \<sigma>_def: "\<sigma> = i # \<upsilon> @ [[S' \<rightarrow> \<alpha> . \<beta>], init_symbol M]" using \<tau>_def by simp
      from n_steps(2)[unfolded this] show ?thesis 
      proof cases
        case (expand Y \<alpha>' X \<beta>' \<gamma> j \<rho>' w')
        moreover with Cons have
          "\<rho> = [Y \<rightarrow> [] . \<alpha>'] # \<tau> @ [[S' \<rightarrow> \<alpha> . \<beta>], init_symbol M]" by simp
        moreover from expand \<tau>_def Cons have "\<forall>i\<in>set ([Y \<rightarrow> [] . \<alpha>'] # \<tau>). ?in_Prods i" 
          using \<sigma>_def  expanding_imp_in_Prods_G expand n_steps(2) \<tau>_def(3) by auto
        ultimately show ?thesis using Suc.prems(2) \<tau>_def Cons by fastforce
      qed (cases \<upsilon>, (use \<tau>_def Cons Suc in auto))+
    qed
  qed 
qed

lemma first_step_is_eps:
  assumes "([init_state M, init_symbol M], u) \<turnstile>(Suc n) (qs, v)"
  obtains \<alpha> where 
    "([init_state M, init_symbol M], u) \<turnstile> ([[S \<rightarrow> [] . \<alpha>], init_state M, init_symbol M], u)"
    "([[S \<rightarrow> [] . \<alpha>], init_state M, init_symbol M], u) \<turnstile>* (qs, v)"
proof -
  from assms obtain ps u' where step: "([init_state M, init_symbol M], u) \<turnstile> (ps, u')"
    and steps: "(ps, u') \<turnstile>* (qs, v)"
    by (metis relpowp_Suc_D2 rtranclp_power surj_pair)
  moreover have "u = u'"
    using step_equal_or_Cons step by fast
  moreover with step obtain r rs where 
    "ps = r#rs" "(r, rs) \<in> delta_eps M (init_state M) (init_symbol M)"
    using step_epsE by fastforce 
  ultimately show thesis using that by blast
qed

lemma reachable_snd_not_empty_imp_hd_in_G:
  assumes "([init_state M, init_symbol M], u) \<turnstile>* ([A \<rightarrow> \<alpha> . \<beta>] # [B \<rightarrow> \<gamma> . \<delta>] # \<rho>, v)"
    "\<gamma>@\<delta> \<noteq> []"
  shows "(A, \<alpha>@\<beta>) \<in> Prods G"
proof -
  from reachable_imp_init_or_in_G[OF assms(1)] obtain \<sigma> \<alpha>' \<beta>' where \<sigma>_def:
    "[A \<rightarrow> \<alpha> . \<beta>] # [B \<rightarrow> \<gamma> . \<delta>] # \<rho> = \<sigma> @ [[S' \<rightarrow> \<alpha>' . \<beta>'], init_symbol M]" "\<alpha>' @ \<beta>' = [Nt S]"
    "\<forall>i\<in>set \<sigma>. case i of [X \<rightarrow> \<gamma> . \<delta>] \<Rightarrow> (X, \<gamma> @ \<delta>) \<in> Prods G"
    by blast
  have "\<sigma> \<noteq> []" 
    by standard (use assms(2) \<sigma>_def in auto)
  from this show ?thesis using \<sigma>_def Cons_eq_append_conv 
    by fastforce
qed

lemma singleton_derive_imp_completes:
  assumes "Prods G' \<turnstile> [Nt X] \<Rightarrow> map Tm u"
    "(A, \<alpha> @ Nt X # \<beta>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], u @ v) 
          \<turnstile>* ([A \<rightarrow> \<alpha> @ [Nt X] . \<beta>] # \<rho> @ [init_symbol M], v)"
proof -
  note deriv = derive_singleton[of "Prods G'" "Nt X" "map Tm u"]
  with assms expanding have 
    "([A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], u @ v) 
      \<turnstile> ([X \<rightarrow> [] . map Tm u] # [A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], u @ v)"
    by auto
  also with completes_Tms step_imp_in_Prods have 
    "... \<turnstile>* ([X \<rightarrow> map Tm u . []] # [A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], v)" 
    by (metis deriv append.right_neutral append_Nil assms(1) completes_Tms_Cons sym.inject(1))
  also  have "... \<turnstile> ([A \<rightarrow> \<alpha> @ [Nt X] . \<beta>] # \<rho> @ [init_symbol M], v)"
    using assms deriv by auto
  finally show ?thesis .
qed

section \<open>Language Equivalence\<close>

lemma derive_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow> map Tm w"
    "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>] # \<rho> @ [init_symbol M], w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
proof -
  from derive_word_imp_single_Nt[OF assms(1)] obtain u v X y where \<beta>_decomp:
    "\<beta> = map Tm u @ Nt X # map Tm y" "Prods G' \<turnstile> [Nt X] \<Rightarrow> map Tm v" "w = u @ v @ y" by metis
  with completes_Tms[of A \<alpha> u "Nt X # map Tm y @ \<gamma>" _ "v @ y @ x"] have 
    "([A \<rightarrow> \<alpha> . \<beta> @ \<gamma>] # \<rho> @ [init_symbol M], w @ x) 
      \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . Nt X # map Tm y @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x)" 
    using assms by simp
  also from singleton_derive_imp_completes[OF \<beta>_decomp(2), of _ "\<alpha> @ map Tm u" _ _ "y@x"] have 
    "... \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u @ [Nt X] . map Tm y @ \<gamma>] # \<rho> @ [init_symbol M], y @ x)"
    using \<beta>_decomp(1) assms(2) by auto
  also from completes_Tms have "... \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
    using \<beta>_decomp by (smt (verit) append.assoc append_Cons append_Nil assms(2))
  finally show ?thesis .
qed


lemma derives_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w"
    "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>] # \<rho> @ [init_symbol M], w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
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
      have first: "([A \<rightarrow> \<alpha> . \<beta> @ \<gamma>] # \<rho> @ [init_symbol M], w @ x) 
              \<turnstile>* ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 . Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x)"
        (is "_ \<turnstile>* (?\<sigma>, _)")
        using less(1)[OF leqs(1) _ \<beta>_decomp(2), of _ _ "Nt X # \<delta>\<^sub>2 @ \<gamma>" _ "v @ y @ x"]
          \<beta>_decomp less.prems(1) by simp
      have last: "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] . \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], y @ x) 
                  \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
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
            "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 . Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x) 
              \<turnstile> ([X \<rightarrow> [] . \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v @ y @ x)" 
            using expanding_singleton \<beta>_decomp(1) less.prems(1) by 
              (metis derive_singleton sym.inject(1), force)
          note first
          also note X_step(2)
          also from less(1)[OF \<beta>'_decomp(6) _ \<beta>'_decomp(2), of _ _ _ _ "v' @ y' @ y @ x"] 
          have "... \<turnstile>* ([X \<rightarrow> \<xi>\<^sub>1 . Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v' @ y' @ y @ x)" 
               (is "_ \<turnstile>* (?\<tau>, _)")
          using \<beta>'_decomp(5) append.assoc append_Cons append_Nil X_step(1)
            by (metis \<beta>'_decomp(5) append.assoc append_Cons append_Nil)
          also with Y_prod' have "... \<turnstile> ([Y \<rightarrow> [] . \<gamma>'] # ?\<tau>, v' @ y' @ y @ x)" 
             using X_step(1) by simp
          also from less(1)[OF Y_prod(3) _ Y_prod(2), of Y "[]" "[]" _ "y' @ y @ x"]
          have "... \<turnstile>* ([Y \<rightarrow> \<gamma>' . []] # ?\<tau>, y' @ y @ x)" 
            using Y_prod' 
            by (smt (verit, best) Cons_eq_appendI self_append_conv self_append_conv2)
          also have "... \<turnstile> ([X \<rightarrow> \<xi>\<^sub>1 @ [Nt Y] . \<xi>\<^sub>2] # ?\<sigma>, y' @ y @ x)"
            using reducing Y_prod' X_step(1) by presburger
          also from less(1)[OF \<beta>'_decomp(8) _ \<beta>'_decomp(4), of X _ "[]" _ "y @ x"] have
            "... \<turnstile>* ([X \<rightarrow> \<beta>' . []] # ?\<sigma>, y @ x)"
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
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) \<turnstile>(n) ([final_state, init_symbol M], [])"
  obtains u v m k where
    "m + k = n"
    "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) \<turnstile>(m) ([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], v)"
    "([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], v) \<turnstile>(k) ([final_state, init_symbol M], [])"
  using assms proof (induction n arbitrary: A \<alpha> \<beta> \<rho> w thesis rule: less_induct)
  case (less n)
  show ?case 
  proof (cases n)
    case (Suc m)
    then obtain \<sigma> x where step: "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) \<turnstile> (\<sigma>, x)"
      "(\<sigma>, x) \<turnstile>(m) ([final_state, init_symbol M], [])"
      using less.prems(2) by (metis relpowp_Suc_D2 surj_pair)
    from step_app_init_symbol_preserved[OF step(1)] obtain B \<gamma> \<delta> \<tau> u v j k where \<sigma>_complete:
      "\<sigma> = [B \<rightarrow> \<gamma> . \<delta>] # \<tau> @ [init_symbol M]" "x = u @ v" "Prods G' \<turnstile> \<delta> \<Rightarrow>* map Tm u"
      "([B \<rightarrow> \<gamma> . \<delta>] # \<tau> @ [init_symbol M], u @ v) \<turnstile>(j) ([B \<rightarrow> \<gamma> @ \<delta> . []] # \<tau> @ [init_symbol M], v)"
      "([B \<rightarrow> \<gamma> @ \<delta> . []] # \<tau> @ [init_symbol M], v) \<turnstile>(k) ([final_state, init_symbol M], [])"
      "j + k = m" using less.IH by (metis Suc lessI step(2))
    from this(5) reaches_final_imp_in_It have B_in_Prods: "(B, \<gamma> @ \<delta>) \<in> Prods G'"
      using relpowp_imp_rtranclp in_It_imp_in_Prods by fastforce
    from step(1) show ?thesis
    proof cases
      case (shift A' \<alpha>' a \<beta>' i \<rho>' y)
      with \<sigma>_complete have eqs: "w = a # u @ v" "B = A" "\<gamma> = \<alpha> @ [Tm a]" "\<delta> = \<beta>'" by auto
      with shift have 
        "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) \<turnstile> ([A \<rightarrow> \<alpha> @ [Tm a] . \<beta>'] # \<rho> @ [init_symbol M], u @ v)"
        using step by auto
      also have "... \<turnstile>(j) ([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], v)" 
        using eqs \<sigma>_complete shift by simp
      finally show ?thesis using less.prems(1)[of "Suc j" k "a # u" v] \<sigma>_complete[unfolded eqs] Suc
        using derives_Cons shift by auto
    next
      case (reduce Y \<alpha>' X \<beta>' \<gamma>' \<rho>' y)
      then show ?thesis using less.prems(1)[of 0 n "[]" w] less.prems(2) by force
    next
      case (expand Y \<gamma>' X \<alpha>' \<beta>' i \<rho>' y)
      with \<sigma>_complete have eqs: "B = Y" "w = u @ v" "X = A" "\<delta> = \<gamma>'" "\<beta> = Nt Y # \<beta>'" by auto
      with expand step step_imp_in_Prods have Y_derives: "Prods G' \<turnstile> [Nt Y] \<Rightarrow>* map Tm u" 
        using \<sigma>_complete(3) by (metis append.right_neutral append_Nil derives_Cons_rule item.case)
      from eqs expand have exp_step:
        "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) 
          \<turnstile> ([Y \<rightarrow> [] . \<gamma>'] # [A \<rightarrow> \<alpha> . Nt Y # \<beta>'] # \<rho> @ [init_symbol M], u @ v)"
        using step by auto
      moreover with \<sigma>_complete eqs have j_steps: 
        "... \<turnstile>(j) ([Y \<rightarrow> \<gamma>' . []] # [A \<rightarrow> \<alpha> . Nt Y # \<beta>'] # \<rho> @ [init_symbol M], v)"
        using expand by simp
      moreover have reduct_step: "... \<turnstile> ([A \<rightarrow> \<alpha> @ [Nt Y] . \<beta>'] # \<rho> @ [init_symbol M], v)"
        using expand step step_imp_in_Prods by force
      moreover with less.IH obtain v' x' j' k' l where complete_reaches: "v = v' @ x'" "Prods G' \<turnstile> \<beta>' \<Rightarrow>* map Tm v'"
        "... \<turnstile>(j') ([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], x')"
        "([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], x') \<turnstile>(k') ([final_state, init_symbol M], [])"
        "k = Suc l"
        "j' + k' = l"
      proof - (* TODO refactor *)
        from expand step \<sigma>_complete eqs have 
          "([Y \<rightarrow> \<gamma>' . []] # [A \<rightarrow> \<alpha> . Nt Y # \<beta>'] # \<rho> @ [init_symbol M], v) 
            \<turnstile>(k) ([final_state, init_symbol M], [])"
          by auto
        moreover have "[Y \<rightarrow> \<gamma>' . []] # [A \<rightarrow> \<alpha> . Nt Y # \<beta>'] # \<rho> @ [init_symbol M] 
          \<noteq> [final_state, init_symbol M]"  by auto
        ultimately obtain l where l_steps: "k = Suc l"
          "([A \<rightarrow> \<alpha> @ [Nt Y] . \<beta>'] # \<rho> @ [init_symbol M], v) \<turnstile>(l) ([final_state, init_symbol M], [])"
          using eqs step \<sigma>_complete reducing stepn_neq_imp_not_expanding_reaches reduct_step 
          by (metis list.sel(1) prod.inject)
        moreover with \<sigma>_complete(6) Suc have lt: "l < n" by linarith
        ultimately show thesis using less.IH[OF lt _ l_steps(2)] that expand eqs
          by (smt (verit, best) Cons_eq_append_conv append.assoc append_self_conv2)
      qed
      ultimately have A_completes: "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) 
          \<turnstile>(Suc (Suc j) + j') ([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], x')"
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
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) \<turnstile>* ([final_state, init_symbol M], [])"
  obtains u v where 
    "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([A \<rightarrow> \<alpha> . \<beta>] # \<rho> @ [init_symbol M], w) \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], v)"
    "([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], v) \<turnstile>* ([final_state, init_symbol M], [])"
proof -
  from assms have A_in_Prods: "(A, \<alpha> @ \<beta>) \<in> Prods G'" 
    using reaches_final_imp_in_It in_It_imp_in_Prods by fastforce
  from reaches_final_imp_complete_reaches_final assms rtranclp_imp_relpowp obtain u v where complete:
    "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([A \<rightarrow> \<alpha> @ \<beta> . []] # \<rho> @ [init_symbol M], v) \<turnstile>* ([final_state, init_symbol M], [])" 
    using relpowp_imp_rtranclp by metis
  with derives_imp_completes[OF this(2), of A \<alpha> "[]"] A_in_Prods show thesis using that
    by simp
qed

lemma reaches_final_imp_second_is_chain:
  assumes "([A \<rightarrow> \<alpha> . \<beta>] # i # \<rho> @ [init_symbol M], w) \<turnstile>* ([final_state, init_symbol M], [])"
  obtains X \<alpha>' \<beta>' where "i = [X \<rightarrow> \<alpha>' . Nt A # \<beta>']"
proof -
  from assms reaches_final_imp_completes obtain x where 
    "([A \<rightarrow> \<alpha> @ \<beta> . []] # i # \<rho> @ [init_symbol M], x) \<turnstile>* ([final_state, init_symbol M], [])"
    by (metis Cons_eq_appendI)
  then show thesis
  proof (cases rule: converse_rtranclpE)
    case (step y)
    from this(1) show ?thesis 
      using that by cases auto
  qed force
qed

lemma reaches_without_stack_imp_S':
  assumes "([[A \<rightarrow> \<alpha> . \<beta>], init_symbol M], w) \<turnstile>* ([final_state, init_symbol M], [])"
  shows "[A \<rightarrow> \<alpha> . \<beta>] = init_state M \<or> [A \<rightarrow> \<alpha> . \<beta>] = final_state"
proof -
  from reaches_final_imp_completes[of _ _ _ "[]"] assms obtain u v where "w = u @ v"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
    "([[A \<rightarrow> \<alpha> . \<beta>], init_symbol M], w) \<turnstile>* ([[A \<rightarrow> \<alpha> @ \<beta> . []], init_symbol M], v)"
    "([[A \<rightarrow> \<alpha> @ \<beta> . []], init_symbol M], v) \<turnstile>* ([final_state, init_symbol M], [])"
    (is "?complete \<turnstile>* ?final")
    by (metis append_Nil)
  from this(4) have "?complete = ?final"
    using init_symbol_notin_It second_notin_It_imp_complete_step_impossible 
    by (cases rule: converse_rtranclpE) blast+
  thus ?thesis by (simp add: append_eq_Cons_conv)
qed

definition Lang :: "'t list set" where
  "Lang \<equiv> {w. ([init_state M, init_symbol M], w) \<turnstile>* ([final_state, init_symbol M], [])}"

lemma hist_init [simp]:
  "hist (\<rho> @ [init_symbol M]) = hist \<rho>"
  using IPDA_def by (induction \<rho>) auto


lemma invariant: 
  assumes "([init_state M, init_symbol M], u@v) \<turnstile>* (\<rho>, v)" (is "(?S,_) \<turnstile>* _")
  shows "Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u"
proof -
  from assms obtain n where "([init_state M, init_symbol M], u@v) \<turnstile>(n) (\<rho>, v)"
    using rtranclp_imp_relpowp by fast
  then show ?thesis
  proof (induction n arbitrary:u v \<rho>)
    case (Suc n)
    then obtain \<sigma> w where n_steps: "(?S, u @ v) \<turnstile>(n) (\<sigma>, w)" "(\<sigma>, w) \<turnstile> (\<rho>, v)"
      by auto
    from this(2) show ?case 
    proof (cases rule: step_cases)
      case (shift A \<alpha> a \<beta> i \<tau>)
      with steps_shift_decomp n_steps(1)[THEN relpowp_imp_rtranclp]
      obtain x where u_decomp: "u = x @ [a]" "w = a # v" 
        using n_steps(2) by blast
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
        from reduce have "hist \<rho> = hist \<tau> @ \<beta> @ [Nt Y]" by simp
        also have "Prods G \<turnstile> ... \<Rightarrow>* hist \<tau> @ \<beta> @ \<alpha>"
          using Y_prod derives_prepend by (metis derive_singleton r_into_rtranclp) 
        also have "... = hist \<sigma>" using reduce by auto
        finally show ?thesis .
      qed
      also from reduce n_steps(1) Suc.IH have "Prods G \<turnstile> ... \<Rightarrow>* map Tm u" by blast
      finally show ?thesis .
    next
      case (expand Y \<alpha> X \<beta> \<gamma> i \<tau> x)
      with n_steps(1) Suc.IH show ?thesis by fastforce
    qed
  qed (simp add: hist_defs)
qed

lemma Lang_subst_Lang_G:
  "Lang \<subseteq> LangS G"
  unfolding Lang_def Context_Free_Grammar.Lang_def S_def 
  by (standard, metis Nil_is_append_conv append.right_neutral hist_Cons hist_singleton
    init_symbol_ipda invariant mem_Collect_eq)

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
    "([[S' \<rightarrow> \<alpha> . \<beta>], init_symbol M], v) \<turnstile>* ([final_state, init_symbol M], [])"
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
        Lang_eq_Lang_G Lang_preserved hist_singleton rtrancl_refl init_state_ipda ipda by force
  qed
qed

end

end
