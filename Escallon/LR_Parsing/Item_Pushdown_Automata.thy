theory Item_Pushdown_Automata
  imports 
    Extended_Cfg
    Pushdown_Automata.Pushdown_Automata
begin

definition (in Extended_Cfg) IPDA :: "(('n, 't) item, 't, ('n, 't) item) pda" where
  "IPDA \<equiv> let
    P = Prods G';
    \<Delta> = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {});
    \<E> = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> P} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})         
in
  \<lparr>init_state = [S' \<rightarrow> [] . [Nt S]], init_symbol = [S' \<rightarrow> [] . []], 
    final_states = {[S' \<rightarrow> [Nt S] . []]}, delta = \<Delta>, delta_eps = \<E>\<rparr>"


locale ipda = Extended_Cfg G for G :: "('n::fresh0, 't) Cfg" +
  fixes M :: "(('n, 't) item, 't, ('n, 't) item) pda"
  assumes ipda: "M = Extended_Cfg.IPDA G"
begin


lemma init_state_ipda [simp]:
  "init_state M = [S' \<rightarrow> [] . [Nt S]]"
  using ipda unfolding IPDA_def by simp

lemma init_symbol_ipda [simp]:
  "init_symbol M = [S' \<rightarrow> [] . []]"
  using ipda unfolding IPDA_def by simp

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
  using ipda unfolding IPDA_def by simp

lemma delta_ipda [simp]:
  "delta M = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {})"
using ipda unfolding IPDA_def by simp

lemma delta_eps_ipda [simp]:
  "delta_eps M = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> Prods G'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})"
  using ipda unfolding IPDA_def by simp


lemma delta_Tm_neq_empty [simp]:
  assumes "a \<noteq> b"
  shows "delta M ([X \<rightarrow> \<alpha> . Tm a # \<gamma>]) b q = {}"
  using assms unfolding IPDA_def by simp

lemma delta_nempty_imp_Tm_eq:
  assumes "delta M p a q \<noteq> {}"
  obtains X \<beta> \<gamma> where "p = [X \<rightarrow> \<beta> . Tm a # \<gamma>]"
proof -
  obtain X \<beta> \<alpha> where p_def: "p = [X \<rightarrow> \<beta> . \<alpha>]" using item.exhaust by blast
  then consider (Nil) "\<alpha> = []" | (Tm_eq) \<gamma> where "\<alpha> = Tm a # \<gamma>" | 
   (Tm_neq) a' \<gamma> where "\<alpha> = Tm a' # \<gamma>" "a' \<noteq> a" | (Nt) A \<gamma> where "\<alpha> = Nt A # \<gamma>"
    using list.exhaust sym.exhaust by metis
  then show thesis using p_def assms that by cases auto
qed

lemma delta_eps_Nt_neq_empty [simp]:
  assumes "Y \<noteq> Y'"
  shows "delta_eps M ([Y \<rightarrow> \<alpha> . []]) ([X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) = {}"
  using assms unfolding IPDA_def by simp


lemma delta_eps_complete_imp_reducing:
  assumes "delta_eps M ([Y \<rightarrow> \<alpha> . []]) q \<noteq> {}"
  obtains X \<beta> \<gamma> where "q = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]"
proof -
  obtain X \<beta> \<gamma> where q_def: "q = [X \<rightarrow> \<beta> . \<gamma>]" using item.exhaust by metis
  then show thesis
  proof (cases \<gamma>)
    case (Cons a as)
    then show ?thesis 
    by (cases a) (use assms q_def Cons that in fastforce)+
  qed (use assms q_def in fastforce)
qed

lemma delta_eps_nempty_imp_expanding_or_reducing:
  assumes "delta_eps M p q \<noteq> {}"
  obtains X \<beta> Y \<gamma> where "p = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]"  |
    Y \<alpha> X \<beta>  \<gamma> where "p = [Y \<rightarrow> \<alpha> . []]" "q = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]"
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
      by (cases a) (use p_def assms that in auto)
  qed
qed

lemmas init_defs = init_state_def init_symbol_def

lemma in_final_imp_final_state:
  assumes "q \<in> final_states M"
  shows "q = final_state"
  using assms unfolding IPDA_def S'_def S_def by simp

inductive step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 70) where
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


lemma shift [simp]:
  "([A \<rightarrow> \<alpha> . Tm a # \<beta>]#\<rho>#\<rho>s, a#u) \<turnstile> ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#\<rho>#\<rho>s, u)"
proof -
  have "([A \<rightarrow> \<alpha>@[Tm a] . \<beta>], [\<rho>]) \<in> delta M ([A \<rightarrow> \<alpha> . Tm a # \<beta>]) a \<rho>"
    using IPDA_def by simp
  then show ?thesis using delta 
    by (metis Cons_eq_appendI append.left_neutral)
qed

lemma shifting [simp]:
  "([A \<rightarrow> \<alpha> . Tm a # \<beta>]#\<rho>@[init_symbol M], a#u) \<turnstile> ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#\<rho>@[init_symbol M], u)"
  by (cases \<rho>) auto


lemma reducing [simp]:
  "([Y \<rightarrow> \<alpha> . []]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]#\<rho>, w)"
proof -
  have "([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>], []) \<in> delta_eps M ([Y \<rightarrow> \<alpha> . []]) ([X \<rightarrow> \<beta> . Nt Y#\<gamma>])"
    unfolding IPDA_def by simp
  thus ?thesis using eps by (metis Cons_eq_appendI append.left_neutral)
qed


lemma expanding_in_delta_eps:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([Y \<rightarrow> [] . \<alpha>], [[X \<rightarrow> \<beta> . Nt Y#\<gamma>], i]) \<in> delta_eps M ([X \<rightarrow> \<beta> . Nt Y#\<gamma>]) i"
  using assms ipda unfolding G'_def S'_def S_def IPDA_def by auto

lemma expanding_Cons [simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
  using expanding_in_delta_eps[OF assms] eps 
  by (metis eq_Nil_appendI Cons_eq_appendI)

lemma expanding:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w)"
  using assms by (cases \<rho>) auto

lemma expanding_singleton:
  assumes "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<alpha>"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w)"
  using assms expanding by (simp add: derive_singleton)

lemma expanding_singleton_Cons:
  assumes "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<alpha>"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
  using assms expanding_Cons by (simp add: derive_singleton)

lemma in_delta_imp_shifting:
  assumes "(q, qs) \<in> delta M p0 a p1"
  obtains X \<beta> \<gamma> where "p0 = [X \<rightarrow> \<beta> . Tm a # \<gamma>]"
    "(q,qs) = ([X \<rightarrow> \<beta> @ [Tm a] . \<gamma>], [p1])"
proof -
  from assms have "delta M p0 a p1 \<noteq> {}" by auto
  from delta_nempty_imp_Tm_eq[OF this] 
    obtain X \<beta> \<gamma> where p0_def: "p0 = [X \<rightarrow> \<beta> . Tm a # \<gamma>]" by blast
  hence "delta M p0 a p1 = {([X \<rightarrow> \<beta> @ [Tm a] . \<gamma>], [p1])}" by simp
  with assms show thesis using delta_ipda that p0_def 
    by (metis (lifting) singletonD)
qed

lemma eps_cases[consumes 1, case_names reducing expand]:
  assumes "(q0,qs) \<in> delta_eps M p0 p1"
  obtains Y \<alpha> X \<beta> \<gamma> where
    "p0 = [Y \<rightarrow> \<alpha> . []]" "p1 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "q0 = [X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]" "qs = []" |
    X \<beta> Y \<gamma> \<alpha> where
    "p0 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" "(Y, \<alpha>) \<in> Prods G'" "q0 = [Y \<rightarrow> [] . \<alpha>]" "qs = p0#[p1]" 
proof -
  from delta_eps_nempty_imp_expanding_or_reducing consider 
    X \<beta> Y \<gamma> where "p0 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" |
    Y \<alpha> X \<beta> \<gamma> where "p0 = [Y \<rightarrow> \<alpha> . []]" "p1 = [X \<rightarrow> \<beta> . Nt Y # \<gamma>]" 
    using assms by blast
  then show thesis
    by cases (use that assms in auto) 
qed

lemma step_cases[consumes 1, case_names shift reduct expand, cases set: step]:
  assumes "c0 \<turnstile> c1"
obtains A \<alpha> a \<beta> i \<rho> u where 
    "c0 = ([A \<rightarrow> \<alpha> . Tm a # \<beta>]#i#\<rho>, a#u)" "c1 = ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#i#\<rho>, u)" |
    Y \<alpha> X \<beta> \<gamma> \<rho> w where
      "c0 = ([Y \<rightarrow> \<alpha> . []]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>, w)"  "c1 = ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]#\<rho>, w)" |
    Y \<alpha> X \<beta> \<gamma> i \<rho> w where 
    "c0 = ([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"  "c1 = ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
      "(Y, \<alpha>) \<in> Prods G'"
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

lemma step_imp_in_It:
  assumes "i0 \<in> It G'" "i1 \<in> It G'"
    "(i0#i1#is, u) \<turnstile> (j#js, v)"
  shows "j \<in> It G'"
  using assms(3,1,2) by (cases rule: step_cases) (simp add: It_defs)+


lemma Prods_G_closed_expanding:
  assumes "([X \<rightarrow> \<alpha> . Nt Y # \<beta>] # \<rho>, u) \<turnstile> ([Y \<rightarrow> [] . \<gamma>] # [X \<rightarrow> \<alpha> . Nt Y # \<beta>] # \<rho>, v)"
    "(X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G"
  shows "(Y, \<gamma>) \<in> Prods G"
  using assms proof cases
  case (expand Y \<alpha>' X \<beta>' \<gamma> i \<rho> w)
  hence "(Y, \<alpha>') \<in> Prods G \<or> (Y, \<alpha>') = (S', [Nt S])" unfolding G'_def by auto
  hence "(Y, \<alpha>') \<in> Prods G"
  proof
    assume "(Y, \<alpha>') = (S' , [Nt S])"
    with assms(2) S'_Prod_notin_G(2)[of "\<alpha> @ Nt Y # \<beta>"] expand show ?thesis by simp
  qed simp
  then show ?thesis using expand by blast
qed simp+


abbreviation steps (infix \<open>\<turnstile>*\<close> 50) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

abbreviation stepn ( \<open>_ \<turnstile>'(_') _\<close> 50) where
  "stepn c0 n c1 \<equiv> (step ^^ n) c0 c1"

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by (induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct)
  (use step_len_dec surj_pair le_trans in fastforce)+

lemma completes_Tms_Cons:
  "([A \<rightarrow> \<alpha> . map Tm u @ \<beta>]#i#is, u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . \<beta>]#i#is, v)"
proof (induction u arbitrary: \<alpha>)
  case (Cons a u)
  have "([A \<rightarrow> \<alpha> . map Tm (a # u) @ \<beta>] # i # is, (a # u) @ v) 
        \<turnstile> ([A \<rightarrow> \<alpha> @ [Tm a] . map Tm u @ \<beta>] # i # is, u @ v)"
    by simp
  also note Cons[of "\<alpha>@[Tm a]"] 
  finally show ?case by auto
qed simp

lemma stepn_Suc_imp_two_items:
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
    using that by cases auto
qed

lemma completes_Tms:
  "([A \<rightarrow> \<alpha> . map Tm u @ \<beta>]#\<rho>@[init_symbol M], u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . \<beta>]#\<rho>@[init_symbol M], v)"
  using completes_Tms_Cons by (cases \<rho>) auto

lemma reachable_imp_in_It:
  "\<lbrakk>([init_state M, init_symbol M], u) \<turnstile>* (\<rho>, v); i \<in> set \<rho> - {init_symbol M}\<rbrakk> 
    \<Longrightarrow> i \<in> It G'"
proof (induction arbitrary: i rule: rtranclp_induct2)
  case (step \<rho>0 u \<rho>1 v)
  from step(2) show ?case 
    using step(3,4) by (cases rule: step_cases) (fastforce simp: It_defs)+ 
qed (auto simp: It_defs G'_def)

lemma reachable_imp_not_Nil:
  "\<lbrakk>(\<rho>, u) \<turnstile>* (\<sigma>, v); \<rho> \<noteq> []\<rbrakk> \<Longrightarrow> \<sigma> \<noteq> []"
  by (induction rule: rtranclp_induct2)
    (simp, use step.cases in blast)

lemma reachable_imp_hd_not_init_symbol:
  assumes "([init_state M, init_symbol M], u) \<turnstile>* (i#\<rho>, v)"
  shows "i \<noteq> init_symbol M"
proof -
  from assms obtain n where "([init_state M, init_symbol M], u) \<turnstile>(n) (i#\<rho>, v)"
    using rtranclp_imp_relpowp by fast
  then show ?thesis
  proof (induction n arbitrary: i \<rho> v)
    case (Suc n)
    then obtain j \<sigma> w where n_steps: "([init_state M, init_symbol M], u) \<turnstile>(n) (j#\<sigma>, w)"
      "(j#\<sigma>, w) \<turnstile> (i#\<rho>, v)" using reachable_imp_not_Nil 
      by (metis neq_Nil_conv relpowp_Suc_E rtranclp_power surj_pair)
    with Suc have j_not_init: "j \<noteq> init_symbol M" by fast
    from n_steps(2) show ?case 
      by cases (use in_Prods_imp_item_neq_init_symbol in force)+
  qed force
qed

corollary reachable_imp_head_in_It:
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
    using G'_def S_neq_S' that by auto
qed auto

lemma final_state_step_impossible:
  assumes "([[S' \<rightarrow> \<alpha> . []], init_symbol M], u) \<turnstile> c"
  shows False
  using assms by cases simp+
  


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
        using final_state_step_impossible[of "[Nt S]"] append_eq_Cons_conv by fastforce 
      with n_steps init_state_expands show ?thesis 
        using Suc.prems(2)[of _ "[]" "[Nt S]"] \<sigma>_init by force
    next
      case (Cons i \<nu>)
      hence \<sigma>_def: "\<sigma> = i # \<nu> @ [[S' \<rightarrow> \<alpha> . \<beta>], init_symbol M]" using \<tau>_def by simp
      from n_steps(2)[unfolded this] show ?thesis 
      proof cases
        case (expand Y \<alpha>' X \<beta>' \<gamma> j \<rho>' w')
        moreover with Cons have
          "\<rho> = [Y \<rightarrow> [] . \<alpha>'] # \<tau> @ [[S' \<rightarrow> \<alpha> . \<beta>], init_symbol M]" by simp
        moreover from expand \<tau>_def Cons have "\<forall>i\<in>set ([Y \<rightarrow> [] . \<alpha>'] # \<tau>). ?in_Prods i" 
        proof -
          from expand \<tau>_def Cons have "(X, \<beta>' @ Nt Y # \<gamma>) \<in> Prods G" by auto
          from Prods_G_closed_expanding[OF _ this] expand n_steps(2) \<tau>_def(3) show ?thesis 
            by (metis append_Nil expanding_Cons item.case set_ConsD)
        qed
        ultimately show ?thesis using Suc.prems(2) \<tau>_def Cons by fastforce
      qed (cases \<nu>, (use \<tau>_def Cons Suc in auto))+
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
  ultimately show thesis using that by auto
qed

corollary reachable_snd_not_empty_imp_hd_in_G:
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
  shows "([A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], u @ v) 
          \<turnstile>* ([A \<rightarrow> \<alpha> @ [Nt X] . \<beta>] # \<rho> @ [init_symbol M], v)"
proof -
  from assms derive_singleton[of "Prods G'" "Nt X" "map Tm u"] expanding have 
    "([A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], u @ v) 
      \<turnstile> ([X \<rightarrow> [] . map Tm u] # [A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], u @ v)"
    by auto
  also from completes_Tms have 
    "... \<turnstile>* ([X \<rightarrow> map Tm u . []] # [A \<rightarrow> \<alpha> . [Nt X] @ \<beta>] # \<rho> @ [init_symbol M], v)" 
    by (metis append.right_neutral append_Nil completes_Tms_Cons)
  also have "... \<turnstile> ([A \<rightarrow> \<alpha> @ [Nt X] . \<beta>] # \<rho> @ [init_symbol M], v)"
    by simp
  finally show ?thesis .
qed


lemma derive_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow> map Tm w"
  shows "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>] # \<rho> @ [init_symbol M], w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
proof -
  from derive_decomp[OF assms] obtain u v X y where \<beta>_decomp:
    "\<beta> = map Tm u @ Nt X # map Tm y" "Prods G' \<turnstile> [Nt X] \<Rightarrow> map Tm v" "w = u @ v @ y" by metis
  with completes_Tms[of A \<alpha> u "Nt X # map Tm y @ \<gamma>" _ "v @ y @ x"] have 
    "([A \<rightarrow> \<alpha> . \<beta> @ \<gamma>] # \<rho> @ [init_symbol M], w @ x) 
      \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . Nt X # map Tm y @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x)" 
    by simp
  also from singleton_derive_imp_completes[OF \<beta>_decomp(2), of _ "\<alpha> @ map Tm u" _ _ "y@x"] have 
    "... \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u @ [Nt X] . map Tm y @ \<gamma>] # \<rho> @ [init_symbol M], y @ x)"
    by simp
  also from completes_Tms have "... \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
    using \<beta>_decomp by (smt (verit, best) append.assoc append_Cons append_Nil)
  finally show ?thesis .
qed


lemma derives_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w"
  shows "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>] # \<rho> @ [init_symbol M], w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
proof -
  from assms obtain n where "Prods G' \<turnstile> \<beta> \<Rightarrow>(n) map Tm w" 
    using rtranclp_imp_relpowp by fast
  then show ?thesis
  proof (induction n arbitrary: \<beta> w A \<alpha> \<gamma> \<rho> x rule: less_induct)
    case (less n)
    then show ?case 
    proof (cases n)
      case (Suc m)
      note Suc_m = this
      with derives_decomp_less obtain \<delta>\<^sub>1 i u X j v \<delta>\<^sub>2 k y where
        decomp:
        "\<beta> = \<delta>\<^sub>1 @ Nt X # \<delta>\<^sub>2"
        "Prods G' \<turnstile> \<delta>\<^sub>1 \<Rightarrow>(i) map Tm u" "Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v" "Prods G' \<turnstile> \<delta>\<^sub>2 \<Rightarrow>(k) map Tm y"
        "w = u @ v @ y" "i + j + k = n" "j > 0" 
        using less(2)  by (smt (verit, best))
      hence leqs: "i < n" "k < n" by auto
      have first: "([A \<rightarrow> \<alpha> . \<beta> @ \<gamma>] # \<rho> @ [init_symbol M], w @ x) 
              \<turnstile>* ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 . Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x)"
        (is "_ \<turnstile>* (?\<sigma>, _)")
        using less(1)[OF leqs(1) decomp(2), of _ _ "Nt X # \<delta>\<^sub>2 @ \<gamma>" _ "v @ y @ x"]
          decomp by simp
      have last: "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] . \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], y @ x) 
                  \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)"
        using less(1)[OF leqs(2) decomp(4), of _ "\<alpha> @ \<delta>\<^sub>1 @ [Nt X]"] decomp(1) by simp
      show ?thesis 
      proof (cases "j = n")
        case True
        with decomp have Tms: "i = 0" "k = 0" "\<delta>\<^sub>1 = map Tm u" "\<delta>\<^sub>2 = map Tm y"
          by auto
        from True decomp(6,7) Suc obtain \<beta>' where m_steps:
          "Prods G' \<turnstile> [Nt X] \<Rightarrow> \<beta>'" "Prods G' \<turnstile> \<beta>' \<Rightarrow>(m) map Tm v"
          using decomp(3) by (meson relpowp_Suc_D2)
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
            using \<beta>'_decomp(7) by (metis order_less_trans)
          note first
          also from m_steps \<beta>'_decomp(1) have 
            "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 . Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x) 
              \<turnstile> ([X \<rightarrow> [] . \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v @ y @ x)"
            using expanding_singleton by simp
          also from less(1)[OF \<beta>'_decomp(6,2), of _ _ _ _ "v' @ y' @ y @ x"] 
          have "... \<turnstile>* ([X \<rightarrow> \<xi>\<^sub>1 . Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v' @ y' @ y @ x)" 
               (is "_ \<turnstile>* (?\<tau>, _)")
            by (metis \<beta>'_decomp(5) append.assoc append_Cons append_Nil)
          also from Y_prod(1) have "... \<turnstile> ([Y \<rightarrow> [] . \<gamma>'] # ?\<tau>, v' @ y' @ y @ x)" 
            using expanding_singleton by fastforce
          also from less(1)[OF Y_prod(3,2), of Y "[]" "[]" _ "y' @ y @ x"]
          have "... \<turnstile>* ([Y \<rightarrow> \<gamma>' . []] # ?\<tau>, y' @ y @ x)" 
            by (smt (verit, best) Cons_eq_appendI append.right_neutral self_append_conv2)
          also have "... \<turnstile> ([X \<rightarrow> \<xi>\<^sub>1 @ [Nt Y] . \<xi>\<^sub>2] # ?\<sigma>, y' @ y @ x)"
            using reducing by presburger
          also from less(1)[OF \<beta>'_decomp(8,4), of X _ "[]" _ "y @ x"] have
            "... \<turnstile>* ([X \<rightarrow> \<beta>' . []] # ?\<sigma>, y @ x)"
            using \<beta>'_decomp(1) append.assoc by (metis append.right_neutral append_Cons append_Nil)
          finally show ?thesis using reducing last 
            by (smt (verit, best) append_eq_appendI converse_rtranclp_into_rtranclp rtranclp_trans)
        qed (use derive_imp_completes decomp Tms Suc_m less.prems relpowp_Suc_0 in metis)
      next
        case False
        hence "j < n" using decomp by linarith
        then show ?thesis
          using first last derivern_singleton_imp_prod[OF decomp(3)]
          by (smt (verit, ccfv_threshold) append.assoc append_Cons append_Nil decomp(3) less.IH
              rtranclp_trans)
      qed
    qed (use completes_Tms in simp)
  qed
qed



definition Lang :: "'t list set" where
  "Lang \<equiv> {w. ([init_state M, init_symbol M], w) \<turnstile>* ([final_state, init_symbol M], [])}"


lemma hist_singleton_init [simp]:
  "hist ([[A \<rightarrow> \<alpha> . \<beta>], init_symbol M]) = \<alpha>"
  unfolding IPDA_def using hist_singleton by auto

lemma hist_init [simp]:
  "hist (\<rho> @ [init_symbol M]) = hist \<rho>"
  using IPDA_def by (induction \<rho>) auto

lemma hd_in_prods_imp_derives_expanded_hist:
  assumes "(Y, \<alpha>) \<in> P"
  shows "P \<turnstile> hist ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>] # \<rho>) \<Rightarrow>*  hist ([Y \<rightarrow> \<alpha> . []] # [X \<rightarrow> \<beta> . Nt Y # \<gamma>] # \<rho>)"         
    (is "P \<turnstile> ?h1 \<Rightarrow>* ?h2")
  using assms by (auto simp: derive_prepend derive_singleton r_into_rtranclp)


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
      case (reduct Y \<alpha> X \<beta> \<gamma> \<tau> x)
      have "Prods G \<turnstile> hist \<rho> \<Rightarrow>* hist \<sigma>"
      proof -
        from n_steps reduct have Y_prod: "(Y, \<alpha>) \<in> Prods G" 
          using reachable_snd_not_empty_imp_hd_in_G 
            relpowp_imp_rtranclp by fastforce
        from reduct have "hist \<rho> = hist \<tau> @ \<beta> @ [Nt Y]" by simp
        also have "Prods G \<turnstile> ... \<Rightarrow>* hist \<tau> @ \<beta> @ \<alpha>"
          using Y_prod derives_prepend by (metis derive_singleton r_into_rtranclp) 
        also have "... = hist \<sigma>" using reduct by auto
        finally show ?thesis .
      qed
      also from reduct n_steps(1) Suc.IH have "Prods G \<turnstile> ... \<Rightarrow>* map Tm u" by blast
      finally show ?thesis .
    next
      case (expand Y \<alpha> X \<beta> \<gamma> i \<tau> x)
      with n_steps(1) Suc.IH show ?thesis by fastforce
    qed
  qed (simp add: hist_defs)
qed

corollary Lang_subst_Lang_G:
  "Lang \<subseteq> LangS G"
  unfolding Lang_def Context_Free_Grammar.Lang_def S_def 
  by (standard, metis invariant append.right_neutral hist_singleton_init mem_Collect_eq)

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
    "([[S' \<rightarrow> \<alpha> . \<beta>], init_symbol IPDA], v) \<turnstile>* ([final_state, init_symbol IPDA], [])"
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
