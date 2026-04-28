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


lemma shifting_Cons [simp]:
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

lemma expanding [simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>@[init_symbol M], w)"
  using assms by (cases \<rho>) auto

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

lemma eps_cases[consumes 1, case_names reducing expanding_Cons]:
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

lemma step_cases[consumes 1, case_names shifting_Cons reducing expanding_Cons]:
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


abbreviation steps (infix \<open>\<turnstile>*\<close> 70) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

abbreviation stepn ( \<open>_ \<turnstile>'(_') _\<close> 70) where
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

lemma completes_Tms:
  "([A \<rightarrow> \<alpha> . map Tm u @ \<beta>]#\<rho>@[init_symbol M], u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . \<beta>]#\<rho>@[init_symbol M], v)"
  using completes_Tms_Cons by (cases \<rho>) auto


lemma reachable_imp_in_It:
  "\<lbrakk>([init_state M, init_symbol M], u) \<turnstile>* (\<rho>1, v); i \<in> set \<rho>1 - {init_symbol M}\<rbrakk> 
    \<Longrightarrow> i \<in> It G'"
proof (induction arbitrary: i rule: rtranclp_induct2)
  case (step \<rho>0 u \<rho>1 v)
  from step(2) show ?case 
    using step(3,4) by (cases rule: step_cases) (fastforce simp: It_defs)+ 
qed (auto simp: It_defs G'_def)


lemma steps_substring:
  assumes "(\<rho>0, w) \<turnstile>* (\<rho>2, v)"
  obtains u where "w = u@v"
  sorry

lemma list_app_last_is_next_hd:
  assumes "w = u@v@y"
    "w = xs@a#y"
    "v \<noteq> []"
  shows "last v = a"
  using assms 
  by (metis append.assoc append_Cons append_Nil append_same_eq last_append last_snoc)

lemma reachable_imp_reachable_substring:
  assumes "(\<rho>0, u) \<turnstile>* (\<rho>2, y)"
    "u = v@w@y"
  obtains \<rho>1 where "(\<rho>0, u) \<turnstile>* (\<rho>1, w@y)"
proof -
  from assms(1) obtain n where "(\<rho>0, u) \<turnstile>(n) (\<rho>2, y)"
    by (metis rtranclp_imp_relpowp)
  with assms(2) obtain \<rho>1 where "(\<rho>0, u) \<turnstile>* (\<rho>1, w@y)"
  proof (induction n arbitrary: \<rho>2 v w y thesis rule: less_induct)
    case (less n)
    show ?case 
    proof (cases n)
      case (Suc m)
      with less(4) obtain \<rho>1 z where msteps: "(\<rho>0, u) \<turnstile>(m) (\<rho>1, z)" "(\<rho>1, z) \<turnstile> (\<rho>2, y)" by auto
      from msteps(2) consider "z = y" | a where "z = a#y" using step.cases by blast
      then show ?thesis
      proof cases
        case 1
        with less(1,3) msteps(1) Suc obtain \<rho>' where "(\<rho>0, u) \<turnstile>* (\<rho>', w @ y)" by blast
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
          from less(1)[OF _ _ this msteps(1)] obtain \<rho>' where "(\<rho>0, u) \<turnstile>* (\<rho>', cs @ z)"
            using Suc by blast
          then show ?thesis using cs_def 2 less(2) by simp
        qed (use less rtranclp_power append_Nil in metis)
      qed
    qed (use less that in auto)
  qed
  then show thesis using that by blast
qed


lemma syms_tl_imp_substring:
  assumes "([A \<rightarrow> \<alpha> . \<beta> @ map Tm u]#\<rho>, v) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta>@map Tm u . []]#\<rho>', w)"
  obtains v' where "v = v'@u"
  oops


(* TODO review *)
corollary reaches_final_imp_substring:
  assumes "([A \<rightarrow> \<alpha> . \<beta> @ map Tm u]#\<rho>, v) \<turnstile>* ([final_state, init_symbol M], [])"
  obtains v' where "v = v'@u"
  oops

lemma derivern_last_step:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r(Suc n) map Tm w"
  obtains u A v where "P \<turnstile> \<alpha> \<Rightarrow>r(n) map Tm u@Nt A#map Tm v" "P \<turnstile> map Tm u@Nt A#map Tm v \<Rightarrow>r map Tm w"
  using assms proof (induction n arbitrary: \<alpha> thesis w)
  case 0
  hence "P \<turnstile> \<alpha> \<Rightarrow>r map Tm w" by auto
  then obtain x A \<beta> v where "\<alpha> = x@Nt A#map Tm v" "x@\<beta>@map Tm v = map Tm w" 
    using deriver.cases by metis
  then show ?case using 0 
    by (smt (verit, best) map_eq_append_conv relpowp_0_E relpowp_Suc_E)
next
  case (Suc n)
  from Suc(3) obtain \<beta> where "P \<turnstile> \<alpha> \<Rightarrow>r \<beta>" "P \<turnstile> \<beta> \<Rightarrow>r(Suc n) map Tm w" 
    by (metis relpowp_Suc_D2)
  then show ?case using Suc by (metis relpowp_Suc_I2)
qed

lemma derivers_induct[consumes 1, case_names base step]:
  assumes "P \<turnstile> xs \<Rightarrow>r* ys"
  and "Q xs"
  and "\<And>u A v w. \<lbrakk> P \<turnstile> xs \<Rightarrow>r* u @ Nt A #  map Tm v; Q (u @ Nt A # map Tm v); (A,w) \<in> P \<rbrakk> 
      \<Longrightarrow> Q (u @ w @ map Tm v)"
  shows "Q ys"
using assms
proof (induction rule: rtranclp_induct)
  case base
  from this(1) show ?case .
next
  case (step y z)
  from deriver.cases[OF step(2)] step(1,3-) show ?case by metis
qed

lemma derivern_induct[consumes 1, case_names 0 Suc]:
  assumes "P \<turnstile> xs \<Rightarrow>r(n) ys"
  and "Q 0 xs"
  and "\<And>n u A v w. \<lbrakk> P \<turnstile> xs \<Rightarrow>r(n) u @ Nt A#map Tm v; Q n (u @ Nt A#map Tm v); (A,w) \<in> P \<rbrakk> 
    \<Longrightarrow> Q (Suc n) (u @ w @ map Tm v)"
  shows "Q n ys"
using assms(1) proof (induction n arbitrary: ys)
  case 0
  thus ?case using assms(2) by auto
next
  case (Suc n)
  from relpowp_Suc_E[OF Suc.prems]
  obtain xs' where n: "P \<turnstile> xs \<Rightarrow>r(n) xs'" and 1: "P \<turnstile> xs' \<Rightarrow>r ys" by auto
  from deriver.cases[OF 1] obtain u A v w where "xs' = u @ Nt A # map Tm v" "(A,w) \<in> P" "ys = u @ w @ map Tm v"
    by metis
  with Suc.IH[OF n] assms(3) n
  show ?case by blast
qed


lemma derives_singleton_imp_completes:
  assumes "Prods G' \<turnstile> [Nt B] \<Rightarrow>* map Tm w"
  shows "([A \<rightarrow> \<alpha> . [Nt B]@\<beta>]#\<rho>@[init_symbol M], w@u) \<turnstile>* ([A \<rightarrow> \<alpha>@[Nt B] . \<beta>]#\<rho>@[init_symbol M], u)"
        (is "(?\<sigma>, _) \<turnstile>* _")
proof -
  from assms obtain \<gamma> where "Prods G' \<turnstile> [Nt B] \<Rightarrow> \<gamma>"
    "Prods G' \<turnstile> \<gamma> \<Rightarrow>* map Tm w" 
    by (metis converse_rtranclpE last_ConsL last_map list.map_disc_iff not_Cons_self2
        sym.distinct(1))
  from derive.cases this(1) have "(B, \<gamma>) \<in> Prods G'" using derive_singleton by blast
  show ?thesis sorry
qed

lemma derivels_empty_imp_no_Tms:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>l* []"
    "\<alpha> \<noteq> []"
  obtains X \<beta> where "\<alpha> = Nt X # \<beta>"
proof -
  from assms obtain \<beta> where "P \<turnstile> \<alpha> \<Rightarrow>l \<beta>" "P \<turnstile> \<beta> \<Rightarrow>l* []" 
    by (metis converse_rtranclpE)
  with derivel.cases obtain u X \<gamma> where "\<alpha> = map Tm u @ Nt X # \<gamma>" by meson
  moreover from this have "map Tm u = []" using assms 
    by (simp add: derivels_map_Tm_append)
  ultimately show thesis using that by blast
qed


lemma derives_empty_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>* []"
  shows "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>]#\<rho>@[init_symbol M], w) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>]#\<rho>@[init_symbol M], w)"
proof -
  from assms obtain n where "Prods G' \<turnstile> \<beta> \<Rightarrow>l(n) []" 
    using rtranclp_imp_relpowp by (metis derivels_iff_derives list.simps(8))
  then show ?thesis
  proof (induction n arbitrary: A \<alpha> \<beta> \<gamma> \<rho>)
    case (Suc n)
    then obtain \<beta>' where step: "Prods G' \<turnstile> \<beta> \<Rightarrow>l \<beta>'" "Prods G' \<turnstile> \<beta>' \<Rightarrow>l(n) []" 
      by (meson relpowp_Suc_D2)
    then obtain X \<delta> where \<beta>_decomp: "\<beta> = Nt X # \<delta>" 
      using derivels_empty_imp_no_Tms by (metis Suc.prems derivel_from_empty relpowp_imp_rtranclp)
    show ?case
    proof (cases \<beta>')
      case Nil
      with step have \<delta>_Nil: "\<delta> = []" unfolding \<beta>_decomp 
        by (simp add: derivel_Nt_Cons)
      with \<beta>_decomp have "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>]#\<rho>@[init_symbol M], w) 
        \<turnstile> ([X \<rightarrow> [] . []]#[A \<rightarrow> \<alpha> . Nt X#\<gamma>]#\<rho>@[init_symbol M], w)"
        using step Nil
        by (metis (no_types, lifting) append_Cons derivel_Nt_Cons expanding self_append_conv2)
      also have "... \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>]#\<rho>@[init_symbol M], w)"
        using \<beta>_decomp \<delta>_Nil by auto
      finally show ?thesis .
    next
      case (Cons a u)
      then show ?thesis sorry
    qed
  qed simp
qed


lemma derives_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w"
  shows "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>]#\<rho>@[init_symbol M], w@x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>]#\<rho>@[init_symbol M], x)"
using assms proof (induction "length w" arbitrary: A \<alpha> \<beta> \<gamma> \<rho> w x rule: less_induct)
  case less
  show ?case
  proof (cases w)
    case (Cons a as)
    with less(2) obtain \<delta> X \<zeta> u v y where \<beta>_decomp: "\<beta> = \<delta> @ [Nt X] @ \<zeta>" 
      "Prods G' \<turnstile> \<delta> \<Rightarrow>* map Tm u"
      "Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm v"
      "Prods G' \<turnstile> \<zeta> \<Rightarrow>* map Tm y"
      "w = u@v@y"
      "v \<noteq> []"
      sorry
    show ?thesis proof (cases "length v = length w")
      case True
      with \<beta>_decomp have eqs: "u = []" "v = w" "y = []" by auto 
      with \<beta>_decomp derives_empty_imp_completes have 
        "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>] # \<rho> @ [init_symbol M], w@x) 
          \<turnstile>* ([A \<rightarrow> \<alpha>@\<delta> . Nt X#\<zeta>@\<gamma>] # \<rho> @ [init_symbol M], w@x)"
        by force
      also from derives_singleton_imp_completes[OF \<beta>_decomp(3), unfolded eqs(2), of _ "\<alpha>@\<delta>"] have 
        "... \<turnstile>* ([A \<rightarrow> \<alpha>@\<delta>@[Nt X] . \<zeta>@\<gamma>] # \<rho> @ [init_symbol M], x)" 
        using append.assoc by simp
      also from \<beta>_decomp derives_empty_imp_completes[of _ _ "\<alpha>@\<delta>@[Nt X]"] eqs(3) have 
        "... \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)" by simp
      finally show ?thesis .
    next
      case False
      with \<beta>_decomp have ineqs: "length u < length w" "length v < length w" "length y < length w"
        by auto
      from less(1)[OF ineqs(1)] \<beta>_decomp have 
        "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>] # \<rho> @ [init_symbol M], w@x) 
           \<turnstile>* ([A \<rightarrow> \<alpha>@\<delta> . Nt X#\<zeta>@\<gamma>] # \<rho> @ [init_symbol M], v@y@x)"
        by simp
      also from less(1)[OF ineqs(2), of "[Nt X]" _ "\<alpha>@\<delta>" _ _] \<beta>_decomp have
        "... \<turnstile>* ([A \<rightarrow> \<alpha>@\<delta>@[Nt X] . \<zeta> @ \<gamma>] # \<rho> @ [init_symbol M], y@x)" by simp
      also from less(1)[OF ineqs(3), of \<zeta> _ "\<alpha>@\<delta>@[Nt X]"] \<beta>_decomp have 
        "... \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>] # \<rho> @ [init_symbol M], x)" by simp
      finally show ?thesis .
    qed
  qed (use less derives_empty_imp_completes in simp)
qed



definition Lang :: "'t list set" where
  "Lang \<equiv> {w. ([init_state M, init_symbol M], w) \<turnstile>* ([final_state, init_symbol M], [])}"


lemma hist_singleton_init [simp]:
  "hist ([[A \<rightarrow> \<alpha> . \<beta>], init_symbol M]) = \<alpha>"
  unfolding IPDA_def using hist_singleton by auto

lemma hist_init [simp]:
  "hist (\<rho>@[init_symbol M]) = hist \<rho>"
  using IPDA_def by (induction \<rho>) auto

lemma invariant: 
  assumes "([init_state M, init_symbol M], u@v) \<turnstile>* (\<rho>, v)"
  shows "Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u"
  sorry

corollary Lang_subst_Lang_G:
  "Lang \<subseteq> LangS G"
  unfolding Lang_def Context_Free_Grammar.Lang_def S_def 
  by (standard, metis invariant append.right_neutral hist_singleton_init mem_Collect_eq)
 


lemma Lang_eq_Lang_G:
  "Lang = LangS G"
  sorry


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
    by (rule ccontr) (use step step_equal_or_Cons in fastforce)
  moreover with step obtain r rs where 
    "ps = r#rs" "(r, rs) \<in> delta_eps M (init_state M) (init_symbol M)"
    using step_epsE by fastforce 
  ultimately show thesis using that by auto
qed

end

end
