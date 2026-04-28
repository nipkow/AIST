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

lemma list_app_last_is_next_hd:
  assumes "w = u@v@y"
    "w = xs@a#y"
    "v \<noteq> []"
  shows "last v = a"
  using assms 
  by (metis append.assoc append_Cons append_Nil append_same_eq last_append last_snoc)


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

lemma derives_decomp_less:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>(Suc n) map Tm w"
  obtains \<gamma>\<^sub>1 i u X j v \<gamma>\<^sub>2 k x where
    "\<alpha> = \<gamma>\<^sub>1 @ Nt X # \<gamma>\<^sub>2"
    "P \<turnstile> \<gamma>\<^sub>1 \<Rightarrow>(i) map Tm u" "P \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v" "P \<turnstile> \<gamma>\<^sub>2 \<Rightarrow>(k) map Tm x" "w = u @ v @ x"
    "i + j + k = Suc n" "j > 0"
proof -
  from assms obtain \<gamma>\<^sub>1 X \<gamma>\<^sub>2 where "\<alpha> = \<gamma>\<^sub>1 @ Nt X # \<gamma>\<^sub>2" 
    by (smt (verit, ccfv_SIG) deriven_Suc_iff)
  moreover with deriven_appendD[of _ _ \<gamma>\<^sub>1 "Nt X # \<gamma>\<^sub>2" "map Tm w"] assms obtain i u jk vx where
    "Suc n = i + jk" "P \<turnstile> \<gamma>\<^sub>1 \<Rightarrow>(i) map Tm u" "P \<turnstile> Nt X # \<gamma>\<^sub>2 \<Rightarrow>(jk) map Tm vx"
    "w = u @ vx" using deriven_append_map_Tm by blast
  moreover from this(3) deriven_appendD[of _ _ "[Nt X]" \<gamma>\<^sub>2 "map Tm vx"] obtain j k v x where
    "j + k = jk" "P \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v" "P \<turnstile> \<gamma>\<^sub>2 \<Rightarrow>(k) map Tm x" 
    "vx = v @ x"
    by (metis (no_types, lifting) append_Cons append_Nil deriven_append_map_Tm)
  ultimately show thesis using that by fastforce
qed

(* If needed can be trivially extended to obtain m where 
    n = Suc m and P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w still holds *)
lemma derivern_singleton_imp_prod:
  assumes "P \<turnstile> [Nt X] \<Rightarrow>(n) map Tm w"
  obtains \<alpha> m where "P \<turnstile> [Nt X] \<Rightarrow> \<alpha>"
    "P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w" "m < n"
  using assms by (cases n) (force, metis lessI relpowp_Suc_D2)


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
        with decomp have "i = 0" "k = 0" "\<delta>\<^sub>1 = map Tm u" "\<delta>\<^sub>2 = map Tm y"
        proof -
          from decomp show "i = 0" "k = 0" using True by auto
          thus "\<delta>\<^sub>1 = map Tm u" "\<delta>\<^sub>2 = map Tm y" using decomp by auto
        qed   
        from True decomp(6,7) Suc obtain \<beta>' where m_steps:
          "Prods G' \<turnstile> [Nt X] \<Rightarrow> \<beta>'" "Prods G' \<turnstile> \<beta>' \<Rightarrow>(m) map Tm v"
          using decomp(3) by (meson relpowp_Suc_D2)
        show ?thesis 
        proof (cases m)
          case 0
          note first
          also from m_steps[unfolded 0] have 
            "(?\<sigma>, v @ y @ x) \<turnstile> ([X \<rightarrow> [] . map Tm v] # ?\<sigma>, v @ y @ x)" 
            using expanding by (simp add: derive_singleton)
          also from completes_Tms[of _ "[]" v "[]" _ "y@x"] have 
            "... \<turnstile>* ([X \<rightarrow> map Tm v . []] # ?\<sigma>, y @ x)" 
            by (metis append.right_neutral append_Nil completes_Tms_Cons)
          also have "... \<turnstile> ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] . \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], y @ x)"
            using reducing[of X _ _ "\<alpha> @ \<delta>\<^sub>1" "\<delta>\<^sub>2 @ \<gamma>"] by simp
          also note last
          finally show ?thesis .
        next
          case (Suc m')
          from derives_decomp_less[OF m_steps(2)[unfolded Suc]] obtain \<xi>\<^sub>1 i' u' Y j' v' \<xi>\<^sub>2 k' y' 
            where \<beta>'_decomp:
            "\<beta>' = \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2" "Prods G' \<turnstile> \<xi>\<^sub>1 \<Rightarrow>(i') map Tm u'" "Prods G' \<turnstile> [Nt Y] \<Rightarrow>(j') map Tm v'"
            "Prods G' \<turnstile> \<xi>\<^sub>2 \<Rightarrow>(k') map Tm y'" "v = u' @ v' @ y'" "i' + j' + k' = Suc m'" "j' > 0"
            by metis
          hence X_leqs: "i' < n" "j' < n" "k' < n"
            using Suc Suc_m by auto
          from derivern_singleton_imp_prod[OF \<beta>'_decomp(3)] obtain \<gamma>' j'' where Y_prod: 
            "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<gamma>'" "Prods G' \<turnstile> \<gamma>' \<Rightarrow>(j'') map Tm v'"
            "j'' < n"
            using X_leqs(2) by (metis order_less_trans)
          note first
          also from m_steps \<beta>'_decomp(1) have 
            "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 . Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x) 
              \<turnstile> ([X \<rightarrow> [] . \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v @ y @ x)"
            using expanding by (simp add: derive_singleton)
          also from less(1)[OF X_leqs(1) \<beta>'_decomp(2), of X "[]" "Nt Y # \<xi>\<^sub>2" _ "v' @ y' @ y @ x"] 
          have "... \<turnstile>* ([X \<rightarrow> \<xi>\<^sub>1 . Nt Y # \<xi>\<^sub>2] # ?\<sigma>, v' @ y' @ y @ x)" 
               (is "_ \<turnstile>* (?\<tau>, _)")
            by (metis \<beta>'_decomp(5) append.assoc append_Cons append_Nil)
          also from Y_prod have "... \<turnstile> ([Y \<rightarrow> [] . \<gamma>'] # ?\<tau>, v' @ y' @ y @ x)" 
            using expanding by (simp add: derive_singleton)
          also from less(1)[OF Y_prod(3,2), of Y "[]" "[]" _ "y' @ y @ x"]
          have "... \<turnstile>* ([Y \<rightarrow> \<gamma>' . []] # ?\<tau>, y' @ y @ x)" 
            by (smt (verit, best) Cons_eq_appendI append.right_neutral self_append_conv2)
          also have "... \<turnstile> ([X \<rightarrow> \<xi>\<^sub>1 @ [Nt Y] . \<xi>\<^sub>2] # ?\<sigma>, y' @ y @ x)"
            using reducing by presburger
          also from less(1)[OF X_leqs(3) \<beta>'_decomp(4), of X "\<xi>\<^sub>1 @ [Nt Y]" "[]" _ "y @ x"] have
            "... \<turnstile>* ([X \<rightarrow> \<beta>' . []] # ?\<sigma>, y @ x)"
            using \<beta>'_decomp(1) append.assoc by (metis append.right_neutral append_Cons append_Nil)
          also have "... \<turnstile> ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] . \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], y @ x)"
            using reducing[of X _ _ "\<alpha> @ \<delta>\<^sub>1"] by simp
          also note last
          finally show ?thesis by presburger
        qed
      next
        case False
        hence "j < n" using decomp by linarith
        with derivern_singleton_imp_prod[OF decomp(3)] obtain \<xi> j' where X_prod:
          "Prods G' \<turnstile> [Nt X] \<Rightarrow> \<xi>" "Prods G' \<turnstile> \<xi> \<Rightarrow>(j') map Tm v"
          "j' < n" 
          by (metis add_lessD1 less_imp_add_positive)
        note first
        also from X_prod have "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 . Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], v @ y @ x) 
                            \<turnstile> ([X \<rightarrow> [] . \<xi>] # ?\<sigma>, v @ y @ x)"
          using expanding by (simp add: derive_singleton)
        also from less(1)[OF X_prod(3,2), of X "[]" "[]" _ "y @ x"] have 
          "... \<turnstile>* ([X \<rightarrow> \<xi> . []] # ?\<sigma>, y @ x)" 
          by (metis append.right_neutral append_Cons append_Nil)
        also have "... \<turnstile> ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] . \<delta>\<^sub>2 @ \<gamma>] # \<rho> @ [init_symbol M], y @ x)"
          using reducing[of X _ _ "\<alpha> @ \<delta>\<^sub>1"] by simp
        also note last
        finally show ?thesis .
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
