theory LR_Parser 
  imports 
    Extended_Cfg
begin

context Extended_Cfg
begin

section \<open>IPDA, char(G) and \<open>LR\<^sub>0(G)\<close>\<close>

definition IPDA :: "(('n, 't) item, 't, ('n, 't) item) pda" where
  "IPDA \<equiv> let
    P = Prods G';
    Q = It G'; 
    \<delta> = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {});
    \<E> = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> . Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> P} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})         
in
  \<lparr>pda.init_state = [S' \<rightarrow> [] . [Nt S]], pda.init_symbol = [S' \<rightarrow> [] . []], 
    pda.final_states = {[S' \<rightarrow> [Nt S] . []]}, pda.delta = \<delta>, pda.delta_eps = \<E>\<rparr>"


definition history :: "('n, 't) item \<Rightarrow> ('n, 't) syms" where
  "history i \<equiv> case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> \<alpha>"

definition hist :: "('n, 't) item list \<Rightarrow> ('n,'t) syms" where
  "hist \<rho> \<equiv> concat (map history \<rho>)"

definition rev_hist :: "('n, 't) item list \<Rightarrow> ('n,'t) syms" where
  "rev_hist \<rho> \<equiv> concat (map history (rev \<rho>))"

lemma rev_hist_Cons[simp]:
  "rev_hist (i#\<rho>) = rev_hist \<rho> @ history i"
  unfolding rev_hist_def by simp

lemmas hist_defs = hist_def rev_hist_def history_def

definition char_fa :: "(('n, 't) sym, ('n, 't) item) nfa" where
  "char_fa \<equiv> let 
      P = Prods G';
      Q = It G';
      F = {[X \<rightarrow> \<alpha> . []] |X \<alpha>. [X \<rightarrow> \<alpha> . []] \<in> It G'};
      \<delta> = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> if a = Y \<and> (X, \<alpha>@Y#\<beta>) \<in> P then {[X \<rightarrow> \<alpha>@[Y] . \<beta>]} else {}| 
         _ \<Rightarrow> {}); 
      \<E> = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @Nt Y#\<beta>) \<in> P \<and> (Y, \<gamma>) \<in> P} in
    \<lparr>nfa.states = Q, nfa.init = {[S' \<rightarrow> [] . [Nt S]]}, nfa.final = F, nfa.nxt = \<delta>, nfa.eps = \<E>\<rparr>"

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
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> if a = Y \<and> ((X, \<alpha> @ (Y#\<beta>)) \<in> Prods G') then {[X \<rightarrow> \<alpha> @ [Y] . \<beta>]} else {}| 
        _ \<Rightarrow> {})"
  unfolding char_fa_def by (meson nfa.select_convs(4))

lemma eps_char_fa [simp]:
  "nfa.eps char_fa 
    = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G' \<and> (Y, \<gamma>) \<in> Prods G'}"
  unfolding char_fa_def by (meson nfa.select_convs(5))

definition LR\<^sub>0 :: "(('n, 't) sym, ('n, 't) item set) dfa" where
  "LR\<^sub>0 \<equiv> nfa.Power_dfa char_fa"



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
      using eq nxt_closed q_def by cases (auto simp: items_of_Prods_def)
  qed (use nxt_closed q_def in fastforce)+
qed (use G'_def items_of_Prods_def It_finite[OF G'_finite] in fastforce)+
thm nfa.dfa_Power

sublocale canon_LR0: dfa LR\<^sub>0
  unfolding LR\<^sub>0_def by (rule char_fa.dfa_Power)

end

section \<open>IPDAs\<close>

locale IPDA =
  fixes G G' :: "('n::fresh0, 't) Cfg"
      and S S' :: 'n  
  assumes extended: "Extended_Cfg G"
  defines "S \<equiv> Start G"
      and "S' \<equiv> fresh0 (Nts (Prods G) \<union> {S})"
      and "G' \<equiv> Cfg (Prods G \<union> {(S', [Nt S])}) S'"
begin

type_synonym ('q,'s) config = "'q list \<times> 's list"

abbreviation "P \<equiv> Extended_Cfg.IPDA G"

lemmas P_def = Extended_Cfg.IPDA_def[OF extended]

lemma init_state_def: "init_state P = [S' \<rightarrow> [] . [Nt S]]"
  unfolding P_def S'_def S_def by auto

lemma init_symbol_def: "init_symbol P = [S' \<rightarrow> [] . []]"
  unfolding P_def S'_def S_def by auto

lemmas init_defs = init_state_def init_symbol_def

lemma delta_eps_init_is_S:
  "delta_eps P (init_state P) (init_symbol P) = {([S \<rightarrow> [] . \<alpha>], [init_state P, init_symbol P]) |\<alpha>. (S,\<alpha>) \<in> Prods G'}"
proof -
  let ?\<delta> = "(\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta> .Nt Y#\<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> Prods G'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {} | _ \<Rightarrow> {})"
  have delta: "?\<delta> = delta_eps P"
    unfolding P_def
    by (metis (lifting) ext G'_def S'_def S_def pda.select_convs(5))
  then show ?thesis unfolding init_state_def
    by (smt (verit, best) Collect_cong case_prod_conv item.case list.simps(5) sym.simps(5))
qed


lemma delta_init_empty:
  "delta P (init_state P) a (init_symbol P) = {}"
proof -
  let ?\<delta> = "(\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {} | _ \<Rightarrow> {})"
  have delta: "?\<delta> = delta P"  unfolding P_def by simp
  from init_state_def have "?\<delta> (init_state P) a (init_symbol P) = {}" 
    by auto
  with ext delta show ?thesis  by (metis (lifting))
qed

inductive step :: "(('n,'t) item,'t) config \<Rightarrow> (('n,'t) item,'t) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 70) where
delta[intro]: "\<lbrakk>\<alpha> = [p0, p1]; \<alpha>' = q#qs; (q,qs) \<in> delta P p0 a p1\<rbrakk> 
                \<Longrightarrow> (\<alpha>@\<beta>,a#w) \<turnstile> (\<alpha>'@\<beta>,w)" |
eps[intro]: "\<lbrakk>\<alpha> = [p0, p1]; \<alpha>' = q#qs; (q,qs) \<in> delta_eps P p0 p1\<rbrakk> 
                \<Longrightarrow> (\<alpha>@\<beta>, w) \<turnstile> (\<alpha>'@\<beta>, w)"

inductive_cases step_deltaE[elim]: "(s, x#w) \<turnstile> (s', w)"
inductive_cases step_epsE[elim]: "(s, w) \<turnstile> (s', w)"

lemma step_equal_or_cons:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_cons[OF assms] by fastforce

lemma shifting[simp]:
  "([A \<rightarrow> \<alpha> . Tm a # \<beta>]#\<rho>#\<rho>s, a#u) \<turnstile> ([A \<rightarrow> \<alpha>@[Tm a] . \<beta>]#\<rho>#\<rho>s, u)"
proof -
  have "([A \<rightarrow> \<alpha>@[Tm a] . \<beta>], [\<rho>]) \<in> delta P ([A \<rightarrow> \<alpha> . Tm a # \<beta>]) a \<rho>"
    using P_def by simp
  then show ?thesis using delta by fastforce
qed

lemma reducing[simp]:
  "([Y \<rightarrow> \<alpha> . []]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>]#\<rho>, w)"
proof -
  have "([X \<rightarrow> \<beta> @ [Nt Y] . \<gamma>], []) \<in> delta_eps P ([Y \<rightarrow> \<alpha> . []]) ([X \<rightarrow> \<beta> . Nt Y#\<gamma>])"
    unfolding P_def by simp
  thus ?thesis using eps by fastforce
qed

lemma expanding_in_delta_eps:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([Y \<rightarrow> [] . \<alpha>], [[X \<rightarrow> \<beta> . Nt Y#\<gamma>], i]) \<in> delta_eps P ([X \<rightarrow> \<beta> . Nt Y#\<gamma>]) i"
  using assms unfolding G'_def S'_def S_def P_def  by auto

lemma expanding[simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] . \<alpha>]#[X \<rightarrow> \<beta> . Nt Y#\<gamma>]#i#\<rho>, w)"
  using expanding_in_delta_eps[OF assms] eps by fastforce


abbreviation steps (infix \<open>\<turnstile>*\<close> 70) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

abbreviation stepn ( \<open>_ \<turnstile>'(_') _\<close> 70) where
  "stepn c0 n c1 \<equiv> (step ^^ n) c0 c1"

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by ((induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct),
  (use step_len_dec surj_pair le_trans in fastforce)+)


lemma syms_complete:
  "([A \<rightarrow> \<alpha> . map Tm u @ \<beta>]#i#is, u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u . \<beta>]#i#is, v)"
proof (induction u arbitrary: \<alpha>)
  case (Cons a u)
  have "([A \<rightarrow> \<alpha> . map Tm (a # u) @ \<beta>] # i # is, (a # u) @ v) \<turnstile> ([A \<rightarrow> \<alpha> @ [Tm a] . map Tm u @ \<beta>] # i # is, u @ v)"
    by simp
  then show ?case using Cons[of "\<alpha>@[Tm a]"] 
    by (metis (no_types, lifting) append_Cons append_assoc 
        converse_rtranclp_into_rtranclp eq_Nil_appendI list.simps(9))
qed simp



lemma steps_substring:
  assumes "(\<rho>0, w) \<turnstile>* (\<rho>2, v)"
  obtains u where "w = u@v"
  sorry

lemma reachable_impl_reachable_substring:
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
          then obtain cs where cs_def: "w = cs @ [a]" using less(3) as
          proof -
            obtain c where c_def: "c = last w" by presburger
            with Cons less(3) as have "c = a" 
            proof -
              have f1: "c = last (v @ b # bs)"
                by (simp add: \<open>c = last w\<close> local.Cons)
              obtain tts :: "'t list" where
                "u = tts @ a # y"
                using \<open>\<And>thesis. (\<And>as. u = as @ a # y \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
              then show ?thesis
                using f1 less(3) local.Cons by auto
            qed
            thus thesis using that unfolding c_def 
              by (metis append_butlast_last_id list.distinct(1) local.Cons)
          qed
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


lemma syms_tl_impl_substring:
  assumes "([A \<rightarrow> \<alpha> . \<beta> @ map Tm u]#\<rho>, v) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta>@map Tm u . []]#\<rho>', w)"
  obtains v' where "v = v'@u"
  sorry

lemma reaches_final_impl_reaches_complete:
  assumes "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>, v) \<turnstile>* ([[S' \<rightarrow> [Nt S] . []], init_symbol P], [])"
  obtains w where "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>, v) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> . []]#\<rho>', w)"
  sorry

corollary reaches_final_impl_substring:
  assumes "([A \<rightarrow> \<alpha> . \<beta> @ map Tm u]#\<rho>, v) \<turnstile>* ([[S' \<rightarrow> [Nt S] . []], init_symbol P], [])"
  obtains v' where "v = v'@u"
  using reaches_final_impl_reaches_complete[OF assms, THEN syms_tl_impl_substring]
  by metis

lemma reaches_final_impl_interm_reaches_final:
  assumes "c0 \<turnstile>* ([[S' \<rightarrow> [Nt S] . []], init_symbol P], [])"
    "c0 \<turnstile>* c1"
  shows "c1 \<turnstile>* ([[S' \<rightarrow> [Nt S] . []], init_symbol P], [])"
  sorry





definition Lang :: "'t list set" where
  "Lang \<equiv> {w. ([init_state P, init_symbol P], w)
             \<turnstile>* ([[S' \<rightarrow> [Nt S] . []], init_symbol P], [])}"

lemma Lang_eq_Lang_G:
  "Lang = LangS G"
  sorry


lemma first_step_is_eps:
  assumes "([init_state P, init_symbol P], u) \<turnstile>* (qs, v)"
    "([init_state P, init_symbol P], u) \<noteq> (qs, v)"
  obtains \<alpha> where 
    "([init_state P, init_symbol P], u) \<turnstile> ([[S \<rightarrow> [] . \<alpha>], init_state P, init_symbol P], u)"
    "([[S \<rightarrow> [] . \<alpha>], init_state P, init_symbol P], u) \<turnstile>* (qs, v)"
proof -
  from assms obtain ps u' where step: "([init_state P, init_symbol P], u) \<turnstile> (ps, u')"
    and steps: "(ps, u') \<turnstile>* (qs, v)"
    by (metis converse_rtranclpE2)
  have eps: "u = u'" 
  proof (rule ccontr)
    assume neq: "u \<noteq> u'"
    with step obtain a r rs where "([init_state P, init_symbol P], a#u') \<turnstile> (r#rs, u')"
      "(r, rs) \<in> delta P (init_state P) a (init_symbol P)" 
      by (smt (verit, best) list.inject self_append_conv step_deltaE step_equal_or_cons)
    then show False using delta_init_empty by simp
  qed
  with step obtain r rs where rrs_def: "ps = r#rs" "(r, rs) \<in> delta_eps P (init_state P) (init_symbol P)"
    using step_epsE[of "[init_state P, init_symbol P]" u ps] by fastforce 
  then show thesis using delta_eps_init_is_S that rrs_def step steps eps by auto
qed
  

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

lemma step_equal_or_cons:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_cons[OF assms] by fastforce

abbreviation stepn  (\<open>_ \<turnstile>'(_') _\<close> 70) where
  "c0 \<turnstile>(n) c1 \<equiv> (step ^^ n) c0 c1"

abbreviation steps (infix \<open>\<turnstile>*\<close> 70) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by ((induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct),
  (use step_len_dec surj_pair le_trans in fastforce)+)

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


lemma steps_impl_eps_stepn:
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

lemma eps_stepn_impl_steps: "c0 \<turnstile>\<epsilon>(n) c1 \<Longrightarrow> c0 \<turnstile>* c1" 
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
    with steps_len_dec eps_stepn_impl_steps have  "length u \<ge> length (a#w)" by blast
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

lemma ipda: "LR_Parser.IPDA G"
  by standard


notation char_fa.step (infix \<open>\<turnstile>c\<close> 70)
notation char_fa.steps (infix \<open>\<turnstile>c*\<close> 70)
notation char_fa.eps_stepn (\<open>_ \<turnstile>\<epsilon>'(_') _\<close> 70)

abbreviation IPDA_step :: "('n, 't) item list \<times> 't list \<Rightarrow> ('n, 't) item list \<times> 't list \<Rightarrow> bool"
  (infix \<open>\<turnstile>P\<close> 70) where "IPDA_step \<equiv> IPDA.step G" 
abbreviation IPDA_steps :: "('n, 't) item list \<times> 't list \<Rightarrow> ('n, 't) item list \<times> 't list \<Rightarrow> bool"
  (infix \<open>\<turnstile>P*\<close> 70) where "IPDA_steps \<equiv> IPDA.steps G"





(*lemma char_init_step_is_eps:
  assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c ([A \<rightarrow> \<alpha> . \<beta>], \<gamma>')" (is "(?S,_) \<turnstile>c _")
  shows "A = S \<and> \<gamma> = \<gamma>'"
  using assms proof cases
  case (nxt a)
  from assms have "(S', [Nt S]) \<notin> Prods G"
    unfolding S_defs sorry
  hence "nfa.nxt char_fa ?S a = {}" sorry
  then show ?thesis using nxt oops
 


lemma char_init_noeps_eq:
  assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>\<epsilon>(0) ([A \<rightarrow> \<alpha> . \<beta>], \<gamma>')"
  shows "([S' \<rightarrow> [] . [Nt S]], \<gamma>) = ([A \<rightarrow> \<alpha> . \<beta>], \<gamma>')"
  using assms proof cases
  case (nxt q a)
  moreover obtain u :: "('n,'t) syms" where u_def: "u = a # \<gamma>'"  by blast
  ultimately have "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>\<epsilon>(0) (q,u)" "(q,u) \<turnstile>c ([A \<rightarrow> \<alpha> . \<beta>], \<gamma>')" by simp+
  with u_def show ?thesis
  proof (induction "length \<gamma> - length u" arbitrary: q u a \<gamma>' A \<alpha> \<beta> rule: less_induct)
    case less
    from less(3) show ?case 
    proof cases
      case refl
      then show ?thesis using char_init_step_is_eps less(2)
        using S'_def S_def less.prems(3) sorry
    next
      case (nxt p a)
      from char_fa.eps_stepn_impl_steps[OF nxt(1)] char_fa.steps_len_dec have "length (a#u) \<le> length \<gamma>"
        by presburger
      hence "length \<gamma> - length (a#u) < length \<gamma> - length u" by simp
      then show ?thesis 
        by (metis \<open>([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* (p, a # u)\<close> char_fa.steps_len_dec impossible_Cons 
            item.exhaust less.hyps nxt(1,2))   
    qed
  qed
qed presburger

lemma char_fa_comp_impl_deriver:
    assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
    obtains w \<gamma>' where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>'@Nt A#w" "Prods G' \<turnstile> \<gamma>'@Nt A#w \<Rightarrow>r \<gamma>'@\<alpha>@\<beta>@w" "\<gamma> = \<gamma>'@\<alpha>"
proof -
  from assms obtain n where "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>\<epsilon>(n) ([A \<rightarrow> \<alpha> . \<beta>], [])"
    using char_fa.steps_impl_eps_stepn by blast
  with that show ?thesis
  proof (induction n arbitrary: A \<alpha> \<beta>)
    case 0
    with char_init_noeps_eq assms have eq: "([S' \<rightarrow> [] . [Nt S]], \<gamma>) = ([A \<rightarrow> \<alpha> . \<beta>], [])" 
      by auto
    then show ?case using G'_def S_defs deriver_singleton 0(1) by fastforce 
  next
    case (Suc n)
    with char_fa.last_eps_step obtain X \<alpha>' \<beta>' where
      "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>\<epsilon>(n) ([X \<rightarrow> \<alpha>' . Nt A#\<beta>'], \<alpha>)" 
      "([X \<rightarrow> \<alpha>' . Nt A#\<beta>'], \<alpha>) \<turnstile>c ([A \<rightarrow> [] . \<alpha> @ \<beta>], \<alpha>)"
      "([A \<rightarrow> [] . \<alpha> @ \<beta>], \<alpha>) \<turnstile>\<epsilon>(0) ([A \<rightarrow> \<alpha> . \<beta>], [])"
      sorry
    then show ?case sorry
  qed
qed 

lemma deriver_decomp:
  assumes "P \<turnstile> A \<Rightarrow>r* \<gamma>@Nt B#map Tm w"
  obtains X :: "'n list"
    and \<alpha> \<beta> :: "('n,'t) syms list"
    and v :: "'t list list"
    and n :: nat
  where "Suc n = length X" "length X = length \<alpha>" "length \<alpha> = length \<beta>" "length \<beta> = length v" 
    "X!n = B" "P \<turnstile> A \<Rightarrow>r \<alpha>!0 @ Nt (X!0) # \<beta>!0"
    "\<forall>i<n. let Xi = X!i; Xsi = X!(Suc i); \<alpha>si = \<alpha>!(Suc i); \<beta>si = \<beta>!(Suc i); vi = v!i in 
            (Xi, \<alpha>si@Nt Xsi#\<beta>si) \<in> P \<and> P \<turnstile> \<beta>si \<Rightarrow>r* map Tm vi"
    "w = rev (concat v)" "\<gamma> = concat \<alpha>"
  oops

lemma deriver_decomp_reachable:
  assumes "P \<turnstile> A \<Rightarrow>r* \<gamma>@Nt B#map Tm w"
          "i < Suc n"
    and decomp: "Suc n = length X" "length X = length \<alpha>" "length \<alpha> = length \<beta>" "length \<beta> = length v" 
    "X!n = B" "P \<turnstile> A \<Rightarrow>r \<alpha>!0 @ Nt (X!0) # \<beta>!0"
    "\<forall>i<n. let Xi = X!i; Xsi = X!(Suc i); \<alpha>si = \<alpha>!(Suc i); \<beta>si = \<beta>!(Suc i); vi = v!i in 
            (Xi, \<alpha>si@Nt Xsi#\<beta>si) \<in> P \<and> P \<turnstile> \<beta>si \<Rightarrow>r* map Tm vi"
    "w = rev (concat v)" "\<gamma> = concat \<alpha>"
  shows "P \<turnstile> A \<Rightarrow>r* take i (concat \<alpha>) @ Nt (X!i) # rev (take i (map Tm (concat v)))"
  sorry *)



(* mv? *)
lemma index_gt_left_impl_right:
  assumes "length xs < m" "m < length (xs@y#ys)"
        shows "(xs@y#ys)!m \<in> set ys"
proof -
  have "(xs@y#ys)!m = (y#ys)!(m-length xs)" 
    using assms(1) by (meson le_eq_less_or_eq nth_append_right)
  also have "... = ys!(m-length xs-1)" 
    using assms(1) by simp
  finally show ?thesis 
    by (metis One_nat_def Suc_pred add_diff_inverse_nat add_less_cancel_left assms length_Cons
        length_append less_Suc_eq not_less_eq nth_mem zero_less_diff)
qed

  
  

lemma deriver_impl_in_Prods:
  assumes "P \<turnstile> \<beta> @ Nt A # map Tm u \<Rightarrow>r \<gamma> @ Nt X # map Tm v"
  obtains \<alpha> where "\<beta> @ \<alpha> @ map Tm u = \<gamma> @ Nt X # map Tm v"
    "(A, \<alpha>) \<in> P" 
proof -
  from deriver.cases[OF assms] obtain A' \<alpha>' \<beta>' u' where
    deriv: "\<beta> @ Nt A # map Tm u = \<beta>' @ Nt A' # map Tm u'" (is "?w = ?w'")
    "\<gamma> @ Nt X # map Tm v = \<beta>' @ \<alpha>' @ map Tm u'"
    "(A', \<alpha>') \<in> P" by metis
  moreover have "\<beta> = \<beta>'" "A = A'" "u = u'" 
  proof -
    have "map Tm u = map Tm u'"
    proof (rule ccontr)
      assume neq: "map Tm u \<noteq> map Tm u'"
      then show False
      proof (cases "length u = length u'")
        case False
        note u_neq = False
        let ?n = "length \<beta>"
        let ?m = "length \<beta>'"
        have inds: "?w!?n = Nt A" "?w'!?m = Nt A'" by auto 
        show ?thesis
        proof (cases "?n < ?m")
          case True
          obtain a where "?w!?m = Tm a" 
            using deriv(1) index_gt_left_impl_right[of \<beta> ?m "Nt A" "map Tm u", OF True] by auto
          then show False using inds(2) deriv(1) by simp
        next
          case False
          with deriv(1) u_neq have lt: "?m < ?n"
            by (metis append_eq_append_conv list.inject map_Tm_inject_iff nat_neq_iff)
          obtain a where "?w'!?n = Tm a"
            using deriv(1) index_gt_left_impl_right[of \<beta>' ?n "Nt A'" "map Tm u'", OF lt]
            by (metis add_Suc_right ex_map_conv length_Cons length_append less_add_Suc1)
          then show False using inds(1) deriv(1) by simp
        qed
      qed (use deriv(1) neq in auto)
    qed
    then show "\<beta> = \<beta>'" "A = A'" "u = u'" using deriv(1) by auto
  qed
  ultimately show thesis using that by presburger
qed

lemma eq_tl_impl_substring:
  assumes "length u \<ge> length v"
  "xs @ u = ys @ v"
obtains w where "w @ v = u"
  using assms 
  by (smt (verit, best) append_eq_append_conv append_eq_append_conv2 dual_order.eq_iff le_add2
      length_append)

(*Does not hold in general*)
lemma deriver_decomp:
  assumes "P \<turnstile> \<alpha> @ Nt X # map Tm u \<Rightarrow>r \<gamma> @ Nt A # map Tm w"
  obtains \<beta> v where "(X, \<beta>@Nt A#map Tm v) \<in> P" "\<gamma> = \<alpha>@\<beta>" 
      "map Tm (v@u) = map Tm w"
  sorry
(*proof -
  obtain xs where xs_def: "\<gamma> @ Nt A # map Tm w = \<alpha> @ xs @ map Tm u" "(X, xs) \<in> P" 
    using deriver_impl_in_Prods[OF assms] by metis
  moreover have "length w \<ge> length u" using assms sorry
  ultimately obtain zs :: "('a,'b) syms" where zs_def: "zs @ map Tm u = map Tm w" 
    using eq_tl_impl_substring[of "map Tm u" "map Tm w"] 
    by (metis append.assoc append_Cons append_Nil length_map)
  then obtain ys where "xs = ys@zs" "\<gamma>''@ys = \<gamma>'@[Nt A]"
  proof -
    note xs_def(1)[symmetric]
    also have "\<gamma>' @ Nt A # map Tm w = \<gamma>' @ Nt A # zs @ map Tm u" using zs_def by presburger
    also with xs_def obtain ys where "\<gamma>' @ Nt A # zs @ map Tm u = \<gamma>'' @ ys @ zs @ map Tm u"
      sorry
    finally show thesis using that  \<open>\<gamma>' @ Nt A # zs @ map Tm u = \<gamma>'' @ ys @ zs @ map Tm u\<close> 
      by force
  qed
  then show thesis using that sorry
qed *)

definition toitems :: "'n list \<Rightarrow> ('n,'t) syms list \<Rightarrow> ('n,'t) syms list \<Rightarrow> ('n,'t) item list" where
  "toitems X \<alpha> \<beta> \<equiv> (let \<alpha>\<beta> = zip (tl \<alpha>) (tl \<beta>); Xs = zip X (tl X) in 
    map2 (\<lambda>(Xi, Xsi) (\<alpha>si,\<beta>si). [Xi \<rightarrow> \<alpha>si . Nt Xsi # \<beta>si]) Xs \<alpha>\<beta>)"



lemma derives_impl_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm u"
  shows "([A \<rightarrow> \<alpha> . \<beta>@\<gamma>]#\<rho>, u@v) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . \<gamma>]#\<rho>, v)"
  sorry

lemma deriver_impl_IPDA_comp:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>'@Nt A#map Tm w"
    "Prods G' \<turnstile> \<gamma>'@Nt A#map Tm w \<Rightarrow>r \<gamma>'@\<alpha>@\<beta>@map Tm w"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  obtains \<rho> where "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>@[init_symbol IPDA], v@w) 
                    \<turnstile>P* ([[S' \<rightarrow> [Nt S] . []], init_symbol IPDA], [])"
          "rev_hist \<rho> = \<gamma>'" 
proof -
  let ?q0 = "[init_state IPDA, init_symbol IPDA]"
  let ?qf = "[[S' \<rightarrow> [Nt S] . []], init_symbol IPDA]"
  from assms obtain n where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(n) \<gamma>'@Nt A#map Tm w" 
    using rtranclp_power by meson
  with assms(2,3) that show thesis
  proof (induction n arbitrary: \<gamma>' A v w \<alpha> \<beta> thesis)
    case 0 
    then have A_is_S: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r \<gamma>' @\<alpha>@\<beta>@map Tm w" "(S', \<alpha>@\<beta>) \<in> Prods G'" "A = S'"
      by (simp add: Cons_eq_append_conv deriver_singleton)+
     from this have eq_S: "\<alpha>@\<beta> = [Nt S]" "\<gamma>' = [] \<and> w = []"
       using S'_derive_impl_S derive_singleton "0.prems"(4) Cons_eq_append_conv by (blast, fastforce)
    hence "rev_hist [] = \<gamma>'" unfolding hist_defs by simp
    from eq_S consider (left) "\<alpha> = [Nt S] \<and> \<beta> = []" | (right) "\<alpha> = [] \<and> \<beta> = [Nt S]"
      using append_eq_Cons_conv by fastforce
    then show ?case
    proof cases
      case left
      then show ?thesis using 0 
        by (metis A_is_S(3) \<open>rev_hist [] = \<gamma>'\<close> derivers_imp_derives derives_from_empty eq_S(2) 
            list.map_disc_iff rtranclp.rtrancl_refl self_append_conv2)
    next
      case right
      with 0(2) have "Prods G' \<turnstile> [Nt S] \<Rightarrow>r* map Tm v" by argo
      hence v_in_G: "v \<in> LangS G" 
        using G'_derives_impl_G_derives_if_no_S' S_neq_S' 
        unfolding Lang_def by (simp add: derivers_imp_derives eq_S(2))
      have ipda: "LR_Parser.IPDA G" by (metis Extended_Cfg_axioms IPDA.intro)
      from v_in_G IPDA.Lang_eq_Lang_G[OF ipda] have "(?q0, v) \<turnstile>P* (?qf, [])"
        unfolding IPDA.Lang_def[OF ipda] by auto
      then show ?thesis using 0(3) A_is_S 
        by (metis (no_types, lifting) \<open>rev_hist [] = \<gamma>'\<close> append.right_neutral append_Nil eq_S(2) 
            local.IPDA_def pda.select_convs(1) right)
    qed
  next
    case (Suc n)
    from Suc(5) obtain X \<gamma>'' u where n_steps: "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(n) \<gamma>'' @ Nt X # map Tm u"
      "Prods G' \<turnstile> \<gamma>'' @ Nt X # map Tm u \<Rightarrow>r \<gamma>' @ Nt A # map Tm w"
      by (metis (no_types, lifting) deriver.cases relpowp_Suc_E)

    (* Does not hold in general. Strong induction needed instead *)
    obtain \<gamma>''' u' where X_prod: "(X, \<gamma>'''@Nt A#map Tm u') \<in> Prods G'" "\<gamma>' = \<gamma>''@\<gamma>'''" 
      "map Tm (u'@u) = map Tm w"
      using deriver_decomp[OF n_steps(2)] by blast
    from reduced_derived_substring_impl_derives[of G' \<gamma>' "[Nt A]", OF _ G'_reduced G'_not_empty] 
    Suc.prems(4) obtain v' where A_derives: "Prods G' \<turnstile> [Nt A] \<Rightarrow>r* map Tm v'"
    by (metis (no_types, opaque_lifting) Cfg.sel(2) G'_def append_Cons append_self_conv2
           derivern_imp_deriven derivers_iff_derives rtranclp_power)
    hence A_Cons_derivers: "Prods G' \<turnstile> Nt A#map Tm u' \<Rightarrow>r* map Tm (v'@u')" 
      using derives_append derivers_iff_derives 
      by (metis append_Cons append_Nil map_append)
    from Suc(1)[OF _ this _ n_steps(1)] obtain \<rho> where \<rho>_def:
      "([X \<rightarrow> \<gamma>''' . Nt A#map Tm u'] # \<rho> @ [init_symbol IPDA], v' @ u' @ u) \<turnstile>P* (?qf, [])"
      "rev_hist \<rho> = \<gamma>''"
      using n_steps(2) X_prod(2,3) append_assoc 
      by (metis append_Cons map_Tm_inject_iff map_append)
    have Xw_final: "([X \<rightarrow> \<gamma>''' @ [Nt A] . map Tm u'] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* (?qf, [])"
    proof -
      from derives_impl_completes A_derives derivers_iff_derives have 
        "([X \<rightarrow> \<gamma>''' . Nt A#map Tm u'] # \<rho> @ [init_symbol IPDA], v' @ u' @ u) 
          \<turnstile>P* ([X \<rightarrow> \<gamma>'''@ [Nt A] . map Tm u'] # \<rho> @ [init_symbol IPDA], u' @ u)"
        by (metis append_Cons append_Nil)
      with IPDA.reaches_final_impl_interm_reaches_final[OF ipda] \<rho>_def(1) 
      show ?thesis by (metis S'_def S_def X_prod(3) map_Tm_inject_iff)
    qed
    let ?\<rho>' = "[X \<rightarrow> \<gamma>''' . Nt A#map Tm u'] # \<rho>"
    have \<rho>'_hist: "rev_hist ?\<rho>' = \<gamma>'" using \<rho>_def(2) X_prod(2)  by (simp add: history_def)
    have "([A \<rightarrow> \<alpha> . \<beta>] # ?\<rho>' @ [init_symbol IPDA], v@w) 
      \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []]# ?\<rho>' @ [init_symbol IPDA], w)" 
      using derives_impl_completes derivers_iff_derives Suc(3) 
      by (metis append.right_neutral)
    also have "... \<turnstile>P ([X \<rightarrow> \<gamma>''' @ [Nt A] . map Tm u'] # \<rho> @ [init_symbol IPDA], w)"
      using LR_Parser.IPDA.reducing[OF ipda] by simp
    also note Xw_final
    finally show thesis using Suc(4)[OF _ \<rho>'_hist] by presburger
  qed
qed

end

end
