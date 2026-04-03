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
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [s])} else {});
    \<E> = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta>@[Nt Y] . \<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> P} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> if Y = Y' then {([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], [])} else {})        
in
  \<lparr>pda.init_state = [S' \<rightarrow> [] . [Nt S]], pda.init_symbol = [S' \<rightarrow> [] . []], 
    pda.final_states = {[S' \<rightarrow> [Nt S] . []]}, pda.delta = \<delta>, pda.delta_eps = \<E>\<rparr>"


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

section \<open>IPDA Configurations\<close>

locale IPDA =
  fixes G G' :: "('n::fresh0, 't) Cfg"
      and S S' :: 'n  
  assumes extended: "Extended_Cfg G"
  defines "S \<equiv> Start G"
      and "S' \<equiv> fresh0 (Nts (Prods G) \<union> {S})"
      and "G' \<equiv> Cfg (Prods G \<union> {(S', [Nt S])}) S'"
begin

type_synonym ('q,'s) config = "'q list \<times> 's list"

definition "P \<equiv> Extended_Cfg.IPDA G"

inductive step :: "(('n,'t) item,'t) config \<Rightarrow> (('n,'t) item,'t) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 70) where
delta[intro]: "\<lbrakk>let \<delta> = pda.delta P in  \<alpha> = p#ps; \<alpha>' = q#qs; (q,qs) \<in> \<delta> p x ps\<rbrakk> 
                \<Longrightarrow> (\<alpha>@\<beta>,x#w) \<turnstile> (\<alpha>'@\<beta>,w)" |
eps[intro]: "\<lbrakk>let \<delta>\<^sub>\<epsilon> = pda.delta_eps P in \<alpha> = p#ps; \<alpha>' = q#qs; (q,qs) \<in> \<delta>\<^sub>\<epsilon> p ps\<rbrakk> 
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

abbreviation steps (infix \<open>\<turnstile>*\<close> 70) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by ((induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct),
  (use step_len_dec surj_pair le_trans in fastforce)+)

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

notation char_fa.step (infix \<open>\<turnstile>c\<close> 70)
notation char_fa.steps (infix \<open>\<turnstile>c*\<close> 70)
notation char_fa.stepn (\<open>_ \<turnstile>c'(_') _\<close> 70)
notation char_fa.eps_stepn (\<open>_ \<turnstile>\<epsilon>'(_') _\<close> 70)

lemma char_init_step_is_eps:
  assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c ([A \<rightarrow> \<alpha> . \<beta>], \<gamma>')" (is "(?S,_) \<turnstile>c _")
  shows "A = S \<and> \<gamma> = \<gamma>'"
  using assms proof cases
  case (nxt a)
  from assms have "(S', [Nt S]) \<notin> Prods G"
    unfolding S_defs sorry
  hence "nfa.nxt char_fa ?S a = {}" sorry
  then show ?thesis using nxt by blast
qed simp


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
        using S'_def S_def less.prems(3) by blast
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

lemma comp_impl_deriver:
    assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
    shows "\<exists>w \<gamma>'. Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>'@Nt A#w \<and> Prods G' \<turnstile> \<gamma>'@Nt A#w \<Rightarrow>r \<gamma>'@\<alpha>@\<beta>@w \<and> \<gamma> = \<gamma>'@\<alpha>"
proof -
  from assms obtain n where "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>\<epsilon>(n) ([A \<rightarrow> \<alpha> . \<beta>], [])"
    using char_fa.steps_impl_eps_stepn by blast
  then show ?thesis
  proof (induction n arbitrary: A \<alpha> \<beta>)
    case 0
    with char_init_noeps_eq assms have eq: "([S' \<rightarrow> [] . [Nt S]], \<gamma>) = ([A \<rightarrow> \<alpha> . \<beta>], [])" 
      by auto
    then show ?case using G'_def S_defs deriver_singleton by force
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

end

end
