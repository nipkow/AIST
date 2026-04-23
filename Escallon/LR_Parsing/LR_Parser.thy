theory LR_Parser 
  imports 
    Item_Pushdown_Automata
    Finite_Automata_HF.Finite_Automata_HF
begin

context Extended_Cfg
begin



section \<open>char(G), \<open>LR\<^sub>0(G)\<close>\<close>

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
      using eq nxt_closed q_def by cases (auto simp: It_defs)
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


interpretation I: ipda G IPDA 
  by standard simp

corollary ipda_IPDA: 
  "ipda G IPDA"
  by (rule I.ipda_axioms)

notation char_fa.step (infix \<open>\<turnstile>c\<close> 70)
notation char_fa.steps (infix \<open>\<turnstile>c*\<close> 70)
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




(*

lemma char_init_step_is_eps:
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
      from char_fa.eps_stepn_imp_steps[OF nxt(1)] char_fa.steps_len_dec have "length (a#u) \<le> length \<gamma>"
        by presburger
      hence "length \<gamma> - length (a#u) < length \<gamma> - length u" by simp
      then show ?thesis 
        by (metis \<open>([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* (p, a # u)\<close> char_fa.steps_len_dec impossible_Cons 
            item.exhaust less.hyps nxt(1,2))   
    qed
  qed
qed presburger

lemma char_fa_comp_imp_deriver:
    assumes "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> . \<beta>], [])"
    obtains w \<gamma>' where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>'@Nt A#w" "Prods G' \<turnstile> \<gamma>'@Nt A#w \<Rightarrow>r \<gamma>'@\<alpha>@\<beta>@w" "\<gamma> = \<gamma>'@\<alpha>"
proof -
  from assms obtain n where "([S' \<rightarrow> [] . [Nt S]], \<gamma>) \<turnstile>\<epsilon>(n) ([A \<rightarrow> \<alpha> . \<beta>], [])"
    using char_fa.steps_imp_eps_stepn by blast
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
  sorry 





lemma eq_tl_imp_substring:
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
  oops
(*proof -
  obtain xs where xs_def: "\<gamma> @ Nt A # map Tm w = \<alpha> @ xs @ map Tm u" "(X, xs) \<in> P" 
    using deriver_imp_in_Prods[OF assms] by metis
  moreover have "length w \<ge> length u" using assms sorry
  ultimately obtain zs :: "('a,'b) syms" where zs_def: "zs @ map Tm u = map Tm w" 
    using eq_tl_imp_substring[of "map Tm u" "map Tm w"] 
    by (metis append.assoc append_Cons append_Nil length_map)
  then obtain ys where "xs = ys@zs" "\<delta>@ys = \<gamma>'@[Nt A]"
  proof -
    note xs_def(1)[symmetric]
    also have "\<gamma>' @ Nt A # map Tm w = \<gamma>' @ Nt A # zs @ map Tm u" using zs_def by presburger
    also with xs_def obtain ys where "\<gamma>' @ Nt A # zs @ map Tm u = \<delta> @ ys @ zs @ map Tm u"
      sorry
    finally show thesis using that  \<open>\<gamma>' @ Nt A # zs @ map Tm u = \<delta> @ ys @ zs @ map Tm u\<close> 
      by force
  qed
  then show thesis using that sorry
qed *)

definition toitems :: "'n list \<Rightarrow> ('n,'t) syms list \<Rightarrow> ('n,'t) syms list \<Rightarrow> ('n,'t) item list" where
  "toitems X \<alpha> \<beta> \<equiv> (let \<alpha>\<beta> = zip (tl \<alpha>) (tl \<beta>); Xs = zip X (tl X) in 
    map2 (\<lambda>(Xi, Xsi) (\<alpha>si,\<beta>si). [Xi \<rightarrow> \<alpha>si . Nt Xsi # \<beta>si]) Xs \<alpha>\<beta>)"


lemma derivers_S_append_imp_comp:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm w"
    "\<alpha>@\<beta> = [Nt S]"
  shows "([[S' \<rightarrow> \<alpha> . \<beta>], init_symbol IPDA], w) \<turnstile>P* ([I.final_state, init_symbol IPDA], [])"
proof -
  from assms consider "\<alpha> = [Nt S] \<and> \<beta> = []" | (init) "\<alpha> = [] \<and> \<beta> = [Nt S]"
    using append_eq_Cons_conv by fastforce
  then show ?thesis
  proof cases
    case init
    with assms(1) have "w \<in> LangS G'" using G'_derives_from_S_imp_in_Lang
      by (simp add: derivers_imp_derives)
    then show ?thesis using I.Lang_eq_Lang_G Lang_preserved I.init_state_ipda init 
      unfolding I.Lang_def by auto
  qed (use assms(1) derivers_imp_derives in force)
qed

lemma derivers_imp_in_stack:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>@Nt A#map Tm w"
    "Prods G' \<turnstile> \<gamma>@Nt A#map Tm w \<Rightarrow>r \<gamma>@\<alpha>@map Tm w"
    "\<gamma>@\<alpha>@map Tm w = \<delta>@Nt B#map Tm u"
    "Prods G' \<turnstile> \<delta>@Nt B#map Tm u \<Rightarrow>r \<delta>@\<beta>@map Tm u"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
    "([A \<rightarrow> \<alpha> . []]#\<rho>@[init_symbol IPDA], w) \<turnstile>P* ([final_state, init_symbol IPDA],[])"
  obtains X xs ys \<rho>l \<rho>r where 
    "\<rho> = \<rho>l@[X \<rightarrow> xs . Nt B#ys]#\<rho>r" 
    "([A \<rightarrow> \<alpha> . []]#\<rho>@[init_symbol IPDA], w) \<turnstile>P* ([X \<rightarrow> xs . Nt B#ys]#\<rho>r@[init_symbol IPDA], v@u)"
    "([X \<rightarrow> xs . Nt B#ys]#\<rho>r@[init_symbol IPDA], v@u) \<turnstile>P* ([final_state, init_symbol IPDA],[])"
  sorry

(* FIXME: Does not hold. *)
lemma deriver_imp_ex_hist:
  assumes 
    "Prods G' \<turnstile> \<gamma>@Nt A#map Tm u \<Rightarrow>r* \<delta>@Nt B#map Tm v"
obtains \<rho> \<sigma> where     
    "([A \<rightarrow> \<alpha> . []]#\<rho>@[init_symbol IPDA], u) \<turnstile>P* ([B \<rightarrow> \<beta> . []]#\<sigma>@[init_symbol IPDA], v)"
    "hist \<rho> = \<gamma>"
    "hist \<sigma> = \<delta>"
  oops

*)


lemma derivers_append_map_Tm:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@map Tm v \<Rightarrow>r* u @ map Tm v"
  using assms by (simp add: derivern_append_map_Tm rtranclp_power)


lemma derivers_prepend:
  assumes "P \<turnstile> \<beta> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@\<beta> \<Rightarrow>r* \<alpha> @ u"
  using assms derivern_prepend rtranclp_power by (smt (verit))+

lemma syms_split_last_eq_imp_tl_eq:
  assumes "\<alpha> @ Nt A # map Tm w = \<beta> @ Nt A # \<gamma> @ map Tm v"
    "Nt A \<notin> set \<gamma>"
  obtains u where "\<gamma> = map Tm u" "w = u@v"
  using assms proof (induction w arbitrary: thesis v \<gamma> rule: rev_induct)
  case Nil
  from Nil(2) have A_last: "last (\<beta> @ Nt A # \<gamma> @ map Tm v) = Nt A" 
    by (simp add: snoc_eq_iff_butlast)
  have "\<gamma> @ map Tm v = []" 
    by (rule ccontr)
      (metis append.right_neutral last_ConsR last_appendR last_in_set last_map list.distinct(1)
        list.map_disc_iff sym.distinct(1) Nil(3) A_last)
  then show ?case using Nil by auto
next
  case (snoc a w)
  from snoc(3) have butlast_eq: "\<alpha> @ Nt A # map Tm w = \<beta> @ Nt A # butlast (\<gamma> @ map Tm v)"
  proof -
    have "\<gamma> @ map Tm v \<noteq> []"
      by standard (use snoc(3) in auto)
    then obtain \<delta> b where "\<gamma> @ map Tm v = \<delta> @ [b]" using rev_exhaust by meson
    with snoc(3) show ?thesis by force
  qed
  let ?\<delta> = "butlast (\<gamma> @ map Tm v)"
  obtain \<delta> v' where \<delta>v'_def: "\<delta>@map Tm v' = ?\<delta>" by fast
  note \<delta>v'_eq = butlast_eq[unfolded this[symmetric]]
  from \<delta>v'_def snoc(4) have "Nt A \<notin> set \<delta>" 
  proof -
    from \<delta>v'_def have "set \<delta> \<subseteq> set ?\<delta>" 
      by (metis Un_iff set_append subsetI) 
    also have "... \<subseteq> set (\<gamma> @ map Tm v)" 
      by (meson in_set_butlastD subsetI)
    finally show ?thesis using snoc(4) by auto
  qed
  from snoc(1)[OF _ \<delta>v'_eq this] obtain u where "\<delta> = map Tm u" "w = u @ v'" by blast
  then show thesis using snoc(2,3) \<delta>v'_def \<delta>v'_eq append_same_eq
    by (smt (verit, ccfv_threshold) list.inject map_Tm_inject_iff map_eq_append_conv
        same_append_eq)
qed

corollary syms_decomp_rightmost:
  assumes "\<alpha> @ Nt A # map Tm w = \<beta> @ \<gamma> @ \<delta> @ map Tm x"
    "Nt A \<in> set \<gamma>" "Nt A \<notin> set \<delta>"
  obtains \<eta> u v where "\<gamma> = \<eta> @ Nt A # map Tm u" "\<delta> = map Tm v"  "w = u@v@x"
proof -
  from split_list_last[OF assms(2)] obtain \<zeta> \<theta> where \<gamma>_decomp: "\<gamma> = \<zeta> @ Nt A # \<theta>" "Nt A \<notin> set \<theta>" 
    by blast
  with assms(1) have "\<alpha> @ Nt A # map Tm w = \<beta> @ \<zeta> @ Nt A # \<theta> @ \<delta> @ map Tm x" by simp
  moreover from \<gamma>_decomp(2) assms(3) have "Nt A \<notin> set (\<theta>@\<delta>)" by simp
  ultimately obtain y where y_defs: "\<theta>@\<delta> = map Tm y" "w = y @ x" 
    using syms_split_last_eq_imp_tl_eq[of \<alpha> A _ "\<beta>@\<zeta>" "\<theta>@\<delta>" _] by auto
  then obtain u v where "\<theta> = map Tm u" "\<delta> = map Tm v" "w = u@v@x" 
    using append_eq_map_conv y_defs by (metis append.assoc)
  then show thesis using that \<gamma>_decomp 
    by blast
qed

corollary syms_decomp_rightmost2:
  assumes "\<alpha> @ Nt A # map Tm w = \<beta> @ \<gamma> @ map Tm x"
    "Nt A \<in> set \<gamma>"
  obtains \<delta> u where "\<gamma> = \<delta> @ Nt A # map Tm u" "w = u@x"
proof -
  from assms(1) have 1: "\<alpha> @ Nt A # map Tm w = \<beta> @ \<gamma> @ [] @ map Tm x" by simp
  obtain \<delta> u v where "\<gamma> = \<delta> @ Nt A # map Tm u" "[] = map Tm v" "w = u@v@x"
    using syms_decomp_rightmost[OF 1 assms(2) _] by auto
  then show thesis using that by blast
qed

lemma no_Nts_imp_Tms:
  assumes "\<nexists>A. Nt A \<in> set \<alpha>"
  obtains w where "\<alpha> = map Tm w"
  using assms by (metis sym.exhaust ex_map_conv)

lemma syms_split_rightmost:
  assumes "\<exists>A. Nt A \<in> set \<alpha>"
  obtains \<beta> A u where "\<alpha> = \<beta> @ Nt A # map Tm u"
  using assms proof (induction "length \<alpha>" arbitrary: \<alpha> thesis rule: less_induct)
  case less
  then obtain X \<beta> where \<alpha>_def: "\<alpha> = X#\<beta>" 
    by (metis list.set_cases)
  show ?case 
  proof (cases "\<exists>A. Nt A \<in> set \<beta>")
    case True
    show thesis using less(1)[OF _ _ True] less(2) unfolding \<alpha>_def 
      by (metis Cons_eq_appendI length_Cons lessI)
  next
    case False
    show ?thesis using no_Nts_imp_Tms[OF False] less(2)[of "[]"] less(3) False 
      unfolding \<alpha>_def by force
  qed
qed



lemma deriver_cases[consumes 1, case_names rightmost Tms_only]:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r \<beta>"
  obtains \<gamma> A u \<gamma>' B v where "\<alpha> = \<gamma> @ Nt A # map Tm u" "\<beta> = \<gamma>' @ Nt B # map Tm v" |
          \<gamma> A u v where "\<alpha> = \<gamma> @ Nt A # map Tm u" "\<beta> = map Tm v"
proof -
  from assms obtain \<gamma> A u \<delta> where \<alpha>\<beta>_defs: "\<alpha> = \<gamma> @ Nt A # map Tm u" "\<beta> = \<gamma> @ \<delta> @ map Tm u"
    using deriver.cases by meson
  consider "\<nexists>B. Nt B \<in> set \<delta>" | B where "Nt B \<in> set \<delta>" by blast
  then show thesis
  proof cases
    case 1
    from no_Nts_imp_Tms[OF 1] show ?thesis 
      by (meson \<alpha>\<beta>_defs(1) syms_split_rightmost no_Nts_imp_Tms that(1,2)) 
  next
    case 2
    then show ?thesis using syms_split_rightmost \<alpha>\<beta>_defs 
      by (metis no_Nts_imp_Tms that(1,2))
  qed
qed




(* induct set? *)
lemma stepcnt_induct[consumes 1, case_names base step]:
  assumes
    "r\<^sup>*\<^sup>* a b"
    "P a"
    "\<And>n y z. \<lbrakk>(r ^^ n) a y; r y z; P y\<rbrakk> \<Longrightarrow> P z"
  shows "P b"
proof -
  from assms(1) obtain n where "(r ^^ n) a b" 
    by (metis rtranclp_power)
  then show ?thesis 
    by (induction n arbitrary: b) (use assms(2-) in auto)
qed

lemma stepcnt_induct2[consumes 1, case_names base step]:
  assumes
    "r\<^sup>*\<^sup>* a b"
    "P a"
    "\<And>n z. \<lbrakk>\<And>y. (r ^^ n) a y \<Longrightarrow> P y; (r ^^ Suc n) a z\<rbrakk> \<Longrightarrow> P z"
  shows "P b"
proof -
  from assms(1) obtain n where "(r ^^ n) a b" 
    by (metis rtranclp_power)
  then show ?thesis
    by (induction n arbitrary: b) (use assms(2-) in auto)
qed



(*

lemma derive_imp_derive_Nt:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r* \<delta>"
    "P \<turnstile> \<delta> \<Rightarrow>r \<gamma>' @ Nt B # map Tm w"
    "P = Prods G''"
    "reduced G''"
    "LangS G'' \<noteq> {}"
    "Eps_free P"
  obtains X \<alpha> \<alpha>' \<beta> \<beta>' v v' where
    "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha>@Nt X#\<beta>"
    "P \<turnstile> \<alpha>@Nt X#\<beta> \<Rightarrow>r* \<alpha>@Nt X#map Tm v"
    "P \<turnstile> \<alpha>@Nt X#map Tm v \<Rightarrow>r \<alpha>@\<alpha>'@Nt B#\<beta>'@map Tm v"
    "P \<turnstile> \<alpha>@\<alpha>'@Nt B#\<beta>'@map Tm v \<Rightarrow>r* \<alpha>@\<alpha>'@ Nt B#map Tm (v'@v)" 
    "\<gamma>' = \<alpha>@\<alpha>'" "w = v'@v"

(*proof (cases "[Nt A] = \<delta>")
  case True
  with assms have A_step: "P \<turnstile> [Nt A] \<Rightarrow>r \<gamma>' @ Nt B # map Tm w" by auto
  then show ?thesis using assms that
    by (smt (verit, ccfv_threshold) True append.assoc append.right_neutral append.right_neutral
        deriver.cases list.map_disc_iff rtranclp.rtrancl_refl same_append_eq self_append_conv2)
next
  case False
  note A_neq_\<delta> = this
  obtain \<alpha> C x \<beta> where \<delta>_prod: "\<delta> = \<alpha> @ Nt C # map Tm x" "(C,\<beta>) \<in> P"
    "\<alpha> @ \<beta> @ map Tm x = \<gamma>' @ Nt B # map Tm w" 
    using deriver.cases[OF assms(2)] by metis
  then show ?thesis 
  proof (cases "Nt B \<in> set \<beta>")
    case True
    from \<delta>_prod syms_decomp_rightmost2[OF _ True] obtain \<zeta> u where "\<beta> = \<zeta> @ Nt B # map Tm u"
      "w = u@x" by metis
    then show ?thesis using that[of _ _ _ _ \<zeta> _] \<delta>_prod assms 
      by (smt (verit, best) Cons_eq_appendI append_assoc append_same_eq map_append rtranclp.simps)
  next
    case False
    with that \<delta>_prod show thesis
    proof (induction "length (\<gamma>'@Nt B#map Tm w)" arbitrary: \<gamma>' \<delta> \<alpha> C x \<beta> B w thesis rule: less_induct)
      case less
      from less(3-) have "Nt B \<in> set \<alpha>" 
      by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral 
          in_Nts_syms list.set_intros(1))
    from syms_decomp_rightmost[OF _ this less(6), of _ _ "[]" x] less
    obtain \<zeta> u v where \<alpha>_decomp: "\<alpha> = \<zeta> @ Nt B # map Tm u" "\<beta> = map Tm v" "w = u@v@x" 
      by (metis self_append_conv2)
    moreover from this have "length (\<zeta> @ Nt B # map Tm u) < length (\<gamma>' @ Nt B # map Tm w)" 
    proof -
      thm less
      show ?thesis sorry
    qed
(* TODO fix this mess *)
    ultimately obtain \<eta> X \<theta> y \<eta>' \<theta>' y' where
      "P \<turnstile> [Nt A] \<Rightarrow>r* \<eta> @ Nt X # \<theta>" "P \<turnstile> \<eta> @ Nt X # \<theta> \<Rightarrow>r* \<eta> @ Nt X # map Tm y"
      "P \<turnstile> \<eta> @ Nt X # map Tm y \<Rightarrow> \<eta> @ \<eta>' @ Nt B # \<theta>' @ map Tm y"
      "P \<turnstile> \<eta> @ \<eta>' @ Nt B # \<theta>' @ map Tm y \<Rightarrow>r* \<eta> @ \<eta>' @ Nt B # map Tm (y' @ y)"
      "\<zeta> = \<eta> @ \<eta>'" "u = y' @ y" 
      using less(1)[of \<zeta> B u _ dd xx gg "[]" "map Tm u"] less(3) less.prems 
      
    with less \<alpha>_decomp show thesis 
      using \<open>length \<zeta> < length \<gamma>'\<close> by force
      

    then show ?case using less(1)[of \<zeta> B u "\<zeta> @ [Nt B]" "map Tm u" "[]"] less(3) 
      sorry
    qed



    with \<delta>_prod have "Nt B \<in> set \<alpha>" 
      by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral 
          in_Nts_syms list.set_intros(1))
    from syms_decomp_rightmost[OF _ this False, of _ _ "[]" x] \<delta>_prod(3)
    obtain \<zeta> u v where \<alpha>_decomp: "\<alpha> = \<zeta> @ Nt B # map Tm u" "\<beta> = map Tm v" "w = u@v@x" 
      by (metis self_append_conv2)
    thm less(1)
    then show ?thesis using step(4)[of \<alpha>1 X1 \<beta>1 v1 \<alpha>1' \<beta>1'] \<delta>_prod
  qed
qed 














  using assms(1,2) proof (induction "length \<gamma>'" arbitrary: \<delta> \<gamma>' B w rule: less_induct)
  case less
  then show ?case 
  proof (cases "[Nt A] = \<delta>")
    case True
    with less have A_step: "P \<turnstile> [Nt A] \<Rightarrow>r \<gamma>' @ Nt B # map Tm w" by auto
    then show ?thesis using less
      by (smt (verit, ccfv_threshold) True append.assoc append.right_neutral append.right_neutral
          deriver.cases list.map_disc_iff rtranclp.rtrancl_refl same_append_eq self_append_conv2)
  next
    case False
    note A_neq_\<delta> = this
    obtain \<alpha> C x \<beta> where \<delta>_prod: "\<delta> = \<alpha> @ Nt C # map Tm x" "(C,\<beta>) \<in> P"
      "\<alpha> @ \<beta> @ map Tm x = \<gamma>' @ Nt B # map Tm w" 
      using deriver.cases[OF less(4)] by metis
    then show ?thesis 
    proof (cases "Nt B \<in> set \<beta>")
      case True
      from \<delta>_prod syms_decomp_rightmost2[OF _ True] obtain \<zeta> u where "\<beta> = \<zeta> @ Nt B # map Tm u"
        "w = u@x" by metis
      then show ?thesis using less(2)[of _ _ _ _ \<zeta> _] \<delta>_prod less(1,3-4) 
        by (smt (verit, best) Cons_eq_appendI append_assoc append_same_eq map_append rtranclp.simps)
    next
      case False
      with \<delta>_prod have "Nt B \<in> set \<alpha>" 
        by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral 
            in_Nts_syms list.set_intros(1))
      from syms_decomp_rightmost[OF _ this False, of _ _ "[]" x] \<delta>_prod(3)
      obtain \<zeta> u v where \<alpha>_decomp: "\<alpha> = \<zeta> @ Nt B # map Tm u" "\<beta> = map Tm v" "w = u@v@x" 
        by (metis self_append_conv2)
      thm less(1)
      then show ?thesis using step(4)[of \<alpha>1 X1 \<beta>1 v1 \<alpha>1' \<beta>1'] \<delta>_prod
    qed
  qed
qed 





  using assms(1,2) proof (induction arbitrary: \<gamma>' B w rule: rtranclp_induct)
  case base
  then show ?case
    by (metis append.right_neutral append_Nil list.simps(8) rtranclp.rtrancl_refl)
next
  case (step \<delta> \<gamma>)
  then show ?case
  proof (cases "[Nt A] = \<delta>")
    case True
    with step have A_step: "P \<turnstile> [Nt A] \<Rightarrow>r \<gamma>" by auto
    then show ?thesis
    proof (cases rule: deriver_cases)
      case (rightmost _ _ _  \<zeta> D v)
      note rightmost = rightmost(2)
      then obtain \<iota> where \<gamma>_prod: "\<zeta> @ \<iota> @ map Tm v = \<gamma>' @ Nt B # map Tm w" "(D,\<iota>) \<in> P" 
        using deriver_imp_handle step(5) by meson
      then show ?thesis 
      proof (cases "Nt B \<in> set \<iota>")
        case True
        from syms_decomp_rightmost2[OF \<gamma>_prod(1)[symmetric] True] obtain \<theta> u where 
          \<iota>_decomp: "\<iota> = \<theta> @ Nt B # map Tm u" "w = u @ v" by blast
        with A_step \<iota>_decomp \<gamma>_prod(1) step(4-) rightmost show thesis by fastforce
      next
        case False
        with \<gamma>_prod(1) have "Nt B \<in> set \<zeta>"
          by (metis Nts_syms_map_Tm Un_iff empty_iff in_Nts_syms in_set_conv_decomp set_append)
        with \<gamma>_prod(1) False syms_decomp_rightmost[OF _ this False, of _ _ "[]" v]
        obtain \<eta> u x where "\<zeta> = \<eta> @ Nt B # map Tm u" "\<iota> = map Tm x" "w = u @ x @ v"
          using that by auto
        with A_step rightmost \<gamma>_prod(1) step(5)
          step(4)[of "[]" A "[]" "[]" \<eta>] show thesis by fastforce
      qed
    next
      case (Tms_only \<eta> C u v)
      then show ?thesis using step 
        by (metis deriver_imp_derive not_derive_map_Tm)
    qed
  next
    case False
    note A_neq_\<delta> = this
    from step(5) obtain \<alpha> C x \<beta> where \<gamma>_prod: "\<gamma> = \<alpha> @ Nt C # map Tm x" "(C,\<beta>) \<in> P"
      "\<alpha> @ \<beta> @ map Tm x = \<gamma>' @ Nt B # map Tm w" 
      using deriver.cases[OF step(5)] by metis
    then show ?thesis 
    proof (cases "Nt B \<in> set \<beta>")
      case True
      from \<gamma>_prod syms_decomp_rightmost2[OF _ True] obtain \<zeta> u where "\<beta> = \<zeta> @ Nt B # map Tm u"
        "w = u@x" by metis
      then show ?thesis using step(4)[of _ _ _ _ \<zeta> _] \<gamma>_prod step(1-2,5) 
        by (smt (verit, best) Cons_eq_appendI append_assoc append_same_eq map_append rtranclp.simps)
    next
      case False
      with \<gamma>_prod have "Nt B \<in> set \<alpha>" 
        by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral 
            in_Nts_syms list.set_intros(1))
      from syms_decomp_rightmost[OF _ this False, of _ _ "[]" x] \<gamma>_prod(3)
      obtain \<zeta> u v where \<alpha>_decomp: "\<alpha> = \<zeta> @ Nt B # map Tm u" "\<beta> = map Tm v" "w = u@v@x" 
        by (metis self_append_conv2)
      with \<gamma>_prod step(2,5) 
        (* TODO: prove that if an Nt is in a string, there exists a step that produced it *)
      then show ?thesis using step(3) \<gamma>_prod 
    qed
  qed
qed







    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed 

 using assms(1,2) proof (induction arbitrary: \<gamma>' B w thesis rule: stepcnt_induct)
  case base
  then show ?case 
    by (metis append.right_neutral append_Nil list.simps(8) rtranclp.rtrancl_refl)
next
  case (step n \<delta> \<gamma>)
  then show ?case proof (induction n arbitrary: \<gamma> \<delta> \<gamma>' B w  thesis rule: less_induct)
    case (less n)
    show ?case 
    proof (cases n)
      case 0
      with less have A_step: "P \<turnstile> [Nt A] \<Rightarrow>r \<gamma>" by auto
      then show ?thesis
      proof (cases rule: deriver_cases)
        case (rightmost _ _ _  \<zeta> D v)
        note rightmost = rightmost(2)
        then obtain \<iota> where \<gamma>_prod: "\<zeta> @ \<iota> @ map Tm v = \<gamma>' @ Nt B # map Tm w" "(D,\<iota>) \<in> P" 
          using deriver_imp_handle less(6) by meson
        then show ?thesis 
        proof (cases "Nt B \<in> set \<iota>")
          case True
          from syms_decomp_rightmost2[OF \<gamma>_prod(1)[symmetric] True] obtain \<theta> u where 
            \<iota>_decomp: "\<iota> = \<theta> @ Nt B # map Tm u" "w = u @ v" by blast
          with A_step \<iota>_decomp \<gamma>_prod(1) less(5-) rightmost show thesis by fastforce
        next
          case False
          with \<gamma>_prod(1) have "Nt B \<in> set \<zeta>"
            by (metis Nts_syms_map_Tm Un_iff empty_iff in_Nts_syms in_set_conv_decomp set_append)
          with \<gamma>_prod(1) False syms_decomp_rightmost[OF _ this False, of _ _ "[]" v]
          obtain \<eta> u x where "\<zeta> = \<eta> @ Nt B # map Tm u" "\<iota> = map Tm x" "w = u @ x @ v"
            using that by auto
          with A_step rightmost \<gamma>_prod(1) less(6)
            less(5)[of "[]" A "[]" "[]" \<eta>] show thesis by fastforce
        qed
      next
        case (Tms_only \<eta> C u v)
        then show ?thesis using less 
          by (metis deriver_imp_derive not_derive_map_Tm)
      qed
    next
      case (Suc m)
      obtain \<alpha> C x \<beta> where \<gamma>_prod: "\<gamma> = \<alpha> @ Nt C # map Tm x" "(C,\<beta>) \<in> P"
        "\<alpha> @ \<beta> @ map Tm x = \<gamma>' @ Nt B # map Tm w" 
        using deriver.cases[OF less(6)] by metis
      then show ?thesis
      proof (cases "Nt B \<in> set \<beta>")
        case True
        from \<gamma>_prod syms_decomp_rightmost2[OF _ True] obtain \<zeta> u where "\<beta> = \<zeta> @ Nt B # map Tm u"
          "w = u@x" by metis
        then show ?thesis using less(5)[of \<alpha> C "map Tm x" x \<zeta> "map Tm u"] \<gamma>_prod less(1-4,6)
          by (metis (no_types, lifting) ext append.assoc append_Cons append_same_eq map_append 
              rtranclp.simps rtranclp_power) 
      next
        case False
        with \<gamma>_prod have "Nt B \<in> set \<alpha>" 
          by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral 
              in_Nts_syms list.set_intros(1))
        from syms_decomp_rightmost[OF _ this False, of _ _ "[]" x] \<gamma>_prod(3)
        obtain \<zeta> u v where \<alpha>_decomp: "\<alpha> = \<zeta> @ Nt B # map Tm u" "\<beta> = map Tm v" "w = u@v@x" 
          by (metis self_append_conv2)
        thm less(1)[of m \<eta> \<delta> C \<alpha> x]  less(4)
        then show ?thesis sorry
      qed
    qed
  qed
qed *) *)

lemma derivers_tl_substring:
  assumes "P \<turnstile> \<alpha> @ Nt A # map Tm v \<Rightarrow>r* \<beta> @ Nt B # map Tm w"
  obtains u where "w = u@v"
  using assms proof (induction "\<beta> @ Nt B # map Tm w" arbitrary: \<beta> B w thesis)
  case base
  then show ?case using right_derivs_eq_imp_eq_tl[OF base(1)] by blast
next
  case (step y \<beta> B w)
  then obtain \<gamma> C u where y_def: "y = \<gamma> @ Nt C # map Tm u" 
    by (metis deriver_cases)
  with step(3) obtain x where u_decomp: "u = x@v" by blast
  from step(2) obtain \<delta> where "\<beta> @ Nt B # map Tm w = \<gamma> @ \<delta> @ map Tm u" 
    unfolding y_def using deriver_imp_handle by metis
  with syms_decomp_rightmost show ?case using u_decomp sorry
qed

lemma deriver_rightmost_cases[consumes 1, case_names prod prefix]:
  assumes "P \<turnstile> \<alpha> @ Nt A # map Tm u \<Rightarrow>r \<beta> @ Nt B # map Tm w"
  obtains \<gamma> v where "\<beta> @ Nt B # map Tm w = \<alpha> @ \<gamma> @ Nt B # map Tm v @ map Tm u" |
          \<delta> v x where "\<alpha> = \<delta> @ Nt B # map Tm x" "\<beta> @ Nt B # map Tm w = \<alpha> @ map Tm (v@u)"
proof -
  from assms obtain \<gamma> where deriv: "\<beta> @ Nt B # map Tm w = \<alpha> @ \<gamma> @ map Tm u" "(A, \<gamma>) \<in> P" 
    by (metis deriver_imp_handle)
  then consider (Tms) x where "\<gamma> = map Tm x" | (Nt) \<delta> C \<zeta> where "\<gamma> = \<delta> @ Nt C # \<zeta>" 
    by (metis split_list no_Nts_imp_Tms)
  then show ?thesis 
  proof cases
    case Tms
    with deriv have "\<beta> @ Nt B # map Tm w = \<alpha> @ map Tm (x@u)" by auto
    moreover from this obtain \<delta> v where "\<alpha> = \<delta> @ Nt B # map Tm v" 
      by (metis Nts_syms_append Nts_syms_map_Tm append.right_neutral append_Nil in_Nts_syms 
          in_set_conv_decomp list.simps(8) syms_decomp_rightmost2)
    ultimately show ?thesis using deriv that by blast
  next
    case Nt
    obtain \<eta> D y where "Nt C # \<zeta> = \<eta> @ Nt D # map Tm y" 
        by (meson list.set_intros(1) syms_split_rightmost)
   moreover from this have "B = D" using deriv Nt right_derivs_eq_imp_eq_tl[of \<beta> B w "\<alpha> @ \<delta> @ \<eta>" D "y@u"]
     by simp
   ultimately show ?thesis using Nt that deriv by (metis append.assoc append_Cons)
  qed
qed


lemma derivers_Nt_imp_last_produced:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<gamma>"
    "Nt B \<in> set \<gamma>"
  obtains C \<alpha> \<beta> \<delta> v where "P \<turnstile> [Nt A] \<Rightarrow>r* \<delta> @ Nt C # map Tm v"
    "P \<turnstile> \<delta> @ Nt C # map Tm v \<Rightarrow>r \<delta> @ \<alpha> @ Nt B # \<beta> @ map Tm v"
    "P \<turnstile> \<delta> @ \<alpha> @ Nt B # \<beta> @ map Tm v \<Rightarrow>r* \<gamma>"
    "Nt B \<notin> set \<beta>"
  using assms proof (induction n arbitrary: \<gamma>)
  case 0
  from 0(2) show ?case using 0(1)[of "[]" A "[]"] split_list[OF 0(3)] 
    by (metis "0.prems"(3) Nil_is_map_conv append_Nil2 in_set_conv_decomp_last relpowp_Suc_0
        rtranclp.rtrancl_refl self_append_conv2)
next
  case (Suc n)
  then obtain \<delta> where \<delta>_def: "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<delta>" "P \<turnstile> \<delta> \<Rightarrow>r \<gamma>" by auto
  show ?case 
  proof (cases "Nt B \<in> set \<delta>")
    case True
    then show ?thesis using Suc \<delta>_def rtranclp.rtrancl_into_rtrancl
      by (smt (verit, best))
  next
    case False
    from \<delta>_def obtain \<zeta> C v \<eta> where yz_defs: "\<delta> = \<zeta> @ Nt C # map Tm v" "\<gamma> = \<zeta> @ \<eta> @ map Tm v"
        "(C, \<eta>) \<in> P" by (meson deriver.cases)
      moreover with \<delta>_def(2) Suc(4) False obtain \<alpha> \<beta> where "\<eta> = \<alpha> @ Nt B # \<beta>" "Nt B \<notin> set \<beta>"
        using split_list_last by force 
      ultimately show ?thesis using \<delta>_def Suc
        by (metis (no_types, lifting) append.assoc append_Cons relpowp_imp_rtranclp rtranclp.simps)
  qed
qed

lemma derivers_imp_derivers_tl:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha> @ Nt A # map Tm v"
  obtains \<beta> where "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha> @ Nt A # \<beta>"
    "P \<turnstile> \<alpha> @ Nt A # \<beta> \<Rightarrow>r* \<alpha> @ Nt A # map Tm v"
  using assms by induction (use that assms in auto)
thm deriver.cases
inductive rm_chain :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) syms \<Rightarrow> ('a, 'b) item list \<Rightarrow> ('a, 'b) syms 
                            \<Rightarrow> bool" 
   (\<open>_ \<Turnstile> _ \<Rightarrow>r* _ \<Rightarrow>r* _\<close> 30) for P where

refl[intro]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [] \<Rightarrow>r* \<alpha>" |

(*step[intro]:  "\<lbrakk>P \<turnstile> \<alpha> @ Nt A # map Tm v \<Rightarrow>r \<alpha> @ \<alpha>'@ Nt B # \<beta> @ map Tm v; P \<turnstile> \<beta> \<Rightarrow>r* map Tm u\<rbrakk>
    \<Longrightarrow> P \<Turnstile> \<alpha> @ Nt A # map Tm v \<Rightarrow>r* [[A \<rightarrow> \<alpha>' . Nt B # \<beta>]] \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt B # map Tm u @ map Tm v " | *)

(* step_Tms[intro]: "P \<turnstile> \<alpha> @ Nt A # map Tm v \<Rightarrow>r \<alpha> @ map Tm u @ map Tm v 
    \<Longrightarrow> P \<Turnstile> \<alpha> @ Nt A # map Tm v \<Rightarrow>r* [[A \<rightarrow> [] . map Tm u]] \<Rightarrow>r* \<alpha> @ map Tm u @ map Tm v" | *)

step[intro]:  "\<lbrakk>P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v; 
    P \<turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r \<alpha> @ \<alpha>' @ Nt Y # \<beta> @ map Tm v; P \<turnstile> \<beta> \<Rightarrow>r* map Tm u\<rbrakk>
    \<Longrightarrow> P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [X \<rightarrow> \<alpha>' . Nt Y # \<beta>]#\<rho> \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v"


lemma rm_chain_Tms_impossible[simp]:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> x#xs . map Tm u]#\<rho> \<Rightarrow>r* \<beta>"
  shows False
  using assms by cases auto

lemma rm_chain_imp_Nt_hd[elim]:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> \<alpha>' . \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"
  obtains B \<beta>' where "\<beta> = Nt B # \<beta>'"
  using assms by cases auto


(* using inductive_cases adds the impossible Nil case *)
(*
lemma rm_chain_stepE[elim]:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* [[A \<rightarrow> \<alpha>' . Nt B # \<beta>]] \<Rightarrow>r* \<gamma>"
  obtains \<delta> v u where 
    "\<alpha> = \<delta> @ Nt A # map Tm v" "\<gamma> = \<delta> @ \<alpha>' @ Nt B # map Tm u @ map Tm v"
    "P \<turnstile> \<delta> @ Nt A # map Tm v \<Rightarrow>r \<delta> @ \<alpha>' @ Nt B # \<beta> @ map Tm v"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u"
  using assms by cases (use that rm_chain_impossible in fastforce)+ *)

(*lemma rm_chain_step_TmsE[elim]:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* [[A \<rightarrow> \<alpha>' . map Tm u]] \<Rightarrow>r* \<gamma>"
  obtains \<delta> v where 
    "\<alpha> = \<delta> @ Nt A # map Tm v" "\<alpha>' = []" "\<gamma> = \<delta> @ map Tm u @ map Tm v"
    "P \<turnstile> \<delta> @ Nt A # map Tm v \<Rightarrow>r \<delta> @ map Tm u @ map Tm v"
  using assms by cases (use that rm_chain_impossible in fastforce)+*)

inductive_cases rm_chain_reflE[elim]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [] \<Rightarrow>r* \<beta>"
inductive_cases rm_chain_stepE[elim]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> \<alpha>' . Nt B # \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"

(*inductive_cases rm_chain_steps_TmsE[elim]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> \<alpha>' . map Tm u]#i#\<rho> \<Rightarrow>r* \<gamma>"*)

lemma rm_chain_imp_prod:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"
  shows "(A, \<alpha>@\<beta>) \<in> P"
  using assms syms_split_rightmost by cases (simp add: deriver_imp_in_Prods)



lemma Nt_in_chain_imp_produced:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma> @ Nt X # map Tm v"
    "Nt B \<in> set \<gamma>"
  obtains "is" A \<alpha> \<beta> js \<delta> u where "\<rho> = is @ [A \<rightarrow> \<alpha> . Nt B # \<beta>] # js"
    "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* js \<Rightarrow>r* \<delta> @ Nt A # map Tm u"
  oops



lemma rm_chain_singleton_imp_eq:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . Nt C # \<beta>]#\<rho> \<Rightarrow>r* \<gamma> @ Nt B # map Tm w"
  shows "C = B \<and> (\<exists>u v. w = u @ v \<and> P \<turnstile> \<beta> \<Rightarrow>r* map Tm u)"
  using assms proof cases
  case (step \<alpha>' v u)
  with right_derivs_eq_imp_eq_tl[of _ _ _ "\<alpha>' @ \<alpha>" C] have "w = u @ v"
    by fastforce
  moreover with step have "C = B" by simp
  ultimately show ?thesis using step by blast 
qed



lemma rm_chain_imp_hd_prod_rightmost:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma> @ Nt B # map Tm w"
  obtains A \<alpha> \<beta> "is" u v where "\<rho> = [A \<rightarrow> \<alpha> . Nt B # \<beta>] # is"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u" "w = u @ v" | "\<alpha>\<^sub>0 = \<gamma> @ Nt B # map Tm w"
using assms proof cases
  case (step \<rho> \<alpha> X v \<alpha>' Y \<beta> u)
  moreover with right_derivs_eq_imp_eq_tl[of _ _ _ "\<alpha> @ \<alpha>'"] have "w = u@v" by simp
  moreover from this have "B = Y" using step(2) by simp
  ultimately show ?thesis using that by blast
qed argo



lemma rm_chain_imp_derivers:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta>"
  shows "P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>"
  using assms proof induction
  case (step \<alpha>\<^sub>0 \<rho> \<alpha> X v \<alpha>' Y \<beta> u)
  from step(3) derivers_append_map_Tm[OF step(3)] have
    "P \<turnstile>  \<alpha> @ \<alpha>' @ Nt Y # \<beta> @ map Tm v \<Rightarrow>r*  \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v"
    by (metis append_Cons append_Nil derivers_prepend)
  then show ?case using step by simp
qed simp

lemma app_derivers_app:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* map Tm u"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  shows "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* map Tm (u@v)"
  using assms derivers_iff_derives by (metis derives_append_map_Tm)

lemma syms_append_cases[consumes 1, case_names left right]:
  assumes "\<alpha> @ Nt X # map Tm w = \<beta> @ \<gamma>"
  obtains u v where "\<beta> = \<alpha> @ Nt X # map Tm u" "\<gamma> = map Tm v" "w = u @ v" |
          \<delta> where "\<alpha> = \<beta> @ \<delta>" "\<delta> @ Nt X # map Tm w = \<gamma>"
proof (cases "Nt X \<in> set \<gamma>")
  case True
  with syms_decomp_rightmost[of \<alpha> X w \<beta> \<gamma> "[]" "[]"]
  show ?thesis using assms using that(2) by force
next
  case False
  with assms have "Nt X \<in> set \<beta>" 
    by (metis in_set_conv_decomp Un_iff set_append)
  with syms_decomp_rightmost[of \<alpha> X w "[]" \<beta> \<gamma> "[]"]
  show ?thesis using False that(1) Cons_eq_appendI assms by force
qed

thm syms_decomp_rightmost
lemma derivers_singleton_imp_rm_chain:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v"
    "P = Prods J"
    "reduced J"
    "LangS J \<noteq> {}"
    "A \<in> Nts P"
  obtains \<rho> where "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v"
  using assms(1) proof (induction n arbitrary: \<alpha> X v thesis)
  case 0
  then show ?case using rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" \<alpha> X] by auto
next
  case (Suc n)
  from Suc(3) obtain \<beta> B u \<gamma> where Suc_steps: "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<beta> @ Nt B # map Tm u"
    "\<beta> @ \<gamma> @ map Tm u = \<alpha> @ Nt X # map Tm v" "P \<turnstile> \<beta> @ Nt B # map Tm u \<Rightarrow>r \<beta> @ \<gamma> @ map Tm u"
    using deriver.cases by (smt (verit, del_insts) relpowp_Suc_E)
  from Suc(1)[OF _ this(1)] obtain \<rho> where last_chain_step: "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta> @ Nt B # map Tm u" 
    by blast


  from  last_chain_step Suc_steps(2,3) Suc(2) show thesis
  proof (induction "length \<rho>" arbitrary: \<rho>  B  \<beta> u X \<gamma> \<alpha> v thesis rule: less_induct)
    case less
    show ?case proof (cases "Nt X \<in> set \<gamma>")
      case True
      from less obtain \<delta> w where"\<gamma> = \<delta> @ Nt X # map Tm w" "w @ u = v" 
      by (metis True syms_decomp_rightmost2)
    with less show thesis by force
    next
      case False
      with less have X_in_\<beta>: "Nt X \<in> set \<beta>" 
        by (metis Nts_syms_append Nts_syms_map_Tm Un_iff empty_iff in_Nts_syms list.set_intros(1))
      with rm_chain_imp_hd_prod_rightmost[OF less(2)] 
      obtain X' \<alpha>' \<beta>' "is" where 
        \<rho>_def: "\<rho> = [X' \<rightarrow> \<alpha>' . Nt B # \<beta>'] # is" 
        using that by cases (auto simp add: Cons_eq_append_conv)
      from rm_chain_stepE[OF less(2)[unfolded \<rho>_def]] obtain \<zeta> w x where
        snd_last_chn_step: 
        "\<beta> @ Nt B # map Tm u = \<zeta> @ \<alpha>' @ Nt B # map Tm w @ map Tm x"
        "P \<Turnstile> [Nt A] \<Rightarrow>r* is \<Rightarrow>r* \<zeta> @ Nt X' # map Tm x"
        "P \<turnstile> \<zeta> @ Nt X' # map Tm x \<Rightarrow>r \<zeta> @ \<alpha>' @ Nt B # \<beta>' @ map Tm x"
        "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm w"
        by metis
      from right_derivs_eq_imp_eq_tl this(1) have uwx: "u = w @ x" 
        by (metis append.assoc map_append)
      with snd_last_chn_step(1) have \<beta>\<zeta>\<alpha>': "\<beta> = \<zeta> @ \<alpha>'"
        by simp
      from syms_decomp_rightmost[OF _ X_in_\<beta> False, of \<alpha> v "[]" u] obtain \<delta> y z where
        \<beta>\<gamma>_decomp: "\<beta> = \<delta> @ Nt X # map Tm y" "\<gamma> = map Tm z" "v = y @ z @ u"
        using less(3) by auto
      have B\<beta>'_derivers: "P \<turnstile> Nt B # \<beta>' \<Rightarrow>r* map Tm z @ map Tm w" 
      proof -
        have "P \<turnstile> [Nt B] \<Rightarrow>r map Tm z" using deriver_singleton deriver_imp_in_Prods[OF less(4)] 
          \<beta>\<gamma>_decomp by fast
        from this[THEN r_into_rtranclp[of "deriver P"]] app_derivers_app snd_last_chn_step(4) 
          show ?thesis by fastforce
      qed
      from \<beta>\<gamma>_decomp(3) uwx have v_decomp: "v = y @ z @ w @ x" by simp
      note \<beta>\<gamma>_decomp(1)[unfolded \<beta>\<zeta>\<alpha>', symmetric]
      then show thesis
      proof (cases rule: syms_append_cases)
        case (left u' v')
        from \<beta>\<gamma>_decomp less(3) have \<alpha>\<delta>: "\<alpha> = \<delta>" by force
        note \<rho>_def snd_last_chn_step(2) less(3) \<beta>\<zeta>\<alpha>' uwx
        thm less(1)[of "is" \<zeta> X' x "\<alpha>' @ Nt B # map Tm w" \<alpha> X v]
        thm less(1)[of js' \<alpha> X vv]
        thm less(1)[of "is" X'' \<alpha>'' X' \<beta>'' js \<zeta> x X "\<alpha>' @ Nt B # map Tm w" \<alpha> v]
        
        show thesis using less(8) \<alpha>\<delta> v_decomp \<beta>\<gamma>_decomp uwx \<rho>_def sorry
        thm rm_chain_stepE[OF snd_last_chn_step(2)[unfolded is_def]]
        thm less(1)[of \<rho>1 X1 \<alpha>1 B1 \<beta>'1 is1] left less(2-)
        from left snd_last_chn_step(3) have 
          "P \<turnstile> \<delta> @ Nt X # map Tm u' @ Nt X' # map Tm x \<Rightarrow>r \<delta> @ Nt X # map Tm u' @ map Tm v'" sorry
        show ?thesis sorry
      next
        case (right \<eta>)
        with \<beta>\<gamma>_decomp less(6) have \<alpha>\<zeta>\<eta>: "\<alpha> = \<zeta>@\<eta>" by force
        from right snd_last_chn_step(3) have 
          "P \<turnstile> \<zeta> @ Nt X' # map Tm x \<Rightarrow>r \<zeta> @ \<eta> @ Nt X # (map Tm y @ Nt B # \<beta>') @ map Tm x"
          by auto
        moreover have "P \<turnstile> map Tm y @ Nt B # \<beta>' \<Rightarrow>r* map Tm (y @ z @ w)"
          using  B\<beta>'_derivers derivers_prepend map_append by auto
      ultimately show ?thesis using rm_chain.step[OF snd_last_chn_step(2)] less(8) \<alpha>\<zeta>\<eta>
        v_decomp by fastforce
      qed

      then show ?thesis sorry
    qed

  qed



  show ?case 
  proof (cases "Nt X \<in> set \<gamma>")
    case True
    from Suc_steps(2) obtain \<delta> w where"\<gamma> = \<delta> @ Nt X # map Tm w" "w @ u = v" 
      by (metis True syms_decomp_rightmost2)
    with Suc Suc_steps last_chain_step show thesis by force
  next
    case False
    with Suc_steps(2) have X_in_\<beta>: "Nt X \<in> set \<beta>" 
      by (metis Nts_syms_append Nts_syms_map_Tm Un_iff empty_iff in_Nts_syms list.set_intros(1))
    with rm_chain_imp_hd_prod_rightmost[OF last_chain_step] 
    obtain X' \<alpha>' \<beta>' "is" where 
      \<rho>_def: "\<rho> = [X' \<rightarrow> \<alpha>' . Nt B # \<beta>'] # is" 
      using that by cases (auto simp add: Cons_eq_append_conv)

    from this last_chain_step False X_in_\<beta> Suc_steps(2,3) Suc(2) show thesis
    proof (induction "length \<rho>" arbitrary: \<alpha>' \<rho> X' B \<beta>' "is" \<beta> u X \<gamma> \<alpha> v thesis rule: less_induct)
      case less

      note \<rho>_def = less(2)
      note last_chain_step = less(3)
      note False = less(4)
      note X_in_\<beta> = less(5)
      from rm_chain_stepE[OF last_chain_step[unfolded \<rho>_def]] obtain \<zeta> w x where
        snd_last_chn_step: 
        "\<beta> @ Nt B # map Tm u = \<zeta> @ \<alpha>' @ Nt B # map Tm w @ map Tm x"
        "P \<Turnstile> [Nt A] \<Rightarrow>r* is \<Rightarrow>r* \<zeta> @ Nt X' # map Tm x"
        "P \<turnstile> \<zeta> @ Nt X' # map Tm x \<Rightarrow>r \<zeta> @ \<alpha>' @ Nt B # \<beta>' @ map Tm x"
        "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm w"
        by metis
      from right_derivs_eq_imp_eq_tl this(1) have uwx: "u = w @ x" 
        by (metis append.assoc map_append)
      with snd_last_chn_step(1) have \<beta>\<zeta>\<alpha>': "\<beta> = \<zeta> @ \<alpha>'"
        by simp
      from syms_decomp_rightmost[OF _ X_in_\<beta> False, of \<alpha> v "[]" u] obtain \<delta> y z where
        \<beta>\<gamma>_decomp: "\<beta> = \<delta> @ Nt X # map Tm y" "\<gamma> = map Tm z" "v = y @ z @ u"
        using less(6) by auto
      have B\<beta>'_derivers: "P \<turnstile> Nt B # \<beta>' \<Rightarrow>r* map Tm z @ map Tm w" 
      proof -
        have "P \<turnstile> [Nt B] \<Rightarrow>r map Tm z" using deriver_singleton deriver_imp_in_Prods[OF less(7)] 
          \<beta>\<gamma>_decomp by fast
        from this[THEN r_into_rtranclp[of "deriver P"]] app_derivers_app snd_last_chn_step(4) show ?thesis
          by fastforce
      qed
      from \<beta>\<gamma>_decomp(3) uwx have v_decomp: "v = y @ z @ w @ x" by simp
      note \<beta>\<gamma>_decomp(1)[unfolded \<beta>\<zeta>\<alpha>', symmetric]
      then show thesis
      proof (cases rule: syms_append_cases)
        case (left u' v')
        from \<beta>\<gamma>_decomp less(6) have \<alpha>\<delta>: "\<alpha> = \<delta>" by force
        from rm_chain_imp_hd_prod_rightmost[OF snd_last_chn_step(2)] 
        obtain X'' \<alpha>'' \<beta>'' js where is_def:
          "is = [X'' \<rightarrow> \<alpha>'' . Nt X' # \<beta>''] # js"
          using left by cases simp+
        moreover have "P \<Turnstile> [Nt A] \<Rightarrow>r* is \<Rightarrow>r* \<zeta> @ Nt X' # map Tm v" sorry
        moreover from left have "Nt X \<in> set \<zeta>" "Nt X \<notin> set \<alpha>'"
          by auto
        thm less(1)[of "is" X'' \<alpha>'' X' \<beta>'' js \<zeta> x X "\<alpha>' @ Nt B # map Tm w" \<alpha> v]
        
        show thesis using less(8) \<alpha>\<delta> v_decomp \<beta>\<gamma>_decomp uwx \<rho>_def sorry
        thm rm_chain_stepE[OF snd_last_chn_step(2)[unfolded is_def]]
        thm less(1)[of \<rho>1 X1 \<alpha>1 B1 \<beta>'1 is1] left less(2-)
        from left snd_last_chn_step(3) have 
          "P \<turnstile> \<delta> @ Nt X # map Tm u' @ Nt X' # map Tm x \<Rightarrow>r \<delta> @ Nt X # map Tm u' @ map Tm v'" sorry
        show ?thesis sorry
      next
        case (right \<eta>)
        with \<beta>\<gamma>_decomp less(6) have \<alpha>\<zeta>\<eta>: "\<alpha> = \<zeta>@\<eta>" by force
        from right snd_last_chn_step(3) have 
          "P \<turnstile> \<zeta> @ Nt X' # map Tm x \<Rightarrow>r \<zeta> @ \<eta> @ Nt X # (map Tm y @ Nt B # \<beta>') @ map Tm x"
          by auto
        moreover have "P \<turnstile> map Tm y @ Nt B # \<beta>' \<Rightarrow>r* map Tm (y @ z @ w)"
          using  B\<beta>'_derivers derivers_prepend map_append by auto
      ultimately show ?thesis using rm_chain.step[OF snd_last_chn_step(2)] less(8) \<alpha>\<zeta>\<eta>
        v_decomp by fastforce
      qed



      then show ?case sorry
    qed



    from rm_chain_stepE[OF last_chain_step[unfolded \<rho>_def(1)]] obtain \<zeta> w x where
      snd_last_chn_step: 
      "\<beta> @ Nt B # map Tm u = \<zeta> @ \<alpha>' @ Nt B # map Tm w @ map Tm x"
      "P \<Turnstile> [Nt A] \<Rightarrow>r* is \<Rightarrow>r* \<zeta> @ Nt X' # map Tm x"
      "P \<turnstile> \<zeta> @ Nt X' # map Tm x \<Rightarrow>r \<zeta> @ \<alpha>' @ Nt B # \<beta>' @ map Tm x"
      "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm w"
      by metis
    from right_derivs_eq_imp_eq_tl this(1) have uwx: "u = w @ x" 
      by (metis append.assoc map_append)
    with snd_last_chn_step(1) have \<beta>\<zeta>\<alpha>': "\<beta> = \<zeta> @ \<alpha>'"
      by simp
    from syms_decomp_rightmost[OF _ X_in_\<beta> False, of \<alpha> v "[]" u] obtain \<delta> y z where
      \<beta>\<gamma>_decomp: "\<beta> = \<delta> @ Nt X # map Tm y" "\<gamma> = map Tm z" "v = y @ z @ u"
      using Suc_steps(2) by auto

    have B\<beta>'_derivers: "P \<turnstile> Nt B # \<beta>' \<Rightarrow>r* map Tm z @ map Tm w" 
    proof -
      have "P \<turnstile> [Nt B] \<Rightarrow>r map Tm z" using deriver_singleton deriver_imp_in_Prods[OF Suc_steps(3)] 
        \<beta>\<gamma>_decomp by fast
      from this[THEN r_into_rtranclp[of "deriver P"]] app_derivers_app snd_last_chn_step(4) show ?thesis
        by fastforce
    qed
    from \<beta>\<gamma>_decomp(3) uwx have v_decomp: "v = y @ z @ w @ x" by simp

    note \<beta>\<gamma>_decomp(1)[unfolded \<beta>\<zeta>\<alpha>', symmetric]
    then show thesis
    proof (cases rule: syms_append_cases)
      case (left u' v')
      from \<beta>\<gamma>_decomp Suc_steps(2) have "\<alpha> = \<delta>" by force
      from rm_chain_imp_hd_prod_rightmost[OF snd_last_chn_step(2)] 
      obtain X'' \<alpha>'' \<beta>'' js where is_def:
        "is = [X'' \<rightarrow> \<alpha>'' . Nt X' # \<beta>''] # js"
        using left by cases simp+
      thm rm_chain_stepE[OF snd_last_chn_step(2)[unfolded is_def]]
      from left snd_last_chn_step(3) have 
        "P \<turnstile> \<delta> @ Nt X # map Tm u' @ Nt X' # map Tm x \<Rightarrow>r \<delta> @ Nt X # map Tm u' @ map Tm v'"
        thm left rm_chain.step[of P "[Nt A]" "is" \<delta> X vv] Suc(2)
      then show ?thesis sorry
    next
      case (right \<eta>)
      with \<beta>\<gamma>_decomp Suc_steps(2) have \<alpha>\<zeta>\<eta>: "\<alpha> = \<zeta>@\<eta>" by force
      from right snd_last_chn_step(3) have 
        "P \<turnstile> \<zeta> @ Nt X' # map Tm x \<Rightarrow>r \<zeta> @ \<eta> @ Nt X # (map Tm y @ Nt B # \<beta>') @ map Tm x"
        by auto
      moreover have "P \<turnstile> map Tm y @ Nt B # \<beta>' \<Rightarrow>r* map Tm (y @ z @ w)"
        using  B\<beta>'_derivers derivers_prepend map_append by auto
    ultimately show ?thesis using rm_chain.step[OF snd_last_chn_step(2)] Suc(2) \<alpha>\<zeta>\<eta>
      v_decomp by fastforce
    qed
      


    from snd_last_chn_step(3) have 
      "P \<turnstile> \<zeta> @ Nt X' # map Tm x \<Rightarrow>r \<delta> @ Nt X # (map Tm y @ Nt B # \<beta>') @ map Tm x"
      using \<beta>\<zeta>\<alpha>' \<beta>\<gamma>_decomp(1) append.assoc by (metis append_Cons)
    moreover have "P \<turnstile> map Tm y @ Nt B # \<beta>' \<Rightarrow>r* map Tm (y @ z @ w)"
      using derivers_prepend[OF B\<beta>'_derivers] map_append by simp

    (* prove that B derives tms. Prove that those tms @ u = v ( Use syms_decomp_rightmost )
       Go one step back (the step that produces B), and "sneak" everything to the right of X into \<beta>. 
       Then derive replace [X' \<rightarrow> \<alpha>' . Nt B # \<beta>'] with [X' \<rightarrow> \<alpha>'' . Nt X # as @ Nt B # \<beta>']
       on top of is. as must be Tms and B derives tms, and \<alpha>' = \<alpha>'' @ Nt X # as. 
      

*)

    then show ?thesis sorry
  qed
qed
  

 (* lemma derivers_decomp_gen:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<gamma> @ Nt B # \<delta>"
  obtains X \<alpha> \<alpha>' \<beta> \<beta>' v where
    "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha>@Nt X#\<beta>"
    "P \<turnstile> \<alpha>@Nt X#\<beta> \<Rightarrow>r* \<alpha>@Nt X#map Tm v"
    "P \<turnstile> \<alpha>@Nt X#map Tm v \<Rightarrow>r \<alpha>@\<alpha>'@Nt B#\<beta>'@map Tm v"
    "\<gamma> = \<alpha>@\<alpha>'" "\<delta> = \<beta>' @ map Tm v"
  using assms proof (induction "length \<gamma>" arbitrary: \<gamma> B \<delta> thesis rule: less_induct)
  case less
  from derivers_Nt_imp_last_produced obtain C \<alpha> \<beta> \<gamma>' v where 
    "P \<turnstile> [Nt A] \<Rightarrow>r* \<gamma>' @ Nt C # map Tm v"
    "P \<turnstile> \<gamma>' @ Nt C # map Tm v \<Rightarrow>r \<gamma>' @ \<alpha> @ Nt B # \<beta> @ map Tm v"
    "P \<turnstile> \<gamma>' @ \<alpha> @ Nt B # \<beta> @ map Tm v \<Rightarrow>r* \<gamma> @ Nt B # \<delta>" 
    "Nt B \<notin> set \<beta>"
    using less(3) 
  then show ?case oops


lemma derivers_decomp:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<gamma>' @ Nt B # map Tm w"
    "P = Prods G''"
    "reduced G''"
    "LangS G'' \<noteq> {}"
  obtains X \<alpha> \<alpha>' \<beta> v v' where
    "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha>@Nt X#map Tm v"
    "P \<turnstile> \<alpha>@Nt X#map Tm v \<Rightarrow>r \<alpha>@\<alpha>'@Nt B#\<beta>@map Tm v"
    "P \<turnstile> \<alpha>@\<alpha>'@Nt B#\<beta>@map Tm v \<Rightarrow>r* \<alpha>@\<alpha>'@ Nt B#map Tm (v'@v)" 
    "\<gamma>' = \<alpha>@\<alpha>'" "w = v'@v"
proof -
  from derivers_Nt_imp_last_produced obtain C \<alpha> \<beta> \<delta> v where B_prod:
    "P \<turnstile> [Nt A] \<Rightarrow>r* \<delta> @ Nt C # map Tm v"
    "P \<turnstile> \<delta> @ Nt C # map Tm v \<Rightarrow>r \<delta> @ \<alpha> @ Nt B # \<beta> @ map Tm v"
    "P \<turnstile> \<delta> @ \<alpha> @ Nt B # \<beta> @ map Tm v \<Rightarrow>r* \<gamma>' @ Nt B # map Tm w" 
    "Nt B \<notin> set \<beta>" using assms(1,2) by (smt (verit, ccfv_SIG) in_set_conv_decomp)
  from B_prod(3,1,2,4) that assms(1,2) show ?thesis
  proof (induction  "\<delta> @ \<alpha> @ Nt B # \<beta> @ map Tm v" arbitrary: thesis \<delta> \<alpha> \<beta> v C rule: converse_rtranclp_induct)
    case base
    from base(1,4) have "\<gamma>' = \<delta>@\<alpha>" "map Tm w = \<beta> @ map Tm v"
    proof -
      from base(4) have "Nt B \<notin> set \<beta> \<union> set (map Tm v)" "Nt B \<notin> set (map Tm w)"
        using sym.exhaust by auto
      with x_notin_tl_imp_eq base(1) show "\<gamma>' = \<delta>@\<alpha>" "map Tm w = \<beta> @ map Tm v" 
        by (metis append.assoc set_append)+
    qed
    then show ?case using base(5)[of \<delta> C "map Tm v" v \<alpha> \<beta>] base(1-4)
sorry
  next
    case (step z)
    then obtain \<zeta> D u where z_def: "z = \<zeta> @ Nt D # map Tm u" using deriver.cases 
      by (metis converse_rtranclpE)
    from step(1)[unfolded z_def] show thesis sorry
  qed
qed













    case base
    from base(1,4) have "\<gamma>' = \<delta>@\<alpha>" "map Tm w = \<beta> @ map Tm v"
    proof -
      from base(4) have "Nt B \<notin> set \<beta> \<union> set (map Tm v)" "Nt B \<notin> set (map Tm w)"
        using sym.exhaust by auto
      with x_notin_tl_imp_eq base(1) show "\<gamma>' = \<delta>@\<alpha>" "map Tm w = \<beta> @ map Tm v" 
        by (metis append.assoc set_append)+
    qed
    then show ?case using base(5)[of \<delta> C "map Tm v" v \<alpha> \<beta>] base(1-4)
      by (metis rtranclp.simps syms_split_last_eq_imp_tl_eq)
  next
    case (step y)
    from step(2) consider
      \<eta> u where "y = \<eta> @ Nt B # map Tm u" |
      \<eta> C u
    then show ?case sorry
  qed
qed
    



  using assms(1,2) proof (induction "length \<gamma>'" arbitrary: \<gamma>' B w thesis rule: less_induct)





  using assms(1,2) proof (induction "\<gamma>' @ Nt B # map Tm w" arbitrary: \<gamma>' B w thesis)
  case (step \<delta>)
  obtain \<alpha> C x \<beta> where \<delta>_prod: "\<delta> = \<alpha> @ Nt C # map Tm x" "(C,\<beta>) \<in> P"
    "\<alpha> @ \<beta> @ map Tm x = \<gamma>' @ Nt B # map Tm w" 
    using deriver.cases[OF step(2)] by metis
  then show ?case 
  proof (cases "Nt B \<in> set \<beta>")
    case True
    from \<delta>_prod syms_decomp_rightmost2[OF _ True] obtain \<zeta> u where "\<beta> = \<zeta> @ Nt B # map Tm u"
      "w = u@x" by metis
    then show ?thesis using step(4)[of \<alpha> C "map Tm x" x \<zeta> "map Tm u"] \<delta>_prod step(1-3,5)
      by (smt (verit) append.assoc append_Cons append_eq_append_conv length_Cons length_append 
          length_map relpowp_imp_rtranclp rtranclp.rtrancl_refl)
  next
    case False
    with \<delta>_prod have "Nt B \<in> set \<alpha>" 
      by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral 
          in_Nts_syms list.set_intros(1))
    from syms_decomp_rightmost[OF _ this False, of _ _ "[]" x] \<delta>_prod(3)
    obtain \<zeta> u v where \<alpha>_decomp: "\<alpha> = \<zeta> @ Nt B # map Tm u" "\<beta> = map Tm v" "w = u@v@x" 
      by (metis self_append_conv2)
    hence \<delta>B_def: "\<delta> = \<zeta> @ Nt B # map Tm u @ Nt C # map Tm x" using \<delta>_prod by simp
    from derivers_Nt_imp_produced[OF step(1) _ this] obtain X \<alpha>' \<beta>' \<eta> y where
      "P \<turnstile> [Nt A] \<Rightarrow>r* \<eta> @ Nt X # map Tm y" "P \<turnstile> \<eta> @ Nt X # map Tm y \<Rightarrow>r \<eta> @ \<alpha>' @ Nt B # \<beta>' @ map Tm y"
      "P \<turnstile> \<eta> @ \<alpha>' @ Nt B # \<beta>' @ map Tm y \<Rightarrow>r* \<delta>" by (metis Un_iff \<delta>_prod(1) \<open>Nt B \<in> set \<alpha>\<close> set_append)
    then show ?thesis sorry




  then show ?case proof (induction n arbitrary: \<delta> \<gamma>' B w rule: less_induct)
    case (less n)
    then show ?case
    proof (cases n)
      case 0
      with less have "P \<turnstile> [Nt A] \<Rightarrow>r \<gamma>' @ Nt B # map Tm w" by simp
      then show ?thesis using less(5)[of "[]" A "[]" "[]"] by auto
    next
      case (Suc m)
      obtain \<alpha> C x \<beta> where \<delta>_prod: "\<delta> = \<alpha> @ Nt C # map Tm x" "(C,\<beta>) \<in> P"
        "\<alpha> @ \<beta> @ map Tm x = \<gamma>' @ Nt B # map Tm w" 
        using deriver.cases[OF less(3)] by metis
      then show ?thesis 
      proof (cases "Nt B \<in> set \<beta>")
        case True
        from \<delta>_prod syms_decomp_rightmost2[OF _ True] obtain \<zeta> u where "\<beta> = \<zeta> @ Nt B # map Tm u"
          "w = u@x" by metis
        then show ?thesis using less(5)[of \<alpha> C "map Tm x" x \<zeta> "map Tm u"] \<delta>_prod less(1-4,6)
          by (metis (no_types, lifting) ext append.assoc append_Cons append_same_eq map_append 
              rtranclp.simps rtranclp_power) 
      next
        case False
        with \<delta>_prod have "Nt B \<in> set \<alpha>" 
          by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral 
              in_Nts_syms list.set_intros(1))
        from syms_decomp_rightmost[OF _ this False, of _ _ "[]" x] \<delta>_prod(3)
        obtain \<zeta> u v where \<alpha>_decomp: "\<alpha> = \<zeta> @ Nt B # map Tm u" "\<beta> = map Tm v" "w = u@v@x" 
          by (metis self_append_conv2)
        hence \<delta>B_def: "\<delta> = \<zeta> @ Nt B # map Tm u @ Nt C # map Tm x" using \<delta>_prod by simp
        with derivers_Nt_imp_produced[OF step]
        then show ?thesis sorry
      qed
    qed
  qed
qed satx


  using assms(1,2) proof (induction "\<gamma>' @ Nt B # map Tm w" arbitrary: \<gamma>' B w thesis 
                          rule: rtranclp_induct)
  case (step \<delta>)
  show ?case
  proof (cases "[Nt A] = \<delta>", goal_cases single_step steps)
    case single_step
    then show ?case using step
      by (metis append.right_neutral append_Nil list.simps(8) rtranclp.rtrancl_refl)
  next
    case steps
    moreover from step(2) obtain C \<zeta> u \<eta> where \<delta>_prod: "\<delta> = \<zeta> @ Nt C # map Tm u" "(C, \<eta>) \<in> P" 
      "\<zeta>@\<eta>@map Tm u = \<gamma>'@Nt B # map Tm w"
      using deriver.cases by metis
    ultimately show thesis using derive_imp_derive_Nt[OF step(1,2)] step(3,4) steps 
      by (metis assms(3-))
  qed
qed simp

lemma rtranclp_step_imp_Suc:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>"
    "P \<turnstile> \<beta> \<Rightarrow>r \<gamma>"
  obtains n where "P \<turnstile> \<alpha> \<Rightarrow>r(Suc n) \<gamma>"
  using rtranclp_imp_relpowp[OF assms(1)] assms(2) by auto


lemma converse_rtranclp_step_imp_Suc:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r \<beta>"
    "P \<turnstile> \<beta> \<Rightarrow>r* \<gamma>"
  obtains n where "P \<turnstile> \<alpha> \<Rightarrow>r(Suc n) \<gamma>"
proof -
  from assms(1) have "P \<turnstile> \<alpha> \<Rightarrow>r(Suc 0) \<beta>" by auto
  also from rtranclp_imp_relpowp[OF assms(2)] obtain n where "P \<turnstile> \<beta> \<Rightarrow>r(n) \<gamma>" by blast
  finally show thesis using that by simp
qed



    (* New approach: we show that A must be in the stack, reachable by X as seen above. 
       Be more precise to show that w' is actually u@v@w. with \<alpha> \<Rightarrow>* u. After one \<epsilon> transition, IH
      can be used
      Problem: proving hist \<rho> = \<gamma>' 

      Previous approach: induct over n steps. Problem: last step does not produce A in general
      Possibly: induct over n steps with weak induction obtaining X and m where
        S' \<Rightarrow>r(m) \<gamma>Xu \<Rightarrow>r \<gamma>\<delta>A\<zeta>u \<Rightarrow>r* \<gamma>'Aw with m < n *)
*)
lemma deriver_imp_IPDA_comp:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>'@Nt A#map Tm w"
    "Prods G' \<turnstile> \<gamma>'@Nt A#map Tm w \<Rightarrow>r \<gamma>'@\<alpha>@\<beta>@map Tm w"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  obtains \<rho> where 
    "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>@[init_symbol IPDA], v@w) \<turnstile>P* ([I.final_state, init_symbol IPDA], [])" 
    "hist \<rho> = \<gamma>'"
  sorry



(*
  using assms(1) proof cases
  case rtrancl_refl
  then have step: "\<gamma>' = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S]"
    using assms(2) S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
  then show ?thesis 
    by (metis I.hist_init I.init_symbol_ipda append.right_neutral append_Nil assms(3)
        derivers_S_append_imp_comp hist_singleton local.rtrancl_refl map_Tm_Nt_eq_map_Tm_Nt that)
next
  case (rtrancl_into_rtrancl b)
  then obtain n where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<gamma>' @ Nt A # map Tm w"
    using rtranclp_step_imp_Suc by blast
  from derivers_decomp[OF this _ G'_reduced G'_not_empty] obtain X \<alpha>' \<gamma> \<beta>' u v' where decomp:
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt X # map Tm v'" 
    "Prods G' \<turnstile> \<gamma> @ Nt X # map Tm v' \<Rightarrow>r \<gamma> @ \<alpha>' @ Nt A # \<beta>' @ map Tm v'"
    "Prods G' \<turnstile> \<gamma> @ \<alpha>' @ Nt A # \<beta>' @ map Tm v' \<Rightarrow>r* \<gamma> @ \<alpha>' @ Nt A # map Tm (u@v')"
    "u@v' = w" "\<gamma> @ \<alpha>' = \<gamma>'" by metis
  then obtain \<rho> "is" where "\<rho> = [X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # is" by blast  
  with decomp show ?thesis 
  proof (induction "is" arbitrary: X \<alpha>' A \<beta>')
    case Nil
    then show ?case sorry
  next
    case (Cons a "is")
    then show ?case sorry
  qed
qed







  using assms proof (induction "\<gamma>'@Nt A#map Tm w" arbitrary: \<gamma>' A w \<alpha> \<beta> v thesis rule: rtranclp_induct)
  case base
  then have "\<gamma>' = [] \<and> w = []" "\<alpha>@\<beta> = [Nt S]"
    by (simp add: Cons_eq_append_conv,
        metis (no_types, opaque_lifting) S'_derive_imp_S append_Nil2 derive_singleton 
        deriver_singleton list.exhaust list.simps(3) Cons_eq_append_conv)
  then show ?case using base unfolding hist_defs
    by (metis append.left_neutral append.right_neutral concat.simps(1) derivers_S_append_imp_comp 
        list.inject list.simps(8) sym.inject(1))
next
  case (step \<gamma>)
  then obtain as where \<alpha>_derivers: "Prods G' \<turnstile> \<alpha> \<Rightarrow>r* map Tm as"
    using reduced_derived_substring_imp_derives[OF _ G'_reduced G'_not_empty] G'_def 
    by (metis (no_types, lifting) Cfg.sel(2) derivers_iff_derives derivers_imp_derives
        rtranclp.rtrancl_into_rtrancl)
  obtain X \<delta> u where \<gamma>_def: "\<gamma> = \<delta> @ Nt X#map Tm u"
    using step(2) by (meson deriver.cases)
  then obtain xs ys where xy_defs: "(X, xs@ys) \<in> Prods G'" "\<delta>@xs@ys@map Tm u = \<gamma>'@Nt A#map Tm w"
    using step deriver_imp_handle by (metis self_append_conv2)
  with step obtain v' where ys_derivers: "Prods G' \<turnstile> ys \<Rightarrow>r* map Tm v'"
    using reduced_derived_substring_imp_derives[OF _ G'_reduced G'_not_empty] G'_def \<gamma>_def 
    by (metis (no_types, lifting) Cfg.sel(2) append.assoc derivers_iff_derives derivers_imp_derives
        rtranclp.rtrancl_into_rtrancl)
  with step(2,3) obtain \<rho> where last_chain_step:
    "([X \<rightarrow> xs . ys]#\<rho>@[init_symbol IPDA], v'@u) \<turnstile>P* ([final_state, init_symbol IPDA],[])"
    "hist \<rho> = \<delta>"
    using \<gamma>_def xy_defs by metis
  with reaches_final_imp_compl_final have X_compl_final:
    "([X \<rightarrow> xs@ys . []]#\<rho>@[init_symbol IPDA], u) \<turnstile>P* ([final_state, init_symbol IPDA],[])"
    using ys_derivers derivers_imp_derives sorry
  obtain Y ws zs \<rho>l \<rho>r where Y_defs:
    "\<rho> = \<rho>l@[Y \<rightarrow> ws . Nt A#zs]#\<rho>r" 
    "([X \<rightarrow> xs@ys . []]#\<rho>@[init_symbol IPDA], u) \<turnstile>P* (([Y \<rightarrow> ws . Nt A#zs]#\<rho>r)@[init_symbol IPDA], as@v@w)"
    "(([Y \<rightarrow> ws . Nt A#zs]#\<rho>r)@[init_symbol IPDA], as@v@w) \<turnstile>P* ([final_state, init_symbol IPDA],[])"
  proof -
    from xy_defs(2) \<gamma>_def step(2) have 2: 
      "Prods G' \<turnstile> \<delta> @ Nt X # map Tm u \<Rightarrow>r \<delta> @ (xs @ ys) @ map Tm u" by auto
     have 3: "Prods G' \<turnstile> \<alpha>@\<beta> \<Rightarrow>r* map Tm (as @ v)"
       using \<alpha>_derivers step(6) by (meson derivers_iff_derives derives_append_map_Tm)
     show thesis using that derivers_imp_in_stack[OF _ 2 _ _ 3 X_compl_final] xy_defs(2) 
       by (metis (no_types, lifting) \<gamma>_def append.assoc append.simps(2) step.hyps(1) step.prems(2))
   qed
   let ?\<rho>' = "[Y \<rightarrow> ws . Nt A#zs]#\<rho>r"
  note Y_defs(2)
  also have Y_step: 
    "(?\<rho>'@[init_symbol IPDA], as@v@w) \<turnstile>P ([A \<rightarrow> [] . \<alpha>@\<beta>]#?\<rho>'@[init_symbol IPDA], as@v@w)"
    using expanding deriver_imp_in_Prods step(5) 
    by (metis (no_types, lifting) append.assoc append_Cons)
  also with derivers_imp_completes have A_init_steps:
    "... \<turnstile>P* ([A \<rightarrow> \<alpha> . \<beta>]#?\<rho>'@[init_symbol IPDA], v@w)"
    using \<alpha>_derivers by (metis append_Nil rtranclp_power)
  finally have ex_comp: "... \<turnstile>P* ([final_state, init_symbol IPDA], [])"
    using X_compl_final  sorry
  moreover have "hist ?\<rho>' = \<gamma>'" 
  proof -
    from Y_defs(2) Y_step A_init_steps 
    derivers_imp_completes rtranclp_imp_relpowp step(6)
    have "([X \<rightarrow> xs @ ys . []]#\<rho>@[init_symbol IPDA], u) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []]#?\<rho>'@[init_symbol IPDA],w)"
      using rtranclp_trans 
      by (smt (verit, ccfv_threshold) append.right_neutral rtranclp.rtrancl_into_rtrancl)
    with \<gamma>_def step(2) xy_defs(2) X_compl_final show ?thesis using last_chain_step(2) sorry
  qed
  ultimately show ?case using step(4) by presburger
qed





    (* Does not hold in general. Strong induction needed instead *)
    obtain \<delta>' u' where X_prod: "(X, \<delta>'@Nt A#map Tm u') \<in> Prods G'" "\<gamma>' = \<delta>@\<delta>'" 
      "map Tm (u'@u) = map Tm w"
      using deriver_decomp[OF n_steps(2)] by blast
    from reduced_derived_substring_imp_derives[OF _ G'_reduced G'_not_empty] 
    Suc.prems(4) obtain v' where A_derives: "Prods G' \<turnstile> [Nt A] \<Rightarrow>r* map Tm v'"
     by (metis (no_types, opaque_lifting) append_Cons append_self_conv2
        derivern_imp_deriven derivers_iff_derives rtranclp_power)
    hence A_Cons_derivers: "Prods G' \<turnstile> Nt A#map Tm u' \<Rightarrow>r* map Tm (v'@u')" 
      using derives_append derivers_iff_derives by (metis append_Cons append_Nil map_append)
    from Suc(1)[OF _ this _ n_steps(1)] obtain \<rho> where last_chain_step:
      "([X \<rightarrow> \<delta>' . Nt A#map Tm u'] # \<rho> @ [init_symbol IPDA], v' @ u' @ u) \<turnstile>P* (?qf, [])"
      "hist \<rho> = \<delta>"
      using n_steps(2) X_prod(2,3) append_assoc by (metis append_Cons map_Tm_inject_iff map_append)
    hence Xw_final: "([X \<rightarrow> \<delta>' @ [Nt A] . map Tm u'] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* (?qf, [])"
      using derives_imp_complete_reaches_final Suc(3) derivers_iff_derives 
      by (metis A_derives X_prod(3) append_Cons append_Nil map_Tm_inject_iff) 
    let ?\<rho>' = "[X \<rightarrow> \<delta>' . Nt A#map Tm u'] # \<rho>"
    have \<rho>'_hist: "hist ?\<rho>' = \<gamma>'" using last_chain_step(2) X_prod(2) by (simp add: history_def)
    have "([A \<rightarrow> \<alpha> . \<beta>] # ?\<rho>' @ [init_symbol IPDA], v@w) 
      \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []]# ?\<rho>' @ [init_symbol IPDA], w)" 
      using derives_imp_completes derivers_iff_derives Suc(3) 
      by (metis append.right_neutral)
    also have "... \<turnstile>P ([X \<rightarrow> \<delta>' @ [Nt A] . map Tm u'] # \<rho> @ [init_symbol IPDA], w)"
      using LR_Parser.IPDA.reducing[OF ipda] by simp
    also note Xw_final
    finally show thesis using Suc(4)[OF _ \<rho>'_hist] by presburger
  qed *)


end

end
