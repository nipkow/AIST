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
  sorry 

*)



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
  oops
(*proof -
  obtain xs where xs_def: "\<gamma> @ Nt A # map Tm w = \<alpha> @ xs @ map Tm u" "(X, xs) \<in> P" 
    using deriver_impl_in_Prods[OF assms] by metis
  moreover have "length w \<ge> length u" using assms sorry
  ultimately obtain zs :: "('a,'b) syms" where zs_def: "zs @ map Tm u = map Tm w" 
    using eq_tl_impl_substring[of "map Tm u" "map Tm w"] 
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


lemma derivers_S_append_impl_comp:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm w"
    "\<alpha>@\<beta> = [Nt S]"
  shows "([[S' \<rightarrow> \<alpha> . \<beta>], init_symbol IPDA], w) \<turnstile>P* ([I.final_state, init_symbol IPDA], [])"
proof -
  from assms consider "\<alpha> = [Nt S] \<and> \<beta> = []" | (init) "\<alpha> = [] \<and> \<beta> = [Nt S]"
    using append_eq_Cons_conv by fastforce
  then show ?thesis
  proof cases
    case init
    with assms(1) have "w \<in> LangS G'" using G'_derives_from_S_impl_in_Lang
      by (simp add: derivers_imp_derives)
    then show ?thesis using I.Lang_eq_Lang_G Lang_preserved I.init_state_ipda init 
      unfolding I.Lang_def by auto
  qed (use assms(1) derivers_imp_derives in force)
qed

lemma derivers_impl_in_stack:
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
lemma deriver_impl_ex_hist:
  assumes 
    "Prods G' \<turnstile> \<gamma>@Nt A#map Tm u \<Rightarrow>r* \<delta>@Nt B#map Tm v"
obtains \<rho> \<sigma> where     
    "([A \<rightarrow> \<alpha> . []]#\<rho>@[init_symbol IPDA], u) \<turnstile>P* ([B \<rightarrow> \<beta> . []]#\<sigma>@[init_symbol IPDA], v)"
    "hist \<rho> = \<gamma>"
    "hist \<sigma> = \<delta>"
  oops




lemma last_Nt:
  assumes "\<alpha>@\<beta>@\<gamma>@map Tm u = \<delta>@Nt A#map Tm v"
    "Nt A \<in> set \<beta>"
    "Nt A \<notin> set \<gamma>"
  obtains \<zeta> w x where "\<beta> = \<zeta> @ Nt A # map Tm w" "\<gamma> = map Tm x"
  sorry

lemma derivers_append_map_Tm:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@map Tm v \<Rightarrow>r* u @ map Tm v"
  using assms by (simp add: derivern_append_map_Tm rtranclp_power)


lemma derivers_prepend:
  assumes "P \<turnstile> \<beta> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@\<beta> \<Rightarrow>r* \<alpha> @ u"
  using assms derivern_prepend rtranclp_power by (smt (verit))+


 
lemma deriver_decomp:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r* \<gamma>' @ Nt B # map Tm w"
    "[Nt A] \<noteq> \<gamma>' @ Nt B # map Tm w"
    "P = Prods G''"
    "reduced G''"
    "LangS G'' \<noteq> {}"
  obtains X \<alpha> \<alpha>' \<beta> \<beta>' v v' where
    "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha>@Nt X#\<beta>"
    "P \<turnstile> \<alpha>@Nt X#\<beta> \<Rightarrow>r* \<alpha>@Nt X#map Tm v"
    "P \<turnstile> \<alpha>@Nt X#map Tm v \<Rightarrow>r \<alpha>@\<alpha>'@Nt B#\<beta>'@map Tm v"
    "P \<turnstile> \<alpha>@\<alpha>'@Nt B#\<beta>'@map Tm v \<Rightarrow>r* \<alpha>@\<alpha>'@ Nt B#map Tm (v'@v)" 
    "\<gamma>' = \<alpha>@\<alpha>'" "w = v'@v"
  using assms(1,2) proof (induction "\<gamma>' @ Nt B # map Tm w" arbitrary: \<gamma>' B w thesis rule: rtranclp_induct)
  case (step \<delta>)
  show ?case
  proof (cases "[Nt A] = \<delta>", goal_cases single_step steps)
    case single_step
    then show ?case using step
      by (metis append.right_neutral append_Nil list.simps(8) rtranclp.rtrancl_refl)
  next
    case steps
    from step(2) obtain C \<zeta> u \<eta> where \<delta>_prod: "\<delta> = \<zeta> @ Nt C # map Tm u" "(C, \<eta>) \<in> P" 
      "\<zeta>@\<eta>@map Tm u = \<gamma>'@Nt B # map Tm w"
      using deriver.cases by metis
    from step(3)[OF \<delta>_prod(1) _ steps[unfolded this(1)]] obtain \<alpha> X \<beta> v \<alpha>' \<beta>' v' where \<delta>_decomp:
      "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha>@Nt X#\<beta>" "P \<turnstile> \<alpha>@Nt X#\<beta> \<Rightarrow>r* \<alpha>@Nt X#map Tm v" 
      "P \<turnstile> \<alpha>@Nt X#map Tm v \<Rightarrow>r \<alpha>@\<alpha>'@Nt C#\<beta>'@map Tm v" 
      "P \<turnstile> \<alpha>@\<alpha>'@Nt C#\<beta>'@map Tm v \<Rightarrow>r* \<alpha>@\<alpha>'@Nt C#map Tm (v'@v)" 
      "\<zeta> = \<alpha>@\<alpha>'" "u = v'@v" using assms(3-) by blast
    note aux = step(4)[of \<zeta> C "\<beta>'@map Tm v" "v'@v"] 


    from  \<delta>_prod(3) consider "Nt B \<in> set \<eta>" | "Nt B \<in> set \<zeta> \<and> Nt B \<notin> set \<eta>"
      by (metis Nts_syms_Nil Nts_syms_append Nts_syms_map_Tm Un_iff append.right_neutral in_Nts_syms
          list.set_intros(1))
    then show ?case proof cases
      case 1
      then obtain \<theta> \<iota> where \<eta>_decomp: "\<theta> @ Nt B # \<iota> = \<eta>" "Nt B \<notin> set \<iota>"
        by (metis split_list_last)
      with \<delta>_prod have \<iota>_is_Tms: "\<iota> @ map Tm u = map Tm w"
        sorry
      moreover then obtain x where \<iota>_def: "\<iota> = map Tm x" 
        by (metis append_eq_map_conv)
      moreover from \<delta>_decomp have "P \<turnstile> [Nt A] \<Rightarrow>r* \<zeta> @ Nt C # \<beta>' @ map Tm v" 
         "P \<turnstile> \<zeta> @ Nt C # \<beta>' @ map Tm v \<Rightarrow>r* \<zeta> @ Nt C # map Tm (v' @ v)"
         "P \<turnstile> \<zeta> @ Nt C # map Tm (v' @ v) \<Rightarrow>r \<zeta> @ \<theta> @ Nt B # \<iota> @ map Tm (v' @ v)"
         "P \<turnstile> \<zeta> @ \<theta> @ Nt B # \<iota> @ map Tm (v' @ v) \<Rightarrow>r* \<zeta> @ \<theta> @ Nt B # map Tm (x @ v' @ v)"
          apply simp
        using \<delta>_decomp apply simp
        using \<delta>_prod \<eta>_decomp deriver.cases 
         \<delta>_decomp(6) step.hyps(2) apply force
        using \<iota>_def by simp
      moreover have "\<gamma>' = \<zeta> @ \<theta>" using \<delta>_prod(3) \<eta>_decomp \<iota>_is_Tms 
        by fastforce
      ultimately show ?thesis using \<delta>_decomp 
        by (metis (mono_tags, lifting) map_Tm_inject_iff map_append step.prems(1)) 
    next
      case 2
      then show ?thesis sorry
    qed
  qed
qed simp


    (* New approach: we show that A must be in the stack, reachable by X as seen above. 
       Be more precise to show that w' is actually u@v@w. with \<alpha> \<Rightarrow>* u. After one \<epsilon> transition, IH
      can be used
      Problem: proving hist \<rho> = \<gamma>' 

      Previous approach: induct over n steps. Problem: last step does not produce A in general
      Possibly: induct over n steps with weak induction obtaining X and m where
        S' \<Rightarrow>r(m) \<gamma>Xu \<Rightarrow>r \<gamma>\<delta>A\<zeta>u \<Rightarrow>r* \<gamma>'Aw with m < n *)
lemma deriver_impl_IPDA_comp:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>'@Nt A#map Tm w"
    "Prods G' \<turnstile> \<gamma>'@Nt A#map Tm w \<Rightarrow>r \<gamma>'@\<alpha>@\<beta>@map Tm w"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  obtains \<rho> where 
    "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>@[init_symbol IPDA], v@w) \<turnstile>P* ([I.final_state, init_symbol IPDA], [])" 
    "hist \<rho> = \<gamma>'"
  using assms(1) proof cases
  case rtrancl_refl
  then have step: "\<gamma>' = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S]"
    using assms(2) S'_derive_impl_S append_eq_Cons_conv deriver_imp_derive by fastforce
  then show ?thesis 
    by (metis I.hist_init I.init_symbol_ipda append.right_neutral append_Nil assms(3)
        derivers_S_append_impl_comp hist_singleton local.rtrancl_refl map_Tm_Nt_eq_map_Tm_Nt that)
next
  case (rtrancl_into_rtrancl b)
  then show ?thesis sorry
qed
qed






  using assms proof (induction "\<gamma>'@Nt A#map Tm w" arbitrary: \<gamma>' A w \<alpha> \<beta> v thesis rule: rtranclp_induct)
  case base
  then have "\<gamma>' = [] \<and> w = []" "\<alpha>@\<beta> = [Nt S]"
    by (simp add: Cons_eq_append_conv,
        metis (no_types, opaque_lifting) S'_derive_impl_S append_Nil2 derive_singleton 
        deriver_singleton list.exhaust list.simps(3) Cons_eq_append_conv)
  then show ?case using base unfolding hist_defs
    by (metis append.left_neutral append.right_neutral concat.simps(1) derivers_S_append_impl_comp 
        list.inject list.simps(8) sym.inject(1))
next
  case (step \<gamma>)
  then obtain as where \<alpha>_derivers: "Prods G' \<turnstile> \<alpha> \<Rightarrow>r* map Tm as"
    using reduced_derived_substring_impl_derives[OF _ G'_reduced G'_not_empty] G'_def 
    by (metis (no_types, lifting) Cfg.sel(2) derivers_iff_derives derivers_imp_derives
        rtranclp.rtrancl_into_rtrancl)
  obtain X \<delta> u where \<gamma>_def: "\<gamma> = \<delta> @ Nt X#map Tm u"
    using step(2) by (meson deriver.cases)
  then obtain xs ys where xy_defs: "(X, xs@ys) \<in> Prods G'" "\<delta>@xs@ys@map Tm u = \<gamma>'@Nt A#map Tm w"
    using step deriver_impl_handle by (metis self_append_conv2)
  with step obtain v' where ys_derivers: "Prods G' \<turnstile> ys \<Rightarrow>r* map Tm v'"
    using reduced_derived_substring_impl_derives[OF _ G'_reduced G'_not_empty] G'_def \<gamma>_def 
    by (metis (no_types, lifting) Cfg.sel(2) append.assoc derivers_iff_derives derivers_imp_derives
        rtranclp.rtrancl_into_rtrancl)
  with step(2,3) obtain \<rho> where \<rho>_def:
    "([X \<rightarrow> xs . ys]#\<rho>@[init_symbol IPDA], v'@u) \<turnstile>P* ([final_state, init_symbol IPDA],[])"
    "hist \<rho> = \<delta>"
    using \<gamma>_def xy_defs by metis
  with reaches_final_impl_compl_final have X_compl_final:
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
     show thesis using that derivers_impl_in_stack[OF _ 2 _ _ 3 X_compl_final] xy_defs(2) 
       by (metis (no_types, lifting) \<gamma>_def append.assoc append.simps(2) step.hyps(1) step.prems(2))
   qed
   let ?\<rho>' = "[Y \<rightarrow> ws . Nt A#zs]#\<rho>r"
  note Y_defs(2)
  also have Y_step: 
    "(?\<rho>'@[init_symbol IPDA], as@v@w) \<turnstile>P ([A \<rightarrow> [] . \<alpha>@\<beta>]#?\<rho>'@[init_symbol IPDA], as@v@w)"
    using expanding deriver_impl_in_Prods step(5) 
    by (metis (no_types, lifting) append.assoc append_Cons)
  also with derivers_impl_completes have A_init_steps:
    "... \<turnstile>P* ([A \<rightarrow> \<alpha> . \<beta>]#?\<rho>'@[init_symbol IPDA], v@w)"
    using \<alpha>_derivers by (metis append_Nil rtranclp_power)
  finally have ex_comp: "... \<turnstile>P* ([final_state, init_symbol IPDA], [])"
    using X_compl_final  sorry
  moreover have "hist ?\<rho>' = \<gamma>'" 
  proof -
    from Y_defs(2) Y_step A_init_steps 
    derivers_impl_completes rtranclp_imp_relpowp step(6)
    have "([X \<rightarrow> xs @ ys . []]#\<rho>@[init_symbol IPDA], u) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []]#?\<rho>'@[init_symbol IPDA],w)"
      using rtranclp_trans 
      by (smt (verit, ccfv_threshold) append.right_neutral rtranclp.rtrancl_into_rtrancl)
    with \<gamma>_def step(2) xy_defs(2) X_compl_final show ?thesis using \<rho>_def(2) sorry
  qed
  ultimately show ?case using step(4) by presburger
qed




(*
    (* Does not hold in general. Strong induction needed instead *)
    obtain \<delta>' u' where X_prod: "(X, \<delta>'@Nt A#map Tm u') \<in> Prods G'" "\<gamma>' = \<delta>@\<delta>'" 
      "map Tm (u'@u) = map Tm w"
      using deriver_decomp[OF n_steps(2)] by blast
    from reduced_derived_substring_impl_derives[OF _ G'_reduced G'_not_empty] 
    Suc.prems(4) obtain v' where A_derives: "Prods G' \<turnstile> [Nt A] \<Rightarrow>r* map Tm v'"
     by (metis (no_types, opaque_lifting) append_Cons append_self_conv2
        derivern_imp_deriven derivers_iff_derives rtranclp_power)
    hence A_Cons_derivers: "Prods G' \<turnstile> Nt A#map Tm u' \<Rightarrow>r* map Tm (v'@u')" 
      using derives_append derivers_iff_derives by (metis append_Cons append_Nil map_append)
    from Suc(1)[OF _ this _ n_steps(1)] obtain \<rho> where \<rho>_def:
      "([X \<rightarrow> \<delta>' . Nt A#map Tm u'] # \<rho> @ [init_symbol IPDA], v' @ u' @ u) \<turnstile>P* (?qf, [])"
      "hist \<rho> = \<delta>"
      using n_steps(2) X_prod(2,3) append_assoc by (metis append_Cons map_Tm_inject_iff map_append)
    hence Xw_final: "([X \<rightarrow> \<delta>' @ [Nt A] . map Tm u'] # \<rho> @ [init_symbol IPDA], w) \<turnstile>P* (?qf, [])"
      using derives_impl_complete_reaches_final Suc(3) derivers_iff_derives 
      by (metis A_derives X_prod(3) append_Cons append_Nil map_Tm_inject_iff) 
    let ?\<rho>' = "[X \<rightarrow> \<delta>' . Nt A#map Tm u'] # \<rho>"
    have \<rho>'_hist: "hist ?\<rho>' = \<gamma>'" using \<rho>_def(2) X_prod(2) by (simp add: history_def)
    have "([A \<rightarrow> \<alpha> . \<beta>] # ?\<rho>' @ [init_symbol IPDA], v@w) 
      \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []]# ?\<rho>' @ [init_symbol IPDA], w)" 
      using derives_impl_completes derivers_iff_derives Suc(3) 
      by (metis append.right_neutral)
    also have "... \<turnstile>P ([X \<rightarrow> \<delta>' @ [Nt A] . map Tm u'] # \<rho> @ [init_symbol IPDA], w)"
      using LR_Parser.IPDA.reducing[OF ipda] by simp
    also note Xw_final
    finally show thesis using Suc(4)[OF _ \<rho>'_hist] by presburger
  qed *)


end

end
