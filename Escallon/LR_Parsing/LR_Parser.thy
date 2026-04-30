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
    by (metis A_last Nil.prems(3) append.right_neutral isNt_simps(1,2) last_ConsR last_appendR last_in_set
        last_map list.distinct(1) list.map_disc_iff)
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
  using assms by (metis ex_map_conv sym.exhaust)

lemma Tms_iff_no_Nts:
  "(\<exists>w. \<alpha> = map Tm w) \<longleftrightarrow> (\<nexists>A. Nt A \<in> set \<alpha>)"
  by (rule iffI) (use sym.exhaust in force, use no_Nts_imp_Tms in blast)



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
    show ?thesis 
      by (meson \<alpha>\<beta>_defs(1) syms_split_rightmost Tms_iff_no_Nts that(1,2)) 
  next
    case 2
    then show ?thesis using syms_split_rightmost \<alpha>\<beta>_defs 
      by (metis Tms_iff_no_Nts that(1,2))
  qed
qed



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
  from step(2) obtain \<delta> where eq: "\<beta> @ Nt B # map Tm w = \<gamma> @ \<delta> @ map Tm u" 
    unfolding y_def using deriver_imp_handle by metis
  consider "Nt B \<in> set \<delta>" | "Nt B \<notin> set \<delta>" "Nt B \<in> set \<gamma>"
  proof (cases "Nt B \<in> set \<delta>")
    case False
    then show ?thesis using eq that 
      by (metis Un_iff ex_map_conv in_set_conv_decomp set_append sym.distinct(1))
  qed (use that in simp)
  then show ?case
    using eq u_decomp step by cases 
      ((metis append.assoc syms_decomp_rightmost2),
        (metis append.assoc append_Nil syms_decomp_rightmost[of \<beta> B _ "[]" \<gamma> \<delta>]))
qed

lemma deriver_rightmost_cases[consumes 1, case_names prod prefix]:
  assumes "P \<turnstile> \<alpha> @ Nt A # map Tm u \<Rightarrow>r \<beta> @ Nt B # map Tm w"
  obtains \<gamma> v where "\<beta> @ Nt B # map Tm w = \<alpha> @ \<gamma> @ Nt B # map Tm v @ map Tm u" |
          \<delta> v x where "\<alpha> = \<delta> @ Nt B # map Tm x" "\<beta> @ Nt B # map Tm w = \<alpha> @ map Tm (v@u)"
proof -
  from assms obtain \<gamma> where deriv: "\<beta> @ Nt B # map Tm w = \<alpha> @ \<gamma> @ map Tm u" "(A, \<gamma>) \<in> P" 
    by (metis deriver_imp_handle)
  then consider (Tms) x where "\<gamma> = map Tm x" | (Nt) \<delta> C \<zeta> where "\<gamma> = \<delta> @ Nt C # \<zeta>" 
    by (metis split_list Tms_iff_no_Nts)
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

lemma derivers_imp_derivers_tl:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha> @ Nt A # map Tm v"
  obtains \<beta> where "P \<turnstile> [Nt A] \<Rightarrow>r* \<alpha> @ Nt A # \<beta>"
    "P \<turnstile> \<alpha> @ Nt A # \<beta> \<Rightarrow>r* \<alpha> @ Nt A # map Tm v"
  using assms by induction (use that assms in auto)

inductive rm_chain :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) syms \<Rightarrow> ('a, 'b) item list \<Rightarrow> ('a, 'b) syms 
                            \<Rightarrow> bool" 
   (\<open>_ \<Turnstile> _ \<Rightarrow>r* _ \<Rightarrow>r* _\<close> 30) for P where
refl[intro]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [] \<Rightarrow>r* \<alpha>" |

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

inductive_cases rm_chain_reflE[elim]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [] \<Rightarrow>r* \<beta>"
inductive_cases rm_chain_stepE[elim]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> \<alpha>' . Nt B # \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"

lemma rm_chain_imp_prod:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"
  shows "(A, \<alpha>@\<beta>) \<in> P"
  using assms syms_split_rightmost by cases (simp add: deriver_imp_in_Prods)



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
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u" "w = u @ v" | "\<alpha>\<^sub>0 = \<gamma> @ Nt B # map Tm w" "\<rho> = []"
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


lemma rm_chain_append:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* \<sigma> \<Rightarrow>r* \<beta>"
    "P \<Turnstile> \<beta> \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  shows "P \<Turnstile> \<alpha> \<Rightarrow>r* \<rho>@\<sigma> \<Rightarrow>r* \<gamma>"
  using assms(2,1) by induction auto

lemma rm_chain_decomp:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* \<rho>@\<sigma> \<Rightarrow>r* \<gamma>"
  obtains \<beta> where 
    "P \<Turnstile> \<alpha> \<Rightarrow>r* \<sigma> \<Rightarrow>r* \<beta>"
    "P \<Turnstile> \<beta> \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  using assms proof (induction \<rho> arbitrary: \<gamma>)
  case (Cons a \<rho>)
  then show ?case 
    by (smt (verit, del_insts) append.simps(2) list.distinct(1) list.simps(1) rm_chain.simps)
qed auto



lemma rm_chain_snoc:
  assumes "P \<Turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r* \<rho> @ [[X \<rightarrow> \<alpha>' . Nt Y # \<beta>]] \<Rightarrow>r* \<gamma>"
  obtains u where "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u" 
    "P \<Turnstile> \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  using assms 
  by (smt (verit, best) append_same_eq right_derivs_eq_imp_eq_tl rm_chain_decomp rm_chain_reflE
      rm_chain_stepE)

lemma rm_chain_substring:
  assumes "P \<Turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta> @ Nt Y # map Tm w"
  obtains u where "w = u @ v"
  using assms proof (induction "\<alpha> @ Nt X # map Tm v" \<rho> "\<beta> @ Nt Y # map Tm w" arbitrary: \<beta> Y w)
  case refl
  then show ?case using right_derivs_eq_imp_eq_tl[OF refl(1)] by simp
next
  case (step \<rho> \<alpha>' X v \<gamma> Y' \<beta>' u)
  then show ?case 
    by (meson assms derivers_tl_substring rm_chain_imp_derivers that)
qed

lemma rightmost_eq_imp_tl_substring:
  assumes "\<alpha> @ Nt X # map Tm w = \<alpha>' @ \<gamma> @ map Tm v"
  obtains u where "w = u @ v"
  using assms that by (cases "Nt X \<in> set \<gamma>")
    ((meson syms_decomp_rightmost2),
   (metis Tms_iff_no_Nts Un_iff append.assoc append_Nil in_set_conv_decomp 
     set_append syms_decomp_rightmost[of \<alpha> X w "[]" \<alpha>' \<gamma> v]))

lemma syms_split_tl:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
  obtains \<beta>' where "\<beta> = \<beta>' @ map Tm v"
proof -
  consider (Tms) u where "\<beta> = map Tm u" | (rightmost) \<beta>' Y u where "\<beta> = \<beta>' @ Nt Y # map Tm u"
    by (meson Tms_iff_no_Nts syms_split_rightmost)
  then show thesis
  proof cases
    case Tms
    then show ?thesis using rightmost_eq_imp_tl_substring[OF assms[unfolded Tms]] that 
      by fastforce
  next
    case rightmost
    with assms[unfolded this] show ?thesis 
      using rightmost_eq_imp_tl_substring[of "\<alpha> @ Nt X # \<beta>'" Y u] 
      by (metis append.assoc append_Cons map_append that)
  qed
qed

lemma syms_split_leq:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
    "length \<alpha>' \<le> length \<alpha>"
  obtains \<alpha>'' \<beta>'  where "\<alpha> = \<alpha>' @ \<alpha>''" "\<gamma> = \<alpha>'' @ Nt X # \<beta>'" "\<beta> = \<beta>' @ map Tm v"
using assms proof (induction \<alpha>' arbitrary: \<alpha> thesis)
  case Nil
  then show ?case using Nil(1)[of \<alpha>] syms_split_tl[OF Nil(2)] 
    by (smt (verit, ccfv_threshold) Cons_eq_appendI append_assoc append_same_eq self_append_conv2) 
next
  case (Cons a \<alpha>')
  note Cons_\<alpha>' = this
  show ?case 
    by (cases \<alpha>) (use Cons in auto)
qed

lemma syms_split_gt:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
    "length \<alpha>' > length \<alpha>"
  obtains \<alpha>'' where "\<alpha>' = \<alpha> @ Nt X # \<alpha>''" "\<beta> = \<alpha>'' @ \<gamma> @ map Tm v"
using assms proof (induction \<alpha> arbitrary: \<alpha>' thesis)
  case Nil
  then show ?case using Nil(1)[of "[]"] 
    by (metis (no_types, lifting) append_eq_Cons_conv length_greater_0_conv list.size(3))
next
  case (Cons a \<alpha>)
  show ?case 
    by (cases \<alpha>') (use Cons in auto)
qed



lemma syms_split_cases:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
  obtains \<alpha>'' \<beta>'  where "\<alpha> = \<alpha>' @ \<alpha>''" "\<gamma> = \<alpha>'' @ Nt X # \<beta>'" "\<beta> = \<beta>' @ map Tm v" |
              \<alpha>'' where "\<alpha>' = \<alpha> @ Nt X # \<alpha>''" "\<beta> = \<alpha>'' @ \<gamma> @ map Tm v"
  by (cases "length \<alpha>' \<le> length \<alpha>")  
    (meson assms that syms_split_leq syms_split_gt not_le_imp_less)+ 

lemma derivers_singleton_imp_produced:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # \<beta>"
  obtains m \<alpha>' B v \<alpha>'' \<beta>' where
    "m < Suc n"
    "P \<turnstile> [Nt A] \<Rightarrow>r(m) \<alpha>' @ Nt B # map Tm v"
    "P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm v"
    "\<alpha> = \<alpha>' @ \<alpha>''"
    "P \<turnstile> \<beta>' @ map Tm v \<Rightarrow>r* \<beta>"
  using assms proof (induction "Suc n" arbitrary: n \<alpha> X \<beta> thesis rule: less_induct)
  case less
  show ?case 
  proof (cases n)
    case 0
    then show ?thesis using less(2)[of 0 "[]" A "[]" \<alpha> \<beta>] less(3) by auto
  next
    case (Suc m)
    note Suc_m = this
    from less(3) obtain \<alpha>' B v where n_steps: "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha>' @ Nt B # map Tm v"
      "P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha> @ Nt X # \<beta>" 
      by (smt (verit) deriver.cases relpowp_Suc_E)
    then obtain \<gamma> where B_prod: "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v" "(B, \<gamma>) \<in> P"
      by (metis deriver_imp_handle in_set_conv_decomp syms_split_rightmost)
    then show thesis proof (cases rule: syms_split_cases)
      case (1 \<alpha>'' \<beta>')
      then show ?thesis using less(2)[OF _ n_steps(1), of \<alpha>'' \<beta>'] B_prod n_steps(2) by fastforce
    next
      case (2 \<alpha>'')
      with n_steps have "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha> @ Nt X # \<alpha>'' @ Nt B # map Tm v" by simp
      with less(1)[of _ X \<alpha> "\<alpha>'' @ Nt B # map Tm v"] obtain k \<delta> C w \<zeta> \<beta>' where k_steps:
        "k < Suc m" "P \<turnstile> [Nt A] \<Rightarrow>r(k) \<delta> @ Nt C # map Tm w"
        "P \<turnstile> \<delta> @ Nt C # map Tm w \<Rightarrow>r \<delta> @ \<zeta> @ Nt X # \<beta>' @ map Tm w" "\<alpha> = \<delta> @ \<zeta>"
        "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<alpha>'' @ Nt B # map Tm v" using Suc by blast
      from this(5) \<open>\<beta> = \<alpha>'' @ \<gamma> @ map Tm v\<close> B_prod(2) have derivers_\<beta>: "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<beta>" 
        using 2 by (meson deriver.intros rtranclp.simps)
      show ?thesis using less(2)[OF _ k_steps(2-4) derivers_\<beta>] Suc_m k_steps(1) by linarith    
    qed
  qed
qed

lemma derivers_singleton_imp_rm_chain:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v"
    "P = Prods J"
    "reduced J"
    "LangS J \<noteq> {}"
    "A \<in> Nts P"
  obtains \<rho> where "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v"
  using assms(1) proof (induction "Suc n" arbitrary: \<alpha> X v n thesis rule: less_induct)
  case (less n)
  show ?case 
  proof (cases n)
    case 0
    then show ?thesis using rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" \<alpha> X] less by auto
  next
    case (Suc m)
    note Suc_m = this
    with less obtain \<beta> B u \<gamma> where Suc_steps: "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<beta> @ Nt B # map Tm u"
      "\<beta> @ \<gamma> @ map Tm u = \<alpha> @ Nt X # map Tm v" "P \<turnstile> \<beta> @ Nt B # map Tm u \<Rightarrow>r \<beta> @ \<gamma> @ map Tm u"
      using deriver.cases by (smt (verit, del_insts) relpowp_Suc_E)
    with less(1)[OF _ this(1)] Suc obtain \<rho> where last_chain_step: 
      "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta> @ Nt B # map Tm u" using less.hyps by blast
    show ?thesis
    proof (cases "Nt X \<in> set \<gamma>")
      case True
      from Suc_steps(2) obtain \<delta> w where"\<gamma> = \<delta> @ Nt X # map Tm w" "w @ u = v" 
      by (metis True syms_decomp_rightmost2)
      with Suc Suc_steps less show thesis using last_chain_step by fastforce
    next
      case False
      with Suc_steps(2) have X_in_\<beta>: "Nt X \<in> set \<beta>" 
        by (metis Nts_syms_append Nts_syms_map_Tm Un_iff empty_iff in_Nts_syms list.set_intros(1))
      from syms_decomp_rightmost[OF _ X_in_\<beta> False, of \<alpha> v "[]" u] obtain \<delta> y z where
        \<beta>\<gamma>_decomp: "\<beta> = \<delta> @ Nt X # map Tm y" "\<gamma> = map Tm z" "v = y @ z @ u"
        using Suc_steps(2) by auto
      hence B_deriver: "P \<turnstile> [Nt B] \<Rightarrow>r map Tm z" using deriver_singleton 
        deriver_imp_in_Prods[OF Suc_steps(3)] by fast
      from \<beta>\<gamma>_decomp derivers_singleton_imp_produced[of m P A \<delta> X "map Tm y @ Nt B # map Tm u"] 
        Suc_steps(1) Suc
      obtain k \<alpha>' C w \<alpha>'' \<beta>' where k_steps:
        "P \<turnstile> [Nt A] \<Rightarrow>r(k) \<alpha>' @ Nt C # map Tm w"
        "P \<turnstile> \<alpha>' @ Nt C # map Tm w \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm w"
        "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm y @ Nt B # map Tm u"
        "\<delta> = \<alpha>' @ \<alpha>''" "k < Suc m" 
        by (smt (verit, ccfv_SIG) Cons_eq_appendI append_assoc)
      with \<beta>\<gamma>_decomp Suc_steps(2-) B_deriver have suffix_derivers_v:
          "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm v"
        using deriver.intros deriver_singleton 
          by (metis (mono_tags, lifting) map_append rtranclp.simps)
      show ?thesis 
      proof (cases k)
        case 0
        with k_steps(1) have eqs: "\<alpha>' = [] \<and> A = C \<and> w = []" 
          by (metis append1_eq_conv eq_Nil_appendI map_is_Nil_conv relpowp_0_E right_derivs_eq_imp_eq_tl
              sym.inject(1)) 
        moreover with k_steps(3) have "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm v" using eqs suffix_derivers_v by simp
        ultimately show ?thesis using less(2) rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" \<alpha>'' X \<beta>']
          0 k_steps 
          by (metis Suc_steps(2) \<beta>\<gamma>_decomp append.assoc append.right_neutral append_Cons append_Nil
              list.simps(8) map_append rm_chain.refl)
      next
        case (Suc j)
        from less(1)[OF _ _ k_steps(1)[unfolded Suc]] obtain \<rho> where \<rho>_def:
          "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha>' @ Nt C # map Tm w" using k_steps(5)[unfolded Suc] Suc_m
          by auto
        moreover from suffix_derivers_v obtain u' where "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm u'" "u' @ w = v"
          by (metis converse_rtranclpE derivers_iff_derives derives_append_map_Tm map_Tm_inject_iff
              not_derive_map_Tm)
        moreover from \<beta>\<gamma>_decomp Suc_steps(2) have "\<alpha> = \<delta>" by force
        ultimately show ?thesis using less(2) rm_chain.step[OF \<rho>_def k_steps(2)] 
          k_steps(4) by fastforce
      qed
    qed
  qed
qed

lemma deriver_imp_IPDA_comp:
  assumes
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r \<alpha>@\<beta>"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  shows
    "([[S' \<rightarrow> \<alpha> . \<beta>], init_symbol IPDA], v) \<turnstile>P* ([I.final_state, init_symbol IPDA], [])"
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
    then show ?thesis using eq_S I.Lang_def right 
        I.Lang_eq_Lang_G Lang_preserved hist_singleton rtrancl_refl by auto
  qed
qed


lemma derivers_imp_IPDA_comp:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>@Nt A#map Tm w"
    "Prods G' \<turnstile> \<gamma>@Nt A#map Tm w \<Rightarrow>r \<gamma>@\<alpha>@\<beta>@map Tm w"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  obtains \<rho> where 
    "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>@[init_symbol IPDA], v@w) \<turnstile>P* ([I.final_state, init_symbol IPDA], [])" 
    "hist \<rho> = \<gamma>"
  using assms(1) proof cases
  case rtrancl_refl
  with assms have eqs: "\<gamma> = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S]" 
    using S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
  then show thesis using S'_derive_imp_S deriver_imp_IPDA_comp assms that 
    by (metis I.hist_init I.init_symbol_ipda append.right_neutral append_Nil hist_singleton list.inject
        rtrancl_refl sym.inject(1))
next
  case (rtrancl_into_rtrancl b)
  then obtain n where "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<gamma> @ Nt A # map Tm w" 
    by (meson relpowp_Suc_I rtranclp_imp_relpowp)
  from derivers_singleton_imp_rm_chain[OF this _ G'_reduced G'_not_empty] obtain \<rho> where 
    "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma> @ Nt A # map Tm w"
    using Nts_G'_is_union by blast
  then show ?thesis using assms that proof (induction \<rho> arbitrary: \<gamma> A w \<alpha> \<beta> v thesis)
    case Nil
    then have eqs: "\<gamma> = [] \<and> w = [] \<and> \<alpha>@\<beta> = [Nt S] \<and> A = S'" 
      using S'_derive_imp_S append_eq_Cons_conv deriver_imp_derive by fastforce
    then show thesis using S'_derive_imp_S deriver_imp_IPDA_comp Nil
    by (metis I.hist_init I.init_symbol_ipda append.right_neutral append_Nil hist_singleton
        list.simps(8))
  next
    case (Cons i \<rho>)
    then obtain X \<alpha>' \<beta>' where 
      "i = [X \<rightarrow> \<alpha>' . Nt A # \<beta>']" 
      using rm_chain_imp_hd_prod_rightmost[OF Cons(2)]
      by (metis list.distinct(1) list.inject)
    with rm_chain_stepE Cons(2) obtain \<alpha>'' u v' where X_chain:
      "Prods G' \<Turnstile> [Nt S'] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha>'' @ Nt X # map Tm v'"
      "Prods G' \<turnstile> \<alpha>'' @ Nt X # map Tm v' \<Rightarrow>r \<alpha>'' @ \<alpha>' @ Nt A # \<beta>' @ map Tm v'"
      "Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm u" "u @ v' = w" "\<alpha>'' @ \<alpha>' = \<gamma>"
      by (smt (verit, best) append.assoc append_same_eq map_append right_derivs_eq_imp_eq_tl)
    then obtain \<rho>' where \<rho>'_def:
      "([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho>' @ [init_symbol IPDA], u@v') 
          \<turnstile>P* ([I.final_state, init_symbol IPDA], [])"
      "hist \<rho>' = \<alpha>''" 
      using Cons(1)[OF X_chain(1) rm_chain_imp_derivers[OF X_chain(1)], of "\<alpha>' @ [Nt A]" \<beta>']
      by auto
    let ?\<rho> = "[X \<rightarrow> \<alpha>' . Nt A # \<beta>'] # \<rho>'"
    have hist_\<rho>: "hist ?\<rho> = \<gamma>" using X_chain(5) \<rho>'_def(2) by simp
    from I.derives_imp_completes[OF Cons(5)[THEN derivers_imp_derives]] have 
      "([A \<rightarrow> \<alpha> . \<beta>] # ?\<rho> @ [init_symbol IPDA], v @ w) \<turnstile>P* ([A \<rightarrow> \<alpha>@\<beta> . []] # ?\<rho> @ [init_symbol IPDA], w)"
      by (metis append.right_neutral)
    also have "... \<turnstile>P ([X \<rightarrow> \<alpha>' @ [Nt A] . \<beta>'] # \<rho>' @ [init_symbol IPDA], u@v')"
      using X_chain(4) by auto
    also have "... \<turnstile>P* ([I.final_state, init_symbol IPDA], [])" using \<rho>'_def by presburger
    finally show ?case using hist_\<rho> Cons(6) by presburger
  qed
qed 




end

end
