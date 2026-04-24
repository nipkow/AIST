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


(* TODO: Specify correctly and use *)
lemma Nt_in_left_context_imp_produced:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [X' \<rightarrow> \<alpha>' . Nt X # \<beta>] # \<rho> \<Rightarrow>r* \<alpha> @ Nt B # \<alpha>'' @ \<alpha>' @ Nt X # map Tm w"
    "Nt B \<in> set \<alpha>"
  obtains "is" A C \<beta>' \<beta>'' \<gamma>  js \<delta> u where 
    "[X' \<rightarrow> \<alpha>' . Nt X # \<beta>] # \<rho> = is @ [A \<rightarrow> \<alpha>'' @ Nt B # \<alpha>''' . Nt C # \<beta>'] # js"
    "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<beta>'' @ Nt B # \<alpha>'' . Nt C # \<beta>'] # js 
                  \<Rightarrow>r* \<gamma> @ \<alpha>'' @ Nt B # \<alpha>'' @ Nt C # \<beta>' @ map Tm u"
    "P \<Turnstile> \<delta> @ Nt A # map Tm u \<Rightarrow>r* is @ [[A \<rightarrow> \<alpha>'' . Nt C # \<beta>']] \<Rightarrow>r*  \<alpha> @ \<alpha>' @ Nt X # map Tm w"
    "Nt B \<in> set \<alpha>''"
  sorry

lemma chain_produces_right_context_imp_derivers:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [X' \<rightarrow> \<alpha>' @ Nt A # \<alpha>'' . Nt X # \<beta>] # \<sigma> 
                        \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt A # \<alpha>'' @ Nt X # map Tm v"
    "P \<Turnstile> \<alpha> @ \<alpha>' @ Nt A # \<alpha>'' @ Nt X # map Tm v \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt A # map Tm w"
  shows "P \<turnstile> \<alpha>'' @ Nt X # map Tm v \<Rightarrow>r* map Tm w"
  sorry


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
  from Suc(1)[OF _ this(1)] obtain \<rho> where last_chain_step: 
    "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta> @ Nt B # map Tm u" by blast
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
      thm Nt_in_left_context_imp_produced
      thm \<beta>\<zeta>\<alpha>'

      from \<beta>\<gamma>_decomp Suc_steps(2) have "\<alpha> = \<delta>" by force
      from rm_chain_imp_hd_prod_rightmost[OF snd_last_chn_step(2)] 
      obtain X'' \<alpha>'' \<beta>'' js where is_def:
        "is = [X'' \<rightarrow> \<alpha>'' . Nt X' # \<beta>''] # js"
        using left by cases simp+
      thm rm_chain_stepE[OF snd_last_chn_step(2)[unfolded is_def]]
      from left snd_last_chn_step(3) have 
        "P \<turnstile> \<delta> @ Nt X # map Tm u' @ Nt X' # map Tm x \<Rightarrow>r \<delta> @ Nt X # map Tm u' @ map Tm v'" sorry
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
  qed
qed


lemma deriver_imp_IPDA_comp:
  assumes "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>'@Nt A#map Tm w"
    "Prods G' \<turnstile> \<gamma>'@Nt A#map Tm w \<Rightarrow>r \<gamma>'@\<alpha>@\<beta>@map Tm w"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  obtains \<rho> where 
    "([A \<rightarrow> \<alpha> . \<beta>]#\<rho>@[init_symbol IPDA], v@w) \<turnstile>P* ([I.final_state, init_symbol IPDA], [])" 
    "hist \<rho> = \<gamma>'"
  sorry


end

end
