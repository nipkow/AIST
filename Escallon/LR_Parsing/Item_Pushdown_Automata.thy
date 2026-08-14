theory Item_Pushdown_Automata
  imports 
    Extended_Cfg
    Generalized_Pushdown_Automata
begin

section \<open>Context-Free Items\<close>

datatype ('n, 't) item = Item 'n  "('n, 't) syms"  "('n, 't) syms" ("[_ \<rightarrow> _ \<cdot> _]")

abbreviation prod_of_item :: "('n, 't) item \<Rightarrow> ('n, 't) prod" where
  "prod_of_item i \<equiv> case i of [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<Rightarrow> (A, \<alpha>@\<beta>)"

definition history :: "('n, 't) item \<Rightarrow> ('n, 't) syms" where
  "history i \<equiv> case i of [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<Rightarrow> \<alpha>"

lemma history_unfold [simp]: "history [A \<rightarrow> \<alpha> \<cdot> \<beta>] = \<alpha>"
  unfolding history_def by simp

definition hist :: "('n, 't) item list \<Rightarrow> ('n,'t) syms" where
  "hist \<rho> \<equiv> concat (map history \<rho>)"

lemma hist_Nil [simp]:
  "hist [] = []" 
  unfolding hist_def by simp

lemma hist_singleton [simp]:
  "hist ([[A \<rightarrow> \<alpha> \<cdot> \<beta>]]) = \<alpha>"
  unfolding hist_def by simp

lemma hist_Cons [simp]:
  "hist (i#\<rho>) = history i @ hist \<rho>"
  unfolding hist_def by simp

lemma hist_append [simp]:
  "hist (\<rho> @ \<sigma>) = hist \<rho> @ hist \<sigma>"
  unfolding hist_def by simp

lemmas hist_defs = hist_def history_def

definition It :: "('n, 't) Cfg \<Rightarrow> ('n, 't) item set" where
  "It G = {[A \<rightarrow> \<alpha> \<cdot> \<beta>] |A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> Prods G}"

definition Nts_of_items :: "('n, 't) item set \<Rightarrow> 'n set" where
  "Nts_of_items I \<equiv> (\<lambda>i. case i of [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<Rightarrow> A) ` I"

definition Hists_of_items :: "('n, 't) item set \<Rightarrow> ('n, 't) syms set" where
  "Hists_of_items I \<equiv> (\<lambda>i. case i of [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<Rightarrow> \<alpha>) ` I"

lemma in_items_imp_in_Nts [intro]:
  assumes "[A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> I"
  shows "A \<in> Nts_of_items I"
  using assms unfolding Nts_of_items_def by force

lemma in_items_imp_in_Hists [intro]:
  assumes "[A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> I"
  shows "\<alpha> \<in> Hists_of_items I"
  using assms unfolding Hists_of_items_def by force

lemma in_Prods_imp_in_It:
  "prod_of_item i \<in> Prods G \<Longrightarrow> i \<in> It G"
  unfolding It_def by (metis (mono_tags, lifting) item.case item.exhaust mem_Collect_eq)

lemma in_It_imp_in_Prods:
  "i \<in> It G \<Longrightarrow> prod_of_item i \<in> Prods G"
  unfolding It_def by auto

lemma in_Prods_iff_in_It:
  "prod_of_item i \<in> Prods G = (i \<in> It G)"
  using in_Prods_imp_in_It in_It_imp_in_Prods by auto

lemma prod_items_finite:
  "finite {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w}"
proof -
  let ?f = "\<lambda>n. [A \<rightarrow> take n w \<cdot> drop n w]"
  have "bij_betw ?f {..< Suc (length w)} {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w}"
    unfolding bij_betw_def proof
    show "inj_on ?f {..<Suc (length w)}"
      by standard (auto, metis less_Suc_eq_le length_take min_absorb2)
  next
    show "?f ` {..< Suc (length w)} = {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w}"
    proof
      show "{[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w} \<subseteq> ?f ` {..< Suc (length w)}"
      proof
        fix i
        assume "i \<in> {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w}"
        then obtain \<alpha> \<beta> where i_def: "i = [A \<rightarrow> \<alpha> \<cdot> \<beta>]" "w = \<alpha> @ \<beta>" by blast
        moreover from i_def have "i = [A \<rightarrow> take (length \<alpha>) w \<cdot> drop (length \<alpha>) w]"
          by simp
        ultimately show "i \<in> ?f ` {..< Suc (length w)}" by fastforce
      qed
    qed auto
  qed
  then show ?thesis using bij_betw_finite by fast
qed

corollary finite_It:
  assumes "finite (Prods G)"
  shows "finite (It G)"
proof -
  have "It G = (\<Union>(A,w)\<in>Prods G. {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w})"
    unfolding It_def by auto
  with prod_items_finite show ?thesis using assms by fastforce
qed

lemma finite_items_imp_finite_Nts:
  assumes "finite I"
  shows "finite (Nts_of_items I)"
  using assms unfolding Nts_of_items_def by blast

lemma finite_items_imp_finite_Hists:
  assumes "finite I"
  shows "finite (Hists_of_items I)"
  using assms unfolding Hists_of_items_def by blast

lemma finite_lists_length_eq_Hists:
  assumes "finite I" "finite A"
  shows "finite {xs |xs \<alpha>. set xs \<subseteq> A \<and> length xs = length \<alpha> \<and> \<alpha> \<in> (Hists_of_items I)}"
proof -
  note finite_Hists = finite_items_imp_finite_Hists[OF assms(1)]
  have "{xs|xs \<alpha>. set xs \<subseteq> A \<and> length xs = length \<alpha> \<and> \<alpha> \<in> (Hists_of_items I)}
        = {xs|xs n. set xs \<subseteq> A \<and> length xs = n \<and> n \<in> length ` (Hists_of_items I)}"
    by blast
  with finite_lists_length_eq_set finite_Hists assms(2) show ?thesis by auto
qed

subsection \<open>Complete and Noncomplete Items\<close>

definition completes :: "('n, 't) item set \<Rightarrow> ('n, 't) item set" where
  "completes I \<equiv> {i \<in> I. case i of [X \<rightarrow> \<alpha> \<cdot> \<beta>] \<Rightarrow> \<beta> = []}"

lemma completes_subset [simp]:
  "completes I \<subseteq> I" unfolding completes_def by simp

lemma completesD [dest]:
  "i \<in> completes I \<Longrightarrow> i \<in> I"
  using completes_subset by blast

lemma completesE [elim]:
  assumes "i \<in> completes I"
  obtains X \<alpha> where "i = [X \<rightarrow> \<alpha> \<cdot> []]"
  using assms unfolding completes_def 
  by (metis (mono_tags, lifting) item.case item.exhaust mem_Collect_eq)

lemma completes_singleton_imp_eq:
  assumes "completes I = {[X \<rightarrow> \<alpha> \<cdot> []]}"
    "[A \<rightarrow> \<beta> \<cdot> []] \<in> I"
  shows "[A \<rightarrow> \<beta> \<cdot> []] = [X \<rightarrow> \<alpha> \<cdot> []]"
  using assms unfolding completes_def by fastforce

abbreviation "incompletes I \<equiv> I - completes I"

lemma incompletesE [elim]:
  assumes "i \<in> incompletes I"
  obtains X \<alpha> Y \<beta> where "i = [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>]"
  using assms unfolding completes_def
  by (metis (mono_tags, lifting) item.case item.exhaust mem_Collect_eq neq_Nil_conv
      set_diff_eq)

section \<open>The Item Pushdown Automaton\<close>

definition (in Extended_Cfg) IPDA :: "(('n, 't) item, 't) gpda" where
  "IPDA \<equiv> let
    P = Prods G';
    \<Delta> = {([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], a, [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]])|X \<beta> a \<gamma>. (X, \<beta> @ Tm a # \<gamma>) \<in> P};
    \<E> = {([[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[Y \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]])
        | X \<beta> Y \<gamma> \<alpha>. (X, \<beta> @ Nt Y # \<gamma>) \<in> P \<and> (Y, \<alpha>) \<in> P} \<union> 
        {([[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]])
        | Y \<alpha> X \<beta> \<gamma>. (X, \<beta> @ Nt Y # \<gamma>) \<in> P \<and> (Y, \<alpha>) \<in> P}     
  in \<lparr>gpda.states = It G', init = [S' \<rightarrow> [] \<cdot> [Nt S]], final = {[S' \<rightarrow> [Nt S] \<cdot> []]}, nxt = \<Delta>, eps = \<E>\<rparr>"


locale ipda = Extended_Cfg G for G :: "('n::fresh0, 't) Cfg" +
  fixes M :: "(('n, 't) item, 't) gpda"
  assumes ipda: "M = Extended_Cfg.IPDA G"
begin

subsection \<open>Basic Properties\<close>

lemma states_ipda [simp]:
  "states M = It G'"
  using ipda unfolding IPDA_def by (meson gpda.select_convs(1))

lemma init_ipda [simp]:
  "init M = [S' \<rightarrow> [] \<cdot> [Nt S]]"
  using ipda unfolding IPDA_def by (meson gpda.select_convs(2))

abbreviation (input) "final_state \<equiv> [S' \<rightarrow> [Nt S] \<cdot> []]"

lemma final_ipda [simp]:
  "final M = {final_state}"
  using ipda unfolding IPDA_def by (meson select_convs(3))

lemma final_state_in_It [simp]:
  "final_state \<in> It G'"
  unfolding It_def G'_def by auto

lemma nxt_ipda [simp]:
  "nxt M = {([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], a, [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]])|X \<beta> a \<gamma>. (X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'}"
  using ipda unfolding IPDA_def by (meson select_convs(4))

lemma nxt_nempty_imp_Tm_eq:
  assumes "(ps, a, qs) \<in> nxt M"
  obtains X \<beta> \<gamma> where "ps = [[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]]" "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'"
    "qs = [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]]"
  using assms by auto

lemma eps_ipda [simp]:
  "eps M =  {([[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [Y \<rightarrow> [] \<cdot> \<alpha>] # [[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]])
        | X \<beta> Y \<gamma> \<alpha>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'} \<union> 
        {([[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]])
        | Y \<alpha> X \<beta> \<gamma>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'}"
  using ipda unfolding IPDA_def by (meson select_convs(5))

lemma eps_cases [consumes 1, case_names expand reduce]:
  assumes "(ps, qs) \<in> eps M" 
  obtains X \<beta> Y \<gamma> \<alpha> where "ps = [[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]]" "qs = [[Y \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]]"
    "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" "(Y, \<alpha>) \<in> Prods G'" |
    Y \<alpha> X \<beta> \<gamma> where "ps = [[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]]" "qs =  [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]]"
     "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'" "(Y, \<alpha>) \<in> Prods G'"
  using assms unfolding eps_ipda by auto

lemma in_final_imp_final_state:
  assumes "q \<in> final M"
  shows "q = final_state"
  using assms unfolding IPDA_def S'_def by simp

sublocale gpda M
proof (standard, goal_cases)
  case 1
  then show ?case 
    by (simp add: G'_def IPDA_def in_Prods_imp_in_It ipda)
next
  case 2
  then show ?case 
    using final_state_in_It by simp
next
  case (3 ps a qs)
  with nxt_nempty_imp_Tm_eq obtain X \<beta> \<gamma> where "ps = [[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]]"
    "(X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'" "qs = [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]]" by blast
  with in_Prods_imp_in_It show ?case by force
next
  case (4 ps qs)
  then show ?case 
    using in_Prods_imp_in_It by (cases rule: eps_cases) force+
next
  case 5
  then show ?case using finite_It[OF G'_finite] by simp
qed

corollary gpda_IPDA:
  "gpda IPDA"
  using ipda gpda_axioms by presburger

subsection \<open>Step\<close>

lemma shifting [simp]:
  assumes "(A, \<alpha> @ Tm a # \<beta>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]#\<rho>s, a#u) \<turnstile> ([A \<rightarrow> \<alpha>@[Tm a] \<cdot> \<beta>]#\<rho>s, u)"
proof -
  have "([[A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]], a, [[A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>]]) \<in> nxt M"
    using IPDA_def assms by auto
  then show ?thesis using step_nxt 
    by (metis Cons_eq_appendI append.left_neutral)
qed

lemma reducing [simp]:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([Y \<rightarrow> \<alpha> \<cdot> []]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]#\<rho>, w)"
proof -
  have "([[Y \<rightarrow> \<alpha> \<cdot> []], [X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]] @ \<rho>, w) \<turnstile> ([[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]] @ \<rho>, w)"
    by (rule step_eps) (use assms in fastforce)
  thus ?thesis by simp
qed

lemma expanding:
  assumes "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] \<cdot> \<alpha>]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"
proof -
  have "([[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]] @ \<rho>, w) \<turnstile> ([[Y \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]] @ \<rho>, w)"
    using assms step_eps by fastforce
  thus ?thesis by simp
qed

lemma expanding_singleton:
  assumes "Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<alpha>" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
  shows "([X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w) \<turnstile> ([Y \<rightarrow> [] \<cdot> \<alpha>]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"
  using assms expanding by (simp add: derive_singleton)

lemma step_cases[consumes 1, case_names shift reduce expand, cases set: step]:
  assumes "c0 \<turnstile> c1"
obtains A \<alpha> a \<beta> \<rho> u where 
    "c0 = ([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]#\<rho>, a#u)" "c1 = ([A \<rightarrow> \<alpha>@[Tm a] \<cdot> \<beta>]#\<rho>, u)" |
    Y \<alpha> X \<beta> \<gamma> \<rho> w where
      "c0 = ([Y \<rightarrow> \<alpha> \<cdot> []]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"  "c1 = ([X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]#\<rho>, w)" |
    Y \<alpha> X \<beta> \<gamma> \<rho> w where 
    "c0 = ([X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"  "c1 = ([Y \<rightarrow> [] \<cdot> \<alpha>]#[X \<rightarrow> \<beta> \<cdot> Nt Y#\<gamma>]#\<rho>, w)"
  using assms by cases auto

lemma step_imp_in_Prods:
  assumes "(i # \<rho>, u) \<turnstile> (j # \<sigma>, v)"
  shows "prod_of_item i \<in> Prods G' \<and> prod_of_item j \<in> Prods G'"
  using assms by cases (use assms in fastforce)+

corollary step_imp_in_It:
  assumes "(i # \<rho>, u) \<turnstile> (j # \<sigma>, v)"
  shows "i \<in> It G'" "j \<in> It G'"
  using step_imp_in_Prods[OF assms] in_Prods_iff_in_It by auto

lemma step_imp_not_Nil:
  assumes "(\<rho>, u) \<turnstile> (\<sigma>, v)"
  shows "\<rho> \<noteq> [] \<and> \<sigma> \<noteq> []"
  using assms by cases auto

lemma reducing_imp_in_Prods_G:
  assumes "([Y \<rightarrow> \<alpha> \<cdot> []] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>, u) \<turnstile> ([X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>] # \<rho>, u)"
  shows "(Y, \<alpha>) \<in> Prods G"
  using assms proof cases
  case (reduce Y \<alpha> X \<beta> \<gamma> \<rho> w)
  with step_imp_in_Prods have Prods_G': "(Y, \<alpha>) \<in> Prods G'" "(X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'"
    using assms by fastforce+
  from this(1) show ?thesis proof (cases rule: G'_Prod_cases)
    case init
    with reduce Prods_G' show ?thesis using S'_Prod_notin_G' by simp
  qed (use reduce in simp)
qed simp_all

lemma step_not_expanding_unique:
  assumes "(\<rho>, u) \<turnstile> c0" "(\<rho>, u) \<turnstile> c1"
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]"
  shows "c0 = c1"
  using assms(1) by (cases; use assms(2) in cases, use assms(3) in auto)

lemma step_reaches_final_imp_S:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> @ \<sigma>, u) \<turnstile> (final_state # \<sigma>, v)"
  shows "[A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> = [[S \<rightarrow> \<alpha> \<cdot> []], init M]"
  using assms(1) by cases auto


subsection \<open>Steps\<close>

lemma step_not_expanding_imp_reaches:
  assumes "(\<rho>, u) \<turnstile> c0" "(\<rho>, u) \<turnstile>(Suc n) c1"
    "\<exists>X \<alpha> a \<beta>. hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> []] \<or> hd \<rho> = [X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]"
  shows "c0 \<turnstile>(n) c1"
  using step_not_expanding_unique assms by (metis relpowp_Suc_D2)

lemma completes_Tms:
  "(A, \<alpha> @ map Tm u @ \<beta>) \<in> Prods G' 
    \<Longrightarrow> ([A \<rightarrow> \<alpha> \<cdot> map Tm u @ \<beta>]#\<rho>, u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u \<cdot> \<beta>]#\<rho>, v)"
proof (induction u arbitrary: \<alpha>)
  case (Cons a u)
  hence "([A \<rightarrow> \<alpha> \<cdot> map Tm (a # u) @ \<beta>] #  \<rho>, (a # u) @ v) 
        \<turnstile> ([A \<rightarrow> \<alpha> @ [Tm a] \<cdot> map Tm u @ \<beta>] # \<rho>, u @ v)"
    by simp
  also note Cons(1)[of "\<alpha>@[Tm a]"] 
  finally show ?case using Cons by auto
qed simp

lemma steps_in_It:
  "\<lbrakk>(i # \<rho>, u) \<turnstile>* (j # \<sigma>, v); i \<in> It G'\<rbrakk> \<Longrightarrow> j \<in> It G'"
  by (induction "j # \<sigma>" v arbitrary: j \<sigma> rule: rtranclp_induct2)
    (simp, metis neq_Nil_conv step_imp_in_It(2) step_imp_not_Nil)

lemma steps_neq_in_It:
  assumes "(i # \<rho>, u) \<turnstile>* (j # \<sigma>, v)" "(i # \<rho>, u) \<noteq> (j # \<sigma>, v)"
  shows "i \<in> It G' \<and> j \<in> It G'"
  using assms(1) proof (cases rule: converse_rtranclpE)
  case (step y)
  from this(1) step_imp_in_It(1) have "i \<in> It G'" 
    by (metis list.exhaust old.prod.exhaust step_imp_not_Nil)
  then show ?thesis using steps_in_It step assms(1) by blast
qed (use assms(2) in simp)

corollary steps_shift_decomp:
  assumes "(\<rho>, u @ v) \<turnstile>* ([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<sigma>, a # v)"
    "([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<sigma>, a # v) \<turnstile> (\<tau>, v)"
  obtains x where "u = x @ [a]"
  using reachable_imp_substring[OF assms(1)] by auto

lemma complete_S'_step_impossible:
  assumes "([S' \<rightarrow> \<alpha> \<cdot> []] # \<rho>, w) \<turnstile> c"
  shows False
  using assms S'_Prod_notin_G' assms step_imp_in_Prods by cases force+

subsection \<open>Language Equivalence\<close>

lemma derives_imp_completes:
  assumes "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w"
    "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'"
  shows "([A \<rightarrow> \<alpha> \<cdot> \<beta>@\<gamma>] # \<rho>, w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> \<cdot> \<gamma>] # \<rho>, x)"
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
      with deriven_decomp_less obtain \<delta>\<^sub>1 i u X j v \<delta>\<^sub>2 k y where
        \<beta>_decomp:
        "\<beta> = \<delta>\<^sub>1 @ Nt X # \<delta>\<^sub>2"
        "Prods G' \<turnstile> \<delta>\<^sub>1 \<Rightarrow>(i) map Tm u" "Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v" 
        "Prods G' \<turnstile> \<delta>\<^sub>2 \<Rightarrow>(k) map Tm y" "w = u @ v @ y" "i + j + k = n" "j > 0" 
        using less(3) by (smt (verit, best))
      hence leqs: "i < n" "k < n" by auto
      have first: "([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] # \<rho>, w @ x) 
              \<turnstile>* ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 \<cdot> Nt X # \<delta>\<^sub>2 @ \<gamma>] # \<rho>, v @ y @ x)"
        (is "_ \<turnstile>* (?\<sigma>, _)")
        using less(1)[OF leqs(1) _ \<beta>_decomp(2), of _ _ "Nt X # \<delta>\<^sub>2 @ \<gamma>" _ "v @ y @ x"]
          \<beta>_decomp less.prems(1) by simp
      have last: "([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] \<cdot> \<delta>\<^sub>2 @ \<gamma>] # \<rho>, y @ x) 
                  \<turnstile>* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] # \<rho>, x)"
        using less(1)[OF leqs(2) _ \<beta>_decomp(4), of _ "\<alpha> @ \<delta>\<^sub>1 @ [Nt X]"] \<beta>_decomp(1) less.prems(1) by simp
      show ?thesis 
      proof (cases "j = n")
        case True
        with \<beta>_decomp have Tms: "i = 0" "k = 0" "\<delta>\<^sub>1 = map Tm u" "\<delta>\<^sub>2 = map Tm y"
          by auto
        from True \<beta>_decomp(6,7) Suc obtain \<beta>' where m_steps:
          "Prods G' \<turnstile> [Nt X] \<Rightarrow> \<beta>'" "Prods G' \<turnstile> \<beta>' \<Rightarrow>(m) map Tm v"
          using \<beta>_decomp(3) by (meson relpowp_Suc_D2)
        note first
        also from expanding_singleton m_steps(1) have 
          "(?\<sigma>, v @ y @ x) \<turnstile> ([X \<rightarrow> [] \<cdot> \<beta>'] # ?\<sigma>, v @ y @ x)"
          using \<beta>_decomp(1)  less.prems(1) by force
        also from less.IH[of m X "[]" \<beta>' "[]" v ?\<sigma> "y@x"] derive.cases[OF m_steps(1)] m_steps(2)
        have "... \<turnstile>* ([X \<rightarrow> \<beta>' \<cdot> []] # ?\<sigma>, y @ x)" using Suc 
          by (metis append.right_neutral append_Nil derive_singleton lessI m_steps(1)
              sym.inject(1))
        also have "... \<turnstile> ([A \<rightarrow> \<alpha> @ \<delta>\<^sub>1 @ [Nt X] \<cdot> \<delta>\<^sub>2 @ \<gamma>] # \<rho>, y @ x)"
          by (smt (verit, best) Cons_eq_appendI \<beta>_decomp(1) append.assoc derive_singleton ipda.reducing
              ipda_axioms less.prems(1) m_steps(1) sym.inject(1))
        finally show ?thesis using last by auto
      next
        case False
        hence "j < n" using \<beta>_decomp by linarith
        then show ?thesis
          using first last \<beta>_decomp(3) less.prems(1)
          by (smt (verit, ccfv_threshold) \<beta>_decomp(1,3) append.assoc append_Cons append_self_conv2 less.IH
              rtranclp_trans)
      qed
    qed (use completes_Tms in simp)
  qed
qed

lemma reaches_final_imp_completes:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>(n) ([final_state], [])"
  shows  
    "\<exists>v i j. (([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>(i) ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v)) \<and>
    (([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v) \<turnstile>(j) ([final_state], [])) \<and> i + j = n"
using assms proof (induction n arbitrary: A \<alpha> \<beta> \<rho> u rule: less_induct)
  case (less n)
  then show ?case proof (cases n)
    case (Suc m)
    with less obtain c where stepm: "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile> c" "c \<turnstile>(m) ([final_state], [])"
      by (meson relpowp_Suc_D2)
    from this(1) show ?thesis proof cases
      case (shift _ _ a \<beta>' _ u')
      with less stepm Suc obtain w i j where "c \<turnstile>(i) ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, w)"
        "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, w) \<turnstile>(j) ([final_state], [])" "i + j = m"
        by (smt (verit, ccfv_threshold) append.assoc append_Cons append_Nil item.inject lessI
            list.inject prod.inject)
      with stepm show ?thesis 
        by (metis (no_types, lifting) Suc add_Suc relpowp_Suc_I2)
    next 
      case reduce
      then show ?thesis using Suc less 
        by (smt (verit, del_insts) add.left_neutral append.right_neutral item.inject list.inject
            prod.inject relpowp_0_E relpowp_Suc_0 relpowp_Suc_E stepm(1))
    next
      case (expand Y \<gamma> _ _ \<delta> _ _)
      with less stepm Suc obtain w i j where ij: "c \<turnstile>(i) ([Y \<rightarrow> \<gamma> \<cdot> []] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w)"
        "([Y \<rightarrow> \<gamma> \<cdot> []] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>(j) ([final_state], [])" "i + j = m"
        by (smt (verit, del_insts) lessI prod.inject self_append_conv2)
      then obtain k c' where Suc_k: "j = Suc k" "([Y \<rightarrow> \<gamma> \<cdot> []] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile> c'"
        "c' \<turnstile>(k) ([final_state], [])" 
        by (cases j) (simp, metis ij(2) relpowp_Suc_D2)
      from Suc_k(2) show ?thesis 
      proof cases
        case (reduce Z _ _ _ \<zeta>)
        with Suc_k(1,3) ij(3) Suc less obtain m' n' x where m'n':
          "c' \<turnstile>(m') ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, x)" 
          "([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, x) \<turnstile>(n') ([final_state], [])" "m' + n' = k" 
          by (smt (verit, ccfv_threshold) Suc_lessD append.assoc append_Cons append_Nil item.inject
              less_add_Suc2 list.inject prod.inject)
        note stepm(1) also note ij(1) also note Suc_k(2) also note m'n'(1)
        finally show ?thesis using ij Suc_k m'n' Suc by force
      qed simp_all
    qed
  qed (use less in auto)
qed


lemma reaches_final_imp_last_is_init_or_final:
  "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>* ([final_state], []) \<Longrightarrow> 
  last ([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>) = init M \<or> last ([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>) = final_state"
proof (induction "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w)" arbitrary: A \<alpha> \<beta> \<rho> w rule: converse_rtranclp_induct)
  case (step z)
  from this(1) show ?case 
    using step by cases auto
qed simp

lemma invariant:
  assumes "([init M], u@v) \<turnstile>* (rev \<rho>, v)"
  shows "Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u"
proof -
  from assms obtain n where "([init M], u@v) \<turnstile>(n) (rev \<rho>, v)"
    using rtranclp_imp_relpowp by fast
  then show ?thesis
  proof (induction n arbitrary:u v \<rho>)
    case (Suc n)
    then obtain \<sigma> w where n_steps: "([init M], u @ v) \<turnstile>(n) (rev \<sigma>, w)" "(rev \<sigma>, w) \<turnstile> (rev \<rho>, v)"
      by (metis relpowp_Suc_E rev_swap surj_pair)
    from this(2) show ?case 
    proof (cases rule: step_cases)
      case (shift A \<alpha> a \<beta> \<tau> x)
      with steps_shift_decomp n_steps(1)[THEN relpowp_imp_rtranclp]
      obtain y where u_decomp: "u = y @ [a]" "w = a # v" 
        using n_steps(2) by (metis prod.inject)
      with Suc.IH[of y "a#v"] n_steps(1) have derives_y: "Prods G \<turnstile> hist \<sigma> \<Rightarrow>* map Tm y"
        by simp
      moreover have "hist \<rho> = hist \<sigma> @ [Tm a]" using shift unfolding hist_defs by simp
      ultimately show ?thesis using derives_append[OF derives_y] u_decomp by simp
    next
      case (reduce Y \<alpha> X \<beta> \<gamma> \<tau> x)
      have "Prods G \<turnstile> hist \<rho> \<Rightarrow> hist \<sigma>"
      proof -
        from n_steps(2)[unfolded reduce] have Y_prod: "(Y, \<alpha>) \<in> Prods G" 
          using reducing_imp_in_Prods_G by simp 
        from reduce have "hist \<rho> = hist (rev \<tau>) @ \<beta> @ [Nt Y]" by simp
        also have "Prods G \<turnstile> ... \<Rightarrow> hist (rev \<tau>) @ \<beta> @ \<alpha>"
          using Y_prod[THEN derive.intros, of "hist (rev \<tau>) @ \<beta>" "[]"] by simp
        also have "... = hist \<sigma>" using reduce by auto
        finally show ?thesis .
      qed
      also from reduce n_steps(1) Suc.IH have "Prods G \<turnstile> ... \<Rightarrow>* map Tm u" by blast
      finally show ?thesis .
    next
      case (expand Y \<alpha> X \<beta> \<gamma> \<tau> x)
      with n_steps(1) Suc.IH show ?thesis by fastforce
    qed
  qed (simp add: hist_defs)
qed

lemma Lang_subst_Lang_G:
  "Lang \<subseteq> LangS G"
proof 
  fix w
  assume "w \<in> Lang"
  hence "([gpda.init M], w) \<turnstile>* ([final_state], [])" unfolding Lang_def
    by auto
  with invariant[of w "[]" "[final_state]"] show "w \<in> LangS G" 
    using G'_derives_from_S_imp_in_Lang G_derives_imp_G'_derives Lang_preserved by force
qed

lemma Lang_G_subst_Lang: 
  "LangS G \<subseteq> Lang"
  using Lang_preserved G'_def G_derives_imp_G'_derives 
    derives_imp_completes[of _ _ S' "[]" "[]" "[]" "[]"] 
  unfolding Lang_def Context_Free_Grammar.Lang_def by auto

theorem Lang_eq_Lang_G:
  "Lang = LangS G"
  using Lang_subst_Lang_G Lang_G_subst_Lang by order

lemma deriver_imp_IPDA_comp:
  assumes
    "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r \<alpha>@\<beta>"
    "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v"
  shows
    "([[S' \<rightarrow> \<alpha> \<cdot> \<beta>]], v) \<turnstile>* ([final_state], [])"
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
        Lang_eq_Lang_G Lang_preserved hist_singleton rtrancl_refl init_ipda ipda 
      using in_final_imp_final_state mem_Collect_eq by auto
  qed
qed

end
end
