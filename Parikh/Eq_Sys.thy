theory Eq_Sys
  imports
    "Lfun"
    "Parikh_Img"
    "../CFG"
    "../CFL"
begin

(* TODO: remove unnecessary definitions and rename *)

text \<open>In his proof, Pilling uses the fact that each CFG has an associated system of equations such
that the CFG is the system's minimal solution. In this file, we will introduce for a given CFG two
equation systems - one which assumes that the alphabet is commutative, i.e. only considers
the languages' parikh images, and one which does not make this assumption - and show that the CFG
is indeed the minimal solution of both.\<close>


section \<open>systems of equations\<close>

text \<open>Given an system of equations
\<open>X\<^sub>0 \<supseteq> r\<^sub>0, X\<^sub>1 \<supseteq> r\<^sub>1, X\<^sub>2 \<supseteq> r\<^sub>2, \<dots>\<close> or \<open>\<Psi> X\<^sub>0 \<supseteq> \<Psi> r\<^sub>0, \<Psi> X\<^sub>1 \<supseteq> \<Psi> r\<^sub>1, \<Psi> X\<^sub>2 \<supseteq> \<Psi> r\<^sub>2, \<dots>\<close>
(depending on the context), we represent it as a list of of language functions where we identify
each of the variables \<open>X\<^sub>0, X\<^sub>1, X\<^sub>2, \<dots>\<close>, by its integer, i.e. \<open>Var i\<close> denotes the variable \<open>X\<^sub>i\<close>.
The \<open>i\<close>-th item of the list then represents the right-hand side \<open>r\<^sub>i\<close> of the \<open>i\<close>-th equation.\<close>

type_synonym 'a eq_sys = "'a rlexp list"


subsection \<open>system of equations without Parikh images\<close>

text \<open>Now we can define what it means for a valuation \<open>v\<close> to solve the classic system of equations,
i.e. the one without Parikh images:\<close>
definition solves_ineq_sys :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_ineq_sys sys v \<equiv> \<forall>i < length sys. eval (sys ! i) v \<subseteq> v i"

(* solves equation with = *)
definition solves_eq_sys :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_eq_sys sys v \<equiv> \<forall>i < length sys. eval (sys ! i) v = v i"

text \<open>\<open>sol\<close> is a minimal solution iff it is a solution and there is no smaller solution:\<close>
definition min_sol_ineq_sys :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "min_sol_ineq_sys sys sol \<equiv>
    solves_ineq_sys sys sol \<and> (\<forall>sol'. solves_ineq_sys sys sol' \<longrightarrow> (\<forall>x. sol x \<subseteq> sol' x))"


subsection \<open>System of equations with Parikh images\<close>

text \<open>Now we look at the system of equations where the Parikh image is applied on both sides of
each equation. First, we introduce what it means for a valuation \<open>v\<close> to solve the \<open>x\<close>-th equation:\<close>
(* solves equation with \<subseteq>, only caring about the Parikh image *)
definition solves_ineq_comm :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_ineq_comm x eq v \<equiv> parikh_img (eval eq v) \<subseteq> parikh_img (v x)"

text \<open>A valuation \<open>v\<close> solves the whole system iff it solves all equations:\<close>
(* solves equation system with \<subseteq>, only caring about the Parikh image *)
definition solves_ineq_sys_comm :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_ineq_sys_comm sys v \<equiv> \<forall>i < length sys. solves_ineq_comm i (sys ! i) v"

(* solves equation with =, only caring about the Parikh image*)
definition solves_eq_comm :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_eq_comm x eq v \<equiv> parikh_img (eval eq v) = parikh_img (v x)"

(* solves equation system with =, only caring about the Parikh image *)
definition solves_eq_sys_comm :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "solves_eq_sys_comm sys v \<equiv> \<forall>i < length sys. solves_eq_comm i (sys ! i) v"

text \<open>We introduce partial solutions, i.e. solutions which might depend on one or multiple variables.
They are therefore not represented as valuations, but as language functions (TODO). \<open>sol\<close> is a partial
solution of the \<open>x\<close>-th equation iff it solves the equation independent on the values of the other
variables, i.e. independent on the valuation as long as the valuation and \<open>sol\<close> coincide.
Note that \<open>sol\<close> might depend on the variable \<open>x\<close> (we will deal with this problem later)\<close>
definition partial_sol_ineq :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> 'a rlexp \<Rightarrow> bool" where
  "partial_sol_ineq x eq sol \<equiv> \<forall>v. v x = eval sol v \<longrightarrow> solves_ineq_comm x eq v"

text \<open>We generalize this to partial solutions of whole systems of equations:
\<open>sols\<close> maps each variable \<open>i\<close> to a language function (TODO) representing the partial solution
of the \<open>i\<close>-th equation (Note that \<open>sols\<close> is defined on all natural numbers, though).
\<open>sols\<close> is a partial solution of the whole system iff all valuations coinciding with \<open>sols\<close> solve
the system of equations:\<close>
definition solution_ineq_sys :: "'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a rlexp) \<Rightarrow> bool" where
  "solution_ineq_sys sys sols \<equiv> \<forall>v. (\<forall>x. v x = eval (sols x) v) \<longrightarrow> solves_ineq_sys_comm sys v"

text \<open>Given a system of equations \<open>sys\<close>, \<open>sols\<close> is a minimal partial solution of the first \<open>n\<close>
equations of the system iff the following conditions are satisfied:
1. \<open>sols\<close> is a partial solution of the system's first \<open>n\<close> equations
2. \<open>sols\<close> does not assign a proper partial solution to the remaining equations,
   i.e. \<open>sols i = Var i\<close> for \<open>i \<ge> n\<close>
3. No language function (TODO) in \<open>sols\<close> depends on variables smaller than \<open>n\<close>.
   Furthermore, the partial solution of no equation depends on variables not occurring in the equation system
4. There is no partial solution smaller than \<open>sols\<close> which solves all of the first \<open>n\<close> equations\<close>
definition partial_min_sol_ineq_sys :: "nat \<Rightarrow> 'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a rlexp) \<Rightarrow> bool" where
  "partial_min_sol_ineq_sys n sys sols \<equiv>
    solution_ineq_sys (take n sys) sols \<and>
    (\<forall>i \<ge> n. sols i = Var i) \<and>
    (\<forall>i < n. \<forall>x \<in> vars (sols i). x \<ge> n \<and> x < length sys) \<and>
    (\<forall>sols' v'. (\<forall>x. v' x = eval (sols' x) v')
                  \<and> solves_ineq_sys_comm (take n sys) v'
                  \<longrightarrow> (\<forall>i. parikh_img (eval (sols i) v') \<subseteq> parikh_img (v' i)))"


text \<open>Given the \<open>x\<close>-th equation \<open>eq\<close>, \<open>sol\<close> is a minimal partial solution of this equation iff
1. \<open>sol\<close> is a partial solution of \<open>eq\<close>,
2. \<open>sol\<close> is a proper partial solution (i.e. it does not depend on \<open>x\<close>) and only depends on variables
   occurring in the equation \<open>eq\<close> and
3. no partial solution of the equation \<open>eq\<close> is smaller than \<open>sol\<close>\<close>
definition partial_min_sol_one_ineq :: "nat \<Rightarrow> 'a rlexp \<Rightarrow> 'a rlexp \<Rightarrow> bool" where
  "partial_min_sol_one_ineq x eq sol \<equiv>
    partial_sol_ineq x eq sol \<and>
    vars sol \<subseteq> vars eq - {x} \<and>
    (\<forall>sol' v'. solves_ineq_comm x eq v' \<and> v' x = eval sol' v'
               \<longrightarrow> parikh_img (eval sol v') \<subseteq> parikh_img (v' x))"


text \<open>\<open>sol\<close> is a minimal solution of the system \<open>sys\<close> of equations iff it is a solution
and there is no smaller solution:\<close>
definition min_sol_ineq_sys_comm :: "'a eq_sys \<Rightarrow> 'a valuation \<Rightarrow> bool" where
  "min_sol_ineq_sys_comm sys sol \<equiv>
    solves_ineq_sys_comm sys sol \<and>
    (\<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. parikh_img (sol x) \<subseteq> parikh_img (sol' x)))"


text \<open>Substitution into each equation of a system:\<close>
definition subst_sys :: "(nat \<Rightarrow> 'a rlexp) \<Rightarrow> 'a eq_sys \<Rightarrow> 'a eq_sys" where
  "subst_sys \<equiv> map \<circ> subst"

lemma subst_sys_subst:
  assumes "i < length sys"
  shows "(subst_sys s sys) ! i = subst s (sys ! i)"
  unfolding subst_sys_def by (simp add: assms)


text \<open>If the parikh image of two equations \<open>f\<close> and \<open>g\<close> is identical on all valuations, then their
minimal partial solution is identical, too:\<close>
lemma same_min_sol_if_same_parikh_img:
  assumes same_parikh_img: "\<forall>v. parikh_img (eval f v) = parikh_img (eval g v)"
      and same_vars:       "vars f - {x} = vars g - {x}"
      and minimal_sol:     "partial_min_sol_one_ineq x f sol"
    shows                  "partial_min_sol_one_ineq x g sol"
proof -
  from minimal_sol have "vars sol \<subseteq> vars g - {x}"
    unfolding partial_min_sol_one_ineq_def using same_vars by blast
  moreover from same_parikh_img minimal_sol have "partial_sol_ineq x g sol"
    unfolding partial_min_sol_one_ineq_def partial_sol_ineq_def solves_ineq_comm_def by simp
  moreover from same_parikh_img minimal_sol have "\<forall>sol' v'. solves_ineq_comm x g v' \<and> v' x = eval sol' v'
               \<longrightarrow> parikh_img (eval sol v') \<subseteq> parikh_img (v' x)"
    unfolding partial_min_sol_one_ineq_def solves_ineq_comm_def by blast
  ultimately show ?thesis unfolding partial_min_sol_one_ineq_def by fast
qed



section \<open>CFG as minimal solution of equation system\<close>

text \<open>We show that each CFG induces a system of equations such that the CFG's language is the
minimal solution of this system\<close>

definition bij_Nt_Var :: "'n set \<Rightarrow> (nat \<Rightarrow> 'n) \<Rightarrow> ('n \<Rightarrow> nat) \<Rightarrow> bool" where
  "bij_Nt_Var A \<gamma> \<gamma>' \<equiv> bij_betw \<gamma> {..< card A} A \<and> bij_betw \<gamma>' A {..< card A}
                          \<and> (\<forall>x \<in> {..< card A}. \<gamma>' (\<gamma> x) = x) \<and> (\<forall>y \<in> A. \<gamma> (\<gamma>' y) = y)"

lemma exists_bij_Nt_Var: "finite A \<Longrightarrow> \<exists>\<gamma> \<gamma>'. bij_Nt_Var A \<gamma> \<gamma>'"
proof -
  assume "finite A"
  then have "\<exists>\<gamma>. bij_betw \<gamma> {..< card A} A" by (simp add: bij_betw_iff_card)
  then obtain \<gamma> where 1: "bij_betw \<gamma> {..< card A} A" by blast
  let ?\<gamma>' = "the_inv_into {..< card A} \<gamma>"
  from the_inv_into_f_f 1 have 2: "\<forall>x \<in> {..< card A}. ?\<gamma>' (\<gamma> x) = x" unfolding bij_betw_def by fast
  from bij_betw_the_inv_into[OF 1] have 3: "bij_betw ?\<gamma>' A {..< card A}" by blast
  with 1 f_the_inv_into_f_bij_betw have 4: "\<forall>y \<in> A. \<gamma> (?\<gamma>' y) = y" by metis
  from 1 2 3 4 show ?thesis unfolding bij_Nt_Var_def by blast
qed


definition rlexp_sym :: "('n \<Rightarrow> nat) \<Rightarrow> ('n, 't) sym \<Rightarrow> 't rlexp" where
  "rlexp_sym \<gamma>' s = (case s of Tm a \<Rightarrow> Const {[a]} | Nt A \<Rightarrow> Var (\<gamma>' A))"

definition rlexp_concats :: "'a rlexp list \<Rightarrow> 'a rlexp" where
  "rlexp_concats fs = foldr Concat fs (Const {[]})"

definition rlexp_syms :: "('n \<Rightarrow> nat) \<Rightarrow> ('n, 't) syms \<Rightarrow> 't rlexp" where
  "rlexp_syms \<gamma>' w = rlexp_concats (map (rlexp_sym \<gamma>') w)"


(* Some auxiliary lemmas *)

lemma subst_lang_mono: "mono (subst_lang P)"
  using mono_if_omega_cont[OF omega_cont_Lang_lfp] by blast

lemma CFL_Lang_not_in_Prods_aux:
  assumes "A \<notin> Nts P"
    shows "((subst_lang P)^^n) (\<lambda>A. {}) A = {}"
proof (cases n)
  case (Suc nat)
  from assms have "Rhss P A = {}" unfolding Nts_def Rhss_def by blast
  with Suc show ?thesis unfolding subst_lang_def by simp
qed auto

lemma CFL_Lang_not_in_Prods: "A \<notin> Nts P \<Longrightarrow> Lang_lfp P A = {}"
  by (simp add: Lang_lfp_eq_Lang Lang_empty_if_notin_Lhss Nts_Lhss_Rhs_Nts)


locale CFG_eq_sys =
  fixes P :: "('n,'a) Prods"
  fixes S :: 'n
  fixes \<gamma> :: "nat \<Rightarrow> 'n"
  fixes \<gamma>' :: "'n \<Rightarrow> nat"
  assumes finite_P: "finite P"
  assumes bij_\<gamma>_\<gamma>':  "bij_Nt_Var (Nts P) \<gamma> \<gamma>'"
begin

abbreviation "CFG_sys sys \<equiv>
  length sys = card (Nts P) \<and>
    (\<forall>i < card (Nts P). reg_eval (sys ! i) \<and> (\<forall>x \<in> vars (sys ! i). x < card (Nts P))
                        \<and> (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A)
                            \<longrightarrow> eval (sys ! i) s = subst_lang P L (\<gamma> i)))"

abbreviation "sol \<equiv> \<lambda>i. if i < card (Nts P) then Lang_lfp P (\<gamma> i) else {}"

lemma rlexp_sym_reg: "reg_eval (rlexp_sym \<gamma>' s)"
unfolding rlexp_sym_def proof (induction s)
  case (Tm x)
  have "regular_lang {[x]}" by (meson lang.simps(3))
  then show ?case by auto
qed auto

lemma rlexp_concats_reg:
  assumes "\<forall>f \<in> set fs. reg_eval f"
    shows "reg_eval (rlexp_concats fs)"
  using assms epsilon_regular unfolding rlexp_concats_def by (induction fs) auto

lemma rlexp_syms_reg: "reg_eval (rlexp_syms \<gamma>' w)"
proof -
  from rlexp_sym_reg have "\<forall>s \<in> set w. reg_eval (rlexp_sym \<gamma>' s)" by blast
  with rlexp_concats_reg show ?thesis unfolding rlexp_syms_def
    by (metis (no_types, lifting) image_iff list.set_map)
qed


lemma rlexp_sym_vars_Nt:
  assumes "s (\<gamma>' A) = L A"
    shows "vars (rlexp_sym \<gamma>' (Nt A)) = {\<gamma>' A}"
  using assms unfolding rlexp_sym_def by simp

lemma rlexp_sym_vars_Tm: "vars (rlexp_sym \<gamma>' (Tm x)) = {}"
  unfolding rlexp_sym_def by simp

lemma rlexp_concats_vars: "vars (rlexp_concats fs) = \<Union>(vars ` set fs)"
  unfolding rlexp_concats_def by (induction fs) simp_all

(* it even holds equality, but we will not need it *)
lemma insts'_vars: "vars (rlexp_syms \<gamma>' w) \<subseteq> \<gamma>' ` nts_syms w"
proof
  fix x
  assume "x \<in> vars (rlexp_syms \<gamma>' w)"
  with rlexp_concats_vars have "x \<in> \<Union>(vars ` set (map (rlexp_sym \<gamma>') w))"
    unfolding rlexp_syms_def by blast
  then obtain f where *: "f \<in> set (map (rlexp_sym \<gamma>') w) \<and> x \<in> vars f" by blast
  then obtain s where **: "s \<in> set w \<and> rlexp_sym \<gamma>' s = f" by auto
  with * rlexp_sym_vars_Tm obtain A where ***: "s = Nt A" by (metis empty_iff sym.exhaust)
  with ** have ****: "A \<in> nts_syms w" unfolding nts_syms_def by blast
  with rlexp_sym_vars_Nt have "vars (rlexp_sym \<gamma>' (Nt A)) = {\<gamma>' A}" by blast
  with * ** *** **** show "x \<in> \<gamma>' ` nts_syms w" by blast
qed


lemma rlexp_sym_inst_Nt:
  assumes "v (\<gamma>' A) = L A"
    shows "eval (rlexp_sym \<gamma>' (Nt A)) v = inst_sym L (Nt A)"
  using assms unfolding rlexp_sym_def inst_sym_def by force

lemma rlexp_sym_inst_Tm: "eval (rlexp_sym \<gamma>' (Tm a)) v = inst_sym L (Tm a)"
  unfolding rlexp_sym_def inst_sym_def by force

lemma rlexp_concats_concats:
  assumes "length fs = length Ls"
      and "\<forall>i < length fs. eval (fs ! i) v = Ls ! i"
    shows "eval (rlexp_concats fs) v = concats Ls"
using assms proof (induction fs arbitrary: Ls)
  case Nil
  then show ?case unfolding rlexp_concats_def concats_def by simp
next
  case (Cons f1 fs)
  then obtain L1 Lr where *: "Ls = L1#Lr" by (metis length_Suc_conv)
  with Cons have "eval (rlexp_concats fs) v = concats Lr" by fastforce
  moreover from Cons.prems * have "eval f1 v = L1" by force
  ultimately show ?case unfolding rlexp_concats_def concats_def by (simp add: "*")
qed

lemma rlexp_syms_insts:
  assumes "\<forall>A \<in> nts_syms w. v (\<gamma>' A) = L A"
    shows "eval (rlexp_syms \<gamma>' w) v = inst_syms L w"
proof -
  have "\<forall>i < length w. eval (rlexp_sym \<gamma>' (w!i)) v = inst_sym L (w!i)"
  proof (rule allI, rule impI)
    fix i
    assume "i < length w"
    then show "eval (rlexp_sym \<gamma>' (w ! i)) v = inst_sym L (w ! i)"
      using assms proof (induction "w!i")
      case (Nt A)
      then have "v (\<gamma>' A) = L A" unfolding nts_syms_def by force
      with rlexp_sym_inst_Nt Nt show ?case by metis
    next
      case (Tm x)
      with rlexp_sym_inst_Tm show ?case by metis
    qed
  qed
  then show ?thesis unfolding rlexp_syms_def inst_syms_def using rlexp_concats_concats
    by (metis (mono_tags, lifting) length_map nth_map)
qed


lemma subst_lang_rlexp:
  "\<exists>eq. reg_eval eq \<and> vars eq \<subseteq> \<gamma>' ` Nts P
         \<and> (\<forall>v L. (\<forall>A \<in> Nts P. v (\<gamma>' A) = L A) \<longrightarrow> eval eq v = subst_lang P L A)"
proof -
  let ?Insts = "(rlexp_syms \<gamma>') ` (Rhss P A)"
  from finite_Rhss[OF finite_P] have "finite ?Insts" by simp
  moreover from rlexp_syms_reg have "\<forall>f \<in> ?Insts. reg_eval f" by blast
  ultimately obtain eq where *: "reg_eval eq \<and> \<Union>(vars ` ?Insts) = vars eq
                                  \<and> (\<forall>v. (\<Union>f \<in> ?Insts. eval f v) = eval eq v)"
    using finite_Union_regular by metis

  moreover have "vars eq \<subseteq> \<gamma>' ` Nts P"
  proof
    fix x
    assume "x \<in> vars eq"
    with * obtain f where **: "f \<in> ?Insts \<and> x \<in> vars f" by blast
    then obtain w where ***: "w \<in> Rhss P A \<and> f = rlexp_syms \<gamma>' w" by blast
    with ** insts'_vars have "x \<in> \<gamma>' ` nts_syms w" by auto
    with *** show "x \<in> \<gamma>' ` Nts P" unfolding Nts_def Rhss_def by blast
  qed

  moreover have "\<forall>v L. (\<forall>A \<in> Nts P. v (\<gamma>' A) = L A) \<longrightarrow> eval eq v = subst_lang P L A"
  proof (rule allI | rule impI)+
    fix v :: "nat \<Rightarrow> 'a lang" and L :: "'n \<Rightarrow> 'a lang"
    assume state_L: "\<forall>A \<in> Nts P. v (\<gamma>' A) = L A"

    have "\<forall>w \<in> Rhss P A. eval (rlexp_syms \<gamma>' w) v = inst_syms L w"
    proof
      fix w
      assume "w \<in> Rhss P A"
      with state_L Nts_nts_syms have "\<forall>A \<in> nts_syms w. v (\<gamma>' A) = L A" by fast
      from rlexp_syms_insts[OF this] show "eval (rlexp_syms \<gamma>' w) v = inst_syms L w" by blast
    qed

    then have "subst_lang P L A = (\<Union>f \<in> ?Insts. eval f v)" unfolding subst_lang_def by auto
    with * show "eval eq v = subst_lang P L A" by auto
  qed

  ultimately show ?thesis by auto
qed


lemma CFG_as_eq_sys: "\<exists>sys. CFG_sys sys"
proof -
  from bij_\<gamma>_\<gamma>' have *: "\<And>eq. vars eq \<subseteq> \<gamma>' ` Nts P \<Longrightarrow> \<forall>x \<in> vars eq. x < card (Nts P)"
    unfolding bij_Nt_Var_def bij_betw_def by auto
  from subst_lang_rlexp have "\<forall>A. \<exists>eq. reg_eval eq \<and> vars eq \<subseteq> \<gamma>' ` Nts P \<and>
                             (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A) \<longrightarrow> eval eq s = subst_lang P L A)"
    by blast
  with bij_\<gamma>_\<gamma>' * have "\<forall>i < card (Nts P). \<exists>eq. reg_eval eq \<and> (\<forall>x \<in> vars eq. x < card (Nts P))
                    \<and> (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A) \<longrightarrow> eval eq s = subst_lang P L (\<gamma> i))"
    unfolding bij_Nt_Var_def by metis
  with Skolem_list_nth[where P="\<lambda>i eq. reg_eval eq \<and> (\<forall>x \<in> vars eq. x < card (Nts P))
                       \<and> (\<forall>s L. (\<forall>A \<in> Nts P. s (\<gamma>' A) = L A) \<longrightarrow> eval eq s = subst_lang P L (\<gamma> i))"]
    show ?thesis by blast
qed

lemma CFG_sys_CFL_is_sol:
  assumes "CFG_sys sys"
  shows "solves_ineq_sys sys sol"
unfolding solves_ineq_sys_def proof (rule allI, rule impI)
  fix i
  assume "i < length sys"
  with assms have "i < card (Nts P)" by argo
  from bij_\<gamma>_\<gamma>' have *: "\<forall>A \<in> Nts P. sol (\<gamma>' A) = Lang_lfp P A"
    unfolding bij_Nt_Var_def bij_betw_def by force
  with \<open>i < card (Nts P)\<close> assms have "eval (sys ! i) sol = subst_lang P (Lang_lfp P) (\<gamma> i)"
    by presburger
  with lfp_fixpoint[OF subst_lang_mono] have 1: "eval (sys ! i) sol = Lang_lfp P (\<gamma> i)"
    unfolding Lang_lfp_def by metis

  from \<open>i < card (Nts P)\<close> bij_\<gamma>_\<gamma>' have "\<gamma> i \<in> Nts P"
    unfolding bij_Nt_Var_def using bij_betwE by blast
  with * have "Lang_lfp P (\<gamma> i) = sol (\<gamma>' (\<gamma> i))" by auto
  also have "\<dots> = sol i" using bij_\<gamma>_\<gamma>' \<open>i < card (Nts P)\<close> unfolding bij_Nt_Var_def by auto
  finally show "eval (sys ! i) sol \<subseteq> sol i" using 1 by blast
qed

lemma CFG_sys_CFL_is_min_aux:
  assumes "CFG_sys sys"
      and "solves_ineq_sys sys sol'"
    shows "Lang_lfp P \<le> (\<lambda>A. sol' (\<gamma>' A))" (is "_ \<le> ?L'")
proof -
  have "subst_lang P ?L' A \<subseteq> ?L' A" for A
  proof (cases "A \<in> Nts P")
    case True
    with assms(1) bij_\<gamma>_\<gamma>' have "\<gamma>' A < length sys"
      unfolding bij_Nt_Var_def bij_betw_def by fastforce
    with assms(1) bij_\<gamma>_\<gamma>' True have "subst_lang P ?L' A = eval (sys ! \<gamma>' A) sol'"
      unfolding bij_Nt_Var_def by metis
    also from True assms(2) \<open>\<gamma>' A < length sys\<close> bij_\<gamma>_\<gamma>' have "\<dots> \<subseteq> ?L' A"
      unfolding solves_ineq_sys_def bij_Nt_Var_def by blast
    finally show ?thesis .
  next
    case False
    then have "Rhss P A = {}" unfolding Nts_def Rhss_def by blast
    with False show ?thesis unfolding subst_lang_def by simp
  qed
  then have "subst_lang P ?L' \<le> ?L'" by (simp add: le_funI)
  from lfp_lowerbound[of "subst_lang P", OF this] Lang_lfp_def show ?thesis by metis
qed

lemma CFG_sys_CFL_is_min:
  assumes "CFG_sys sys"
      and "solves_ineq_sys sys sol'"
    shows "sol x \<subseteq> sol' x"
proof (cases "x < card (Nts P)")
  case True
  then have "sol x = Lang_lfp P (\<gamma> x)" by argo
  also from CFG_sys_CFL_is_min_aux[OF assms] have "\<dots> \<subseteq> sol' (\<gamma>' (\<gamma> x))" by (simp add: le_fun_def)
  finally show ?thesis using True bij_\<gamma>_\<gamma>' unfolding bij_Nt_Var_def by auto
next
  case False
  then show ?thesis by auto
qed

lemma CFL_is_min_sol:
  "\<exists>sys. (\<forall>eq \<in> set sys. reg_eval eq) \<and> (\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys)
          \<and> min_sol_ineq_sys sys sol"
proof -
  from CFG_as_eq_sys obtain sys where *: "CFG_sys sys" by blast
  then have "length sys = card (Nts P)" by blast
  moreover from * have "\<forall>eq \<in> set sys. reg_eval eq" by (simp add: all_set_conv_all_nth)
  moreover from * \<open>length sys = card (Nts P)\<close> have "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
    by (simp add: all_set_conv_all_nth)
  moreover from CFG_sys_CFL_is_sol[OF *] CFG_sys_CFL_is_min[OF *]
    have "min_sol_ineq_sys sys sol" unfolding min_sol_ineq_sys_def by blast
  ultimately show ?thesis by blast
qed

end


section \<open>Relationship between the system of equations with and the one without Parikh images\<close>

text \<open>To any solution \<open>sol\<close> of a commutative system of equations, there corresponds
a solution to the same non-commutative system which has the same Parikh image as \<open>sol\<close>\<close>
lemma sol_comm_sol:
  assumes sol_is_sol_comm: "solves_ineq_sys_comm sys sol"
  shows   "\<exists>sol'. (\<forall>x. parikh_img (sol x) = parikh_img (sol' x)) \<and> solves_ineq_sys sys sol'"
proof
  let ?sol' = "\<lambda>x. \<Union>(parikh_img_eq_class (sol x))"

  have sol'_sol: "\<forall>x. parikh_img (?sol' x) = parikh_img (sol x)"
      using parikh_img_Union_class by metis

  moreover have "solves_ineq_sys sys ?sol'"
  unfolding solves_ineq_sys_def proof (rule allI, rule impI)
    fix i
    assume "i < length sys"
    with sol_is_sol_comm have "parikh_img (eval (sys ! i) sol) \<subseteq> parikh_img (sol i)"
      unfolding solves_ineq_sys_comm_def solves_ineq_comm_def by blast
    moreover from sol'_sol have "parikh_img (eval (sys ! i) ?sol') = parikh_img (eval (sys ! i) sol)"
      using rlexp_mono_parikh_eq by meson
    ultimately have "parikh_img (eval (sys ! i) ?sol') \<subseteq> parikh_img (sol i)" by simp
    then show "eval (sys ! i) ?sol' \<subseteq> ?sol' i" using subseteq_comm_subseteq by metis
  qed

  ultimately show "(\<forall>x. parikh_img (sol x) = parikh_img (?sol' x)) \<and> solves_ineq_sys sys ?sol'"
    by simp
qed

text \<open>A minimal solution of the non-commutative system of equations is a solution of the
commutative system of equations, as well.\<close>
lemma min_sol_min_sol_comm:
  assumes "min_sol_ineq_sys sys sol"
    shows "min_sol_ineq_sys_comm sys sol"
unfolding min_sol_ineq_sys_comm_def proof
  from assms show "solves_ineq_sys_comm sys sol"
    unfolding min_sol_ineq_sys_def min_sol_ineq_sys_comm_def solves_ineq_sys_def
      solves_ineq_sys_comm_def solves_ineq_comm_def by (simp add: parikh_img_mono)

  show " \<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. parikh_img (sol x) \<subseteq> parikh_img (sol' x))"
  proof (rule allI, rule impI)
    fix sol'
    assume "solves_ineq_sys_comm sys sol'"
    with sol_comm_sol obtain sol'' where sol''_intro:
      "(\<forall>x. parikh_img (sol' x) = parikh_img (sol'' x)) \<and> solves_ineq_sys sys sol''" by meson
    with assms have "\<forall>x. sol x \<subseteq> sol'' x" unfolding min_sol_ineq_sys_def by auto
    with sol''_intro show "\<forall>x. parikh_img (sol x) \<subseteq> parikh_img (sol' x)"
      using parikh_img_mono by metis
  qed
qed

text \<open>All minimal solutions of a commutative system of equations have the same Parikh image\<close>
lemma min_sol_comm_unique:
  assumes sol1_is_min_sol: "min_sol_ineq_sys_comm sys sol1"
      and sol2_is_min_sol: "min_sol_ineq_sys_comm sys sol2"
    shows                  "parikh_img (sol1 x) = parikh_img (sol2 x)"
proof -
  from sol1_is_min_sol sol2_is_min_sol have "parikh_img (sol1 x) \<subseteq> parikh_img (sol2 x)"
    unfolding min_sol_ineq_sys_comm_def by simp
  moreover from sol1_is_min_sol sol2_is_min_sol have "parikh_img (sol2 x) \<subseteq> parikh_img (sol1 x)"
    unfolding min_sol_ineq_sys_comm_def by simp
  ultimately show ?thesis by blast
qed


end
