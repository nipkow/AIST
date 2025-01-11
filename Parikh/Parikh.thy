theory Parikh
  imports 
    "../CFG"
    "../CFL"
    "$AFP/Regular-Sets/Regular_Set"
    "$AFP/Regular-Sets/Regular_Exp"
begin


section \<open>functions of languages\<close>

datatype 'a lfun = V nat
                 | N "'a lang"
                 | Union2 "'a lfun" "'a lfun"
                 | UnionC "nat \<Rightarrow> 'a lfun"
                 | Conc "'a lfun" "'a lfun"
                 | Star "'a lfun"

type_synonym 'a state = "nat \<Rightarrow> 'a lang"

primrec eval :: "'a lfun \<Rightarrow> 'a state \<Rightarrow> 'a lang" where
  "eval (V n) s = s n" |
  "eval (N l) _ = l" |
  "eval (Union2 f g) s = eval f s \<union> eval g s" |
  "eval (UnionC f) s = (\<Union>i. eval (f i) s)" |
  "eval (Conc f g) s = eval f s @@ eval g s" |
  "eval (Star f) s = star (eval f s)"

primrec vars :: "'a lfun \<Rightarrow> nat set" where
  "vars (V n) = {n}" |
  "vars (N _) = {}" |
  "vars (Union2 f g) = vars f \<union> vars g" |
  "vars (UnionC f) = (\<Union>i. vars (f i))" |
  "vars (Conc f g) = vars f \<union> vars g" |
  "vars (Star f) = vars f"

primrec subst :: "'a lfun \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> 'a lfun" where
  "subst (V n) s = s n" |
  "subst (N l) _ = N l" |
  "subst (Union2 f g) s = Union2 (subst f s) (subst g s)" |
  "subst (UnionC f) s = UnionC (\<lambda>i. subst (f i) s)" |
  "subst (Conc f g) s = Conc (subst f s) (subst g s)" |
  "subst (Star f) s = Star (subst f s)"


section \<open>Regular functions\<close>

inductive regular_fun :: "'a lfun \<Rightarrow> bool" where
  Variable:    "regular_fun (V _)" |
  Const:       "regular_lang l \<Longrightarrow> regular_fun (N l)" |
  Union2:      "\<lbrakk> regular_fun f; regular_fun g \<rbrakk> \<Longrightarrow> regular_fun (Union2 f g)" |
  Conc:        "\<lbrakk> regular_fun f; regular_fun g \<rbrakk> \<Longrightarrow> regular_fun (Conc f g)" |
  Star:        "regular_fun f \<Longrightarrow> regular_fun (Star f)"

declare regular_fun.intros [intro]
inductive_cases ConstE [elim]:       "regular_fun (N l)"
inductive_cases Union2E [elim]:      "regular_fun (Union2 f g)"
inductive_cases ConcE [elim]:        "regular_fun (Conc f g)"
inductive_cases StarE [elim]:        "regular_fun (Star f)"


lemma countable_union_finally_empty:
  assumes "\<forall>j>i. f j = {}"
  shows "(\<Union>j. f j) = (\<Union>j\<le>i. f j)"
  sorry


lemma finite_union_regular:
  assumes "\<forall>j\<le>i. regular_fun (f j)"
      and "\<forall>j>i. f j = N {}"
    shows "\<exists>g. regular_fun g \<and> (\<forall>s. eval (UnionC f) s = eval g s)"
using assms proof (induction i arbitrary: f)
  case 0
  then have "eval (UnionC f) s = eval (f 0) s" for s
    using countable_union_finally_empty[of 0 "\<lambda>j. eval (f j) s"] by simp
  with "0.prems" show ?case by blast
next
  case (Suc i)
  let ?f' = "(\<lambda>j. if j \<le> i then f j else N {})"
  from Suc obtain g' where "regular_fun g' \<and> (\<forall>s. eval (UnionC ?f') s = eval g' s)" by fastforce
  moreover with Suc.prems have "eval (UnionC f) s = eval (Union2 g' (f (Suc i))) s" for s
    using countable_union_finally_empty[of "Suc i" "\<lambda>j. eval (f j) s"]
          countable_union_finally_empty[of i "\<lambda>j. eval (?f' j) s"]
    by (simp add: atMost_Suc sup_commute)
  ultimately show ?case using Suc.prems by blast
qed


lemma regular_fun_regular:
  assumes "regular_fun f"
      and "\<And>n. n \<in> vars f \<Longrightarrow> regular_lang (s n)"
    shows "regular_lang (eval f s)"
using assms proof (induction rule: regular_fun.induct)
  case (Union2 f g)
  then obtain r1 r2 where "Regular_Exp.lang r1 = eval f s \<and> Regular_Exp.lang r2 = eval g s" by auto
  then have "Regular_Exp.lang (Plus r1 r2) = eval (Union2 f g) s" by simp
  then show ?case by blast
next
  case (Conc f g)
  then obtain r1 r2 where "Regular_Exp.lang r1 = eval f s \<and> Regular_Exp.lang r2 = eval g s" by auto
  then have "Regular_Exp.lang (Times r1 r2) = eval (Conc f g) s" by simp
  then show ?case by blast
next
  case (Star f)
  then obtain r  where "Regular_Exp.lang r = eval f s" by auto
  then have "Regular_Exp.lang (Regular_Exp.Star r) = eval (Star f) s" by simp
  then show ?case by blast
qed auto


lemma regular_fun_mono:
  assumes "regular_fun f"
  shows "mono (eval f)"
using assms proof (induction rule: regular_fun.induct)
  case (Variable uu)
  then show ?case by (simp add: le_funD ord.mono_on_def)
next
  case (Const l)
  then show ?case by (simp add: ord.mono_on_def)
next
  case (Union2 f g)
  then show ?case by (smt (verit, best) eval.simps(3) ord.mono_on_def sup_mono)
next
  case (Conc f g)
  then show ?case by (simp add: conc_mono ord.mono_on_def)
next
  case (Star f)
  then show ?case
    by (smt (verit, best) dual_order.trans eval.simps(6) in_star_iff_concat monotone_on_def subsetI)
qed


(*lemma regular_fun_mono:
  assumes "regular_fun f"
      and "\<forall>i. s i \<subseteq> s' i"
    shows "eval f s \<subseteq> eval f s'"
using assms proof (induction rule: regular_fun.induct)
  case (Variable uu)
  then show ?case by auto
next
  case (Const l)
  then show ?case by auto
next
  case (Union2 f g)
  then show ?case by auto
next
  case (Conc f g)
  then show ?case by fastforce
next
  case (Star f)
  have "\<And>w. w \<in> star (eval f s) \<Longrightarrow> w \<in> star (eval f s')"
  proof -
    fix w
    assume "w \<in> star (eval f s)"
    then obtain n where "w \<in> (eval f s) ^^ n" using star_pow by auto
    with Star have "w \<in> (eval f s') ^^ n" using funpow_mono sorry
    show "w \<in> star (eval f s')" sorry
  qed
  then show ?case sorry
qed*)


section \<open>Parikh image\<close>

definition parikh_vec :: "'t list \<Rightarrow> ('t \<Rightarrow> nat)" where
  "parikh_vec xs c = length (filter (\<lambda>x. c = x) xs)"

definition parikh_img :: "'t lang \<Rightarrow> ('t \<Rightarrow> nat) set" where
  "parikh_img L = { parikh_vec w | w. w \<in> L }"

(* TODO: really necessary? *)
definition subseteq_comm :: "'t lang \<Rightarrow> 't lang \<Rightarrow> bool" where
  "subseteq_comm L1 L2 \<equiv> parikh_img L1 \<subseteq> parikh_img L2"


section \<open>systems of equations\<close>

type_synonym 'a eq_sys = "'a lfun list"

(* sys independent on variables \<le> n *)
definition indep_ub :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> bool" where
  "indep_ub sys n \<equiv> \<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x > n"

definition indep_lb :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> bool" where
  "indep_lb sys n \<equiv> \<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < n"

definition solves_ineq_sys :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_ineq_sys sys s \<equiv> \<forall>i < length sys. eval (sys ! i) s \<subseteq> s i"

definition solves_eq_sys :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_eq_sys sys s \<equiv> \<forall>i < length sys. eval (sys ! i) s = s i"

definition solves_ineq_sys_comm :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_ineq_sys_comm sys s \<equiv> \<forall>i < length sys. parikh_img (eval (sys ! i) s) \<subseteq> parikh_img (s i)"

definition solves_eq_sys_comm :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_eq_sys_comm sys s \<equiv> \<forall>i < length sys. parikh_img (eval (sys ! i) s) = parikh_img (s i)"

definition sys_subst :: "'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> 'a eq_sys" where
  "sys_subst sys s \<equiv> map (\<lambda>eq. subst eq s) sys"

definition partial_sol :: "'a eq_sys \<Rightarrow> 'a eq_sys \<Rightarrow> bool" where
  "partial_sol sys sol \<equiv> length sol = length sys \<and> indep_ub sol (length sys - 1)
                  \<and> (\<forall>s. solves_eq_sys_comm (sys_subst sys (\<lambda>i. if i < length sys then sol ! i else V i)) s)"


section \<open>The lemma from the paper\<close>

fun g_pre :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g_pre _ _ 0 = N {}" |
  "g_pre f_sys i (Suc n) = subst (f_sys ! i) (\<lambda>j. if j < length f_sys then g_pre f_sys j n else V j)"

definition g :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g f_sys i \<equiv> UnionC (\<lambda>n. g_pre f_sys i n)"

lemma lemma_paper:
  assumes "\<forall>eq \<in> set f_sys. regular_fun eq"
    shows "\<exists>g_sys. length g_sys = length f_sys \<and> indep_ub g_sys (length f_sys - 1)
                \<and> (solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys g_sys s)
                \<and> (solves_eq_sys g_sys s \<longrightarrow> solves_eq_sys f_sys s)"
  sorry


section \<open>The theorem from the paper\<close>

lemma theorem_paper_aux:
  assumes "regular_fun f0"
  shows "\<exists>g0. regular_fun g0 \<and> partial_sol [f0] [g0]
            \<and> (\<forall>g0'. partial_sol [f0] [g0'] \<longrightarrow>
                (\<forall>s. parikh_img (eval g0 s) \<subseteq> parikh_img (eval g0' s)))"
  sorry

lemma theorem_paper:
  assumes "\<forall>eq \<in> set f_sys. regular_fun eq"
    shows "\<exists>gs. (\<forall>g \<in> set gs. regular_fun g) \<and> partial_sol f_sys gs
                  \<and> (\<forall>gs'. partial_sol f_sys gs'
                    \<longrightarrow>(\<forall>s. \<forall>i<length gs. subseteq_comm (eval (gs ! i) s) (eval (gs' ! i) s)))"
  sorry

lemma
  assumes "\<forall>eq \<in> set f_sys. regular_fun eq"
      and "indep_lb f_sys (length f_sys)"
    shows "\<exists>s. (\<forall>i. regular_lang (s i)) \<and> solves_eq_sys_comm f_sys s
          \<and> (\<forall>s'. solves_eq_sys_comm f_sys s' \<longrightarrow> (\<forall>i. parikh_img (s' i) \<subseteq> parikh_img (s i)))"
  sorry


end
