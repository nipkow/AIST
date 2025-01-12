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


lemma lfun_mono_aux:
  assumes "\<forall>i. s i \<subseteq> s' i"
    shows "eval f s \<subseteq> eval f s'"
using assms proof (induction rule: lfun.induct)
  case (Conc x1a x2a)
  then show ?case by fastforce
next
  case (Star f)
  then show ?case
    by (smt (verit, best) eval.simps(6) in_star_iff_concat order_trans subsetI)
qed auto


lemma lfun_mono:
  fixes f :: "'a lfun"
  shows "mono (eval f)"
  using lfun_mono_aux by (metis le_funD monoI)


lemma substitution_lemma:
  assumes "\<forall>i. s' i = eval (upd i) s"
  shows "eval (subst f upd) s = eval f s'"
  using assms by (induction rule: lfun.induct) auto


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

lemma g_pre_eval:
  assumes "\<forall>j < length f_sys. s' j = eval (g_pre f_sys j n) s"
      and "\<forall>j \<ge> length f_sys. s' j = s j"
    shows "eval (g_pre f_sys i (Suc n)) s = eval (f_sys ! i) s'"
using assms by (simp add: substitution_lemma)

lemma g_pre_monotonically_increasing:
  "eval (g_pre f_sys i n) s \<subseteq> eval (g_pre f_sys i (Suc n)) s"
proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?s = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j n) s else s j"
  let ?s_Suc = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j (Suc n)) s else s j"
  from Suc.IH have s_subseteq_s_Suc: "?s j \<subseteq> ?s_Suc j" for j by auto

  have "eval (g_pre f_sys i (Suc n)) s = eval (f_sys ! i) ?s" using g_pre_eval[of f_sys] by auto
  also have "\<dots> \<subseteq> eval (f_sys ! i) ?s_Suc" using s_subseteq_s_Suc lfun_mono_aux[of ?s ?s_Suc] by auto
  also have "\<dots> = eval (g_pre f_sys i (Suc (Suc n))) s" using g_pre_eval[of f_sys ?s_Suc] by auto
  finally show ?case .
qed

lemma g_pre_subseteq_sol:
  assumes "i < length f_sys"
      and "solves_ineq_sys f_sys s"
    shows "eval (g_pre f_sys i n) s \<subseteq> eval (f_sys ! i) s"
using assms proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?s' = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j n) s else s j"

  have "?s' j \<subseteq> s j" for j
  proof (cases "j < length f_sys")
    case True
    with Suc have "?s' j \<subseteq> eval (f_sys ! j) s" by auto
    also have "\<dots> \<subseteq> s j" using assms(2) True unfolding solves_ineq_sys_def by auto
    finally show ?thesis .
  next
    case False
    then show ?thesis by auto
  qed
  then have "eval (f_sys ! i) ?s' \<subseteq> eval (f_sys ! i) s" using lfun_mono_aux by meson
  then show ?case using g_pre_eval[of f_sys ?s'] by auto
qed


definition g :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g f_sys i \<equiv> UnionC (\<lambda>n. g_pre f_sys i n)"

lemma solves_g_if_solves_f_ineq:
  assumes "i < length f_sys"
      and "solves_ineq_sys f_sys s"
    shows "eval (g f_sys i) s \<subseteq> eval (f_sys ! i) s"
unfolding g_def proof
  fix x
  assume "x \<in> eval (UnionC (g_pre f_sys i)) s"
  then show "x \<in> eval (f_sys ! i) s" using g_pre_subseteq_sol[OF assms] by auto
qed

lemma Union_index_shift: "(\<Union>n. f n) = f 0 \<union> (\<Union>n. f (Suc n))"
proof
  show "\<Union> (range f) \<subseteq> f 0 \<union> (\<Union>n. f (Suc n))"
  proof
    fix x
    assume "x \<in> \<Union> (range f)"
    then obtain n where x_in_f: "n \<ge> 0 \<and> x \<in> f n" by auto
    show "x \<in> f 0 \<union> (\<Union>n. f (Suc n))"
    proof (cases "n=0")
      case True
      with x_in_f show ?thesis by auto
    next
      case False
      with x_in_f have "\<exists>n'. Suc n' = n" by presburger
      then obtain n' where "Suc n' = n" by blast
      with x_in_f show ?thesis by auto
    qed
  qed
  show "f 0 \<union> (\<Union>n. f (Suc n)) \<subseteq> \<Union> (range f)" by auto
qed

lemma "(\<Union>n. eval (g_pre f_sys i (Suc n)) s)
    \<subseteq> eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
proof
  fix x
  assume "x \<in> (\<Union>n. eval (g_pre f_sys i (Suc n)) s)"
  then obtain n where n_intro: "x \<in> eval (g_pre f_sys i (Suc n)) s" by auto

  let ?s_g_pre = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j n) s else s j"
  let ?s_g = "\<lambda>j. if j < length f_sys then eval (g f_sys j) s else s j"
  have s_g_pre_subseteq_s_g: "?s_g_pre j \<subseteq> ?s_g j" for j unfolding g_def by auto

  from n_intro have "x \<in> eval (f_sys ! i) ?s_g_pre"
    using g_pre_eval[of f_sys ?s_g_pre] by auto
  with s_g_pre_subseteq_s_g have "x \<in> eval (f_sys ! i) ?s_g"
    using lfun_mono_aux[of ?s_g_pre ?s_g] by auto
  then show "x \<in> eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
    using substitution_lemma by (smt (verit) eval.simps(1))
qed

lemma "eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s
    \<subseteq> (\<Union>n. eval (g_pre f_sys i (Suc n)) s)"
proof
  fix x
  assume "x \<in> eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
  show "x \<in> (\<Union>n. eval (g_pre f_sys i (Suc n)) s)" sorry
qed

lemma solves_f_if_solves_g_eq:
  assumes "\<forall>i < length f_sys. eval (g f_sys i) s = s i"
  shows "solves_eq_sys f_sys s"
unfolding solves_eq_sys_def proof (standard, standard)
  fix i
  assume "i < length f_sys"
  with assms(1) have "s i = (\<Union>n. eval (g_pre f_sys i n) s)" unfolding g_def by auto
  also have "\<dots> = (\<Union>n. eval (g_pre f_sys i (Suc n)) s)"
    using Union_index_shift[of "\<lambda>n. eval (g_pre f_sys i n) s"] by auto
  also have "\<dots> = eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
    sorry
  also have "\<dots> = eval (f_sys ! i) s" using assms by (simp add: substitution_lemma)
  finally show "eval (f_sys ! i) s = s i" by auto
qed

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
