theory Pilling_Lemma
  imports
    Lfun
    Eq_Sys
begin

section \<open>The lemma from Pilling's paper\<close>

(* In this section, the lemma from Pilling's paper will be proved.
   For some reason, the lemma will not be needed in the further proof.
*)


subsection \<open>g_pre (in the paper g_{iN} resp. X_{iN}\<close>

fun g_pre :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g_pre _ _ 0 = Const {}" |
  "g_pre f_sys i (Suc n) = subst (f_sys ! i) (\<lambda>j. if j < length f_sys then g_pre f_sys j n else Var j)"


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
  also have "\<dots> \<subseteq> eval (f_sys ! i) ?s_Suc" using s_subseteq_s_Suc lfun_mono_aux[where s="?s"] by auto
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


lemma g_pre_indep:
  assumes "i < length f_sys"
  shows "\<forall>x \<in> vars (g_pre f_sys i n). x \<ge> length f_sys"
proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?upd = "\<lambda>x. if x < length f_sys then g_pre f_sys x n else Var x"
  from vars_subst_upper have "vars (g_pre f_sys i (Suc n)) \<subseteq> (\<Union>x. vars (?upd x))" by simp
  moreover have "\<forall>y \<in> vars (?upd x). y \<ge> length f_sys" for x using Suc by simp
  ultimately show ?case by auto
qed



subsection \<open>g\<close>

(* This is the only reason why we have included the countable union in the lfun definition *)
definition g :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g f_sys i \<equiv> UnionC (\<lambda>n. g_pre f_sys i n)"


lemma g_indep:
  assumes "i < length f_sys"
  shows "\<forall>x \<in> vars (g f_sys i). x \<ge> length f_sys"
unfolding g_def using assms g_pre_indep by auto


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


lemma g_pre_g_Union: "(\<Union>n. eval (g_pre f_sys i (Suc n)) s) =
  eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else Var i)) s"
proof -
  let ?s = "(\<lambda>n j. if j < length f_sys then eval (g_pre f_sys j n) s else s j)"
  have "?s n j \<subseteq> ?s (Suc n) j" for n j
    using g_pre_monotonically_increasing by fastforce
  then have s_monotone: "\<forall>n. ?s n \<le> ?s (Suc n)" by (simp add: le_fun_def)

  have s_Union: "(\<Union>i. if x < length f_sys then eval (g_pre f_sys x i) s else s x) =
    (if x < length f_sys then eval (g f_sys x) s else s x)" for x
    unfolding g_def by simp

  have "eval (g_pre f_sys i (Suc n)) s = eval (f_sys ! i) (?s n)" for n
    using g_pre_eval[of f_sys] by auto
  then have "(\<Union>n. eval (g_pre f_sys i (Suc n)) s) = (\<Union>n. eval (f_sys ! i) (?s n))" by auto
  also have "\<dots> = eval (f_sys ! i) (\<lambda>x. \<Union>i. if x < length f_sys then eval (g_pre f_sys x i) s else s x)"
    using s_monotone lfun_cont[of ?s "f_sys ! i"] by argo
  also have "\<dots> = eval (f_sys ! i) (\<lambda>x. if x < length f_sys then eval (g f_sys x) s else s x)"
    using s_Union by simp
  also have "\<dots> = eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else Var i)) s"
    using substitution_lemma[of "\<lambda>x. if x < length f_sys then eval (g f_sys x) s else s x"
                                "\<lambda>i. if i < length f_sys then g f_sys i else Var i"]
    by fastforce
  finally show ?thesis .
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
  also have "\<dots> = eval (f_sys ! i) s"
    using g_pre_g_Union[of f_sys] assms by (simp add: substitution_lemma)
  finally show "eval (f_sys ! i) s = s i" by auto
qed


(* The lemma from Pilling's paper *)
lemma lemma_paper:
  assumes "\<forall>eq \<in> set f_sys. regular_fun eq"
    shows "\<exists>g_sys. length g_sys = length f_sys \<and> (\<forall>eq \<in> set g_sys. \<forall>x \<in> vars eq. x \<ge> length f_sys)
                \<and> (\<forall>s. solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys g_sys s)
                \<and> (\<forall>s. solves_eq_sys g_sys s \<longrightarrow> solves_eq_sys f_sys s)"
proof -
  let ?g_sys = "map (\<lambda>i. g f_sys i) [0..<length f_sys]"
  have length_g_sys: "length ?g_sys = length f_sys" by auto
  have indep_g_sys: "\<forall>eq \<in> set ?g_sys. \<forall>x \<in> vars eq. x \<ge> length f_sys"
    using g_indep by fastforce

  have "\<lbrakk> i < length f_sys; solves_ineq_sys f_sys s \<rbrakk> \<Longrightarrow> eval (?g_sys ! i) s \<subseteq> s i" for s i
    using solves_g_if_solves_f_ineq solves_ineq_sys_def by fastforce
  then have g_sol_of_f: "solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys ?g_sys s" for s
    using solves_ineq_sys_def by (metis length_g_sys)

  have f_sol_of_g: "solves_eq_sys ?g_sys s \<longrightarrow> solves_eq_sys f_sys s" for s
    using solves_f_if_solves_g_eq solves_eq_sys_def
    by (metis add_0 diff_zero length_g_sys nth_map_upt)

  from length_g_sys indep_g_sys g_sol_of_f f_sol_of_g show ?thesis by blast
qed

end
