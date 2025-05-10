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
  "g_pre f_sys i (Suc n) = subst (\<lambda>j. if j < length f_sys then g_pre f_sys j n else Var j) (f_sys ! i)"


lemma g_pre_eval:
  assumes "\<forall>j < length f_sys. v' j = eval (g_pre f_sys j n) v"
      and "\<forall>j \<ge> length f_sys. v' j = v j"
    shows "eval (g_pre f_sys i (Suc n)) v = eval (f_sys ! i) v'"
using assms by (simp add: substitution_lemma)


lemma g_pre_monotonically_increasing:
  "eval (g_pre f_sys i n) v \<subseteq> eval (g_pre f_sys i (Suc n)) v"
proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?v = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j n) v else v j"
  let ?v_Suc = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j (Suc n)) v else v j"
  from Suc.IH have v_subseteq_v_Suc: "?v j \<subseteq> ?v_Suc j" for j by auto

  have "eval (g_pre f_sys i (Suc n)) v = eval (f_sys ! i) ?v" using g_pre_eval[of f_sys] by auto
  also have "\<dots> \<subseteq> eval (f_sys ! i) ?v_Suc" using v_subseteq_v_Suc lfun_mono_aux[where v="?v"] by auto
  also have "\<dots> = eval (g_pre f_sys i (Suc (Suc n))) v" using g_pre_eval[of f_sys ?v_Suc] by auto
  finally show ?case .
qed


lemma g_pre_subseteq_sol:
  assumes "i < length f_sys"
      and "solves_ineq_sys f_sys v"
    shows "eval (g_pre f_sys i n) v \<subseteq> eval (f_sys ! i) v"
using assms proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?v' = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j n) v else v j"

  have "?v' j \<subseteq> v j" for j
  proof (cases "j < length f_sys")
    case True
    with Suc have "?v' j \<subseteq> eval (f_sys ! j) v" by auto
    also have "\<dots> \<subseteq> v j" using assms(2) True unfolding solves_ineq_sys_def by auto
    finally show ?thesis .
  next
    case False
    then show ?thesis by auto
  qed
  then have "eval (f_sys ! i) ?v' \<subseteq> eval (f_sys ! i) v" using lfun_mono_aux by meson
  then show ?case using g_pre_eval[of f_sys ?v'] by auto
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
      and "solves_ineq_sys f_sys v"
    shows "eval (g f_sys i) v \<subseteq> eval (f_sys ! i) v"
unfolding g_def proof
  fix x
  assume "x \<in> eval (UnionC (g_pre f_sys i)) v"
  then show "x \<in> eval (f_sys ! i) v" using g_pre_subseteq_sol[OF assms] by auto
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


lemma g_pre_g_Union: "(\<Union>n. eval (g_pre f_sys i (Suc n)) v) =
  eval (subst (\<lambda>i. if i < length f_sys then g f_sys i else Var i) (f_sys ! i)) v"
proof -
  let ?v = "(\<lambda>n j. if j < length f_sys then eval (g_pre f_sys j n) v else v j)"
  have "?v n j \<subseteq> ?v (Suc n) j" for n j
    using g_pre_monotonically_increasing by fastforce
  then have s_monotone: "\<forall>n. ?v n \<le> ?v (Suc n)" by (simp add: le_fun_def)

  have s_Union: "(\<Union>i. if x < length f_sys then eval (g_pre f_sys x i) v else v x) =
    (if x < length f_sys then eval (g f_sys x) v else v x)" for x
    unfolding g_def by simp

  have "eval (g_pre f_sys i (Suc n)) v = eval (f_sys ! i) (?v n)" for n
    using g_pre_eval[of f_sys] by auto
  then have "(\<Union>n. eval (g_pre f_sys i (Suc n)) v) = (\<Union>n. eval (f_sys ! i) (?v n))" by auto
  also have "\<dots> = eval (f_sys ! i) (\<lambda>x. \<Union>i. if x < length f_sys then eval (g_pre f_sys x i) v else v x)"
    using s_monotone lfun_cont[of ?v "f_sys ! i"] by argo
  also have "\<dots> = eval (f_sys ! i) (\<lambda>x. if x < length f_sys then eval (g f_sys x) v else v x)"
    using s_Union by simp
  also have "\<dots> = eval (subst (\<lambda>i. if i < length f_sys then g f_sys i else Var i) (f_sys ! i)) v"
    using substitution_lemma[of "\<lambda>x. if x < length f_sys then eval (g f_sys x) v else v x"
                                "\<lambda>i. if i < length f_sys then g f_sys i else Var i"]
    by fastforce
  finally show ?thesis .
qed


lemma solves_f_if_solves_g_eq:
  assumes "\<forall>i < length f_sys. eval (g f_sys i) v = v i"
  shows "solves_eq_sys f_sys v"
unfolding solves_eq_sys_def proof (standard, standard)
  fix i
  assume "i < length f_sys"
  with assms(1) have "v i = (\<Union>n. eval (g_pre f_sys i n) v)" unfolding g_def by auto
  also have "\<dots> = (\<Union>n. eval (g_pre f_sys i (Suc n)) v)"
    using Union_index_shift[of "\<lambda>n. eval (g_pre f_sys i n) v"] by auto
  also have "\<dots> = eval (f_sys ! i) v"
    using g_pre_g_Union[of f_sys] assms by (simp add: substitution_lemma)
  finally show "eval (f_sys ! i) v = v i" by auto
qed


(* The lemma from Pilling's paper *)
lemma lemma_paper:
  assumes "\<forall>eq \<in> set f_sys. regular_fun eq"
    shows "\<exists>g_sys. length g_sys = length f_sys \<and> (\<forall>eq \<in> set g_sys. \<forall>x \<in> vars eq. x \<ge> length f_sys)
                \<and> (\<forall>v. solves_ineq_sys f_sys v \<longrightarrow> solves_ineq_sys g_sys v)
                \<and> (\<forall>v. solves_eq_sys g_sys v \<longrightarrow> solves_eq_sys f_sys v)"
proof -
  let ?g_sys = "map (\<lambda>i. g f_sys i) [0..<length f_sys]"
  have length_g_sys: "length ?g_sys = length f_sys" by auto
  have indep_g_sys: "\<forall>eq \<in> set ?g_sys. \<forall>x \<in> vars eq. x \<ge> length f_sys"
    using g_indep by fastforce

  have "\<lbrakk> i < length f_sys; solves_ineq_sys f_sys v \<rbrakk> \<Longrightarrow> eval (?g_sys ! i) v \<subseteq> v i" for v i
    using solves_g_if_solves_f_ineq solves_ineq_sys_def by fastforce
  then have g_sol_of_f: "solves_ineq_sys f_sys v \<longrightarrow> solves_ineq_sys ?g_sys v" for v
    using solves_ineq_sys_def by (metis length_g_sys)

  have f_sol_of_g: "solves_eq_sys ?g_sys v \<longrightarrow> solves_eq_sys f_sys v" for v
    using solves_f_if_solves_g_eq solves_eq_sys_def
    by (metis add_0 diff_zero length_g_sys nth_map_upt)

  from length_g_sys indep_g_sys g_sol_of_f f_sol_of_g show ?thesis by blast
qed

end
