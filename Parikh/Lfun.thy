theory Lfun
  imports 
    "Regular-Sets.Regular_Set"
    "Regular-Sets.Regular_Exp"
begin


section \<open>Definition of language functions\<close>

(* "language functions" are functions which get languages as arguments and also
   produce languages.
*)

datatype 'a lfun = Var nat                        (* Variable *)
                 | Const "'a lang"                  (* Constant *)
                 | Union2 "'a lfun" "'a lfun"
                 | UnionC "nat \<Rightarrow> 'a lfun"      (* Countable union *)
                 | Concat "'a lfun" "'a lfun"     (* Concatenation *)
                 | Star "'a lfun"

(* instantiate each variable with a language *)
type_synonym 'a valuation = "nat \<Rightarrow> 'a lang"

(* evaluate function for a given state, this produces a language *)
primrec eval :: "'a lfun \<Rightarrow> 'a valuation \<Rightarrow> 'a lang" where
  "eval (Var n) v = v n" |
  "eval (Const l) _ = l" |
  "eval (Union2 f g) v = eval f v \<union> eval g v" |
  "eval (UnionC f) v = (\<Union>i. eval (f i) v)" |
  "eval (Concat f g) v = eval f v @@ eval g v" |
  "eval (Star f) v = star (eval f v)"

(* all variables occurring in a function *)
primrec vars :: "'a lfun \<Rightarrow> nat set" where
  "vars (Var n) = {n}" |
  "vars (Const _) = {}" |
  "vars (Union2 f g) = vars f \<union> vars g" |
  "vars (UnionC f) = (\<Union>i. vars (f i))" |
  "vars (Concat f g) = vars f \<union> vars g" |
  "vars (Star f) = vars f"

(* substitute each occurrence of a variable i by the language function s i *)
primrec subst :: "(nat \<Rightarrow> 'a lfun) \<Rightarrow> 'a lfun \<Rightarrow> 'a lfun" where
  "subst s (Var n) = s n" |
  "subst _ (Const l) = Const l" |
  "subst s (Union2 f g) = Union2 (subst s f) (subst s g)" |
  "subst s (UnionC f) = UnionC (\<lambda>i. subst s (f i))" |
  "subst s (Concat f g) = Concat (subst s f) (subst s g)" |
  "subst s (Star f) = Star (subst s f)"



section \<open>Some lemmas about the introduced functions\<close>

lemma substitution_lemma:
  assumes "\<forall>i. v' i = eval (upd i) v"
  shows "eval (subst upd f) v = eval f v'"
  using assms by (induction rule: lfun.induct) auto

lemma substitution_lemma_update:
  "eval (subst (Var(x := f')) f) v = eval f (v(x := eval f' v))"
  using substitution_lemma[of "v(x := eval f' v)"] by force

lemma subst_id: "eval (subst Var f) v = eval f v"
  using substitution_lemma[of v] by simp


lemma vars_subst: "vars (subst upd f) = (\<Union>x \<in> vars f. vars (upd x))"
  by (induction f) auto

lemma vars_subst_upper: "vars (subst upd f) \<subseteq> (\<Union>x. vars (upd x))"
  using vars_subst by force


lemma vars_subst_upd_upper: "vars (subst (Var(x := fx)) f) \<subseteq> vars f - {x} \<union> vars fx"
proof
  fix y
  let ?upd = "Var(x := fx)"
  assume "y \<in> vars (subst ?upd f)"
  then obtain y' where "y' \<in> vars f \<and> y \<in> vars (?upd y')" using vars_subst by blast
  then show "y \<in> vars f - {x} \<union> vars fx" by (cases "x = y'") auto
qed

lemma vars_subst_upd_aux:
  assumes "x \<in> vars f"
  shows   "vars f - {x} \<union> vars fx \<subseteq> vars (subst (Var(x := fx)) f)"
proof
  fix y
  let ?upd = "Var(x := fx)"
  assume as: "y \<in> vars f - {x} \<union> vars fx"
  then show "y \<in> vars (subst ?upd f)"
  proof (cases "y \<in> vars f - {x}")
    case True
    then show ?thesis using vars_subst by fastforce
  next
    case False
    with as have "y \<in> vars fx" by blast
    with assms show ?thesis using vars_subst by fastforce
  qed
qed

lemma vars_subst_upd:
  assumes "x \<in> vars f"
  shows   "vars (subst (Var(x := fx)) f) = vars f - {x} \<union> vars fx"
  using assms vars_subst_upd_upper vars_subst_upd_aux by blast

lemma eval_vars:
  assumes "\<forall>i \<in> vars f. s i = s' i"
  shows "eval f s = eval f s'"
  using assms by (induction f) auto

lemma eval_vars_subst:
  assumes "\<forall>i \<in> vars f. v i = eval (upd i) v"
  shows "eval (subst upd f) v = eval f v"
proof -
  let ?v' = "\<lambda>i. if i \<in> vars f then v i else eval (upd i) v"
  let ?v'' = "\<lambda>i. eval (upd i) v"
  have v'_v'': "?v' i = ?v'' i" for i using assms by simp
  then have v_v'': "\<forall>i. ?v'' i = eval (upd i) v" by simp

  from assms have "eval f v = eval f ?v'" using eval_vars[of f] by simp
  also have "\<dots> = eval (subst upd f) v"
    using assms substitution_lemma[OF v_v'', of f] by (simp add: eval_vars)
  finally show ?thesis by simp
qed



section \<open>Monotonicity of language functions\<close>

lemma lfun_mono_aux:
  assumes "\<forall>i \<in> vars f. v i \<subseteq> v' i"
  shows "eval f v \<subseteq> eval f v'"
using assms proof (induction rule: lfun.induct)
  case (Star x)
  then show ?case
    by (smt (verit, best) eval.simps(6) in_star_iff_concat order_trans subsetI vars.simps(6))
qed fastforce+

lemma lfun_mono:
  fixes f :: "'a lfun"
  shows "mono (eval f)"
  using lfun_mono_aux by (metis le_funD monoI)



section \<open>Continuity of language functions\<close>

(* Surprisingly, I could not find such a lemma in Regular_Set.thy *)
lemma langpow_mono:
  fixes A :: "'a lang"
  assumes "A \<subseteq> B"
  shows "A ^^ n \<subseteq> B ^^ n"
using assms conc_mono[of A B] by (induction n) auto

lemma lfun_cont_aux1:
  assumes "\<forall>i. v i \<le> v (Suc i)"
      and "w \<in> (\<Union>i. eval f (v i))"
    shows "w \<in> eval f (\<lambda>x. \<Union>i. v i x)"
proof -
  from assms(2) obtain n where n_intro: "w \<in> eval f (v n)" by auto
  have "v n x \<subseteq> (\<Union>i. v i x)" for x by auto
  with n_intro show "?thesis"
    using lfun_mono_aux[where v="v n" and v'="\<lambda>x. \<Union>i. v i x"] by auto
qed

lemma langpow_Union_eval:
  assumes "\<forall>i. v i \<le> v (Suc i)"
      and "w \<in> (\<Union>i. eval f (v i)) ^^ n"
    shows "w \<in> (\<Union>i. eval f (v i) ^^ n)"
using assms proof (induction n arbitrary: w)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain u u' where w_decomp: "w = u@u'" and
    "u \<in> (\<Union>i. eval f (v i)) \<and> u' \<in> (\<Union>i. eval f (v i)) ^^ n" by fastforce
  with Suc have "u \<in> (\<Union>i. eval f (v i)) \<and> u' \<in> (\<Union>i. eval f (v i) ^^ n)" by auto
  then obtain i j where i_intro: "u \<in> eval f (v i)" and j_intro: "u' \<in> eval f (v j) ^^ n" by blast
  let ?m = "max i j"
  from i_intro Suc.prems(1) lfun_mono_aux have 1: "u \<in> eval f (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded1 subset_eq)
  from Suc.prems(1) lfun_mono_aux have "eval f (v j) \<subseteq> eval f (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded2)
  with j_intro langpow_mono have 2: "u' \<in> eval f (v ?m) ^^ n" by auto
  from 1 2 show ?case using w_decomp by auto
qed

lemma lfun_cont_aux2:
  assumes "\<forall>i. v i \<le> v (Suc i)"
      and "w \<in> eval f (\<lambda>x. \<Union>i. v i x)"
    shows "w \<in> (\<Union>i. eval f (v i))"
using assms proof (induction arbitrary: w rule: lfun.induct)
  case (Concat f g)
  then obtain u u' where w_decomp: "w = u@u'"
    and "u \<in> eval f (\<lambda>x. \<Union>i. v i x) \<and> u' \<in> eval g (\<lambda>x. \<Union>i. v i x)" by auto
  with Concat have "u \<in> (\<Union>i. eval f (v i)) \<and> u' \<in> (\<Union>i. eval g (v i))" by auto
  then obtain i j where i_intro: "u \<in> eval f (v i)" and j_intro: "u' \<in> eval g (v j)" by blast
  let ?m = "max i j"
  from i_intro Concat.prems(1) lfun_mono_aux have "u \<in> eval f (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded1 subset_eq)
  moreover from j_intro Concat.prems(1) lfun_mono_aux have "u' \<in> eval g (v ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded2 subset_eq)
  ultimately show ?case using w_decomp by auto
next
  case (Star f)
  then obtain n where n_intro: "w \<in> (eval f (\<lambda>x. \<Union>i. v i x)) ^^ n"
    using eval.simps(6) star_pow by blast
  with Star have "w \<in> (\<Union>i. eval f (v i)) ^^ n" using langpow_mono by blast
  with Star.prems have "w \<in> (\<Union>i. eval f (v i) ^^ n)" using langpow_Union_eval by auto
  then show ?case by (auto simp add: star_def)
qed fastforce+


(* The actual continuity lemma *)
lemma lfun_cont:
  assumes "\<forall>i. v i \<le> v (Suc i)"
  shows "eval f (\<lambda>x. \<Union>i. v i x) = (\<Union>i. eval f (v i))"
proof
  from assms show "eval f (\<lambda>x. \<Union>i. v i x) \<subseteq> (\<Union>i. eval f (v i))" using lfun_cont_aux2 by auto
  from assms show "(\<Union>i. eval f (v i)) \<subseteq> eval f (\<lambda>x. \<Union>i. v i x)" using lfun_cont_aux1 by blast
qed



section \<open>Regular functions\<close>

(* A regular function is a function which evaluates to a regular language
   if all of its arguments are regular. This applies to all operations
   defined for lfun, except the countable union (which is needed for the
   proof of the lemma in Pilling's paper)
*)

fun regular_fun :: "'a lfun \<Rightarrow> bool" where
  "regular_fun (Var _) \<longleftrightarrow> True" |
  "regular_fun (Const l) \<longleftrightarrow> regular_lang l" |
  "regular_fun (Union2 f g) \<longleftrightarrow> regular_fun f \<and> regular_fun g" |
  "regular_fun (Concat f g) \<longleftrightarrow> regular_fun f \<and> regular_fun g" |
  "regular_fun (Star f) \<longleftrightarrow> regular_fun f" |
  (* Might actually be a regular_fun, but in general it is not *)
  "regular_fun (UnionC _) \<longleftrightarrow> False"


lemma emptyset_regular: "regular_fun (Const {})"
  using lang.simps(1) regular_fun.simps(2) by blast

lemma epsilon_regular: "regular_fun (Const {[]})"
  using lang.simps(2) regular_fun.simps(2) by blast


(* If all arguments are regular, a regular function evaluates to a regular language *)
lemma regular_fun_regular:
  assumes "regular_fun f"
      and "\<And>n. n \<in> vars f \<Longrightarrow> regular_lang (v n)"
    shows "regular_lang (eval f v)"
using assms proof (induction rule: regular_fun.induct)
  case (3 f g)
  then obtain r1 r2 where "Regular_Exp.lang r1 = eval f v \<and> Regular_Exp.lang r2 = eval g v" by auto
  then have "Regular_Exp.lang (Plus r1 r2) = eval (Union2 f g) v" by simp
  then show ?case by blast
next
  case (4 f g)
  then obtain r1 r2 where "Regular_Exp.lang r1 = eval f v \<and> Regular_Exp.lang r2 = eval g v" by auto
  then have "Regular_Exp.lang (Times r1 r2) = eval (Concat f g) v" by simp
  then show ?case by blast
next
  case (5 f)
  then obtain r  where "Regular_Exp.lang r = eval f v" by auto
  then have "Regular_Exp.lang (Regular_Exp.Star r) = eval (Star f) v" by simp
  then show ?case by blast
qed simp_all


(* A regular function stays regular if all variables are substituted by regular functions *)
lemma subst_reg_fun:
  assumes "regular_fun f"
      and "\<forall>x \<in> vars f. regular_fun (upd x)"
    shows "regular_fun (subst upd f)"
  using assms by (induction f rule: regular_fun.induct) simp_all


lemma subst_reg_fun_update:
  assumes "regular_fun f"
      and "regular_fun g"
    shows "regular_fun (subst (Var(x := g)) f)"
  using assms subst_reg_fun fun_upd_def by (metis regular_fun.simps(1))


lemma finite_Union_regular_aux:
  "\<forall>f \<in> set fs. regular_fun f \<Longrightarrow> \<exists>g. regular_fun g \<and> \<Union>(vars ` set fs) = vars g
                                      \<and> (\<forall>v. (\<Union>f \<in> set fs. eval f v) = eval g v)"
proof (induction fs)
  case Nil
  then show ?case using emptyset_regular by fastforce
next
  case (Cons f1 fs)
  then obtain g where *: "regular_fun g \<and> \<Union>(vars ` set fs) = vars g
                          \<and> (\<forall>v. (\<Union>f\<in>set fs. eval f v) = eval g v)" by auto
  let ?g' = "Union2 f1 g"
  from Cons.prems * have "regular_fun ?g' \<and> \<Union> (vars ` set (f1 # fs)) = vars ?g'
      \<and> (\<forall>v. (\<Union>f\<in>set (f1 # fs). eval f v) = eval ?g' v)" by simp
  then show ?case by blast
qed


lemma finite_Union_regular:
  assumes "finite F"
      and "\<forall>f \<in> F. regular_fun f"
    shows "\<exists>g. regular_fun g \<and> \<Union>(vars ` F) = vars g \<and> (\<forall>v. (\<Union>f\<in>F. eval f v) = eval g v)"
  using assms finite_Union_regular_aux finite_list by metis



section \<open>Constant functions\<close>

abbreviation const_fun :: "'a lfun \<Rightarrow> bool" where
  "const_fun f \<equiv> vars f = {}"

lemma const_fun_lang: "const_fun f \<Longrightarrow> \<exists>l. \<forall>v. eval f v = l"
proof (induction f)
  case (UnionC x)
  then show ?case by (metis emptyE eval_vars)
qed auto

lemma const_fun_regular_lang:
  assumes "const_fun f"
      and "regular_fun f"
    shows "\<exists>l. regular_lang l \<and> (\<forall>v. eval f v = l)"
  using assms const_fun_lang regular_fun_regular by fastforce

end
