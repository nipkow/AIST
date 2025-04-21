theory Lfun
  imports 
    "Regular-Sets.Regular_Set"
    "Regular-Sets.Regular_Exp"
begin


section \<open>Definition of language functions\<close>

(* "language functions" are functions which get languages as arguments and also
   produce languages.
*)

datatype 'a lfun = V nat                        (* Variable *)
                 | N "'a lang"                  (* Constant *)
                 | Union2 "'a lfun" "'a lfun"
                 | UnionC "nat \<Rightarrow> 'a lfun"      (* Countable union *)
                 | Conc "'a lfun" "'a lfun"     (* Concatenation *)
                 | Star "'a lfun"

(* instantiate each variable with a language *)
type_synonym 'a state = "nat \<Rightarrow> 'a lang"

(* evaluate function for a given state, this produces a language *)
primrec eval :: "'a lfun \<Rightarrow> 'a state \<Rightarrow> 'a lang" where
  "eval (V n) s = s n" |
  "eval (N l) _ = l" |
  "eval (Union2 f g) s = eval f s \<union> eval g s" |
  "eval (UnionC f) s = (\<Union>i. eval (f i) s)" |
  "eval (Conc f g) s = eval f s @@ eval g s" |
  "eval (Star f) s = star (eval f s)"

(* all variables occurring in a function *)
primrec vars :: "'a lfun \<Rightarrow> nat set" where
  "vars (V n) = {n}" |
  "vars (N _) = {}" |
  "vars (Union2 f g) = vars f \<union> vars g" |
  "vars (UnionC f) = (\<Union>i. vars (f i))" |
  "vars (Conc f g) = vars f \<union> vars g" |
  "vars (Star f) = vars f"

(* substitute each occurrence of a variable i by the language function s i *)
primrec subst :: "'a lfun \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> 'a lfun" where
  "subst (V n) s = s n" |
  "subst (N l) _ = N l" |
  "subst (Union2 f g) s = Union2 (subst f s) (subst g s)" |
  "subst (UnionC f) s = UnionC (\<lambda>i. subst (f i) s)" |
  "subst (Conc f g) s = Conc (subst f s) (subst g s)" |
  "subst (Star f) s = Star (subst f s)"



section \<open>Some lemmas about the introduced functions\<close>

lemma substitution_lemma:
  assumes "\<forall>i. s' i = eval (upd i) s"
  shows "eval (subst f upd) s = eval f s'"
  using assms by (induction rule: lfun.induct) auto

lemma substitution_lemma_update:
  "eval (subst f (V(x := f'))) s = eval f (s(x := eval f' s))"
  using substitution_lemma[of "s(x := eval f' s)"] by force

lemma subst_id: "eval (subst f V) s = eval f s"
  using substitution_lemma[of s] by simp


lemma vars_subst: "vars (subst f upd) = (\<Union>x \<in> vars f. vars (upd x))"
  by (induction f) auto

lemma vars_subst_upper: "vars (subst f upd) \<subseteq> (\<Union>x. vars (upd x))"
  using vars_subst by force


lemma vars_subst_upd_upper: "vars (subst f (V(x := fx))) \<subseteq> vars f - {x} \<union> vars fx"
proof
  fix y
  let ?upd = "V(x := fx)"
  assume "y \<in> vars (subst f ?upd)"
  then obtain y' where "y' \<in> vars f \<and> y \<in> vars (?upd y')" using vars_subst by blast
  then show "y \<in> vars f - {x} \<union> vars fx" by (cases "x = y'") auto
qed

lemma vars_subst_upd_aux:
  assumes "x \<in> vars f"
  shows   "vars f - {x} \<union> vars fx \<subseteq> vars (subst f (V(x := fx)))"
proof
  fix y
  let ?upd = "V(x := fx)"
  assume as: "y \<in> vars f - {x} \<union> vars fx"
  then show "y \<in> vars (subst f ?upd)"
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
  shows   "vars (subst f (V(x := fx))) = vars f - {x} \<union> vars fx"
  using assms vars_subst_upd_upper vars_subst_upd_aux by blast

lemma eval_vars:
  assumes "\<forall>i \<in> vars f. s i = s' i"
  shows "eval f s = eval f s'"
  using assms by (induction f) auto

lemma eval_vars_subst:
  assumes "\<forall>i \<in> vars f. s i = eval (upd i) s"
  shows "eval (subst f upd) s = eval f s"
proof -
  let ?s' = "\<lambda>i. if i \<in> vars f then s i else eval (upd i) s"
  let ?s'' = "\<lambda>i. eval (upd i) s"
  have s'_s'': "?s' i = ?s'' i" for i using assms by simp
  then have s_s'': "\<forall>i. ?s'' i = eval (upd i) s" by simp

  from assms have "eval f s = eval f ?s'" using eval_vars[of f] by simp
  also have "\<dots> = eval (subst f upd) s"
    using assms substitution_lemma[OF s_s'', of f] by (simp add: eval_vars)
  finally show ?thesis by simp
qed



section \<open>Monotonicity of language functions\<close>

lemma lfun_mono_aux:
  assumes "\<forall>i \<in> vars f. s i \<subseteq> s' i"
  shows "eval f s \<subseteq> eval f s'"
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
  assumes "\<forall>i. s i \<le> s (Suc i)"
      and "w \<in> (\<Union>i. eval f (s i))"
    shows "w \<in> eval f (\<lambda>x. \<Union>i. s i x)"
proof -
  from assms(2) obtain n where n_intro: "w \<in> eval f (s n)" by auto
  have "s n x \<subseteq> (\<Union>i. s i x)" for x by auto
  with n_intro show "?thesis"
    using lfun_mono_aux[where s="s n" and s'="\<lambda>x. \<Union>i. s i x"] by auto
qed

lemma langpow_Union_eval:
  assumes "\<forall>i. s i \<le> s (Suc i)"
      and "w \<in> (\<Union>i. eval f (s i)) ^^ n"
    shows "w \<in> (\<Union>i. eval f (s i) ^^ n)"
using assms proof (induction n arbitrary: w)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain u v where w_decomp: "w = u@v" and
    "u \<in> (\<Union>i. eval f (s i)) \<and> v \<in> (\<Union>i. eval f (s i)) ^^ n" by fastforce
  with Suc have "u \<in> (\<Union>i. eval f (s i)) \<and> v \<in> (\<Union>i. eval f (s i) ^^ n)" by auto
  then obtain i j where i_intro: "u \<in> eval f (s i)" and j_intro: "v \<in> eval f (s j) ^^ n" by blast
  let ?m = "max i j"
  from i_intro Suc.prems(1) lfun_mono_aux have 1: "u \<in> eval f (s ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded1 subset_eq)
  from Suc.prems(1) lfun_mono_aux have "eval f (s j) \<subseteq> eval f (s ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded2)
  with j_intro langpow_mono have 2: "v \<in> eval f (s ?m) ^^ n" by auto
  from 1 2 show ?case using w_decomp by auto
qed

lemma lfun_cont_aux2:
  assumes "\<forall>i. s i \<le> s (Suc i)"
      and "w \<in> eval f (\<lambda>x. \<Union>i. s i x)"
    shows "w \<in> (\<Union>i. eval f (s i))"
using assms proof (induction arbitrary: w rule: lfun.induct)
  case (Conc f g)
  then obtain u v where w_decomp: "w = u@v"
    and "u \<in> eval f (\<lambda>x. \<Union>i. s i x) \<and> v \<in> eval g (\<lambda>x. \<Union>i. s i x)" by auto
  with Conc have "u \<in> (\<Union>i. eval f (s i)) \<and> v \<in> (\<Union>i. eval g (s i))" by auto
  then obtain i j where i_intro: "u \<in> eval f (s i)" and j_intro: "v \<in> eval g (s j)" by blast
  let ?m = "max i j"
  from i_intro Conc.prems(1) lfun_mono_aux have "u \<in> eval f (s ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded1 subset_eq)
  moreover from j_intro Conc.prems(1) lfun_mono_aux have "v \<in> eval g (s ?m)"
    by (metis le_fun_def lift_Suc_mono_le max.cobounded2 subset_eq)
  ultimately show ?case using w_decomp by auto
next
  case (Star f)
  then obtain n where n_intro: "w \<in> (eval f (\<lambda>x. \<Union>i. s i x)) ^^ n"
    using eval.simps(6) star_pow by blast
  with Star have "w \<in> (\<Union>i. eval f (s i)) ^^ n" using langpow_mono by blast
  with Star.prems have "w \<in> (\<Union>i. eval f (s i) ^^ n)" using langpow_Union_eval by auto
  then show ?case by (auto simp add: star_def)
qed fastforce+


(* The actual continuity lemma *)
lemma lfun_cont:
  assumes "\<forall>i. s i \<le> s (Suc i)"
  shows "eval f (\<lambda>x. \<Union>i. s i x) = (\<Union>i. eval f (s i))"
proof
  from assms show "eval f (\<lambda>x. \<Union>i. s i x) \<subseteq> (\<Union>i. eval f (s i))" using lfun_cont_aux2 by auto
  from assms show "(\<Union>i. eval f (s i)) \<subseteq> eval f (\<lambda>x. \<Union>i. s i x)" using lfun_cont_aux1 by blast
qed



section \<open>Regular functions\<close>

(* A regular function is a function which evaluates to a regular language
   if all of its arguments are regular. This applies to all operations
   defined for lfun, except the countable union (which is needed for the
   proof of the lemma in Pilling's paper)
*)

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


lemma emptyset_regular: "regular_fun (N {})"
  using lang.simps(1) by blast

lemma epsilon_regular: "regular_fun (N {[]})"
  using lang.simps(2) by blast


(* If all arguments are regular, a regular function evaluates to a regular language *)
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


(* A regular function stays regular if all variables are substituted by regular functions *)
lemma subst_reg_fun:
  assumes "regular_fun f"
      and "\<forall>x \<in> vars f. regular_fun (upd x)"
    shows "regular_fun (subst f upd)"
  using assms by (induction rule: regular_fun.induct) auto


lemma subst_reg_fun_update:
  assumes "regular_fun f"
      and "regular_fun g"
    shows "regular_fun (subst f (V(x := g)))"
  using assms subst_reg_fun fun_upd_def by (metis Variable)


lemma finite_Union_regular_aux:
  "\<forall>f \<in> set fs. regular_fun f \<Longrightarrow> \<exists>g. regular_fun g \<and> \<Union>(vars ` set fs) = vars g
                                      \<and> (\<forall>s. (\<Union>f \<in> set fs. eval f s) = eval g s)"
proof (induction fs)
  case Nil
  then show ?case using emptyset_regular by force
next
  case (Cons f1 fs)
  then obtain g where *: "regular_fun g \<and> \<Union>(vars ` set fs) = vars g
                          \<and> (\<forall>s. (\<Union>f\<in>set fs. eval f s) = eval g s)" by auto
  let ?g' = "Union2 f1 g"
  from Cons.prems * show ?case by auto
qed


lemma finite_Union_regular:
  assumes "finite F"
      and "\<forall>f \<in> F. regular_fun f"
    shows "\<exists>g. regular_fun g \<and> \<Union>(vars ` F) = vars g \<and> (\<forall>s. (\<Union>f\<in>F. eval f s) = eval g s)"
  using assms finite_Union_regular_aux finite_list by metis


(* TODO: this lemma should include parikh_img, shouldn't it? *)
(* f(Y*Z, X\<^sub>1, \<dots>, X\<^sub>m) = Y* f(Z, X\<^sub>1, \<dots>, X\<^sub>m) if f is a regular function

  Pilling's paper shows "=", but needs an additional assumption and I don't unterstand how
  the proof should work in the Union case:
     if f(Y*Z, X\<^sub>1, \<dots>, X\<^sub>m) = g(Y*Z, X\<^sub>1, \<dots>, X\<^sub>m) \<union> h(Y*Z, X\<^sub>1, \<dots>, X\<^sub>m) and g contains Y*Z, but h doesn't,
     then g(Y*Z, X\<^sub>1, \<dots>, X\<^sub>m) \<union> h(Y*Z, X\<^sub>1, \<dots>, X\<^sub>m) = Y* (g(Z, X\<^sub>1, \<dots>, X\<^sub>m) \<union> h(Z, X\<^sub>1, \<dots>, X\<^sub>m)) seems
     wrong to me
*)
lemma reg_fun_homogeneous_aux:
  assumes "regular_fun f"
      and "s x = star Y @@ Z"
    shows "eval f s \<subseteq> star Y @@ eval f (s(x := Z))"
using assms proof (induction rule: regular_fun.induct)
  case (Variable uu)
  then show ?case sorry
next
  case (Const l)
  have "eval (N l) s \<subseteq> star Y @@ eval (N l) s" using concI_if_Nil1 by blast
  then show ?case by simp
next
  case (Union2 f g)
  then show ?case sorry
next
  case (Conc f g)
  then show ?case sorry
next
  case (Star f)
  then show ?case sorry
qed


(* TODO: this lemma should include parikh_img, shouldn't it? *)
lemma reg_fun_homogeneous:
  assumes "regular_fun f"
      and "regular_fun y"
      and "regular_fun z"
    shows "eval (subst f (V(x := Conc (Star y) z))) s \<subseteq> eval (Conc (Star y) (subst f (V(x := z)))) s"
          (is "?L \<subseteq> ?R")
proof -
  let ?s' = "s(x := star (eval y s) @@ eval z s)"
  have "?L = eval f ?s'" using substitution_lemma_update by force
  also have "\<dots> \<subseteq> star (eval y s) @@ eval f (?s'(x := eval z s))"
    using assms reg_fun_homogeneous_aux[of f ?s'] unfolding fun_upd_def by auto
  also have "\<dots> = ?R" using substitution_lemma[of "s(x := eval z s)"] by simp
  finally show ?thesis .
qed

(* TODO: this lemma should include parikh_img, shouldn't it? *)
(* reformulate previous lemma with regular functions as arguments instead of languages *)
lemma reg_fun_homogeneous2:
  assumes "regular_fun f"
      and "regular_fun y"
      and "regular_fun z"                                                          
    shows "eval (subst f (\<lambda>a. if a = x then Conc (Star y) z else V a)) s
      \<subseteq> eval (Conc (Star y) (subst f (\<lambda>a. if a = x then z else V a))) s" (is "?L \<subseteq> ?R")
proof -
  let ?s' = "\<lambda>a. if a = x then star (eval y s) @@ eval z s else s a"
  have "?L = eval f ?s'"
    using substitution_lemma[of ?s' "\<lambda>a. if a = x then Conc (Star y) z else V a"] by fastforce
  also have "\<dots> \<subseteq> star (eval y s) @@ eval f (?s'(x := eval z s))"
    using assms reg_fun_homogeneous_aux[of f ?s'] by simp
  also have "\<dots> = ?R" using substitution_lemma[of "?s'(x := eval z s)"] by simp
  finally show ?thesis .
qed


section \<open>Constant functions\<close>

abbreviation const_fun :: "'a lfun \<Rightarrow> bool" where
  "const_fun f \<equiv> vars f = {}"

lemma const_fun_lang: "const_fun f \<Longrightarrow> \<exists>l. \<forall>s. eval f s = l"
proof (induction f)
  case (UnionC x)
  then show ?case by (metis emptyE eval_vars)
qed auto

lemma const_fun_regular_lang:
  assumes "const_fun f"
      and "regular_fun f"
    shows "\<exists>l. regular_lang l \<and> (\<forall>s. eval f s = l)"
  using assms const_fun_lang regular_fun_regular by fastforce

end
