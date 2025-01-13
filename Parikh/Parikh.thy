theory Parikh
  imports 
    "../CFG"
    "../CFL"
    "$AFP/Regular-Sets/Regular_Set"
    "$AFP/Regular-Sets/Regular_Exp"
begin


section \<open>General stuff\<close>

lemma langpow_mono:
  fixes A :: "'a lang"
  assumes "A \<subseteq> B"
  shows "A ^^ n \<subseteq> B ^^ n"
using assms conc_mono[of A B] by (induction n) auto


lemma countable_union_finally_empty:
  assumes "\<forall>j>i. f j = {}"
  shows "(\<Union>j. f j) = (\<Union>j\<le>i. f j)"
  sorry


(* currently not needed *)
lemma generalized_arden: "lfp (\<lambda>X. A @@ X \<union> B) = star A @@ B" (is "lfp ?f = _")
proof (rule lfp_eqI)
  show "mono ?f" by (simp add: Un_commute conc_mono le_supI2 monoI)

  have "A @@ star A \<union> {[]} = star A" using star_unfold_left by blast
  then show "A @@ star A @@ B \<union> B = star A @@ B"
    by (metis conc_Un_distrib(2) conc_assoc conc_epsilon(1))

  show "\<And>X. A @@ X \<union> B = X \<Longrightarrow> star A @@ B \<subseteq> X"
  proof -
    fix X
    assume "A @@ X \<union> B = X"
    then have "X = A ^^ Suc n @@ X \<union> (\<Union>m\<le>n. A ^^ m @@ B)" for n using arden_helper by metis
    then have "A ^^ n @@ B \<subseteq> X" for n by blast
    then show "star A @@ B \<subseteq> X" unfolding star_def by blast
  qed
qed



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


lemma vars_subst: "vars (subst f upd) = (\<Union>x \<in> vars f. vars (upd x))"
  by (induction f) auto

lemma vars_subst_upper: "vars (subst f upd) \<subseteq> (\<Union>x. vars (upd x))"
  using vars_subst by force


(* Continuity of lfun *)

lemma lfun_cont_aux1:
  assumes "\<forall>i. s i \<le> s (Suc i)"
      and "w \<in> (\<Union>i. eval f (s i))"
    shows "w \<in> eval f (\<lambda>x. \<Union>i. s i x)"
proof -
  from assms(2) obtain n where n_intro: "w \<in> eval f (s n)" by auto
  have "s n x \<subseteq> (\<Union>i. s i x)" for x by auto
  with n_intro show "?thesis"
    using lfun_mono_aux[of "s n" "\<lambda>x. \<Union>i. s i x"] by auto
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

lemma lfun_cont:
  assumes "\<forall>i. s i \<le> s (Suc i)"
  shows "eval f (\<lambda>x. \<Union>i. s i x) = (\<Union>i. eval f (s i))"
proof
  from assms show "eval f (\<lambda>x. \<Union>i. s i x) \<subseteq> (\<Union>i. eval f (s i))" using lfun_cont_aux2 by auto
  from assms show "(\<Union>i. eval f (s i)) \<subseteq> eval f (\<lambda>x. \<Union>i. s i x)" using lfun_cont_aux1 by blast
qed



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

(* Parikh vector *)

definition parikh_vec :: "'t list \<Rightarrow> ('t \<Rightarrow> nat)" where
  "parikh_vec xs c = length (filter (\<lambda>x. c = x) xs)"

definition vec0 :: "'t \<Rightarrow> nat" where
  "vec0 c \<equiv> 0"

lemma parikh_vec_concat: "parikh_vec (u@v) = (\<lambda>c. parikh_vec u c + parikh_vec v c)"
  by (auto simp add: parikh_vec_def)

lemma parikh_vec_commut: "parikh_vec (u@v) = parikh_vec (v@u)"
  by (auto simp add: parikh_vec_def)

lemma parikh_vec_left_conc: "parikh_vec u = parikh_vec u' \<Longrightarrow> parikh_vec (u@v) = parikh_vec (u'@v)"
  unfolding parikh_vec_def by (metis filter_append replicate_length_filter)

lemma parikh_vec_right_conc: "parikh_vec u = parikh_vec u' \<Longrightarrow> parikh_vec (v@u) = parikh_vec (v@u')"
  unfolding parikh_vec_def by (metis filter_append replicate_length_filter)

(* Parikh image *)

definition parikh_img :: "'t lang \<Rightarrow> ('t \<Rightarrow> nat) set" where
  "parikh_img L = { parikh_vec w | w. w \<in> L }"

(* TODO: really necessary? *)
definition subseteq_comm :: "'t lang \<Rightarrow> 't lang \<Rightarrow> bool" where
  "subseteq_comm L1 L2 \<equiv> parikh_img L1 \<subseteq> parikh_img L2"

lemma "w \<in> L \<Longrightarrow> parikh_vec w \<in> parikh_img L"
  unfolding parikh_img_def by auto

lemma "parikh_vec w \<in> parikh_img L \<Longrightarrow> \<exists>w'. parikh_vec w = parikh_vec w' \<and> w' \<in> L"
  unfolding parikh_img_def by blast

lemma parikh_img_Un [simp]: "parikh_img (L1 \<union> L2) = parikh_img L1 \<union> parikh_img L2"
  by (auto simp add: parikh_img_def)

lemma parikh_img_UNION: "parikh_img (\<Union>(L ` I)) = \<Union> ((\<lambda>i. parikh_img (L i)) ` I)"
  by (auto simp add: parikh_img_def)

lemma parikh_img_mono: "A \<subseteq> B \<Longrightarrow> parikh_img A \<subseteq> parikh_img B"
  unfolding parikh_img_def by fast

lemma parikh_img_conc: "parikh_img (L1 @@ L2) = { (\<lambda>c. v1 c + v2 c) | v1 v2. v1 \<in> parikh_img L1 \<and> v2 \<in> parikh_img L2 }" (is "_ = ?R")
proof -
  have "parikh_img (L1 @@ L2) = { parikh_vec (u@v) | u v. u \<in> L1 \<and> v \<in> L2 }" (is "_ = ?M")
    using parikh_img_def[of "L1 @@ L2"] conc_def by blast
  moreover have "?M \<subseteq> ?R"
    using parikh_vec_concat parikh_img_def by blast
  moreover have "?R \<subseteq> ?M"
  proof
    fix x
    assume "x \<in> ?R"
    then obtain v1 v2 where v1_v2: "v1 \<in> parikh_img L1 \<and> v2 \<in> parikh_img L2 \<and> x = (\<lambda>c. v1 c + v2 c)"
      by auto
    then obtain u1 u2 where "u1 \<in> L1" "parikh_vec u1 = v1" "u2 \<in> L2" "parikh_vec u2 = v2"
      using parikh_img_def by (smt (verit) mem_Collect_eq)
    then show "x \<in> ?M"
      using parikh_vec_concat[of u1 u2] v1_v2 by force
  qed
  ultimately show ?thesis by auto
qed

lemma parikh_img_commut: "parikh_img (L1 @@ L2) = parikh_img (L2 @@ L1)"
proof -
  have "{ (\<lambda>c. v1 c + v2 c) | v1 v2. v1 \<in> parikh_img L1 \<and> v2 \<in> parikh_img L2 } =
        { (\<lambda>c. v1 c + v2 c) | v1 v2. v1 \<in> parikh_img L2 \<and> v2 \<in> parikh_img L1 }"
    using add.commute by blast
  then show ?thesis
    using parikh_img_conc[of L1] parikh_img_conc[of L2] by auto
qed

lemma parikh_conc_right: "parikh_img A = parikh_img B \<Longrightarrow> parikh_img (A @@ C) = parikh_img (B @@ C)"
  by (auto simp add: parikh_img_conc)

lemma parikh_conc_left: "parikh_img A = parikh_img B \<Longrightarrow> parikh_img (C @@ A) = parikh_img (C @@ B)"
  by (auto simp add: parikh_img_conc)

lemma parikh_pow_distrib: "parikh_img A = parikh_img B \<Longrightarrow> parikh_img (A ^^ n) = parikh_img (B ^^ n)"
  by (induction n) (auto simp add: parikh_img_conc)

lemma parikh_star_distrib:
  assumes "parikh_img A = parikh_img B"
  shows "parikh_img (star A) = parikh_img (star B)"
proof
  show "parikh_img (star A) \<subseteq> parikh_img (star B)"
  proof
    fix v
    assume "v \<in> parikh_img (star A)"
    then obtain w where w_intro: "parikh_vec w = v \<and> w \<in> star A" unfolding parikh_img_def by blast
    then obtain n where "w \<in> A ^^ n" unfolding star_def by blast
    then have "v \<in> parikh_img (A ^^ n)" using w_intro unfolding parikh_img_def by blast
    with assms have "v \<in> parikh_img (B ^^ n)" using parikh_pow_distrib by blast
    then show "v \<in> parikh_img (star B)" unfolding star_def using parikh_img_UNION by fastforce
  qed
  show "parikh_img (star B) \<subseteq> parikh_img (star A)"
  proof
    fix v
    assume "v \<in> parikh_img (star B)"
    then obtain w where w_intro: "parikh_vec w = v \<and> w \<in> star B" unfolding parikh_img_def by blast
    then obtain n where "w \<in> B ^^ n" unfolding star_def by blast
    then have "v \<in> parikh_img (B ^^ n)" using w_intro unfolding parikh_img_def by blast
    with assms have "v \<in> parikh_img (A ^^ n)" using parikh_pow_distrib by blast
    then show "v \<in> parikh_img (star A)" unfolding star_def using parikh_img_UNION by fastforce
  qed
qed


lemma parikh_img_union_pow_aux1:
  assumes "v \<in> parikh_img ((A \<union> B) ^^ n)"
    shows "v \<in> parikh_img (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))"
using assms proof (induction n arbitrary: v)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain w where w_intro: "w \<in> (A \<union> B) ^^ (Suc n) \<and> parikh_vec w = v"
    unfolding parikh_img_def by auto
  then obtain w1 w2 where w1_w2_intro: "w = w1@w2 \<and> w1 \<in> A \<union> B \<and> w2 \<in> (A \<union> B) ^^ n" by fastforce
  let ?v1 = "parikh_vec w1" and ?v2 = "parikh_vec w2"

  from w1_w2_intro have "?v2 \<in> parikh_img ((A \<union> B) ^^ n)" unfolding parikh_img_def by blast
  with Suc.IH have "?v2 \<in> parikh_img (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))" by auto
  then obtain w2' where w2'_intro: "parikh_vec w2' = parikh_vec w2 \<and>
      w2' \<in> (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))" unfolding parikh_img_def by fastforce
  then obtain i where i_intro: "i \<le> n \<and> w2' \<in> A ^^ i @@ B ^^ (n-i)" by blast

  from w1_w2_intro w2'_intro have "parikh_vec w = parikh_vec (w1@w2')"
    using parikh_vec_right_conc by metis
  moreover have "parikh_vec (w1@w2') \<in> parikh_img (\<Union>i \<le> Suc n. A ^^ i @@ B ^^ (Suc n-i))"
  proof (cases "w1 \<in> A")
    case True
    with i_intro have Suc_i_valid: "Suc i \<le> Suc n" and "w1@w2' \<in> A ^^ (Suc i) @@ B ^^ (Suc n - Suc i)"
      by (auto simp add: conc_assoc)
    then have "parikh_vec (w1@w2') \<in> parikh_img (A ^^ (Suc i) @@ B ^^ (Suc n - Suc i))"
      unfolding parikh_img_def by auto
    with Suc_i_valid parikh_img_UNION show ?thesis by fast
  next
    case False
    with w1_w2_intro have "w1 \<in> B" by blast
    with i_intro have "parikh_vec (w1@w2') \<in> parikh_img (B @@ A ^^ i @@ B ^^ (n-i))"
      unfolding parikh_img_def by blast
    then have "parikh_vec (w1@w2') \<in> parikh_img (A ^^ i @@ B ^^ (Suc n-i))"
      using parikh_img_commut conc_assoc
      by (metis Suc_diff_le conc_pow_comm i_intro lang_pow.simps(2))
    with i_intro parikh_img_UNION show ?thesis by fastforce
  qed
  ultimately show ?case using w_intro by auto
qed

(*lemma parikh_img_union_pow_aux2:
  assumes "v \<in> parikh_img (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))"
  shows "v \<in> parikh_img ((A \<union> B) ^^ n)"
proof -
  from assms parikh_img_UNION have "v \<in> (\<Union>i\<le>n. parikh_img (A ^^ i @@B ^^ (n-i)))" by metis
  then obtain i where i_leq_n: "i \<le> n" and "v \<in> parikh_img (A ^^ i @@ B ^^ (n-i))" by blast
  then obtain w where w_intro: "parikh_vec w = v \<and> w \<in> A ^^ i @@ B ^^ (n-i)"
    unfolding parikh_img_def by blast
  then have "w \<in> (A \<union> B) ^^ i @@ B ^^ (n-i)" by (meson conc_mono langpow_mono subset_eq sup_ge1)
  then have "w \<in> (A \<union> B) ^^ i @@ (A \<union> B) ^^ (n-i)" by (meson conc_mono langpow_mono subset_eq sup_ge2)
  then have "w \<in> (A \<union> B) ^^ n" using lang_pow_add[of "i" "n-i" "A\<union>B"] i_leq_n by simp
  then show ?thesis using w_intro unfolding parikh_img_def by blast
qed*)

lemma parikh_img_star_aux1:
  assumes "v \<in> parikh_img (star (A \<union> B))"
  shows "v \<in> parikh_img (star A @@ star B)"
proof -
  from assms have "v \<in> (\<Union>n. parikh_img ((A \<union> B) ^^ n))"
    unfolding star_def using parikh_img_UNION by metis
  then obtain n where "v \<in> parikh_img ((A \<union> B) ^^ n)" by blast
  then have "v \<in> parikh_img (\<Union>i \<le> n. A ^^ i @@ B ^^ (n-i))"
    using parikh_img_union_pow_aux1 by auto
  then have "v \<in> (\<Union>i\<le>n. parikh_img (A ^^ i @@ B ^^ (n-i)))" using parikh_img_UNION by metis
  then obtain i where "i\<le>n \<and> v \<in> parikh_img (A ^^ i @@ B ^^ (n-i))" by blast
  then obtain w where w_intro: "parikh_vec w = v \<and> w \<in> A ^^ i @@ B ^^ (n-i)"
    unfolding parikh_img_def by blast
  then obtain w1 w2 where w_decomp: "w=w1@w2 \<and> w1 \<in> A ^^ i \<and> w2 \<in> B ^^ (n-i)" by blast
  then have "w1 \<in> star A" and "w2 \<in> star B" by auto
  with w_decomp have "w \<in> star A @@ star B" by auto
  with w_intro show ?thesis unfolding parikh_img_def by blast
qed

lemma parikh_img_star_aux2:
  assumes "v \<in> parikh_img (star A @@ star B)"
  shows "v \<in> parikh_img (star (A \<union> B))"
proof -
  from assms obtain w where w_intro: "parikh_vec w = v \<and> w \<in> star A @@ star B"
    unfolding parikh_img_def by blast
  then obtain w1 w2 where w_decomp: "w=w1@w2 \<and> w1 \<in> star A \<and> w2 \<in> star B" by blast
  then obtain i j where "w1 \<in> A ^^ i" and w2_intro: "w2 \<in> B ^^ j" unfolding star_def by blast
  then have w1_in_union: "w1 \<in> (A \<union> B) ^^ i" using langpow_mono by blast
  from w2_intro have "w2 \<in> (A \<union> B) ^^ j" using langpow_mono by blast
  with w1_in_union w_decomp have "w \<in> (A \<union> B) ^^ (i+j)" using lang_pow_add by fast
  with w_intro show ?thesis unfolding parikh_img_def by auto
qed

lemma parikh_img_star: "parikh_img (star (A \<union> B)) = parikh_img (star A @@ star B)"
proof
  show "parikh_img (star (A \<union> B)) \<subseteq> parikh_img (star A @@ star B)" using parikh_img_star_aux1 by auto
  show "parikh_img (star A @@ star B) \<subseteq> parikh_img (star (A \<union> B))" using parikh_img_star_aux2 by auto
qed


lemma parikh_img_star2: "parikh_img (star (star E @@ F)) = parikh_img ({[]} \<union> star E @@ star F @@ F)"
  sorry


lemma parikh_img_arden_aux:
  assumes "parikh_img (A @@ X \<union> B) = parikh_img X"
  shows "parikh_img (A ^^ n @@ B) \<subseteq> parikh_img X"
using assms proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have "parikh_img (A ^^ (Suc n) @@ B) \<subseteq> parikh_img (A @@ A ^^ n @@B)"
    by (simp add: conc_assoc)
  moreover from Suc parikh_conc_left have "\<dots> \<subseteq> parikh_img (A @@ X)"
    by (metis conc_Un_distrib(1) parikh_img_Un sup.orderE sup.orderI)
  moreover from Suc.prems have "\<dots> \<subseteq> parikh_img X" by auto
  ultimately show ?case by fast
qed

lemma parikh_img_arden:
  assumes "parikh_img (A @@ X \<union> B) = parikh_img X"
  shows "parikh_img (star A @@ B) \<subseteq> parikh_img X"
proof
  fix x
  assume "x \<in> parikh_img (star A @@ B)"
  then have "\<exists>n. x \<in> parikh_img (A ^^ n @@ B)"
    unfolding star_def by (simp add: conc_UNION_distrib(2) parikh_img_UNION)
  then obtain n where "x \<in> parikh_img (A ^^ n @@ B)" by blast
  then show "x \<in> parikh_img X" using parikh_img_arden_aux[OF assms] by fast
qed



section \<open>systems of equations\<close>

type_synonym 'a eq_sys = "'a lfun list"

(* sys independent on variables \<le> n *)
definition indep_ub :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> bool" where
  "indep_ub sys n \<equiv> \<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x > n"

(* sys independent on variables \<ge> n *)
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


lemma g_pre_indep:
  assumes "i < length f_sys"
  shows "\<forall>x \<in> vars (g_pre f_sys i n). x \<ge> length f_sys"
proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?upd = "\<lambda>x. if x < length f_sys then g_pre f_sys x n else V x"
  from vars_subst_upper have "vars (g_pre f_sys i (Suc n)) \<subseteq> (\<Union>x. vars (?upd x))" by simp
  moreover have "\<forall>y \<in> vars (?upd x). y \<ge> length f_sys" for x using Suc by simp
  ultimately show ?case by auto
qed


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

(*lemma "(\<Union>n. eval (g_pre f_sys i (Suc n)) s)
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
qed*)

lemma g_pre_g_Union: "(\<Union>n. eval (g_pre f_sys i (Suc n)) s) =
  eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
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
  also have "\<dots> = eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
    using substitution_lemma[of "\<lambda>x. if x < length f_sys then eval (g f_sys x) s else s x"
                                "\<lambda>i. if i < length f_sys then g f_sys i else V i"]
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


lemma lemma_paper:
  assumes "\<forall>eq \<in> set f_sys. regular_fun eq"
    shows "\<exists>g_sys. length g_sys = length f_sys \<and> indep_ub g_sys (length f_sys - 1)
                \<and> (\<forall>s. solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys g_sys s)
                \<and> (\<forall>s. solves_eq_sys g_sys s \<longrightarrow> solves_eq_sys f_sys s)"
proof -
  let ?g_sys = "map (\<lambda>i. g f_sys i) [0..<length f_sys]"
  have length_g_sys: "length ?g_sys = length f_sys" by auto
  have indep_g_sys: "indep_ub ?g_sys (length f_sys - 1)"
    unfolding indep_ub_def using g_indep by fastforce

  have "\<lbrakk> i < length f_sys; solves_ineq_sys f_sys s \<rbrakk> \<Longrightarrow> eval (?g_sys ! i) s \<subseteq> s i" for s i
    using solves_g_if_solves_f_ineq solves_ineq_sys_def by fastforce
  then have g_sol_of_f: "solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys ?g_sys s" for s
    using solves_ineq_sys_def by (metis length_g_sys)

  have f_sol_of_g: "solves_eq_sys ?g_sys s \<longrightarrow> solves_eq_sys f_sys s" for s
    using solves_f_if_solves_g_eq solves_eq_sys_def
    by (metis add_0 diff_zero length_g_sys nth_map_upt)

  from length_g_sys indep_g_sys g_sol_of_f f_sol_of_g show ?thesis by blast
qed


section \<open>The theorem from the paper\<close>

definition regular_fun' :: "nat \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "regular_fun' x f \<equiv> \<exists>p q. regular_fun p \<and> regular_fun q \<and>
    f = Union2 p (Conc q (V x)) \<and> (\<forall>y \<in> vars p. y \<noteq> x)"

lemma "regular_fun' x f \<Longrightarrow> regular_fun f"
  unfolding regular_fun'_def by fast

lemma emptyset_regular: "regular_fun (N {})"
  using lang.simps(1) by blast

lemma epsilon_regular: "regular_fun (N {[]})"
  using lang.simps(2) by blast


lemma "regular_fun f \<Longrightarrow>
    \<exists>f'. regular_fun' x f' \<and> (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))"
proof (induction rule: regular_fun.induct)
  case (Variable y)
  then show ?case
  proof (cases "x=y")
    let ?f' = "Union2 (N {}) (Conc (N {[]}) (V x))"
    case True
    then have "regular_fun' x ?f'"
      unfolding regular_fun'_def by (simp add: emptyset_regular epsilon_regular)
    moreover have "eval ?f' s = eval (V y) s" for s :: "'a state"
      using True by simp
    ultimately show ?thesis by metis
  next
    let ?f' = "Union2 (V y) (Conc (N {}) (V x))"
    case False
    then have "regular_fun' x ?f'"
      unfolding regular_fun'_def by (auto simp add: emptyset_regular epsilon_regular)
    moreover have "eval ?f' s = eval (V y) s" for s :: "'a state"
      using False by simp
    ultimately show ?thesis by metis
  qed
next
  case (Const l)
  let ?f' = "Union2 (N l) (Conc (N {}) (V x))"
  have "regular_fun' x ?f'"
    unfolding regular_fun'_def using Const by (auto simp add: emptyset_regular)
  moreover have "eval ?f' s = eval (N l) s" for s :: "'a state" by simp
  ultimately show ?case by metis
next
  case (Union2 f1 f2)
  then obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and>
      (\<forall>s. parikh_img (eval f1 s) = parikh_img (eval f1' s))"
    and f2'_intro: "regular_fun' x f2' \<and> (\<forall>s. parikh_img (eval f2 s) = parikh_img (eval f2' s))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "regular_fun p1 \<and> regular_fun q1 \<and>
    f1' = Union2 p1 (Conc q1 (V x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "regular_fun p2 \<and> regular_fun q2 \<and> f2' = Union2 p2 (Conc q2 (V x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?f' = "Union2 (Union2 p1 p2) (Conc (Union2 q1 q2) (V x))"
  have "regular_fun' x ?f'" unfolding regular_fun'_def using p1_q1_intro p2_q2_intro by auto
  moreover have "parikh_img (eval ?f' s) = parikh_img (eval (Union2 f1 f2) s)" for s
    using p1_q1_intro p2_q2_intro f1'_intro f2'_intro
    by (simp add: conc_Un_distrib(2) sup_assoc sup_left_commute)
  ultimately show ?case by metis
next
  case (Conc f1 f2)
  then obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and>
      (\<forall>s. parikh_img (eval f1 s) = parikh_img (eval f1' s))"
    and f2'_intro: "regular_fun' x f2' \<and> (\<forall>s. parikh_img (eval f2 s) = parikh_img (eval f2' s))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "regular_fun p1 \<and> regular_fun q1 \<and>
    f1' = Union2 p1 (Conc q1 (V x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "regular_fun p2 \<and> regular_fun q2 \<and> f2' = Union2 p2 (Conc q2 (V x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?q' = "Union2 (Conc q1 (Conc (V x) q2)) (Union2 (Conc p1 q2) (Conc q1 p2))"
  let ?f' = "Union2 (Conc p1 p2) (Conc ?q' (V x))"

  have "\<forall>s. (parikh_img (eval (Conc f1 f2) s) = parikh_img (eval ?f' s))"
  proof (rule allI)
    fix s
    have f2_subst: "parikh_img (eval f2 s) = parikh_img (eval p2 s \<union> eval q2 s @@ s x)"
      using p2_q2_intro f2'_intro by auto

    have "parikh_img (eval (Conc f1 f2) s) = parikh_img ((eval p1 s \<union> eval q1 s @@ s x) @@ eval f2 s)"
      using p1_q1_intro f1'_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(5) parikh_conc_right)
    also have "\<dots> = parikh_img (eval p1 s @@ eval f2 s \<union> eval q1 s @@ s x @@ eval f2 s)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = parikh_img (eval p1 s @@ (eval p2 s \<union> eval q2 s @@ s x)
        \<union> eval q1 s @@ s x @@ (eval p2 s \<union> eval q2 s @@ s x))"
      using f2_subst by (smt (verit, ccfv_threshold) parikh_conc_right parikh_img_Un parikh_img_commut)
    also have "\<dots> = parikh_img (eval p1 s @@ eval p2 s \<union> (eval p1 s @@ eval q2 s @@ s x \<union>
        eval q1 s @@ eval p2 s @@ s x \<union> eval q1 s @@ s x @@ eval q2 s @@ s x))"
      using parikh_img_commut by (smt (z3) conc_Un_distrib(1) parikh_conc_right parikh_img_Un sup_assoc)
    also have "\<dots> = parikh_img (eval p1 s @@ eval p2 s \<union> (eval p1 s @@ eval q2 s \<union>
        eval q1 s @@ eval p2 s \<union> eval q1 s @@ s x @@ eval q2 s) @@ s x)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = parikh_img (eval ?f' s)"
      by (simp add: Un_commute)
    finally show "parikh_img (eval (Conc f1 f2) s) = parikh_img (eval ?f' s)" .
  qed
  moreover have "regular_fun' x ?f'" unfolding regular_fun'_def using p1_q1_intro p2_q2_intro by auto
  ultimately show ?case by metis
next
  case (Star f)
  then obtain f' where f'_intro: "regular_fun' x f' \<and>
      (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))" by auto
  then obtain p q where p_q_intro: "regular_fun p \<and> regular_fun q \<and>
    f' = Union2 p (Conc q (V x)) \<and> (\<forall>y \<in> vars p. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?q_new = "Conc (Star p) (Conc (Star (Conc q (V x))) (Conc (Star (Conc q (V x))) q))"
  let ?f_new = "Union2 (Star p) (Conc ?q_new (V x))"

  have "\<forall>s. (parikh_img (eval (Star f) s) = parikh_img (eval ?f_new s))"
  proof (rule allI)
    fix s
    have "parikh_img (eval (Star f) s) = parikh_img (star (eval p s \<union> eval q s @@ s x))"
      using f'_intro parikh_star_distrib p_q_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(5) eval.simps(6))
    also have "\<dots> = parikh_img (star (eval p s) @@ star (eval q s @@ s x))"
      using parikh_img_star by blast
    also have "\<dots> = parikh_img (star (eval p s) @@
        star ({[]} \<union> star (eval q s @@ s x) @@ eval q s @@ s x))"
      by (metis Un_commute conc_star_comm star_idemp star_unfold_left)
    also have "\<dots> = parikh_img (star (eval p s) @@ star (star (eval q s @@ s x) @@ eval q s @@ s x))"
      by auto
    also have "\<dots> = parikh_img (star (eval p s) @@ ({[]} \<union> star (eval q s @@ s x)
        @@ star (eval q s @@ s x) @@ eval q s @@ s x))"
      using parikh_img_star2 parikh_conc_left by blast
    also have "\<dots> = parikh_img (star (eval p s) @@ {[]} \<union> star (eval p s) @@ star (eval q s @@ s x)
        @@ star (eval q s @@ s x) @@ eval q s @@ s x)" by (metis conc_Un_distrib(1))
    also have "\<dots> = parikh_img (eval ?f_new s)" by (simp add: conc_assoc)
    finally show "parikh_img (eval (Star f) s) = parikh_img (eval ?f_new s)" .
  qed
  moreover have "regular_fun' x ?f_new" unfolding regular_fun'_def using p_q_intro by fastforce
  ultimately show ?case by metis
qed


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
