theory Parikh_Img
  imports 
    "./Lfun"
    "HOL-Library.Multiset"
begin


section \<open>Parikh image\<close>

(* a Parikh vector is represented as a multiset *)

(* compute Parikh vector for given word *)
abbreviation parikh_vec where
  "parikh_vec \<equiv> mset"

(* Parikh image for a given language *)
definition parikh_img :: "'a lang \<Rightarrow> 'a multiset set" where
  "parikh_img L \<equiv> parikh_vec ` L"

(* TODO: really necessary? *)
definition subseteq_comm :: "'t lang \<Rightarrow> 't lang \<Rightarrow> bool" where
  "subseteq_comm L1 L2 \<equiv> parikh_img L1 \<subseteq> parikh_img L2"


lemma parikh_img_Un [simp]: "parikh_img (L1 \<union> L2) = parikh_img L1 \<union> parikh_img L2"
  by (auto simp add: parikh_img_def)

lemma parikh_img_UNION: "parikh_img (\<Union>(L ` I)) = \<Union> ((\<lambda>i. parikh_img (L i)) ` I)"
  by (auto simp add: parikh_img_def)

lemma parikh_img_mono: "A \<subseteq> B \<Longrightarrow> parikh_img A \<subseteq> parikh_img B"
  unfolding parikh_img_def by fast

lemma parikh_img_mono_eq: "A = B \<Longrightarrow> parikh_img A = parikh_img B"
  using parikh_img_mono by blast


lemma parikh_img_Star_pow: "v \<in> parikh_img (eval (Star f) s) \<Longrightarrow> \<exists>n. v \<in> parikh_img (eval f s ^^ n)"
proof -
  assume "v \<in> parikh_img (eval (lfun.Star f) s)"
  then have "v \<in> parikh_img (star (eval f s))" by simp
  then show ?thesis unfolding star_def by (simp add: parikh_img_UNION)
qed


lemma parikh_img_conc: "parikh_img (L1 @@ L2) = { v1 + v2 | v1 v2. v1 \<in> parikh_img L1 \<and> v2 \<in> parikh_img L2 }"
  unfolding parikh_img_def by force

lemma parikh_img_commut: "parikh_img (L1 @@ L2) = parikh_img (L2 @@ L1)"
proof -
  have "{ v1 + v2 | v1 v2. v1 \<in> parikh_img L1 \<and> v2 \<in> parikh_img L2 } = 
        { v2 + v1 | v1 v2. v1 \<in> parikh_img L1 \<and> v2 \<in> parikh_img L2 }"
    using add.commute by blast
  then show ?thesis
    using parikh_img_conc[of L1] parikh_img_conc[of L2] by auto
qed


lemma parikh_conc_right_subset: "parikh_img A \<subseteq> parikh_img B \<Longrightarrow> parikh_img (A @@ C) \<subseteq> parikh_img (B @@ C)"
  by (auto simp add: parikh_img_conc)

lemma parikh_conc_left_subset: "parikh_img A \<subseteq> parikh_img B \<Longrightarrow> parikh_img (C @@ A) \<subseteq> parikh_img (C @@ B)"
  by (auto simp add: parikh_img_conc)

lemma parikh_conc_subset:
  assumes "parikh_img A \<subseteq> parikh_img C"
      and "parikh_img B \<subseteq> parikh_img D"
    shows "parikh_img (A @@ B) \<subseteq> parikh_img (C @@ D)"
  using assms parikh_conc_right_subset parikh_conc_left_subset by blast

lemma parikh_conc_right: "parikh_img A = parikh_img B \<Longrightarrow> parikh_img (A @@ C) = parikh_img (B @@ C)"
  by (auto simp add: parikh_img_conc)

lemma parikh_conc_left: "parikh_img A = parikh_img B \<Longrightarrow> parikh_img (C @@ A) = parikh_img (C @@ B)"
  by (auto simp add: parikh_img_conc)

lemma parikh_pow_mono: "parikh_img A \<subseteq> parikh_img B \<Longrightarrow> parikh_img (A ^^ n) \<subseteq> parikh_img (B ^^ n)"
  by (induction n) (auto simp add: parikh_img_conc)

lemma parikh_star_mono:
  assumes "parikh_img A \<subseteq> parikh_img B"
  shows "parikh_img (star A) \<subseteq> parikh_img (star B)"
proof
  fix v
  assume "v \<in> parikh_img (star A)"
  then obtain w where w_intro: "parikh_vec w = v \<and> w \<in> star A" unfolding parikh_img_def by blast
  then obtain n where "w \<in> A ^^ n" unfolding star_def by blast
  then have "v \<in> parikh_img (A ^^ n)" using w_intro unfolding parikh_img_def by blast
  with assms have "v \<in> parikh_img (B ^^ n)" using parikh_pow_mono by blast
  then show "v \<in> parikh_img (star B)" unfolding star_def using parikh_img_UNION by fastforce
qed

lemma parikh_star_mono_eq:
  assumes "parikh_img A = parikh_img B"
  shows "parikh_img (star A) = parikh_img (star B)"
  using parikh_star_mono by (metis Orderings.order_eq_iff assms)


lemma parikh_img_subst_mono:
  assumes "\<forall>i. parikh_img (eval (A i) s) \<subseteq> parikh_img (eval (B i) s)"
  shows "parikh_img (eval (subst f A) s) \<subseteq> parikh_img (eval (subst f B) s)"
using assms proof (induction f)
  case (UnionC f)
  then have "parikh_img (\<Union>i. eval (subst (f i) A) s) \<subseteq> parikh_img (\<Union>i. eval (subst (f i) B) s)"
    by (simp add: SUP_mono' parikh_img_UNION)
  then show ?case by simp
next
  case (Conc f1 f2)
  then have "parikh_img (eval (subst f1 A) s @@ eval (subst f2 A) s)
              \<subseteq> parikh_img (eval (subst f1 B) s @@ eval (subst f2 B) s)"
    using parikh_conc_subset by blast
  then show ?case by simp
next
  case (Star f)
  then have "parikh_img (star (eval (subst f A) s)) \<subseteq> parikh_img (star (eval (subst f B) s))"
    using parikh_star_mono by blast
  then show ?case by simp
qed auto

lemma parikh_img_subst_mono_upd:
  assumes "parikh_img (eval A s) \<subseteq> parikh_img (eval B s)"
  shows "parikh_img (eval (subst f (V(x := A))) s) \<subseteq> parikh_img (eval (subst f (V(x := B))) s)"
  using parikh_img_subst_mono[of "V(x := A)" s "V(x := B)"] assms by auto

lemma parikh_img_subst_mono_eq:
  assumes "\<forall>i. parikh_img (eval (A i) s) = parikh_img (eval (B i) s)"
  shows "parikh_img (eval (subst f (\<lambda>i. A i)) s) = parikh_img (eval (subst f (\<lambda>i. B i)) s)"
  using parikh_img_subst_mono assms by blast

lemma lfun_mono_parikh:
  assumes "\<forall>i \<in> vars f. parikh_img (s i) \<subseteq> parikh_img (s' i)"
  shows "parikh_img (eval f s) \<subseteq> parikh_img (eval f s')"
using assms proof (induction rule: lfun.induct)
case (Conc f1 f2)
  then have "parikh_img (eval f1 s @@ eval f2 s) \<subseteq> parikh_img (eval f1 s' @@ eval f2 s')"
    using parikh_conc_subset by (metis UnCI vars.simps(5))
  then show ?case by simp
qed (auto simp add: SUP_mono' parikh_img_UNION parikh_star_mono)


lemma lfun_mono_parikh_eq:
  assumes "\<forall>i \<in> vars f. parikh_img (s i) = parikh_img (s' i)"
  shows "parikh_img (eval f s) = parikh_img (eval f s')"
  using assms lfun_mono_parikh by blast



section \<open>(E\<union>F)* and E*F* have the same Parikh image\<close>

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
    by simp
  moreover have "parikh_vec (w1@w2') \<in> parikh_img (\<Union>i \<le> Suc n. A ^^ i @@ B ^^ (Suc n-i))"
  proof (cases "w1 \<in> A")
    case True
    with i_intro have Suc_i_valid: "Suc i \<le> Suc n" and "w1@w2' \<in> A ^^ (Suc i) @@ B ^^ (Suc n - Suc i)"
      by (auto simp add: conc_assoc)
    then have "parikh_vec (w1@w2') \<in> parikh_img (A ^^ (Suc i) @@ B ^^ (Suc n - Suc i))"
      unfolding parikh_img_def by blast
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



section \<open>(E*F)* and {\<epsilon>} \<union> E*F*F have the same Parikh image\<close>

(* It even holds = but this is not necessary *)
lemma parikh_img_conc_pow: "parikh_img ((A @@ B) ^^ n) \<subseteq> parikh_img (A ^^ n @@ B ^^ n)"
proof (induction n)
  case (Suc n)
  then have "parikh_img ((A @@ B) ^^ n @@ A @@ B) \<subseteq> parikh_img (A ^^ n @@ B ^^ n @@ A @@ B)"
    using parikh_conc_right_subset conc_assoc by metis
  also have "\<dots> = parikh_img (A ^^ n @@ A @@ B ^^ n @@ B)"
    by (metis parikh_img_commut conc_assoc parikh_conc_left)
  finally show ?case by (simp add: conc_assoc conc_pow_comm)
qed simp

lemma parikh_img_conc_star: "parikh_img (star (A @@ B)) \<subseteq> parikh_img (star A @@ star B)"
proof
  fix v
  assume "v \<in> parikh_img (star (A @@ B))"
  then have "\<exists>n. v \<in> parikh_img ((A @@ B) ^^ n)" unfolding star_def by (simp add: parikh_img_UNION)
  then obtain n where "v \<in> parikh_img ((A @@ B) ^^ n)" by blast
  with parikh_img_conc_pow have "v \<in> parikh_img (A ^^ n @@ B ^^ n)" by fast
  then have "v \<in> parikh_img (A ^^ n @@ star B)"
    unfolding star_def using parikh_conc_left_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
  then show "v \<in> parikh_img (star A @@ star B)"
    unfolding star_def using parikh_conc_right_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
qed

lemma parikh_img_conc_pow2: "parikh_img ((A @@ B) ^^ Suc n) \<subseteq> parikh_img (star A @@ star B @@ B)"
proof
  fix v
  assume "v \<in> parikh_img ((A @@ B) ^^ Suc n)"
  with parikh_img_conc_pow have "v \<in> parikh_img (A ^^ Suc n @@ B ^^ n @@ B)"
    by (metis conc_pow_comm lang_pow.simps(2) subsetD)
  then have "v \<in> parikh_img (star A @@ B ^^ n @@ B)"
    unfolding star_def using parikh_conc_right_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
  then show "v \<in> parikh_img (star A @@ star B @@ B)"
    unfolding star_def using parikh_conc_right_subset parikh_conc_left_subset
    by (metis (no_types, lifting) Sup_upper parikh_img_mono rangeI subset_eq)
qed

lemma parikh_img_star2_aux1:
  "parikh_img (star (star E @@ F)) \<subseteq> parikh_img ({[]} \<union> star E @@ star F @@ F)"
proof
  fix v
  assume "v \<in> parikh_img (star (star E @@ F))"
  then have "\<exists>n. v \<in> parikh_img ((star E @@ F) ^^ n)"
    unfolding star_def by (simp add: parikh_img_UNION)
  then obtain n where v_in_pow_n: "v \<in> parikh_img ((star E @@ F) ^^ n)" by blast
  show "v \<in> parikh_img ({[]} \<union> star E @@ star F @@ F)"
  proof (cases n)
    case 0
    with v_in_pow_n have "v = parikh_vec []" unfolding parikh_img_def by simp
    then show ?thesis unfolding parikh_img_def by blast
  next
    case (Suc m)
    with parikh_img_conc_pow2 v_in_pow_n have "v \<in> parikh_img (star (star E) @@ star F @@ F)" by blast
    then show ?thesis by (metis UnCI parikh_img_Un star_idemp)
  qed
qed

lemma parikh_img_star2_aux2: "parikh_img (star E @@ star F @@ F) \<subseteq> parikh_img (star (star E @@ F))"
proof -
  have "F \<subseteq> star E @@ F" unfolding star_def using Nil_in_star
    by (metis concI_if_Nil1 star_def subsetI)
  then have "parikh_img (star E @@ F @@ star F) \<subseteq> parikh_img (star E @@ F @@ star (star E @@ F))"
    using parikh_conc_left_subset parikh_img_mono parikh_star_mono by meson
  also have "\<dots> \<subseteq> parikh_img (star (star E @@ F))"
    by (metis conc_assoc inf_sup_ord(3) parikh_img_mono star_unfold_left)
  finally show ?thesis using conc_star_comm by metis
qed

lemma parikh_img_star2: "parikh_img (star (star E @@ F)) = parikh_img ({[]} \<union> star E @@ star F @@ F)"
proof
  from parikh_img_star2_aux1
    show "parikh_img (star (star E @@ F)) \<subseteq> parikh_img ({[]} \<union> star E @@ star F @@ F)" .
  from parikh_img_star2_aux2
    show "parikh_img ({[]} \<union> star E @@ star F @@ F) \<subseteq> parikh_img (star (star E @@ F))"
    by (metis le_sup_iff parikh_img_Un star_unfold_left sup.cobounded2)
qed



section \<open>A homogeneous-like property for regular functions\<close>

lemma reg_fun_homogeneous_aux:
  assumes "regular_fun f"
      and "s x = star Y @@ Z"
    shows "parikh_img (eval f s) \<subseteq> parikh_img (star Y @@ eval f (s(x := Z)))"
using assms proof (induction rule: regular_fun.induct)
  case (Variable y)
  show ?case
  proof (cases "x = y")
    case True
    with Variable show ?thesis by simp
  next
    case False
    have "eval (V y) s \<subseteq> star Y @@ eval (V y) s" by (metis Nil_in_star concI_if_Nil1 subsetI)
    with False parikh_img_mono show ?thesis by auto
  qed
next
  case (Const l)
  have "eval (N l) s \<subseteq> star Y @@ eval (N l) s" using concI_if_Nil1 by blast
  then show ?case by (simp add: parikh_img_mono)
next
  case (Union2 f g)
  then have "parikh_img (eval (Union2 f g) s) \<subseteq> parikh_img (star Y @@ eval f (s(x := Z)) \<union>
                                                            star Y @@ eval g (s(x := Z)))"
    by fastforce
  then show ?case by (metis conc_Un_distrib(1) eval.simps(3))
next
  case (Conc f g)
  then have "parikh_img (eval (Conc f g) s) \<subseteq> parikh_img ((star Y @@ eval f (s(x := Z)))
                                                          @@ star Y @@ eval g (s(x := Z)))"
    by (metis eval.simps(5) parikh_conc_subset)
  also have "\<dots> = parikh_img (star Y @@ star Y @@ eval f (s(x := Z)) @@ eval g (s(x := Z)))"
    by (metis conc_assoc parikh_conc_right parikh_img_commut)
  also have "\<dots> = parikh_img (star Y @@ eval f (s(x := Z)) @@ eval g (s(x := Z)))"
    by (metis conc_assoc conc_star_star)
  finally show ?case by (metis eval.simps(5))
next
  case (Star f)
  then have "parikh_img (star (eval f s)) \<subseteq> parikh_img (star (star Y @@ eval f (s(x := Z))))"
    using parikh_star_mono by blast
  also from parikh_img_conc_star have "\<dots> \<subseteq> parikh_img (star Y @@ star (eval f (s(x := Z))))"
    by fastforce
  finally show ?case by (metis eval.simps(6))
qed

lemma reg_fun_homogeneous:
  assumes "regular_fun f"
      and "regular_fun y"
      and "regular_fun z"
    shows "parikh_img (eval (subst f (V(x := Conc (Star y) z))) s)
            \<subseteq> parikh_img (eval (Conc (Star y) (subst f (V(x := z)))) s)"
            (is "parikh_img ?L \<subseteq> parikh_img ?R")
proof -
  let ?s' = "s(x := star (eval y s) @@ eval z s)"
  have "parikh_img ?L = parikh_img (eval f ?s')" using substitution_lemma_update[of f] by simp
  also have "\<dots> \<subseteq> parikh_img (star (eval y s) @@ eval f (?s'(x := eval z s)))"
    using assms reg_fun_homogeneous_aux[of f ?s'] unfolding fun_upd_def by auto
  also have "\<dots> = parikh_img ?R" using substitution_lemma[of "s(x := eval z s)"] by simp
  finally show ?thesis .
qed

(* reformulate previous lemma with regular functions as arguments instead of languages *)
lemma reg_fun_homogeneous2:
  assumes "regular_fun f"
      and "regular_fun y"
      and "regular_fun z"
    shows "parikh_img (eval (subst f (V(x := Conc (Star y) z))) s)
            \<subseteq> parikh_img (eval (Conc (Star y) (subst f (V(x := z)))) s)"
            (is "parikh_img ?L \<subseteq> parikh_img ?R")
proof -
  let ?s' = "s(x := star (eval y s) @@ eval z s)"
  have "parikh_img ?L = parikh_img (eval f ?s')"
    using substitution_lemma[of ?s' "V(x := Conc (Star y) z)"] by fastforce
  also have "\<dots> \<subseteq> parikh_img (star (eval y s) @@ eval f (?s'(x := eval z s)))"
    using assms reg_fun_homogeneous_aux[of f ?s'] by (meson fun_upd_apply)
  also have "\<dots> = parikh_img ?R" using substitution_lemma[of "?s'(x := eval z s)"] by simp
  finally show ?thesis .
qed



section \<open>Extension of Arden's lemma to Parikh images\<close>

lemma parikh_img_arden_aux:
  assumes "parikh_img (A @@ X \<union> B) \<subseteq> parikh_img X"
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
  assumes "parikh_img (A @@ X \<union> B) \<subseteq> parikh_img X"
  shows "parikh_img (star A @@ B) \<subseteq> parikh_img X"
proof
  fix x
  assume "x \<in> parikh_img (star A @@ B)"
  then have "\<exists>n. x \<in> parikh_img (A ^^ n @@ B)"
    unfolding star_def by (simp add: conc_UNION_distrib(2) parikh_img_UNION)
  then obtain n where "x \<in> parikh_img (A ^^ n @@ B)" by blast
  then show "x \<in> parikh_img X" using parikh_img_arden_aux[OF assms] by fast
qed


section \<open>Equivalence class of languages with same Parikh image\<close>

definition parikh_img_eq_class :: "'a lang \<Rightarrow> 'a lang set" where
  "parikh_img_eq_class L \<equiv> {L'. parikh_img L' = parikh_img L}"


lemma parikh_img_Union_class: "parikh_img A = parikh_img (\<Union>(parikh_img_eq_class A))"
proof
  let ?A' = "\<Union>(parikh_img_eq_class A)"
  show "parikh_img A \<subseteq> parikh_img ?A'"
    unfolding parikh_img_eq_class_def by (simp add: Union_upper parikh_img_mono)

  show "parikh_img ?A' \<subseteq> parikh_img A"
  proof
    fix v
    assume "v \<in> parikh_img ?A'"
    then obtain a where a_intro: "parikh_vec a = v \<and> a \<in> ?A'"
      unfolding parikh_img_def by blast
    then obtain L where L_intro: "a \<in> L \<and> L \<in> parikh_img_eq_class A"
      unfolding parikh_img_eq_class_def by blast
    then have "parikh_img L = parikh_img A" unfolding parikh_img_eq_class_def by fastforce
    with a_intro L_intro show "v \<in> parikh_img A" unfolding parikh_img_def by blast
  qed
qed


lemma subseteq_comm_subseteq:
  assumes "parikh_img A \<subseteq> parikh_img B"
  shows "A \<subseteq> \<Union>(parikh_img_eq_class B)" (is "A \<subseteq> ?B'")
proof
  fix a
  assume a_in_A: "a \<in> A"
  from assms have "parikh_img A \<subseteq> parikh_img ?B'"
    using parikh_img_Union_class by blast
  with a_in_A have vec_a_in_B': "parikh_vec a \<in> parikh_img ?B'" unfolding parikh_img_def by fast
  then have "\<exists>b. parikh_vec b = parikh_vec a \<and> b \<in> ?B'"
    unfolding parikh_img_def by fastforce
  then obtain b where b_intro: "parikh_vec b = parikh_vec a \<and> b \<in> ?B'" by blast
  with vec_a_in_B' have "parikh_img (?B' \<union> {a}) = parikh_img ?B'"unfolding parikh_img_def by blast
  with parikh_img_Union_class have "parikh_img (?B' \<union> {a}) = parikh_img B" by blast
  then show "a \<in> ?B'" unfolding parikh_img_eq_class_def by blast
qed


end
