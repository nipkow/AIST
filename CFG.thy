theory CFG
imports Main
begin

subsection "CFG and Derivations"

datatype ('n,'t) symb = T 't | N 'n

type_synonym ('n,'t) symbs = "('n,'t) symb list"

type_synonym ('n,'t) prod = "'n \<times> ('n,'t) symbs"

type_synonym ('n,'t) prods = "('n,'t) prod set"

datatype ('n,'t) cfg =  CFG (prods : "('n,'t) prods") (start : "'n")

inductive step1 :: "('n,'t) prods \<Rightarrow> ('n,'t) symbs \<Rightarrow> ('n,'t)symbs \<Rightarrow> bool" ("(_ \<turnstile> _ \<Rightarrow> _)" [50, 0, 50] 50) where
"(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> u @ [N A] @ v \<Rightarrow> u @ \<alpha> @ v"

abbreviation stepn ("(_ \<turnstile> _ \<Rightarrow>'(_') _)" [50, 0, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>(n) v \<equiv> (step1 P ^^ n) u v"

abbreviation steps ("(_ \<turnstile> _ \<Rightarrow>* _)" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>* v \<equiv> ((step1 P) ^**) u v"

definition "Lang P A = {w. P \<turnstile> [N A] \<Rightarrow>* map T w}"

lemma step1_apppend:
  "\<G> \<turnstile> u \<Rightarrow> v \<Longrightarrow> \<G> \<turnstile> u@w \<Rightarrow> v@w"
apply(erule step1.cases)
using step1.intros by fastforce

lemma step1_prepend:
  "\<G> \<turnstile> u \<Rightarrow> v \<Longrightarrow> \<G> \<turnstile> w@u \<Rightarrow> w@v"
apply(erule step1.cases)
by (metis append.assoc step1.intros)

lemma deriv_apppend:
  "\<G> \<turnstile> u \<Rightarrow>* v \<Longrightarrow> \<G> \<turnstile> u@w \<Rightarrow>* v@w"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl)
  then show ?case
    by (meson rtranclp.rtrancl_into_rtrancl step1_apppend)
qed

lemma deriv_prepend:
  "\<G> \<turnstile> u \<Rightarrow>* v \<Longrightarrow> \<G> \<turnstile> w@u \<Rightarrow>* w@v"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl)
  then show ?case
    by (meson rtranclp.rtrancl_into_rtrancl step1_prepend)
qed

lemma deriv1_if_valid_prod:
  "(A, \<alpha>) \<in> P \<Longrightarrow> P \<turnstile> [N A] \<Rightarrow> \<alpha>"
by (metis append.left_neutral append.right_neutral step1.intros)

lemma Derivation1_from_empty:
  "\<G> \<turnstile> [] \<Rightarrow> w \<Longrightarrow> w = []"
using step1.cases by auto

lemma Derivation_from_empty:
  "\<G> \<turnstile> [] \<Rightarrow>* (w::('n,'t)symbs) \<Longrightarrow> w = []"
by (induction "[]::('n,'t)symbs" w rule: rtranclp.induct) (auto simp: Derivation1_from_empty)

lemma Derivation_concat_split: "P \<turnstile> u1 @ u2 \<Rightarrow>(n) v \<Longrightarrow>
  \<exists>v1 v2 n1 n2. v = v1 @ v2 \<and> P \<turnstile> u1 \<Rightarrow>(n1) v1 \<and> P \<turnstile> u2 \<Rightarrow>(n2) v2 \<and> n1 \<le> n \<and> n2 \<le> n"
proof (induction n arbitrary: u1 u2 v rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis using less.prems by auto
  next
    case (Suc m)
    then obtain v12 where 1: "P \<turnstile> u1 @ u2 \<Rightarrow>(m) v12" and 2: "P \<turnstile> v12 \<Rightarrow> v"
      using less.prems by(auto simp add: OO_def)
    obtain v1 v2 m1 m2 where IH: "v12 = v1 @ v2" "P \<turnstile> u1 \<Rightarrow>(m1) v1" "P \<turnstile> u2 \<Rightarrow>(m2) v2" "m1 \<le> m" "m2 \<le> m"
      using less.IH[of m, OF _ 1] Suc by blast
    with 2 obtain A \<alpha> v1' v2' where #: "(A,\<alpha>) \<in> P" "v1 @ v2 = v1' @ [N A] @ v2'" "v = v1' @ \<alpha> @ v2'"
      by (meson step1.cases)
    show ?thesis
    proof (cases "length (v1' @ [N A]) \<le> length v1")
      case True
      let ?v2 = "take (length v1 - length (v1' @ [N A])) v2'"
      have "v1 = v1' @ [N A] @ ?v2" using True #(2)
        by (smt (verit, best) append.assoc append_eq_conv_conj take_all take_append)
      then have "P \<turnstile> u1 \<Rightarrow>(Suc m1) v1' @ \<alpha> @ ?v2"
        using IH(2) step1.intros[OF #(1), of v1' ?v2] Suc \<open>m1 \<le> m\<close> by (metis relpowp_Suc_I)
      then show ?thesis using  #(2,3) IH(3-5) \<open>v1 = _\<close> Suc
        by (smt (verit, best) append_assoc nat_le_linear not_less_eq_eq same_append_eq)
    next
      case False
      let ?v1 = "drop (length v1) v1'"
      have "v2 = ?v1 @ [N A] @ v2'" using False #(2)
        by (simp add: append_eq_append_conv_if)
      then have "P \<turnstile> u2 \<Rightarrow>(Suc m2) ?v1 @ \<alpha> @ v2'"
        by (metis "#"(1) IH(3) relpowp_Suc_I step1.intros)
      then show ?thesis using  #(2,3) IH(2,4,5) Suc \<open>v2 = _\<close>
        by (metis append.assoc append_same_eq nat_le_linear not_less_eq_eq)
    qed
  qed
qed

lemma Derivation_start1:
  assumes "P \<turnstile> [N A] \<Rightarrow>(n) map T w"
  shows "\<exists>\<alpha> m. n = Suc m \<and> P \<turnstile> \<alpha> \<Rightarrow>(m) (map T w) \<and> (A,\<alpha>) \<in> P"
proof (cases n)
  case 0
  thus ?thesis
    using assms by (auto)
next
  case (Suc m)
  then obtain \<alpha> where *: "P \<turnstile> [N A] \<Rightarrow> \<alpha>" "P \<turnstile> \<alpha> \<Rightarrow>(m) map T w"
    using assms by (meson relpowp_Suc_E2)
  from  step1.cases[OF *(1)] have "(A, \<alpha>) \<in> P"
    by (simp add: Cons_eq_append_conv) blast
  thus ?thesis using *(2) Suc by auto
qed

end