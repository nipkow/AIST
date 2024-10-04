theory CFG
imports Main
begin

subsection "CFG and Derivations"

datatype ('n,'t) symb = T 't | N 'n

type_synonym ('n,'t) symbs = "('n,'t) symb list"

type_synonym ('n,'t) prod = "'n \<times> ('n,'t) symbs"

type_synonym ('n,'t) prods = "('n,'t) prod set"

datatype ('n,'t) cfg =  CFG (prods : "('n,'t) prods") (start : "'n")

inductive derive :: "('n,'t) prods \<Rightarrow> ('n,'t) symbs \<Rightarrow> ('n,'t)symbs \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_ \<Rightarrow>/ _))" [50, 0, 50] 50) where
"(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> u @ [N A] @ v \<Rightarrow> u @ \<alpha> @ v"

abbreviation deriven ("(_ \<turnstile> _ \<Rightarrow>'(_') _)" [50, 0, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>(n) v \<equiv> (derive P ^^ n) u v"

abbreviation derives ("(_ \<turnstile> _ \<Rightarrow>* _)" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>* v \<equiv> ((derive P) ^**) u v"

inductive derivehd :: "('n,'t) prods \<Rightarrow> ('n,'t) symbs \<Rightarrow> ('n,'t)symbs \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_ \<Rightarrow>h/ _))" [50, 0, 50] 50) where
"(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> N A # v \<Rightarrow>h \<alpha> @ v"

abbreviation derivehds ("(_ \<turnstile> _ \<Rightarrow>h* _)" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>h* v \<equiv> ((derivehd P) ^**) u v"

inductive derivel :: "('n,'t) prods \<Rightarrow> ('n,'t) symbs \<Rightarrow> ('n,'t)symbs \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_ \<Rightarrow>l/ _))" [50, 0, 50] 50) where
"(A,\<alpha>) \<in> P \<Longrightarrow> P \<turnstile> map T u @ N A # v \<Rightarrow>l map T u @ \<alpha> @ v"

abbreviation derivels ("(_ \<turnstile> _ \<Rightarrow>l* _)" [50, 0, 50] 50) where
"P \<turnstile> u \<Rightarrow>l* v \<equiv> ((derivel P) ^**) u v"

lemma derive_iff: "R \<turnstile> u \<Rightarrow> v \<longleftrightarrow> (\<exists> (A,w) \<in> R. \<exists>u1 u2. u = u1 @ N A # u2 \<and> v = u1 @ w @ u2)"
  apply (rule iffI)
   apply (induction rule: derive.induct)
   apply (fastforce)
  using derive.intros by fastforce 

lemma derivehd_iff: "R \<turnstile> u \<Rightarrow>h v \<longleftrightarrow> (\<exists> (A,w) \<in> R. \<exists>u2. u = N A # u2 \<and> v = w @ u2)"
  apply (rule iffI)
   apply (induction rule: derivehd.induct)
   apply (fastforce)
  using derivehd.intros by fastforce

lemma Un_derive: "R \<union> S \<turnstile> y \<Rightarrow> z \<longleftrightarrow> R \<turnstile> y \<Rightarrow> z \<or> S \<turnstile> y \<Rightarrow> z"
  by (fastforce simp: derive_iff)

definition "Lang P A = {w. P \<turnstile> [N A] \<Rightarrow>* map T w}"

lemma derive_append:
  "\<G> \<turnstile> u \<Rightarrow> v \<Longrightarrow> \<G> \<turnstile> u@w \<Rightarrow> v@w"
apply(erule derive.cases)
using derive.intros by fastforce

lemma derive_prepend:
  "\<G> \<turnstile> u \<Rightarrow> v \<Longrightarrow> \<G> \<turnstile> w@u \<Rightarrow> w@v"
apply(erule derive.cases)
by (metis append.assoc derive.intros)

lemma derive_append_decomp:
  "P \<turnstile> u@v \<Rightarrow> w \<longleftrightarrow>
  (\<exists>u'. w = u'@v \<and> P \<turnstile> u \<Rightarrow> u') \<or> (\<exists>v'. w = u@v' \<and> P \<turnstile> v \<Rightarrow> v')"
(is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain A r u1 u2
    where Ar: "(A,r) \<in> P"
      and uv: "u@v = u1 @ N A # u2"
      and w: "w = u1 @ r @ u2"
    by (auto simp: derive_iff)
  from uv have "(\<exists>s. u2 = s @ v \<and> u = u1 @ N A # s) \<or>
  (\<exists>s. u1 = u@s \<and> v = s @ N A # u2)"
    by (auto simp: append_eq_append_conv2 append_eq_Cons_conv)
  with Ar w show "?r" by (fastforce simp: derive_iff)
next
  show "?r \<Longrightarrow> ?l"
    by (auto simp add: derive_append derive_prepend)
qed

lemma derive_Cons:
"P \<turnstile> u \<Rightarrow> v \<Longrightarrow> P \<turnstile> a#u \<Rightarrow> a#v"
  using derive_prepend[of P u v "[a]"] by auto

lemma derives_append:
  "\<G> \<turnstile> u \<Rightarrow>* v \<Longrightarrow> \<G> \<turnstile> u@w \<Rightarrow>* v@w"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl)
  then show ?case
    by (meson rtranclp.rtrancl_into_rtrancl derive_append)
qed

lemma derives_prepend:
  "\<G> \<turnstile> u \<Rightarrow>* v \<Longrightarrow> \<G> \<turnstile> w@u \<Rightarrow>* w@v"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl)
  then show ?case
    by (meson rtranclp.rtrancl_into_rtrancl derive_prepend)
qed

lemma derives_Cons:
"R \<turnstile> u \<Rightarrow>* v \<Longrightarrow> R \<turnstile> a#u \<Rightarrow>* a#v"
  using derives_prepend[of _ _ _ "[a]"] by simp

lemma deriv1_if_valid_prod:
  "(A, \<alpha>) \<in> P \<Longrightarrow> P \<turnstile> [N A] \<Rightarrow> \<alpha>"
by (metis append.left_neutral append.right_neutral derive.intros)

lemma Derivation1_from_empty:
  "\<G> \<turnstile> [] \<Rightarrow> w \<Longrightarrow> w = []"
using derive.cases by auto

lemma derivel_from_empty:
  "\<G> \<turnstile> [] \<Rightarrow>l w \<Longrightarrow> w = []"
using derivel.cases by auto

lemma Derivation_from_empty:
  "\<G> \<turnstile> [] \<Rightarrow>* (w::('n,'t)symbs) \<Longrightarrow> w = []"
by (induction "[]::('n,'t)symbs" w rule: rtranclp.induct) (auto simp: Derivation1_from_empty)

lemma derivels_from_empty:
  "\<G> \<turnstile> [] \<Rightarrow>l* (w::('n,'t)symbs) \<Longrightarrow> w = []"
by (induction "[]::('n,'t)symbs" w rule: rtranclp.induct) (auto simp: derivel_from_empty)

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
      by (meson derive.cases)
    show ?thesis
    proof (cases "length (v1' @ [N A]) \<le> length v1")
      case True
      let ?v2 = "take (length v1 - length (v1' @ [N A])) v2'"
      have "v1 = v1' @ [N A] @ ?v2" using True #(2)
        by (smt (verit, best) append.assoc append_eq_conv_conj take_all take_append)
      then have "P \<turnstile> u1 \<Rightarrow>(Suc m1) v1' @ \<alpha> @ ?v2"
        using IH(2) derive.intros[OF #(1), of v1' ?v2] Suc \<open>m1 \<le> m\<close> by (metis relpowp_Suc_I)
      then show ?thesis using  #(2,3) IH(3-5) \<open>v1 = _\<close> Suc
        by (smt (verit, best) append_assoc nat_le_linear not_less_eq_eq same_append_eq)
    next
      case False
      let ?v1 = "drop (length v1) v1'"
      have "v2 = ?v1 @ [N A] @ v2'" using False #(2)
        by (simp add: append_eq_append_conv_if)
      then have "P \<turnstile> u2 \<Rightarrow>(Suc m2) ?v1 @ \<alpha> @ v2'"
        by (metis "#"(1) IH(3) relpowp_Suc_I derive.intros)
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
  from  derive.cases[OF *(1)] have "(A, \<alpha>) \<in> P"
    by (simp add: Cons_eq_append_conv) blast
  thus ?thesis using *(2) Suc by auto
qed

lemma T_Cons_derive:
  "P \<turnstile> T a # u \<Rightarrow> v \<longleftrightarrow> (\<exists>w. v = T a # w \<and> P \<turnstile> u \<Rightarrow> w)"
  by (fastforce simp: derive_iff Cons_eq_append_conv)

lemma T_Cons_derives:
  "P \<turnstile> T a # u \<Rightarrow>* v \<longleftrightarrow> (\<exists>w. v = T a # w \<and> P \<turnstile> u \<Rightarrow>* w)"
  (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    apply (induction "T a # u" arbitrary: u rule: converse_rtranclp_induct)
    by (auto simp: T_Cons_derive)
next
  assume ?r
  then obtain w where v: "v = T a # w" and uw: "P \<turnstile> u \<Rightarrow>* w"
    by auto
  from uw show ?l
    apply (unfold v)
  proof (induction arbitrary: rule: rtranclp_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    from derive_Cons[OF \<open>P \<turnstile> y \<Rightarrow> z\<close>, of "T a"]
      step.IH
    show ?case by auto
  qed
qed

lemma T_Cons_derivel:
  "P \<turnstile> T a # u \<Rightarrow>l v \<longleftrightarrow> (\<exists>w. v = T a # w \<and> P \<turnstile> u \<Rightarrow>l w)"
  apply (cases v)
  apply (auto simp: derivel.simps Cons_eq_append_conv)
  apply (metis list.simps(9))
  done

lemma derivel_map_T_append:
  "P \<turnstile> map T w @ u \<Rightarrow>l v \<longleftrightarrow> (\<exists>x. v = map T w @ x \<and> P \<turnstile> u \<Rightarrow>l x)"
  apply (induct w arbitrary:v)
  by (auto simp: T_Cons_derivel Cons_eq_append_conv)

lemma T_Cons_derivels:
  "P \<turnstile> T a # u \<Rightarrow>l* v \<longleftrightarrow> (\<exists>w. v = T a # w \<and> P \<turnstile> u \<Rightarrow>l* w)"
  (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    apply (induction "T a # u" arbitrary: u rule: converse_rtranclp_induct)
    by (auto simp: T_Cons_derivel)
next
  assume ?r
  then obtain w where v: "v = T a # w" and uw: "P \<turnstile> u \<Rightarrow>l* w"
    by auto
  from uw show ?l
    apply (unfold v)
  proof (induction arbitrary: rule: rtranclp_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    then have "P \<turnstile> T a # y \<Rightarrow>l T a # z" by (auto simp:T_Cons_derivel)
    with step.IH
    show ?case by auto
  qed
qed

lemma derive_singleton: "P \<turnstile> [a] \<Rightarrow> u \<longleftrightarrow> (\<exists>A. (A,u) \<in> P \<and> a = N A)"
  by (auto simp: derive_iff Cons_eq_append_conv)

lemma deriven_singleton: "P \<turnstile> [a] \<Rightarrow>(n) u \<longleftrightarrow> (
  case n of 0 \<Rightarrow> u = [a]
   | Suc m \<Rightarrow> \<exists>(A,w) \<in> P. a = N A \<and> P \<turnstile> w \<Rightarrow>(m) u)"
  (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case apply auto
      by (smt (verit, best) Suc.prems case_prodI derive_singleton relpowp_Suc_E2)
  qed
  show "?r \<Longrightarrow> ?l"
    apply (auto simp:  split: nat.splits)
    by (metis derive_singleton relpowp.simps(2) relpowp_Suc_I2)
qed

lemma relpowp_Suc_right: "(R ^^ Suc n) = R OO (R ^^ n)"
  by (simp add: relpowp_commute)

lemma deriven_append:
  "P \<turnstile> u \<Rightarrow>(n) v \<Longrightarrow> P \<turnstile> u @ w \<Rightarrow>(n) v @ w"
  apply (induction n arbitrary: v)
   apply simp
  using derive_append by fastforce

lemma deriven_prepend:
  "P \<turnstile> u \<Rightarrow>(n) v \<Longrightarrow> P \<turnstile> w @ u \<Rightarrow>(n) w @ v"
  apply (induction n arbitrary: v)
   apply simp
  using derive_prepend by fastforce

lemma deriven_append_decomp:
  "P \<turnstile> u @ v \<Rightarrow>(n) w \<longleftrightarrow>
  (\<exists>n1 n2 w1 w2. n = n1 + n2 \<and> w = w1 @ w2 \<and> P \<turnstile> u \<Rightarrow>(n1) w1 \<and> P \<turnstile> v \<Rightarrow>(n2) w2)"
  (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    apply (induction n arbitrary: u v)
     apply auto[1]
    apply (auto simp del: relpowp.simps simp: relpowp_Suc_right
        derive_append_decomp)
     apply (metis add_Suc relpowp_Suc_I2)
    by (metis add_Suc_right relpowp_Suc_I2)
next
  assume ?r
  then obtain n1 n2 w1 w2
    where [simp]: "n = n1 + n2" "w = w1 @ w2"
      and u: "P \<turnstile> u \<Rightarrow>(n1) w1" and v: "P \<turnstile> v \<Rightarrow>(n2) w2"
    by auto
  from u deriven_append
  have "P \<turnstile> u @ v \<Rightarrow>(n1) w1 @ v" by fastforce
  also from v deriven_prepend
  have "P \<turnstile> w1 @ v \<Rightarrow>(n2) w1 @ w2" by fastforce
  finally show ?l by auto
qed

lemma deriven_Cons_decomp:
  "P \<turnstile> a # u \<Rightarrow>(n) v \<longleftrightarrow>
  (\<exists>v2. v = a#v2 \<and> P \<turnstile> u \<Rightarrow>(n) v2) \<or>
  (\<exists>n1 n2 A w v1 v2. n = Suc (n1 + n2) \<and> v = v1 @ v2 \<and> a = N A \<and>
   (A,w) \<in> P \<and> P \<turnstile> w \<Rightarrow>(n1) v1 \<and> P \<turnstile> u \<Rightarrow>(n2) v2)"
(is "?l = ?r")
proof
  assume ?l
  then obtain n1 n2 v1 v2
    where [simp]: "n = n1 + n2" "v = v1 @ v2"
      and 1: "P \<turnstile> [a] \<Rightarrow>(n1) v1" and 2: "P \<turnstile> u \<Rightarrow>(n2) v2"
    unfolding deriven_append_decomp[of n P "[a]" u v,simplified]
    by auto
  show ?r
  proof (cases "n1")
    case 0
    with 1 2 show ?thesis by auto
  next
    case [simp]: (Suc m)
    with 1 obtain A w
      where [simp]: "a = N A" "(A,w) \<in> P" and w: "P \<turnstile> w \<Rightarrow>(m) v1"
      by (auto simp: deriven_singleton simp del: relpowp.simps)
    with 2
    have "n = Suc (m + n2) \<and> v = v1 @ v2 \<and> a = N A \<and>
   (A,w) \<in> P \<and> P \<turnstile> w \<Rightarrow>(m) v1 \<and> P \<turnstile> u \<Rightarrow>(n2) v2"
      by auto
    then show ?thesis
      by (auto simp: append_eq_Cons_conv)
  qed
next
  assume "?r"
  then
  show "?l"
  proof (elim disjE exE conjE)
    fix v2
    assume [simp]: "v = a # v2" and u: "P \<turnstile> u \<Rightarrow>(n) v2"
    from deriven_prepend[OF u, of "[a]"]
    show ?thesis
      by (auto simp del: relpowp.simps(2))
  next
    fix n1 n2 A w v1 v2
    assume [simp]: "n = Suc (n1 + n2)" "v = v1 @ v2" "a = N A"
      and Aw: "(A, w) \<in> P"
      and w: "P \<turnstile> w \<Rightarrow>(n1) v1"
      and u: "P \<turnstile> u \<Rightarrow>(n2) v2"
    have "P \<turnstile> [a] \<Rightarrow> w"
      by (simp add: Aw deriv1_if_valid_prod)
    with w have "P \<turnstile> [a] \<Rightarrow>(Suc n1) v1"
      by (metis relpowp_Suc_I2)
    from deriven_append[OF this]
    have 1: "P \<turnstile> a#u \<Rightarrow>(Suc n1) v1@u"
      by auto
    also have "P \<turnstile> \<dots> \<Rightarrow>(n2) v1@v2"
      using deriven_prepend[OF u].
    finally
    show ?thesis by simp
  qed
qed

lemma deriven_derivels: "P \<turnstile> u \<Rightarrow>* map T v \<longleftrightarrow> P \<turnstile> u \<Rightarrow>l* map T v"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain n where "P \<turnstile> u \<Rightarrow>(n) map T v"
    by (meson rtranclp_imp_relpowp)
  then show "?r"
  proof (induction n arbitrary: u v rule: less_induct)
    case (less n)
    then show ?case
      apply (induction u)
      apply (auto simp: deriven_Cons_decomp T_Cons_derivels)
        apply (metis Derivation_from_empty rtranclp.simps rtranclp_power)

      sorry
  qed
next
  show "?r \<Longrightarrow> ?l" sorry
qed

end