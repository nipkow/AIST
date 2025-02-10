theory CNF
  imports uProds
begin

definition isTm :: "('n, 't) sym \<Rightarrow> bool" where 
  "isTm S = (\<exists>a. S = Tm a)"

definition isNt :: "('n, 't) sym \<Rightarrow> bool" where 
  "isNt S = (\<exists>A. S = Nt A)"

definition Unit_free :: "('n, 't) Prods \<Rightarrow> bool" where
  "Unit_free Ps = (\<nexists>l A. (l,[Nt A]) \<in> Ps)"

lemma negrImpEps_free: "\<N> ps ps' \<Longrightarrow> Eps_free (set ps')"
  unfolding \<N>_def eps_elim_def Eps_free_def by blast

lemma upgrImpUnit_free: "\<U> ps ps' \<Longrightarrow> Unit_free (set ps')" 
  unfolding \<U>_def \<U>_rules_def unit_elim_def new_prods_def unit_prods_def Unit_free_def by simp

lemma upgr_Eps_free:
  assumes "Eps_free (set ps)" "\<U> ps ps'"
  shows "Eps_free (set ps')"
  using assms 
  unfolding \<U>_def Eps_free_def \<U>_rules_def unit_elim_def unit_prods_def new_prods_def by auto

lemma Nts_correct: "A \<notin> Nts Ps \<Longrightarrow> (\<nexists>S \<alpha>. (S, \<alpha>) \<in> Ps \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>))"
unfolding Nts_def nts_of_syms_def by auto

(* Chomsky Normal Form *)

axiomatization fresh :: "('n::infinite,'t) cfg \<Rightarrow> 'n" where
fresh: "fresh g \<notin> Nts(set (prods g)) \<union> {start g}"

abbreviation L :: "('n,'t) cfg \<Rightarrow> 't list set" where
  "L g \<equiv> Lang (set (prods g)) (start g)"

definition uniformize :: "'n::infinite \<Rightarrow> 't \<Rightarrow> ('n, 't) cfg \<Rightarrow> ('n, 't) cfg \<Rightarrow> bool" where 
      "uniformize A t g g' \<equiv> (
    \<exists> l r p s. (l,r) \<in> set (prods g) \<and> (r = p@[Tm t]@s) 
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A = fresh g)
    \<and> prods g' = ((removeAll (l,r) (prods g)) @ [(A,[Tm t]), (l, p@[Nt A]@s)]) 
    \<and> start g' = start g)"

lemma uniformize_Eps_free:
  assumes "Eps_free (set (prods g))"
    and "uniformize A t g g'"
  shows "Eps_free (set (prods g'))"
  using assms unfolding uniformize_def Eps_free_def by force

lemma uniformize_Unit_free:
  assumes "Unit_free (set (prods g))"
    and "uniformize A t g g'"
  shows "Unit_free (set (prods g'))"
proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set (prods g)))"
    using assms(1) unfolding Unit_free_def by simp
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(2) set_removeAll unfolding uniformize_def by force
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A,[Tm t]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set (prods g) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using \<open>?lrps\<close> by simp
  ultimately show ?thesis unfolding Unit_free_def by simp
qed

definition prodTms :: "('n,'t) prod \<Rightarrow> nat" where
  "prodTms p \<equiv> (if length (snd p) \<le> 1 then 0 else length (filter (isTm) (snd p)))"

definition prodNts :: "('n,'t) prod \<Rightarrow> nat" where
  "prodNts p \<equiv> (if length (snd p) \<le> 2 then 0 else length (filter (isNt) (snd p)))"

fun badTmsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badTmsCount [] = 0" |
  "badTmsCount (p#ps) = (prodTms p) + badTmsCount ps"

lemma badTmsCountSet: "(\<forall>p \<in> set ps. prodTms p = 0) \<longleftrightarrow> badTmsCount ps = 0"
  by (induction ps) auto

fun badNtsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badNtsCount [] = 0" |
  "badNtsCount (p#ps) = (prodNts p) + badNtsCount ps"

lemma badNtsCountSet: "(\<forall>p \<in> set ps. prodNts p = 0) \<longleftrightarrow> badNtsCount ps = 0"
  by (induction ps) auto

definition uniform :: "('n, 't) Prods \<Rightarrow> bool" where
  "uniform Ps \<equiv> \<forall>(A, \<alpha>) \<in> Ps. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"

lemma uniform_badTmsCount: 
  "uniform (set ps) \<longleftrightarrow> badTmsCount ps = 0"
proof 
  assume "uniform (set ps)" (is "?assm")
  have "\<forall>p \<in> set ps. prodTms p = 0"
  proof 
    fix p assume "p \<in> set ps"
    hence "(\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t])"
      using \<open>?assm\<close> unfolding uniform_def by auto
    hence "length (snd p) \<le> 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      by auto
    hence "length (snd p) \<le> 1 \<or> length (filter (isTm) (snd p)) = 0"
      unfolding isTm_def by (auto simp: filter_empty_conv)
    thus "prodTms p = 0"
      unfolding prodTms_def by argo
   qed
   thus "badTmsCount ps = 0"
     using badTmsCountSet by blast
next 
  assume "badTmsCount ps = 0" (is "?assm")
  have "\<forall>p \<in> set ps. ((\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t]))"
  proof 
    fix p assume "p \<in> set ps"
    hence "prodTms p = 0"
      using \<open>?assm\<close> badTmsCountSet by blast
    hence "length (snd p) \<le> 1 \<or> length (filter (isTm) (snd p)) = 0"
      unfolding prodTms_def by argo
    hence "length (snd p) \<le> 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      by (auto simp: isTm_def filter_empty_conv)
    hence "length (snd p) = 0 \<or> length (snd p) = 1 \<or> (\<nexists>t. Tm t \<in> set (snd p))"
      using order_neq_le_trans by blast
    thus "(\<nexists>t. Tm t \<in> set (snd p)) \<or> (\<exists>t. snd p = [Tm t])"
      by (auto simp: length_Suc_conv)
  qed
  thus "uniform (set ps)"
    unfolding uniform_def by auto
qed

definition binary :: "('n, 't) Prods \<Rightarrow> bool" where
  "binary Ps \<equiv> \<forall>(A, \<alpha>) \<in> Ps. length \<alpha> \<le> 2"

lemma binary_badNtsCount:
  assumes "uniform (set ps)" "badNtsCount ps = 0"
  shows "binary (set ps)"
proof -
  have "\<forall>p \<in> set ps. length (snd p) \<le> 2"
  proof 
    fix p assume "p \<in> set ps" (is "?assm")
    obtain A \<alpha> where "(A, \<alpha>) = p"
      using prod.collapse by blast
    hence "((\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])) \<and> (prodNts (A, \<alpha>) = 0)"
      using assms badNtsCountSet \<open>?assm\<close> unfolding uniform_def by auto
    hence "((\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])) \<and> (length \<alpha> \<le> 2 \<or> length (filter (isNt) \<alpha>) = 0)"
      unfolding prodNts_def by force
    hence "((\<nexists>t. Tm t \<in> set \<alpha>) \<or> (length \<alpha> \<le> 1)) \<and> (length \<alpha> \<le> 2 \<or> (\<nexists>N. Nt N \<in> set \<alpha>))"
      by (auto simp: filter_empty_conv[of isNt \<alpha>] isNt_def)
    hence "length \<alpha> \<le> 2"
      by (metis Suc_1 Suc_le_eq in_set_conv_nth le_Suc_eq nat_le_linear sym.exhaust)
    thus "length (snd p) \<le> 2"
      using \<open>(A, \<alpha>) = p\<close> by auto
  qed
  thus ?thesis
    by (auto simp: binary_def)
qed

lemma count_bin_un: "(binary (set ps) \<and> uniform (set ps)) \<longleftrightarrow> (badTmsCount ps = 0 \<and> badNtsCount ps = 0)"
proof 
  assume "binary (set ps) \<and> uniform (set ps)" (is "?assm")
  hence "badTmsCount ps = 0 \<and> (\<forall>(A, \<alpha>) \<in> set ps. length \<alpha> \<le> 2)"
    unfolding binary_def using uniform_badTmsCount by blast
  thus "badTmsCount ps = 0 \<and> badNtsCount ps = 0"
    by (metis badNtsCountSet case_prodE prod.sel(2) prodNts_def)
next
  assume "badTmsCount ps = 0 \<and> badNtsCount ps = 0" (is "?assm")
  show "binary (set ps) \<and> uniform (set ps)"
    using \<open>?assm\<close> binary_badNtsCount uniform_badTmsCount by blast 
qed


definition binarizeNt :: "'n::infinite \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n,'t) cfg \<Rightarrow> ('n,'t) cfg \<Rightarrow> bool" where
      "binarizeNt A B\<^sub>1 B\<^sub>2 g g' \<equiv> (
    \<exists>l r p s. (l,r) \<in> set (prods g) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A = fresh g)
    \<and> prods g' = ((removeAll (l,r) (prods g)) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)])
    \<and> start g' = start g)"

lemma binarizeNt_Eps_free:
  assumes "Eps_free (set (prods g))"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "Eps_free (set (prods g'))"
  using assms unfolding binarizeNt_def Eps_free_def by force

lemma binarizeNt_Unit_free:
  assumes "Unit_free (set (prods g))"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "Unit_free (set (prods g'))"
  proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set (prods g)))"
    using assms(1) unfolding Unit_free_def by simp
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> (set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(2) set_removeAll unfolding binarizeNt_def by force
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set (prods g) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using \<open>?lrps\<close> by simp
  ultimately show ?thesis unfolding Unit_free_def by simp
qed

lemma binarizeNt_aux1:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "A \<noteq> B\<^sub>1 \<and> A \<noteq> B\<^sub>2"
  using assms fresh unfolding binarizeNt_def Nts_def nts_of_syms_def by fastforce

lemma derives_sub:
  assumes "Ps \<turnstile> [Nt A] \<Rightarrow> u" and "Ps \<turnstile> xs \<Rightarrow> p @ [Nt A] @ s"
  shows "Ps \<turnstile> xs \<Rightarrow>* p @ u @ s"
proof -
  have "Ps \<turnstile> p @ [Nt A] @ s \<Rightarrow>* p @ u @ s"
    using assms derive_append derive_prepend by blast
  thus ?thesis
    using assms(2) by simp
qed

lemma cnf_r1Tm: 
  assumes "uniformize A t g g'"
    and "set (prods g) \<turnstile> lhs \<Rightarrow> rhs"
  shows "set (prods g') \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' B v where "lhs = p'@[Nt B]@s' \<and> rhs = p'@v@s' \<and> (B,v) \<in> set (prods g)" (is "?Bv")
    using derive.cases[OF assms(2)] by fastforce
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g)))
      \<and> set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding uniformize_def by fastforce
  thus ?thesis
  proof (cases "(B, v) \<in> set (prods g')")
    case True
    then show ?thesis
      using derive.intros[of B v] \<open>?Bv\<close> by blast
  next
    case False
    hence "B = l \<and> v = p@[Tm t]@s"
      by (simp add: \<open>?lrps\<close> \<open>?Bv\<close>) 
    have 1: "(set (prods g')) \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
      using \<open>?lrps\<close> by (simp add: derive_singleton)
    have "(set (prods g')) \<turnstile> [Nt A] \<Rightarrow> [Tm t]"
      using \<open>?lrps\<close> by (simp add: derive_singleton)
    hence "(set (prods g')) \<turnstile> [Nt l] \<Rightarrow>* p@[Tm t]@s"
      using 1 derives_sub[of \<open>set (prods g')\<close>] by blast
    then show ?thesis 
      using False \<open>B = l \<and> v = p@[Tm t]@s\<close> \<open>?Bv\<close> derives_append derives_prepend by blast
  qed
qed

lemma cnf_r1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
    and "(set (prods g)) \<turnstile> lhs \<Rightarrow> rhs"
  shows "(set (prods g')) \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' C v where "lhs = p'@[Nt C]@s' \<and> rhs = p'@v@s' \<and> (C,v) \<in> set (prods g)" (is "?Cv")
    using derive.cases[OF assms(2)] by fastforce
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g)))
    \<and> (set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding binarizeNt_def by fastforce
  thus ?thesis
  proof (cases "(C, v) \<in> set (prods g')")
    case True
    then show ?thesis
      using derive.intros[of C v] \<open>?Cv\<close> by blast
  next
    case False
    hence "C = l \<and> v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s"
      by (simp add: \<open>?lrps\<close> \<open>?Cv\<close>)
    have 1: "set (prods g') \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
      using \<open>?lrps\<close> by (simp add: derive_singleton)
    have "set (prods g') \<turnstile> [Nt A] \<Rightarrow> [Nt B\<^sub>1,Nt B\<^sub>2]"
      using \<open>?lrps\<close> by (simp add: derive_singleton)
    hence "set (prods g') \<turnstile> [Nt l] \<Rightarrow>* p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" 
      using 1 derives_sub[of \<open>set (prods g')\<close>] by blast
    thus ?thesis 
      using False \<open>C = l \<and> v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s\<close> \<open>?Cv\<close> derives_append derives_prepend by blast
  qed
qed

(* p = (A, [Tm t]): Replace the fresh Nt A in rhs by \<alpha> *)
fun elim :: "('n, 't) prod \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms"  where
  "elim _ [] = []" |
  "elim (A,\<alpha>) (r#rhs) = (if r = Nt A then \<alpha>@(elim (A,\<alpha>) rhs) else r#(elim (A,\<alpha>) rhs))"

lemma slemma1_1: 
  assumes "uniformize A t g g'"
    and "(A, \<alpha>) \<in> set (prods g')"
  shows "\<alpha> = [Tm t]"
proof -
  have "A \<notin> Nts (set (prods g))"
    using assms(1) fresh unfolding uniformize_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set (prods g)"
    unfolding Nts_def by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Tm t] \<and> (A, \<alpha>) \<in> set (prods g')"
    using assms(1) unfolding uniformize_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma1_1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
    and "(A, \<alpha>) \<in> set (prods g')"
  shows "\<alpha> = [Nt B\<^sub>1,Nt B\<^sub>2]"
proof -
  have "A \<notin> Nts (set (prods g))"
    using assms(1) fresh unfolding binarizeNt_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set (prods g)"
    unfolding Nts_def  by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Nt B\<^sub>1,Nt B\<^sub>2] \<and> (A, \<alpha>) \<in> set (prods g')"
    using assms(1) unfolding binarizeNt_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_0: "elim (A, \<alpha>) (u@v)  = elim (A, \<alpha>) u @ elim (A, \<alpha>) v"
  by (induction u) simp_all

lemma slemma4_2_0: "(lhs = A) \<longleftrightarrow> (Nt lhs = Nt A)" 
  by simp

lemma slemma4_2_1: 
  assumes "h \<noteq> (Nt A)"
  shows "[h] = elim (A, \<alpha>) [h]"
  using assms by simp

lemma slemma4_1:
  assumes "(Nt A) \<notin> set rhs"
  shows "\<forall>\<alpha>. rhs = elim (A, \<alpha>) rhs"
  using assms by (induction rhs arbitrary: A) auto

lemma slemma4_3_1:
  assumes "lhs = A"
  shows "(\<alpha> = elim (A, \<alpha>) [Nt lhs])"
  using assms by simp

lemma slemma4_4:
  assumes "uniformize A t g g'"
    and "(l,r) \<in> set (prods g)"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> Nts (set (prods g))"
    using assms(1) fresh unfolding uniformize_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set (prods g) \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>set (prods g)\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
    and "(l,r) \<in> set (prods g)"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> Nts (set (prods g))"
    using assms(1) fresh unfolding binarizeNt_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set (prods g) \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>set (prods g)\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed


lemma lemma1:
  assumes "uniformize A t g g'"
    and "set (prods g') \<turnstile> lhs \<Rightarrow> rhs"
  shows "(elim (A, [Tm t]) lhs = elim (A, [Tm t]) rhs) \<or> (set (prods g) \<turnstile> (elim (A, [Tm t]) lhs) \<Rightarrow> (elim (A, [Tm t]) rhs))"
proof -
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g))) 
      \<and> set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding uniformize_def by fastforce
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set (prods g')" (is "?uv")
    using derive.cases[OF assms(2)] by fastforce
  thus ?thesis
  proof (cases "u = A")
    case True
    then show ?thesis 
    proof (cases "v = [Tm t]")
      case True
      have "elim (A, [Tm t]) lhs = elim (A, [Tm t]) p' @ elim (A, [Tm t]) ([Nt A]@s')"
        using \<open>?uv\<close> \<open>u = A\<close> slemma4_0 by fast
      hence "elim (A, [Tm t]) lhs = elim (A, [Tm t]) p' @ [Tm t] @ elim (A, [Tm t]) s'"
        by simp
      then show ?thesis
        by (simp add: True \<open>?uv\<close> slemma4_0) 
    next
      case False
      then show ?thesis 
        using True \<open>?uv\<close> assms(1) slemma1_1 by fastforce 
    qed
  next
    case False
    then show ?thesis 
    proof (cases "(Nt A) \<in> set v")
      case True
      hence 1: "v = p@[Nt A]@s \<and> Nt A \<notin> set p \<and> Nt A \<notin> set s" 
        using \<open>?lrps\<close> \<open>?uv\<close> assms slemma4_4 by fastforce
      hence "elim (A, [Tm t]) v = elim (A, [Tm t]) p @ elim (A, [Tm t]) ([Nt A]@s)"
        using slemma4_0 by fast
      hence "elim (A, [Tm t]) v = p @ [Tm t] @ s"
        using 1 slemma4_0 slemma4_1 slemma4_3_1 by metis
      hence 2: "(u, elim (A, [Tm t]) v) \<in> set (prods g)" using \<open>?lrps\<close> 
        using True \<open>?uv\<close> assms(1) slemma4_4 by fastforce
      have "elim (A, [Tm t]) lhs = elim (A, [Tm t]) p' @ elim (A, [Tm t]) ([Nt u]@s')"
        using \<open>?uv\<close> slemma4_0 by fast
      hence 3: "elim (A, [Tm t]) lhs = elim (A, [Tm t]) p' @ [Nt u] @ elim (A, [Tm t]) s'" 
        using \<open>u \<noteq> A\<close> by simp
      have "elim (A, [Tm t]) rhs = elim (A, [Tm t]) p' @ elim (A, [Tm t]) (v@s')"
        using \<open>?uv\<close> slemma4_0 by fast
      hence "elim (A, [Tm t]) rhs = elim (A, [Tm t]) p' @ elim (A, [Tm t]) v @ elim (A, [Tm t]) s'"
        using slemma4_0 by fastforce
      then show ?thesis 
        using 2 3 assms(2) \<open>?uv\<close> derive.simps by fast
    next
      case False
      hence 1: "(u, v) \<in> set (prods g)" 
        using assms(1) \<open>?uv\<close> \<open>u \<noteq> A\<close> \<open>?lrps\<close> by (simp add: in_set_conv_decomp)
       have "elim (A, [Tm t]) lhs = elim (A, [Tm t]) p' @ elim (A, [Tm t]) ([Nt u]@s')"
         using \<open>?uv\<close> slemma4_0 by fast
       hence 2: "elim (A, [Tm t]) lhs = elim (A, [Tm t]) p' @ [Nt u] @ elim (A, [Tm t]) s'"
         using \<open>u \<noteq> A\<close> by simp
       have "elim (A, [Tm t]) rhs = elim (A, [Tm t]) p' @ elim (A, [Tm t]) (v@s')"
         using \<open>?uv\<close> slemma4_0 by fast
       hence "elim (A, [Tm t]) rhs = elim (A, [Tm t]) p' @ elim (A, [Tm t]) v @ elim (A, [Tm t]) s'"
         using slemma4_0 by fastforce
       hence "elim (A, [Tm t]) rhs = elim (A, [Tm t]) p' @ v @ elim (A, [Tm t]) s'"
         using False slemma4_1 by fastforce
       thus ?thesis 
         using 1 2 assms(2) \<open>?uv\<close> derive.simps by fast
    qed
  qed
qed

lemma lemma1Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
    and "set (prods g') \<turnstile> lhs \<Rightarrow> rhs"
  shows "(elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs) 
          \<or> ((set (prods g)) \<turnstile> (elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs) \<Rightarrow> elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs)"
proof -
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g)))
    \<and> (set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding binarizeNt_def by fastforce
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set (prods g')" (is "?uv")
    using derive.cases[OF assms(2)] by fastforce
  thus ?thesis
  proof (cases "u = A")
    case True
    then show ?thesis 
    proof (cases "v = [Nt B\<^sub>1,Nt B\<^sub>2]")
      case True
      have "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) ([Nt A]@s')"
        using \<open>?uv\<close> \<open>u = A\<close> slemma4_0 by fast
      hence 1: "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ [Nt B\<^sub>1,Nt B\<^sub>2] @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) s'"
        by simp
      have "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) ([Nt B\<^sub>1,Nt B\<^sub>2]@s')"
        using \<open>?uv\<close> \<open>u = A\<close> slemma4_0 True by fast
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ [Nt B\<^sub>1,Nt B\<^sub>2] @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) s'"
        using assms(1) binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 g g'] by fastforce 
      then show ?thesis
        using 1 by simp
    next
      case False
      then show ?thesis
        using True \<open>?uv\<close> assms(1) slemma1_1Nt by fastforce
    qed
  next
    case False
    then show ?thesis 
    proof (cases "(Nt A) \<in> set v")
      case True
      have "Nt A \<notin> set p \<and> Nt A \<notin> set s" 
        using \<open>?lrps\<close> assms(1) by (metis UnI1 UnI2 set_append slemma4_4Nt)
      hence 1: "v = p@[Nt A]@s \<and> Nt A \<notin> set p \<and> Nt A \<notin> set s" 
        using True \<open>?lrps\<close> \<open>?uv\<close> assms slemma4_4Nt[of A B\<^sub>1 B\<^sub>2 g g'] binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 g g'] by auto
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) ([Nt A]@s)"
        using slemma4_0 by fast
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v = p @ [Nt B\<^sub>1,Nt B\<^sub>2] @ s"
        using 1 slemma4_0 slemma4_1 slemma4_3_1 by metis
      hence 2: "(u, elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v) \<in> set (prods g)" 
        using True \<open>?lrps\<close>  \<open>?uv\<close> assms(1) slemma4_4Nt by fastforce
      have "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) ([Nt u]@s')"
        using \<open>?uv\<close> slemma4_0 by fast
      hence 3: "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ [Nt u] @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) s'" 
        using \<open>u \<noteq> A\<close> by simp
      have "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) (v@s')"
        using \<open>?uv\<close> slemma4_0 by fast
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) s'"
        using slemma4_0 by fastforce
      then show ?thesis 
        using 2 3 assms(2) \<open>?uv\<close> derive.simps by fast
    next
      case False
      hence 1: "(u, v) \<in> set (prods g)" 
        using assms(1) \<open>?uv\<close> \<open>u \<noteq> A\<close> \<open>?lrps\<close> by (simp add: in_set_conv_decomp)
       have "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) ([Nt u]@s')"
         using \<open>?uv\<close> slemma4_0 by fast
       hence 2: "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ [Nt u] @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) s'"
         using \<open>u \<noteq> A\<close> by simp
       have "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) (v@s')"
         using \<open>?uv\<close> slemma4_0 by fast
       hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) s'"
         using slemma4_0 by fastforce
       hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p' @ v @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) s'"
         using False slemma4_1 by fastforce
       thus ?thesis 
         using 1 2 assms(2) \<open>?uv\<close> derive.simps by fast
    qed
  qed
qed

lemma lemma3:
  assumes "set (prods g') \<turnstile> lhs \<Rightarrow>* rhs"
    and "uniformize A t g g'"
  shows "set (prods g) \<turnstile> (elim (A, [Tm t]) lhs) \<Rightarrow>* (elim (A, [Tm t]) rhs)"
  using assms
proof (induction)
  case (step y z)
  then show ?case 
    using lemma1[of A t g g' y z] rtranclp.rtrancl_into_rtrancl by fastforce 
qed simp

lemma lemma3Nt:
  assumes "set (prods g') \<turnstile> lhs \<Rightarrow>* rhs"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "set (prods g) \<turnstile> (elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) lhs) \<Rightarrow>* (elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) rhs)"
  using assms 
proof (induction)
  case (step y z)
  then show ?case 
    using lemma1Nt[of A B\<^sub>1 B\<^sub>2 g g' y z] rtranclp.rtrancl_into_rtrancl by fastforce 
qed simp

lemma slemma4_7: "map Tm w = elim (A, \<alpha>) (map Tm w)"
  by (induction w) auto

lemma lemma4:
  assumes "uniformize A t g g'" 
  shows "L g' \<subseteq> L g"
proof 
  fix w
  assume "w \<in> L g'"
  hence "set (prods g') \<turnstile> [Nt (start g')] \<Rightarrow>* map Tm w"
    unfolding Lang_def by simp
  hence "set (prods g') \<turnstile> [Nt (start g)] \<Rightarrow>* map Tm w"
    using assms unfolding uniformize_def by auto
  hence "set (prods g) \<turnstile> elim (A, [Tm t]) [Nt (start g)] \<Rightarrow>*  elim (A, [Tm t]) (map Tm w)"
    using assms lemma3[of g' \<open>[Nt (start g)]\<close> \<open>map Tm w\<close> A t g] by blast
  moreover have "elim (A, [Tm t]) [Nt (start g)] = [Nt (start g)]"
    using assms fresh unfolding uniformize_def 
    by (metis Un_iff singletonI slemma4_2_0 slemma4_2_1) (*TODO*)
  moreover have "elim (A, [Tm t]) (map Tm w) = map Tm w" 
    using \<open>w \<in> L g'\<close> slemma4_7 by metis
  ultimately show "w \<in> L g" 
    using  \<open>w \<in> L g'\<close> by (simp add: Lang_def)
qed

lemma lemma4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "L g' \<subseteq> L g"
proof
  fix w
  assume "w \<in> L g'"
  hence "set (prods g') \<turnstile> [Nt (start g')] \<Rightarrow>* map Tm w"
    by (simp add: Lang_def)
  hence "set (prods g') \<turnstile> [Nt (start g)] \<Rightarrow>* map Tm w"
    using assms unfolding binarizeNt_def by auto
  hence "set (prods g) \<turnstile> elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) [Nt (start g)] \<Rightarrow>*  elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) (map Tm w)"
    using assms lemma3Nt[of g' \<open>[Nt (start g)]\<close> \<open>map Tm w\<close> A B\<^sub>1 B\<^sub>2 g] by blast
  moreover have "elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) [Nt (start g)] = [Nt (start g)]"
    using assms fresh unfolding binarizeNt_def 
    by (metis UnCI singletonI slemma4_2_0 slemma4_2_1) (*TODO*)
  moreover have "elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) (map Tm w) = map Tm w" 
    using \<open>w \<in> L g'\<close> slemma4_7 by metis
  ultimately show "w \<in> L g" using Lang_def \<open>w \<in> L g'\<close> 
    by (metis (no_types, lifting) mem_Collect_eq)
qed

lemma slemma5_1:
  assumes "set (prods g) \<turnstile> lhs \<Rightarrow>* rhs"
    and "lhs = [Nt S]"
    and "uniformize A t g g'"
  shows "set (prods g') \<turnstile> lhs \<Rightarrow>* rhs"
  using assms apply (induction) apply auto by (meson cnf_r1Tm rtranclp_trans)

lemma slemma5_1Nt:
  assumes "set (prods g) \<turnstile> lhs \<Rightarrow>* rhs"
    and "lhs = [Nt S]"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "set (prods g') \<turnstile> lhs \<Rightarrow>* rhs"
  using assms apply (induction) apply auto by (meson cnf_r1Nt rtranclp_trans)

lemma lemma5: 
  assumes "uniformize A t g g'"
  shows "L g \<subseteq> L g'"
proof 
  fix w
  assume "w \<in> L g"
  hence "set (prods g) \<turnstile> [Nt (start g')] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def uniformize_def by auto 
  thus "w \<in> L g'" 
    using assms slemma5_1 Lang_def by fastforce
qed 

lemma lemma5Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "L g \<subseteq> L g'"
proof 
  fix w
  assume "w \<in> L g"
  hence "set (prods g) \<turnstile> [Nt (start g')] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def binarizeNt_def by auto 
  thus "w \<in> L g'" 
    using assms slemma5_1Nt Lang_def by fast
qed 

lemma cnf_lemma1: 
  assumes "uniformize A t g g'"
  shows "L g = L g'"
  using assms lemma4 lemma5 by fast

lemma cnf_lemma1Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "L g = L g'"
  using assms lemma4Nt lemma5Nt by fast

definition eqLang :: "('n,'t) cfg \<Rightarrow> ('n,'t) cfg \<Rightarrow> bool" where
  "eqLang g g' \<longleftrightarrow> L g = L g'"

lemma uniformizeRtc_Eps_free: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g'"
    and "Eps_free (set (prods g))"
  shows "Eps_free (set (prods g'))"
  using assms by (induction) (auto simp: uniformize_Eps_free)

lemma binarizeNtRtc_Eps_free:
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g g'"
    and "Eps_free (set (prods g))"
  shows "Eps_free (set (prods g'))"
  using assms by (induction) (auto simp: binarizeNt_Eps_free)

lemma uniformizeRtc_Unit_free: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g'"
    and "Unit_free (set (prods g))"
  shows "Unit_free (set (prods g'))"
  using assms by (induction) (auto simp: uniformize_Unit_free)

lemma binarizeNtRtc_Unit_free:
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g g'"
    and "Unit_free (set (prods g))"
  shows "Unit_free (set (prods g'))"
  using assms by (induction) (auto simp: binarizeNt_Unit_free)

(* proofs about Nts *)

lemma Nts_aux1: "Nts (Ps \<union> Ps') = Nts Ps \<union> Nts Ps'"
  unfolding Nts_def by simp

lemma uniformize_Nts: 
  assumes "uniformize A t g g'" "S \<in> Nts (set (prods g))"
  shows "S \<in> Nts (set (prods g'))"
proof -
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g))) 
      \<and> set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding uniformize_def by fastforce
  thus ?thesis
  proof (cases "S \<in> Nts {(l,r)}")
    case True
    hence "S \<in> Nts {(A,[Tm t]), (l, p@[Nt A]@s)}"
      unfolding Nts_def nts_of_syms_def using \<open>?lrps\<close> by auto
    then show ?thesis using  \<open>?lrps\<close> Nts_aux1 by (metis UnCI)
  next
    case False
    hence "S \<in> Nts (set (prods g) - {(l,r)})"
      unfolding Nts_def using \<open>?lrps\<close> 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) Nts_aux1 Nts_def)
    then show ?thesis 
      by (simp add: \<open>?lrps\<close> Nts_def)
  qed
qed  

lemma uniformizeRtc_Nts: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g'" "S \<in> Nts (set (prods g))"
  shows "S \<in> Nts (set (prods g'))"
  using assms by (induction rule: rtranclp.induct) (auto simp: uniformize_Nts)

lemma binarizeNt_Nts: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'" "S \<in> Nts (set (prods g))"
  shows "S \<in> Nts (set (prods g'))"
proof -
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g)))
    \<and> (set (prods g') = ((set (prods g) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding binarizeNt_def by fastforce
    thus ?thesis
  proof (cases "S \<in> Nts {(l,r)}")
    case True
    hence "S \<in> Nts {(A,[Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}"
      unfolding Nts_def nts_of_syms_def using \<open>?lrps\<close> by auto
    then show ?thesis 
      using  \<open>?lrps\<close> Nts_aux1 by (metis UnCI)
  next
    case False
    hence "S \<in> Nts (set (prods g) - {(l,r)})"
      unfolding Nts_def using \<open>?lrps\<close> 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) Nts_aux1 Nts_def)
    then show ?thesis 
      by (simp add: \<open>?lrps\<close> Nts_def)
  qed
qed  

lemma binarizeNtRtc_Nts: 
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g g'" "S \<in> Nts (set (prods g))"
  shows "S \<in> Nts (set (prods g'))"
  using assms by (induction rule: rtranclp.induct) (auto simp: binarizeNt_Nts)

(* Termination *)

theorem cnf_lemma2: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g'"
  shows "L g = L g'"
  using assms by (induction rule: rtranclp.induct) (fastforce simp: cnf_lemma1)+ 

theorem cnf_lemma2Nt: 
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g g'"
  shows "L g = L g'"
  using assms by (induction rule: rtranclp.induct) (fastforce simp: cnf_lemma1Nt)+

theorem cnf_lemma: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g'"
    and "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g' g''"
  shows "L g = L g''"
  using assms cnf_lemma2 cnf_lemma2Nt uniformizeRtc_Nts by fastforce

(* Psart 2 *)
lemma badTmsCount_append: "badTmsCount (Ps@Ps') = badTmsCount Ps + badTmsCount Ps'"
  by (induction Ps) auto

lemma badNtsCount_append: "badNtsCount (Ps@Ps') = badNtsCount Ps + badNtsCount Ps'"
  by (induction Ps) auto

lemma badTmsCount_removeAll: 
  assumes "prodTms p > 0" "p \<in> set Ps"
  shows "badTmsCount (removeAll p Ps) < badTmsCount Ps"
  using assms by (induction Ps) fastforce+

lemma badNtsCount_removeAll: 
  assumes "prodNts p > 0" "p \<in> set Ps"
  shows "badNtsCount (removeAll p Ps) < badNtsCount Ps"
  using assms by (induction Ps) fastforce+

lemma badTmsCount_removeAll2:
  assumes "prodTms p > 0" "p \<in> set Ps" "prodTms p' < prodTms p"
  shows "badTmsCount (removeAll p Ps) + prodTms p' < badTmsCount Ps"
  using assms by (induction Ps) fastforce+

lemma badNtsCount_removeAll2:
  assumes "prodNts p > 0" "p \<in> set Ps" "prodNts p' < prodNts p"
  shows "badNtsCount (removeAll p Ps) + prodNts p' < badNtsCount Ps"
  using assms by (induction Ps) fastforce+

lemma lemma6_a: 
  assumes "uniformize A t g g'" 
  shows "badTmsCount (prods g') < badTmsCount (prods g)"
proof -
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g))) 
      \<and> prods g' = ((removeAll (l,r) (prods g)) @ [(A,[Tm t]), (l, p@[Nt A]@s)])" (is "?lrps")
    using assms fresh unfolding uniformize_def by auto
  hence "prodTms (l,p@[Tm t]@s) = length (filter (isTm) (p@[Tm t]@s))"
    unfolding prodTms_def by auto
  hence 1: "prodTms (l,p@[Tm t]@s) = Suc (length (filter (isTm) (p@s)))"
    by (simp add: isTm_def)
  have 2: "badTmsCount (prods g') = badTmsCount (removeAll (l,r) (prods g)) + badTmsCount [(A,[Tm t])] + badTmsCount [(l, p@[Nt A]@s)]"
    using \<open>?lrps\<close> by (auto simp: badTmsCount_append)
  have 3: "badTmsCount (removeAll (l,r) (prods g)) < badTmsCount (prods g)"
    using 1 badTmsCount_removeAll \<open>?lrps\<close> gr0_conv_Suc by blast
  have "prodTms (l, p@[Nt A]@s) = (length (filter (isTm) (p@[Nt A]@s))) \<or> prodTms (l, p@[Nt A]@s) = 0"
    unfolding prodTms_def using \<open>?lrps\<close> by simp
  thus ?thesis
  proof 
    assume "prodTms (l, p@[Nt A]@s) = (length (filter (isTm) (p@[Nt A]@s)))"
    hence "badTmsCount (prods g') = badTmsCount (removeAll (l,r) (prods g)) + prodTms (l, p@[Nt A]@s)"
      using 2 by (simp add: prodTms_def)
    moreover have "prodTms (l,p@[Nt A]@s) < prodTms (l,p@[Tm t]@s)"
      using 1 \<open>prodTms (l, p @ [Nt A] @ s) = length (filter isTm (p @ [Nt A] @ s))\<close> isTm_def by force 
    ultimately show "badTmsCount (prods g') < badTmsCount (prods g)" 
      using badTmsCount_removeAll2[of "(l,r)" "prods g" "(l,p @[Nt A]@s)"] \<open>?lrps\<close> 1 by auto
  next 
    assume "prodTms (l, p@[Nt A]@s) = 0"
    hence "badTmsCount (prods g') = badTmsCount (removeAll (l,r) (prods g))"
      using 2 by (simp add: prodTms_def)
    thus "badTmsCount (prods g') < badTmsCount (prods g)" 
      using 3 by simp
  qed
qed

lemma lemma6_b: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
  shows "badNtsCount (prods g') < badNtsCount (prods g)"
proof -
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g)))
    \<and> prods g' = ((removeAll (l,r) (prods g)) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)])" (is "?lrps")
    using assms(1) fresh unfolding binarizeNt_def by auto
  hence "prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = length (filter (isNt) (p@[Nt B\<^sub>1,Nt B\<^sub>2]@s))"
    unfolding prodNts_def by auto
  hence 1: "prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = Suc (Suc (length (filter (isNt) (p@s))))"
    by (simp add: isNt_def)
  have 2: "badNtsCount (prods g') = badNtsCount (removeAll (l,r) (prods g)) + badNtsCount [(A, [Nt B\<^sub>1,Nt B\<^sub>2])] + badNtsCount [(l, (p@[Nt A]@s))]"
    using \<open>?lrps\<close> by (auto simp: badNtsCount_append prodNts_def)
  have 3: "badNtsCount (removeAll (l,r) (prods g)) < badNtsCount (prods g)"
    using \<open>?lrps\<close> badNtsCount_removeAll 1 by force
  have "prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s)) \<or> prodNts (l, p@[Nt A]@s) = 0"
    unfolding prodNts_def using \<open>?lrps\<close> by simp
  thus ?thesis 
  proof 
    assume "prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))"
    hence "badNtsCount (prods g') = badNtsCount (removeAll (l,r) (prods g)) + badNtsCount [(l, (p@[Nt A]@s))]"
      using 2 by (simp add: prodNts_def)
    moreover have "prodNts (l, p@[Nt A]@s) < prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)"
      using 1 \<open>prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))\<close> isNt_def by simp
    ultimately show ?thesis 
      using badNtsCount_removeAll2[of "(l,r)" "prods g" "(l, (p@[Nt A]@s))"] 1 \<open>?lrps\<close> by auto
  next 
    assume "prodNts (l, p@[Nt A]@s) = 0"
    hence "badNtsCount (prods g') = badNtsCount (removeAll (l,r) (prods g))"
      using 2 by (simp add: prodNts_def)
    thus ?thesis 
      using 3 by simp
  qed
qed

lemma badTmsCount0_removeAll: "badTmsCount Ps = 0 \<Longrightarrow> badTmsCount (removeAll (l,r) Ps) = 0" 
  by (induction Ps) auto 

lemma slemma15_a:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
    and "badTmsCount (prods g) = 0"
  shows "badTmsCount (prods g') = 0"
proof -
  obtain l r p s where "(l,r) \<in> set (prods g) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods g)))
    \<and> (prods g' = ((removeAll (l,r) (prods g)) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)]))" (is "?lrps")
    using assms(1) fresh unfolding binarizeNt_def by auto
  hence "badTmsCount (prods g') = badTmsCount (removeAll (l,r) (prods g)) + badTmsCount [(l, (p@[Nt A]@s))]"
    by (auto simp: badTmsCount_append prodTms_def isTm_def)
  moreover have "badTmsCount (removeAll (l,r) (prods g)) = 0"
    using badTmsCount0_removeAll[of \<open>prods g\<close> l r] assms(2) by simp
  moreover have "badTmsCount [(l, (p@[Nt A]@s))] = 0" 
  proof -
    have "prodTms (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = 0"
      using \<open>?lrps\<close> assms(2) badTmsCountSet by auto
    thus "badTmsCount [(l, (p@[Nt A]@s))] = 0"
      by (auto simp: isTm_def prodTms_def)
  qed
  ultimately show ?thesis 
    by simp
qed

lemma lemma15_a:
  assumes "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g g'"
    and "badTmsCount (prods g) = 0"
  shows "badTmsCount (prods g') = 0"
  using assms by (induction) (auto simp: slemma15_a)

lemma noTms_prodTms0:
  assumes "prodTms (l,r) = 0"
  shows "length r \<le> 1 \<or> (\<forall>a \<in> set r. isNt a)"
proof -
  have "length r \<le> 1 \<or> (\<nexists>a. a \<in> set r \<and> isTm a)"
    using assms unfolding prodTms_def using empty_filter_conv by fastforce
  thus ?thesis 
    by (metis isNt_def isTm_def sym.exhaust)
qed

lemma badTmsCountNot0:
  assumes "badTmsCount (prods g) > 0"
  shows "\<exists>l r t. (l,r) \<in> set (prods g) \<and> length r \<ge> 2 \<and> Tm t \<in> set r"
proof -
  have "\<exists>p \<in> set (prods g). prodTms p > 0"
    using assms badTmsCountSet not_gr0 by blast
  from this obtain l r where "(l, r) \<in> set (prods g) \<and> prodTms (l,r) > 0" (is "?lr")
    by auto
  hence 1: "length r \<ge> 2"
    unfolding prodTms_def using not_le_imp_less by fastforce
  hence "prodTms (l,r) = length (filter (isTm) r)"
    unfolding prodTms_def by simp
  hence "\<exists>t. Tm t \<in> set r"
    by (metis \<open>?lr\<close> empty_filter_conv isTm_def length_greater_0_conv)
  thus ?thesis using \<open>?lr\<close> 1 by blast
qed

lemma badNtsCountNot0: 
  assumes "badNtsCount (prods g) > 0" 
  shows "\<exists>l r. (l, r) \<in> set (prods g) \<and> length r \<ge> 3"
proof -
  have "\<exists>p \<in> set (prods g). prodNts p > 0"
    using assms badNtsCountSet not_gr0 by blast
  from this obtain l r where "(l, r) \<in> set (prods g) \<and> prodNts (l,r) > 0" (is "?lr")
    by auto
  hence "length r \<ge> 3"
    unfolding prodNts_def using not_le_imp_less by fastforce
  thus ?thesis using \<open>?lr\<close> by auto
qed

lemma list_longer2: "length l \<ge> 2 \<and> x \<in> set l \<Longrightarrow> (\<exists>hd tl . l = hd@[x]@tl \<and> (hd \<noteq> [] \<or> tl \<noteq> []))"
  using split_list_last by fastforce 

lemma list_longer3: "length l \<ge> 3 \<Longrightarrow> (\<exists>hd tl x y. l = hd@[x]@[y]@tl \<and> (hd \<noteq> [] \<or> tl \<noteq> []))"
  by (metis Suc_le_length_iff append.left_neutral append_Cons neq_Nil_conv numeral_3_eq_3)

lemma lemma8_a:
  assumes "badTmsCount (prods g) > 0"
  shows "\<exists>g' A t. uniformize A t g g'"
proof -
  obtain l r t where "(l,r) \<in> set (prods g) \<and> length r \<ge> 2 \<and> Tm t \<in> set r" (is "?lr")
    using assms badTmsCountNot0 by blast
  from this obtain p s where "r = p@[Tm t]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])" (is "?ps")
    unfolding isTm_def using \<open>?lr\<close> list_longer2[of r] by blast
  from this obtain A g' where "A = fresh g \<and> g' = cfg (removeAll (l, r) (prods g) @ [(A, [Tm t]), (l, p @ [Nt A] @ s)]) (start g)" 
    by auto
  hence "uniformize A t g g'"
    unfolding uniformize_def using \<open>?lr\<close>  \<open>?ps\<close> by auto
  thus ?thesis by blast
qed

thm binarizeNt_def
lemma lemma8_b:
  assumes "badTmsCount (prods g) = 0"
    and "badNtsCount (prods g) > 0"
  shows "\<exists>g' A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
proof -
  obtain l r where "(l, r) \<in> set (prods g) \<and> length r \<ge> 3" (is "?lr")
    using assms(2) badNtsCountNot0 by blast
  obtain p s X Y where "r = p@[X]@[Y]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])" (is "?psXY")
    using \<open>?lr\<close> list_longer3[of r] by blast
  have "(\<forall>a \<in> set r. isNt a)"
    using \<open>?lr\<close> assms(1) badTmsCountSet[of \<open>prods g\<close>] noTms_prodTms0[of l r] by simp
  from this obtain B\<^sub>1 B\<^sub>2 where "X = Nt B\<^sub>1 \<and> Y = Nt B\<^sub>2"
    using isNt_def \<open>?psXY\<close> by fastforce
  hence "(r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> [])" (is "?B")
    using \<open>?psXY\<close> by auto
  from this obtain A g' where "A = fresh g \<and> g' = cfg (removeAll (l, r) (prods g) @ [(A, [Nt B\<^sub>1, Nt B\<^sub>2]), (l, p @ [Nt A] @ s)]) (start g)"
    by simp
  hence "binarizeNt A B\<^sub>1 B\<^sub>2 g g'"
    unfolding binarizeNt_def using \<open>?lr\<close> \<open>?B\<close> by auto
  thus ?thesis by blast
qed

lemma uniformize_2: "\<exists>g'. ((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g' \<and> (badTmsCount (prods g') = 0)"
proof (induction "badTmsCount (prods g)" arbitrary: g rule: less_induct)
  case less
  then show ?case
  proof (cases "badTmsCount (prods g) = 0")
    case False
    from this obtain g' A t where "uniformize A t g g'" (is "?g'")
      using lemma8_a by blast
    hence "badTmsCount (prods g') < badTmsCount (prods g)"
      using lemma6_a[of A t g g'] by blast
    from this obtain g'' where "(\<lambda>x y. \<exists>A t. uniformize A t x y)\<^sup>*\<^sup>* g' g'' \<and> badTmsCount (prods g'') = 0"
      using less by blast
    thus ?thesis 
      using \<open>?g'\<close> converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A t. uniformize A t x y)" g g' g''] by blast
  qed blast
qed

lemma binarizeNt_2: 
  assumes "badTmsCount (prods g) = 0"
    shows "\<exists>g'. ((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g g' \<and> (badNtsCount (prods g') = 0)"
using assms proof (induction "badNtsCount (prods g)" arbitrary: g rule: less_induct)
  case less
  then show ?case 
  proof (cases "badNtsCount (prods g) = 0")
    case False
    from this obtain g' A B\<^sub>1 B\<^sub>2 where "binarizeNt A B\<^sub>1 B\<^sub>2 g g'" (is "?g'")
      using assms lemma8_b less(2) by blast
    hence "badNtsCount (prods g') < badNtsCount (prods g)"
      using lemma6_b by blast
    from this obtain g'' where "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y)\<^sup>*\<^sup>* g' g'' \<and> badNtsCount (prods g'') = 0"
      using less slemma15_a[of A B\<^sub>1 B\<^sub>2 g g'] \<open>?g'\<close> by blast
    then show ?thesis 
      using \<open>?g'\<close> converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y)" g g' g''] by blast
  qed blast
qed

theorem uni_bin_exists: "\<forall>g::('n::infinite,'t) cfg. \<exists>g'::('n,'t)cfg. uniform (set (prods g')) \<and> binary (set (prods g')) \<and> L g = L g'"
proof 
  fix g::"('n::infinite,'t) cfg"
  obtain g' where "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g' \<and> (badTmsCount (prods g') = 0)" (is "?g'")
    using uniformize_2 by blast
  obtain g'' where "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g' g'' \<and> (badNtsCount (prods g'') = 0) \<and> (badTmsCount (prods g'') = 0)" (is "?g''")
    using \<open>?g'\<close> binarizeNt_2 lemma15_a by blast
  hence "uniform (set (prods g'')) \<and> binary (set (prods g''))"
    using count_bin_un by blast
  moreover have "L g = L g''"
    using \<open>?g'\<close> \<open>?g''\<close> cnf_lemma by blast
  ultimately show "\<exists>g'::('n,'t)cfg. uniform (set (prods g')) \<and> binary (set (prods g')) \<and> L g = L g'"
    by blast
qed

theorem cnf_noe_nou: 
  assumes "Eps_free (set (prods (g::('n::infinite,'t) cfg)))" "Unit_free (set (prods g))"
  shows "\<exists>g'::('n,'t) cfg. (uniform (set (prods g')) \<and> binary (set (prods g'))) \<and> (L g = L g') \<and> Eps_free (set (prods g')) \<and> Unit_free (set (prods g'))"
proof -
  obtain g' where "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) g g' \<and> (badTmsCount (prods g') = 0) \<and> Eps_free (set (prods g')) \<and> Unit_free (set (prods g'))" (is "?g'")
    using assms uniformize_2 uniformizeRtc_Eps_free uniformizeRtc_Unit_free by blast
  obtain g'' where "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) g' g'' \<and> (badNtsCount (prods g'') = 0) \<and> (badTmsCount (prods g'') = 0)" (is "?g''")
    using \<open>?g'\<close> binarizeNt_2 lemma15_a by blast
  hence "uniform (set (prods g'')) \<and> binary (set (prods g'')) \<and> Eps_free (set (prods g'')) \<and> Unit_free (set (prods g''))"
    using \<open>?g'\<close> count_bin_un binarizeNtRtc_Eps_free binarizeNtRtc_Unit_free by fastforce
  moreover have "L g = L g''"
    using \<open>?g'\<close> \<open>?g''\<close> cnf_lemma by blast
  ultimately show ?thesis
    using \<open>?g'\<close> \<open>?g''\<close> assms(1) by blast
qed

definition CNF :: "('n, 't) Prods \<Rightarrow> bool" where
  "CNF Ps \<equiv> (\<forall>(A,\<alpha>) \<in> Ps. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t]))"

abbreviation cnf :: "('n, 't) cfg \<Rightarrow> bool" where
  "cnf g \<equiv> CNF (set (prods g))"

(* alternative form more similar to the one Jana Hofmann used *)
lemma CNF_eq: "CNF Ps \<longleftrightarrow> (uniform Ps \<and> binary Ps \<and> Eps_free Ps \<and> Unit_free Ps)"
proof 
  assume "CNF Ps" (is "?assm")
  hence "Eps_free Ps"
    unfolding CNF_def Eps_free_def by fastforce
  moreover have "Unit_free Ps"
    using \<open>?assm\<close> unfolding CNF_def Unit_free_def isNt_def isTm_def by fastforce
  moreover have "uniform Ps"
  proof -
    have "\<forall>(A,\<alpha>) \<in> Ps. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t])"
      using \<open>?assm\<close> unfolding CNF_def.
    hence "\<forall>(A, \<alpha>) \<in> Ps. (\<forall>N \<in> set \<alpha>. isNt N) \<or> (\<exists>t. \<alpha> = [Tm t])"
      unfolding isNt_def by fastforce
    hence "\<forall>(A, \<alpha>) \<in> Ps. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"
      by (auto simp: isNt_def)
    thus "uniform Ps"
      unfolding uniform_def.
  qed
  moreover have "binary Ps"
    using \<open>?assm\<close> unfolding binary_def CNF_def by auto
  ultimately show "uniform Ps \<and> binary Ps \<and> Eps_free Ps \<and> Unit_free Ps"
    by blast
next 
  assume "uniform Ps \<and> binary Ps \<and> Eps_free Ps \<and> Unit_free Ps" (is "?assm")
  have"\<forall>p \<in> Ps. (\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. (snd p) = [Tm t])"
  proof
    fix p assume "p \<in> Ps" (is "?p")
    obtain A \<alpha> where "(A, \<alpha>) = p" (is "?A\<alpha>")
      by (metis prod.exhaust_sel)
    hence "length \<alpha> = 1 \<or> length \<alpha> = 2"
      using \<open>?assm\<close> \<open>?p\<close> order_neq_le_trans unfolding binary_def Eps_free_def by fastforce
    hence "(\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t])"
    proof 
      assume "length \<alpha> = 1"
      hence "\<exists>S. \<alpha> = [S]"
        by (simp add: length_Suc_conv)
      moreover have "\<nexists>N. \<alpha> = [Nt N]"
        using \<open>?assm\<close> \<open>?A\<alpha>\<close> \<open>?p\<close> unfolding Unit_free_def by blast
      ultimately show ?thesis by (metis sym.exhaust)
    next
      assume "length \<alpha> = 2"
      obtain B C where "\<alpha> = [B, C]" (is "?BC")
        using \<open>length \<alpha> = 2\<close> by (metis One_nat_def Suc_1 diff_Suc_1 length_0_conv length_Cons neq_Nil_conv)
      have "(\<nexists>t. Tm t \<in> set \<alpha>)"
        using \<open>length \<alpha> = 2\<close> \<open>?assm\<close> \<open>?A\<alpha>\<close> \<open>?p\<close> unfolding uniform_def by auto
      hence "(\<forall>N \<in> set \<alpha>. \<exists>A. N = Nt A)"
        by (metis sym.exhaust)
      hence "\<exists>B' C'. B = Nt B' \<and> C = Nt C'" 
        using \<open>?BC\<close> by simp
      thus ?thesis using \<open>?A\<alpha>\<close> \<open>?BC\<close> by auto
    qed
    thus "(\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. (snd p) = [Tm t])" using \<open>?A\<alpha>\<close> by auto
  qed
  thus "CNF Ps" by (auto simp: CNF_def)
qed

(* Main Theorem: existence of cnf for all cfg with the same Language except for the empty word [] *)
theorem cnf_exists: 
  shows "\<forall>g::('n::infinite,'t) cfg. \<exists>g'::('n,'t) cfg. (cnf g') \<and> (L g' = L g - {[]})"
proof
  fix g::"('n,'t)cfg"
  obtain Ps\<^sub>0 where "\<N> (prods g) Ps\<^sub>0" (is "?Ps\<^sub>0")
    using \<N>_exists by blast
  obtain Ps\<^sub>u where "\<U> Ps\<^sub>0 Ps\<^sub>u" (is "?Ps\<^sub>u")
    using \<U>_exists by blast
  obtain g\<^sub>u where "g\<^sub>u = cfg Ps\<^sub>u (start g)" (is "?g\<^sub>u")
    by simp
  hence 1: "Eps_free (set (prods g\<^sub>u)) \<and> Unit_free (set (prods g\<^sub>u))"
    using \<open>?Ps\<^sub>0\<close> \<open>?Ps\<^sub>u\<close> negrImpEps_free upgrImpUnit_free upgr_Eps_free by fastforce
  have 2: "L g\<^sub>u = L g - {[]}"
    using \<open>?Ps\<^sub>0\<close> \<open>?Ps\<^sub>u\<close> \<open>?g\<^sub>u\<close> \<N>_\<U>_lang_eq[of \<open>prods g\<close> Ps\<^sub>0 Ps\<^sub>u \<open>start g\<close>] by (simp add: \<N>_lang_eq)
  obtain g'::"('n,'t) cfg" where "uniform (set (prods g')) \<and> binary (set (prods g')) \<and> L g\<^sub>u = L g' \<and> Eps_free (set (prods g')) \<and> Unit_free (set (prods g'))" (is "?g'")
    using 1 cnf_noe_nou by blast
  hence "cnf g'" 
    using \<open>?g'\<close> CNF_eq by blast
  moreover have "L g' = L g - {[]}"
    using 2 \<open>?g'\<close> by blast
  ultimately show "\<exists>g'::('n,'t) cfg. (cnf g') \<and> (L g' = L g - {[]})" by blast
qed


(* some helpful properties *)
lemma cnf_length_derive: 
  assumes "Ps \<turnstile> [Nt S] \<Rightarrow>* \<alpha>" "CNF Ps" 
  shows "length \<alpha> \<ge> 1"
  using assms CNF_eq Eps_free_derives_Nil length_greater_0_conv less_eq_Suc_le by auto

lemma cnf_length_derive2: 
  assumes "Ps \<turnstile> [Nt A, Nt B] \<Rightarrow>* \<alpha>" "CNF Ps" 
  shows "length \<alpha> \<ge> 2"
proof -
  obtain u v where "Ps \<turnstile> [Nt A] \<Rightarrow>* u \<and> Ps \<turnstile> [Nt B] \<Rightarrow>* v \<and> \<alpha> = u @ v" (is "?uv")
    using assms(1) derives_append_decomp[of Ps \<open>[Nt A]\<close> \<open>[Nt B]\<close> \<alpha>] by auto
  hence "length u \<ge> 1 \<and> length v \<ge> 1" 
    using assms(2) cnf_length_derive[of Ps] by blast
  thus ?thesis
    using \<open>?uv\<close> by simp
qed

lemma cnf_single_derive:
  assumes "Ps \<turnstile> [Nt S] \<Rightarrow>* [Tm t]" "CNF Ps"
  shows "(S, [Tm t]) \<in> Ps"
proof -
  obtain \<alpha> where "Ps \<turnstile> [Nt S] \<Rightarrow> \<alpha> \<and> Ps \<turnstile> \<alpha> \<Rightarrow>* [Tm t]" (is "?\<alpha>")
    using assms(1) converse_rtranclpE by force
  hence 1: "(S, \<alpha>) \<in> Ps" 
    by (simp add: derive_singleton)
  have "\<nexists>A B. \<alpha> = [Nt A, Nt B]"
  proof (rule ccontr)
    assume "\<not> (\<nexists>A B. \<alpha> = [Nt A, Nt B])"
    from this obtain A B where "\<alpha> = [Nt A, Nt B]" (is "?AB")
      by blast
    have "\<forall>w. Ps \<turnstile> [Nt A, Nt B] \<Rightarrow>* w \<longrightarrow> length w \<ge> 2"
      using cnf_length_derive2 assms(2) by force
    moreover have "length [Tm t] = 1"
      by simp
    ultimately show False
      using \<open>?\<alpha>\<close> \<open>?AB\<close> by auto
  qed
  from this obtain a where "\<alpha> = [Tm a]"
    using 1 assms(2) unfolding CNF_def by auto
  hence "t = a"
    using \<open>?\<alpha>\<close> by (simp add: derives_T_Cons)
  thus ?thesis 
    using 1 \<open>\<alpha> = [Tm a]\<close> by blast
qed

lemma cnf_word:
  assumes "Ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w" "CNF Ps" 
    and "length w \<ge> 2"
  shows "\<exists>A B u v. (S, [Nt A, Nt B]) \<in> Ps \<and> Ps \<turnstile> [Nt A] \<Rightarrow>* map Tm u \<and> Ps \<turnstile> [Nt B] \<Rightarrow>* map Tm v \<and> u@v = w \<and> u \<noteq> [] \<and> v \<noteq> []"
proof -
  have 1: "(S, map Tm w) \<notin> Ps"
    using assms(2) assms(3) unfolding CNF_def by auto
  have "\<exists>\<alpha>. Ps \<turnstile> [Nt S] \<Rightarrow> \<alpha> \<and> Ps \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
    using assms(1) converse_rtranclpE by fastforce
  from this obtain \<alpha> where "(S, \<alpha>) \<in> Ps \<and> Ps \<turnstile> \<alpha> \<Rightarrow>* map Tm w" (is "?\<alpha>")
    by (auto simp: derive_singleton)
  hence "(\<nexists>t. \<alpha> = [Tm t])"
    using 1 derives_T_Cons[of Ps] derives_from_empty by auto
  hence "\<exists>A B. Ps \<turnstile> [Nt S] \<Rightarrow> [Nt A, Nt B] \<and> Ps \<turnstile> [Nt A, Nt B] \<Rightarrow>* map Tm w"
    using assms(2) \<open>?\<alpha>\<close>  derive_singleton[of Ps \<open>Nt S\<close> \<alpha>] unfolding CNF_def by fast
  from this obtain A B where "(S, [Nt A, Nt B]) \<in> Ps \<and> Ps \<turnstile> [Nt A, Nt B] \<Rightarrow>* map Tm w" (is "?AB")
    using derive_singleton[of Ps \<open>Nt S\<close>] by blast
  hence "\<not>(Ps \<turnstile> [Nt A] \<Rightarrow>* []) \<and> \<not>(Ps \<turnstile> [Nt B] \<Rightarrow>* [])"
    using assms(2) CNF_eq Eps_free_derives_Nil by blast
  from this obtain u v where "Ps \<turnstile> [Nt A] \<Rightarrow>* u \<and> Ps \<turnstile> [Nt B] \<Rightarrow>* v \<and> u@v = map Tm w \<and> u \<noteq> [] \<and> v \<noteq> []" (is "?uv")
    using \<open>?AB\<close> derives_append_decomp[of Ps \<open>[Nt A]\<close> \<open>[Nt B]\<close> \<open>map Tm w\<close>] by force
  moreover have "\<exists>u' v'. u = map Tm u' \<and> v = map Tm v'"
    using \<open>?uv\<close> map_eq_append_conv[of Tm w u v] by auto
  ultimately show ?thesis
    using \<open>?AB\<close> append_eq_map_conv[of u v Tm w] list.simps(8)[of Tm] by fastforce
qed

end 