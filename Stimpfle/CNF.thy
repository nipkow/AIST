theory CNF
  imports uProds
begin

definition isTm :: "('n, 't) sym \<Rightarrow> bool" where 
  "isTm s = (\<exists>a. s = Tm a)"

definition isNt :: "('n, 't) sym \<Rightarrow> bool" where 
  "isNt s = (\<exists>A. s = Nt A)"

definition nouProds :: "('n, 't) Prods \<Rightarrow> bool" where
  "nouProds P = (\<nexists>l A. (l,[Nt A]) \<in> P)"

lemma negrImpEps_free: 
  assumes "nepr P P'"
  shows "Eps_free (set P')"
  using assms unfolding nepr_def munge_def Eps_free_def by blast

lemma upgrImpnouProds:
  assumes "uppr P P'"
  shows "nouProds (set P')" 
  using assms 
  unfolding uppr_def uppr_rules_def nonUnitProds_def newProds_def unitProds_def nouProds_def by simp

lemma upgr_Eps_free:
  assumes "Eps_free (set P)"
    and "uppr P P'"
  shows "Eps_free (set P')"
  using assms 
  unfolding uppr_def Eps_free_def uppr_rules_def nonUnitProds_def unitProds_def newProds_def by auto

lemma Nts_correct: "A \<notin> Nts P \<Longrightarrow> (\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>))"
unfolding Nts_def nts_of_syms_def by auto

(* subsumed by lemma Lang_empty_if_notin_Lhss
lemma not_in_lang: 
  assumes "S \<notin> Nts P"  
  shows "Lang P S = {}"
  using assms Nts_correct 
  by (metis Lang_def all_not_in_conv deriven_start1 insert_is_Un list.set_intros(1) list.simps(15) mem_Collect_eq rtranclp_power)
*)

(* Chomsky Normal Form *)

axiomatization fresh :: "('n::infinite,'t) cfg \<Rightarrow> 'n" where
fresh: "fresh G \<notin> Nts(set (prods G)) \<union> {start G}"

abbreviation L :: "('n,'t) cfg \<Rightarrow> 't list set" where
  "L G \<equiv> Lang (set (prods G)) (start G)"

definition uniformize :: "'n::infinite \<Rightarrow> 't \<Rightarrow> ('n, 't) cfg \<Rightarrow> ('n, 't) cfg \<Rightarrow> bool" where 
      "uniformize A t G G' \<equiv> (
    \<exists> l r p s. (l,r) \<in> set (prods G) \<and> (r = p@[Tm t]@s) 
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A = fresh G)
    \<and> prods G' = ((removeAll (l,r) (prods G)) @ [(A,[Tm t]), (l, p@[Nt A]@s)]) 
    \<and> start G' = start G)"

lemma uniformize_Eps_free:
  assumes "Eps_free (set (prods G))"
    and "uniformize A t G G'"
  shows "Eps_free (set (prods G'))"
  using assms unfolding uniformize_def Eps_free_def by force

lemma uniformize_nouProds:
  assumes "nouProds (set (prods G))"
    and "uniformize A t G G'"
  shows "nouProds (set (prods G'))"
proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set (prods G)))"
    using assms(1) unfolding nouProds_def by simp
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(2) set_removeAll unfolding uniformize_def by force
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A,[Tm t]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set (prods G) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using \<open>?lrps\<close> by simp
  ultimately show ?thesis unfolding nouProds_def by simp
qed

definition prodTms :: "('n,'t) prod \<Rightarrow> nat" where
  "prodTms p \<equiv> (if length (snd p) \<le> 1 then 0 else length (filter (isTm) (snd p)))"

definition prodNts :: "('n,'t) prod \<Rightarrow> nat" where
  "prodNts p \<equiv> (if length (snd p) \<le> 2 then 0 else length (filter (isNt) (snd p)))"

fun badTmsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badTmsCount [] = 0" |
  "badTmsCount (p#ps) = (prodTms p) + badTmsCount ps"

lemma badTmsCountSet: "(\<forall>p \<in> set P. prodTms p = 0) \<longleftrightarrow> badTmsCount P = 0"
  by (induction P) auto

fun badNtsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badNtsCount [] = 0" |
  "badNtsCount (p#ps) = (prodNts p) + badNtsCount ps"

lemma badNtsCountSet: "(\<forall>p \<in> set P. prodNts p = 0) \<longleftrightarrow> badNtsCount P = 0"
  by (induction P) auto

definition uniform :: "('n, 't) Prods \<Rightarrow> bool" where
  "uniform P \<equiv> \<forall>(A, \<alpha>) \<in> P. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"

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
  "binary P \<equiv> \<forall>(A, \<alpha>) \<in> P. length \<alpha> \<le> 2"

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
      "binarizeNt A B\<^sub>1 B\<^sub>2 G G' \<equiv> (
    \<exists>l r p s. (l,r) \<in> set (prods G) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A = fresh G)
    \<and> prods G' = ((removeAll (l,r) (prods G)) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)])
    \<and> start G' = start G)"

lemma binarizeNt_Eps_free:
  assumes "Eps_free (set (prods G))"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "Eps_free (set (prods G'))"
  using assms unfolding binarizeNt_def Eps_free_def by force

lemma binarizeNt_nouProds:
  assumes "nouProds (set (prods G))"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "nouProds (set (prods G'))"
  proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set (prods G)))"
    using assms(1) unfolding nouProds_def by simp
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> (set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(2) set_removeAll unfolding binarizeNt_def by force
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set (prods G) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using \<open>?lrps\<close> by simp
  ultimately show ?thesis unfolding nouProds_def by simp
qed

lemma binarizeNt_aux1:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "A \<noteq> B\<^sub>1 \<and> A \<noteq> B\<^sub>2"
  using assms fresh unfolding binarizeNt_def Nts_def nts_of_syms_def by fastforce

lemma cnf_r1Tm: 
  assumes "uniformize A t G G'"
    and "set (prods G) \<turnstile> lhs \<Rightarrow> rhs"
  shows "set (prods G') \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set (prods G)" (is "?uv")
    using assms(2) derive.cases by meson
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G)))
      \<and> set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding uniformize_def by fastforce
  thus ?thesis 
  proof (cases "u = l")
    case True
    then show ?thesis
    proof (cases "v = p@[Tm t]@s")
      case True
      have 1: "(set (prods G')) \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      have "(set (prods G')) \<turnstile> [Nt A] \<Rightarrow> [Tm t]"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      hence "(set (prods G')) \<turnstile> [Nt l] \<Rightarrow>* p@[Tm t]@s"
        using 1 by (meson converse_rtranclp_into_rtranclp r_into_rtranclp derive_append derive_prepend)
      thus ?thesis 
        using True \<open>u = l\<close> \<open>?uv\<close> derives_append derives_prepend by blast
    next
      case False
      then show ?thesis
        by (metis Pair_inject UnI2 Un_commute \<open>?lrps\<close> \<open>?uv\<close> insert_Diff insert_iff r_into_rtranclp derive.intros)
    qed
  next
    case False
    then show ?thesis 
      by (metis Pair_inject UnI2 Un_commute \<open>?lrps\<close> \<open>?uv\<close> insert_Diff insert_iff r_into_rtranclp derive.intros) 
  qed
qed

lemma cnf_r1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
    and "(set (prods G)) \<turnstile> lhs \<Rightarrow> rhs"
  shows "(set (prods G')) \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set (prods G)" (is "?uv")
    using assms(2) derive.cases by meson
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G)))
    \<and> (set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding binarizeNt_def by fastforce
  thus ?thesis
  proof (cases "u = l")
    case True
    then show ?thesis 
    proof (cases "v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s")
      case True
      have 1: "set (prods G') \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      have "set (prods G') \<turnstile> [Nt A] \<Rightarrow> [Nt B\<^sub>1,Nt B\<^sub>2]"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      hence "set (prods G') \<turnstile> [Nt l] \<Rightarrow>* p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" 
        using 1 by (meson converse_rtranclp_into_rtranclp derives_append derives_prepend r_into_rtranclp) 
      thus ?thesis 
        using True \<open>u = l\<close> \<open>?uv\<close> derives_append derives_prepend by blast
    next
      case False
      then show ?thesis 
        by (metis UnCI \<open>?lrps\<close> \<open>?uv\<close> insertE insert_Diff prod.inject r_into_rtranclp derive.intros) 
    qed
  next
    case False
    then show ?thesis 
      using \<open>?lrps\<close> \<open>?uv\<close> derive.simps by fastforce
  qed
qed

(* p = (A, [Tm t]): Replace the fresh Nt A in rhs by \<alpha> *)
fun elim :: "('n, 't) prod \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms"  where
  "elim _ [] = []" |
  "elim (A,\<alpha>) (r#rhs) = (if r = Nt A then \<alpha>@(elim (A,\<alpha>) rhs) else r#(elim (A,\<alpha>) rhs))"

lemma slemma1_1: 
  assumes "uniformize A t G G'"
    and "(A, \<alpha>) \<in> set (prods G')"
  shows "\<alpha> = [Tm t]"
proof -
  have "A \<notin> Nts (set (prods G))"
    using assms(1) fresh unfolding uniformize_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set (prods G)"
    unfolding Nts_def by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Tm t] \<and> (A, \<alpha>) \<in> set (prods G')"
    using assms(1) unfolding uniformize_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma1_1Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
    and "(A, \<alpha>) \<in> set (prods G')"
  shows "\<alpha> = [Nt B\<^sub>1,Nt B\<^sub>2]"
proof -
  have "A \<notin> Nts (set (prods G))"
    using assms(1) fresh unfolding binarizeNt_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set (prods G)"
    unfolding Nts_def  by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Nt B\<^sub>1,Nt B\<^sub>2] \<and> (A, \<alpha>) \<in> set (prods G')"
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
  assumes "uniformize A t G G'"
    and "(l,r) \<in> set (prods G)"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> Nts (set (prods G))"
    using assms(1) fresh unfolding uniformize_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set (prods G) \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>set (prods G)\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
    and "(l,r) \<in> set (prods G)"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> Nts (set (prods G))"
    using assms(1) fresh unfolding binarizeNt_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set (prods G) \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using Nts_correct[of A \<open>set (prods G)\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed


lemma lemma1:
  assumes "uniformize A t G G'"
    and "set (prods G') \<turnstile> lhs \<Rightarrow> rhs"
  shows "(elim (A, [Tm t]) lhs = elim (A, [Tm t]) rhs) \<or> (set (prods G) \<turnstile> (elim (A, [Tm t]) lhs) \<Rightarrow> (elim (A, [Tm t]) rhs))"
proof -
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G))) 
      \<and> set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding uniformize_def by fastforce
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set (prods G')" (is "?uv")
    using assms(2) derive.cases by meson
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
      hence 2: "(u, elim (A, [Tm t]) v) \<in> set (prods G)" using \<open>?lrps\<close> 
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
      hence 1: "(u, v) \<in> set (prods G)" 
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
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
    and "set (prods G') \<turnstile> lhs \<Rightarrow> rhs"
  shows "(elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs) 
          \<or> ((set (prods G)) \<turnstile> (elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs) \<Rightarrow> elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs)"
proof -
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G)))
    \<and> (set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding binarizeNt_def by fastforce
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set (prods G')" (is "?uv")
    using assms(2) derive.cases by meson
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
        using assms(1) binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 G G'] by fastforce 
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
        using True \<open>?lrps\<close> \<open>?uv\<close> assms slemma4_4Nt[of A B\<^sub>1 B\<^sub>2 G G'] binarizeNt_aux1[of A B\<^sub>1 B\<^sub>2 G G'] by auto
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) ([Nt A]@s)"
        using slemma4_0 by fast
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v = p @ [Nt B\<^sub>1,Nt B\<^sub>2] @ s"
        using 1 slemma4_0 slemma4_1 slemma4_3_1 by metis
      hence 2: "(u, elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v) \<in> set (prods G)" 
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
      hence 1: "(u, v) \<in> set (prods G)" 
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
  assumes "set (prods G') \<turnstile> lhs \<Rightarrow>* rhs"
    and "uniformize A t G G'"
  shows "set (prods G) \<turnstile> (elim (A, [Tm t]) lhs) \<Rightarrow>* (elim (A, [Tm t]) rhs)"
  using assms
proof (induction)
  case (step y z)
  then show ?case 
    using lemma1[of A t G G' y z] rtranclp.rtrancl_into_rtrancl by fastforce 
qed simp

lemma lemma3Nt:
  assumes "set (prods G') \<turnstile> lhs \<Rightarrow>* rhs"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "set (prods G) \<turnstile> (elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) lhs) \<Rightarrow>* (elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) rhs)"
  using assms 
proof (induction)
  case (step y z)
  then show ?case 
    using lemma1Nt[of A B\<^sub>1 B\<^sub>2 G G' y z] rtranclp.rtrancl_into_rtrancl by fastforce 
qed simp

lemma slemma4_7: "map Tm w = elim (A, \<alpha>) (map Tm w)"
  by (induction w) auto

lemma lemma4:
  assumes "uniformize A t G G'" 
  shows "L G' \<subseteq> L G"
proof 
  fix w
  assume "w \<in> L G'"
  hence "set (prods G') \<turnstile> [Nt (start G')] \<Rightarrow>* map Tm w"
    unfolding Lang_def by simp
  hence "set (prods G') \<turnstile> [Nt (start G)] \<Rightarrow>* map Tm w"
    using assms unfolding uniformize_def by auto
  hence "set (prods G) \<turnstile> elim (A, [Tm t]) [Nt (start G)] \<Rightarrow>*  elim (A, [Tm t]) (map Tm w)"
    using assms lemma3[of G' \<open>[Nt (start G)]\<close> \<open>map Tm w\<close> A t G] by blast
  moreover have "elim (A, [Tm t]) [Nt (start G)] = [Nt (start G)]"
    using assms fresh unfolding uniformize_def 
    by (metis Un_iff singletonI slemma4_2_0 slemma4_2_1) (*TODO*)
  moreover have "elim (A, [Tm t]) (map Tm w) = map Tm w" 
    using \<open>w \<in> L G'\<close> slemma4_7 by metis
  ultimately show "w \<in> L G" 
    using  \<open>w \<in> L G'\<close> by (simp add: Lang_def)
qed

lemma lemma4Nt:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "L G' \<subseteq> L G"
proof
  fix w
  assume "w \<in> L G'"
  hence "set (prods G') \<turnstile> [Nt (start G')] \<Rightarrow>* map Tm w"
    by (simp add: Lang_def)
  hence "set (prods G') \<turnstile> [Nt (start G)] \<Rightarrow>* map Tm w"
    using assms unfolding binarizeNt_def by auto
  hence "set (prods G) \<turnstile> elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) [Nt (start G)] \<Rightarrow>*  elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) (map Tm w)"
    using assms lemma3Nt[of G' \<open>[Nt (start G)]\<close> \<open>map Tm w\<close> A B\<^sub>1 B\<^sub>2 G] by blast
  moreover have "elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) [Nt (start G)] = [Nt (start G)]"
    using assms fresh unfolding binarizeNt_def 
    by (metis UnCI singletonI slemma4_2_0 slemma4_2_1) (*TODO*)
  moreover have "elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) (map Tm w) = map Tm w" 
    using \<open>w \<in> L G'\<close> slemma4_7 by metis
  ultimately show "w \<in> L G" using Lang_def \<open>w \<in> L G'\<close> 
    by (metis (no_types, lifting) mem_Collect_eq)
qed

lemma slemma5_1:
  assumes "set (prods G) \<turnstile> lhs \<Rightarrow>* rhs"
    and "lhs = [Nt S]"
    and "uniformize A t G G'"
  shows "set (prods G') \<turnstile> lhs \<Rightarrow>* rhs"
  using assms apply (induction) apply auto by (meson cnf_r1Tm rtranclp_trans)

lemma slemma5_1Nt:
  assumes "set (prods G) \<turnstile> lhs \<Rightarrow>* rhs"
    and "lhs = [Nt S]"
    and "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "set (prods G') \<turnstile> lhs \<Rightarrow>* rhs"
  using assms apply (induction) apply auto by (meson cnf_r1Nt rtranclp_trans)

lemma lemma5: 
  assumes "uniformize A t G G'"
  shows "L G \<subseteq> L G'"
proof 
  fix w
  assume "w \<in> L G"
  hence "set (prods G) \<turnstile> [Nt (start G')] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def uniformize_def by auto 
  thus "w \<in> L G'" 
    using assms slemma5_1 Lang_def by fastforce
qed 

lemma lemma5Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "L G \<subseteq> L G'"
proof 
  fix w
  assume "w \<in> L G"
  hence "set (prods G) \<turnstile> [Nt (start G')] \<Rightarrow>* map Tm w"
    using assms unfolding Lang_def binarizeNt_def by auto 
  thus "w \<in> L G'" 
    using assms slemma5_1Nt Lang_def by fast
qed 

lemma cnf_lemma1: 
  assumes "uniformize A t G G'"
  shows "L G = L G'"
  using assms lemma4 lemma5 by fast

lemma cnf_lemma1Nt: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "L G = L G'"
  using assms lemma4Nt lemma5Nt by fast

definition eqLang :: "('n,'t) cfg \<Rightarrow> ('n,'t) cfg \<Rightarrow> bool" where
  "eqLang G G' \<longleftrightarrow> L G = L G'"

lemma uniformizeRtc_Eps_free: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G'"
    and "Eps_free (set (prods G))"
  shows "Eps_free (set (prods G'))"
  using assms by (induction) (auto simp: uniformize_Eps_free)

lemma binarizeNtRtc_Eps_free:
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G G'"
    and "Eps_free (set (prods G))"
  shows "Eps_free (set (prods G'))"
  using assms by (induction) (auto simp: binarizeNt_Eps_free)

lemma uniformizeRtc_nouProds: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G'"
    and "nouProds (set (prods G))"
  shows "nouProds (set (prods G'))"
  using assms by (induction) (auto simp: uniformize_nouProds)

lemma binarizeNtRtc_nouProds:
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G G'"
    and "nouProds (set (prods G))"
  shows "nouProds (set (prods G'))"
  using assms by (induction) (auto simp: binarizeNt_nouProds)

(* proofs about Nts *)

lemma Nts_aux1: "Nts (P \<union> P') = Nts P \<union> Nts P'"
  unfolding Nts_def by simp

lemma uniformize_Nts: 
  assumes "uniformize A t G G'" "S \<in> Nts (set (prods G))"
  shows "S \<in> Nts (set (prods G'))"
proof -
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G))) 
      \<and> set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) set_removeAll fresh unfolding uniformize_def by fastforce
  thus ?thesis
  proof (cases "S \<in> Nts {(l,r)}")
    case True
    hence "S \<in> Nts {(A,[Tm t]), (l, p@[Nt A]@s)}"
      unfolding Nts_def nts_of_syms_def using \<open>?lrps\<close> by auto
    then show ?thesis using  \<open>?lrps\<close> Nts_aux1 by (metis UnCI)
  next
    case False
    hence "S \<in> Nts (set (prods G) - {(l,r)})"
      unfolding Nts_def using \<open>?lrps\<close> 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) Nts_aux1 Nts_def)
    then show ?thesis 
      by (simp add: \<open>?lrps\<close> Nts_def)
  qed
qed  

lemma uniformizeRtc_Nts: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G'" "S \<in> Nts (set (prods G))"
  shows "S \<in> Nts (set (prods G'))"
  using assms by (induction rule: rtranclp.induct) (auto simp: uniformize_Nts)

lemma binarizeNt_Nts: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'" "S \<in> Nts (set (prods G))"
  shows "S \<in> Nts (set (prods G'))"
proof -
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G)))
    \<and> (set (prods G') = ((set (prods G) - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
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
    hence "S \<in> Nts (set (prods G) - {(l,r)})"
      unfolding Nts_def using \<open>?lrps\<close> 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) Nts_aux1 Nts_def)
    then show ?thesis 
      by (simp add: \<open>?lrps\<close> Nts_def)
  qed
qed  

lemma binarizeNtRtc_Nts: 
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G G'" "S \<in> Nts (set (prods G))"
  shows "S \<in> Nts (set (prods G'))"
  using assms by (induction rule: rtranclp.induct) (auto simp: binarizeNt_Nts)

(* Termination *)

theorem cnf_lemma2: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G'"
  shows "L G = L G'"
  using assms by (induction rule: rtranclp.induct) (fastforce simp: cnf_lemma1)+ 

theorem cnf_lemma2Nt: 
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G G'"
  shows "L G = L G'"
  using assms by (induction rule: rtranclp.induct) (fastforce simp: cnf_lemma1Nt)+

theorem cnf_lemma: 
  assumes "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G'"
    and "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G' G''"
  shows "L G = L G''"
  using assms cnf_lemma2 cnf_lemma2Nt uniformizeRtc_Nts by fastforce

(* Part 2 *)
lemma badTmsCount_append: "badTmsCount (P@P') = badTmsCount P + badTmsCount P'"
  by (induction P) auto

lemma badNtsCount_append: "badNtsCount (P@P') = badNtsCount P + badNtsCount P'"
  by (induction P) auto

lemma badTmsCount_removeAll: 
  assumes "prodTms p > 0" "p \<in> set P"
  shows "badTmsCount (removeAll p P) < badTmsCount P"
  using assms by (induction P) fastforce+

lemma badNtsCount_removeAll: 
  assumes "prodNts p > 0" "p \<in> set P"
  shows "badNtsCount (removeAll p P) < badNtsCount P"
  using assms by (induction P) fastforce+

lemma badTmsCount_removeAll2:
  assumes "prodTms p > 0" "p \<in> set P" "prodTms p' < prodTms p"
  shows "badTmsCount (removeAll p P) + prodTms p' < badTmsCount P"
  using assms by (induction P) fastforce+

lemma badNtsCount_removeAll2:
  assumes "prodNts p > 0" "p \<in> set P" "prodNts p' < prodNts p"
  shows "badNtsCount (removeAll p P) + prodNts p' < badNtsCount P"
  using assms by (induction P) fastforce+

lemma lemma6_a: 
  assumes "uniformize A t G G'" 
  shows "badTmsCount (prods G') < badTmsCount (prods G)"
proof -
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G))) 
      \<and> prods G' = ((removeAll (l,r) (prods G)) @ [(A,[Tm t]), (l, p@[Nt A]@s)])" (is "?lrps")
    using assms fresh unfolding uniformize_def by auto
  hence "prodTms (l,p@[Tm t]@s) = length (filter (isTm) (p@[Tm t]@s))"
    unfolding prodTms_def by auto
  hence 1: "prodTms (l,p@[Tm t]@s) = Suc (length (filter (isTm) (p@s)))"
    by (simp add: isTm_def)
  have 2: "badTmsCount (prods G') = badTmsCount (removeAll (l,r) (prods G)) + badTmsCount [(A,[Tm t])] + badTmsCount [(l, p@[Nt A]@s)]"
    using \<open>?lrps\<close> by (auto simp: badTmsCount_append)
  have 3: "badTmsCount (removeAll (l,r) (prods G)) < badTmsCount (prods G)"
    using 1 badTmsCount_removeAll \<open>?lrps\<close> gr0_conv_Suc by blast
  have "prodTms (l, p@[Nt A]@s) = (length (filter (isTm) (p@[Nt A]@s))) \<or> prodTms (l, p@[Nt A]@s) = 0"
    unfolding prodTms_def using \<open>?lrps\<close> by simp
  thus ?thesis
  proof 
    assume "prodTms (l, p@[Nt A]@s) = (length (filter (isTm) (p@[Nt A]@s)))"
    hence "badTmsCount (prods G') = badTmsCount (removeAll (l,r) (prods G)) + prodTms (l, p@[Nt A]@s)"
      using 2 by (simp add: prodTms_def)
    moreover have "prodTms (l,p@[Nt A]@s) < prodTms (l,p@[Tm t]@s)"
      using 1 \<open>prodTms (l, p @ [Nt A] @ s) = length (filter isTm (p @ [Nt A] @ s))\<close> isTm_def by force 
    ultimately show "badTmsCount (prods G') < badTmsCount (prods G)" 
      using badTmsCount_removeAll2[of "(l,r)" "prods G" "(l,p @[Nt A]@s)"] \<open>?lrps\<close> 1 by auto
  next 
    assume "prodTms (l, p@[Nt A]@s) = 0"
    hence "badTmsCount (prods G') = badTmsCount (removeAll (l,r) (prods G))"
      using 2 by (simp add: prodTms_def)
    thus "badTmsCount (prods G') < badTmsCount (prods G)" 
      using 3 by simp
  qed
qed

lemma lemma6_b: 
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
  shows "badNtsCount (prods G') < badNtsCount (prods G)"
proof -
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G)))
    \<and> prods G' = ((removeAll (l,r) (prods G)) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)])" (is "?lrps")
    using assms(1) fresh unfolding binarizeNt_def by auto
  hence "prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = length (filter (isNt) (p@[Nt B\<^sub>1,Nt B\<^sub>2]@s))"
    unfolding prodNts_def by auto
  hence 1: "prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) = Suc (Suc (length (filter (isNt) (p@s))))"
    by (simp add: isNt_def)
  have 2: "badNtsCount (prods G') = badNtsCount (removeAll (l,r) (prods G)) + badNtsCount [(A, [Nt B\<^sub>1,Nt B\<^sub>2])] + badNtsCount [(l, (p@[Nt A]@s))]"
    using \<open>?lrps\<close> by (auto simp: badNtsCount_append prodNts_def)
  have 3: "badNtsCount (removeAll (l,r) (prods G)) < badNtsCount (prods G)"
    using \<open>?lrps\<close> badNtsCount_removeAll 1 by force
  have "prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s)) \<or> prodNts (l, p@[Nt A]@s) = 0"
    unfolding prodNts_def using \<open>?lrps\<close> by simp
  thus ?thesis 
  proof 
    assume "prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))"
    hence "badNtsCount (prods G') = badNtsCount (removeAll (l,r) (prods G)) + badNtsCount [(l, (p@[Nt A]@s))]"
      using 2 by (simp add: prodNts_def)
    moreover have "prodNts (l, p@[Nt A]@s) < prodNts (l,p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)"
      using 1 \<open>prodNts (l, p@[Nt A]@s) = length (filter (isNt) (p@[Nt A]@s))\<close> isNt_def by simp
    ultimately show ?thesis 
      using badNtsCount_removeAll2[of "(l,r)" "prods G" "(l, (p@[Nt A]@s))"] 1 \<open>?lrps\<close> by auto
  next 
    assume "prodNts (l, p@[Nt A]@s) = 0"
    hence "badNtsCount (prods G') = badNtsCount (removeAll (l,r) (prods G))"
      using 2 by (simp add: prodNts_def)
    thus ?thesis 
      using 3 by simp
  qed
qed

lemma badTmsCount0_removeAll: "badTmsCount P = 0 \<Longrightarrow> badTmsCount (removeAll (l,r) P) = 0" 
  by (induction P) auto 

lemma slemma15_a:
  assumes "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
    and "badTmsCount (prods G) = 0"
  shows "badTmsCount (prods G') = 0"
proof -
  obtain l r p s where "(l,r) \<in> set (prods G) \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> Nts (set (prods G)))
    \<and> (prods G' = ((removeAll (l,r) (prods G)) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)]))" (is "?lrps")
    using assms(1) fresh unfolding binarizeNt_def by auto
  hence "badTmsCount (prods G') = badTmsCount (removeAll (l,r) (prods G)) + badTmsCount [(l, (p@[Nt A]@s))]"
    by (auto simp: badTmsCount_append prodTms_def isTm_def)
  moreover have "badTmsCount (removeAll (l,r) (prods G)) = 0"
    using badTmsCount0_removeAll[of \<open>prods G\<close> l r] assms(2) by simp
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
  assumes "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G G'"
    and "badTmsCount (prods G) = 0"
  shows "badTmsCount (prods G') = 0"
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
  assumes "badTmsCount (prods G) > 0"
  shows "\<exists>l r t. (l,r) \<in> set (prods G) \<and> length r \<ge> 2 \<and> Tm t \<in> set r"
proof -
  have "\<exists>p \<in> set (prods G). prodTms p > 0"
    using assms badTmsCountSet not_gr0 by blast
  from this obtain l r where "(l, r) \<in> set (prods G) \<and> prodTms (l,r) > 0" (is "?lr")
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
  assumes "badNtsCount (prods G) > 0" 
  shows "\<exists>l r. (l, r) \<in> set (prods G) \<and> length r \<ge> 3"
proof -
  have "\<exists>p \<in> set (prods G). prodNts p > 0"
    using assms badNtsCountSet not_gr0 by blast
  from this obtain l r where "(l, r) \<in> set (prods G) \<and> prodNts (l,r) > 0" (is "?lr")
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
  assumes "badTmsCount (prods G) > 0"
  shows "\<exists>G' A t. uniformize A t G G'"
proof -
  obtain l r t where "(l,r) \<in> set (prods G) \<and> length r \<ge> 2 \<and> Tm t \<in> set r" (is "?lr")
    using assms badTmsCountNot0 by blast
  from this obtain p s where "r = p@[Tm t]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])" (is "?ps")
    unfolding isTm_def using \<open>?lr\<close> list_longer2[of r] by blast
  from this obtain A G' where "A = fresh G \<and> G' = cfg (removeAll (l, r) (prods G) @ [(A, [Tm t]), (l, p @ [Nt A] @ s)]) (start G)" 
    by auto
  hence "uniformize A t G G'"
    unfolding uniformize_def using \<open>?lr\<close>  \<open>?ps\<close> by auto
  thus ?thesis by blast
qed

thm binarizeNt_def
lemma lemma8_b:
  assumes "badTmsCount (prods G) = 0"
    and "badNtsCount (prods G) > 0"
  shows "\<exists>G' A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
proof -
  obtain l r where "(l, r) \<in> set (prods G) \<and> length r \<ge> 3" (is "?lr")
    using assms(2) badNtsCountNot0 by blast
  obtain p s X Y where "r = p@[X]@[Y]@s \<and> (p \<noteq> [] \<or> s \<noteq> [])" (is "?psXY")
    using \<open>?lr\<close> list_longer3[of r] by blast
  have "(\<forall>a \<in> set r. isNt a)"
    using \<open>?lr\<close> assms(1) badTmsCountSet[of \<open>prods G\<close>] noTms_prodTms0[of l r] by simp
  from this obtain B\<^sub>1 B\<^sub>2 where "X = Nt B\<^sub>1 \<and> Y = Nt B\<^sub>2"
    using isNt_def \<open>?psXY\<close> by fastforce
  hence "(r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> [])" (is "?B")
    using \<open>?psXY\<close> by auto
  from this obtain A G' where "A = fresh G \<and> G' = cfg (removeAll (l, r) (prods G) @ [(A, [Nt B\<^sub>1, Nt B\<^sub>2]), (l, p @ [Nt A] @ s)]) (start G)"
    by simp
  hence "binarizeNt A B\<^sub>1 B\<^sub>2 G G'"
    unfolding binarizeNt_def using \<open>?lr\<close> \<open>?B\<close> by auto
  thus ?thesis by blast
qed

lemma uniformize_2: "\<exists>G'. ((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G' \<and> (badTmsCount (prods G') = 0)"
proof (induction "badTmsCount (prods G)" arbitrary: G rule: less_induct)
  case less
  then show ?case
  proof (cases "badTmsCount (prods G) = 0")
    case False
    from this obtain G' A t where "uniformize A t G G'" (is "?G'")
      using lemma8_a by blast
    hence "badTmsCount (prods G') < badTmsCount (prods G)"
      using lemma6_a[of A t G G'] by blast
    from this obtain G'' where "(\<lambda>x y. \<exists>A t. uniformize A t x y)\<^sup>*\<^sup>* G' G'' \<and> badTmsCount (prods G'') = 0"
      using less by blast
    thus ?thesis 
      using \<open>?G'\<close> converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A t. uniformize A t x y)" G G' G''] by blast
  qed blast
qed

lemma binarizeNt_2: 
  assumes "badTmsCount (prods G) = 0"
    shows "\<exists>G'. ((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G G' \<and> (badNtsCount (prods G') = 0)"
using assms proof (induction "badNtsCount (prods G)" arbitrary: G rule: less_induct)
  case less
  then show ?case 
  proof (cases "badNtsCount (prods G) = 0")
    case False
    from this obtain G' A B\<^sub>1 B\<^sub>2 where "binarizeNt A B\<^sub>1 B\<^sub>2 G G'" (is "?G'")
      using assms lemma8_b less(2) by blast
    hence "badNtsCount (prods G') < badNtsCount (prods G)"
      using lemma6_b by blast
    from this obtain G'' where "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y)\<^sup>*\<^sup>* G' G'' \<and> badNtsCount (prods G'') = 0"
      using less slemma15_a[of A B\<^sub>1 B\<^sub>2 G G'] \<open>?G'\<close> by blast
    then show ?thesis 
      using \<open>?G'\<close> converse_rtranclp_into_rtranclp[of "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y)" G G' G''] by blast
  qed blast
qed

theorem uni_bin_exists: "\<forall>G::('n::infinite,'t) cfg. \<exists>G'::('n,'t)cfg. uniform (set (prods G')) \<and> binary (set (prods G')) \<and> L G = L G'"
proof 
  fix G::"('n::infinite,'t) cfg"
  obtain G' where "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G' \<and> (badTmsCount (prods G') = 0)" (is "?G'")
    using uniformize_2 by blast
  obtain G'' where "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G' G'' \<and> (badNtsCount (prods G'') = 0) \<and> (badTmsCount (prods G'') = 0)" (is "?G''")
    using \<open>?G'\<close> binarizeNt_2 lemma15_a by blast
  hence "uniform (set (prods G'')) \<and> binary (set (prods G''))"
    using count_bin_un by blast
  moreover have "L G = L G''"
    using \<open>?G'\<close> \<open>?G''\<close> cnf_lemma by blast
  ultimately show "\<exists>G'::('n,'t)cfg. uniform (set (prods G')) \<and> binary (set (prods G')) \<and> L G = L G'"
    by blast
qed

theorem cnf_noe_nou: 
  assumes "Eps_free (set (prods (G::('n::infinite,'t) cfg)))" "nouProds (set (prods G))"
  shows "\<exists>G'::('n,'t) cfg. (uniform (set (prods G')) \<and> binary (set (prods G'))) \<and> (L G = L G') \<and> Eps_free (set (prods G')) \<and> nouProds (set (prods G'))"
proof -
  obtain G' where "((\<lambda>x y. \<exists>A t. uniformize A t x y) ^**) G G' \<and> (badTmsCount (prods G') = 0) \<and> Eps_free (set (prods G')) \<and> nouProds (set (prods G'))" (is "?G'")
    using assms uniformize_2 uniformizeRtc_Eps_free uniformizeRtc_nouProds by blast
  obtain G'' where "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 x y) ^**) G' G'' \<and> (badNtsCount (prods G'') = 0) \<and> (badTmsCount (prods G'') = 0)" (is "?G''")
    using \<open>?G'\<close> binarizeNt_2 lemma15_a by blast
  hence "uniform (set (prods G'')) \<and> binary (set (prods G'')) \<and> Eps_free (set (prods G'')) \<and> nouProds (set (prods G''))"
    using \<open>?G'\<close> count_bin_un binarizeNtRtc_Eps_free binarizeNtRtc_nouProds by fastforce
  moreover have "L G = L G''"
    using \<open>?G'\<close> \<open>?G''\<close> cnf_lemma by blast
  ultimately show ?thesis
    using \<open>?G'\<close> \<open>?G''\<close> assms(1) by blast
qed

definition CNF :: "('n, 't) Prods \<Rightarrow> bool" where
  "CNF P \<equiv> (\<forall>(A,\<alpha>) \<in> P. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t]))"

abbreviation cnf :: "('n, 't) cfg \<Rightarrow> bool" where
  "cnf G \<equiv> CNF (set (prods G))"

lemma CNF_eq: "CNF P \<longleftrightarrow> (uniform P \<and> binary P \<and> Eps_free P \<and> nouProds P)"
proof 
  assume "CNF P" (is "?assm")
  hence "Eps_free P"
    unfolding CNF_def Eps_free_def by fastforce
  moreover have "nouProds P"
    using \<open>?assm\<close> unfolding CNF_def nouProds_def isNt_def isTm_def by fastforce
  moreover have "uniform P"
  proof -
    have "\<forall>(A,\<alpha>) \<in> P. (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t])"
      using \<open>?assm\<close> unfolding CNF_def.
    hence "\<forall>(A, \<alpha>) \<in> P. (\<forall>N \<in> set \<alpha>. isNt N) \<or> (\<exists>t. \<alpha> = [Tm t])"
      unfolding isNt_def by fastforce
    hence "\<forall>(A, \<alpha>) \<in> P. (\<nexists>t. Tm t \<in> set \<alpha>) \<or> (\<exists>t. \<alpha> = [Tm t])"
      by (auto simp: isNt_def)
    thus "uniform P"
      unfolding uniform_def.
  qed
  moreover have "binary P"
    using \<open>?assm\<close> unfolding binary_def CNF_def by auto
  ultimately show "uniform P \<and> binary P \<and> Eps_free P \<and> nouProds P"
    by blast
next 
  assume "uniform P \<and> binary P \<and> Eps_free P \<and> nouProds P" (is "?assm")
  have"\<forall>p \<in> P. (\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. (snd p) = [Tm t])"
  proof
    fix p assume "p \<in> P" (is "?p")
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
        using \<open>?assm\<close> \<open>?A\<alpha>\<close> \<open>?p\<close> unfolding nouProds_def by blast
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
  thus "CNF P" by (auto simp: CNF_def)
qed

theorem cnf_exists: 
  shows "\<forall>G::('n::infinite,'t) cfg. \<exists>G'::('n,'t) cfg. (cnf G') \<and> (L G' = L G - {[]})"
proof
  fix G::"('n,'t)cfg"
  obtain P\<^sub>0 where "nepr (prods G) P\<^sub>0" (is "?P\<^sub>0")
    using nepr_exists by blast
  obtain P\<^sub>u where "uppr P\<^sub>0 P\<^sub>u" (is "?P\<^sub>u")
    using uppr_exists by blast
  obtain G\<^sub>u where "G\<^sub>u = cfg P\<^sub>u (start G)" (is "?G\<^sub>u")
    by simp
  hence 1: "Eps_free (set (prods G\<^sub>u)) \<and> nouProds (set (prods G\<^sub>u))"
    using \<open>?P\<^sub>0\<close> \<open>?P\<^sub>u\<close> negrImpEps_free upgrImpnouProds upgr_Eps_free by fastforce
  have 2: "L G\<^sub>u = L G - {[]}"
    using \<open>?P\<^sub>0\<close> \<open>?P\<^sub>u\<close> \<open>?G\<^sub>u\<close> nepr_uppr_lang_eq[of \<open>prods G\<close> P\<^sub>0 P\<^sub>u \<open>start G\<close>] by (simp add: nepr_lang_eq)
  obtain G'::"('n,'t) cfg" where "uniform (set (prods G')) \<and> binary (set (prods G')) \<and> L G\<^sub>u = L G' \<and> Eps_free (set (prods G')) \<and> nouProds (set (prods G'))" (is "?G'")
    using 1 cnf_noe_nou by blast
  hence "cnf G'" 
    using \<open>?G'\<close> CNF_eq by blast
  moreover have "L G' = L G - {[]}"
    using 2 \<open>?G'\<close> by blast
  ultimately show "\<exists>G'::('n,'t) cfg. (cnf G') \<and> (L G' = L G - {[]})" by blast
qed

end