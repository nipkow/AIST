theory CNF
  imports "../CFG" eProds uProds
begin

definition isTmnlSym :: "('n, 't) sym \<Rightarrow> bool" where 
  "isTmnlSym s = (\<exists>a. s = Tm a)"

definition isNonTmnlSym :: "('n, 't) sym \<Rightarrow> bool" where 
  "isNonTmnlSym s = (\<exists>A. s = Nt A)"

definition noeProds :: "('n, 't) prodS \<Rightarrow> bool" where
  "noeProds P = (\<nexists>l. (l,[]) \<in> P)"

definition noUnitProds :: "('n, 't) prodS \<Rightarrow> bool" where
  "noUnitProds P = (\<nexists>l A. (l,[Nt A]) \<in> P)"

lemma negrImpnoeProds: 
  assumes "nepr P P'"
  shows "noeProds (set P')"
  using assms unfolding nepr_def noeProds_def munge_def by simp

lemma upgrImpnoUnitProds:
  assumes "uppr P P'"
  shows "noUnitProds (set P')" 
  using assms 
  unfolding uppr_def uppr_rules_def nonUnitProds_def newProds_def unitProds_def noUnitProds_def by simp

lemma upgr_noeProds:
  assumes "noeProds (set P)"
    and "uppr P P'"
  shows "noeProds (set P')"
  using assms 
  unfolding uppr_def noeProds_def uppr_rules_def nonUnitProds_def unitProds_def newProds_def by simp

(* Chomsky Normal Form *)

definition trans1Tmnl :: "'n \<Rightarrow> 't \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> bool" where 
      "trans1Tmnl A t P P' \<equiv> (
    \<exists> l r p s. (l,r) \<in> set P \<and> (r = p@[Tm t]@s) 
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P))
    \<and> (set P' = ((set P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})))"

lemma trans1Tmnl_noeProds:
  assumes "noeProds (set P)"
    and "trans1Tmnl A t P P'"
  shows "noeProds (set P')"
  using assms unfolding trans1Tmnl_def noeProds_def by force

lemma trans1Tmnl_noUnitProds:
  assumes "noUnitProds (set P)"
    and "trans1Tmnl A t P P'"
  shows "noUnitProds (set P')"
proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set P))"
    using assms(1) unfolding noUnitProds_def by simp
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> set P' = ((set P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(2) unfolding trans1Tmnl_def by auto
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A,[Tm t]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set P' = ((set P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})"
    using \<open>?lrps\<close> by simp
  ultimately show ?thesis unfolding noUnitProds_def by simp
qed


definition prodTmnls :: "('n,'t) prod \<Rightarrow> nat" where
  "prodTmnls p = (if length (snd p) \<le> 1 then 0 else length (filter (isTmnlSym) (snd p)))"

definition prodNonTmnls :: "('n,'t) prod \<Rightarrow> nat" where
  "prodNonTmnls p = (if length (snd p) \<le> 2 then 0 else length (filter (isNonTmnlSym) (snd p)))"

definition badTmnlsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badTmnlsCount P = fold (+) (map prodTmnls P) 0"

definition badNtmsCount :: "('n,'t) prods \<Rightarrow> nat" where
  "badNtmsCount P = fold (+) (map prodNonTmnls P) 0"

definition cnf :: "('n,'t) prods \<Rightarrow> bool" where
  "cnf P = ((badTmnlsCount P = 0) \<and> (badNtmsCount P = 0))"

definition trans2Nt :: "'n \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> bool" where
      "trans2Nt A B\<^sub>1 B\<^sub>2 P P' \<equiv> (
    \<exists>l r p s. (l,r) \<in> set P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P))
    \<and> (set P' = ((set P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})))"

lemma trans2Nt_noeProds:
  assumes "noeProds (set P)"
    and "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
  shows "noeProds (set P')"
  using assms unfolding trans2Nt_def noeProds_def by force

lemma trans2Nt_noUnitProds:
  assumes "noUnitProds (set P)"
    and "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
  shows "noUnitProds (set P')"
  proof -
  have 1: "(\<nexists>l A. (l,[Nt A]) \<in> (set P))"
    using assms(1) unfolding noUnitProds_def by simp
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) 
      \<and> (set P' = ((set P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(2) unfolding trans2Nt_def by auto
  hence "\<nexists>l' A'. (l,[Nt A']) \<in> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}" 
    using Cons_eq_append_conv by fastforce
  hence "\<nexists>l' A'. (l',[Nt A']) \<in> ((set P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using 1 by simp
  moreover have "set P' = ((set P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)})"
    using \<open>?lrps\<close> by simp
  ultimately show ?thesis unfolding noUnitProds_def by simp
qed

lemma trans2Nt_aux1:
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
  shows "A \<noteq> B\<^sub>1 \<and> A \<noteq> B\<^sub>2"
  using assms unfolding trans2Nt_def nts_def by auto


lemma cnf_r1Tm: 
  assumes "trans1Tmnl A t P P'"
    and "set P \<turnstile> lhs \<Rightarrow> rhs"
  shows "set P' \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set P" (is "?uv")
    using assms(2) derive.cases by meson
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P))
      \<and> set P' = ((set P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) unfolding trans1Tmnl_def by auto
  thus ?thesis 
  proof (cases "u = l")
    case True
    then show ?thesis
    proof (cases "v = p@[Tm t]@s")
      case True
      have 1: "(set P') \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      have "(set P') \<turnstile> [Nt A] \<Rightarrow> [Tm t]"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      hence "(set P') \<turnstile> [Nt l] \<Rightarrow>* p@[Tm t]@s"
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
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
    and "(set P) \<turnstile> lhs \<Rightarrow> rhs"
  shows "(set P') \<turnstile> lhs \<Rightarrow>* rhs"
proof -
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set P" (is "?uv")
    using assms(2) derive.cases by meson
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P))
    \<and> (set P' = ((set P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) unfolding trans2Nt_def by auto
  thus ?thesis
  proof (cases "u = l")
    case True
    then show ?thesis 
    proof (cases "v = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s")
      case True
      have 1: "set P' \<turnstile> [Nt l] \<Rightarrow> p@[Nt A]@s"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      have "set P' \<turnstile> [Nt A] \<Rightarrow> [Nt B\<^sub>1,Nt B\<^sub>2]"
        using \<open>?lrps\<close> by (simp add: derive_singleton)
      hence "set P' \<turnstile> [Nt l] \<Rightarrow>* p@[Nt B\<^sub>1,Nt B\<^sub>2]@s" 
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

(* p = (A, [Tm t]): Replace the new non-terminal A in rhs by terminal t *)
fun elim :: "('n, 't) prod \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms"  where
  "elim _ [] = []" |
  "elim (A,\<alpha>) (r#rhs) = (if r = Nt A then \<alpha>@(elim (A,\<alpha>) rhs) else r#(elim (A,\<alpha>) rhs))"

(* Does rhs from new grammar G' has any new nonterminals, i.e. ones not in G *)
definition noNewNts :: "('n, 't) prods \<Rightarrow> ('n, 't) sym set \<Rightarrow> bool" where
  "noNewNts P rhS = (\<forall>r. (Nt r \<in> rhS) \<longrightarrow> r \<in> nts (set P))"

lemma slemma1_1: 
  assumes "trans1Tmnl A t P P'"
    and "(A, \<alpha>) \<in> set P'"
  shows "\<alpha> = [Tm t]"
proof -
  have "A \<notin> nts (set P)"
    using assms(1) unfolding trans1Tmnl_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set P"
    unfolding nts_def by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Tm t] \<and> (A, \<alpha>) \<in> set P'"
    using assms(1) unfolding trans1Tmnl_def by auto
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma1_1Nt:
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
    and "(A, \<alpha>) \<in> set P'"
  shows "\<alpha> = [Nt B\<^sub>1,Nt B\<^sub>2]"
proof -
  have "A \<notin> nts (set P)"
    using assms(1) unfolding trans2Nt_def by blast
  hence "\<nexists>\<alpha>. (A, \<alpha>) \<in> set P"
    unfolding nts_def  by auto
  hence "\<nexists>\<alpha>. \<alpha> \<noteq> [Nt B\<^sub>1,Nt B\<^sub>2] \<and> (A, \<alpha>) \<in> set P'"
    using assms(1) unfolding trans2Nt_def by auto
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

lemma nts_correct: "A \<notin> nts P \<Longrightarrow> (\<nexists>S \<alpha>. (S, \<alpha>) \<in> P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>))"
  unfolding nts_def apply (induction rule: nt.induct) apply auto
  by (metis Un_iff case_prod_conv in_set_conv_decomp insertCI nt.simps(2) nt_append)

lemma slemma4_4:
  assumes "trans1Tmnl A t P P'"
    and "(l,r) \<in> set P"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> nts (set P)"
    using assms(1) unfolding trans1Tmnl_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using nts_correct[of A \<open>set P\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed

lemma slemma4_4Nt:
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
    and "(l,r) \<in> set P"
  shows "(Nt A) \<notin> set r"
proof -
  have "A \<notin> nts (set P)"
    using assms(1) unfolding trans2Nt_def by blast
  hence "\<nexists>S \<alpha>. (S, \<alpha>) \<in> set P \<and> (Nt A \<in> {Nt S} \<union> set \<alpha>)"
    using nts_correct[of A \<open>set P\<close>] by blast
  thus ?thesis 
    using assms(2) by blast
qed


lemma lemma1:
  assumes "trans1Tmnl A t P P'"
    and "set P' \<turnstile> lhs \<Rightarrow> rhs"
  shows "(elim (A, [Tm t]) lhs = elim (A, [Tm t]) rhs) \<or> (set P \<turnstile> (elim (A, [Tm t]) lhs) \<Rightarrow> (elim (A, [Tm t]) rhs))"
proof -
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P)) 
      \<and> set P' = ((set P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) unfolding trans1Tmnl_def by auto
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set P'" (is "?uv")
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
      hence 2: "(u, elim (A, [Tm t]) v) \<in> set P" using \<open>?lrps\<close> 
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
      hence 1: "(u, v) \<in> set P" 
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
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
    and "set P' \<turnstile> lhs \<Rightarrow> rhs"
  shows "(elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs) 
          \<or> ((set P) \<turnstile> (elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) lhs) \<Rightarrow> elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) rhs)"
proof -
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P))
    \<and> (set P' = ((set P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) unfolding trans2Nt_def by auto
  obtain p' s' u v where "lhs = p'@[Nt u]@s' \<and> rhs = p'@v@s' \<and> (u,v) \<in> set P'" (is "?uv")
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
        using assms(1) trans2Nt_aux1[of A B\<^sub>1 B\<^sub>2 P P'] by fastforce 
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
        using True \<open>?lrps\<close> \<open>?uv\<close> assms slemma4_4Nt[of A B\<^sub>1 B\<^sub>2 P P'] trans2Nt_aux1[of A B\<^sub>1 B\<^sub>2 P P'] by auto
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v = elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) p @ elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) ([Nt A]@s)"
        using slemma4_0 by fast
      hence "elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v = p @ [Nt B\<^sub>1,Nt B\<^sub>2] @ s"
        using 1 slemma4_0 slemma4_1 slemma4_3_1 by metis
      hence 2: "(u, elim (A, [Nt B\<^sub>1,Nt B\<^sub>2]) v) \<in> set P" 
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
      hence 1: "(u, v) \<in> set P" 
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
  assumes "set P' \<turnstile> lhs \<Rightarrow>* rhs"
    and "trans1Tmnl A t P P'"
  shows "set P \<turnstile> (elim (A, [Tm t]) lhs) \<Rightarrow>* (elim (A, [Tm t]) rhs)"
  using assms
proof (induction)
  case (step y z)
  then show ?case 
    using lemma1[of A t P P' y z] rtranclp.rtrancl_into_rtrancl by fastforce 
qed simp

lemma lemma3Nt:
  assumes "set P' \<turnstile> lhs \<Rightarrow>* rhs"
    and "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
  shows "set P \<turnstile> (elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) lhs) \<Rightarrow>* (elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) rhs)"
  using assms 
proof (induction)
  case (step y z)
  then show ?case 
    using lemma1Nt[of A B\<^sub>1 B\<^sub>2 P P' y z] rtranclp.rtrancl_into_rtrancl by fastforce 
qed simp

lemma slemma4_7: "map Tm w = elim (A, \<alpha>) (map Tm w)"
  by (induction w) auto

lemma slemma4_2: 
  assumes "trans1Tmnl A t P P'"
    and "N \<in> nts (set P)"
  shows "[Nt N] = elim (A, [Tm t]) [Nt N]"
  using assms unfolding trans1Tmnl_def by auto

lemma slemma4_2Nt: 
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
    and "N \<in> nts (set P)"
  shows "[Nt N] = elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) [Nt N]"
  using assms unfolding trans2Nt_def by auto

lemma lemma4:
  assumes "trans1Tmnl A t P P'" 
    and "S \<in> nts (set P)"
  shows "lang P' S \<subseteq> lang P S"
proof 
  fix w
  assume "w \<in> lang P' S"
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    unfolding Lang_def by simp
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding trans1Tmnl_def by auto
  hence "set P \<turnstile> elim (A, [Tm t]) [Nt S] \<Rightarrow>*  elim (A, [Tm t]) (map Tm w)"
    using assms lemma3[of P' \<open>[Nt S]\<close> \<open>map Tm w\<close> A t P] by blast
  moreover have "elim (A, [Tm t]) [Nt S] = [Nt S]"
    using assms unfolding trans1Tmnl_def by auto
  moreover have "elim (A, [Tm t]) (map Tm w) = map Tm w" 
    using \<open>w \<in> lang P' S\<close> slemma4_7 by metis
  ultimately show "w \<in> lang P S" 
    using L_def \<open>w \<in> lang P' S\<close> by (simp add: Lang_def)
qed

lemma lemma4Nt:
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
    and "S \<in> nts (set P)"
  shows "lang P' S \<subseteq> lang P S"
proof
  fix w
  assume "w \<in> lang P' S"
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    by (simp add: Lang_def)
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    using assms unfolding trans2Nt_def by auto
  hence "set P \<turnstile> elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) [Nt S] \<Rightarrow>*  elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) (map Tm w)"
    using assms lemma3Nt[of P' \<open>[Nt S]\<close> \<open>map Tm w\<close> A B\<^sub>1 B\<^sub>2 P] by blast
  moreover have "elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) [Nt S] = [Nt S]"
    using assms unfolding trans2Nt_def by auto 
  moreover have "elim (A, [Nt B\<^sub>1, Nt B\<^sub>2]) (map Tm w) = map Tm w" 
    using \<open>w \<in> lang P' S\<close> slemma4_7 by metis
  ultimately show "w \<in> lang P S" using Lang_def \<open>w \<in> lang P' S\<close> 
    by (metis (no_types, lifting) mem_Collect_eq)
qed

lemma slemma5_1:
  assumes "set P \<turnstile> lhs \<Rightarrow>* rhs"
    and "lhs = [Nt S]"
    and "trans1Tmnl A t P P'"
  shows "set P' \<turnstile> lhs \<Rightarrow>* rhs"
  using assms apply (induction) apply auto by (meson cnf_r1Tm rtranclp_trans)

lemma slemma5_1Nt:
  assumes "set P \<turnstile> lhs \<Rightarrow>* rhs"
    and "lhs = [Nt S]"
    and "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
  shows "set P' \<turnstile> lhs \<Rightarrow>* rhs"
  using assms apply (induction) apply auto by (meson cnf_r1Nt rtranclp_trans)

lemma lemma5: 
  assumes "trans1Tmnl A t P P'"
  shows "lang P S \<subseteq> lang P' S"
proof 
  fix w
  assume "w \<in> lang P S"
  hence "set P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    unfolding Lang_def by simp
  thus "w \<in> lang P' S" 
    using assms slemma5_1 Lang_def by fastforce
qed 

lemma lemma5Nt: 
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'"
  shows "lang P S \<subseteq> lang P' S"
proof 
  fix w
  assume "w \<in> lang P S"
  hence "set P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
    unfolding Lang_def by simp
  thus "w \<in> lang P' S" 
    using assms slemma5_1Nt Lang_def by fast
qed 

lemma cnf_lemma1: 
  assumes "trans1Tmnl A t P P'" "S \<in> nts (set P)"
  shows "lang P S = lang P' S"
  using assms lemma4 lemma5 by fast

lemma cnf_lemma1Nt: 
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'" "S \<in> nts (set P)"
  shows "lang P S = lang P' S"
  using assms lemma4Nt lemma5Nt by fast

definition eqLang :: "('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> 'n \<Rightarrow> bool" where
  "eqLang P P' S \<longleftrightarrow> lang P S = lang P' S"

lemma trans1TmnlRtc_noeProds: 
  assumes "((\<lambda>x y. \<exists>A t. trans1Tmnl A t x y) ^**) P P'"
    and "noeProds (set P)"
  shows "noeProds (set P')"
  using assms by (induction) (auto simp: trans1Tmnl_noeProds)

lemma trans2NtRtc_noeProds:
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. trans2Nt A B\<^sub>1 B\<^sub>2 x y) ^**) P P'"
    and "noeProds (set P)"
  shows "noeProds (set P')"
  using assms by (induction) (auto simp: trans2Nt_noeProds)

lemma trans1TmnlRtc_noUnitProds: 
  assumes "((\<lambda>x y. \<exists>A t. trans1Tmnl A t x y) ^**) P P'"
    and "noUnitProds (set P)"
  shows "noUnitProds (set P')"
  using assms by (induction) (auto simp: trans1Tmnl_noUnitProds)

lemma trans2NtRtc_noUnitProds:
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. trans2Nt A B\<^sub>1 B\<^sub>2 x y) ^**) P P'"
    and "noUnitProds (set P)"
  shows "noUnitProds (set P')"
  using assms by (induction) (auto simp: trans2Nt_noUnitProds)

(* proofs about nts and an arbitrary start Symbol S *)

lemma nts_aux1: "nts (P \<union> P') = nts P \<union> nts P'"
  unfolding nts_def by simp

lemma trans1Tmnl_nts: 
  assumes "trans1Tmnl A t P P'" "S \<in> nts (set P)"
  shows "S \<in> nts (set P')"
proof -
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Tm t]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P)) 
      \<and> set P' = ((set P - {(l,r)}) \<union> {(A,[Tm t]), (l, p@[Nt A]@s)})" (is "?lrps")
    using assms(1) unfolding trans1Tmnl_def by auto
  thus ?thesis
  proof (cases "S \<in> nts {(l,r)}")
    case True
    hence "S \<in> nts {(A,[Tm t]), (l, p@[Nt A]@s)}"
      unfolding nts_def using \<open>?lrps\<close> by auto
    then show ?thesis using  \<open>?lrps\<close> nts_aux1 by (metis UnCI)
  next
    case False
    hence "S \<in> nts (set P - {(l,r)})"
      unfolding nts_def using \<open>?lrps\<close> 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) nts_aux1 nts_def)
    then show ?thesis 
      by (simp add: \<open>?lrps\<close> nts_def)
  qed
qed  

lemma trans1TmnlRtc_nts: 
  assumes "((\<lambda>x y. \<exists>A t. trans1Tmnl A t x y) ^**) P P'" "S \<in> nts (set P)"
  shows "S \<in> nts (set P')"
  using assms by (induction rule: rtranclp.induct) (auto simp: trans1Tmnl_nts)

lemma trans2Nt_nts: 
  assumes "trans2Nt A B\<^sub>1 B\<^sub>2 P P'" "S \<in> nts (set P)"
  shows "S \<in> nts (set P')"
proof -
  obtain l r p s where "(l,r) \<in> set P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s) \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A \<notin> nts (set P))
    \<and> (set P' = ((set P - {(l,r)}) \<union> {(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}))" (is "?lrps")
    using assms(1) unfolding trans2Nt_def by auto
    thus ?thesis
  proof (cases "S \<in> nts {(l,r)}")
    case True
    hence "S \<in> nts {(A,[Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)}"
      unfolding nts_def using \<open>?lrps\<close> by auto
    then show ?thesis 
      using  \<open>?lrps\<close> nts_aux1 by (metis UnCI)
  next
    case False
    hence "S \<in> nts (set P - {(l,r)})"
      unfolding nts_def using \<open>?lrps\<close> 
      by (metis UnCI UnE Un_Diff_cancel2 assms(2) nts_aux1 nts_def)
    then show ?thesis 
      by (simp add: \<open>?lrps\<close> nts_def)
  qed
qed  

lemma trans2NtRtc_nts: 
  assumes "((\<lambda>x y. \<exists>A t B\<^sub>1 B\<^sub>2. trans2Nt A B\<^sub>1 B\<^sub>2 x y) ^**) P P'" "S \<in> nts (set P)"
  shows "S \<in> nts (set P')"
  using assms by (induction rule: rtranclp.induct) (auto simp: trans2Nt_nts)

(* Termination for an arbitrary start Symbol S *)

theorem cnf_lemma2: 
  assumes "((\<lambda>x y. \<exists>A t. trans1Tmnl A t x y) ^**) P P'" "S \<in> nts (set P)" 
  shows "(lang P S = lang P' S)"
  using assms by (induction rule: rtranclp.induct) (fastforce simp: cnf_lemma1 trans1TmnlRtc_nts)+

theorem cnf_lemma2Nt: 
  assumes "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. trans2Nt A B\<^sub>1 B\<^sub>2 x y) ^**) P P'" "S \<in> nts (set P)" 
  shows "(lang P S = lang P' S)"
  using assms by (induction rule: rtranclp.induct) (fastforce simp: cnf_lemma1Nt trans2NtRtc_nts)+

theorem cnf_lemma: 
  assumes "((\<lambda>x y. \<exists>A t. trans1Tmnl A t x y) ^**) P P'"
    and "((\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. trans2Nt A B\<^sub>1 B\<^sub>2 x y) ^**) P' P''"
    and "S \<in> nts (set P)"
  shows "lang P S = lang P'' S"
  using assms cnf_lemma2 cnf_lemma2Nt trans1TmnlRtc_nts by fastforce

(* Part 2 *)

lemma lemam16_b:
  assumes "badTmnlsCount P = 0"
    and "r \<in> set P"
  shows "prodTmnls r = 0 "
  using assms unfolding badTmnlsCount_def
  by (simp add: fold_plus_sum_list_rev) 

theorem trans1Tmnl_2: 
  assumes "infinite(UNIV::'a set)"
  shows "\<exists>P'. ((\<lambda>x y. \<exists>A t. trans1Tmnl A t x y) ^**) P P' \<and> (badTmnlsCount P' = 0)"
proof (induction "badTmnlsCount P")
  case 0
  then show ?case by auto
next
  case (Suc x)
  then show ?case sorry
qed


definition "isCnf P \<equiv> (\<forall>l r. (l,r) \<in> set P \<longrightarrow> (
    (length r = 2 \<and> list_all (isNonTmnlSym) r) \<or> 
    (length r = 1 \<and> list_all (isTmnlSym) r)))"


theorem cnf_trans: "\<forall>P. infinite(UNIV::'a set) \<and> [] \<notin> lang P S \<Longrightarrow> \<exists>P'. isCnf P'" 
  sorry
end