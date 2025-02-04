theory uProds
  imports eProds
begin

(* Rules of the form A\<rightarrow>B, where A and B are in nonterminals P *)
definition unit_prods :: "('n,'t) prods \<Rightarrow> ('n,'t) Prods" where
  "unit_prods P = {(l,r) \<in> set P. \<exists>A. r = [Nt A]}"

(* A \<Rightarrow>* B where A and B are in nonTerminals g *)
definition rec_unit_prods :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) set" where
  "rec_unit_prods P = {(a,b). P \<turnstile> [Nt a] \<Rightarrow>* [Nt b] \<and> {a,b} \<subseteq> Nts P}"

definition unit_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
  "unit_elim P = (set P - (unit_prods P))"

definition new_prods :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where 
  "new_prods P = {(a,r). \<exists>b. (b,r) \<in> (unit_elim P) \<and> (a, b) \<in> rec_unit_prods (unit_prods P)}"

definition \<U>_rules :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
  "\<U>_rules P = (unit_elim P \<union> new_prods P)"

definition \<U> :: "('n, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> bool" where
  "\<U> P P' = (set P' = \<U>_rules P)"

(* Proofs *)
(* Finiteness & Existence *)

(* finiteness unit_prods which also implies finiteness for unit_elim *)
fun uprods :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "uprods [] = []" |
  "uprods (p#ps) = (if \<exists>A. (snd p) = [Nt A] then p#uprods ps else uprods ps)"

lemma unit_prods_uprods: "set (uprods P) = unit_prods P"
  unfolding unit_prods_def by (induction P) auto

lemma finiteunit_prods: "finite (unit_prods P)"
  using unit_prods_uprods by (metis List.finite_set)

(* finiteness for rec_unit_prods *)
definition NtsCross :: "('n, 't) Prods  \<Rightarrow> ('n \<times> 'n) set" where
  "NtsCross P = {(A, B). A \<in> Nts P \<and> B \<in> Nts P }"

lemma finiterec_unit_prods: 
  assumes "finite P" 
  shows  "finite (rec_unit_prods P)"
proof -
  have "finite (Nts P)"
    unfolding Nts_def using assms finite_nts_of_syms by auto
  hence "finite (NtsCross P)"
    unfolding NtsCross_def by auto
  moreover have "rec_unit_prods P \<subseteq> NtsCross P"
    unfolding rec_unit_prods_def NtsCross_def by blast
  ultimately show ?thesis
    using assms infinite_super by fastforce 
qed

(* finiteness for new_prods *)
definition nPlambda :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) \<Rightarrow> ('n, 't) Prods" where
  "nPlambda P d = {fst d} \<times> {r. (snd d, r) \<in> P}"

lemma nPImage: "\<Union>((nPlambda (unit_elim P)) ` (rec_unit_prods (unit_prods P))) = new_prods P"
  unfolding new_prods_def nPlambda_def by fastforce

lemma finitenPlambda:
  assumes "finite P" 
  shows "finite (nPlambda P d)"
proof -
  have "{(B, r). (B, r) \<in> P \<and> B = snd d} \<subseteq> P" 
    by blast
  hence "finite {(B, r). (B, r) \<in> P \<and> B = snd d}"
    using assms finite_subset by blast
  hence "finite (snd ` {(B, r). (B, r) \<in> P \<and> B = snd d})" 
    by simp
  moreover have "{r. (snd d, r) \<in> P} = (snd ` {(B, r). (B, r) \<in> P \<and> B = snd d})"
    by force
  ultimately show ?thesis
    using assms unfolding nPlambda_def by simp
qed

lemma finitenew_prods: "finite (new_prods P)"
proof -
  have "finite (unit_elim P)"
    unfolding unit_elim_def using finiteunit_prods by blast
  moreover have "finite (rec_unit_prods (unit_prods P))"
    using finiteunit_prods finiterec_unit_prods by blast
  ultimately show ?thesis
    using nPImage finitenPlambda finite_UN by metis
qed

(* finiteness \<U>_rules *)
lemma finite\<U>Rules: "finite (\<U>_rules P)"
proof -
  have "finite (unit_elim P)"
    unfolding unit_elim_def using finiteunit_prods by blast
  moreover have "finite (new_prods P)"
    using finitenew_prods by blast
  ultimately show ?thesis
    unfolding \<U>_rules_def by blast
qed

(* \<U> Existence *)
lemma \<U>_exists: "\<forall>P. \<exists>P'. \<U> P P'"
  unfolding \<U>_def using finite\<U>Rules finite_list by blast

(* towards theorem 4.4 *)

lemma inNonUnitProds:
  "p \<in> unit_elim P \<Longrightarrow> p \<in> set P"
  unfolding unit_elim_def by blast

lemma psubDeriv:
  assumes "P \<turnstile> u \<Rightarrow> v"
    and "\<forall>p \<in> P. p \<in> P'"
  shows "P' \<turnstile> u \<Rightarrow> v"
  using assms by (meson derive_iff)

lemma psubRtcDeriv:
  assumes "P \<turnstile> u \<Rightarrow>* v"
    and "\<forall>p \<in> P. p \<in> P'"
  shows "P' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: psubDeriv rtranclp.rtrancl_into_rtrancl)

lemma unit_prods_deriv: 
  assumes "unit_prods P \<turnstile> u \<Rightarrow>* v"
  shows "set P \<turnstile> u \<Rightarrow>* v"
proof -
  have "\<forall>p \<in> unit_prods P. p \<in> set P"
    unfolding unit_prods_def by blast
  thus ?thesis 
    using assms psubRtcDeriv by blast
qed

lemma \<U>_r3:
  assumes "\<U> P P'"
    and "set P' \<turnstile> u \<Rightarrow> v"
  shows "set P \<turnstile> u \<Rightarrow>* v"
proof -
  obtain A \<alpha> r1 r2 where "(A, \<alpha>) \<in> set P' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2" (is "?A")
    using assms derive.cases by meson
  hence "(A, \<alpha>) \<in> unit_elim P \<or> (A, \<alpha>) \<in> new_prods P"
    using assms(1) unfolding \<U>_def \<U>_rules_def by simp
  thus ?thesis
  proof
    assume "(A, \<alpha>) \<in> unit_elim P"
    hence "(A, \<alpha>) \<in> set P"
      using inNonUnitProds by blast
    hence "set P \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis using \<open>?A\<close> by simp
  next 
    assume "(A, \<alpha>) \<in> new_prods P"
    from this obtain B where "(B, \<alpha>) \<in> unit_elim P \<and> (A, B) \<in> rec_unit_prods (unit_prods P)" (is "?B")
      unfolding new_prods_def by blast
    hence "unit_prods P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      unfolding rec_unit_prods_def by simp
    hence "set P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      using unit_prods_deriv by blast
    hence 1: "set P \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow>* r1 @ [Nt B] @ r2"
      using derives_append derives_prepend by blast
    have "(B, \<alpha>) \<in> set P"
      using \<open>?B\<close> inNonUnitProds by blast
    hence "set P \<turnstile> r1 @ [Nt B] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis 
      using 1 \<open>?A\<close> by simp
  qed
qed

lemma \<U>_r4: 
  assumes "set P' \<turnstile> u \<Rightarrow>* v"
    and "\<U> P P'"
  shows "set P \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: \<U>_r3 rtranclp_trans)

lemma deriv_rec_unit_prods:
  assumes "set P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "(A, B) \<in> rec_unit_prods (unit_prods P)"
proof -
  have "(A, [Nt B]) \<in> set P"
    using assms by (simp add: derive_singleton)
  hence "(A, [Nt B]) \<in> unit_prods P"
    unfolding unit_prods_def by blast
  hence "unit_prods P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
    by (simp add: derive_singleton)
  moreover have "B \<in> Nts (unit_prods P) \<and> A \<in> Nts (unit_prods P)"
    using \<open>(A, [Nt B]) \<in> unit_prods P\<close> Nts_def nts_of_syms_def by fastforce
  ultimately show ?thesis
    unfolding rec_unit_prods_def by blast
qed

lemma \<U>_r12: 
  assumes "\<U> P P'" "(A, \<alpha>) \<in> set P'"
  shows "(A, \<alpha>) \<notin> unit_prods P"
  using assms unfolding \<U>_def \<U>_rules_def unit_elim_def unit_prods_def new_prods_def by blast

lemma \<U>_r14: 
  assumes "\<U> P P'" 
    and "set P \<turnstile> [Nt A] \<Rightarrow> [Nt B]" "set P' \<turnstile> [Nt B] \<Rightarrow> v"
  shows "set P' \<turnstile> [Nt A] \<Rightarrow> v"
proof -
  have 1: "(A, B) \<in> rec_unit_prods (unit_prods P)"
    using deriv_rec_unit_prods assms(2) by fast
  have 2: "(B, v) \<in> set P'"
    using assms(3) by (simp add: derive_singleton)
  thus ?thesis
  proof (cases "(B, v) \<in> set P")
    case True
    hence "(B, v) \<in> unit_elim P"
      unfolding unit_elim_def using assms(1) assms(3) \<U>_r12[of P P' B v] by (simp add: derive_singleton)
    then show ?thesis
    using 1 assms(1) unfolding \<U>_def \<U>_rules_def new_prods_def derive_singleton by blast
  next
    case False
    hence "(B, v) \<in> new_prods P"
      using assms(1) 2 unfolding unit_elim_def \<U>_def \<U>_rules_def by simp
    from this obtain C where "(C, v) \<in> unit_elim P \<and> (B, C) \<in> rec_unit_prods (unit_prods P)" (is "?C")
      unfolding new_prods_def by blast
    hence "unit_prods P \<turnstile> [Nt A] \<Rightarrow>* [Nt C]"
      using 1 unfolding rec_unit_prods_def by auto
    hence "(A, C) \<in> rec_unit_prods (unit_prods P)"
      unfolding rec_unit_prods_def using "1" \<open>?C\<close> rec_unit_prods_def by fastforce
    hence "(A, v) \<in> new_prods P"
      unfolding new_prods_def using \<open>?C\<close> by blast
    hence "(A, v) \<in> set P'"
      using assms(1) unfolding \<U>_def \<U>_rules_def by blast
    thus ?thesis by (simp add: derive_singleton)
  qed
qed

lemma \<U>_r20_aux:
  assumes "set P \<turnstile> l @ [Nt A] @ r \<Rightarrow>* v" "\<forall>a \<in> set v. \<exists>t. a = Tm t"
  shows "\<exists>\<alpha>. set P \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ \<alpha> @ r \<and> set P \<turnstile> l @ \<alpha> @ r \<Rightarrow>* v \<and> (A, \<alpha>) \<in> set P"
proof -
  obtain l' w r' where "set P \<turnstile> l \<Rightarrow>* l'  \<and> set P \<turnstile> [Nt A] \<Rightarrow>* w \<and>  set P \<turnstile> r \<Rightarrow>* r' \<and> v = l' @ w @ r'" (is "?w")
    using assms(1) by (metis derives_append_decomp)
  have "Nt A \<notin> set v" 
    using assms(2) by blast
  hence "[Nt A] \<noteq> w" 
    using \<open>?w\<close> by auto
  from this obtain \<alpha> where "set P \<turnstile> [Nt A] \<Rightarrow> \<alpha> \<and> set P \<turnstile> \<alpha> \<Rightarrow>* w" (is "?\<alpha>")
    by (metis \<open>?w\<close> converse_rtranclpE)
  hence "(A, \<alpha>) \<in> set P" 
    by (simp add: derive_singleton)
  thus ?thesis by (metis \<open>?\<alpha>\<close> \<open>?w\<close> derive.intros derives_append_decomp) 
qed

lemma \<U>_r20: 
  assumes "set P \<turnstile> u \<Rightarrow>* v"
    and "\<U> P P'" "\<forall>a \<in> set v. \<exists>t. a = Tm t"
  shows "set P' \<turnstile> u \<Rightarrow>* v"
  using assms proof (induction rule: derives_induct')
  case base
  then show ?case by blast
next
  case (step l A r w)
  then show ?case 
  proof (cases "(A, w) \<in> unit_prods P")
    case True
    from this obtain B where "w = [Nt B]" (is "?B")
      unfolding unit_prods_def by blast
    have "set P' \<turnstile> l @ w @ r \<Rightarrow>* v \<and> Nt B \<notin> set v"
      using step.IH assms(2) assms(3) by blast
    obtain \<alpha> where "set P' \<turnstile> l @ [Nt B] @ r \<Rightarrow> l @ \<alpha> @ r \<and> set P' \<turnstile> l @ \<alpha> @ r \<Rightarrow>* v \<and> (B, \<alpha>) \<in> set P'" (is "?\<alpha>")
      using assms(2) assms(3) step.IH \<open>?B\<close>  \<U>_r20_aux[of P' l B r v] by blast
    hence "(A, \<alpha>) \<in> set P'"
      using assms(2) step.hyps(2) \<open>?B\<close> \<U>_r14[of P P' A B \<alpha>] by (simp add: derive_singleton)
    hence "set P' \<turnstile> l @ [Nt A] @ r \<Rightarrow>* l @ \<alpha> @ r"
      using derive.simps by fastforce
    then show ?thesis 
      using \<open>?\<alpha>\<close> by auto
  next
    case False
    hence "(A, w) \<in> unit_elim P"
      unfolding unit_elim_def using step.hyps(2) by blast
    hence "(A, w) \<in> set P'"
      using assms(2) unfolding \<U>_def \<U>_rules_def by simp
    hence "set P' \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ w @ r"
      by (auto simp: derive.simps)
    then show ?thesis
      using step by simp
  qed
qed

theorem \<U>_lang_eq: 
  assumes "\<U> P P'"
  shows "lang P S = lang P' S"
  unfolding Lang_def using assms \<U>_r4 \<U>_r20 ex_map_conv by meson

theorem \<N>_\<U>_lang_eq:
  assumes "\<N> P P\<^sub>0"
    and "\<U> P\<^sub>0 P'"
  shows "lang P' S = lang P\<^sub>0 S - {[]}"
  using assms \<N>_lang_eq[of P P\<^sub>0 S] \<U>_lang_eq[of P\<^sub>0 P' S] by blast

unused_thms
end