theory uProds
  imports eProds
begin

(* Rules of the form A\<rightarrow>B, where A and B are in nonterminals ps *)
definition unit_prods :: "('n,'t) prods \<Rightarrow> ('n,'t) Prods" where
  "unit_prods ps = {(l,r) \<in> set ps. \<exists>A. r = [Nt A]}"

(* A \<Rightarrow>* B where A and B are in nonTerminals g *)
definition rec_unit_prods :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) set" where
  "rec_unit_prods Ps = {(a,b). Ps \<turnstile> [Nt a] \<Rightarrow>* [Nt b] \<and> {a,b} \<subseteq> Nts Ps}"

definition unit_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
  "unit_elim ps = (set ps - (unit_prods ps))"

definition new_prods :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where 
  "new_prods ps = {(a,r). \<exists>b. (b,r) \<in> (unit_elim ps) \<and> (a, b) \<in> rec_unit_prods (unit_prods ps)}"

definition \<U>_rules :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
  "\<U>_rules ps = (unit_elim ps \<union> new_prods ps)"

definition \<U> :: "('n, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> bool" where
  "\<U> ps ps' = (set ps' = \<U>_rules ps)"

(* psroofs *)
(* Finiteness & Existence *)

(* finiteness unit_prods which also implies finiteness for unit_elim *)
fun uprods :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "uprods [] = []" |
  "uprods (p#ps) = (if \<exists>A. (snd p) = [Nt A] then p#uprods ps else uprods ps)"

lemma unit_prods_uprods: "set (uprods ps) = unit_prods ps"
  unfolding unit_prods_def by (induction ps) auto

lemma finiteunit_prods: "finite (unit_prods ps)"
  using unit_prods_uprods by (metis List.finite_set)

(* finiteness for rec_unit_prods *)
definition NtsCross :: "('n, 't) Prods  \<Rightarrow> ('n \<times> 'n) set" where
  "NtsCross Ps = {(A, B). A \<in> Nts Ps \<and> B \<in> Nts Ps }"

lemma finiterec_unit_prods: 
  assumes "finite ps" 
  shows  "finite (rec_unit_prods ps)"
proof -
  have "finite (Nts ps)"
    unfolding Nts_def using assms finite_nts_of_syms by auto
  hence "finite (NtsCross ps)"
    unfolding NtsCross_def by auto
  moreover have "rec_unit_prods ps \<subseteq> NtsCross ps"
    unfolding rec_unit_prods_def NtsCross_def by blast
  ultimately show ?thesis
    using assms infinite_super by fastforce 
qed

(* finiteness for new_prods *)
definition npslambda :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) \<Rightarrow> ('n, 't) Prods" where
  "npslambda ps d = {fst d} \<times> {r. (snd d, r) \<in> ps}"

lemma npsImage: "\<Union>((npslambda (unit_elim ps)) ` (rec_unit_prods (unit_prods ps))) = new_prods ps"
  unfolding new_prods_def npslambda_def by fastforce

lemma finitenpslambda:
  assumes "finite ps" 
  shows "finite (npslambda ps d)"
proof -
  have "{(B, r). (B, r) \<in> ps \<and> B = snd d} \<subseteq> ps" 
    by blast
  hence "finite {(B, r). (B, r) \<in> ps \<and> B = snd d}"
    using assms finite_subset by blast
  hence "finite (snd ` {(B, r). (B, r) \<in> ps \<and> B = snd d})" 
    by simp
  moreover have "{r. (snd d, r) \<in> ps} = (snd ` {(B, r). (B, r) \<in> ps \<and> B = snd d})"
    by force
  ultimately show ?thesis
    using assms unfolding npslambda_def by simp
qed

lemma finitenew_prods: "finite (new_prods ps)"
proof -
  have "finite (unit_elim ps)"
    unfolding unit_elim_def using finiteunit_prods by blast
  moreover have "finite (rec_unit_prods (unit_prods ps))"
    using finiteunit_prods finiterec_unit_prods by blast
  ultimately show ?thesis
    using npsImage finitenpslambda finite_UN by metis
qed

(* finiteness \<U>_rules *)
lemma finite\<U>Rules: "finite (\<U>_rules ps)"
proof -
  have "finite (unit_elim ps)"
    unfolding unit_elim_def using finiteunit_prods by blast
  moreover have "finite (new_prods ps)"
    using finitenew_prods by blast
  ultimately show ?thesis
    unfolding \<U>_rules_def by blast
qed

(* \<U> Existence *)
lemma \<U>_exists: "\<forall>ps. \<exists>ps'. \<U> ps ps'"
  unfolding \<U>_def using finite\<U>Rules finite_list by blast

(* towards theorem 4.4 *)

lemma inNonUnitProds:
  "p \<in> unit_elim ps \<Longrightarrow> p \<in> set ps"
  unfolding unit_elim_def by blast

lemma psubDeriv:
  assumes "ps \<turnstile> u \<Rightarrow> v"
    and "\<forall>p \<in> ps. p \<in> ps'"
  shows "ps' \<turnstile> u \<Rightarrow> v"
  using assms by (meson derive_iff)

lemma psubRtcDeriv:
  assumes "ps \<turnstile> u \<Rightarrow>* v"
    and "\<forall>p \<in> ps. p \<in> ps'"
  shows "ps' \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: psubDeriv rtranclp.rtrancl_into_rtrancl)

lemma unit_prods_deriv: 
  assumes "unit_prods ps \<turnstile> u \<Rightarrow>* v"
  shows "set ps \<turnstile> u \<Rightarrow>* v"
proof -
  have "\<forall>p \<in> unit_prods ps. p \<in> set ps"
    unfolding unit_prods_def by blast
  thus ?thesis 
    using assms psubRtcDeriv by blast
qed

lemma \<U>_r3:
  assumes "\<U> ps ps'"
    and "set ps' \<turnstile> u \<Rightarrow> v"
  shows "set ps \<turnstile> u \<Rightarrow>* v"
proof -
  obtain A \<alpha> r1 r2 where "(A, \<alpha>) \<in> set ps' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2" (is "?A")
    using assms derive.cases by meson
  hence "(A, \<alpha>) \<in> unit_elim ps \<or> (A, \<alpha>) \<in> new_prods ps"
    using assms(1) unfolding \<U>_def \<U>_rules_def by simp
  thus ?thesis
  proof
    assume "(A, \<alpha>) \<in> unit_elim ps"
    hence "(A, \<alpha>) \<in> set ps"
      using inNonUnitProds by blast
    hence "set ps \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis using \<open>?A\<close> by simp
  next 
    assume "(A, \<alpha>) \<in> new_prods ps"
    from this obtain B where "(B, \<alpha>) \<in> unit_elim ps \<and> (A, B) \<in> rec_unit_prods (unit_prods ps)" (is "?B")
      unfolding new_prods_def by blast
    hence "unit_prods ps \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      unfolding rec_unit_prods_def by simp
    hence "set ps \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      using unit_prods_deriv by blast
    hence 1: "set ps \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow>* r1 @ [Nt B] @ r2"
      using derives_append derives_prepend by blast
    have "(B, \<alpha>) \<in> set ps"
      using \<open>?B\<close> inNonUnitProds by blast
    hence "set ps \<turnstile> r1 @ [Nt B] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis 
      using 1 \<open>?A\<close> by simp
  qed
qed

lemma \<U>_r4: 
  assumes "set ps' \<turnstile> u \<Rightarrow>* v"
    and "\<U> ps ps'"
  shows "set ps \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: \<U>_r3 rtranclp_trans)

lemma deriv_rec_unit_prods:
  assumes "set ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "(A, B) \<in> rec_unit_prods (unit_prods ps)"
proof -
  have "(A, [Nt B]) \<in> set ps"
    using assms by (simp add: derive_singleton)
  hence "(A, [Nt B]) \<in> unit_prods ps"
    unfolding unit_prods_def by blast
  hence "unit_prods ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
    by (simp add: derive_singleton)
  moreover have "B \<in> Nts (unit_prods ps) \<and> A \<in> Nts (unit_prods ps)"
    using \<open>(A, [Nt B]) \<in> unit_prods ps\<close> Nts_def nts_of_syms_def by fastforce
  ultimately show ?thesis
    unfolding rec_unit_prods_def by blast
qed

lemma \<U>_r12: 
  assumes "\<U> ps ps'" "(A, \<alpha>) \<in> set ps'"
  shows "(A, \<alpha>) \<notin> unit_prods ps"
  using assms unfolding \<U>_def \<U>_rules_def unit_elim_def unit_prods_def new_prods_def by blast

lemma \<U>_r14: 
  assumes "\<U> ps ps'" 
    and "set ps \<turnstile> [Nt A] \<Rightarrow> [Nt B]" "set ps' \<turnstile> [Nt B] \<Rightarrow> v"
  shows "set ps' \<turnstile> [Nt A] \<Rightarrow> v"
proof -
  have 1: "(A, B) \<in> rec_unit_prods (unit_prods ps)"
    using deriv_rec_unit_prods assms(2) by fast
  have 2: "(B, v) \<in> set ps'"
    using assms(3) by (simp add: derive_singleton)
  thus ?thesis
  proof (cases "(B, v) \<in> set ps")
    case True
    hence "(B, v) \<in> unit_elim ps"
      unfolding unit_elim_def using assms(1) assms(3) \<U>_r12[of ps ps' B v] by (simp add: derive_singleton)
    then show ?thesis
    using 1 assms(1) unfolding \<U>_def \<U>_rules_def new_prods_def derive_singleton by blast
  next
    case False
    hence "(B, v) \<in> new_prods ps"
      using assms(1) 2 unfolding unit_elim_def \<U>_def \<U>_rules_def by simp
    from this obtain C where "(C, v) \<in> unit_elim ps \<and> (B, C) \<in> rec_unit_prods (unit_prods ps)" (is "?C")
      unfolding new_prods_def by blast
    hence "unit_prods ps \<turnstile> [Nt A] \<Rightarrow>* [Nt C]"
      using 1 unfolding rec_unit_prods_def by auto
    hence "(A, C) \<in> rec_unit_prods (unit_prods ps)"
      unfolding rec_unit_prods_def using "1" \<open>?C\<close> rec_unit_prods_def by fastforce
    hence "(A, v) \<in> new_prods ps"
      unfolding new_prods_def using \<open>?C\<close> by blast
    hence "(A, v) \<in> set ps'"
      using assms(1) unfolding \<U>_def \<U>_rules_def by blast
    thus ?thesis by (simp add: derive_singleton)
  qed
qed

lemma \<U>_r20_aux:
  assumes "set ps \<turnstile> l @ [Nt A] @ r \<Rightarrow>* v" "\<forall>a \<in> set v. \<exists>t. a = Tm t"
  shows "\<exists>\<alpha>. set ps \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ \<alpha> @ r \<and> set ps \<turnstile> l @ \<alpha> @ r \<Rightarrow>* v \<and> (A, \<alpha>) \<in> set ps"
proof -
  obtain l' w r' where "set ps \<turnstile> l \<Rightarrow>* l'  \<and> set ps \<turnstile> [Nt A] \<Rightarrow>* w \<and>  set ps \<turnstile> r \<Rightarrow>* r' \<and> v = l' @ w @ r'" (is "?w")
    using assms(1) by (metis derives_append_decomp)
  have "Nt A \<notin> set v" 
    using assms(2) by blast
  hence "[Nt A] \<noteq> w" 
    using \<open>?w\<close> by auto
  from this obtain \<alpha> where "set ps \<turnstile> [Nt A] \<Rightarrow> \<alpha> \<and> set ps \<turnstile> \<alpha> \<Rightarrow>* w" (is "?\<alpha>")
    by (metis \<open>?w\<close> converse_rtranclpE)
  hence "(A, \<alpha>) \<in> set ps" 
    by (simp add: derive_singleton)
  thus ?thesis by (metis \<open>?\<alpha>\<close> \<open>?w\<close> derive.intros derives_append_decomp) 
qed

lemma \<U>_r20: 
  assumes "set ps \<turnstile> u \<Rightarrow>* v"
    and "\<U> ps ps'" "\<forall>a \<in> set v. \<exists>t. a = Tm t"
  shows "set ps' \<turnstile> u \<Rightarrow>* v"
  using assms proof (induction rule: derives_induct')
  case base
  then show ?case by blast
next
  case (step l A r w)
  then show ?case 
  proof (cases "(A, w) \<in> unit_prods ps")
    case True
    from this obtain B where "w = [Nt B]" (is "?B")
      unfolding unit_prods_def by blast
    have "set ps' \<turnstile> l @ w @ r \<Rightarrow>* v \<and> Nt B \<notin> set v"
      using step.IH assms(2) assms(3) by blast
    obtain \<alpha> where "set ps' \<turnstile> l @ [Nt B] @ r \<Rightarrow> l @ \<alpha> @ r \<and> set ps' \<turnstile> l @ \<alpha> @ r \<Rightarrow>* v \<and> (B, \<alpha>) \<in> set ps'" (is "?\<alpha>")
      using assms(2) assms(3) step.IH \<open>?B\<close>  \<U>_r20_aux[of ps' l B r v] by blast
    hence "(A, \<alpha>) \<in> set ps'"
      using assms(2) step.hyps(2) \<open>?B\<close> \<U>_r14[of ps ps' A B \<alpha>] by (simp add: derive_singleton)
    hence "set ps' \<turnstile> l @ [Nt A] @ r \<Rightarrow>* l @ \<alpha> @ r"
      using derive.simps by fastforce
    then show ?thesis 
      using \<open>?\<alpha>\<close> by auto
  next
    case False
    hence "(A, w) \<in> unit_elim ps"
      unfolding unit_elim_def using step.hyps(2) by blast
    hence "(A, w) \<in> set ps'"
      using assms(2) unfolding \<U>_def \<U>_rules_def by simp
    hence "set ps' \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ w @ r"
      by (auto simp: derive.simps)
    then show ?thesis
      using step by simp
  qed
qed

theorem \<U>_lang_eq: 
  assumes "\<U> ps ps'"
  shows "lang ps S = lang ps' S"
  unfolding Lang_def using assms \<U>_r4 \<U>_r20 ex_map_conv by meson

theorem \<N>_\<U>_lang_eq:
  assumes "\<N> ps ps\<^sub>0"
    and "\<U> ps\<^sub>0 ps'"
  shows "lang ps' S = lang ps\<^sub>0 S - {[]}"
  using assms \<N>_lang_eq[of ps ps\<^sub>0 S] \<U>_lang_eq[of ps\<^sub>0 ps' S] by blast

unused_thms
end