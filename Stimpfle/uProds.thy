theory uProds
  imports eProds
begin

(* Rules of the form A\<rightarrow>B, where A and B are in nonterminals P *)
definition unitProds :: "('n,'t) prods \<Rightarrow> ('n,'t) Prods" where
  "unitProds P = {(l,r) \<in> set P. \<exists>A. r = [Nt A]}"

(* A \<Rightarrow>* B where A and B are in nonTerminals g *)
definition allDepS :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) set" where
  "allDepS P = {(a,b). P \<turnstile> [Nt a] \<Rightarrow>* [Nt b] \<and> a \<in> Nts P \<and> b \<in> Nts P}"

definition nonUnitProds :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
  "nonUnitProds P = (set P - (unitProds P))"

definition newProds :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where 
  "newProds P = {(a,r). \<exists>b. (b,r) \<in> (nonUnitProds P) \<and> (a, b) \<in> allDepS (unitProds P)}"

definition uppr_rules :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
  "uppr_rules P = (nonUnitProds P \<union> newProds P)"

definition uppr :: "('n, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> bool" where
  "uppr P P' = (set P' = uppr_rules P)"

(* Proofs *)
(* Finiteness & Existence *)

(* finiteness unitProds which also implies finiteness for nonUnitProds *)
fun uprods :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "uprods [] = []" |
  "uprods (p#ps) = (if \<exists>A. (snd p) = [Nt A] then p#uprods ps else uprods ps)"

lemma unitProds_uprods: "set (uprods P) = unitProds P"
  unfolding unitProds_def by (induction P) auto

lemma finiteunitProds: "finite (unitProds P)"
  using unitProds_uprods by (metis List.finite_set)

(* finiteness for allDepS *)
definition NtsCross :: "('n, 't) Prods  \<Rightarrow> ('n \<times> 'n) set" where
  "NtsCross P = {(A, B). A \<in> Nts P \<and> B \<in> Nts P }"

lemma finiteallDepS: 
  assumes "finite P" 
  shows  "finite (allDepS P)"
proof -
  have "finite (Nts P)"
    unfolding Nts_def using assms finite_nts_of_syms by auto
  hence "finite (NtsCross P)"
    unfolding NtsCross_def by auto
  moreover have "allDepS P \<subseteq> NtsCross P"
    unfolding allDepS_def NtsCross_def by blast
  ultimately show ?thesis
    using assms infinite_super by fastforce 
qed

(* finiteness for newProds *)
definition nPlambda :: "('n, 't) Prods \<Rightarrow> ('n \<times> 'n) \<Rightarrow> ('n, 't) Prods" where
  "nPlambda P d = {fst d} \<times> {r. (snd d, r) \<in> P}"

lemma nPImage: "\<Union>((nPlambda (nonUnitProds P)) ` (allDepS (unitProds P))) = newProds P"
  unfolding newProds_def nPlambda_def by fastforce

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

lemma finitenewProds: "finite (newProds P)"
proof -
  have "finite (nonUnitProds P)"
    unfolding nonUnitProds_def using finiteunitProds by blast
  moreover have "finite (allDepS (unitProds P))"
    using finiteunitProds finiteallDepS by blast
  ultimately show ?thesis
    using nPImage finitenPlambda finite_UN by metis
qed

(* finiteness uppr_rules *)
lemma finiteupprRules: "finite (uppr_rules P)"
proof -
  have "finite (nonUnitProds P)"
    unfolding nonUnitProds_def using finiteunitProds by blast
  moreover have "finite (newProds P)"
    using finitenewProds by blast
  ultimately show ?thesis
    unfolding uppr_rules_def by blast
qed

(* uppr Existence *)
lemma uppr_exists: "\<forall>P. \<exists>P'. uppr P P'"
  unfolding uppr_def using finiteupprRules finite_list by blast

(* towards theorem 4.4 *)

lemma inNonUnitProds:
  "p \<in> nonUnitProds P \<Longrightarrow> p \<in> set P"
  unfolding nonUnitProds_def by blast

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

lemma unitProds_deriv: 
  assumes "unitProds P \<turnstile> u \<Rightarrow>* v"
  shows "set P \<turnstile> u \<Rightarrow>* v"
proof -
  have "\<forall>p \<in> unitProds P. p \<in> set P"
    unfolding unitProds_def by blast
  thus ?thesis 
    using assms psubRtcDeriv by blast
qed

lemma uppr_r3:
  assumes "uppr P P'"
    and "set P' \<turnstile> u \<Rightarrow> v"
  shows "set P \<turnstile> u \<Rightarrow>* v"
proof -
  obtain A \<alpha> r1 r2 where "(A, \<alpha>) \<in> set P' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2" (is "?A")
    using assms derive.cases by meson
  hence "(A, \<alpha>) \<in> nonUnitProds P \<or> (A, \<alpha>) \<in> newProds P"
    using assms(1) unfolding uppr_def uppr_rules_def by simp
  thus ?thesis
  proof
    assume "(A, \<alpha>) \<in> nonUnitProds P"
    hence "(A, \<alpha>) \<in> set P"
      using inNonUnitProds by blast
    hence "set P \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ \<alpha> @ r2"
      by (auto simp: derive.simps)
    thus ?thesis using \<open>?A\<close> by simp
  next 
    assume "(A, \<alpha>) \<in> newProds P"
    from this obtain B where "(B, \<alpha>) \<in> nonUnitProds P \<and> (A, B) \<in> allDepS (unitProds P)" (is "?B")
      unfolding newProds_def by blast
    hence "unitProds P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      unfolding allDepS_def by simp
    hence "set P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
      using unitProds_deriv by blast
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

lemma uppr_r4: 
  assumes "set P' \<turnstile> u \<Rightarrow>* v"
    and "uppr P P'"
  shows "set P \<turnstile> u \<Rightarrow>* v"
  using assms by (induction rule: rtranclp.induct) (auto simp: uppr_r3 rtranclp_trans)

lemma deriv_allDepS:
  assumes "set P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "(A, B) \<in> allDepS (unitProds P)"
proof -
  have "(A, [Nt B]) \<in> set P"
    using assms by (simp add: derive_singleton)
  hence "(A, [Nt B]) \<in> unitProds P"
    unfolding unitProds_def by blast
  hence "unitProds P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
    by (simp add: derive_singleton)
  moreover have "B \<in> Nts (unitProds P) \<and> A \<in> Nts (unitProds P)"
    using \<open>(A, [Nt B]) \<in> unitProds P\<close> Nts_def nts_of_syms_def by fastforce
  ultimately show ?thesis
    unfolding allDepS_def by blast
qed

lemma uppr_r12: 
  assumes "uppr P P'" "(A, \<alpha>) \<in> set P'"
  shows "(A, \<alpha>) \<notin> unitProds P"
  using assms unfolding uppr_def uppr_rules_def nonUnitProds_def unitProds_def newProds_def by blast

lemma uppr_r14: 
  assumes "uppr P P'" 
    and "set P \<turnstile> [Nt A] \<Rightarrow> [Nt B]" "set P' \<turnstile> [Nt B] \<Rightarrow> v"
  shows "set P' \<turnstile> [Nt A] \<Rightarrow> v"
proof -
  have 1: "(A, B) \<in> allDepS (unitProds P)"
    using deriv_allDepS assms(2) by fast
  have 2: "(B, v) \<in> set P'"
    using assms(3) by (simp add: derive_singleton)
  thus ?thesis
  proof (cases "(B, v) \<in> set P")
    case True
    hence "(B, v) \<in> nonUnitProds P"
      unfolding nonUnitProds_def using assms(1) assms(3) uppr_r12[of P P' B v] by (simp add: derive_singleton)
    then show ?thesis
    using 1 assms(1) unfolding uppr_def uppr_rules_def newProds_def derive_singleton by blast
  next
    case False
    hence "(B, v) \<in> newProds P"
      using assms(1) 2 unfolding nonUnitProds_def uppr_def uppr_rules_def by simp
    from this obtain C where "(C, v) \<in> nonUnitProds P \<and> (B, C) \<in> allDepS (unitProds P)" (is "?C")
      unfolding newProds_def by blast
    hence "unitProds P \<turnstile> [Nt A] \<Rightarrow>* [Nt C]"
      using 1 unfolding allDepS_def by auto
    hence "(A, C) \<in> allDepS (unitProds P)"
      unfolding allDepS_def using "1" \<open>?C\<close> allDepS_def by fastforce
    hence "(A, v) \<in> newProds P"
      unfolding newProds_def using \<open>?C\<close> by blast
    hence "(A, v) \<in> set P'"
      using assms(1) unfolding uppr_def uppr_rules_def by blast
    thus ?thesis by (simp add: derive_singleton)
  qed
qed

lemma uppr_r20_aux:
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

lemma uppr_r20: 
  assumes "set P \<turnstile> u \<Rightarrow>* v"
    and "uppr P P'" "\<forall>a \<in> set v. \<exists>t. a = Tm t"
  shows "set P' \<turnstile> u \<Rightarrow>* v"
  using assms proof (induction rule: derives_induct')
  case base
  then show ?case by blast
next
  case (step l A r w)
  then show ?case 
  proof (cases "(A, w) \<in> unitProds P")
    case True
    from this obtain B where "w = [Nt B]" (is "?B")
      unfolding unitProds_def by blast
    have "set P' \<turnstile> l @ w @ r \<Rightarrow>* v \<and> Nt B \<notin> set v"
      using step.IH assms(2) assms(3) by blast
    obtain \<alpha> where "set P' \<turnstile> l @ [Nt B] @ r \<Rightarrow> l @ \<alpha> @ r \<and> set P' \<turnstile> l @ \<alpha> @ r \<Rightarrow>* v \<and> (B, \<alpha>) \<in> set P'" (is "?\<alpha>")
      using assms(2) assms(3) step.IH \<open>?B\<close>  uppr_r20_aux[of P' l B r v] by blast
    hence "(A, \<alpha>) \<in> set P'"
      using assms(2) step.hyps(2) \<open>?B\<close> uppr_r14[of P P' A B \<alpha>] by (simp add: derive_singleton)
    hence "set P' \<turnstile> l @ [Nt A] @ r \<Rightarrow>* l @ \<alpha> @ r"
      using derive.simps by fastforce
    then show ?thesis 
      using \<open>?\<alpha>\<close> by auto
  next
    case False
    hence "(A, w) \<in> nonUnitProds P"
      unfolding nonUnitProds_def using step.hyps(2) by blast
    hence "(A, w) \<in> set P'"
      using assms(2) unfolding uppr_def uppr_rules_def by simp
    hence "set P' \<turnstile> l @ [Nt A] @ r \<Rightarrow> l @ w @ r"
      by (auto simp: derive.simps)
    then show ?thesis
      using step by simp
  qed
qed

theorem uppr_lang_eq: 
  assumes "uppr P P'"
  shows "lang P S = lang P' S"
  unfolding Lang_def using assms uppr_r4 uppr_r20 ex_map_conv by meson

theorem nepr_uppr_lang_eq:
  assumes "nepr P P\<^sub>0"
    and "uppr P\<^sub>0 P'"
  shows "lang P' S = lang P\<^sub>0 S - {[]}"
  using assms nepr_lang_eq[of P P\<^sub>0 S] uppr_lang_eq[of P\<^sub>0 P' S] by blast

unused_thms
end