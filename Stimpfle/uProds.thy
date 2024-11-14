theory uProds
  imports "../CFG" eProds
begin

(* TODO: maybe add tm, tms and allSyms to CFG.thy ? *)
fun tm :: "('n,'t)syms \<Rightarrow> 't set" where
  "tm [] = {}" |
  "tm (Nt A # v) = tm v" |
  "tm (Tm a # v) = {a} \<union> tm v"

definition tms :: "('n,'t)prodS \<Rightarrow> 't set" where 
  "tms P = (\<Union>(A,w)\<in>P. tm w)"

definition allSyms :: "('n,'t)prodS \<Rightarrow> ('n,'t) sym set" where 
  "allSyms P = (Nt ` nts P) \<union> (Tm ` tms P)"

(* Rules of the form A\<rightarrow>B, where A and B are in nonterminals P *)
definition unitProds :: "('n,'t) prods \<Rightarrow> ('n,'t) prodS" where
  "unitProds P = {(l,r) \<in> set P. \<exists>A. r = [Nt A]}"

fun uprods :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "uprods [] = []" |
  "uprods (p#ps) = (if \<exists>A. (snd p) = [Nt A] then p#uprods ps else uprods ps)"

lemma unitProds_uprods: "set (uprods P) = unitProds P"
  unfolding unitProds_def by (induction P) auto

lemma finiteunitProds: "finite (unitProds P)"
  using unitProds_uprods by (metis List.finite_set)

(* A \<Rightarrow>* B where A and B are in nonTerminals g *)
definition allDepS :: "('n, 't) prodS \<Rightarrow> ('n \<times> 'n) set" where
  "allDepS P = {(a,b). P \<turnstile> [Nt a] \<Rightarrow>* [Nt b] \<and> a \<in> nts P \<and> b \<in> nts P}"

(* cross product of all nts in P. Used to show finiteness for allDepS *)
definition ntsCross :: "('n, 't) prodS  \<Rightarrow> ('n \<times> 'n) set" where
  "ntsCross P = {(A, B). A \<in> nts P \<and> B \<in> nts P }"

lemma nt_finite: "finite (nt A)"
  apply (induction A) apply auto
  by (metis Un_insert_left finite_insert nt.simps(2) nt.simps(3) sup_bot_left sym.exhaust)

lemma finiteallDeps: 
  assumes "finite P" 
  shows  "finite (allDepS P)"
proof -
  have "finite (nts P)"
    unfolding nts_def using assms nt_finite using nt_finite by auto
  hence "finite (ntsCross P)"
    unfolding ntsCross_def by auto
  moreover have "allDepS P \<subseteq> ntsCross P"
    unfolding allDepS_def ntsCross_def by blast
  ultimately show ?thesis
    using assms infinite_super by fastforce 
qed

definition nonUnitProds :: "('n, 't) prods \<Rightarrow> ('n, 't) prodS" where
  "nonUnitProds P = (set P - (unitProds P))"

definition newProds :: "('n, 't) prods \<Rightarrow> ('n, 't) prodS" where 
  "newProds P = {(a,r). \<exists>b. (b,r) \<in> (nonUnitProds P) \<and> (a, b) \<in> allDepS (unitProds P)}"

definition uppr_rules :: "('n, 't) prods \<Rightarrow> ('n, 't) prodS" where
  "uppr_rules P = (nonUnitProds P \<union> newProds P)"

definition uppr :: "('n, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> bool" where
  "uppr P P' = (set P' = uppr_rules P)"

(* Existence of uppr for every P *)
lemma uppr_exists: "\<forall>P. \<exists>P'. uppr P P'"
  sorry

(*
theorem thm4_4: 
  assumes "[] \<notin> L G"
    and "negr G0 G"
    and "upgr G G'"
  shows "L G = L G'"
  using assms sorry
*)

theorem uppr_lang_eq:
  assumes "nepr P\<^sub>0 P"
    and "uppr P P'"
  shows "lang P S = lang P' S"
  sorry

end