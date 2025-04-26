theory Pilling
  imports 
    "../CFG"
    "../CFL"
    "./Lfun"
    "./Parikh_Img"
    "./Eq_Sys"
    "Regular-Sets.Regular_Set"
    "Regular-Sets.Regular_Exp"
begin


section \<open>The lemma from Pilling's paper\<close>

(* In this section, the lemma from Pilling's paper will be proved.
   For some reason, the lemma will not be needed in the further proof.
*)

locale pillings_lemma
begin

subsection \<open>g_pre (in the paper g_{iN} resp. X_{iN}\<close>

fun g_pre :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g_pre _ _ 0 = N {}" |
  "g_pre f_sys i (Suc n) = subst (f_sys ! i) (\<lambda>j. if j < length f_sys then g_pre f_sys j n else V j)"


lemma g_pre_eval:
  assumes "\<forall>j < length f_sys. s' j = eval (g_pre f_sys j n) s"
      and "\<forall>j \<ge> length f_sys. s' j = s j"
    shows "eval (g_pre f_sys i (Suc n)) s = eval (f_sys ! i) s'"
using assms by (simp add: substitution_lemma)


lemma g_pre_monotonically_increasing:
  "eval (g_pre f_sys i n) s \<subseteq> eval (g_pre f_sys i (Suc n)) s"
proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?s = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j n) s else s j"
  let ?s_Suc = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j (Suc n)) s else s j"
  from Suc.IH have s_subseteq_s_Suc: "?s j \<subseteq> ?s_Suc j" for j by auto

  have "eval (g_pre f_sys i (Suc n)) s = eval (f_sys ! i) ?s" using g_pre_eval[of f_sys] by auto
  also have "\<dots> \<subseteq> eval (f_sys ! i) ?s_Suc" using s_subseteq_s_Suc lfun_mono_aux[where s="?s"] by auto
  also have "\<dots> = eval (g_pre f_sys i (Suc (Suc n))) s" using g_pre_eval[of f_sys ?s_Suc] by auto
  finally show ?case .
qed


lemma g_pre_subseteq_sol:
  assumes "i < length f_sys"
      and "solves_ineq_sys f_sys s"
    shows "eval (g_pre f_sys i n) s \<subseteq> eval (f_sys ! i) s"
using assms proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?s' = "\<lambda>j. if j < length f_sys then eval (g_pre f_sys j n) s else s j"

  have "?s' j \<subseteq> s j" for j
  proof (cases "j < length f_sys")
    case True
    with Suc have "?s' j \<subseteq> eval (f_sys ! j) s" by auto
    also have "\<dots> \<subseteq> s j" using assms(2) True unfolding solves_ineq_sys_def by auto
    finally show ?thesis .
  next
    case False
    then show ?thesis by auto
  qed
  then have "eval (f_sys ! i) ?s' \<subseteq> eval (f_sys ! i) s" using lfun_mono_aux by meson
  then show ?case using g_pre_eval[of f_sys ?s'] by auto
qed


lemma g_pre_indep:
  assumes "i < length f_sys"
  shows "\<forall>x \<in> vars (g_pre f_sys i n). x \<ge> length f_sys"
proof (induction n arbitrary: i)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?upd = "\<lambda>x. if x < length f_sys then g_pre f_sys x n else V x"
  from vars_subst_upper have "vars (g_pre f_sys i (Suc n)) \<subseteq> (\<Union>x. vars (?upd x))" by simp
  moreover have "\<forall>y \<in> vars (?upd x). y \<ge> length f_sys" for x using Suc by simp
  ultimately show ?case by auto
qed



subsection \<open>g\<close>

(* This is the only reason why we have included the countable union in the lfun definition *)
definition g :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g f_sys i \<equiv> UnionC (\<lambda>n. g_pre f_sys i n)"


lemma g_indep:
  assumes "i < length f_sys"
  shows "\<forall>x \<in> vars (g f_sys i). x \<ge> length f_sys"
unfolding g_def using assms g_pre_indep by auto


lemma solves_g_if_solves_f_ineq:
  assumes "i < length f_sys"
      and "solves_ineq_sys f_sys s"
    shows "eval (g f_sys i) s \<subseteq> eval (f_sys ! i) s"
unfolding g_def proof
  fix x
  assume "x \<in> eval (UnionC (g_pre f_sys i)) s"
  then show "x \<in> eval (f_sys ! i) s" using g_pre_subseteq_sol[OF assms] by auto
qed


lemma Union_index_shift: "(\<Union>n. f n) = f 0 \<union> (\<Union>n. f (Suc n))"
proof
  show "\<Union> (range f) \<subseteq> f 0 \<union> (\<Union>n. f (Suc n))"
  proof
    fix x
    assume "x \<in> \<Union> (range f)"
    then obtain n where x_in_f: "n \<ge> 0 \<and> x \<in> f n" by auto
    show "x \<in> f 0 \<union> (\<Union>n. f (Suc n))"
    proof (cases "n=0")
      case True
      with x_in_f show ?thesis by auto
    next
      case False
      with x_in_f have "\<exists>n'. Suc n' = n" by presburger
      then obtain n' where "Suc n' = n" by blast
      with x_in_f show ?thesis by auto
    qed
  qed
  show "f 0 \<union> (\<Union>n. f (Suc n)) \<subseteq> \<Union> (range f)" by auto
qed


lemma g_pre_g_Union: "(\<Union>n. eval (g_pre f_sys i (Suc n)) s) =
  eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
proof -
  let ?s = "(\<lambda>n j. if j < length f_sys then eval (g_pre f_sys j n) s else s j)"
  have "?s n j \<subseteq> ?s (Suc n) j" for n j
    using g_pre_monotonically_increasing by fastforce
  then have s_monotone: "\<forall>n. ?s n \<le> ?s (Suc n)" by (simp add: le_fun_def)

  have s_Union: "(\<Union>i. if x < length f_sys then eval (g_pre f_sys x i) s else s x) =
    (if x < length f_sys then eval (g f_sys x) s else s x)" for x
    unfolding g_def by simp

  have "eval (g_pre f_sys i (Suc n)) s = eval (f_sys ! i) (?s n)" for n
    using g_pre_eval[of f_sys] by auto
  then have "(\<Union>n. eval (g_pre f_sys i (Suc n)) s) = (\<Union>n. eval (f_sys ! i) (?s n))" by auto
  also have "\<dots> = eval (f_sys ! i) (\<lambda>x. \<Union>i. if x < length f_sys then eval (g_pre f_sys x i) s else s x)"
    using s_monotone lfun_cont[of ?s "f_sys ! i"] by argo
  also have "\<dots> = eval (f_sys ! i) (\<lambda>x. if x < length f_sys then eval (g f_sys x) s else s x)"
    using s_Union by simp
  also have "\<dots> = eval (subst (f_sys ! i) (\<lambda>i. if i < length f_sys then g f_sys i else V i)) s"
    using substitution_lemma[of "\<lambda>x. if x < length f_sys then eval (g f_sys x) s else s x"
                                "\<lambda>i. if i < length f_sys then g f_sys i else V i"]
    by fastforce
  finally show ?thesis .
qed


lemma solves_f_if_solves_g_eq:
  assumes "\<forall>i < length f_sys. eval (g f_sys i) s = s i"
  shows "solves_eq_sys f_sys s"
unfolding solves_eq_sys_def proof (standard, standard)
  fix i
  assume "i < length f_sys"
  with assms(1) have "s i = (\<Union>n. eval (g_pre f_sys i n) s)" unfolding g_def by auto
  also have "\<dots> = (\<Union>n. eval (g_pre f_sys i (Suc n)) s)"
    using Union_index_shift[of "\<lambda>n. eval (g_pre f_sys i n) s"] by auto
  also have "\<dots> = eval (f_sys ! i) s"
    using g_pre_g_Union[of f_sys] assms by (simp add: substitution_lemma)
  finally show "eval (f_sys ! i) s = s i" by auto
qed


(* The lemma from Pilling's paper *)
lemma lemma_paper:
  assumes "\<forall>eq \<in> set f_sys. regular_fun eq"
    shows "\<exists>g_sys. length g_sys = length f_sys \<and> indep_leq g_sys (length f_sys - 1)
                \<and> (\<forall>s. solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys g_sys s)
                \<and> (\<forall>s. solves_eq_sys g_sys s \<longrightarrow> solves_eq_sys f_sys s)"
proof -
  let ?g_sys = "map (\<lambda>i. g f_sys i) [0..<length f_sys]"
  have length_g_sys: "length ?g_sys = length f_sys" by auto
  have indep_g_sys: "indep_leq ?g_sys (length f_sys - 1)"
    unfolding indep_leq_def using g_indep by fastforce

  have "\<lbrakk> i < length f_sys; solves_ineq_sys f_sys s \<rbrakk> \<Longrightarrow> eval (?g_sys ! i) s \<subseteq> s i" for s i
    using solves_g_if_solves_f_ineq solves_ineq_sys_def by fastforce
  then have g_sol_of_f: "solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys ?g_sys s" for s
    using solves_ineq_sys_def by (metis length_g_sys)

  have f_sol_of_g: "solves_eq_sys ?g_sys s \<longrightarrow> solves_eq_sys f_sys s" for s
    using solves_f_if_solves_g_eq solves_eq_sys_def
    by (metis add_0 diff_zero length_g_sys nth_map_upt)

  from length_g_sys indep_g_sys g_sol_of_f f_sol_of_g show ?thesis by blast
qed

end



section \<open>The theorem from the paper\<close>

subsection \<open>Special representation of regular functions\<close>

(* We first show that for every regular function f there is a representation of the form
   (3) (see Pilling's paper, we call it regular_fun' in the following)
   that has the same parikh image as f
*)

definition regular_fun' :: "nat \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "regular_fun' x f \<equiv> \<exists>p q. regular_fun p \<and> regular_fun q \<and>
    f = Union2 p (Conc q (V x)) \<and> x \<notin> vars p"

lemma "regular_fun' x f \<Longrightarrow> regular_fun f"
  unfolding regular_fun'_def by fast


(* Every regular function can be represented in form (3),
   as long as we only care for the Parikh image
*)
lemma regular_fun_regular_fun': "regular_fun f \<Longrightarrow>
    \<exists>f'. regular_fun' x f' \<and> vars f' = vars f \<union> {x} \<and>
         (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))"
proof (induction rule: regular_fun.induct)
  case (Variable y)
  then show ?case
  proof (cases "x=y")
    let ?f' = "Union2 (N {}) (Conc (N {[]}) (V x))"
    case True
    then have "regular_fun' x ?f'"
      unfolding regular_fun'_def by (simp add: emptyset_regular epsilon_regular)
    moreover have "eval ?f' s = eval (V y) s" for s :: "'a state" using True by simp
    moreover have "vars ?f' = vars (V y) \<union> {x}" using True by simp
    ultimately show ?thesis by metis
  next
    let ?f' = "Union2 (V y) (Conc (N {}) (V x))"
    case False
    then have "regular_fun' x ?f'"
      unfolding regular_fun'_def by (auto simp add: emptyset_regular epsilon_regular)
    moreover have "eval ?f' s = eval (V y) s" for s :: "'a state" using False by simp
    moreover have "vars ?f' = vars (V y) \<union> {x}" by simp 
    ultimately show ?thesis by metis
  qed
next
  case (Const l)
  let ?f' = "Union2 (N l) (Conc (N {}) (V x))"
  have "regular_fun' x ?f'"
    unfolding regular_fun'_def using Const by (auto simp add: emptyset_regular)
  moreover have "eval ?f' s = eval (N l) s" for s :: "'a state" by simp
  moreover have "vars ?f' = vars (N l) \<union> {x}" by simp 
  ultimately show ?case by metis
next
  case (Union2 f1 f2)
  then obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and> vars f1' = vars f1 \<union> {x} \<and>
      (\<forall>s. parikh_img (eval f1 s) = parikh_img (eval f1' s))"
    and f2'_intro: "regular_fun' x f2' \<and> vars f2' = vars f2 \<union> {x} \<and>
      (\<forall>s. parikh_img (eval f2 s) = parikh_img (eval f2' s))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "regular_fun p1 \<and> regular_fun q1 \<and>
    f1' = Union2 p1 (Conc q1 (V x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "regular_fun p2 \<and> regular_fun q2 \<and> f2' = Union2 p2 (Conc q2 (V x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?f' = "Union2 (Union2 p1 p2) (Conc (Union2 q1 q2) (V x))"
  have "regular_fun' x ?f'" unfolding regular_fun'_def using p1_q1_intro p2_q2_intro by auto
  moreover have "parikh_img (eval ?f' s) = parikh_img (eval (Union2 f1 f2) s)" for s
    using p1_q1_intro p2_q2_intro f1'_intro f2'_intro
    by (simp add: conc_Un_distrib(2) sup_assoc sup_left_commute)
  moreover from f1'_intro f2'_intro p1_q1_intro p2_q2_intro
    have "vars ?f' = vars (Union2 f1 f2) \<union> {x}" by auto
  ultimately show ?case by metis
next
  case (Conc f1 f2)
  then obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and> vars f1' = vars f1 \<union> {x} \<and>
      (\<forall>s. parikh_img (eval f1 s) = parikh_img (eval f1' s))"
    and f2'_intro: "regular_fun' x f2' \<and> vars f2' = vars f2 \<union> {x} \<and>
      (\<forall>s. parikh_img (eval f2 s) = parikh_img (eval f2' s))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "regular_fun p1 \<and> regular_fun q1 \<and>
    f1' = Union2 p1 (Conc q1 (V x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "regular_fun p2 \<and> regular_fun q2 \<and> f2' = Union2 p2 (Conc q2 (V x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?q' = "Union2 (Conc q1 (Conc (V x) q2)) (Union2 (Conc p1 q2) (Conc q1 p2))"
  let ?f' = "Union2 (Conc p1 p2) (Conc ?q' (V x))"

  have "\<forall>s. (parikh_img (eval (Conc f1 f2) s) = parikh_img (eval ?f' s))"
  proof (rule allI)
    fix s
    have f2_subst: "parikh_img (eval f2 s) = parikh_img (eval p2 s \<union> eval q2 s @@ s x)"
      using p2_q2_intro f2'_intro by auto

    have "parikh_img (eval (Conc f1 f2) s) = parikh_img ((eval p1 s \<union> eval q1 s @@ s x) @@ eval f2 s)"
      using p1_q1_intro f1'_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(5) parikh_conc_right)
    also have "\<dots> = parikh_img (eval p1 s @@ eval f2 s \<union> eval q1 s @@ s x @@ eval f2 s)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = parikh_img (eval p1 s @@ (eval p2 s \<union> eval q2 s @@ s x)
        \<union> eval q1 s @@ s x @@ (eval p2 s \<union> eval q2 s @@ s x))"
      using f2_subst by (smt (verit, ccfv_threshold) parikh_conc_right parikh_img_Un parikh_img_commut)
    also have "\<dots> = parikh_img (eval p1 s @@ eval p2 s \<union> (eval p1 s @@ eval q2 s @@ s x \<union>
        eval q1 s @@ eval p2 s @@ s x \<union> eval q1 s @@ s x @@ eval q2 s @@ s x))"
      using parikh_img_commut by (smt (z3) conc_Un_distrib(1) parikh_conc_right parikh_img_Un sup_assoc)
    also have "\<dots> = parikh_img (eval p1 s @@ eval p2 s \<union> (eval p1 s @@ eval q2 s \<union>
        eval q1 s @@ eval p2 s \<union> eval q1 s @@ s x @@ eval q2 s) @@ s x)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = parikh_img (eval ?f' s)"
      by (simp add: Un_commute)
    finally show "parikh_img (eval (Conc f1 f2) s) = parikh_img (eval ?f' s)" .
  qed
  moreover have "regular_fun' x ?f'" unfolding regular_fun'_def using p1_q1_intro p2_q2_intro by auto
  moreover from f1'_intro f2'_intro p1_q1_intro p2_q2_intro
    have "vars ?f' = vars (Conc f1 f2) \<union> {x}" by auto
  ultimately show ?case by metis
next
  case (Star f)
  then obtain f' where f'_intro: "regular_fun' x f' \<and> vars f' = vars f \<union> {x} \<and>
      (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))" by auto
  then obtain p q where p_q_intro: "regular_fun p \<and> regular_fun q \<and>
    f' = Union2 p (Conc q (V x)) \<and> (\<forall>y \<in> vars p. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?q_new = "Conc (Star p) (Conc (Star (Conc q (V x))) (Conc (Star (Conc q (V x))) q))"
  let ?f_new = "Union2 (Star p) (Conc ?q_new (V x))"

  have "\<forall>s. (parikh_img (eval (Star f) s) = parikh_img (eval ?f_new s))"
  proof (rule allI)
    fix s
    have "parikh_img (eval (Star f) s) = parikh_img (star (eval p s \<union> eval q s @@ s x))"
      using f'_intro parikh_star_mono_eq p_q_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(5) eval.simps(6))
    also have "\<dots> = parikh_img (star (eval p s) @@ star (eval q s @@ s x))"
      using parikh_img_star by blast
    also have "\<dots> = parikh_img (star (eval p s) @@
        star ({[]} \<union> star (eval q s @@ s x) @@ eval q s @@ s x))"
      by (metis Un_commute conc_star_comm star_idemp star_unfold_left)
    also have "\<dots> = parikh_img (star (eval p s) @@ star (star (eval q s @@ s x) @@ eval q s @@ s x))"
      by auto
    also have "\<dots> = parikh_img (star (eval p s) @@ ({[]} \<union> star (eval q s @@ s x)
        @@ star (eval q s @@ s x) @@ eval q s @@ s x))"
      using parikh_img_star2 parikh_conc_left by blast
    also have "\<dots> = parikh_img (star (eval p s) @@ {[]} \<union> star (eval p s) @@ star (eval q s @@ s x)
        @@ star (eval q s @@ s x) @@ eval q s @@ s x)" by (metis conc_Un_distrib(1))
    also have "\<dots> = parikh_img (eval ?f_new s)" by (simp add: conc_assoc)
    finally show "parikh_img (eval (Star f) s) = parikh_img (eval ?f_new s)" .
  qed
  moreover have "regular_fun' x ?f_new" unfolding regular_fun'_def using p_q_intro by fastforce
  moreover from f'_intro p_q_intro have "vars ?f_new = vars (Star f) \<union> {x}" by auto
  ultimately show ?case by metis
qed



subsection \<open>Minimal solution\<close>

(* We show that F(E)*E (in the following q(p)*p is a minimal solution) *)

locale of_form_regular_fun' =
  fixes x :: "nat"
  fixes p :: "'a lfun"
  fixes q :: "'a lfun"
  assumes p_reg:      "regular_fun p"
  assumes q_reg:      "regular_fun q"
  assumes x_not_in_p: "x \<notin> vars p"
begin

abbreviation "eq \<equiv> Union2 p (Conc q (V x))"
abbreviation "sol \<equiv> Conc (Star (subst q (V(x := p)))) p"


(* F(E)*E is a regular function *)
lemma sol_is_reg: "regular_fun sol"
proof -
  from p_reg q_reg have r_reg: "regular_fun (subst q (V(x := p)))"
    using subst_reg_fun_update by auto
  with p_reg show "regular_fun sol" by fast
qed


(* F(E)*E contains only variables which also appear in the equation, except x *)
lemma sol_vars: "vars sol \<subseteq> vars eq - {x}"
proof -
  let ?upd = "V(x := p)"
  let ?subst_q = "subst q ?upd"
  from x_not_in_p have vars_p: "vars p \<subseteq> vars eq - {x}" by fastforce

  have "vars ?subst_q \<subseteq> vars eq - {x}"
  proof
    fix y
    assume y_in_subst_q: "y \<in> vars ?subst_q"
    with vars_subst obtain y' where y'_in_q: "y' \<in> vars q" and y_in_y': "y \<in> vars (?upd y')"
      unfolding fun_upd_def by force
    show "y \<in> vars eq - {x}"
    proof (cases "y' = x")
      case True
      with y_in_y' x_not_in_p show ?thesis by auto
    next
      case False
      with y'_in_q y_in_y' show ?thesis by simp
    qed
  qed
  with x_not_in_p show ?thesis by auto
qed


(* F(E)*E is a solution of equation (3) from the paper (with \<supseteq> instead of =) *)
lemma sol_is_sol_ineq: "partial_sol_ineq x eq sol"
proof (rule partial_sol_ineqI)
  fix s
  assume x_is_sol: "s x = eval sol s"

  let ?r = "subst q (V (x := p))"
  let ?upd = "V(x := sol)"
  let ?q_subst = "subst q ?upd"
  let ?eq_subst = "subst eq ?upd"

  from sol_is_reg have r_reg: "regular_fun ?r" unfolding fun_upd_def by blast
  have homogeneous_app: "parikh_img (eval ?q_subst s) \<subseteq> parikh_img (eval (Conc (Star ?r) ?r) s)"
    using reg_fun_homogeneous[OF q_reg r_reg p_reg] by blast

  from x_not_in_p have "eval (subst p ?upd) s = eval p s" using eval_vars_subst[of p] by simp
  then have "parikh_img (eval ?eq_subst s) = parikh_img (eval p s \<union> eval ?q_subst s @@ eval sol s)"
    by simp
  also have "\<dots> \<subseteq> parikh_img (eval p s \<union> eval (Conc (Star ?r) ?r) s @@ eval sol s)"
    using homogeneous_app by (metis dual_order.refl parikh_conc_right_subset parikh_img_Un sup.mono)
  also have "\<dots> = parikh_img (eval p s) \<union>
      parikh_img (star (eval ?r s) @@ eval ?r s @@ star (eval ?r s) @@ eval p s)"
    by (simp add: conc_assoc)
  also have "\<dots> = parikh_img (eval p s) \<union>
      parikh_img (eval ?r s @@ star (eval ?r s) @@ eval p s)"
    using parikh_img_commut conc_star_star by (smt (verit, best) conc_assoc conc_star_comm)
  also have "\<dots> = parikh_img (star (eval ?r s) @@ eval p s)"
    using star_unfold_left
    by (smt (verit) conc_Un_distrib(2) conc_assoc conc_epsilon(1) parikh_img_Un sup_commute)
  finally show "parikh_img (eval ?eq_subst s) \<subseteq> parikh_img (s x)" using x_is_sol by simp
qed


lemma sol_is_minimal:
  assumes is_sol:    "solves_ineq_comm x eq s"
      and sol'_s:    "s x = eval sol' s"
    shows            "parikh_img (eval sol s) \<subseteq> parikh_img (s x)"
proof -
  from is_sol sol'_s have is_sol': "parikh_img (eval q s @@ s x \<union> eval p s) \<subseteq> parikh_img (s x)"
    unfolding solves_ineq_comm_def by simp
  then have 1: "parikh_img (eval (Conc (Star q) p) s) \<subseteq> parikh_img (s x)"
    using parikh_img_arden by auto

  from is_sol' have "parikh_img (eval p s) \<subseteq> parikh_img (eval (V x) s)" by auto
  then have "parikh_img (eval (subst q (V(x := p))) s) \<subseteq> parikh_img (eval q s)"
    using parikh_img_subst_mono_upd by (metis fun_upd_triv subst_id)
  then have "parikh_img (eval (Star (subst q (V(x := p)))) s) \<subseteq> parikh_img (eval (Star q) s)"
    using parikh_star_mono by auto
  then have "parikh_img (eval sol s) \<subseteq> parikh_img (eval (Conc (Star q) p) s)"
    using parikh_conc_right_subset by (metis eval.simps(5))

  with 1 show ?thesis by fast
qed


(* TODO: should not be needed, right? *)
(* F(E)*E solves equation (3) from the paper (this time with =) *)
(*lemma sol_is_sol_eq: "partial_sol_eq x eq sol"
unfolding partial_sol_eq_def proof
  fix s

  let ?r = "subst q (\<lambda>y. if y = x then p else V y)"
  let ?upd = "\<lambda>y. if y = x then sol else V y"
  let ?upd_subst = "\<lambda>y. if y = x then subst eq ?upd else V y"

  have "parikh_img (eval (subst eq ?upd_subst) s) \<subseteq> parikh_img (eval (subst eq ?upd) s)" for s
  proof -
    fix s
    from sol_is_sol_ineq have "parikh_img (eval (subst eq ?upd) s) \<subseteq> parikh_img (eval sol s)"
      unfolding partial_sol_ineq_def sorry (* by blast *)
    then show "parikh_img (eval (subst eq ?upd_subst) s) \<subseteq> parikh_img (eval (subst eq ?upd) s)"
      using parikh_img_subst_mono[of ?upd_subst s ?upd eq] by auto
  qed
  then have "partial_sol_ineq x eq (subst eq ?upd)" unfolding partial_sol_ineq_def by auto
  then have "parikh_img (eval sol s) \<subseteq> parikh_img (eval (subst eq ?upd) s)"
    using sol_is_minimal by blast
  with sol_is_sol_ineq show "parikh_img (eval (subst eq ?upd) s) = parikh_img (eval sol s)"
    unfolding partial_sol_ineq_def by blast
qed*)


lemma sol_is_minimal_reg_sol:
  "regular_fun sol \<and> partial_min_sol_one_ineq x eq sol"
  unfolding partial_min_sol_one_ineq_def
  using sol_is_reg sol_vars sol_is_sol_ineq sol_is_minimal
  by blast

end


(* Given equation (2), there exists a regular minimal solution *)
lemma exists_minimal_reg_sol:
  assumes eq_reg: "regular_fun eq"
  shows "\<exists>sol. regular_fun sol \<and> partial_min_sol_one_ineq x eq sol"
proof -
  from regular_fun_regular_fun'[OF eq_reg] obtain eq'
    where eq'_intro: "regular_fun' x eq' \<and> vars eq' = vars eq \<union> {x} \<and>
                    (\<forall>s. parikh_img (eval eq s) = parikh_img (eval eq' s))" by blast
  then obtain p q
    where p_q_intro: "regular_fun p \<and> regular_fun q \<and> eq' = Union2 p (Conc q (V x)) \<and> x \<notin> vars p"
    unfolding regular_fun'_def by blast

  let ?sol = "Conc (Star (subst q (V(x := p)))) p"
  from p_q_intro have sol_prop: "regular_fun ?sol \<and> partial_min_sol_one_ineq x eq' ?sol"
    using of_form_regular_fun'.sol_is_minimal_reg_sol unfolding of_form_regular_fun'_def by blast
  with eq'_intro have "partial_min_sol_one_ineq x eq ?sol"
    using same_min_sol_if_same_parikh_img by blast
  with sol_prop show ?thesis by blast
qed


lemma exists_minimal_reg_sol_sys_aux:
  assumes eqs_reg:   "\<forall>eq \<in> set sys. regular_fun eq"
      and sys_valid: "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
      and r_valid:   "r \<le> length sys"   
    shows            "\<exists>sols. partial_min_sol_ineq_sys r sys sols \<and> (\<forall>i. regular_fun (sols i))"
using assms proof (induction r)
  case 0
  have "solution_ineq_sys (take 0 sys) V"
    unfolding solution_ineq_sys_def solves_ineq_sys_comm_def by simp
  then show ?case unfolding partial_min_sol_ineq_sys_def by auto
next
  case (Suc r)
  then obtain sols where sols_intro: "partial_min_sol_ineq_sys r sys sols \<and> (\<forall>i. regular_fun (sols i))"
    by auto
  then have sols_r_V: "sols r = V r" unfolding partial_min_sol_ineq_sys_def by fast
  then have sols_r_upd: "subst (sols r) (V(r := r')) = r'" for r' by fastforce

  let ?sys' = "sys_subst sys sols"

  from eqs_reg Suc.prems have "regular_fun (sys ! r)" by simp
  with sols_intro Suc.prems have sys_r_reg: "regular_fun (?sys' ! r)"
    using subst_reg_fun[of "sys ! r"] sys_subst_subst[of r sys] by simp

  then obtain sol_r where sol_r_intro:
    "regular_fun sol_r \<and> partial_min_sol_one_ineq r (?sys' ! r) sol_r"
    using exists_minimal_reg_sol by blast

  let ?sols' = "\<lambda>i. subst (sols i) (V(r := sol_r))"
  from sols_intro have sols'_r: "?sols' r = sol_r" unfolding partial_min_sol_ineq_sys_def by simp

  from sol_r_intro sols_intro have "\<forall>i. regular_fun (?sols' i)"
    using subst_reg_fun_update by fast

  moreover have "partial_min_sol_ineq_sys (Suc r) sys ?sols'"
  proof -
    have 1: "solution_ineq_sys (take (Suc r) sys) ?sols'"
    unfolding solution_ineq_sys_def proof (rule allI, rule impI)
      fix s
      assume s_sols': "\<forall>x. s x = eval (?sols' x) s"

      (* Proof sketch:
         We know s x = eval (?sols' x) s, in particular s r = eval sol_r s
         For x < r: s x = eval (?sols' x) s = eval (subst (sols x) V(r := sol_r)) s
                        = eval (sols x) s(r := eval sol_r s) = eval (sols x) s(r := s r)
                        = eval (sols x) s
         by IH f.a. x < r: eval (sys ! x) s \<subseteq> s x
         for r: s r \<supseteq> eval (?sys' ! r) s = eval (subst (sys ! r) sols) s
                    = eval (sys ! r) (\<lambda>x. eval (sols x) s) = eval (sys ! r) s
         thus ?sols' is a solution   q.e.d.
      *)

      from sols'_r s_sols' have s_r_sol_r: "s r = eval sol_r s" by simp
      with s_sols' have s_sols: "s x = eval (sols x) s" for x
        using substitution_lemma_update[of "sols x"] by (auto simp add: fun_upd_idem)
      with sols_intro have solves_r_sys: "solves_ineq_sys_comm (take r sys) s"
        unfolding partial_min_sol_ineq_sys_def solution_ineq_sys_def by meson
      
      have "eval (sys ! r) (\<lambda>y. eval (sols y) s) = eval (?sys' ! r) s"
        using substitution_lemma[of "\<lambda>y. eval (sols y) s"]
        by (simp add: Suc.prems(3) Suc_le_lessD sys_subst_subst)
      with s_sols have "eval (sys ! r) s = eval (?sys' ! r) s"
        by (metis (mono_tags, lifting) eval_vars)
      with sol_r_intro s_r_sol_r have "parikh_img (eval (sys ! r) s) \<subseteq> parikh_img (s r)"
        unfolding partial_min_sol_one_ineq_def partial_sol_ineq_def solves_ineq_comm_def by simp
      with solves_r_sys show "solves_ineq_sys_comm (take (Suc r) sys) s"
        unfolding solves_ineq_sys_comm_def solves_ineq_comm_def by (auto simp add: less_Suc_eq)
    qed

    have 2: "\<forall>sols2 s2. (\<forall>x. s2 x = eval (sols2 x) s2)
                  \<and> solves_ineq_sys_comm (take (Suc r) sys) s2
                  \<longrightarrow> (\<forall>i. parikh_img (eval (?sols' i) s2) \<subseteq> parikh_img (s2 i))"
    proof (rule allI | rule impI)+
      fix sols2 s2 i

      (* Proof sketch
         Assume solution_ineq_sys (take (Suc r) sys) sols2 (As.1) and
            \<forall>i. \<forall>x \<in> vars (sols2 i). x > r \<and> x < length sys (As.2) and
            \<forall>x. s' x = eval (sols2 x) s' (As.4) and
         To show: \<forall>i \<le> r. eval (?sols' i) s' \<subseteq> s' i

           From As.2 \<forall>i. \<forall>x \<in> vars (sols2 i). x \<ge> r \<and> x < length sys (1) follows immediately
           We now show solution_ineq_sys (take r sys) sols2 (2):
             Fix s' s.t. \<forall>x. s' x = eval (sols2 x) s'
             By As.1 we have solves_ineq_sys_comm (take (Suc r) sys) sols2
             i.e. f.a. i \<le> r: eval (sys ! i) s' \<subseteq> s' i
             \<Longrightarrow> solves_ineq_sys_comm (take r sys) sols2
           From As.4 s' x = eval (sols2 x) s' (4)
           (1), (2) and (4) yield (by IH) \<forall>i < r. eval (sols i) s' \<subseteq> s' i
           With \<forall>i \<ge> r. eval (sols i) s' = eval (V i) s' = s' i we have
             \<forall>i. eval (sols i) s' \<subseteq> s' i (tmp)

           We show eval solves_ineq_comm x (?sys' ! r) s'
             From As.1 and As.4 we know eval (sys ! r) s' \<subseteq> s' r
             Furthermore eval (?sys' ! r) s' = eval (subst (sys ! r) sols) s'
               = eval (sys ! r) (\<lambda>i. eval (sols i) s') \<subseteq> (tmp) eval (sys ! r) s'
             Thus eval (?sys' ! r) s' \<subseteq> s' r
           with (As.4) we have by (sol_r_intro) eval sol_r s' \<subseteq> s' r (R)

           Finally: \<forall>i. eval (?sols' i) s' = eval (subst (sols i) V(r := sol_r)) s'
             = eval (sols i) s'(r := eval sol_r s') \<subseteq> (R) eval (sols i) s' \<subseteq> (tmp) s' i
      *)

      assume as: "(\<forall>x. s2 x = eval (sols2 x) s2) \<and> solves_ineq_sys_comm (take (Suc r) sys) s2"
      then have "solves_ineq_sys_comm (take r sys) s2" unfolding solves_ineq_sys_comm_def by fastforce
      with as sols_intro have sols_s2: "parikh_img (eval (sols i) s2) \<subseteq> parikh_img (s2 i)" for i
        unfolding partial_min_sol_ineq_sys_def by auto

      have "eval (?sys' ! r) s2 = eval (sys ! r) (\<lambda>i. eval (sols i) s2)"
        unfolding sys_subst_def using substitution_lemma[where f="sys ! r"]
        by (simp add: Suc.prems(3) Suc_le_lessD)
      with sols_s2 have "parikh_img (eval (?sys' ! r) s2) \<subseteq> parikh_img (eval (sys ! r) s2)"
        using lfun_mono_parikh[of "sys ! r"] by auto
      with as have "solves_ineq_comm r (?sys' ! r) s2"
        unfolding solves_ineq_sys_comm_def solves_ineq_comm_def using Suc.prems(3) by force
      with as sol_r_intro have sol_r_min: "parikh_img (eval sol_r s2) \<subseteq> parikh_img (s2 r)"
        unfolding partial_min_sol_one_ineq_def by blast

      let ?s' = "s2(r := eval sol_r s2)"
      from sol_r_min have "parikh_img (?s' i) \<subseteq> parikh_img (s2 i)" for i by simp
      with sols_s2 show "parikh_img (eval (?sols' i) s2) \<subseteq> parikh_img (s2 i)"
        using substitution_lemma_update[of "sols i"] lfun_mono_parikh[of "sols i" ?s' s2] by force
    qed

    from sols_intro have 3: "\<forall>i \<ge> Suc r. ?sols' i = V i"
      unfolding partial_min_sol_ineq_sys_def by auto

    from sols_intro have "\<forall>i < r. \<forall>x \<in> vars (sols i). x \<ge> r \<and> x < length sys"
      unfolding partial_min_sol_ineq_sys_def by simp
    with sols_intro have vars_sols: "\<forall>i < length sys. \<forall>x \<in> vars (sols i). x \<ge> r \<and> x < length sys"
      unfolding partial_min_sol_ineq_sys_def by (metis empty_iff insert_iff leI vars.simps(1))
    with sys_valid have "\<forall>x \<in> vars (subst (sys ! i) sols). x \<ge> r \<and> x < length sys" if "i < length sys" for i
      using vars_subst[of "sys ! i" sols] that by (metis UN_E nth_mem)
    then have "\<forall>x \<in> vars (?sys' ! i). x \<ge> r \<and> x < length sys" if "i < length sys" for i
      unfolding sys_subst_def using Suc.prems(3) that by auto
    moreover from sol_r_intro have "vars (sol_r) \<subseteq> vars (?sys' ! r) - {r}"
      unfolding partial_min_sol_one_ineq_def by simp
    ultimately have vars_sol_r: "\<forall>x \<in> vars sol_r. x > r \<and> x < length sys"
      unfolding partial_min_sol_one_ineq_def using Suc.prems(3)
      by (metis DiffE Suc_le_lessD insertCI nat_less_le subsetD)
    moreover have "vars (?sols' i) \<subseteq> vars (sols i) - {r} \<union> vars sol_r" if "i < length sys" for i
      using vars_subst_upd_upper by meson
    ultimately have "\<forall>x \<in> vars (?sols' i). x > r \<and> x < length sys" if "i < length sys" for i
      using vars_sols that by fastforce
    with r_valid have 4: "\<forall>i < Suc r. \<forall>x \<in> vars (?sols' i). x \<ge> Suc r \<and> x < length sys"
      by (meson Suc.prems(3) Suc_le_eq dual_order.strict_trans1)

    from 1 2 3 4 show "partial_min_sol_ineq_sys (Suc r) sys ?sols'"
      unfolding partial_min_sol_ineq_sys_def by blast
  qed
 
  ultimately show ?case by blast
qed


lemma exists_minimal_reg_sol_sys:
  assumes eqs_reg:   "\<forall>eq \<in> set sys. regular_fun eq"
      and sys_valid: "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
    shows            "\<exists>sols. min_sol_ineq_sys_comm sys sols \<and> (\<forall>i. regular_lang (sols i))"
proof -
  from eqs_reg sys_valid have
    "\<exists>sols. partial_min_sol_ineq_sys (length sys) sys sols \<and> (\<forall>i. regular_fun (sols i))"
    using exists_minimal_reg_sol_sys_aux by blast
  then obtain sols where
    sols_intro: "partial_min_sol_ineq_sys (length sys) sys sols \<and> (\<forall>i. regular_fun (sols i))"
    by blast
  then have "const_fun (sols i)" if "i < length sys" for i
    using that unfolding partial_min_sol_ineq_sys_def by (meson equals0I leD)
  with sols_intro have "\<exists>l. regular_lang l \<and> (\<forall>s. eval (sols i) s = l)" if "i < length sys" for i
    using that const_fun_regular_lang by metis
  then obtain ls where ls_intro: "\<forall>i < length sys. regular_lang (ls i) \<and> (\<forall>s. eval (sols i) s = ls i)"
    by metis

  let ?ls' = "\<lambda>i. if i < length sys then ls i else {}"
  from ls_intro have ls'_intro:
    "(\<forall>i < length sys. regular_lang (?ls' i) \<and> (\<forall>s. eval (sols i) s = ?ls' i))
     \<and> (\<forall>i \<ge> length sys. ?ls' i = {})" by force
  then have ls'_regular: "regular_lang (?ls' i)" for i by (meson lang.simps(1))

  from ls'_intro sols_intro have "solves_ineq_sys_comm sys ?ls'"
    unfolding partial_min_sol_ineq_sys_def solution_ineq_sys_def
    by (smt (verit) eval.simps(1) linorder_not_less nless_le take_all_iff)
  moreover have "\<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. parikh_img (?ls' x) \<subseteq> parikh_img (sol' x))"
  proof (rule allI, rule impI)
    fix sol' x
    assume as: "solves_ineq_sys_comm sys sol'"

    let ?sol_funs = "\<lambda>i. N (sol' i)"
    from as have "solves_ineq_sys_comm (take (length sys) sys) sol'" by simp
    moreover have "sol' x = eval (?sol_funs x) sol'" for x by simp
    ultimately show "\<forall>x. parikh_img (?ls' x) \<subseteq> parikh_img (sol' x)"
      using sols_intro unfolding partial_min_sol_ineq_sys_def
      by (smt (verit) empty_subsetI eval.simps(1) ls'_intro parikh_img_mono)
  qed
  ultimately have "min_sol_ineq_sys_comm sys ?ls'" unfolding min_sol_ineq_sys_comm_def by blast
  with ls'_regular show ?thesis by blast
qed



theorem Parikh: "CFL (TYPE('n)) L \<Longrightarrow> \<exists>L'. regular_lang L' \<and> parikh_img L = parikh_img L'"
proof -
  assume "CFL (TYPE('n)) L"
  then obtain P and S::'n where *: "L = Lang P S \<and> finite P" unfolding CFL_def by blast
  show ?thesis
  proof (cases "S \<in> Nts P")
    case True
    from * finite_Nts exists_mapping obtain \<gamma> \<gamma>' where **: "mapping_Nt_Var (Nts P) \<gamma> \<gamma>'" by metis

    let ?sol = "\<lambda>i. if i < card (Nts P) then CFL.Lang P (\<gamma> i) else {}"
    from ** True have "\<gamma>' S < card (Nts P)" "\<gamma> (\<gamma>' S) = S"
      unfolding mapping_Nt_Var_def bij_betw_def by auto
    with CFL_Lang_eq_CFG_Lang have ***: "Lang P S = ?sol (\<gamma>' S)" by metis

    from * ** CFG_eq_sys.CFL_is_min_sol obtain sys
      where sys_intro: "(\<forall>eq \<in> set sys. regular_fun eq) \<and> (\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys)
                        \<and> min_sol_ineq_sys sys ?sol"
      unfolding CFG_eq_sys_def by blast
    with min_sol_min_sol_comm have sol_is_min_sol: "min_sol_ineq_sys_comm sys ?sol" by fast
    from sys_intro exists_minimal_reg_sol_sys obtain sol' where
      sol'_intro: "min_sol_ineq_sys_comm sys sol' \<and> regular_lang (sol' (\<gamma>' S))" by fastforce
    with sol_is_min_sol min_sol_comm_unique have "parikh_img (?sol (\<gamma>' S)) = parikh_img (sol' (\<gamma>' S))"
      by blast
    with * *** sol'_intro show ?thesis by auto
  next
    case False
    with Nts_Lhss_Rhs_Nts have "S \<notin> Lhss P" by fast
    from Lang_empty_if_notin_Lhss[OF this] * show ?thesis by (metis lang.simps(1))
  qed
qed


end
