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


section \<open>Special representation of regular functions\<close>

(* We first show that for every regular function f there is a representation of the form
   (3) (see Pilling's paper, we call it regular_fun' in the following)
   that has the same parikh image as f
*)

definition regular_fun' :: "nat \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "regular_fun' x f \<equiv> \<exists>p q. regular_fun p \<and> regular_fun q \<and>
    f = Union2 p (Concat q (Var x)) \<and> x \<notin> vars p"

lemma "regular_fun' x f \<Longrightarrow> regular_fun f"
  unfolding regular_fun'_def by fast


text \<open>Every regular function can be represented as regular_fun':\<close>

lemma regular_fun_regular_fun'_Variable: "\<exists>f'. regular_fun' x f' \<and> vars f' = vars (Var y) \<union> {x}
                                        \<and> (\<forall>v. parikh_img (eval (Var y) v) = parikh_img (eval f' v))"
proof (cases "x = y")
let ?f' = "Union2 (Const {}) (Concat (Const {[]}) (Var x))"
  case True
  then have "regular_fun' x ?f'"
    unfolding regular_fun'_def by (simp add: emptyset_regular epsilon_regular)
  moreover have "eval ?f' v = eval (Var y) v" for v :: "'a valuation" using True by simp
  moreover have "vars ?f' = vars (Var y) \<union> {x}" using True by simp
  ultimately show ?thesis by metis
next
  let ?f' = "Union2 (Var y) (Concat (Const {}) (Var x))"
  case False
  then have "regular_fun' x ?f'"
    unfolding regular_fun'_def by (auto simp add: emptyset_regular epsilon_regular)
  moreover have "eval ?f' v = eval (Var y) v" for v :: "'a valuation" using False by simp
  moreover have "vars ?f' = vars (Var y) \<union> {x}" by simp
  ultimately show ?thesis by metis
qed

lemma regular_fun_regular_fun'_Const:
  assumes "\<exists>r. Regular_Exp.lang r = l"
    shows "\<exists>f'. regular_fun' x f' \<and> vars f' = vars (Const l) \<union> {x}
                \<and> (\<forall>v. parikh_img (eval (Const l) v) = parikh_img (eval f' v))"
proof -
  let ?f' = "Union2 (Const l) (Concat (Const {}) (Var x))"
  have "regular_fun' x ?f'"
    unfolding regular_fun'_def using assms by (auto simp add: emptyset_regular)
  moreover have "eval ?f' v = eval (Const l) v" for v :: "'a valuation" by simp
  moreover have "vars ?f' = vars (Const l) \<union> {x}" by simp 
  ultimately show ?thesis by metis
qed

lemma regular_fun_regular_fun'_Union2:
  assumes "\<exists>f'. regular_fun' x f' \<and> vars f' = vars f1 \<union> {x} \<and>
                (\<forall>v. parikh_img (eval f1 v) = parikh_img (eval f' v))"
          "\<exists>f'. regular_fun' x f' \<and> vars f' = vars f2 \<union> {x} \<and>
                (\<forall>v. parikh_img (eval f2 v) = parikh_img (eval f' v))"
    shows "\<exists>f'. regular_fun' x f' \<and> vars f' = vars (Union2 f1 f2) \<union> {x} \<and>
                (\<forall>v. parikh_img (eval (Union2 f1 f2) v) = parikh_img (eval f' v))"
proof -
  from assms obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and> vars f1' = vars f1 \<union> {x} \<and>
      (\<forall>v. parikh_img (eval f1 v) = parikh_img (eval f1' v))"
    and f2'_intro: "regular_fun' x f2' \<and> vars f2' = vars f2 \<union> {x} \<and>
      (\<forall>v. parikh_img (eval f2 v) = parikh_img (eval f2' v))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "regular_fun p1 \<and> regular_fun q1 \<and>
    f1' = Union2 p1 (Concat q1 (Var x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "regular_fun p2 \<and> regular_fun q2 \<and> f2' = Union2 p2 (Concat q2 (Var x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?f' = "Union2 (Union2 p1 p2) (Concat (Union2 q1 q2) (Var x))"
  have "regular_fun' x ?f'" unfolding regular_fun'_def using p1_q1_intro p2_q2_intro by auto
  moreover have "parikh_img (eval ?f' v) = parikh_img (eval (Union2 f1 f2) v)" for v
    using p1_q1_intro p2_q2_intro f1'_intro f2'_intro
    by (simp add: conc_Un_distrib(2) sup_assoc sup_left_commute)
  moreover from f1'_intro f2'_intro p1_q1_intro p2_q2_intro
    have "vars ?f' = vars (Union2 f1 f2) \<union> {x}" by auto
  ultimately show ?thesis by metis
qed

lemma regular_fun_regular_fun'_Concat:
  assumes "\<exists>f'. regular_fun' x f' \<and> vars f' = vars f1 \<union> {x} \<and>
                (\<forall>v. parikh_img (eval f1 v) = parikh_img (eval f' v))"
          "\<exists>f'. regular_fun' x f' \<and> vars f' = vars f2 \<union> {x} \<and>
                (\<forall>v. parikh_img (eval f2 v) = parikh_img (eval f' v))"
    shows "\<exists>f'. regular_fun' x f' \<and> vars f' = vars (Concat f1 f2) \<union> {x} \<and>
                (\<forall>v. parikh_img (eval (Concat f1 f2) v) = parikh_img (eval f' v))"
proof -
  from assms obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and> vars f1' = vars f1 \<union> {x} \<and>
      (\<forall>v. parikh_img (eval f1 v) = parikh_img (eval f1' v))"
    and f2'_intro: "regular_fun' x f2' \<and> vars f2' = vars f2 \<union> {x} \<and>
      (\<forall>v. parikh_img (eval f2 v) = parikh_img (eval f2' v))"
    by auto
  then obtain p1 q1 p2 q2 where p1_q1_intro: "regular_fun p1 \<and> regular_fun q1 \<and>
    f1' = Union2 p1 (Concat q1 (Var x)) \<and> (\<forall>y \<in> vars p1. y \<noteq> x)"
    and p2_q2_intro: "regular_fun p2 \<and> regular_fun q2 \<and> f2' = Union2 p2 (Concat q2 (Var x)) \<and>
    (\<forall>y \<in> vars p2. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?q' = "Union2 (Concat q1 (Concat (Var x) q2)) (Union2 (Concat p1 q2) (Concat q1 p2))"
  let ?f' = "Union2 (Concat p1 p2) (Concat ?q' (Var x))"

  have "\<forall>v. (parikh_img (eval (Concat f1 f2) v) = parikh_img (eval ?f' v))"
  proof (rule allI)
    fix v
    have f2_subst: "parikh_img (eval f2 v) = parikh_img (eval p2 v \<union> eval q2 v @@ v x)"
      using p2_q2_intro f2'_intro by auto

    have "parikh_img (eval (Concat f1 f2) v) = parikh_img ((eval p1 v \<union> eval q1 v @@ v x) @@ eval f2 v)"
      using p1_q1_intro f1'_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(5) parikh_conc_right)
    also have "\<dots> = parikh_img (eval p1 v @@ eval f2 v \<union> eval q1 v @@ v x @@ eval f2 v)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = parikh_img (eval p1 v @@ (eval p2 v \<union> eval q2 v @@ v x)
        \<union> eval q1 v @@ v x @@ (eval p2 v \<union> eval q2 v @@ v x))"
      using f2_subst by (smt (verit, ccfv_threshold) parikh_conc_right parikh_img_Un parikh_img_commut)
    also have "\<dots> = parikh_img (eval p1 v @@ eval p2 v \<union> (eval p1 v @@ eval q2 v @@ v x \<union>
        eval q1 v @@ eval p2 v @@ v x \<union> eval q1 v @@ v x @@ eval q2 v @@ v x))"
      using parikh_img_commut by (smt (z3) conc_Un_distrib(1) parikh_conc_right parikh_img_Un sup_assoc)
    also have "\<dots> = parikh_img (eval p1 v @@ eval p2 v \<union> (eval p1 v @@ eval q2 v \<union>
        eval q1 v @@ eval p2 v \<union> eval q1 v @@ v x @@ eval q2 v) @@ v x)"
      by (simp add: conc_Un_distrib(2) conc_assoc)
    also have "\<dots> = parikh_img (eval ?f' v)"
      by (simp add: Un_commute)
    finally show "parikh_img (eval (Concat f1 f2) v) = parikh_img (eval ?f' v)" .
  qed
  moreover have "regular_fun' x ?f'" unfolding regular_fun'_def using p1_q1_intro p2_q2_intro by auto
  moreover from f1'_intro f2'_intro p1_q1_intro p2_q2_intro
    have "vars ?f' = vars (Concat f1 f2) \<union> {x}" by auto
  ultimately show ?thesis by metis
qed

lemma regular_fun_regular_fun'_Star:
  assumes "\<exists>f'. regular_fun' x f' \<and> vars f' = vars f \<union> {x}
                \<and> (\<forall>v. parikh_img (eval f v) = parikh_img (eval f' v))"
  shows "\<exists>f'. regular_fun' x f' \<and> vars f' = vars (Star f) \<union> {x}
                \<and> (\<forall>v. parikh_img (eval (Star f) v) = parikh_img (eval f' v))"
proof -
  from assms obtain f' where f'_intro: "regular_fun' x f' \<and> vars f' = vars f \<union> {x} \<and>
      (\<forall>v. parikh_img (eval f v) = parikh_img (eval f' v))" by auto
  then obtain p q where p_q_intro: "regular_fun p \<and> regular_fun q \<and>
    f' = Union2 p (Concat q (Var x)) \<and> (\<forall>y \<in> vars p. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?q_new = "Concat (Star p) (Concat (Star (Concat q (Var x))) (Concat (Star (Concat q (Var x))) q))"
  let ?f_new = "Union2 (Star p) (Concat ?q_new (Var x))"

  have "\<forall>v. (parikh_img (eval (Star f) v) = parikh_img (eval ?f_new v))"
  proof (rule allI)
    fix v
    have "parikh_img (eval (Star f) v) = parikh_img (star (eval p v \<union> eval q v @@ v x))"
      using f'_intro parikh_star_mono_eq p_q_intro
      by (metis eval.simps(1) eval.simps(3) eval.simps(5) eval.simps(6))
    also have "\<dots> = parikh_img (star (eval p v) @@ star (eval q v @@ v x))"
      using parikh_img_star by blast
    also have "\<dots> = parikh_img (star (eval p v) @@
        star ({[]} \<union> star (eval q v @@ v x) @@ eval q v @@ v x))"
      by (metis Un_commute conc_star_comm star_idemp star_unfold_left)
    also have "\<dots> = parikh_img (star (eval p v) @@ star (star (eval q v @@ v x) @@ eval q v @@ v x))"
      by auto
    also have "\<dots> = parikh_img (star (eval p v) @@ ({[]} \<union> star (eval q v @@ v x)
        @@ star (eval q v @@ v x) @@ eval q v @@ v x))"
      using parikh_img_star2 parikh_conc_left by blast
    also have "\<dots> = parikh_img (star (eval p v) @@ {[]} \<union> star (eval p v) @@ star (eval q v @@ v x)
        @@ star (eval q v @@ v x) @@ eval q v @@ v x)" by (metis conc_Un_distrib(1))
    also have "\<dots> = parikh_img (eval ?f_new v)" by (simp add: conc_assoc)
    finally show "parikh_img (eval (Star f) v) = parikh_img (eval ?f_new v)" .
  qed
  moreover have "regular_fun' x ?f_new" unfolding regular_fun'_def using p_q_intro by fastforce
  moreover from f'_intro p_q_intro have "vars ?f_new = vars (Star f) \<union> {x}" by auto
  ultimately show ?thesis by metis
qed

(* Every regular function can be represented in form (3),
   as long as we only care for the Parikh image
*)
lemma regular_fun_regular_fun': "regular_fun f \<Longrightarrow>
    \<exists>f'. regular_fun' x f' \<and> vars f' = vars f \<union> {x} \<and>
         (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))"
proof (induction rule: regular_fun.induct)
  case (Variable uu)
  from regular_fun_regular_fun'_Variable show ?case by blast
next
  case (Const l)
  from regular_fun_regular_fun'_Const[OF this] show ?case by blast
next
  case (Union2 f g)
  from regular_fun_regular_fun'_Union2[OF this(3,4)] show ?case by blast
next
  case (Concat f g)
  from regular_fun_regular_fun'_Concat[OF this(3,4)] show ?case by blast
next
  case (Star f)
  from regular_fun_regular_fun'_Star[OF this(2)] show ?case by blast
qed


section \<open>Minimal solution\<close>

subsection \<open>Minimal solution for a single equation\<close>

(* We show that F(E)*E (in the following q(p)*p is a minimal solution) *)

locale of_form_regular_fun' =
  fixes x :: "nat"
  fixes p :: "'a lfun"
  fixes q :: "'a lfun"
  assumes p_reg:      "regular_fun p"
  assumes q_reg:      "regular_fun q"
  assumes x_not_in_p: "x \<notin> vars p"
begin

abbreviation "eq \<equiv> Union2 p (Concat q (Var x))"
abbreviation "sol \<equiv> Concat (Star (subst (Var(x := p)) q)) p"


(* F(E)*E is a regular function *)
lemma sol_is_reg: "regular_fun sol"
proof -
  from p_reg q_reg have r_reg: "regular_fun (subst (Var(x := p)) q)"
    using subst_reg_fun_update by auto
  with p_reg show "regular_fun sol" by fast
qed


(* F(E)*E contains only variables which also appear in the equation, except x *)
lemma sol_vars: "vars sol \<subseteq> vars eq - {x}"
proof -
  let ?upd = "Var(x := p)"
  let ?subst_q = "subst ?upd q"
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
unfolding partial_sol_ineq_def proof (rule allI, rule impI)
  fix v
  assume x_is_sol: "v x = eval sol v"

  let ?r = "subst (Var (x := p)) q"
  let ?upd = "Var(x := sol)"
  let ?q_subst = "subst ?upd q"
  let ?eq_subst = "subst ?upd eq"

  from sol_is_reg have r_reg: "regular_fun ?r" unfolding fun_upd_def by blast
  have homogeneous_app: "parikh_img (eval ?q_subst v) \<subseteq> parikh_img (eval (Concat (Star ?r) ?r) v)"
    using reg_fun_homogeneous[OF q_reg r_reg p_reg] by blast

  from x_not_in_p have "eval (subst ?upd p) v = eval p v" using eval_vars_subst[of p] by simp
  then have "parikh_img (eval ?eq_subst v) = parikh_img (eval p v \<union> eval ?q_subst v @@ eval sol v)"
    by simp
  also have "\<dots> \<subseteq> parikh_img (eval p v \<union> eval (Concat (Star ?r) ?r) v @@ eval sol v)"
    using homogeneous_app by (metis dual_order.refl parikh_conc_right_subset parikh_img_Un sup.mono)
  also have "\<dots> = parikh_img (eval p v) \<union>
      parikh_img (star (eval ?r v) @@ eval ?r v @@ star (eval ?r v) @@ eval p v)"
    by (simp add: conc_assoc)
  also have "\<dots> = parikh_img (eval p v) \<union>
      parikh_img (eval ?r v @@ star (eval ?r v) @@ eval p v)"
    using parikh_img_commut conc_star_star by (smt (verit, best) conc_assoc conc_star_comm)
  also have "\<dots> = parikh_img (star (eval ?r v) @@ eval p v)"
    using star_unfold_left
    by (smt (verit) conc_Un_distrib(2) conc_assoc conc_epsilon(1) parikh_img_Un sup_commute)
  finally have *: "parikh_img (eval ?eq_subst v) \<subseteq> parikh_img (v x)" using x_is_sol by simp

  from x_is_sol have "v = v(x := eval sol v)" using fun_upd_triv by metis
  then have "eval eq v = eval (subst (Var(x := sol)) eq) v"
    using substitution_lemma_update[where f=eq] by presburger
  with * show "solves_ineq_comm x eq v" unfolding solves_ineq_comm_def by argo
qed


lemma sol_is_minimal:
  assumes is_sol:    "solves_ineq_comm x eq v"
      and sol'_s:    "v x = eval sol' v"
    shows            "parikh_img (eval sol v) \<subseteq> parikh_img (v x)"
proof -
  from is_sol sol'_s have is_sol': "parikh_img (eval q v @@ v x \<union> eval p v) \<subseteq> parikh_img (v x)"
    unfolding solves_ineq_comm_def by simp
  then have 1: "parikh_img (eval (Concat (Star q) p) v) \<subseteq> parikh_img (v x)"
    using parikh_img_arden by auto

  from is_sol' have "parikh_img (eval p v) \<subseteq> parikh_img (eval (Var x) v)" by auto
  then have "parikh_img (eval (subst (Var(x := p)) q) v) \<subseteq> parikh_img (eval q v)"
    using parikh_img_subst_mono_upd by (metis fun_upd_triv subst_id)
  then have "parikh_img (eval (Star (subst (Var(x := p)) q)) v) \<subseteq> parikh_img (eval (Star q) v)"
    using parikh_star_mono by auto
  then have "parikh_img (eval sol v) \<subseteq> parikh_img (eval (Concat (Star q) p) v)"
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
                    (\<forall>v. parikh_img (eval eq v) = parikh_img (eval eq' v))" by blast
  then obtain p q
    where p_q_intro: "regular_fun p \<and> regular_fun q \<and> eq' = Union2 p (Concat q (Var x)) \<and> x \<notin> vars p"
    unfolding regular_fun'_def by blast

  let ?sol = "Concat (Star (subst (Var(x := p)) q)) p"
  from p_q_intro have sol_prop: "regular_fun ?sol \<and> partial_min_sol_one_ineq x eq' ?sol"
    using of_form_regular_fun'.sol_is_minimal_reg_sol unfolding of_form_regular_fun'_def by blast
  with eq'_intro have "partial_min_sol_one_ineq x eq ?sol"
    using same_min_sol_if_same_parikh_img by blast
  with sol_prop show ?thesis by blast
qed


subsection \<open>Minimal solution of the whole equation system\<close>

locale minimal_sol_one_eq =
  fixes r :: nat
    and sys :: "'a eq_sys"
    and sols :: "nat \<Rightarrow> 'a lfun"
    and sol_r :: "'a lfun"
  assumes eqs_reg:      "\<forall>eq \<in> set sys. regular_fun eq"
      and sys_valid:    "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
      and r_valid:      "r < length sys"
      and sols_is_sol:  "partial_min_sol_ineq_sys r sys sols"
      and sols_reg:     "\<forall>i. regular_fun (sols i)"
      and sol_r_is_sol: "partial_min_sol_one_ineq r (subst_sys sols sys ! r) sol_r"
      and sol_r_reg:    "regular_fun sol_r"
begin


abbreviation "sys' \<equiv> subst_sys sols sys"
abbreviation "sols' \<equiv> \<lambda>i. subst (Var(r := sol_r)) (sols i)"


lemma sols'_r: "sols' r = sol_r"
  using sols_is_sol unfolding partial_min_sol_ineq_sys_def by simp


lemma sols'_reg: "\<forall>i. regular_fun (sols' i)"
  using sols_reg sol_r_reg using subst_reg_fun_update by blast


lemma sols'_is_sol: "solution_ineq_sys (take (Suc r) sys) sols'"
unfolding solution_ineq_sys_def proof (rule allI, rule impI)
  fix v
  assume s_sols': "\<forall>x. v x = eval (sols' x) v"

  from sols'_r s_sols' have s_r_sol_r: "v r = eval sol_r v" by simp
  with s_sols' have s_sols: "v x = eval (sols x) v" for x
    using substitution_lemma_update[where f="sols x"] by (auto simp add: fun_upd_idem)
  with sols_is_sol have solves_r_sys: "solves_ineq_sys_comm (take r sys) v"
    unfolding partial_min_sol_ineq_sys_def solution_ineq_sys_def by meson

  have "eval (sys ! r) (\<lambda>y. eval (sols y) v) = eval (sys' ! r) v"
    using substitution_lemma[of "\<lambda>y. eval (sols y) v"]
    by (simp add: r_valid Suc_le_lessD subst_sys_subst)
  with s_sols have "eval (sys ! r) v = eval (sys' ! r) v"
    by (metis (mono_tags, lifting) eval_vars)
  with sol_r_is_sol s_r_sol_r have "parikh_img (eval (sys ! r) v) \<subseteq> parikh_img (v r)"
    unfolding partial_min_sol_one_ineq_def partial_sol_ineq_def solves_ineq_comm_def by simp
  with solves_r_sys show "solves_ineq_sys_comm (take (Suc r) sys) v"
    unfolding solves_ineq_sys_comm_def solves_ineq_comm_def by (auto simp add: less_Suc_eq)
qed


lemma sols'_min: "\<forall>sols2 v2. (\<forall>x. v2 x = eval (sols2 x) v2)
                   \<and> solves_ineq_sys_comm (take (Suc r) sys) v2
                   \<longrightarrow> (\<forall>i. parikh_img (eval (sols' i) v2) \<subseteq> parikh_img (v2 i))"
proof (rule allI | rule impI)+
  fix sols2 v2 i
  assume as: "(\<forall>x. v2 x = eval (sols2 x) v2) \<and> solves_ineq_sys_comm (take (Suc r) sys) v2"

  then have "solves_ineq_sys_comm (take r sys) v2" unfolding solves_ineq_sys_comm_def by fastforce
  with as sols_is_sol have sols_s2: "parikh_img (eval (sols i) v2) \<subseteq> parikh_img (v2 i)" for i
    unfolding partial_min_sol_ineq_sys_def by auto

  have "eval (sys' ! r) v2 = eval (sys ! r) (\<lambda>i. eval (sols i) v2)"
    unfolding subst_sys_def using substitution_lemma[where f="sys ! r"]
    by (simp add: r_valid Suc_le_lessD)
  with sols_s2 have "parikh_img (eval (sys' ! r) v2) \<subseteq> parikh_img (eval (sys ! r) v2)"
    using lfun_mono_parikh[of "sys ! r"] by auto
  with as have "solves_ineq_comm r (sys' ! r) v2"
    unfolding solves_ineq_sys_comm_def solves_ineq_comm_def using r_valid by force
  with as sol_r_is_sol have sol_r_min: "parikh_img (eval sol_r v2) \<subseteq> parikh_img (v2 r)"
    unfolding partial_min_sol_one_ineq_def by blast

  let ?v' = "v2(r := eval sol_r v2)"
  from sol_r_min have "parikh_img (?v' i) \<subseteq> parikh_img (v2 i)" for i by simp
  with sols_s2 show "parikh_img (eval (sols' i) v2) \<subseteq> parikh_img (v2 i)"
    using substitution_lemma_update[where f="sols i"] lfun_mono_parikh[of "sols i" ?v' v2] by force
qed


lemma sols'_vars_gt_r: "\<forall>i \<ge> Suc r. sols' i = Var i"
  using sols_is_sol unfolding partial_min_sol_ineq_sys_def by auto


lemma sols'_vars_leq_r: "\<forall>i < Suc r. \<forall>x \<in> vars (sols' i). x \<ge> Suc r \<and> x < length sys"
proof -
  from sols_is_sol have "\<forall>i < r. \<forall>x \<in> vars (sols i). x \<ge> r \<and> x < length sys"
    unfolding partial_min_sol_ineq_sys_def by simp
  with sols_is_sol have vars_sols: "\<forall>i < length sys. \<forall>x \<in> vars (sols i). x \<ge> r \<and> x < length sys"
    unfolding partial_min_sol_ineq_sys_def by (metis empty_iff insert_iff leI vars.simps(1))
  with sys_valid have "\<forall>x \<in> vars (subst sols (sys ! i)). x \<ge> r \<and> x < length sys" if "i < length sys" for i
    using vars_subst[of sols "sys ! i"] that by (metis UN_E nth_mem)
  then have "\<forall>x \<in> vars (sys' ! i). x \<ge> r \<and> x < length sys" if "i < length sys" for i
    unfolding subst_sys_def using r_valid that by auto
  moreover from sol_r_is_sol have "vars (sol_r) \<subseteq> vars (sys' ! r) - {r}"
    unfolding partial_min_sol_one_ineq_def by simp
  ultimately have vars_sol_r: "\<forall>x \<in> vars sol_r. x > r \<and> x < length sys"
    unfolding partial_min_sol_one_ineq_def using r_valid
    by (metis DiffE insertCI nat_less_le subsetD)
  moreover have "vars (sols' i) \<subseteq> vars (sols i) - {r} \<union> vars sol_r" if "i < length sys" for i
    using vars_subst_upd_upper by meson
  ultimately have "\<forall>x \<in> vars (sols' i). x > r \<and> x < length sys" if "i < length sys" for i
    using vars_sols that by fastforce
  then show ?thesis by (meson r_valid Suc_le_eq dual_order.strict_trans1)
qed


lemma sols'_is_min_sol: "partial_min_sol_ineq_sys (Suc r) sys sols'"
  unfolding partial_min_sol_ineq_sys_def
  using sols'_is_sol sols'_min sols'_vars_gt_r sols'_vars_leq_r
  by blast


lemma exists_min_sol_Suc_r:
  "\<exists>sols'. partial_min_sol_ineq_sys (Suc r) sys sols' \<and> (\<forall>i. regular_fun (sols' i))"
  using sols'_reg sols'_is_min_sol by blast

end


lemma exists_minimal_reg_sol_sys_aux:
  assumes eqs_reg:   "\<forall>eq \<in> set sys. regular_fun eq"
      and sys_valid: "\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys"
      and r_valid:   "r \<le> length sys"   
    shows            "\<exists>sols. partial_min_sol_ineq_sys r sys sols \<and> (\<forall>i. regular_fun (sols i))"
using assms proof (induction r)
  case 0
  have "solution_ineq_sys (take 0 sys) Var"
    unfolding solution_ineq_sys_def solves_ineq_sys_comm_def by simp
  then show ?case unfolding partial_min_sol_ineq_sys_def by auto
next
  case (Suc r)
  then obtain sols where sols_intro: "partial_min_sol_ineq_sys r sys sols \<and> (\<forall>i. regular_fun (sols i))"
    by auto

  let ?sys' = "subst_sys sols sys"
  from eqs_reg Suc.prems have "regular_fun (sys ! r)" by simp
  with sols_intro Suc.prems have sys_r_reg: "regular_fun (?sys' ! r)"
    using subst_reg_fun[of "sys ! r"] subst_sys_subst[of r sys] by simp
  then obtain sol_r where sol_r_intro:
    "regular_fun sol_r \<and> partial_min_sol_one_ineq r (?sys' ! r) sol_r"
    using exists_minimal_reg_sol by blast

  with Suc sols_intro have "minimal_sol_one_eq r sys sols sol_r"
    unfolding minimal_sol_one_eq_def by force
  from minimal_sol_one_eq.exists_min_sol_Suc_r[OF this] show ?case by blast
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
  with sols_intro have "\<exists>l. regular_lang l \<and> (\<forall>v. eval (sols i) v = l)" if "i < length sys" for i
    using that const_fun_regular_lang by metis
  then obtain ls where ls_intro: "\<forall>i < length sys. regular_lang (ls i) \<and> (\<forall>v. eval (sols i) v = ls i)"
    by metis

  let ?ls' = "\<lambda>i. if i < length sys then ls i else {}"
  from ls_intro have ls'_intro:
    "(\<forall>i < length sys. regular_lang (?ls' i) \<and> (\<forall>v. eval (sols i) v = ?ls' i))
     \<and> (\<forall>i \<ge> length sys. ?ls' i = {})" by force
  then have ls'_regular: "regular_lang (?ls' i)" for i by (meson lang.simps(1))

  from ls'_intro sols_intro have "solves_ineq_sys_comm sys ?ls'"
    unfolding partial_min_sol_ineq_sys_def solution_ineq_sys_def
    by (smt (verit) eval.simps(1) linorder_not_less nless_le take_all_iff)
  moreover have "\<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. parikh_img (?ls' x) \<subseteq> parikh_img (sol' x))"
  proof (rule allI, rule impI)
    fix sol' x
    assume as: "solves_ineq_sys_comm sys sol'"

    let ?sol_funs = "\<lambda>i. Const (sol' i)"
    from as have "solves_ineq_sys_comm (take (length sys) sys) sol'" by simp
    moreover have "sol' x = eval (?sol_funs x) sol'" for x by simp
    ultimately show "\<forall>x. parikh_img (?ls' x) \<subseteq> parikh_img (sol' x)"
      using sols_intro unfolding partial_min_sol_ineq_sys_def
      by (smt (verit) empty_subsetI eval.simps(1) ls'_intro parikh_img_mono)
  qed
  ultimately have "min_sol_ineq_sys_comm sys ?ls'" unfolding min_sol_ineq_sys_comm_def by blast
  with ls'_regular show ?thesis by blast
qed



section \<open>Parikh's theorem\<close>

theorem Parikh: "CFL (TYPE('n)) L \<Longrightarrow> \<exists>L'. regular_lang L' \<and> parikh_img L = parikh_img L'"
proof -
  assume "CFL (TYPE('n)) L"
  then obtain P and S::'n where *: "L = Lang P S \<and> finite P" unfolding CFL_def by blast
  show ?thesis
  proof (cases "S \<in> Nts P")
    case True
    from * finite_Nts exists_mapping obtain \<gamma> \<gamma>' where **: "mapping_Nt_Var (Nts P) \<gamma> \<gamma>'" by metis

    let ?sol = "\<lambda>i. if i < card (Nts P) then Lang_lfp P (\<gamma> i) else {}"
    from ** True have "\<gamma>' S < card (Nts P)" "\<gamma> (\<gamma>' S) = S"
      unfolding mapping_Nt_Var_def bij_betw_def by auto
    with Lang_lfp_eq_Lang have ***: "Lang P S = ?sol (\<gamma>' S)" by metis

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
