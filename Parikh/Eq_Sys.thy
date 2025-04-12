theory Eq_Sys
  imports
    "./Lfun"
    "./Parikh_Img"
begin

section \<open>systems of equations\<close>

(* We just represent the right hand sides *)
type_synonym 'a eq_sys = "'a lfun list"

(* sys independent on variables \<le> n *)
definition indep_leq :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> bool" where
  "indep_leq sys n \<equiv> \<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x > n"

(* solves equation with \<subseteq> *)
definition solves_ineq_sys :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_ineq_sys sys s \<equiv> \<forall>i < length sys. eval (sys ! i) s \<subseteq> s i"

(* solves equation with = *)
definition solves_eq_sys :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_eq_sys sys s \<equiv> \<forall>i < length sys. eval (sys ! i) s = s i"

(* solves equation with \<subseteq>, only caring about the Parikh image *)
definition solves_ineq_comm :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_ineq_comm x eq s \<equiv> parikh_img (eval eq s) \<subseteq> parikh_img (s x)"

(* solves equation system with \<subseteq>, only caring about the Parikh image *)
definition solves_ineq_sys_comm :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_ineq_sys_comm sys s \<equiv> \<forall>i < length sys. solves_ineq_comm i (sys ! i) s"

(* solves equation with =, only caring about the Parikh image*)
definition solves_eq_comm :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_eq_comm x eq s \<equiv> parikh_img (eval eq s) = parikh_img (s x)"

(* solves equation system with =, only caring about the Parikh image *)
definition solves_eq_sys_comm :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_eq_sys_comm sys s \<equiv> \<forall>i < length sys. solves_eq_comm i (sys ! i) s"

(* Substituion into each equation of a system *)
definition sys_subst :: "'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> 'a eq_sys" where
  "sys_subst sys s \<equiv> map (\<lambda>eq. subst eq s) sys"

definition partial_sol_ineq :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "partial_sol_ineq x eq sol \<equiv> \<forall>s. s x = eval sol s \<longrightarrow> solves_ineq_comm x eq s"

definition solution_ineq_sys :: "'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> bool" where
  "solution_ineq_sys sys sols \<equiv> \<forall>s. (\<forall>x. s x = eval (sols x) s) \<longrightarrow> solves_ineq_sys_comm sys s"

definition partial_min_sol_ineq_sys :: "nat \<Rightarrow> 'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> bool" where
  "partial_min_sol_ineq_sys n sys sols \<equiv>
    solution_ineq_sys (take n sys) sols \<and>
    (\<forall>i \<ge> n. sols i = V i) \<and>
    (\<forall>i < n. \<forall>x \<in> vars (sols i). x \<ge> n \<and> x < length sys) \<and>
    (\<forall>sols' s'. (\<forall>x. s' x = eval (sols' x) s')
                  \<and> solves_ineq_sys_comm (take n sys) s'
                  \<longrightarrow> (\<forall>i. parikh_img (eval (sols i) s') \<subseteq> parikh_img (s' i)))"


definition partial_min_sol_one_ineq :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "partial_min_sol_one_ineq x eq sol \<equiv>
    partial_sol_ineq x eq sol \<and>
    vars sol \<subseteq> vars eq - {x} \<and>
    (\<forall>sol' s'. solves_ineq_comm x eq s' \<and> s' x = eval sol' s'
               \<longrightarrow> parikh_img (eval sol s') \<subseteq> parikh_img (s' x))"

definition min_sol_ineq_sys :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "min_sol_ineq_sys sys sol \<equiv>
    solves_ineq_sys_comm sys sol \<and>
    (\<forall>sol'. solves_ineq_sys_comm sys sol' \<longrightarrow> (\<forall>x. parikh_img (sol x) \<subseteq> parikh_img (sol' x)))"

(* TODO: currently unused *)
definition partial_sol_eq :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "partial_sol_eq x eq sol \<equiv> \<forall>s. s x = eval sol s \<longrightarrow> solves_eq_comm x eq s"


lemma partial_sol_ineqI:
  assumes "\<And>s. s x = eval sol s \<Longrightarrow> parikh_img (eval (subst eq (V(x := sol))) s) \<subseteq> parikh_img (s x)"
    shows "partial_sol_ineq x eq sol"
unfolding partial_sol_ineq_def solves_ineq_comm_def proof (rule allI, rule impI)
  fix s
  assume x_is_sol: "s x = eval sol s"

  from x_is_sol have "s = s(x := eval sol s)" using fun_upd_triv by metis
  then have "eval eq s = eval (subst eq (V(x := sol))) s"
    using substitution_lemma_update[of eq] by simp
  with assms x_is_sol show "parikh_img (eval eq s) \<subseteq> parikh_img (s x)" by simp
qed


lemma partial_sol_eqI:
  assumes "\<And>s. s x = eval sol s \<Longrightarrow> parikh_img (eval (subst eq (V(x := sol))) s) = parikh_img (s x)"
    shows "partial_sol_eq x eq sol"
unfolding partial_sol_eq_def solves_eq_comm_def proof (rule allI, rule impI)
  fix s
  assume x_is_sol: "s x = eval sol s"
  
  from x_is_sol have "s = s(x := eval sol s)" using fun_upd_triv by metis
  then have "eval eq s = eval (subst eq (V(x := sol))) s"
    using substitution_lemma_update[of eq] by simp
  with assms x_is_sol show "parikh_img (eval eq s) = parikh_img (s x)" by simp
qed


lemma sys_subst_subst:
  assumes "i < length sys"
  shows "(sys_subst sys s) ! i = subst (sys ! i) s"
  unfolding sys_subst_def by (simp add: assms)


(* TODO: currently unused *)
lemma sol_Suc_n_sol_n:
  assumes "solution_ineq_sys (take (Suc n) sys) sols"
  shows "solution_ineq_sys (take n sys) sols"
  using assms unfolding solution_ineq_sys_def solves_ineq_sys_comm_def by auto


lemma same_min_sol_if_same_parikh_img:
  assumes same_parikh_img: "\<forall>s. parikh_img (eval f s) = parikh_img (eval g s)"
      and same_vars:       "vars f - {x} = vars g - {x}"
      and minimal_sol:     "partial_min_sol_one_ineq x f sol"
    shows                  "partial_min_sol_one_ineq x g sol"
proof -
  from minimal_sol have "vars sol \<subseteq> vars g - {x}"
    unfolding partial_min_sol_one_ineq_def using same_vars by blast
  moreover from same_parikh_img minimal_sol have "partial_sol_ineq x g sol"
    unfolding partial_min_sol_one_ineq_def partial_sol_ineq_def solves_ineq_comm_def by simp
  moreover from same_parikh_img minimal_sol have "\<forall>sol' s'. solves_ineq_comm x g s' \<and> s' x = eval sol' s'
               \<longrightarrow> parikh_img (eval sol s') \<subseteq> parikh_img (s' x)"
    unfolding partial_min_sol_one_ineq_def solves_ineq_comm_def by blast
  ultimately show ?thesis unfolding partial_min_sol_one_ineq_def by fast
qed

end
