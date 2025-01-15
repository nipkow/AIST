theory Pilling
  imports 
    "../CFG"
    "../CFL"
    "./Lfun"
    "./Parikh_Img"
    "$AFP/Regular-Sets/Regular_Set"
    "$AFP/Regular-Sets/Regular_Exp"
begin

section \<open>systems of equations\<close>

(* We just represent the right hand sides *)
type_synonym 'a eq_sys = "'a lfun list"

(* sys independent on variables \<le> n *)
definition indep_ub :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> bool" where
  "indep_ub sys n \<equiv> \<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x > n"

(* sys independent on variables \<ge> n *)
definition indep_lb :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> bool" where
  "indep_lb sys n \<equiv> \<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < n"

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

(* partial solution with \<subseteq>, only caring about the Parikh image *)
definition partial_sol_ineq :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "partial_sol_ineq x eq sol \<equiv> (\<forall>s.
    parikh_img (eval (subst eq (\<lambda>i. if i = x then sol else V i)) s) \<subseteq> parikh_img (eval sol s)
  )"

(* partial solution with =, only caring about the Parikh image *)
definition partial_sol_eq :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "partial_sol_eq x eq sol \<equiv> (\<forall>s.
    parikh_img (eval (subst eq (\<lambda>i. if i = x then sol else V i)) s) = parikh_img (eval sol s)
  )"

(* minimal (partial) solution of a single equation with = *)
definition partial_min_reg_sol_eq :: "nat \<Rightarrow> 'a lfun \<Rightarrow> 'a lfun \<Rightarrow> bool" where
  "partial_min_reg_sol_eq x eq sol \<equiv>
    regular_fun sol \<and> x \<notin> vars sol \<and> partial_sol_eq x eq sol
      \<and> (\<forall>sol'. x \<notin> vars sol' \<and> partial_sol_ineq x eq sol'
                \<longrightarrow> (\<forall>s. parikh_img (eval sol s) \<subseteq> parikh_img (eval sol' s)))"


lemma partial_sol_ineq_solves_ineq_comm:
  "partial_sol_ineq x eq sol \<longleftrightarrow> (\<forall>s. solves_ineq_comm x eq (s(x := eval sol s)))"
proof
  show "partial_sol_ineq x eq sol \<Longrightarrow> \<forall>s. solves_ineq_comm x eq (s(x := eval sol s))"
  proof
    fix s
    assume "partial_sol_ineq x eq sol"
    then have
      s_sol: "parikh_img (eval (subst eq (\<lambda>i. if i = x then sol else V i)) s) \<subseteq> parikh_img (eval sol s)"
      unfolding partial_sol_ineq_def by auto
    show "solves_ineq_comm x eq (s(x := eval sol s))"
      unfolding solves_ineq_comm_def using substitution_lemma
      by (smt (verit) eval.simps(1) fun_upd_other fun_upd_same s_sol)
  qed
  show "\<forall>s. solves_ineq_comm x eq (s(x := eval sol s)) \<Longrightarrow> partial_sol_ineq x eq sol"
  proof -
    assume as: "\<forall>s. solves_ineq_comm x eq (s(x := eval sol s))"
    show "partial_sol_ineq x eq sol"
    unfolding partial_sol_ineq_def proof
      fix s
      let ?s' = "s(x := eval sol s)"
      from as have "parikh_img (eval eq ?s') \<subseteq> parikh_img (?s' x)"
        unfolding solves_ineq_comm_def by blast
      then show "parikh_img (eval (subst eq (\<lambda>i. if i = x then sol else V i)) s) \<subseteq> parikh_img (eval sol s)"
        using substitution_lemma by (smt (verit) eval.simps(1) fun_upd_other fun_upd_same)
    qed
  qed
qed



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
  also have "\<dots> \<subseteq> eval (f_sys ! i) ?s_Suc" using s_subseteq_s_Suc lfun_mono_aux[of ?s ?s_Suc] by auto
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
    shows "\<exists>g_sys. length g_sys = length f_sys \<and> indep_ub g_sys (length f_sys - 1)
                \<and> (\<forall>s. solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys g_sys s)
                \<and> (\<forall>s. solves_eq_sys g_sys s \<longrightarrow> solves_eq_sys f_sys s)"
proof -
  let ?g_sys = "map (\<lambda>i. g f_sys i) [0..<length f_sys]"
  have length_g_sys: "length ?g_sys = length f_sys" by auto
  have indep_g_sys: "indep_ub ?g_sys (length f_sys - 1)"
    unfolding indep_ub_def using g_indep by fastforce

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

lemma emptyset_regular: "regular_fun (N {})"
  using lang.simps(1) by blast

lemma epsilon_regular: "regular_fun (N {[]})"
  using lang.simps(2) by blast


(* Every regular function can be represented in form (3),
   as long as we only care for the Parikh image
*)
lemma regular_fun_regular_fun': "regular_fun f \<Longrightarrow>
    \<exists>f'. regular_fun' x f' \<and> (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))"
proof (induction rule: regular_fun.induct)
  case (Variable y)
  then show ?case
  proof (cases "x=y")
    let ?f' = "Union2 (N {}) (Conc (N {[]}) (V x))"
    case True
    then have "regular_fun' x ?f'"
      unfolding regular_fun'_def by (simp add: emptyset_regular epsilon_regular)
    moreover have "eval ?f' s = eval (V y) s" for s :: "'a state"
      using True by simp
    ultimately show ?thesis by metis
  next
    let ?f' = "Union2 (V y) (Conc (N {}) (V x))"
    case False
    then have "regular_fun' x ?f'"
      unfolding regular_fun'_def by (auto simp add: emptyset_regular epsilon_regular)
    moreover have "eval ?f' s = eval (V y) s" for s :: "'a state"
      using False by simp
    ultimately show ?thesis by metis
  qed
next
  case (Const l)
  let ?f' = "Union2 (N l) (Conc (N {}) (V x))"
  have "regular_fun' x ?f'"
    unfolding regular_fun'_def using Const by (auto simp add: emptyset_regular)
  moreover have "eval ?f' s = eval (N l) s" for s :: "'a state" by simp
  ultimately show ?case by metis
next
  case (Union2 f1 f2)
  then obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and>
      (\<forall>s. parikh_img (eval f1 s) = parikh_img (eval f1' s))"
    and f2'_intro: "regular_fun' x f2' \<and> (\<forall>s. parikh_img (eval f2 s) = parikh_img (eval f2' s))"
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
  ultimately show ?case by metis
next
  case (Conc f1 f2)
  then obtain f1' f2' where f1'_intro: "regular_fun' x f1' \<and>
      (\<forall>s. parikh_img (eval f1 s) = parikh_img (eval f1' s))"
    and f2'_intro: "regular_fun' x f2' \<and> (\<forall>s. parikh_img (eval f2 s) = parikh_img (eval f2' s))"
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
  ultimately show ?case by metis
next
  case (Star f)
  then obtain f' where f'_intro: "regular_fun' x f' \<and>
      (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))" by auto
  then obtain p q where p_q_intro: "regular_fun p \<and> regular_fun q \<and>
    f' = Union2 p (Conc q (V x)) \<and> (\<forall>y \<in> vars p. y \<noteq> x)" unfolding regular_fun'_def by auto

  let ?q_new = "Conc (Star p) (Conc (Star (Conc q (V x))) (Conc (Star (Conc q (V x))) q))"
  let ?f_new = "Union2 (Star p) (Conc ?q_new (V x))"

  have "\<forall>s. (parikh_img (eval (Star f) s) = parikh_img (eval ?f_new s))"
  proof (rule allI)
    fix s
    have "parikh_img (eval (Star f) s) = parikh_img (star (eval p s \<union> eval q s @@ s x))"
      using f'_intro parikh_star_distrib_eq p_q_intro
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
  ultimately show ?case by metis
qed



subsection \<open>Minimal solution\<close>

(* We show that F(E)*E (in the following q(p)*p is a minimal solution) *)

(* F(E)*E is a regular function *)
lemma g_star_e_is_reg:
  assumes p_reg:      "regular_fun p"
      and q_reg:      "regular_fun q"
      and x_not_in_p: "x \<notin> vars p"
    shows             "regular_fun (Conc (Star (subst q (\<lambda>y. if y = x then p else V y))) p)"
proof -
  let ?r = "subst q (\<lambda>y. if y = x then p else V y)"
  let ?sol = "Conc (Star ?r) p"

  from p_reg q_reg have r_reg: "regular_fun ?r"
    using subst_reg_fun by (smt (verit, ccfv_threshold) Variable)
  with p_reg show "regular_fun ?sol" by fast
qed


(* F(E)*E is a solution of equation (3) from the paper (with \<supseteq> instead of =) *)
lemma g_star_e_is_sol_ineq:
  assumes p_reg:      "regular_fun p"
      and q_reg:      "regular_fun q"
      and x_not_in_p: "x \<notin> vars p"
    shows             "partial_sol_ineq x (Union2 p (Conc q (V x)))
      (Conc (Star (subst q (\<lambda>y. if y = x then p else V y))) p)" (is "partial_sol_ineq x ?eq _")
unfolding partial_sol_ineq_def proof
  fix s
  let ?r = "subst q (\<lambda>y. if y = x then p else V y)"
  let ?sol = "Conc (Star ?r) p"
  let ?upd = "\<lambda>y. if y = x then ?sol else V y"

  from g_star_e_is_reg[OF assms] have r_reg: "regular_fun ?r" by blast
  have homogeneous_app: "eval (subst q (\<lambda>i. if i = x then ?sol else V i)) s \<subseteq> eval (Conc (Star ?r) ?r) s"
    using reg_fun_homogeneous[OF q_reg r_reg p_reg] by blast

  from x_not_in_p have "eval (subst p ?upd) s = eval p s" using eval_vars_subst[of p] by simp
  then have "parikh_img (eval (subst ?eq (\<lambda>i. if i = x then ?sol else V i)) s) =
      parikh_img (eval p s \<union> eval (subst q (\<lambda>i. if i = x then ?sol else V i)) s @@ eval ?sol s)"
    by simp
  also have "\<dots> \<subseteq> parikh_img (eval p s \<union> eval (Conc (Star ?r) ?r) s @@ eval ?sol s)"
    using homogeneous_app parikh_img_mono by (metis (no_types, lifting) conc_mono order_refl sup.mono)
  also have "\<dots> = parikh_img (eval p s) \<union>
      parikh_img (star (eval ?r s) @@ eval ?r s @@ star (eval ?r s) @@ eval p s)"
    by (simp add: conc_assoc)
  also have "\<dots> = parikh_img (eval p s) \<union>
      parikh_img (eval ?r s @@ star (eval ?r s) @@ eval p s)"
    using parikh_img_commut conc_star_star by (smt (verit, best) conc_assoc conc_star_comm)
  also have "\<dots> = parikh_img (star (eval ?r s) @@ eval p s)"
    using star_unfold_left
    by (smt (verit) conc_Un_distrib(2) conc_assoc conc_epsilon(1) parikh_img_Un sup_commute)
  finally show "parikh_img (eval (subst ?eq (\<lambda>i. if i = x then ?sol else V i)) s)
                \<subseteq> parikh_img (eval ?sol s)" by simp
qed


(* F(E)*E does not contain the variable x *)
lemma g_star_e_indep:
  assumes p_reg:      "regular_fun p"
      and q_reg:      "regular_fun q"
      and x_not_in_p: "x \<notin> vars p"
    shows             "x \<notin> vars (Conc (Star (subst q (\<lambda>y. if y = x then p else V y))) p)" (is "x \<notin> vars ?sol")
proof -
  let ?r = "subst q (\<lambda>y. if y = x then p else V y)"

  from x_not_in_p have "x \<notin> vars ?r" by (simp add: vars_subst)
  with x_not_in_p show "x \<notin> vars ?sol" by simp
qed


(* F(E)*E is the minimal solution *)
lemma g_star_e_is_minimal:
  assumes p_reg:      "regular_fun p"
      and q_reg:      "regular_fun q"
      and x_not_in_p: "x \<notin> vars p"
      and sol_indep:  "x \<notin> vars sol"
      and is_sol:     "partial_sol_ineq x (Union2 p (Conc q (V x))) sol" (is "partial_sol_ineq x ?eq _")
    shows             "parikh_img (eval (Conc (Star (subst q (\<lambda>y. if y = x then p else V y))) p) s)
                       \<subseteq> parikh_img (eval sol s)" (is "parikh_img (eval ?m s) \<subseteq> _")
proof -
  let ?upd = "\<lambda>i. if i = x then sol else V i"
  let ?r = "subst q ?upd"

  from x_not_in_p have "eval (subst p ?upd) s = eval p s" using eval_vars_subst[of p] by simp
  then have "parikh_img (eval p s \<union> eval ?r s @@ eval sol s) = parikh_img (eval (subst ?eq ?upd) s)"
    by simp
  also from is_sol have "\<dots> \<subseteq> parikh_img (eval sol s)" unfolding partial_sol_ineq_def by fast
  finally have eq': "parikh_img (eval p s \<union> eval ?r s @@ eval sol s) \<subseteq> parikh_img (eval sol s)" .
  then have star_eq: "parikh_img (star (eval ?r s) @@ eval p s) \<subseteq> parikh_img (eval sol s)"
    using parikh_img_arden by auto

  from eq' have "parikh_img (eval p s) \<subseteq> parikh_img (eval sol s)" by simp
  then have "parikh_img (eval (if i = x then p else V i) s) \<subseteq>
      parikh_img (eval (if i = x then sol else V i) s)" for i by simp
  then have "parikh_img (eval (subst q (\<lambda>i. if i = x then p else V i)) s) \<subseteq> parikh_img (eval ?r s)"
    using parikh_img_subst_mono by meson
  then have "parikh_img (star (eval (subst q (\<lambda>i. if i = x then p else V i)) s)) \<subseteq>
      parikh_img (star (eval ?r s))" using parikh_star_distrib by blast
  then have "parikh_img (star (eval (subst q (\<lambda>i. if i = x then p else V i)) s) @@ eval p s)
      \<subseteq> parikh_img (star (eval ?r s) @@ eval p s)" using parikh_conc_right_subset by blast
  with star_eq show "parikh_img (eval ?m s) \<subseteq> parikh_img (eval sol s)" by simp
qed


(* F(E)*E solves equation (3) from the paper (this time with =) *)
lemma g_star_e_is_sol_eq:
  assumes p_reg:      "regular_fun p"
      and q_reg:      "regular_fun q"
      and x_not_in_p: "x \<notin> vars p"
    shows             "partial_sol_eq x (Union2 p (Conc q (V x)))
      (Conc (Star (subst q (\<lambda>y. if y = x then p else V y))) p)" (is "partial_sol_eq x ?eq _")
unfolding partial_sol_eq_def proof
  fix s
  let ?r = "subst q (\<lambda>y. if y = x then p else V y)"
  let ?sol = "Conc (Star ?r) p"
  let ?upd = "\<lambda>y. if y = x then ?sol else V y"

  from g_star_e_indep[OF p_reg q_reg x_not_in_p] have "x \<notin> vars ?sol" by simp
  with x_not_in_p have sol_indep: "x \<notin> vars (subst ?eq ?upd)" using vars_subst[of ?eq ?upd] by auto

  have "parikh_img (eval (subst ?eq (\<lambda>y. if y = x then subst ?eq ?upd else V y)) s) \<subseteq> 
        parikh_img (eval (subst ?eq ?upd) s)" for s
  proof -
    fix s
    from g_star_e_is_sol_ineq[OF p_reg q_reg x_not_in_p]
    have "parikh_img (eval (subst ?eq ?upd) s) \<subseteq> parikh_img (eval ?sol s)"
      unfolding partial_sol_ineq_def by blast
    then show "parikh_img (eval (subst ?eq (\<lambda>y. if y = x then subst ?eq ?upd else V y)) s) \<subseteq> 
        parikh_img (eval (subst ?eq ?upd) s)"
      using parikh_img_subst_mono[of "\<lambda>y. if y = x then subst ?eq ?upd else V y" s ?upd ?eq]
      by auto
  qed
  then have "partial_sol_ineq x ?eq (subst ?eq ?upd)" unfolding partial_sol_ineq_def by auto
  then have "parikh_img (eval ?sol s) \<subseteq> parikh_img (eval (subst ?eq ?upd) s)"
    using g_star_e_is_minimal[OF p_reg q_reg x_not_in_p sol_indep] by blast
  with g_star_e_is_sol_ineq[OF p_reg q_reg x_not_in_p]
    show "parikh_img (eval (subst ?eq ?upd) s) = parikh_img (eval ?sol s)"
    unfolding partial_sol_ineq_def by blast
qed


(* Given equation (3), there exists a regular minimal solution *)
lemma exists_minimal_reg_sol_aux:
  assumes p_reg: "regular_fun p"
      and q_reg: "regular_fun q"
      and x_not_in_p: "x \<notin> vars p"
    shows "\<exists>sol. partial_min_reg_sol_eq x (Union2 p (Conc q (V x))) sol"
unfolding partial_min_reg_sol_eq_def proof
  let ?r = "subst q (\<lambda>y. if y = x then p else V y)"
  let ?sol = "Conc (Star ?r) p"
  let ?eq = "Union2 p (Conc q (V x))"

  from g_star_e_is_reg[OF assms] have "regular_fun ?sol" by simp
  moreover from g_star_e_indep[OF assms] have "x \<notin> vars ?sol" by simp
  moreover from g_star_e_is_sol_eq[OF assms] have "partial_sol_eq x ?eq ?sol" by simp
  moreover from g_star_e_is_minimal[OF assms]
    have "x \<notin> vars sol' \<and> partial_sol_ineq x (Union2 p (Conc q (V x))) sol' \<longrightarrow>
      (\<forall>s. parikh_img (eval ?sol s) \<subseteq> parikh_img (eval sol' s))" for sol'
    by simp
  ultimately show "regular_fun ?sol \<and> x \<notin> vars ?sol \<and> partial_sol_eq x (Union2 p (Conc q (V x))) ?sol
            \<and> (\<forall>sol'. x \<notin> vars sol' \<and> partial_sol_ineq x (Union2 p (Conc q (V x))) sol'
                      \<longrightarrow> (\<forall>s. parikh_img (eval ?sol s) \<subseteq> parikh_img (eval sol' s)))" by blast
qed


(* Given equation (2), there exists a regular minimal solution *)
lemma exists_minimal_reg_sol:
  assumes f_reg: "regular_fun f"
  shows "\<exists>sol. partial_min_reg_sol_eq x f sol"
(*  shows "\<exists>sol. regular_fun sol \<and> x \<notin> vars sol \<and> partial_sol_eq x f sol
            \<and> (\<forall>sol'. x \<notin> vars sol' \<and> partial_sol_ineq x f sol'
                      \<longrightarrow> (\<forall>s. parikh_img (eval sol s) \<subseteq> parikh_img (eval sol' s)))"*)
proof -
  from regular_fun_regular_fun'[OF f_reg] obtain f'
    where f'_intro: "regular_fun' x f' \<and> (\<forall>s. parikh_img (eval f s) = parikh_img (eval f' s))"
    by blast
  then obtain p q
    where p_q_intro: "regular_fun p \<and> regular_fun q \<and> f' = Union2 p (Conc q (V x)) \<and> x \<notin> vars p"
    unfolding regular_fun'_def by blast
  then obtain sol where sol_intro: "regular_fun sol \<and> x \<notin> vars sol \<and> partial_sol_eq x f' sol
            \<and> (\<forall>sol'. x \<notin> vars sol' \<and> partial_sol_ineq x f' sol'
                      \<longrightarrow> (\<forall>s. parikh_img (eval sol s) \<subseteq> parikh_img (eval sol' s)))"
    using exists_minimal_reg_sol_aux unfolding partial_min_reg_sol_eq_def by metis

  have "partial_sol_eq x f sol"
  unfolding partial_sol_eq_def proof
    fix s
    let ?s' = "\<lambda>i. if i = x then eval sol s else s i"
    have "parikh_img (eval (subst f (\<lambda>i. if i = x then sol else V i)) s) = parikh_img (eval f ?s')"
      using substitution_lemma[of ?s' "\<lambda>i. if i = x then sol else V i"] by fastforce
    also have "\<dots> = parikh_img (eval f' ?s')" using f'_intro by auto
    also have "\<dots> = parikh_img (eval (subst f' (\<lambda>i. if i = x then sol else V i)) s)"
      using substitution_lemma[of ?s' "\<lambda>i. if i = x then sol else V i"] by fastforce
    finally show "parikh_img (eval (subst f (\<lambda>i. if i = x then sol else V i)) s)
        = parikh_img (eval sol s)" using sol_intro unfolding partial_sol_eq_def by blast
  qed

  moreover have "x \<notin> vars sol' \<and> partial_sol_ineq x f sol'
            \<longrightarrow> (\<forall>s. parikh_img (eval sol s) \<subseteq> parikh_img (eval sol' s))" for sol'
  proof
    fix sol'
    assume as: "x \<notin> vars sol' \<and> partial_sol_ineq x f sol'"

    have "partial_sol_ineq x f' sol'"
    unfolding partial_sol_ineq_def proof
      fix s
      let ?s' = "\<lambda>i. if i = x then eval sol' s else s i"
      have "parikh_img (eval (subst f' (\<lambda>i. if i = x then sol' else V i)) s) = parikh_img (eval f' ?s')"
        using substitution_lemma[of ?s' "\<lambda>i. if i = x then sol' else V i"] by fastforce
      also have "\<dots> = parikh_img (eval f ?s')" using f'_intro by auto
      also have "\<dots> = parikh_img (eval (subst f (\<lambda>i. if i = x then sol' else V i)) s)"
        using substitution_lemma[of ?s' "\<lambda>i. if i = x then sol' else V i"] by fastforce
      finally show "parikh_img (eval (subst f' (\<lambda>i. if i = x then sol' else V i)) s)
          \<subseteq> parikh_img (eval sol' s)" using sol_intro as unfolding partial_sol_ineq_def by blast
    qed

    with sol_intro as show "\<forall>s. parikh_img (eval sol s) \<subseteq> parikh_img (eval sol' s)" by blast
  qed

  ultimately have "regular_fun sol \<and> x \<notin> vars sol \<and> partial_sol_eq x f sol \<and>
    (\<forall>sol'. x \<notin> vars sol' \<and> partial_sol_ineq x f sol'
            \<longrightarrow> (\<forall>s. parikh_img (eval sol s) \<subseteq> parikh_img (eval sol' s)))"
    using sol_intro by blast
  then show ?thesis unfolding partial_min_reg_sol_eq_def by blast
qed


(* Unfortunately, the proof is incomplete
   An proof by induction will prove the theorem in Pilling's paper
*)

(* solve each equation step by step, reducing the variables one by one *)
lemma exists_minimal_reg_sol_sys:
  assumes eqs_reg:    "\<forall>eq \<in> set sys. regular_fun eq"
      and r_valid:    "r \<le> length sys"
    shows             "\<exists>sols. (\<forall>i<r. partial_min_reg_sol_eq i (sys ! i) (sols i)
                              \<and> (\<forall>i\<ge>r. sols i = V i) \<and> (\<forall>y \<in> vars (sols i). y \<ge> r))"
using assms proof (induction r)
  case (Suc r)
  then obtain sols where sols_intro: "(\<forall>i<r. partial_min_reg_sol_eq i (sys ! i) (sols i)
       \<and> (\<forall>i\<ge>r. sols i = V i) \<and> (\<forall>y \<in> vars (sols i). y \<ge> r))" by auto

  from sols_intro have sols_reg: "regular_fun (sols i)" for i sorry

  have "\<exists>sol_r. partial_min_reg_sol_eq r (sys ! r) sol_r \<and> (\<forall>y\<in>vars sol_r. y \<ge> Suc r)"
  proof -
    let ?eq' = "subst (sys ! r) sols"
    from sols_reg Suc.prems(2) have "regular_fun ?eq'"
      by (simp add: Suc_le_lessD eqs_reg subst_reg_fun)
    show "\<exists>sol_r. partial_min_reg_sol_eq r (sys ! r) sol_r \<and> (\<forall>y\<in>vars sol_r. y \<ge> Suc r)" sorry
  qed

  then show ?case sorry
qed simp


(* Now, the partial solutions must be substituted, this time backwards.
   Unfortunately, this part is missing.
   The connections to CFGs and the actual Parikh theorem is also missing
 *)



end
