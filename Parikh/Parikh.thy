theory Parikh
  imports 
    "../CFG"
    "../CFL"
    "$AFP/Regular-Sets/Regular_Set"
    "$AFP/Regular-Sets/Regular_Exp"
begin


section \<open>functions of languages\<close>

datatype 'a lfun = V nat
                 | N "'a lang"
                 | Union2 "'a lfun" "'a lfun"
                 | UnionC "nat \<Rightarrow> 'a lfun"
                 | Conc "'a lfun" "'a lfun"
                 | Star "'a lfun"

type_synonym 'a state = "nat \<Rightarrow> 'a lang"

primrec eval :: "'a lfun \<Rightarrow> 'a state \<Rightarrow> 'a lang" where
  "eval (V n) s = s n" |
  "eval (N l) _ = l" |
  "eval (Union2 f g) s = eval f s \<union> eval g s" |
  "eval (UnionC f) s = (\<Union>i. eval (f i) s)" |
  "eval (Conc f g) s = eval f s @@ eval g s" |
  "eval (Star f) s = star (eval f s)"

primrec vars :: "'a lfun \<Rightarrow> nat set" where
  "vars (V n) = {n}" |
  "vars (N _) = {}" |
  "vars (Union2 f g) = vars f \<union> vars g" |
  "vars (UnionC f) = (\<Union>i. vars (f i))" |
  "vars (Conc f g) = vars f \<union> vars g" |
  "vars (Star f) = vars f"

primrec subst :: "'a lfun \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> 'a lfun" where
  "subst (V n) s = s n" |
  "subst (N l) _ = N l" |
  "subst (Union2 f g) s = Union2 (subst f s) (subst g s)" |
  "subst (UnionC f) s = UnionC (\<lambda>i. subst (f i) s)" |
  "subst (Conc f g) s = Conc (subst f s) (subst g s)" |
  "subst (Star f) s = Star (subst f s)"


section \<open>Regular functions\<close>

inductive regular_fun :: "'a lfun \<Rightarrow> bool" where
  "regular_fun (V _)" |
  "regular_lang l \<Longrightarrow> regular_fun (N l)" |
  "\<lbrakk> regular_fun f; regular_fun g \<rbrakk> \<Longrightarrow> regular_fun (Union2 f g)" |
  "\<lbrakk> regular_fun f; regular_fun g \<rbrakk> \<Longrightarrow> regular_fun (Conc f g)" |
  "regular_fun f \<Longrightarrow> regular_fun (Star f)"

lemma regular_fun_regular:
  assumes "regular_fun f"
      and "n \<in> vars f \<Longrightarrow> regular_lang (s n)"
    shows "regular_lang (eval f s)"
  sorry

lemma regular_fun_mono:
  assumes "regular_fun f"
      and "\<forall>i. s i \<subseteq> s' i"
    shows "eval f s \<subseteq> eval f s'"
  sorry


section \<open>Parikh image\<close>

definition parikh_vec :: "'t list \<Rightarrow> ('t \<Rightarrow> nat)" where
  "parikh_vec xs c = length (filter (\<lambda>x. c = x) xs)"

definition parikh_img :: "'t lang \<Rightarrow> ('t \<Rightarrow> nat) set" where
  "parikh_img L = { parikh_vec w | w. w \<in> L }"

(* TODO: really necessary? *)
definition subseteq_comm :: "'t lang \<Rightarrow> 't lang \<Rightarrow> bool" where
  "subseteq_comm L1 L2 \<equiv> parikh_img L1 \<subseteq> parikh_img L2"


section \<open>systems of equations\<close>

type_synonym 'a eq_sys = "'a lfun list"

(* sys independent on variables \<le> n *)
definition indep :: "'a eq_sys \<Rightarrow> nat \<Rightarrow> bool" where
  "indep sys n \<equiv> \<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x > n"

definition solves_ineq_sys :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_ineq_sys sys s \<equiv> \<forall>i < length sys. eval (sys ! i) s \<subseteq> s i"

definition solves_eq_sys :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_eq_sys sys s \<equiv> \<forall>i < length sys. eval (sys ! i) s = s i"

definition solves_ineq_sys_comm :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_ineq_sys_comm sys s \<equiv> \<forall>i < length sys. parikh_img (eval (sys ! i) s) \<subseteq> parikh_img (s i)"

definition solves_eq_sys_comm :: "'a eq_sys \<Rightarrow> 'a state \<Rightarrow> bool" where
  "solves_eq_sys_comm sys s \<equiv> \<forall>i < length sys. parikh_img (eval (sys ! i) s) = parikh_img (s i)"

definition sys_subst :: "'a eq_sys \<Rightarrow> (nat \<Rightarrow> 'a lfun) \<Rightarrow> 'a eq_sys" where
  "sys_subst sys s \<equiv> map (\<lambda>eq. subst eq s) sys"

definition partial_sol :: "'a eq_sys \<Rightarrow> 'a eq_sys \<Rightarrow> bool" where
  "partial_sol sys sol \<equiv> length sol = length sys \<and> indep sol (length sys - 1)
                  \<and> (\<forall>s. solves_eq_sys_comm (sys_subst sys (\<lambda>i. if i < length sys then sol ! i else V i)) s)"


section \<open>Lemma 1\<close>

(* TODO: change this, probably remove locale *)
locale tmp =
  fixes f_sys :: "'a eq_sys"
  fixes m :: nat
  fixes r :: nat
  assumes "r \<le> m"
  assumes "length f_sys = r+1"
  assumes f_regular: "\<forall>eq \<in> set f_sys. regular_fun eq"
begin

fun g_pre :: "nat \<Rightarrow> nat \<Rightarrow> 'a lfun" where
  "g_pre _ 0 = N {}" |
  "g_pre i (Suc n) = subst (f_sys ! i) (\<lambda>j. if j \<le> r then g_pre j n else V j)"

definition g :: "nat \<Rightarrow> 'a lfun" where
  "g i \<equiv> UnionC (\<lambda>n. g_pre i n)"

(* The lemma from the paper *)
lemma lemma1: "\<exists>g_sys. length g_sys = r+1 \<and> indep g_sys r
                \<and> (solves_ineq_sys f_sys s \<longrightarrow> solves_ineq_sys g_sys s)
                \<and> (solves_eq_sys g_sys s \<longrightarrow> solves_eq_sys f_sys s)"
  sorry

(* TODO: really necessary *)
definition eq_sys_subseteq :: "'a eq_sys \<Rightarrow> 'a eq_sys \<Rightarrow> bool" where
  "eq_sys_subseteq gs gs' \<equiv> (\<forall>s. \<forall>i\<le>r. subseteq_comm (eval (gs ! i) s) (eval (gs' ! i) s))"

lemma lemma2_aux:
  assumes "regular_fun f0"
  shows "\<exists>g0. regular_fun g0 \<and> partial_sol [f0] [g0]
            \<and> (\<forall>g0'. partial_sol [f0] [g0'] \<longrightarrow>
                (\<forall>s. parikh_img (eval g0 s) \<subseteq> parikh_img (eval g0' s)))"
  sorry

(* The theorem from the paper *)
lemma lemma2: "\<exists>gs. (\<forall>g \<in> set gs. regular_fun g) \<and> partial_sol f_sys gs
                  \<and> (\<forall>gs'. partial_sol f_sys gs' \<longrightarrow> eq_sys_subseteq gs gs')"
  sorry

lemma
  assumes "r = m"
  shows "\<exists>s. (\<forall>i. regular_lang (s i)) \<and> solves_eq_sys_comm f_sys s
          \<and> (\<forall>s'. solves_eq_sys_comm f_sys s' \<longrightarrow> (\<forall>i. parikh_img (s' i) \<subseteq> parikh_img (s i)))"
  sorry

end


end