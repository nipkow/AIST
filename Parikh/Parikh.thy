theory Parikh
  imports 
    "../CFG"
    "../CFL"
    "$AFP/Regular-Sets/Regular_Set"
begin

sledgehammer_params [provers = cvc4 verit z3 spass vampire zipperposition]

section \<open>regular functions\<close>




section \<open>systems of equations\<close>

definition "ineq_sat f i xs \<equiv> ((xs ! i) \<supseteq> f i xs)"
definition "eq_sat f i xs \<equiv> ((xs ! i) = f i xs)"

definition "sat_system_ineq f n xs \<equiv> \<forall>i. (i\<le>n \<longrightarrow> ineq_sat f i xs)"
definition "sat_system_eq f n xs \<equiv> \<forall>i. (i\<le>n \<longrightarrow> eq_sat f i xs)"

locale f_ineq_gs =
  fixes f :: "nat \<Rightarrow> 'a lang list \<Rightarrow> 'a lang"
  fixes m :: nat
  fixes r :: nat
  fixes xs :: "'a lang list"
  fixes ys :: "'a lang list"
  assumes "r \<le> m"
  assumes "length xs = r+1"
  assumes "length ys = m - r"
  assumes f_regular: "True" (* TODO! *)
begin

fun comp_xs_aux :: "nat \<Rightarrow> nat \<Rightarrow> 'a lang list" where
  "comp_xs_aux _ 0 = []"|
  "comp_xs_aux 0 (Suc i) = {}#(comp_xs_aux 0 i)"|
  "comp_xs_aux (Suc n) (Suc i) = (f n ((comp_xs_aux n (length xs))@ys))#(comp_xs_aux (Suc n) i)"

definition "Xs n = comp_xs_aux n (length xs)"

fun g_pre :: "nat \<Rightarrow> nat  \<Rightarrow> 'a lang" where
  "g_pre i 0  = {}"|
  "g_pre i (Suc n) = f i ((Xs n)@ys)"

lemma g_pre_index: "i < length xs \<Longrightarrow> g_pre i n = (comp_xs_aux n i) ! i "
  sorry

definition "g i \<equiv> \<Union>n. g_pre i n"

lemma "g_pre i (Suc n) \<subseteq> f i (xs @ ys)"
proof
  fix x
  assume "x \<in> g_pre i (Suc n)"
  then have "x \<in> f i ((Xs n)@ys)" by auto
  show "x \<in> f i (xs@ys)" sorry
qed
  

lemma lemma1_aux_1:
  assumes f_sub: "\<forall>i\<le>r. (xs ! i) \<supseteq> f i (xs@ys)"
  shows "\<forall>i\<le>r. (xs ! i) \<supseteq> g i"
proof
  fix i
  show "i \<le> r \<longrightarrow> g i \<subseteq> xs ! i"
    proof
      assume "i\<le>r"
      with f_sub have "f i (xs @ ys) \<subseteq> xs ! i" by simp
      show "g i \<subseteq> xs ! i" sorry
    qed
qed
  
lemma lemma1:
  "\<exists>g. ((\<forall>i. (i\<le>r \<longrightarrow> (xs ! i) \<supseteq> f i (xs@ys))) \<longrightarrow> (\<forall>i. (i\<le>r \<longrightarrow> (xs ! i) \<supseteq> g i ys))) \<and>
       ((\<forall>i. (i\<le>r \<longrightarrow> (xs ! i) = g i ys)) \<longrightarrow> (\<forall>i. (i\<le>r \<longrightarrow> (xs ! i) = f i (xs @ ys))))"
  sorry

end


end