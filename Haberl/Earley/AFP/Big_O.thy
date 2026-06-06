theory Big_O
imports Main "HOL-Library.Time_Functions"
begin

text \<open>This is a very simple formalization of Big O only on \<open>nat\<close> and only
for the purpose of presenting the complexity bounds for Earley abstractly.\<close>

definition le_O :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool"
where "(le_O Q f g) = (\<exists>c d. \<forall>x. Q x \<longrightarrow> f x \<le> c * g x + d)"

abbreviation O_le :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("(_/ \<le>O _/ IF _)" [50, 1000, 0] 0) where
"O_le f g Q \<equiv> le_O Q f g"

abbreviation O_le_True :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<le>O" 50) where
"O_le_True f g \<equiv> O_le f g (\<lambda>x. True)"

notation (le_O_no_IF output) "O_le" ("(_/ \<le>O/ _)" [50,50] 50)

notation (latex) O_le ("(_/ \<le>\<^bsub>\<^latex>\<open>\\isaconst{\<close>O\<^latex>\<open>}\<close>\<^esub> _/ IF _)" [50, 1000, 0] 0)

lemma standard_BigO_if_le_O:
  fixes m :: "'a \<Rightarrow> nat"
  assumes "O_le_True (f o m) (g o m)" "finite {n. g(n) = 0}" "surj m"
  shows "\<exists>c. \<exists>n0. \<forall>n \<ge> n0. f n \<le> c * g n"
proof -
  from assms(1) obtain c d where cd: "\<And>x. f(m x) \<le> c * g(m x) + d" unfolding le_O_def by auto
  from assms(2) obtain k where k: "\<forall>n \<ge> k. g n \<noteq> 0"
    by (metis (mono_tags, lifting) finite_nat_set_iff_bounded linorder_neq_iff mem_Collect_eq
        order_le_less_trans)
  let ?n0 = "max k (Min (m ` UNIV))"
  have n0: "\<forall>n \<ge> ?n0. g n \<noteq> 0" using k
    using max.bounded_iff by blast
  let ?c = "c+d"
  have "f n \<le> ?c * g n" if asm: "n \<ge> ?n0" for n
  proof -
    obtain x where "m x = n" using \<open>surj m\<close> by (metis surj_def)
    have "d * g n \<ge> d" using n0 asm by auto
    thus ?thesis using n0 cd[of x] asm unfolding add_mult_distrib
      by (metis add.commute \<open>m x = n\<close> add_le_cancel_right le_trans)
  qed
  thus ?thesis by blast
qed

(* SYNTAX *)
definition BigO :: "('a \<Rightarrow> nat * nat * bool) \<Rightarrow> bool"
  where "BigO fgp \<equiv> \<exists>c d. \<forall>x f g p. fgp x = (f,g,p) \<longrightarrow> p \<longrightarrow> f \<le> c*g + d"

syntax
  "_BigO" :: "pttrn \<Rightarrow> bool \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder BIGO\<close>\<close>BIGO _./ _)\<close> [0, 10] 10)
syntax (latex)
  "_BigO" :: "pttrn \<Rightarrow> bool \<Rightarrow> bool"  (\<open>(\<open>indent=3 notation=\<open>binder BIGO\<close>\<close>\<^latex>\<open>\isaconst{\<close>O\<^latex>\<open>}\<close> _./ _)\<close> [0, 10] 10)

syntax_consts "_BigO" \<rightleftharpoons> BigO

definition imp_O :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"imp_O P1 P2 \<equiv> (P1 \<longrightarrow> P2)"

notation (imp_O output) imp_O (infixr \<open>\<longrightarrow>\<close> 25)
(*<*)
notation (imp_O_no_prem output) imp_O ("\<^latex>\<open>\\hide{\<close>_\<^latex>\<open>}\<close>_")
(*>*)
translations "BIGO x. Q" \<rightharpoonup> "CONST BigO (\<lambda>x. Q)"
translations "BIGO x. CONST imp_O p (a \<le> b)" \<leftharpoondown> "CONST BigO (\<lambda>x. (a, b, p))"

lemma BigO_iff_le_O: "BigO (\<lambda>x. (f x, g x, Q x)) = ((\<lambda>x. f x) \<le>O g IF Q)"
by(auto simp: le_O_def BigO_def)

lemma BigO_if_le_O: "(\<lambda>x. f x) \<le>O g IF Q \<Longrightarrow> BigO (\<lambda>x. (f x, g x, Q x))"
by(auto simp: le_O_def BigO_def)

lemma BigO_if_le_O2: "(\<lambda>(x,y). f x y) \<le>O (\<lambda>(x,y). g x y) IF (\<lambda>(x,y). Q x y)
  \<Longrightarrow> BigO (\<lambda>(x,y). (f x y, g x y, Q x y))"
  by(auto simp: le_O_def BigO_def)

lemma BigO_if_le_O3: "(\<lambda>(x,y,z). f x y z) \<le>O (\<lambda>(x,y,z). g x y z) IF (\<lambda>(x,y,z). Q x y z)
  \<Longrightarrow> BigO (\<lambda>(x,y,z). (f x y z, g x y z, Q x y z))"
  by(auto simp: le_O_def BigO_def)

lemma le_O_if_le: "(\<And>x. Q x \<Longrightarrow> f x \<le> g x) \<Longrightarrow> f \<le>O g IF Q"
by (metis add.commute add_0 le_O_def nat_mult_1)

lemma le_O_if_le2: "(\<And>x y. Q x y \<Longrightarrow> f x y \<le> g x y)
 \<Longrightarrow> (\<lambda>(x,y). f x y) \<le>O (\<lambda>(x,y). g x y) IF (\<lambda>(x,y). Q x y)"
  by (simp add: le_O_if_le split_def)

lemma le_O_if_le3: "(\<And>x y z. Q x y z \<Longrightarrow> f x y z \<le> g x y z)
 \<Longrightarrow> (\<lambda>(x,y,z). f x y z) \<le>O (\<lambda>(x,y,z). g x y z) IF (\<lambda>(x,y,z). Q x y z)"
  by (simp add: le_O_if_le split_def)

lemma le_O_trans[trans]: "f \<le>O g IF Q \<Longrightarrow> g \<le>O h IF Q \<Longrightarrow> f \<le>O h IF Q"
apply(clarsimp simp: le_O_def)
subgoal for cg ch dg dh
 apply(rule_tac x="cg*ch" in exI)
 apply(rule_tac x="cg*dh + dg" in exI)
 apply(rule allI)
  subgoal for x
   apply(erule_tac x=x in allE)
   apply(erule_tac x=x in allE)
   apply(simp add: algebra_simps)
   by (metis add_mono_thms_linordered_semiring(2) distrib_left dual_order.trans mult_le_mono2)
 done
done

lemma le_O_trans2[trans]: "f \<le>O g IF Q \<Longrightarrow> g \<le>O h \<Longrightarrow> f \<le>O h IF Q"
  by (metis le_O_def le_O_trans)

lemma le_O_id: "f \<le>O f IF Q"
apply(clarsimp simp: le_O_def)
apply(rule_tac x="1" in exI)
apply(rule_tac x="0" in exI)
by simp

lemma le_O_k: "(\<lambda>_. k) \<le>O (\<lambda>n. f n) IF Q"
apply(clarsimp simp add: le_O_def)
apply(rule_tac x="0" in exI)
apply(rule_tac x="k" in exI)
by simp

lemma le_O_add: "g \<le>O f IF Q1 \<Longrightarrow> h \<le>O f IF Q2 \<Longrightarrow> (\<lambda>x. g x + h x) \<le>O f IF (\<lambda>x. Q1 x \<and> Q2 x)"
apply(clarsimp simp add: le_O_def)
subgoal for cg ch dg dh
 apply(rule_tac x="cg+ch" in exI)
 apply(rule_tac x="dg+dh" in exI)
 apply (clarsimp)
 subgoal for x
  apply(erule_tac x=x in allE)+
  apply(simp add: algebra_simps)
  done
 done
done

corollary le_O_add1: "g \<le>O f IF Q \<Longrightarrow> h \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x + h x) \<le>O f IF Q"
  using le_O_add by fastforce

corollary le_O_add2L: "f \<le>O f' IF Q \<Longrightarrow> (\<lambda>x. f x + g x) \<le>O (\<lambda>x. f' x + g x) IF Q"
  by (simp add: le_O_add1 le_O_if_le le_O_trans)

corollary le_O_add2R: "f \<le>O f' IF Q \<Longrightarrow> (\<lambda>x. g x + f x) \<le>O (\<lambda>x. g x + f' x) IF Q"
  by (simp add: le_O_add1 le_O_if_le le_O_trans)
                               
corollary le_O_Suc1: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. Suc(g x)) \<le>O f IF Q"
  using le_O_add1[where h = "\<lambda>x. 1", OF _ le_O_k]
  by (metis (no_types, lifting) ext Suc_eq_plus1)


lemma le_O_diff: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x - h x) \<le>O f IF Q"
apply(clarsimp simp add: le_O_def)
subgoal for c d
 apply(rule_tac x="c" in exI)
 apply(rule_tac x="d" in exI)
 apply auto
 done
done

lemma le_O_add_R1: "g \<le>O f1 IF Q \<Longrightarrow> g \<le>O (\<lambda>x. f1 x + f2 x) IF Q"
by (meson le_O_if_le le_O_trans nat_le_iff_add)

lemma le_O_add_R2: "g \<le>O f2 IF Q \<Longrightarrow> g \<le>O (\<lambda>x. f1 x + f2 x) IF Q"
by (meson le_O_if_le le_O_trans2 le_add2)

lemma le_O_add_k_L_iff[simp]: "((\<lambda>x. k + f x) \<le>O g IF Q) \<longleftrightarrow> (f \<le>O g IF Q)"
by (metis (no_types, lifting) ext le_O_add1 le_O_add_R2 le_O_id le_O_k le_O_trans)

lemma le_O_plus_k_R_iff[simp]: "(f \<le>O (\<lambda>x. k + g x) IF Q) \<longleftrightarrow> (f \<le>O g IF Q)"
using le_O_add_k_L_iff le_O_id le_O_trans2 by blast

lemma le_O_mult_k: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. k * g x) \<le>O f IF Q"
apply(clarsimp simp add: le_O_def)
 subgoal for c d
 apply(rule_tac x="k*c" in exI)
 apply(rule_tac x="k*d" in exI)
 apply clarsimp
 by (metis add_mult_distrib2 mult.assoc mult_le_mono2)
done

corollary le_O_mult_k2: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x * k) \<le>O f IF Q"
  by (simp add: ab_semigroup_mult_class.mult.commute le_O_mult_k)

lemma le_O_mult: "g1 \<le>O f1 IF Q \<Longrightarrow> g2 \<le>O f2 IF Q \<Longrightarrow>
 (\<lambda>x. g1 x * g2 x) \<le>O (\<lambda>x. f1 x * f2 x) IF (\<lambda>x. Q x \<and> f1 x > 0 \<and> f2 x > 0)"
  apply(clarsimp simp add: le_O_def)
  subgoal for c1 c2 d1 d2
    apply(rule_tac x="c1*c2+c1*d2+c2*d1" in exI)
    apply(rule_tac x="d1*d2" in exI)
    apply clarsimp
    subgoal for x
      apply(erule_tac x=x in allE)+
      apply(simp add: algebra_simps)
      apply(drule (1) mult_mono)
        apply simp_all
      apply(simp add: algebra_simps)
      apply(subgoal_tac "c1 * (d2 * (f1 x * f2 x)) \<ge> c1 * (d2 * f1 x)")
       apply(subgoal_tac "c2 * (d1 * (f1 x * f2 x)) \<ge> c2 * (d1 * f2 x)")
        apply linarith
       apply simp
      apply simp
      done
    done
  done


lemma le_O_multR: assumes "\<And>x. Q x \<Longrightarrow> g' x > 0" shows "g \<le>O g' IF Q \<Longrightarrow>
 (\<lambda>x. f x * g x) \<le>O (\<lambda>x. f x * g' x) IF Q"
apply(clarsimp simp add: le_O_def)
 subgoal for c d
 apply(rule_tac x="c+d" in exI)
 apply(rule_tac x="0" in exI)
 apply clarsimp
 subgoal for x
  apply(erule_tac x=x in allE)
  apply(simp add: algebra_simps)
  apply(subgoal_tac "d \<le> d * g' x")
  apply linarith
  using assms[of x] by simp
 done
done

lemma le_O_multL: assumes "\<And>x. Q x \<Longrightarrow> g' x > 0" shows "g \<le>O g' IF Q \<Longrightarrow>
 (\<lambda>x. g x * f x) \<le>O (\<lambda>x. g' x * f x) IF Q"
  using le_O_multR
  by (metis (no_types, lifting) ext Groups.ab_semigroup_mult_class.mult.commute assms)

lemma le_O_add_mult1: assumes "\<And>x. Q x \<Longrightarrow> g x > 0"
  shows "(\<lambda>x. f x * g x + f x) \<le>O (\<lambda>x. f x * g x) IF Q"
apply(rule le_O_trans[of _ _ "\<lambda>x. f x * (g x + 1)"])
 apply(rule le_O_if_le)
 apply(simp add: algebra_simps)
 apply(rule le_O_multR)
 apply (simp add: assms)
using le_O_add1 le_O_id le_O_k by blast

lemma le_O_mult': "\<lbrakk> \<And>x. f1 x > 0; \<And>x. f2 x > 0; g1 \<le>O f1 IF Q; g2 \<le>O f2 IF Q \<rbrakk> \<Longrightarrow>
 (\<lambda>x. g1 x * g2 x) \<le>O (\<lambda>x. f1 x * f2 x) IF Q"
  using le_O_mult[of Q g1 f1 g2 f2]
  by presburger

lemma le_O_le_power: assumes "k \<le> l" shows "(\<lambda>n. (f n)^k) \<le>O (\<lambda>n. (f n)^l) IF Q"
  unfolding le_O_def [[metis_instantiate]]
  by (metis add.commute assms less_one linorder_not_le nat_mult_1 order_class.order_eq_iff
      power_increasing trans_le_add1)

lemma le_O_id_le_power: "1 \<le> l \<Longrightarrow> (\<lambda>x. m x) \<le>O (\<lambda>x. (m x)^l) IF Q"
using le_O_le_power by fastforce

lemmas le_O_Is = le_O_id le_O_k le_O_Suc1 le_O_add1 le_O_diff le_O_mult_k le_O_mult_k2 le_O_le_power le_O_id_le_power

lemma le_O_sq_plus1: "(\<lambda>x. (f x + 1)^2) \<le>O (\<lambda>x. (f x)^2)"
apply(clarsimp simp: le_O_def)
apply(rule_tac x="2" in exI)
apply(rule_tac x="2" in exI)
apply(simp add: algebra_simps power2_eq_square)
by (metis mult.commute Nat.nat_arith.rule0 mult_0_right
      mult_Suc_right mult_le_mono1 nle_le not_less_eq_eq)

lemma le_O_sq_Suc: "(\<lambda>x. (Suc(f x))^2) \<le>O (\<lambda>x. (f x)^2)"
unfolding Suc_eq_plus1 by(rule le_O_sq_plus1)

lemma plus1_cube_bound: "((n::nat) + 1) ^ 3 \<le> 7 * n ^ 3 + 1"
proof -
  show ?thesis
  proof (cases "n=0")
    case True
    then show ?thesis by simp
  next
    case False
    have "n \<le> n^3" by (simp add: numeral_3_eq_3)
    moreover have "n^2 \<le> n^3" by (simp add: numeral_3_eq_3 numeral_2_eq_2)
    moreover have "((n::nat) + 1) ^ 3 = n^3 + 3*n^2 + 3*n + 1" by(simp add: algebra_simps numeral_eq_Suc)
    ultimately show ?thesis by linarith
  qed
qed

lemma le_O_cube_plus1: "(\<lambda>x. (f x + 1)^3) \<le>O (\<lambda>x. (f x)^3)"
  apply(clarsimp simp: le_O_def)
  apply(rule_tac x=7 in exI)
  apply(rule_tac x=1 in exI)
  apply rule
  subgoal for x
    using plus1_cube_bound[of "f x"]
    by simp
  done

corollary le_O_cube_Suc: "(\<lambda>x. (Suc(f x))^3) \<le>O (\<lambda>x. (f x)^3)"
unfolding Suc_eq_plus1 by(rule le_O_cube_plus1)

lemma le_O_fstI: "f \<le>O g \<Longrightarrow> (\<lambda>p. f(fst p)) \<le>O (\<lambda>p. g(fst p))"
by (simp add: le_O_def)

lemma "(\<lambda>x. 6*x^3 + 3*x^2 + 7*x + 13) \<le>O (\<lambda>n. n^3) IF Q"
  by(simp add: le_O_Is)

subsection \<open>Recursion modulo O\<close>
(* not yet used *)

text \<open>Solving linear recurrences using an O(n^k)-bound for the additive component.\<close>

lemma pow_diff_strong:
  fixes n k :: nat
  shows "n ^ (k+2) + (k+2) * n ^ (k+1) + 1 \<le> (n+1) ^ (k+2)"
proof (induction k)
  case 0
  show ?case by (simp)
next
  case (Suc k)
  let ?l = "n ^ (Suc k + 2) + (Suc k + 2) * n ^ (Suc k + 1) + 1"
  have "?l \<le> ?l + ((k+2) * n ^ (k+1) + n)" by linarith
  also have "\<dots> = (n+1) * (n ^ (k+2) + (k+2) * n ^ (k+1) + 1)"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> (n+1) * (n+1) ^ (k+2)"
    by (rule mult_le_mono2[OF Suc.IH])
  also have "\<dots> = (n+1) ^ (Suc k + 2)"
    by simp
  finally show ?case .
qed

corollary pow_diff_tight:
  fixes n k :: nat
  assumes "1 \<le> k"
  shows "n ^ (k+1) + (k+1) * n ^ k + 1 \<le> (n+1) ^ (k+1)"
  using assms pow_diff_strong[of n "k-1"] by simp

text \<open>Our Master Lemma ;-)\<close>

lemma lin_rec_O_solution:
  fixes f g :: "nat \<Rightarrow> nat"
  assumes "\<And>n. f(Suc n) = f n + g n"
  and "g \<le>O (\<lambda>n. n^k)"
shows "f \<le>O (%n. n^(Suc k))"
proof -
  from assms(2) obtain c d where gn: "\<And>n. g n \<le> c * n^k + d"
    by (metis le_O_def)
  have "f n \<le> (c+d) * n^(k+1) + f 0" for n
  proof (induction n)
    case (Suc n)
    have "f(Suc n) = f n + g n" by(simp add: assms(1))
    also have "f n + g n \<le> (c+d) * n^(k+1) + f 0 + c * n^k + d"
      using Suc.IH gn[of n] by simp
    also have "\<dots> \<le> (c + d) * Suc n ^ (k + 1) + f 0"
    proof (cases)
      assume "k=0" then show ?thesis by simp
    next
      assume "k\<noteq>0"
      with mult_le_mono2[OF pow_diff_tight[of k n], of "c+d"]
      show ?thesis by (simp add: algebra_simps)
    qed
    finally show ?case .
  qed simp
  thus ?thesis
    unfolding le_O_def by auto
qed

text \<open>The following definition is more for convenience (and does not cater for \<open>IF\<close> (yet?)).\<close>

text \<open>Functions \<open>f\<close> and \<open>g\<close> typically operate on \<open>'a = nat\<close>
 and \<open>m\<close> measures the size of the actual input type \<open>'b\<close>.\<close>
definition le_O_measure :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  ("(_/ \<le>O _/ WRT _)" [50, 1000, 0] 0) where
"(f \<le>O g WRT m) = ((f o m) \<le>O (g o m))"

lemma le_O_measureI: "f \<le>O g \<Longrightarrow> f \<le>O g WRT m"
unfolding le_O_measure_def le_O_def by auto


subsubsection \<open>Example: \<open>append\<close>\<close>

text\<open>The \<open>T_append\<close> recursion pattern but now on \<open>nat\<close> instead of \<open>list\<close>.
(Could be reused for other functions, e.g. length.)\<close>

fun T_append_n :: "nat \<Rightarrow> nat" where
"T_append_n 0 = 1" |
"T_append_n (Suc n) = T_append_n n + 1"

text\<open>Is the step of finding \<open>T_f_n\<close> given \<open>T_f\<close> creative? Always possible?\<close>

text \<open>\<open>T_append_n\<close> is correct wrt \<open>T_append\<close>:\<close>
lemma T_append_T_append_n: "T_append xs ys = T_append_n (length xs)"
  by (induction xs) auto
text \<open>The proof is and should be trivial. Otherwise the \<open>_n\<close> variant is probably not quite right.\<close>

text \<open>The complexity of \<open>T_append_n\<close> using our Master Lemma:\<close>

lemma T_append_n_O_id: "T_append_n \<le>O (\<lambda>n. n)"
proof -
  have 1: "(\<lambda>n. 1) \<le>O (\<lambda>n. n ^ 0)"
    by (simp add: le_O_k)
  from lin_rec_O_solution[of T_append_n, OF T_append_n.simps(2) 1]
  show ?thesis by simp
qed

text \<open>Now we start lifting \<open>T_append_n_O_id\<close> to \<open>T_append\<close>.
This should be routine or even automatic.\<close>

lemma T_append_O_id_WRT: "T_append_n \<le>O (\<lambda>n. n) WRT (\<lambda>(xs, ys). length xs)"
  by (simp add: T_append_n_O_id le_O_measureI)

text \<open>The final theorem about the \<open>T_append\<close>:\<close>
corollary T_append_O: "(\<lambda>(xs,ys). T_append xs ys) \<le>O (\<lambda>(xs,ys). length xs)"
  unfolding T_append_T_append_n using T_append_O_id_WRT unfolding le_O_measure_def comp_def
  by (simp add: split_def)


subsubsection \<open>Example: \<open>rev\<close>\<close>

thm T_rev.simps(2)

text \<open>The definition of \<open>T_rev\<close> contains the summand \<open>T_append (rev xs)\<close>.
However, \<open>T_rev_n\<close> operates on \<open>nat\<close>: there is no \<open>xs\<close>. We need to use "the size of \<open>rev xs\<close>".
Luckily, we know that \<open>rev\<close> preserves the length. Thus the following definition works.
Such knowledge about how auxiliary functions change the size of their input will often be necessary.\<close>
fun T_rev_n :: "nat \<Rightarrow> nat" where
"T_rev_n 0 = 1" |
"T_rev_n (Suc n) = T_rev_n n + T_append_n n + 1"

lemma T_rev_T_rev_n: "T_rev xs = T_rev_n (length xs)"
  by (induction xs) (auto simp: T_append_T_append_n)

text \<open>The complexity proof needs a bit of \<open>\<le>0\<close> reasoning (via \<open>le_O_Suc1\<close>).
For more complex functions there could be more of that.\<close>
lemma T_rev_n_O_pow2: "T_rev_n \<le>O (\<lambda>n. n^2)"
proof -
  have *: "T_rev_n (Suc n) = T_rev_n n + (T_append_n n + 1)" for n
    by (simp add: algebra_simps)
  from lin_rec_O_solution[of T_rev_n, OF *, of 1] T_append_n_O_id
  show ?thesis by (simp add: le_O_Suc1 power2_eq_square)
qed

lemma T_rev_O_pow2_WRT: "T_rev_n \<le>O (\<lambda>n. n^2) WRT length"
  by (simp add: T_rev_n_O_pow2 le_O_measureI)

corollary T_rev_O: "T_rev \<le>O (\<lambda>x. (length x)^2)"
  unfolding T_rev_T_rev_n using T_rev_O_pow2_WRT unfolding le_O_measure_def comp_def
  by (simp add: split_def)


subsubsection \<open>Example: \<open>nth\<close>\<close>

thm T_nth.simps

text \<open>This example is trickier because \<open>nth\<close> is a partial function.
Therefore many lemmas a conditional now. There are also two plausible candidates for \<open>T_nth_n\<close>.
Both work equally well.\<close>

text \<open>Variant 1\<close>

fun T_nth_n :: "nat \<Rightarrow> nat" where
"T_nth_n (Suc m) = T_nth_n m + 1"

lemma T_nth_T_nth_n: "n < length xs \<Longrightarrow> T_nth xs n \<le> T_nth_n (length xs)"
  by (induction xs n rule: T_nth.induct) (auto simp: T_nth.simps split: nat.splits)
corollary T_nth_T_nth_n_O:
  "(\<lambda>(xs,n). T_nth xs n) \<le>O (\<lambda>(xs,n). T_nth_n (length xs)) IF (\<lambda>(xs,n). n < length xs)"
by (simp add: T_nth_T_nth_n le_O_if_le2)

lemma T_nth_n_O_id: "T_nth_n \<le>O (\<lambda>m. m)"
proof -
  from lin_rec_O_solution[of T_nth_n "%_. 1" 0, OF T_nth_n.simps]
  show ?thesis by (simp add: le_O_id)
qed

lemma T_nth_n_O_id_WRT: "T_nth_n \<le>O (\<lambda>n. n) WRT (length o fst)"
  by (simp add: T_nth_n_O_id le_O_measureI)

corollary T_nth_O: "(\<lambda>(xs,n). T_nth xs n) \<le>O (\<lambda>(xs,n). length xs) IF (\<lambda>(xs,n). n < length xs)"
  using T_nth_T_nth_n_O T_nth_n_O_id_WRT unfolding le_O_measure_def comp_def split_def
  using le_O_trans2 by blast

text \<open>Variant 2\<close>

fun T_nth_n2 :: "nat \<Rightarrow> nat" where
"T_nth_n2 0 = 1" |
"T_nth_n2 (Suc n) = T_nth_n2 n + 1"

lemma T_nth_T_nth_n2: "n < length xs \<Longrightarrow> T_nth xs n = T_nth_n2 n"
  by (induction xs n rule: T_nth.induct) (auto simp: T_nth.simps split: nat.splits)
corollary T_nth_T_nth_n2_O:
  "(\<lambda>(xs,n). T_nth xs n) \<le>O (\<lambda>(xs,n). T_nth_n2 n) IF (\<lambda>(xs,n). n < length xs)"
by (simp add: T_nth_T_nth_n2 le_O_if_le2)

lemma T_nth_n2_O_id: "T_nth_n2 \<le>O (\<lambda>n. n)"
proof -
  from lin_rec_O_solution[of T_nth_n2 "%_. 1" 0, OF T_nth_n2.simps(2)]
  show ?thesis by (simp add: le_O_id)
qed

lemma T_nth_n2_O_id_WRT: "T_nth_n2 \<le>O (\<lambda>n. n) WRT snd"
  by (simp add: T_nth_n2_O_id le_O_measureI)

corollary T_nth_O2: "(\<lambda>(xs,n). T_nth xs n) \<le>O (\<lambda>(xs,n). n) IF (\<lambda>(xs,n). n < length xs)"
  using T_nth_T_nth_n2_O T_nth_n2_O_id_WRT unfolding le_O_measure_def comp_def split_def
  using le_O_trans2 by blast

end