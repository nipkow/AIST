(*<*)
theory Paper
imports
  "Earley.EarleyWorklist"
  Sugar
begin
(* set_ItemList \<rightarrow> set_IL *)
(* TODO: localize interpretation in EarleyWorklist *)
declare [[show_question_marks=false]]
declare [[names_short=true]]

type_synonym ('n,'a)item_list = "('n,'a)efficientItemList"
translations (type) "('n,'a)item_list" <= (type) "('n,'a)efficientItemList"

lemma empty_froms_is_replicate: "empty_froms n = replicate (n+1) []"
by(induction n) auto

(*TODO use in def of T_steps *)
definition T_while_option2
  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<times> nat \<Rightarrow> ('a \<times> nat) option" where
"T_while_option2 b f T_f = while_option (\<lambda>(x,n). b x) (\<lambda>(x,n). (f x, n + T_f x))"

definition T_while_option :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> nat" where
"T_while_option b f T_f x = snd (the (T_while_option2 b f T_f (x,0)))"

text \<open>Sanity check:\<close>

(* TODO *)
lemma T_while_option2_sanity:
  "T_while_option2 b f tf (x,n0) = Some (y,n) \<Longrightarrow> while_option b f x = Some y"
unfolding T_while_option2_def
(*  while_option_rule[of ""]*)
  oops

definition le_O :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool"
where "(le_O Q f g) = (\<exists>c d. \<forall>x. Q x \<longrightarrow> f x \<le> c * g x + d)"

abbreviation O_le :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("(_/ \<le>O _/ IF _)" [50, 1000, 0] 0) where
"O_le f g Q \<equiv> le_O Q f g"

abbreviation O_le0 :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" (infix "\<le>O" 50) where
"O_le0 f g \<equiv> O_le f g (\<lambda>x. True)"

notation (le_O_no_IF output) "O_le" ("(_/ \<le>O/ _)" [50,50] 50)

notation (latex) O_le ("(_/ \<le>\<^bsub>\<^latex>\<open>\\isaconst{\<close>O\<^latex>\<open>}\<close>\<^esub> _/ IF _)" [50, 1000, 0] 0)

lemma standard_BigO_if_le_O:
  fixes m :: "'a \<Rightarrow> nat"
  assumes "O_le0 (f o m) (g o m)" "finite {n. g(n) = 0}" "surj m"
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

definition fake_imp :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"fake_imp P1 P2 \<equiv> (P1 \<longrightarrow> P2)"

notation (fake_imp output) fake_imp  (infixr \<open>\<longrightarrow>\<close> 25)
notation (no_fake_imp output) fake_imp ("\<^latex>\<open>\\hide{\<close>_\<^latex>\<open>}\<close>_")

translations "BIGO x. Q" \<rightharpoonup> "CONST BigO (\<lambda>x. Q)"
translations "BIGO x. CONST fake_imp p (a \<le> b)" \<leftharpoondown> "CONST BigO (\<lambda>x. (a, b, p))"

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

lemma le_O_init: "(\<And>x. Q x \<Longrightarrow> f x \<le> g x) \<Longrightarrow> f \<le>O g IF Q"
by (metis add.commute add_0 le_O_def nat_mult_1)

lemma le_O_init2: "(\<And>x y. Q x y \<Longrightarrow> f x y \<le> g x y)
 \<Longrightarrow> (\<lambda>(x,y). f x y) \<le>O (\<lambda>(x,y). g x y) IF (\<lambda>(x,y). Q x y)"
  by (simp add: le_O_init split_def)

lemma le_O_init3: "(\<And>x y z. Q x y z \<Longrightarrow> f x y z \<le> g x y z)
 \<Longrightarrow> (\<lambda>(x,y,z). f x y z) \<le>O (\<lambda>(x,y,z). g x y z) IF (\<lambda>(x,y,z). Q x y z)"
  by (simp add: le_O_init split_def)

lemma le_O_trans[trans]: "f \<le>O g IF Q \<Longrightarrow> g \<le>O h IF Q \<Longrightarrow> f \<le>O h IF Q"
  apply(auto simp: le_O_def)
  apply(rename_tac cg ch dg dh)
apply(rule_tac x="cg*ch" in exI)
  apply(rule_tac x="cg*dh + dg" in exI)
  apply auto
apply(erule_tac x=x in allE)
apply(erule_tac x=x in allE)
  apply(simp add: algebra_simps)
  by (metis add_mono_thms_linordered_semiring(2) distrib_left dual_order.trans mult_le_mono2)

lemma le_O_trans2[trans]: "f \<le>O g IF Q \<Longrightarrow> g \<le>O h \<Longrightarrow> f \<le>O h IF Q"
  by (metis le_O_def le_O_trans)

lemma le_O_id: "f \<le>O f IF Q"
apply(auto simp: le_O_def)
apply(rule_tac x="1" in exI)
apply(rule_tac x="0" in exI)
by simp

lemma le_O_k: "(\<lambda>_. k) \<le>O (\<lambda>n. f n) IF Q"
apply(auto simp add: le_O_def)
apply(rule_tac x="0" in exI)
apply(rule_tac x="k" in exI)
by simp

lemma le_O_add: "g \<le>O f IF Q1 \<Longrightarrow> h \<le>O f IF Q2 \<Longrightarrow> (\<lambda>x. g x + h x) \<le>O f IF (\<lambda>x. Q1 x \<and> Q2 x)"
apply(auto simp add: le_O_def)
subgoal for cg ch dg dh
apply(rule_tac x="cg+ch" in exI)
apply(rule_tac x="dg+dh" in exI)
apply auto
subgoal for x
apply(erule_tac x=x in allE)
apply(erule_tac x=x in allE)
apply(simp add: algebra_simps)
done
done
done

corollary le_O_add1: "g \<le>O f IF Q \<Longrightarrow> h \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x + h x) \<le>O f IF Q"
  using le_O_add by fastforce

corollary le_O_add2L: "f \<le>O f' IF Q \<Longrightarrow> (\<lambda>x. f x + g x) \<le>O (\<lambda>x. f' x + g x) IF Q"
  by (simp add: le_O_add1 le_O_init le_O_trans)

corollary le_O_add2R: "f \<le>O f' IF Q \<Longrightarrow> (\<lambda>x. g x + f x) \<le>O (\<lambda>x. g x + f' x) IF Q"
  by (simp add: le_O_add1 le_O_init le_O_trans)
                               
corollary le_O_Suc1: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. Suc(g x)) \<le>O f IF Q"
  using le_O_add1[where h = "\<lambda>x. 1", OF _ le_O_k]
  by (metis (no_types, lifting) ext Suc_eq_plus1)


lemma le_O_diff: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x - h x) \<le>O f IF Q"
apply(auto simp add: le_O_def)
subgoal for c d
apply(rule_tac x="c" in exI)
apply(rule_tac x="d" in exI)
apply auto
  done
  done

lemma le_O_add_R1: "g \<le>O f1 IF Q \<Longrightarrow> g \<le>O (\<lambda>x. f1 x + f2 x) IF Q"
by (meson le_O_init le_O_trans nat_le_iff_add)

lemma le_O_add_R2: "g \<le>O f2 IF Q \<Longrightarrow> g \<le>O (\<lambda>x. f1 x + f2 x) IF Q"
by (meson le_O_init le_O_trans2 le_add2)

lemma le_O_mult_k: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. k * g x) \<le>O f IF Q"
apply(auto simp add: le_O_def)
apply(rule_tac x="k*c" in exI)
apply(rule_tac x="k*d" in exI)
apply auto
by (metis add_mult_distrib2 mult.assoc mult_le_mono2)

corollary le_O_mult_k2: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x * k) \<le>O f IF Q"
  by (simp add: ab_semigroup_mult_class.mult.commute le_O_mult_k)

lemma le_O_mult: "g1 \<le>O f1 IF Q \<Longrightarrow> g2 \<le>O f2 IF Q \<Longrightarrow>
 (\<lambda>x. g1 x * g2 x) \<le>O (\<lambda>x. f1 x * f2 x) IF (\<lambda>x. Q x \<and> f1 x > 0 \<and> f2 x > 0)"
apply(auto simp add: le_O_def)
subgoal for c1 c2 d1 d2
apply(rule_tac x="c1*c2+c1*d2+c2*d1" in exI)
apply(rule_tac x="d1*d2" in exI)
apply auto
subgoal for x
apply(erule_tac x=x in allE)
  apply(erule_tac x=x in allE)
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
apply(auto simp add: le_O_def)
subgoal for c d
apply(rule_tac x="c+d" in exI)
apply(rule_tac x="0" in exI)
apply auto
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
  apply(rule le_O_init)
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
  apply(auto simp: le_O_def)
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
  apply(auto simp: le_O_def)
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

(* TODO Earley: get rid of next_sym = Some, use not is_final ?? *)
(* in step_fun: rename it*)
(* get rid of global variables P w S from instations *)
(* rename P to Prods? *)
(*
abbreviation "iupdate xs i f \<equiv> xs[i := f(xs!i)]"
notation iupdate ("_[[_ := _]]" [1000,0,0] 0)
*)
(* rename? *)
hide_const (open) \<alpha>
hide_const (open) \<beta>

(* TODO modify thy *)
abbreviation "next_sym x s \<equiv> next_symbol x = Some s"
hide_const (open) next_symbol

lemma accepted_def2: "accepted = (\<exists>x \<in> \<S> (length w). is_final (id x))"
unfolding id_def accepted_def by(rule refl)

lemma accepted_complete: "P \<turnstile> [Nt S] \<Rightarrow>* w \<Longrightarrow> accepted"
using Earley_complete
by(auto simp: accepted_def recognized_def \<S>_def)

notation insert_list (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation union_list (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation diff_list (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)

notation ItemList ("\<^latex>\<open>\\isaconst{\<close>IL\<^latex>\<open>}\<close>")
notation inv_IL (\<open>\<^latex>\<open>\isaconst{\<close>inv\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation isin (\<open>\<^latex>\<open>\isaconst{\<close>isin\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

context Earley_Gw
begin

notation ps ("\<^latex>\<open>\\isaconst{\<close>ps\<^latex>\<open>}\<close>")
notation S ("\<^latex>\<open>\\isaconst{\<close>S\<^latex>\<open>}\<close>")

notation set_ItemList (\<open>\<^latex>\<open>\isaconst{\<close>set\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation empty_IL (\<open>\<^latex>\<open>\isaconst{\<close>empty\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation insert  (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation union_LIL (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation minus_LIL ("\<^latex>\<open>\\isaconst{\<close>diff\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>LIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation minus_IL (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)

notation T_isin (\<open>\<^latex>\<open>\isaconst{\<close>T'_isin\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_insert  (infixr \<open>\<^latex>\<open>\isaconst{\<close>T'_\<^latex>\<open>}\<close>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation T_union_LIL (\<open>\<^latex>\<open>\isaconst{\<close>T'_\<^latex>\<open>}\<close>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close>)
notation T_minus_IL (\<open>\<^latex>\<open>\isaconst{\<close>T'_\<^latex>\<open>}\<close>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close>)

lemma Close2L_Predict: "\<lbrakk> \<not> is_complete x; C' = insert_list x C \<rbrakk> \<Longrightarrow>
    Close2L Bs (x#B,C) (diff_list (union_list (Predict_L x (length Bs)) B) C', C')"
  using Close2L.Predict by blast

lemma Close2L_Complete: "\<lbrakk> is_complete x; C' = insert_list x C \<rbrakk> \<Longrightarrow>
    Close2L Bs (x#B,C) (diff_list (union_list (Complete_L Bs x) B) C', C')"
  using Close2L.Complete by blast

notation Predict_L ("\<^latex>\<open>\\isaconst{\<close>Predict\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation Complete_L ("\<^latex>\<open>\\isaconst{\<close>Complete\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation step2L ("\<^latex>\<open>\\isaconst{\<close>step2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation close2L ("\<^latex>\<open>\\isaconst{\<close>close2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation Init_L ("\<^latex>\<open>\\isaconst{\<close>Init\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation Scan_L ("\<^latex>\<open>\\isaconst{\<close>Scan\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation step_fun ("\<^latex>\<open>\\isaconst{\<close>step2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation close2_L ("\<^latex>\<open>\\isaconst{\<close>close2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation bins_L ("\<^latex>\<open>\\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

end

locale Earley_Gw_eps_T2 = Earley_Gw_eps_T where ps = ps for ps :: "('n,'a) prods" +
  assumes T_nth_IL: "T_nth_IL i = 1"
begin

notation T_nth_IL ("\<^latex>\<open>\\isaconst{\<close>T'_nth\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation T_step_fun ("\<^latex>\<open>\\isaconst{\<close>T'_step2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

definition T_close2_IL ::
  "('n, 'a) item list list \<Rightarrow> ('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList \<Rightarrow> nat" where
"T_close2_IL Bs =
  T_while_option (\<lambda>(il1,il2). list il1 \<noteq> []) (step_fun Bs) (T_step_fun Bs)"

notation T_close2_IL ("\<^latex>\<open>\\isaconst{\<close>T'_close2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

lemma T_steps_eq_T_close2_IL:
  "T_steps Bs = T_close2_IL Bs"
unfolding T_close2_IL_def T_while_option_def T_while_option2_def T_steps.simps steps_time.simps
by(simp add: split_def) 

notation T_bins_L ("\<^latex>\<open>\\isaconst{\<close>T'_bins\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

lemma le_O_add_k_L_iff: "((\<lambda>x. k + f x) \<le>O g IF Q) \<longleftrightarrow> (f \<le>O g IF Q)"
by (metis (no_types, lifting) ext le_O_add1 le_O_add_R2 le_O_id le_O_k le_O_trans)

lemma le_O_plus_k_R_iff[simp]: "(f \<le>O (\<lambda>x. k + g x) IF Q) \<longleftrightarrow> (f \<le>O g IF Q)"
using le_O_add_k_L_iff le_O_id le_O_trans2 by blast

lemma T_steps_le_O: "(\<lambda>(Bs,il1,il2). T_steps Bs (il1, il2)) \<le>O (\<lambda>(Bs,il1,il2). (length Bs)^2)
  IF (\<lambda>(Bs,il1,il2). wf_bins1 (map set Bs) \<and> wf1_IL il1 (length Bs) \<and> wf1_IL il2 (length Bs)
     \<and> inv_IL il1 \<and> inv_IL il2 \<and> (\<forall>i < length Bs. distinct (Bs ! i))
     \<and> set_ItemList il1 \<inter> set_ItemList il2 = {}
     \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs))" (is "?f \<le>O ?g IF ?Q")
proof -
  have 1: "?f \<le>O (\<lambda>(Bs,il1,il2). (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * 1 + 3 * L * Suc K + 7 + 2 * (K + 2))
   + 7 * 1 + 3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K)) IF ?Q"
    by(rule le_O_init3, elim conjE, rule T_steps_bound[unfolded T_nth_IL])
  also have 2: "\<dots> \<le>O (\<lambda>(Bs,il1,il2).
 (L * Suc K) * (Suc (length Bs) *
 (L * Suc K * Suc (length Bs) * (14 + 3 * L * Suc K + 2 * (K + 2))
  + 3 * Suc (length Bs) + 2 * L * Suc K + 14 + Suc K)))"
    unfolding split_def apply(rule le_O_init) by(simp add: algebra_simps)
  also
  have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). Suc (length Bs) *
 (L * Suc K * Suc (length Bs) * (14 + 3 * L * Suc K + 2 * (K + 2))
  + 3 * Suc (length Bs) + 2 * L * Suc K + 14 + Suc K)) IF ?Q"
    unfolding split_def by (rule le_O_mult_k[OF le_O_id])
  also have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). Suc (length Bs) *
 (L * Suc K * Suc (length Bs) * (14 + 3 * L * Suc K + 2 * (K + 2))
  + 3 * Suc (length Bs)))"
    unfolding split_def apply(rule le_O_multR) apply simp
    by(rule le_O_Is)+
  also have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). Suc (length Bs) * (L * Suc K * Suc (length Bs)
  + 3 * Suc (length Bs)))"
    unfolding split_def apply(rule le_O_multR) apply simp
    apply(rule le_O_add2L)
     apply (intro le_O_Is)
    done
  also have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). (L * Suc K + 3) * (length Bs + 1)^2) IF ?Q"
    unfolding split_def apply(rule le_O_init) by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  also have 1: "\<dots> \<le>O (\<lambda>(Bs,il1,il2). (length Bs + 1)^2)"
    unfolding split_def
    by(rule le_O_Is)+
  also have 1: "\<dots> \<le>O ?g"
    unfolding split_def using le_O_trans2[OF le_O_id le_O_fstI[OF le_O_sq_plus1]] .
  finally show ?thesis .
qed

lemmas T_close2_IL_O = BigO_if_le_O3[OF T_steps_le_O[unfolded T_steps_eq_T_close2_IL]]


lemma T_bins_IL_le_O: "T_bins_L \<le>O (\<lambda>k. k^3) IF (\<lambda>k. k \<le> length w)"
proof -
  note le_O_cube_SucSuc = le_O_trans[OF le_O_cube_Suc[of Suc] le_O_cube_Suc[of "\<lambda>x. x"]]
  have "T_bins_L \<le>O (\<lambda>k. (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)))) IF (\<lambda>k. k \<le> length w)"
    by(rule le_O_init, rule T_bins_L_bound)
  also have "\<dots> \<le>O (\<lambda>k. k^3)"
    apply (simp add: split_def T_nth_IL le_O_Is algebra_simps flip: power3_eq_cube)
    apply(rule le_O_Is le_O_cube_SucSuc)+
    done
  finally show ?thesis .
qed

lemmas T_bins_IL_O = BigO_if_le_O[OF T_bins_IL_le_O]


lemma T_isin_le_O: "(\<lambda>(il,x). T_isin il x) \<le>O (\<lambda>(il,x). 1)
  IF \<lambda>(il,x). inv_IL il \<and> wf1_IL il k \<and> from x < length (froms il)" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(il,x). T_nth_IL (from x) + L * (Suc K) + 1) IF ?Q"
    by(rule le_O_init2, elim conjE, rule T_isin_wf)
  also have "\<dots> \<le>O (\<lambda>(il,x). 1) IF ?Q"
    by(simp add: T_nth_IL split_def le_O_Is)
  finally show ?thesis .
qed

lemmas T_isin_O = BigO_if_le_O2[OF T_isin_le_O]


lemma T_insert_le_O: "(\<lambda>(x,il). T_insert x il) \<le>O (\<lambda>(x,il). 1)
  IF \<lambda>(x,il). inv_IL il \<and> wf1_IL il k \<and> from x < length (froms il)" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(x,il). 3 * T_nth_IL (from x) + L * (Suc K) + 1) IF ?Q"
    by(rule le_O_init2, elim conjE, rule T_insert_less)
  also have "\<dots> \<le>O (\<lambda>(x,il). 1) IF ?Q"
    by(simp add: T_nth_IL split_def le_O_Is)
  finally show ?thesis .
qed

lemmas T_insert_O = BigO_if_le_O2[OF T_insert_le_O]


lemma T_step_fun_bound: assumes "(list il1) \<noteq> []" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf1_IL il1 (length Bs)" "inv_IL il1" "length (froms il1) = Suc (length Bs)"
  "wf1_IL il2 (length Bs)" "inv_IL il2" "length (froms il2) = Suc (length Bs)"
shows "T_step_fun Bs (il1, il2) 
    \<le> L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + id(7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
unfolding id_def using T_step_fun_bound[OF assms] by linarith

lemma aux2: "(n::nat)*(n*m) = n^2 * m"
  by(simp add: power2_eq_square)

lemma T_step_fun_bound_le_O: "(\<lambda>(Bs,il1,il2). T_step_fun Bs (il1, il2)) \<le>O (\<lambda>(Bs,il1,il2). (length Bs))
  IF (\<lambda>(Bs,il1,il2). list il1 \<noteq> [] \<and> wf_bins1 (map set Bs) \<and>
  (\<forall>i < length Bs. distinct (Bs ! i)) \<and> wf1_IL il1 (length Bs) \<and> inv_IL il1 \<and>
  length (froms il1) = Suc (length Bs) \<and> wf1_IL il2 (length Bs) \<and> inv_IL il2 \<and>
  length (froms il2) = Suc (length Bs))" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(Bs,il1,il2).
    L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + (7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)) IF ?Q"
    by(rule le_O_init3, elim conjE, rule T_step_fun_bound[unfolded id_def])
  also have "\<dots> \<le>O ?g"
    by (simp add: split_def T_nth_IL le_O_Is algebra_simps aux2 flip: power2_eq_square)
  finally show ?thesis .
qed

lemmas T_step_fun_bound_O = BigO_if_le_O3[OF T_step_fun_bound_le_O]

definition "T_union_LIL_wf_P \<equiv>
  \<lambda>(as,il). inv_IL il \<and> wf1_IL il (length (froms il) - 1) \<and> wf_bin1 (set as) (length (froms il) - 1) 
    \<and> (\<forall>a\<in>set as. from a < length (froms il))"

lemma T_union_LIL_wf:
 "(\<lambda>(as,il). T_union_LIL as il) \<le>O (\<lambda>(as,il). (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1)
  IF T_union_LIL_wf_P"
  unfolding T_union_LIL_wf_P_def
  apply(rule le_O_init2)
  apply(rule T_union_LIL_wf)
  apply blast+
  done

lemma le_O_if_le2: "(\<And>x y. f x y \<le> f' x y) \<Longrightarrow> (\<lambda>(x,y). f x y) \<le>O (\<lambda>(x,y). f' x y)"
  apply(auto simp add: le_O_def)
  by (metis mult_1 trans_le_add1)

lemma T_union_LIL_wf2:
 "(\<lambda>(as,il). length as * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1)
 \<le>O (\<lambda>(as,il). 3 * (length as * (1 + L * (Suc K) + 2)) + 1) IF T_union_LIL_wf_P"
  unfolding T_nth_IL split_def
  apply(rule le_O_init)
  by (simp add: algebra_simps)

lemma T_union_LIL_wf3:
 "(\<lambda>(as,il). 3 * (length as * (1 + L * (Suc K) + 2)) + 1) \<le>O
  (\<lambda>(as,il). length as * (1 + L * (Suc K) + 2)) IF T_union_LIL_wf_P"
  unfolding split_def
  by(rule le_O_Is)+

lemma T_union_LIL_wf4:
 "(\<lambda>(as,il). length as * (1 + L * (Suc K) + 2)) \<le>O
  (\<lambda>(as,il). length as) IF T_union_LIL_wf_P"
  unfolding split_def
  by(simp add: split_def T_union_LIL_wf_P_def le_O_Is)
(*  using EarleyWorklist.inv_IL.elims(2) apply fastforce
  by(rule le_O_Is)+*)

lemmas T_union_LIL_wf5=  BigO_if_le_O2[OF
  le_O_trans[OF le_O_trans[OF le_O_trans[OF
    T_union_LIL_wf T_union_LIL_wf2] T_union_LIL_wf3] T_union_LIL_wf4, unfolded T_union_LIL_wf_P_def]]

definition "T_minus_IL_wf_P \<equiv> \<lambda>(il1,il2).
  wf1_IL il1 (length (froms il1) - 1) \<and> inv_IL il1 \<and> inv_IL il2 \<and> wf1_IL il2 (length (froms il1) - 1)
  \<and> length (froms il2) \<ge> length (froms il1)"

lemma T_minus_IL_wf:
  "(\<lambda>(il1,il2). T_minus_IL il1 il2) \<le>O (\<lambda>(il1,il2). (length (list il1)) * (4 * T_nth_IL (length (froms il1) - 1) + 2*L * (Suc K) + 4) + (length (froms il1) - 1) + 3 + length (list il1) + length (froms il1))
  IF T_minus_IL_wf_P"
  unfolding T_minus_IL_wf_P_def
  apply(rule le_O_init2)
  apply(rule T_minus_IL_wf)
  apply blast+         
  done

lemma T_minus_IL_wf2:
  "(\<lambda>(il1,il2). (length (list il1)) * (4 * T_nth_IL (length (froms il1) - 1) + 2*L * (Suc K) + 4) + (length (froms il1) - 1) + 3 + length (list il1) + length (froms il1))
  \<le>O (\<lambda>(il1,il2). 4 * (length (list il1) * (2*L * (Suc K) + 4)) + 2*length (froms il1) + 3)
  IF T_minus_IL_wf_P"
  unfolding T_nth_IL split_def
  apply(rule le_O_init)
  by (simp add: algebra_simps)

lemma le_O_add_k_L: "f \<le>O g IF Q \<Longrightarrow> (\<lambda>x. f x + k) \<le>O g IF Q"
by (simp add: le_O_add1 le_O_k)

lemma T_minus_IL_wf3:
 "(\<lambda>(il1,il2). 4 * (length (list il1) * (2*L * (Suc K) + 4)) + 2*length (froms il1) + 3)
 \<le>O (\<lambda>(il1,il2). length (list il1) + length (froms il1))
  IF T_minus_IL_wf_P"
  unfolding split_def
  apply(rule le_O_Is)
  apply(rule le_O_add1)
  apply(rule le_O_add_R1)
     apply(rule le_O_Is)
(*     apply(rule le_O_multR)
  apply(simp add: split_def T_minus_IL_wf_P_def)
  using EarleyWorklist.inv_IL.elims(2) apply fastforce*)
  apply(rule le_O_Is)
  apply(rule le_O_Is)
  apply(rule le_O_add_R2)
  apply(rule le_O_Is)+
  done
(*
lemma T_minus_IL_wf4:
 "(\<lambda>(il1,il2). length (list il1) * length (froms il1) + length (froms il1))
 \<le>O (\<lambda>(il1,il2). (length (list il1) + 1) * length (froms il1))
  IF T_minus_IL_wf_P"
  unfolding split_def
  apply(rule le_O_init)
  by (simp add: algebra_simps)
*)
lemmas T_minus_IL_wf5 =  BigO_if_le_O2[OF
  (*le_O_trans[OF*) le_O_trans[OF le_O_trans[OF
    T_minus_IL_wf T_minus_IL_wf2] T_minus_IL_wf3(*] T_minus_IL_wf4*), unfolded T_minus_IL_wf_P_def]]

end

(*>*)

text\<open>
\section{Isabelle Notation} \label{sec:isabelle}

The notation \<open>t :: \<tau>\<close> means that term \<open>t\<close> has type
\<open>\<tau>\<close>. Basic types include @{typ bool} and @{typ nat}, while type variables are written @{typ 'a}, @{typ 'b} etc.
Most type constructors are written postfix, such as @{typ "'a set"} and  @{typ "'a list"}, and the function
space arrow is \<open>\<Rightarrow>\<close>.
The image of function \<open>f\<close> over set \<open>M\<close> is denoted by @{prop "f ` A = {b. \<exists>a\<in>A. f a = b}"}.
%Function update {term "f(a := b)"} is short for @{thm (rhs) fun_upd_def}.

Functions @{const fst} and @{const snd} return the first and second components of a pair.

Lists are constructed from the empty list @{term "[]"} using the infix cons-operator @{term "(#)"}.
The operator @{term "(@)"} appends two lists, @{term "length xs"} denotes the length of @{term xs},
@{const set} converts a list to a set,
@{term "xs!n"} returns the \<open>n\<close>-th element of the list \<open>xs\<close> (starting with @{prop "n=(0::nat)"})
and @{term "xs[n := x]"} is \<open>xs\<close> with @{term "xs!n"} replaced by \<open>x\<close>.

Algebraic data types are defined using the \isakeyword{datatype} keyword.
The @{type option} type is predefined
\begin{quote}
@{datatype option}
\end{quote}
with the function @{thm Option.option.sel[of x]}.

The notation \mbox{\<open>\<lbrakk>A\<^sub>1, \<dots>, A\<^sub>n\<rbrakk> \<Longrightarrow> B\<close>} denotes an implication with premises \<open>A\<^sub>1\<close>, \ldots, \<open>A\<^sub>n\<close> and conclusion \<open>B\<close>.
Sometimes we use the inference rule presentation
\begin{quote}
\inferrule{\<open>A\<^sub>1\<close> \\ \ldots \\ \<open>A\<^sub>n\<close>}{B}
\end{quote}


Equality on type @{type bool} denotes logical equivalence.

\subsection{Context-Free Grammars}

All our types are parameterized by type variables \<open>'n\<close> and \<open>'t\<close>, the types of \concept{nonterminals} and \concept{terminals}.
\concept{Symbols} are a tagged union type:
\begin{quote}
@{datatype sym}
\end{quote}
Variable convention: \<open>A, B, C :: 'n\<close>.
% \<open>a, b, c :: 't\<close>,  and  \<open>x, y, z :: ('n,'t) sym\<close>.
For compactness we sometimes drop the \<open>'n\<close> and \<open>'t\<close> parameters,
e.g.\ we write \<open>sym\<close> instead of \<open>('n,'t)sym\<close>.

A \concept{production}, informally written \<open>A \<rightarrow> \<alpha>\<close>, is a pair of \<open>A :: 'n\<close> (the @{const lhs})
and \<open>\<alpha>\<close> \<open>::\<close> \mbox{\<open>sym list\<close>} (the @{const rhs}).
We use the following abbreviations:
\begin{quote}
\<open>syms = sym list\<close> \quad \<open>prod = 'n \<times> syms\<close> \quad \<open>Prods = prod set\<close>
\end{quote}
%Variable convention:
%\<open>w :: 't list\<close>; lists over terminal symbols are called \concept{terminal words};
%\<open>\<alpha>, \<beta>, \<gamma> :: syms\<close>; elements of type @{type syms} are called \concept{sentential forms}.

Our work is primarily based on sets of productions rather than grammars:
the start symbol is irrelevant most of the time.
\emph{For succinctness, we use \concept{grammar} to refer to a set (or list) of productions.}
Moreover, we only restrict to finite sets of productions when necessary.

The identifier \<open>P\<close> is reserved for sets of productions.
Every \<open>P\<close> induces a single step derivation relation on \<open>syms\<close> in the standard manner:
\begin{quote}
@{thm derive.intros[of _ \<beta> _ \<alpha> \<gamma>]}
\end{quote}
Its transitive-reflexive closure is denoted by @{prop "P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"}.

The language of some nonterminal \<open>A\<close> generated by \<open>P\<close> is easily defined:
\begin{quote}
@{thm Lang_def}
\end{quote}
\<close>text (in Earley_Gw_eps)\<open>
\section{The Story so far}

This paper is a continuation of the work by Nipkow and Rau \cite{NipkowR-CBJ24}.
In this section few summarize the contents of the latter paper, which is a refinement
of an initial inductive definition, via the standard definition to something resembling
a worklist algorithm, but still as an inductive definition.

\subsection{Inductive Definition of Earley's Item Sets} \label{sec:Earley}
\label{sec:EarleyInductive}

An Earley recognizer decides if some word is in the language described by a grammar
by generating a set of so-called \emph{items} (also called \emph{states} in the literature)
and checking if it contains a \emph{final} item.
In the sequel, we fix the following ``global variables'':
\begin{itemize}
\item a grammar @{const P}
\item a start symbol @{const S}
\item an input @{const w} \<open>::\<close> \mbox{@{type "syms"}} consisting only of terminal symbols.
\end{itemize}

An item is a triple @{term "Item r d i"}
where \<open>r = (A, \<alpha>)\<close> is a production from \<open>P\<close>, \<open>d\<close> is a natural number such that @{prop "d \<le> length \<alpha>"},
indicating how far the algorithm has recognized \<open>\<alpha>\<close>,
and \<open>i\<close> is a natural number representing the start index of the subword of @{term w}
recognized by this item. The three projection functions are
@{const prod}, @{const dot} and @{const from}. We use the letters \<open>x\<close> and \<open>y\<close> for items.

A production \<open>A \<rightarrow> \<alpha>\<close> together
with a @{const dot} \<open>d\<close> is shown as \<open>A \<rightarrow> \<alpha>\<^sub>1\<Zspot>\<alpha>\<^sub>2\<close>, where \<open>\<alpha>\<^sub>1\<close> is the prefix of the first \<open>d\<close> symbols of \<open>\<alpha>\<close> and \<open>\<alpha>\<^sub>2\<close>
is the suffix. We will informally show item as pairs \<open>(A \<rightarrow> \<alpha>\<Zspot>\<beta>, i)\<close>.

Below we need the following auxiliary functions on items that query or modify the dotted
production but not the @{const from} component of the item.
\begin{description}
\item[@{const mv_dot}] moves the dot one position to the right:\\
 \mbox{@{const mv_dot} \<open>(A \<rightarrow> \<alpha>\<Zspot>s\<beta>, i)\<close>} \<open>= (A \<rightarrow> \<alpha>s\<Zspot>\<beta>, i)\<close>
%\smallskip

\item[@{const is_complete} \<open>x\<close>] checks if \<open>x\<close> is of the form \mbox{\<open>(A \<rightarrow> \<alpha>\<Zspot>, i)\<close>}.
%\smallskip

\item[@{const next_sym} \<open>x s\<close>] is true iff \<open>x\<close> is of the form \<open>(A \<rightarrow> \<alpha>\<Zspot>s\<beta>, i)\<close>.
\end{description}
Note that @{prop "next_sym x s"} implies @{prop "\<not> is_complete x"}.

Next we give an abstract inductive definition of @{const Earley}, a set
of pairs @{term "(x,j)"} of items and an index. However, it is more intuitive
to present it as an inductive definition of indexed item sets: we write
\mbox{@{prop "x \<in> \<S> j"}} instead of @{prop "(x,j)\<in> Earley"}.
In the indexed presentation, we define item sets
\mbox{@{term "\<S> j"}}, @{prop \<open>j \<le> |w|\<close>}, that depend on each other. However, the dependence is in
one direction only: later sets depend on earlier ones, not the other way around.
Thus the @{term "\<S> j"} can be generated in ascending order. This is the subject of the next section
but plays no role now.

The intuitive meaning of @{prop "Item r d i \<in> \<S> j"} is that the subword
@{term "slice i j w"} (which stands for @{term "drop i (take j w)"}) has been recognized.
We call \<open>i\<close> the \emph{start index} and \<open>j\<close> the \emph{end index} (which is excluded).

The four defining rules are: one rule for the initial set of items, and one rule for each of the core operations that
expand the set of items: scanning, prediction, and completion.
\begin{quote}
{\sc Init}: @{thm [mode=Rule] Earley.Init[simplified Earley_eq_\<S>]} \quad where
@{thm Init_def}
\end{quote}

\begin{quote}
{\sc Scan}: @{thm [mode=Rule] Earley.Scan[simplified Earley_eq_\<S>]}
\end{quote}

\begin{quote}
{\sc Predict}: @{thm [mode=Rule] Earley.Predict[simplified Earley_eq_\<S>]}\\
where @{thm[margin=75,break] Predict_def}
\end{quote}

\begin{quote}
%{\sc Complete}:\\ {thm [mode=Rule] Earley.Complete[simplified Earley_eq_\<S>]}
{\sc Complete}: $\inferrule{@{thm (prem 1) Earley.Complete[simplified Earley_eq_\<S>]} \\
  @{thm (prem 2) Earley.Complete[simplified Earley_eq_\<S>]}\\\\
  @{thm (prem 3) Earley.Complete[simplified Earley_eq_\<S>]}\\
  @{thm (prem 4) Earley.Complete[simplified Earley_eq_\<S>]}}{@{thm (concl) Earley.Complete[simplified Earley_eq_\<S>]}}$
\end{quote}

%\subsection{Correctness}

Input @{const \<open>w\<close>} is \emph{accepted} if @{term "\<S> (length w)"}
contains a final item \mbox{\<open>(S \<rightarrow> \<gamma>\<Zspot>, 0)\<close>}, i.e.\ the entire input has been recognized:
\begin{quote}
%{const_typ is_final}\smallskip\\
@{thm is_final_def}\\

@{thm accepted_def2}
\end{quote}

%In order to split the rhs of a dotted production into the prefix up to the dot and the suffix
%after the dot we introduce two functions @ {const \<alpha>} and @ {const \<beta>}:
%\begin{quote}
%@{thm \<alpha>_def} \qquad @{thm \<beta>_def}
%\end{quote}

We proved \emph{soundness} and \emph{completeness}
of the item-based acceptance w.r.t.\ the grammar:
\begin{quote}
@{thm accpted_sound} \qquad and \qquad
@{thm accepted_complete}
\end{quote}
%Aside: works also for sentential forms


\subsection{The Standard Definition}
\label{sec:standard}

The standard definition of Earley's algorithm
generates each @{term "\<S> j"} completely before moving on to @{term "\<S> (j+1)"}.
This sequential strategy works because elements of @{term "\<S> j"}
do not depend on @{term "\<S> k"} where \<open>j < k\<close>.
Therefore Earley \cite{Earley-CACM} starts with
a more algorithmic formulation. The sets @{term "\<S> 0"}, @{term "\<S> 1"}, \dots, @{term "\<S> (length w)"}
are generated in that order. We follow Jones and define a sequence of \emph{bins} (= item sets),
where the \<open>i\<close>-th bin is meant to hold @{term "\<S> i"}.
Function @{const bins} recursively computes the list of bins
\begin{quote}
%{const_typ "bins::bool"}\smallskip\\
@{thm bins.simps}
\end{quote}
In each step, it takes the (currently) last bin, generates a set of new itemss by scanning
\begin{quote}
@{thm Scan_def}
\end{quote}
and closes this set under prediction and completion.
The closure operator @{const Close} takes two arguments: the current list of bins and the
result of scanning. It is defined in analogy with {\sc Predict} and {\sc Complete}:
\begin{quote}
@{thm [mode=Rule] Close.Init}
\qquad
@{thm [mode=Rule] Close.Predict}
\bigskip

@{thm [mode=Rule] Close_Complete}\smallskip\\
@{thm Complete_def}
\end{quote}

In the end we proved the following correctness theorem:
\begin{quote}
@{thm bins_eq_\<S>}
\end{quote}


\subsection{Epsilon-free Closure}

To simplify the computation of @{const Close}, we follow Jones and assume that @{const P}
is epsilon-free in the rest of the paper, i.e.\ there is no production in @{const P} with an empty @{const rhs}.
In that case, in the completion rule for @{const Close},
@{prop "x \<in> mbox((Bs @ [Close Bs B])) ! from y"} can be simplified to
@{prop "x \<in> Bs ! from y"}. Formally, we define a variant @{const Close1} of @{const Close}
with the simplified completion rule and prove their equivalence:
\begin{quote}
@{thm Close1_eq_Close}
\end{quote}
We mostly ignore wellformedness conditions in this paper but the crucial point of
@{prop "wf_bin1 B (length Bs)"} is that all complete items in \<open>B\<close> have a @{const from}
index of \<open><\<close> @{term \<open>length Bs\<close>}. Thus completion only needs to consult \<open>Bs\<close> and not
the current bin \<open>B\<close>.
Moreover @{term "wf_bins1 Bs"} \<open>\<equiv>\<close> @{prop "\<forall>k < length Bs. wf_bin1 (Bs!k) k"}.


\subsection{One-Pass Closure}
\label{sec:OnePassClosure}

Our previous work concludes with an abstract one-pass formulation of @{const Close1}.
It is still on the level of sets and intentionally nondeterministic.

We formulate the one-pass closure as a transition system @{prop "Bs \<turnstile> (B,C) \<rightarrow> mbox(B',C')"}
where \<open>B\<close>, \<open>C\<close>, \<open>B'\<close>, \<open>C'\<close> are sets of states: \<open>B\<close> is the current set whose closure is to be computed
(the ``worklist''), \<open>C\<close> is the accumulator for the closure, and \mbox{\<open>(B', C')\<close>} is the result
of a) moving some state @{prop "x \<in> B"} to the accumulator (i.e.\ @{prop "C' = C \<union> {x}"}
and b) extending the worklist with all results of prediction or completion (depending on \<open>x\<close>).
The definition is again inductive:
\begin{quote}
@{thm [mode=Rule] Close2.Predict}
\medskip

@{thm [mode=Rule] Close2.Complete}
\end{quote}
Note that a more efficient version of @{term "B \<union> Predict x (length Bs) - (C \<union> {x})"}
would be @{term "(B - {x}) \<union> (Predict x (length Bs) - (C \<union> {x}))"}
(and similarly for @{const Complete})
because \<open>B\<close> and \<open>C\<close> should be disjoint. For simplicity we have ignored this optimization.

The full closure ``algorithm'' consists of the stepwise reduction of \<open>B\<close> to the empty set:
\begin{quote}
@{thm close2_def}
\end{quote}
where \<open>SOME\<close> is Hilbert's epsilon operator: @{term "SOME x. Q"} denotes an arbitrary (but fixed!)
\<open>x\<close> that satisfies \<open>Q\<close> (if such an \<open>x\<close> exists). In our case it does exist, as witnessed by the following
lemma:
\begin{quote}
@{thm [break,margin=70] Close2_NF}
\end{quote}
The proof is by induction on a suitable wellfounded relation (that is based on the fact that
 there are only finitely many wellformed states).
Although it is not obvious, there is a unique \<open>C'\<close> such that @{prop "Bs \<turnstile> (B, C) \<rightarrow>* ({}, C')"},
i.e.\ the result of @{const close2} is independent of which result \<open>SOME\<close> chooses.

As for @{const Close} and @{const Close1}, we can also prove the equivalence of @{const Close1} and @{const close2}.
This is relegated to Section \ref{sec:close2_eq_Close1}.

Of course we still need to show termination of \<open>\<rightarrow>\<close>.
This follows because the set of well-formed items (let us call it \<open>I\<close>) is finite,
because there are only finitely many dotted productions and @{const from} fields.
In each \<open>(B,C) \<rightarrow> (B',C')\<close> step, either @{term "card (I - (B \<union> C))"} decreases
or it remains the same (because no new item was generated) and @{prop "B' \<subset> B"},
which implies termination.
By induction on this wellfounded relation it follows that eventually @{prop "B={}"}
because if not, either prediction or completion applies.

Finally we can replace @{const Close} by @{const close2} in the definition of @{const bins}
and obtain (by proof)
\begin{quote}
@{thm (concl) bins0_close2}\\
@{thm (concl) binsSuc_close2}
\end{quote}

Of course, we have not yet arrived at an executable formulation because of the presence of \<open>SOME\<close>
in @{const close2}.


\subsection{Equivalence of @{const close2} and @{const Close1}}
\label{sec:close2_eq_Close1}

\begin{quote}
@{thm close2_eq_Close1}
\end{quote}

We will sketch the proof because it is omitted in \cite{NipkowR-CBJ24}.
All proofs are by obvious inductions.

The following lemmas are generally useful:
\begin{quote}
@{thm Close2_steps_disj}\medskip\\
@{thm Close2_steps_incr}
\end{quote}

Soundness (@{thm Close2_steps_subset_Close1'}) follows in two obvious steps:
\begin{quote}
@{thm Close2_step_subset_Close1}\medskip\\
@{thm Close2_steps_subset_Close1}
\end{quote}

Completeness is a bit trickier. The key lemma says that in an \<open>\<rightarrow>\<close> sequence. where an element \<open>x\<close>
starts in \<open>B\<close> and ends up in \<open>C'\<close>, there is a \<open>\<rightarrow>\<close> step where that transition takes place.
\begin{quote}
@{thm [break,margin=75] (sub) Close2_steps_subdivide}
\end{quote}
Completeness can be proved from this lemma.
\begin{quote}
@{thm Close2_sim_Close1}
\end{quote}

Altogether this yields the desired
\begin{quote}
@{thm Close2_eq_Close1}
\end{quote}


\section{Refinement}

This section is concerned with an efficient, executable implementation of the closure
operation on bins, and thus all of the recognizer. We proceed in three steps:
\begin{enumerate}
\item Implement sets by lists.
\item Turn the inductive definition into a (functional) while-loop.
\item Augment bins with a data structure for efficient search for items.
\end{enumerate}


\subsection{From Sets to Lists}

This is a canonical data refinement step. We take the worklist algorithm for closure from Section
\ref{sec:OnePassClosure} and replace @{type set} by @{type list}. The new transition relation
has the syntax @{prop \<open>Bs \<turnstile>\<^sub>L (B,C) \<rightarrow> (B',C')\<close>} where \<open>B\<close>, \<open>C\<close>, \<open>B'\<close>, \<open>C'\<close> are item lists
and \<open>Bs\<close> is a list of item lists:
\begin{quote}
@{thm [mode=Rule] Close2L.Predict}
\medskip

@{thm [mode=Rule] Close2L.Complete}
\end{quote}
where
\begin{quote}
@{thm Predict_L_def}\medskip

@{thm [break] Complete_L_def}
\end{quote}
The binary operations @{const insert_list}, @{const union_list} and @{const diff_list} implement the corresponding
set operations on lists. They are defined in Appendix~\ref{SetByList}. We have also replaced
the set of productions @{const P} by a list @{const ps} and assume
@{lemma "P = set (id ps)" by simp}.

Correctness and termination can be proved straightforwardly:
\begin{quote}
@{thm (prem 1,sub) Close2s_if_Close2Ls}\<open>\<Longrightarrow>\<close> @{thm (concl,sub) Close2s_if_Close2Ls}
\medskip

@{thm (concl) Close2L_NF}
\end{quote}
assuming @{thm (prem 2) Close2s_if_Close2Ls}, @{thm (prem 3) Close2s_if_Close2Ls}
(and in the second theorem @{thm (prem 3) Close2L_NF}).

%The transition rules preserve the absence of duplicates in both \<open>B\<close> and \<open>C\<close>,
%but this property is not needed in the above proofs.
%It will be needed in the later complexity analysis.

\subsection{From Inductive to Recursive}

Now we take the step from inductive predicate to directly executable functional
algorithm. We employ an Isabelle/HOL library theory defining a while-combinator
\begin{quote}
@{const_typ while_option}
\end{quote}
whose definition is explained elsewhere \cite{Nipkow-ITP11}. All we need to know is that it is
executable by means of this recursion equation provable as a lemma:
\begin{quote}
@{thm while_option_unfold}
\end{quote}
Termination is equivalent with a @{const Some} result.

The closure computation is performed by the obvious worklist loop:
\begin{quote}
@{thm close2L_def}
\medskip

@{thm [break] step2L.simps}
\end{quote}

By the same well-founded induction as before
we can show termination of @{const close2L}:
\begin{quote}
@{thm (concl) close2L_Some}
\end{quote}
Correctness is provable by a standard invariant preservation argument:
\begin{quote}
@{thm [break] (sub) close2L_Some_iff_Close2s}
\end{quote}


\subsection{Efficient Access to Bins}
\label{sec:IL}

The expensive part of the closure construction is checking, in each step,
if a newly generated item is already present (in \<open>B\<close> or \<open>C\<close>).
The number of possible items is bounded by the number of dotted productions (a constant
\<open>D\<close> depending on @{const P}) times the number of possible @{const from} values,
i.e.\ @{term "D * length w"}. We will store \<open>B\<close> and \<open>C\<close> not just as linear lists
but will pair them with a version partitioned by @{const from} values,
i.e.\ as a list of lists indexed by @{const from} values. When searching for an item \<open>x\<close>,
if we can access partition @{term "from x"} directly, the search takes
time at most \<open>D\<close>, the maximum size of each partition.
When processing the \<open>i\<close>-th input character, i.e. @{term \<open>i = length Bs\<close>}, we
pair \<open>B\<close> (and \<open>C\<close>) with a list (think array) \<open>F\<close> of size \<open>i\<close> such that
\mbox{@{term "F ! j"}} is a list of all @{prop \<open>x \<in> B\<close>} where @{prop \<open>from x = j\<close>}.
The corresponding data type:
\begin{quote}
@{datatype [break,margin=85] efficientItemList}
\end{quote}
with the projection functions @{const list} and @{const froms}.
The invariant
\begin{quote}
@{thm [break] inv_IL.simps[of xs fs]}
\end{quote}
ensures
that \<open>fs\<close> is long enough to accommodate all of \<open>xs\<close>,
that \<open>fs\<close> is an indexed version of \<open>xs\<close>,
and that there are no duplicates.
The condition @{prop "length fs > 0"} simplifies some technicalities and can easily be guaranteed.

This is a data refinement step where we replace item lists by their indexed version
@{type efficientItemList}.
The refinement of the closure algorithm @{const close2L} looks like this:
\begin{quote}
@{thm [break] step_fun.simps}\\

@{thm [break,margin=85]close2_L_def[unfolded steps_def]}
\end{quote}
Upon termination of @{const while_option},
@{term "list o snd o the"} extracts the closure as an item list.
The set operations @{const "empty_IL"}, @{const "insert"},  @{const "union_LIL"} and @{const "minus_IL"}
are defined in Appendix~\ref{SetByList2}.

Finally, we are ready for the executable top-level algorithm,
a refinement of @{const bins} from Section~\ref{sec:standard}:
\begin{quote}
@{thm [break,margin=85] bins_L.simps}\medskip

@{thm Init_L_def}\medskip

@{thm [break] Scan_L_def}
\end{quote}
Note that at the end @{const close2_L} throws away the @{const froms} component
and returns only the @{const list} which @{const bins_L} adds to \<open>Bs\<close>.
The @{const froms} part is not useful any longer.
(Except for the final search for an @{const is_final} item,
but the improvement of that single step is marginal.)

Correctness is expressed as in Section \ref{sec:standard}:
\begin{quote}
@{thm bins_L_eq_\<S>[OF _ le_refl]}
\end{quote}
\<close>
text (in Earley_Gw_eps_T2)\<open>
\section{Complexity}

We have analyzed the running time of the recognizer following the approach detailed elsewhere
\cite{Nipkow-ACMbook}: from the definition of an executable function \<open>\<^latex>\<open>\isaconst{\<close>f\<^latex>\<open>}\<close> :: \<tau> \<Rightarrow> \<tau>'\<close>,
we automatically generate a (time) function definition \<open>\<^latex>\<open>\isaconst{\<close>T_f\<^latex>\<open>}\<close> :: \<tau> \<Rightarrow> nat\<close>
such that  \<open>\<^latex>\<open>\isaconst{\<close>T_f\<^latex>\<open>}\<close> x\<close>
is the number of computation steps of \<open>\<^latex>\<open>\isaconst{\<close>f\<^latex>\<open>}\<close> x\<close> where we count only calls of recursive
user-defined functions. For example, the time function @{const T_isin_list} (for @{const isin_list}
from Appendix~\ref{SetByList}) is defined like this:
\begin{quote}
@{thm T_isin_list.simps}
\end{quote}
The boon and bane of this approach is that one obtains very detailed formulas with somewhat arbitrary
constants. Arbitrary because they depend on the abstract machine model embodied in the generation of
the time functions, which may be quite different from a real machine.
As an extreme example, consider this upper bound:
\begin{quote}
@{thm [break] (sub) T_step_fun_bound}
\end{quote}
Note the following:
\begin{itemize}
\item A large number of well-formedness assumptions are required, which we will elide in the rest
of this section.
\item In the upper bound term, @{const K} and @{const L} are constants depending on @{const ps}.
\item
Function @{term T_nth_IL} is a parameter of the analysis and assumed to be an upper bound of the
real @{const T_nth}, and also of @{term T_list_update}, the time function for the list update
function \<open>xs[i := x]\<close>.
\end{itemize}
There are two interesting choices for @{term T_nth_IL}:
\begin{itemize}
\item Linear time is the standard situation in functional programs.
\item Constant time models array-like access and update of lists. We could achieve this
by another refinement step using 
Lammich's and Lochbihler's Collections library \cite{Collections-AFP,LammichL10} that offers
imperative implementations of arrays with a purely functional, list-like interface
specification.
\end{itemize}
Both choices are discussed below.


\subsection{Interlude: Asymptotic Complexity}

In order to avoid such constant-studded upper bounds as shown above for @{const T_step_fun}
we introduce a simple big $O$ framework, just enough for our purposes.
In the following, \<open>f\<close> and \<open>g\<close> are of type @{typ "'a \<Rightarrow> nat"} and \<open>Q\<close> of type @{typ "'a \<Rightarrow> bool"}.
\begin{quote}
@{thm [break] le_O_def}
\end{quote}
The \<open>IF Q\<close> is dropped if \<open>Q\<close> is @{const True} everywhere.

In contrast to the standard \<open>f \<in> O(g)\<close>, \<open>f\<close> and \<open>g\<close> are not defined on numbers but on an arbitrary type \<open>'a\<close>.
For example, @{prop "(\<lambda>xs. 2 * length xs + 3) \<le> (\<lambda>xs. (length xs)^2)"} is true:
take \<open>c = 1\<close> and \<open>d = 4\<close>. Our notation combines the measure function on some domain (here:
the length of a list) with the growth function (here: linear and quadratic).
It is easy to show that @{thm (prem 1) standard_BigO_if_le_O}, where  \<open>m ::\<close> @{typ "'a \<Rightarrow> nat"},
implies the standard \<open>f \<in> O(g)\<close> under mild assumption (for example, that \<open>m\<close> is surjective
and \<open>g\<close> is 0 only for finitely many arguments).

In concrete instances, \<open>f\<close>, \<open>g\<close> and \<open>Q\<close> will be \<open>\<lambda>\<close> abstractions over the same parameter(s).
Therefore we introduce a quantifier \isaconst{O} that shares the parameters:
\begin{quote}
@{thm [mode=fake_imp] BigO_iff_le_O}
\end{quote}
For example, the fictitious
\begin{quote}
@{prop "(\<lambda>(xs,i). T_f xs i) \<le>O (\<lambda>(xs,i). i) IF (\<lambda>(xs,i). i < length xs)"}
\end{quote}
becomes the more compact @{prop [mode=fake_imp]"BigO(\<lambda>(xs,i). (T_f xs i, i, i < length xs))"}


\subsection{Earley Complexity}

We have analyzed the complexity of our Earley recognizer with all constants present
and in terms of an upper bound @{term T_nth_IL} for @{const T_nth}.
We present the result at the end of this section.
For readability the running times of selected auxiliary functions
are presented in \isaconst{O} notation.
Except in the final result,
\emph{we assume @{term T_nth_IL} is constant and we drop all preconditions for readability}.
%\emph{Distinctness of productions (@{prop "distinct ps"}) is a global assumption in this section.}

Because of the constant time @{const nth} assumption,
single element set operations are constant time as well
\begin{quote}
@{thm [mode=no_fake_imp] T_isin_O[rename_abs il x]}\medskip

@{thm [mode=no_fake_imp] T_insert_O[rename_abs x il]}
\end{quote}
while combinations of sets take linear time:
\begin{quote}
@{thm [mode=no_fake_imp] T_union_LIL_wf5[rename_abs xs il]}\medskip

@{thm [mode=no_fake_imp] T_minus_IL_wf5[rename_abs il\<^sub>1 il\<^sub>2]}
\end{quote}

Each evaluation of @{const step_fun} requires a (constant) number of set operations
that are all of either constant time or linear time in @{term "length Bs"}.
Moreover, @{const Predict_L} is obviously constant time (because @{const ps} is fixed).
Evaluation of @{term "Complete_L Bs x"} is linear in @{term "Bs!from x"},
which is linear in @{term "length Bs"}.
Hence the overall complexity of @{const step_fun} is also linear in @{term "length Bs"}:
\begin{quote}
@{thm [mode=no_fake_imp] T_step_fun_bound_O[rename_abs Bs il\<^sub>1 il\<^sub>2]}
\end{quote}

Now we need to analyze the complexity of @{const close2_L}, which is defined by means of
@{const while_option}. However,
the infrastructure for generation of running time functions is restricted to total functions
(although they may be undefined for particular argument patterns).
Therefore we have to set up @{const T_while_option} by hand. We simply add an accumulator
that counts the computation steps:
\begin{quote}
@{thm T_while_option2_def[of _ _ tf]}
\end{quote}
In the end we project on the counter:
\begin{quote}
@{thm T_while_option_def[of _ _ tf]}
\end{quote}
Now we can define the time function for @{const close2_L}:
\begin{quote}
@{thm [break] (sub) T_close2_IL_def}
\end{quote}
At the beginning of Section \ref{sec:IL} we explained that there are at most @{term "D * length w"}
well-formed items. More precisely, when processing input symbol number @{term "length Bs"},
there are @{term "D * (length Bs+1)"} well-formed items.
Because each iteration of @{const close2_L}~\<open>Bs\<close> takes time proportional to @{term "length Bs"}
and adds at least one item (or shifts one item from \<open>B\<close> to \<open>C\<close>), the execution of @{const close2_L}
has quadratic complexity:
\begin{quote}
@{thm [mode=no_fake_imp] T_close2_IL_O[rename_abs Bs il\<^sub>1 il\<^sub>2]}
\end{quote}
Because each closure takes quadratic time and @{const bins_L} performs linearly many closure steps,
its overall complexity is cubic:
\begin{quote}
@{thm [mode=fake_imp] T_bins_IL_O[rename_abs k]}
\end{quote}

Because @{const accepted} (see Section \ref{sec:EarleyInductive})
requires a single scan of the last bin (to search for an @{const is_final} item),
and its size is bounded by @{term "D*length w"},
the time to compute @{const accepted} @{term w} is bounded by @{term "T_bins_L (length w) + D*length w"}
and is thus cubic in @{term "length w"}.
This confirms Earley's informal analysis.

The above big \isaconst{O} complexities are simplified versions of the more precise
bounds we proved. We close this section with the upper bound
we proved for our full recognizer. We spare the reader the definition of the constants:
\begin{quote}
@{term "C\<^sub>1 *((length w)+2)^3 + C\<^sub>2 * ((length w)+2)^3 * T_nth_IL ((length w)+1)"}
\end{quote}
Note that this bound is a function of @{term T_nth_IL}. It tells us that if @{const nth}
takes linear time (as opposed to constant time as assumed above), our recognizer
has quartic complexity. This confirms the informal analysis by Rau and Nipkow \cite{RauN24}.


\section{Conclusion}

We have completed the development of a verified executable Earley recognizer started by Nipkow and Rau.
In particular, we have verified its complexity. We have also verified an Earley parser for unambiguous grammars
(with the same asymptotic complexity as the recognizer), but its presentation would go beyond the scope
of the current paper.

This is work in progress. The following points, in increasing order of difficulty,
need to be addressed in the future:
\begin{itemize}
\item Lists indexed by @{const from} values should be implemented by proper arrays from
the Isabelle Collections framework \cite{Collections-AFP,LammichL10}.
\item The restriction to epsilon-free grammars should be lifted.
\item The Big \isaconst{O} framework needs to be automated. In particular, it should
  support deriving big \isaconst{O} complexities directly, without having to
  derive precise bounds first.
\item The parser (not presented in this paper) should be generalized from unambiguous to arbitrary
grammars.
\end{itemize}

\begin{credits}
\subsubsection{\ackname}
The first author would like to thank Larry Paulson for inventing the Isabelle theorem prover
and for employing him many years ago to work on the further development of Isabelle.
It was a profound and happy change of direction.

%\vspace{-1ex}
\subsubsection{\discintname}
%It is now necessary to declare any competing interests or to specifically
%state that the authors have no competing interests. Please place the
%statement with a bold run-in heading in small font size beneath the
%(optional) acknowledgments
%for example:
The authors have no competing interests to declare that are relevant to the content of this article.
\end{credits}

\bibliographystyle{splncs04}
\bibliography{root}

\appendix

\section{Set Operations on type  @{type list}}
\label{SetByList}

The definitions in this and the next appendix are mostly self-explanatory.

\begin{quote}
@{thm filter.simps}\\

@{thm fold_simps}\\

@{thm isin_list.simps}\\

@{thm insert_list_def}\\

@{thm union_list_def2}\\

@{thm diff_list_def}
\end{quote}

\section{Set Operations on type @{type efficientItemList}}
\label{SetByList2}

\begin{quote}
@{thm [break] EarleyWorklist.isin.simps}\\

@{thm [break] empty_IL_def[unfolded empty_froms_is_replicate]}\\

@{thm [break] insert.simps}\\

@{thm union_LIL.simps}\\

@{thm IL_of_List_def}\\

@{thm [break]minus_LIL.simps}\\

@{thm [break](sub)minus_IL_def}
\end{quote}
Note that
\begin{description}
\item[@{const empty_IL}] initializes the @{const froms} list with
a list that is sufficiently large for the items that are expected to go into it.
The required size can be determined statically in our setting.
Function @{const replicate} creates a list of that size where every element is @{const Nil}.
\item[@{const union_LIL}] takes as its first argument a list.
\item[@{const minus_LIL}] takes as a first argument the size
of the required @{const froms} list and as the second argument a list.
\end{description}
\<close>

(*<*)
end
(*>*)