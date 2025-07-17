theory Gauss_Jordan
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

text ‹Solver for a system of linear equations ‹xi = a0 * x0 + ... + an*xn + b›
where ‹+, * :: 'a ⇒ 'a ⇒ 'a› are parameters.
The system is represented in matrix form: ‹X = A*X + B› where the matrix is of type ‹'a list list›
and we work with only a single matrix ‹A› augmented with the vector ‹B›.
In each step, the solver eliminates one variable. This step must be supplied as a parameter
‹solve1› that solves ‹x = a * x + rest› for ‹x›. Here, ‹rest› is of the form ‹ak*xk + ... + an*xn+b›
and given as the list ‹[ak,...,an,b]›.
The solution is returned in fully substituted, not triangular form.
The order of the variables/equations is reversed.›

definition "mx m n xss = (length xss = m ∧ (∀xs ∈ set xss. length xs = n))"


fun mult where "mult a b = a * b"

definition mult1 where
"mult1 = map o mult"

(*
foldl can be used here for more efficient code
but this may make the proofs easier
*)
definition dot :: "'a :: {zero, plus, times} list ⇒ 'a list ⇒ 'a" where
"dot as bs = foldr (+) (map2 mult as bs) 0"

lemma γ_dot:
  fixes γ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes γ_add: "\<And>a b. γ (a + b) = γ a + γ b"
  and γ_mul: "\<And>a b. γ (a * b) = γ a * γ b"
  and γ_zero: "γ 0 = 0"
  shows "γ (dot as bs) = dot (map γ as) (map γ bs)"
unfolding dot_def using assms proof(induction as arbitrary: bs)
    case (Cons a as)
    then show ?case using assms apply(cases bs) by simp+
qed simp


lemma γ_dot_Cons:
  fixes γ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes γ_add: "\<And>a b. γ (a + b) = γ a + γ b"
  and γ_mul: "\<And>a b. γ (a * b) = γ a * γ b"
  and γ_zero: "γ 0 = 0"
  shows "γ (dot (a#as) (b#bs)) = γ a*γ b + γ (dot as bs)"
    unfolding dot_def by (simp add: assms)

lemma map2_Cons: "map2 f (x#xs) (y#ys) = f x y # map2 f xs ys"
  by simp

lemma dot_mult:
  shows "(c :: 'a :: semiring_1) * (dot as bs) = (dot (map (mult c) as) bs)"
  unfolding dot_def proof(induction as arbitrary: bs)
  case (Cons a as)
  then show ?case proof(cases bs)
    case (Cons x xs)
    then show ?thesis using Cons.IH[of xs] by (auto simp add: distrib_left mult.assoc)
  qed simp
qed simp

lemma dot_map2_plus:
  assumes "length as = length bs"
  and "length bs = length cs"
  shows "dot (map2 (+) as bs) (cs :: 't :: semiring_1 list) = dot as cs + dot bs cs"
  using assms unfolding dot_def proof(induction as bs cs rule: list_induct3)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys z zs)
    then show ?case apply auto by (simp add: add.assoc add.left_commute combine_common_factor)
  qed

lemma γ_map2_sum:
  fixes γ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes γ_add: "\<And>a b. γ (a + b) = γ a + γ b"
  and γ_mul: "\<And>a b. γ (a * b) = γ a * γ b"
  and γ_zero: "γ 0 = 0"
  shows "map γ (map2 (+) as bs) = map2 (+) (map γ as) (map γ bs)"
    using assms apply(induction as bs rule: list_induct2') by simp+

lemma γ_map_mult:
  fixes γ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes γ_add: "\<And>a b. γ (a + b) = γ a + γ b"
  and γ_mul: "\<And>a b. γ (a * b) = γ a * γ b"
  and γ_zero: "γ 0 = 0"
shows"map \<gamma> (map (mult c) as) = map (mult (γ c)) (map γ as)"
  apply(induction as)
  using assms by simp+

lemma γ_mult1:
  fixes γ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes γ_add: "\<And>a b. γ (a + b) = γ a + γ b"
  and γ_mul: "\<And>a b. γ (a * b) = γ a * γ b"
  and γ_zero: "γ 0 = 0"
shows"map \<gamma> (mult1 c as) = (mult1 (γ c) (map γ as))"
  unfolding mult1_def comp_def using assms γ_map_mult by simp

lemma γ_dot_mult:
  fixes γ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes γ_add: "\<And>a b. γ (a + b) = γ a + γ b"
  and γ_mul: "\<And>a b. γ (a * b) = γ a * γ b"
  and γ_zero: "γ 0 = 0"
  shows "γ c * γ (dot as bs) = γ (dot (map (mult c) as) bs)"
unfolding γ_dot[OF assms] γ_map_mult[OF assms] using dot_mult by blast

locale Gauss =
fixes solve1 :: "'a :: {one, zero, plus, times} ⇒ 'a list ⇒ 'a list"
and γ :: "'a  ⇒ 'b :: semiring_1"
assumes length_solve1: "length(solve1 a cs) = length cs"
and γ_add: "γ (a + b) = γ a + γ b"
and γ_mul: "γ (a * b) = γ a * γ b"
and γ_zero: "γ 0 = 0"
and γ_one: "γ 1 = 1"
and solve1_c: "γ X = γ (dot (solve1 c cs) (Xs@[1])) \<Longrightarrow> γ X = γ (dot (c#cs) (X#Xs@[1]))"

begin
text ‹We work on a matrix representation of ‹X = A*X+B› where the matrix is ‹(A|B)›.
In each step, ‹solve1 a b› solves an equation ‹X_i = a*X_i + b›
 where b is a list of coefficients of the remaining variables (and the additive constant).›

lemmas γ0 = γ_add γ_mul γ_zero
lemmas γ = γ0 γ_one

fun eq where "eq a b = (γ a = γ b) "

(*
is_sol x ds xs :=   x = ds * (xs @ [1])
*)
definition is_sol :: "'a ⇒ 'a list ⇒ 'a list ⇒ bool" where
"is_sol a cs sol = (Suc (length sol) = length cs ∧ eq a (dot cs (sol @ [1])))"

(*
is_sols ys M xs :=  ys = M * (xs @ [1])

*)
fun is_sols :: "'a list ⇒ 'a list list ⇒ 'a list ⇒ bool" where
"is_sols (a#as) (eqn # eqns) sol = (is_sol a eqn sol ∧ is_sols as eqns sol)" |
"is_sols [] [] sol = True" |
"is_sols _  [] sol = False" |
"is_sols []  _ sol = False"

lemma is_sols_length: "is_sols as eqns sol ⟹  length as = length eqns"
  apply(induction as eqns sol rule: is_sols.induct )
  by auto

lemma is_sols_append: "is_sols as1 eqns1 sol ⟹  is_sols as2 eqns2 sol ⟹  is_sols (as1@as2) (eqns1@eqns2) sol"
  apply(induction as1 eqns1 sol rule: is_sols.induct)
  by auto

fun is_sols2 where
"is_sols2 as eqns sol = (length as = length eqns ∧ list_all2 (λs eq. is_sol s eq sol) as eqns)"

(*maybe better with ∀*)
fun is_sols3 where
"is_sols3 sol eqns = (length sol = length eqns ∧ list_all2 (λs eq. is_sol s eq sol) sol eqns)"

lemma wrong_len_not_sol: "length sol ≠ length eqns ⟹  ¬is_sols sol eqns sol2"
  apply(induction rule: is_sols.induct)
  by simp+


lemma is_sols2_eqiv: "is_sols sol eqns sol' = is_sols2 sol eqns sol'"
proof(cases "length sol = length eqns")
  case True
  from True show "is_sols sol eqns sol'  = is_sols2 sol eqns sol'" proof(induction rule: is_sols.induct)
    case (1 a as eqn eqns sol)
    then have len: "length as = length eqns" by simp
    then have "is_sols as eqns sol  = is_sols2 as eqns sol" using 1 by simp
    have "is_sols2 (a # as) (eqn # eqns) sol = list_all2 (λx y. is_sol x y sol) (a # as) (eqn # eqns)"
      using 1 by simp
    also have "… = (is_sol a eqn sol ∧ is_sols2 as eqns sol)"
      using len by simp
    then show ?case using 1 by simp
  qed simp+
qed (simp add: wrong_len_not_sol)

corollary is_sols3_eqiv: "is_sols3 sols eqns = is_sols sols eqns sols"
  by (simp add: is_sols2_eqiv)


fun subst :: "'a list ⇒ 'a list ⇒ 'a list" where
"subst sol (c#cs) = map2 (+) (mult1 c sol) cs"



(*not true in general for regexes*)
lemma solve1_unique: "\<lbrakk> length cs > 0; is_sol X (c#cs) (X#Xs) \<rbrakk> \<Longrightarrow>  is_sol X (solve1 c cs) Xs"
  unfolding is_sol_def oops

lemma solve1_correct: "\<lbrakk> is_sol X (solve1 c cs) Xs \<rbrakk> \<Longrightarrow>  is_sol X (c#cs) (X#Xs) "
  unfolding is_sol_def using solve1_c by (simp add: length_solve1)

(*

‹X#Xs› are a solution of the system of equations
they exist but are not known to the algo

(c#cs) are the coefficients of the first equation
ds     are the coefficients with the first variable eliminated
    aka where the system has been solve1 ed for that variable

(e#es)   are the coefficients of some other equation
  where we want to eleminate the first variable

Y is the solution of that equation

*)
lemma subst_unique:
  assumes "is_sol X ds Xs"
  and "is_sol Y es (X#Xs)"
  shows "is_sol Y (subst ds es) Xs"
using assms unfolding is_sol_def
  oops

lemma map_subst_unique: "⟦
  is_sol y ds ys ;
  is_sols xs eqs (y#ys)
⟧ ⟹  is_sols xs (map (subst ds) eqs) ys"
oops


lemma subst_correct: "⟦
  length ds = length cs ;
  length cs = length ys + 1;
  eq y (dot ds (ys@[1])) ;
  is_sol x (subst ds (c#cs)) ys
⟧ ⟹  is_sol x (c#cs) (y#ys)"
  unfolding eq.simps is_sol_def subst.simps eq.simps proof(standard, goal_cases)
    case 1
    show ?case using ‹length cs = length ys + 1› by simp
  next
    case 2
    have l1: "length (mult1 (\<gamma> c) (map \<gamma> ds)) = length (map \<gamma> cs)"
      using 2(1) unfolding mult1_def comp_def by simp
    have l2: "length (map \<gamma> cs) = length (map \<gamma> ys @ [1])"
      using 2(2) by simp
    have  "\<gamma> x = \<gamma> (dot (map2 (+) (mult1 c ds) cs) (ys @ [1]))" using 2(4) by auto
    hence "γ x = dot (map γ (map2 (+) (mult1 c ds) cs)) (map \<gamma> (ys @ [1]))" unfolding γ_dot[OF γ0] by simp
    hence "γ x = dot (map γ (map2 (+) (mult1 c ds) cs)) (map γ ys @ [1])" using γ by simp
    hence "γ x = dot (map2 (+) (map γ (mult1 c ds)) (map γ cs)) (map γ ys @ [1])" unfolding γ_map2_sum[OF γ0] by simp
    hence "γ x = dot (map2 (+) (mult1 (γ c) (map γ ds)) (map γ cs)) (map γ ys @ [1])" using γ_mult1[OF γ0] by simp
    hence "γ x = dot (mult1 (\<gamma> c) (map \<gamma> ds)) (map \<gamma> ys @ [1]) + dot (map \<gamma> cs) (map \<gamma> ys @ [1])" using dot_map2_plus[OF l1 l2] by simp
    hence "γ x = γ c * dot (map \<gamma> ds) (map \<gamma> ys @ [1]) + dot (map \<gamma> cs) (map \<gamma> ys @ [1])" unfolding mult1_def comp_def sym[OF dot_mult] by simp
    hence "γ x = γ c * γ (dot ds (ys @ [1])) + \<gamma> (dot cs (ys @ [1]))" using γ_dot[OF γ0] γ by simp
    hence "γ x = γ c * γ y + \<gamma> (dot cs (ys @ [1]))" using 2(3) by simp
    hence "γ x = γ (dot (c # cs) (y # (ys@ [1])))" using γ_dot_Cons[OF γ0] by simp
    thus  "γ x = γ (dot (c # cs) ((y # ys) @ [1]))" by simp
  qed

lemma map_subst_correct: "⟦
mx n (b+2) eqs ;
length ds = b+1;
length ys = b;
eq y (dot ds (ys@[1]));
is_sols xs (map (subst ds) eqs) ys
⟧ ⟹  is_sols xs eqs (y#ys)"
unfolding is_sols2_eqiv is_sols2.simps proof(goal_cases)
  case 1
  have "list_all2 (\<lambda>s eq. is_sol s eq (y # ys)) xs eqs"
    proof
      have "list_all2 (\<lambda>s eq. is_sol s (subst ds eq) ys) xs eqs"
        using 1 by (simp add: list_all2_map2)
      then show "list_all2 (\<lambda>s eq. is_sol s (subst ds eq) ys ∧ length eq = b+2) xs eqs"
        using ‹mx n (b+2) eqs› unfolding mx_def using list.rel_mono_strong by fastforce
    next
      fix x Cs
      assume "is_sol x (subst ds Cs) ys ∧ length Cs = b+2"
      then have "length Cs = b+2" by simp
      then obtain c cs where ccs: "c#cs = Cs" by (metis add_2_eq_Suc' list.size(3) nat.distinct(1) neq_Nil_conv)
      then have "length cs = b+1"
        using ‹length Cs = b+2› by fastforce
      then have "length ds = length cs"
        using "1"(2) by simp

      have "length cs = length ys + 1"
        using ‹length cs = b+1› ‹length ys = b› by simp

      show "is_sol x Cs (y # ys)"
        using subst_correct[of ds cs ys y x c, OF ‹length ds = length cs› ‹length cs = length ys + 1›] unfolding ccs
        using ‹eq y (dot ds (ys@[1]))› \<open>is_sol x (subst ds Cs) ys \<and> length Cs = b + 2\<close> by blast
    qed
  then show ?case using 1 by simp
qed


fun solves :: "'a list list ⇒ 'a list list ⇒ 'a list list" where
(* would it be a good idea to map hd here? *)
"solves sols [] = sols" |
"solves sols ((c # cs) # eqs) =
 (let sol = solve1 c cs;
      eqs' = map (subst sol) eqs;
      sols' = sol # map (subst sol) sols
  in solves sols' eqs')" |
(*totality*)
"solves _ _ = []"


lemma length_subst:
  "⟦ length sol = length cs - 1; length cs ≠ 0 ⟧ ⟹  length(subst sol cs) = length sol"
by(auto simp: neq_Nil_conv mult1_def)

lemma length_solves:
  "⟦ mx k (Suc k) eqs; mx n (Suc k) sols ⟧ ⟹  length(solves sols eqs) = k+n"
proof(induction sols eqs arbitrary: k n rule: solves.induct)
  case (1 sols)
  then show ?case by(auto simp: mx_def)
next
  case (2 sols c cs eqs)
  show ?case using "2.prems" "2.IH"[OF refl refl refl, of "k-1" "n+1"]
    by(auto simp add: length_solve1 length_subst mx_def Let_def)
qed (auto simp: mx_def)

lemma length_in_solves:
  "⟦ mx k (Suc k) eqs; mx n (Suc k) sols; cs ∈ set(solves sols eqs) ⟧ ⟹  length cs = Suc 0"
proof(induction sols eqs arbitrary: cs k n rule: solves.induct)
  case (1 sols)
  then show ?case by(auto simp: mx_def)
next
  case (2 sols c cs eqs as)
  show ?case using "2.prems"
    using  "2.IH"[OF refl refl refl, of "k-1" "n+1" as]
    by(auto simp add: length_solve1 length_subst mx_def Let_def)
qed (auto simp: mx_def)

lemma length_map_subst: "⟦ mx n b eqns; length sol = b-1 ; length sol ≠ 0 ⟧ ⟹  mx n (b-1) (map (subst sol) eqns)"
unfolding mx_def
apply(induction eqns)
using length_subst
apply auto
apply (metis One_nat_def linordered_nonzero_semiring_class.zero_le_one list.size(3))
by (metis One_nat_def le0 length_subst)

find_theorems "rev (?x # ?xs)"

lemma is_sols_rev: "is_sols (rev Ys) (rev eqns) Xs = is_sols Ys eqns Xs"
  unfolding is_sols2_eqiv by simp

lemma dot_one: "γ (dot (x#xs) [1]) = γ x"
  unfolding dot_def apply auto
  unfolding γ_add γ_zero γ_mul γ_one
  by simp

lemma dot_one_hd: "length xs > 0 \<Longrightarrow> γ (dot xs [1]) = γ (hd xs)"
  using dot_one apply(cases xs) by simp+

find_theorems "list_all2 ?P ?a ?b \<Longrightarrow> ?C"

lemma is_sols_trivial: "is_sols ys eqns [] \<Longrightarrow> map γ ys = map (γ o hd) eqns"
unfolding is_sols2_eqiv is_sols2.simps is_sol_def eq.simps
proof-
  assume "length ys = length eqns \<and> list_all2 (\<lambda>s eq. Suc (length []) = length eq \<and> \<gamma> s = \<gamma> (dot eq ([] @ [1]))) ys eqns"
  then have "list_all2 (\<lambda>s eq. 1 = length eq \<and> \<gamma> s = \<gamma> (dot eq [1])) ys eqns"
    by simp
  then have "list_all2 (\<lambda>s eq. \<gamma> s = \<gamma> (hd eq)) ys eqns"
    using dot_one_hd by (smt (verit) less_numeral_extra(1) list_all2_mono)
  then show "map \<gamma> ys = map (\<gamma> \<circ> hd) eqns"
    apply(induction) by simp+
qed

(*

  the assumption about shape is only correct at the algo start
  mx h (Suc n + m) eqns
  mx h (Suc n + m) sols

  during the algo we can only say that

  mx n b eqns
  mx m b sols
  b > 0


  the 2 Xs do not stay the same, only sublists
*)

theorem solves_unique:
  shows "⟦ b = n+1; mx n b eqns; mx m b sols;
    is_sols Ys eqns Ys;
    is_sols (rev Xs) sols Ys ⟧
    ⟹  is_sols (Xs@Ys) (rev (solves sols eqns)) []"
oops

lemma is_sol_eq: "is_sol x ds xs \<Longrightarrow> eq x y \<Longrightarrow> is_sol y ds xs"
  unfolding eq.simps is_sol_def by simp

lemma solves_correct_step: "
⟦
  mx n (b+2) eqs;
  length ds = b + 1;
  length xs = b;

  is_sols xs eqs' xs;
  is_sols (x#Ys) sols' xs;

  ds = solve1 c cs;
  eqs' = map (subst ds) eqs;
  sols' = ds # map (subst ds) sols

⟧ \<Longrightarrow>
    is_sols (x#xs) ((c#cs)#eqs) (x#xs)
"
proof(goal_cases)
  case 1
  have "is_sol x (solve1 c cs) xs"
    using 1 by simp
  moreover have "is_sols xs (map (subst ds) eqs) xs"
    using 1 by simp
  moreover have "eq x (dot ds (xs @ [1]))"
    using ‹ds = solve1 c cs› \<open>is_sol x (solve1 c cs) xs\<close> is_sol_def by blast
  ultimately have "is_sols xs eqs (x # xs)"
    using map_subst_correct[OF ‹mx n (b+2) eqs› ‹length ds = b + 1› ‹length xs = b›]
    by simp
  then show ?case using \<open>is_sol x (solve1 c cs) xs\<close> solve1_correct by auto
qed


theorem solves_correct:
  "⟦ b = n+1; mx n b eqns; mx m b sols; length Ys = n;
    is_sols (Xs@Ys) (rev (solves sols eqns)) []
    ⟧ \<Longrightarrow>
    is_sols Ys eqns Ys ∧ is_sols (rev Xs) sols Ys
     "
proof(induction sols eqns arbitrary: Xs Ys n m b rule: solves.induct)
  case (2 sols c cs eqs)
  define sol where "sol = solve1 c cs"
  define eqs' where "eqs' = map (subst sol) eqs"
  define sols' where "sols' = sol # map (subst sol) sols"

  obtain y ys where yys: "y#ys = Ys" by (metis "2.prems"(2,4) length_Cons list.size(3) mx_def nat.simps(3) neq_Nil_conv)

  have "length ys = n - 1" using ‹length Ys = n› yys by auto
  have "length cs = b - 1"
    by (metis "2.prems"(2) One_nat_def add_diff_cancel_right' list.set_intros(1) list.size(4) mx_def)
  then have "length sol = b - 1"
    using length_solve1 sol_def by presburger
  have "length sol > 0" using "2.prems"(1,2) \<open>length sol = b - 1\<close> mx_def by force
  have "mx (n-1) b eqs" using ‹mx n b ((c # cs) # eqs)› unfolding mx_def by auto
  then have "mx (n-1) (b-1) (map (subst sol) eqs)" using length_map_subst ‹length sol = b - 1› ‹length sol > 0› by simp
  then have "mx (n-1) (b-1) eqs'" using eqs'_def by simp
  have "b-1 = n-1+1" using ‹b = n + 1› by (metis "2.prems"(2) One_nat_def add_diff_cancel_right' list.size(4) mx_def)
  have "length cs > 0"
    using \<open>length sol > 0\<close> length_solve1 sol_def by auto
  have "mx m (b-1) (map (subst sol) sols)" using "2.prems"(3) ‹length sol = b - 1› ‹length sol > 0› length_map_subst by blast
  then have "mx (m+1) (b-1) sols'" using sols'_def by (simp add: ‹length sol = b - 1› mx_def)

  have "is_sols ((Xs @ [y]) @ ys) (rev (solves sols ((c # cs) # eqs))) []"
    using ‹is_sols (Xs @ Ys) (rev (solves sols ((c # cs) # eqs))) []› yys by simp
  then have "is_sols ((Xs @ [y]) @ ys) (rev (solves sols' eqs')) []"
    by (metis eqs'_def sol_def sols'_def solves.simps(2))

  have IH: "is_sols ys eqs' ys \<and> is_sols (rev (Xs @ [y])) sols' ys"
    using "2.IH"[OF sol_def eqs'_def sols'_def ‹b-1 = n-1+1› ‹mx (n-1) (b-1) eqs'› ‹mx (m+1) (b - 1) sols'› ‹length ys = n - 1› ‹is_sols ((Xs @ [y]) @ ys) (rev (solves sols' eqs')) []›]
    by simp


  have "is_sols (y # rev Xs) (sol # map (subst sol) sols) ys"
    using IH sols'_def by simp
  then have "is_sol y sol ys"
    by simp
  then have "is_sol y (solve1 c cs) ys"
    using sol_def by simp
  then have "is_sol y (c#cs) (y#ys)"
    using solve1_correct by simp

  have "eq y (dot sol (ys @ [1]))"
    using ‹is_sol y sol ys›
    unfolding is_sol_def by simp

  have "is_sols (rev Xs) (map (subst sol) sols) ys"
    using ‹is_sols (y # rev Xs) (sol # map (subst sol) sols) ys› by simp
  then have "is_sols (rev Xs) sols (y# ys)"
    using map_subst_correct[of m "b-2" ,OF _ _ _ ‹eq y (dot sol (ys @ [1]))› ‹is_sols (rev Xs) (map (subst sol) sols) ys›]
    by (metis "2.prems"(1,3) Suc_eq_plus1 \<open>b - 1 = n - 1 + 1\<close> \<open>length sol = b - 1\<close> \<open>length ys = n - 1\<close> add_2_eq_Suc' add_implies_diff)

  moreover have "is_sols ys (map (subst sol) eqs) ys"
    using eqs'_def IH by simp
  then have "is_sols ys eqs (y#ys)"
    using map_subst_correct[OF _ _ _ ‹eq y (dot sol (ys @ [1]))› ‹is_sols ys (map (subst sol) eqs) ys›]
    by (metis "2.prems"(1,4) One_nat_def Suc_eq_plus1 \<open>b - 1 = n - 1 + 1\<close> \<open>length sol = b - 1\<close> \<open>length ys = n - 1\<close> \<open>mx (n - 1) b eqs\<close> add_2_eq_Suc' list.size(4) yys)

  ultimately show ?case using yys ‹is_sol y (c # cs) (y # ys)› is_sols.simps(1) by blast
next
  case (1 sols)
  have "n = 0" using ‹mx n b []› mx_def by (metis length_0_conv)
  then have "Ys = []" using "1.prems"(4) by auto
  then have "is_sols Ys [] Ys" by simp
  moreover have "is_sols Xs (rev sols) []"
    using "1.prems" ‹Ys = []› by simp
  ultimately show ?case using ‹Ys = []› by (simp add: is_sols2_eqiv list_all2_rev1)
next
  case (3 a va)
  have "b = 0" using ‹mx n b ([] # va)› unfolding mx_def by simp
  then show ?case using 3 by simp
qed

corollary solves_correct': "
  ⟦ b = n+1; mx n b eqns; length Ys = n;
    is_sols Ys (rev (solves [] eqns)) []
    ⟧ \<Longrightarrow>
    is_sols Ys eqns Ys
     "
using solves_correct[of b n eqns 0 "[]" Ys "[]"] by (simp add: mx_def)




end

datatype 'a langR = Lang "'a list set"
fun unLang where "unLang (Lang x) = x"

abbreviation L where "L \<equiv> λx. Lang (lang x)"

(*TODO: stimmt es, dass type alles ist?*)
instantiation langR :: (type) semiring_1
begin
definition times_langR :: "'a langR ⇒ 'a langR ⇒ 'a langR"
  where "A * B ≡ Lang (unLang A @@ unLang B)"
definition plus_langR :: "'a langR ⇒ 'a langR ⇒ 'a langR"
  where "A + B ≡ Lang (unLang A ∪ unLang B)"
definition zero_langR where "zero_langR ≡ Lang {}"
definition one_langR where "one_langR ≡ Lang {[]}"

instance proof(standard, goal_cases)
  case (1 a b c)
  then show ?case by (simp add: Gauss_Jordan.times_langR_def conc_assoc)
next
  case (2 a)
  then show ?case unfolding one_langR_def
    by (metis conc_epsilon(1) times_langR_def unLang.elims unLang.simps)
next
  case (3 a)
  then show ?case unfolding one_langR_def
    by (metis conc_epsilon(2) times_langR_def unLang.elims unLang.simps)
next
  case (4 a b c)
  then show ?case by (simp add: inf_sup_aci(6) plus_langR_def)
next
  case (5 a b)
  then show ?case by (simp add: inf_sup_aci(5) plus_langR_def)
next
  case (6 a)
  then show ?case unfolding zero_langR_def
    by (metis Un_empty_left plus_langR_def unLang.cases unLang.simps)
next
  case (7 a)
  then show ?case unfolding zero_langR_def
    by (simp add: Gauss_Jordan.times_langR_def)
next
  case (8 a)
  then show ?case unfolding zero_langR_def
    by (simp add: Gauss_Jordan.times_langR_def)
next
  case (9 a b c)
  then show ?case by (simp add: conc_Un_distrib(2) plus_langR_def times_langR_def)
next
  case (10 a b c)
  then show ?case by (simp add: conc_Un_distrib(1) plus_langR_def times_langR_def)
next
  case 11
  then show ?case by (simp add: one_langR_def zero_langR_def)
qed
end


lemma Ardens:
  "star A @@ B = (A @@ (star A @@ B)) ∪ B"
proof -
  have "star A = A @@ star A ∪ {[]}"
    by (rule star_unfold_left)
  then have "star A @@ B = (A @@ star A ∪ {[]}) @@ B"
    by metis
  also have "… = (A @@ star A) @@ B ∪ B"
    unfolding conc_Un_distrib by simp
  also have "… = A @@ (star A @@ B) ∪ B"
    by (simp only: conc_assoc)
  finally show ?thesis .
qed

lemma Ardens2: "[] \<notin> A \<Longrightarrow> X = A @@ X \<union> B \<Longrightarrow> X = star A @@ B"
  using Arden_sol_is_star by auto

lemma Ardens3: "X = star A @@ B \<Longrightarrow> X = A @@ X \<union> B"
  using Ardens by auto

instantiation rexp :: (type) plus begin
  definition plus_rexp where "plus_rexp \<equiv> Plus"
  instance ..
end
instantiation rexp :: (type) zero begin
  definition zero_rexp where "zero_rexp \<equiv> Zero"
  instance ..
end
instantiation rexp :: (type) one begin
  definition one_rexp where "one_rexp \<equiv> One"
  instance ..
end
instantiation rexp :: (type) times begin
  definition times_rexp where "times_rexp \<equiv> Times"
  instance ..
end

global_interpretation Gauss where
solve1 = "λr cs. map (λc. Times (Star r) c) cs" and γ = "λr. Lang (lang r)"
defines solves_r = solves and subst_r = subst and mult1_r = mult1
proof (standard, goal_cases)
  case (1 a cs)
  then show ?case by simp
next
  case (2 a b)
  then show ?case by (simp add: plus_langR_def plus_rexp_def)
next
  case (3 a b)
  then show ?case by (simp add: times_langR_def times_rexp_def)
next
  case 4
  then show ?case by (simp add: zero_langR_def zero_rexp_def)
next
  case 5
  then show ?case by (simp add: one_langR_def one_rexp_def)
next
  fix cs X c Xs
  assume "L X = L (dot (map (Times (Star c)) cs) (Xs @ [1]))"
  then have "L X = L (dot (map (mult (Star c)) cs) (Xs @ [1]))"
    by (metis map_eq_conv mult.simps times_rexp_def)

  then have "L X = L (Star c) * L (dot cs (Xs@[1]))"
    using γ_dot_mult[of L] unfolding plus_langR_def plus_rexp_def times_langR_def times_rexp_def zero_langR_def zero_rexp_def
    by fastforce
  then have "lang X = star (lang c) @@ unLang (L (dot cs (Xs@[1])))"
    by (simp add: times_langR_def)
  then have "lang X = lang c @@ lang X \<union> unLang (L (dot cs (Xs@[1])))"
    using Ardens by auto
  then have "L X = L c * L X + L (dot (cs) ((Xs@[1])))"
    by (simp add: plus_langR_def times_langR_def)
  then show "L X = L (dot (c # cs) (X # Xs @ [1]))"
    using γ_dot_Cons[of L] unfolding plus_langR_def plus_rexp_def times_langR_def times_rexp_def zero_langR_def zero_rexp_def
    by fastforce

qed

value "solves_r [] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [[x,y,z]] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [] [[a00,a01,b0]]"

