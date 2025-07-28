theory Gauss_Jordan
imports
  "$AFP/Regular-Sets/Regular_Exp"
  (*
  "/home/ai/Documents/SEMANTICS/Isabelle2025/src/HOL/Library/Extended_Real"
  *)
begin

text ‹Solver for a system of linear equations ‹xi = a0 * x0 + ... + an*xn + b›
where ‹+, * :: 'a ⇒ 'a ⇒ 'a› are type classes.
The system is represented in matrix form: ‹X = A*X + B› where the matrix is of type ‹'a list list›
and we work with only a single matrix ‹A› augmented with the vector ‹B›.
In each step, the solver eliminates one variable. This step must be supplied as a parameter
‹solve1› that solves ‹x = a * x + rest› for ‹x›. Here, ‹rest› is of the form ‹ak*xk + ... + an*xn+b›
and given as the list ‹[ak,...,an,b]›.
The solution is returned in fully substituted, not triangular form.
The order of the variables/equations is reversed.

We work with equivalence classes given by an abstraction function ‹φ› which must be supplied as a parameter.
This is needed because regular expressions do not have the required algebraic structure.
Only the languages they represent do.
›

definition "mx m n xss = (length xss = m ∧ (∀xs ∈ set xss. length xs = n))"


text ‹scalar * vector›
definition mult1 where
"mult1 = map \<circ> times"

(*
foldl can be used here for more efficient code
but this may make the proofs easier
*)
definition dot :: "'a :: {zero, plus, times} list ⇒ 'a list ⇒ 'a" where
"dot as bs = foldr (+) (map2 times as bs) 0"


text ‹
Distributivity lemmas for φ.
They are provided outside the locale, because they are useful for proving ‹solve1› correct.
›
lemma φ_dot:
  fixes φ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes φ_add: "⋀a b. φ (a + b) = φ a + φ b"
  and φ_mul: "⋀a b. φ (a * b) = φ a * φ b"
  and φ_zero: "φ 0 = 0"
  shows "φ (dot as bs) = dot (map φ as) (map φ bs)"
unfolding dot_def using assms proof(induction as arbitrary: bs)
    case (Cons a as)
    then show ?case apply(cases bs) by simp+
qed simp

lemma φ_dot_Cons:
  fixes φ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes φ_add: "⋀a b. φ (a + b) = φ a + φ b"
  and φ_mul: "⋀a b. φ (a * b) = φ a * φ b"
  and φ_zero: "φ 0 = 0"
  shows "φ (dot (a#as) (b#bs)) = φ a*φ b + φ (dot as bs)"
    unfolding dot_def by (simp add: assms)

lemma dot_mult:
  shows "(c :: 'a :: semiring_1) * (dot as bs) = (dot (map (times c) as) bs)"
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
    case (Cons x xs y ys z zs)
    then show ?case apply auto by (simp add: add.assoc add.left_commute combine_common_factor)
  qed simp

lemma φ_map2_sum:
  fixes φ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes φ_add: "⋀a b. φ (a + b) = φ a + φ b"
  and φ_mul: "⋀a b. φ (a * b) = φ a * φ b"
  and φ_zero: "φ 0 = 0"
  shows "map φ (map2 (+) as bs) = map2 (+) (map φ as) (map φ bs)"
    using assms apply(induction as bs rule: list_induct2') by simp+

lemma φ_map_mult:
  fixes φ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes φ_add: "⋀a b. φ (a + b) = φ a + φ b"
  and φ_mul: "⋀a b. φ (a * b) = φ a * φ b"
  and φ_zero: "φ 0 = 0"
shows"map φ (map (times c) as) = map (times (φ c)) (map φ as)"
  apply(induction as)
  using assms by simp+

lemma φ_mult1:
  fixes φ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes φ_add: "⋀a b. φ (a + b) = φ a + φ b"
  and φ_mul: "⋀a b. φ (a * b) = φ a * φ b"
  and φ_zero: "φ 0 = 0"
shows"map φ (mult1 c as) = (mult1 (φ c) (map φ as))"
  unfolding mult1_def comp_def using assms φ_map_mult by simp

lemma φ_dot_mult:
  fixes φ :: "'a :: {one, zero, plus, times} ⇒ 'b :: semiring_1"
  assumes φ_add: "⋀a b. φ (a + b) = φ a + φ b"
  and φ_mul: "⋀a b. φ (a * b) = φ a * φ b"
  and φ_zero: "φ 0 = 0"
  shows "φ c * φ (dot as bs) = φ (dot (map (times c) as) bs)"
unfolding φ_dot[OF assms] φ_map_mult[OF assms] using dot_mult by blast

locale Gauss =
fixes solve1 :: "'a :: {one, zero, plus, times} ⇒ 'a list ⇒ 'a list"
and φ :: "'a  ⇒ 'b :: semiring_1"
assumes length_solve1: "length(solve1 a cs) = length cs"
and φ_add: "φ (a + b) = φ a + φ b"
and φ_mul: "φ (a * b) = φ a * φ b"
and φ_zero: "φ 0 = 0"
and φ_one: "φ 1 = 1"
and solve1_c: "φ X = φ (dot (solve1 c cs) (Xs@[1])) ⟹  φ X = φ (dot (c#cs) (X#Xs@[1]))"

begin
text ‹We work on a matrix representation of ‹X = A*X+B› where the matrix is ‹(A|B)›.
In each step, ‹solve1 a b› solves an equation ‹X_i = a*X_i + b›
 where b is a list of coefficients of the remaining variables (and the additive constant).›

lemmas φ0 = φ_add φ_mul φ_zero
lemmas φ = φ0 φ_one

text ‹We define our equality relation based on φ›
fun eq where "eq a b = (φ a = φ b)"

text ‹
‹is_sol x cs xs› holds when ‹x› \<equiv> ‹a1*x1 + ... + an*xn + b›
‹cs› are the coefficients  ‹[a1, \<dots>, an, b]›
›
definition is_sol :: "'a ⇒ 'a list ⇒ 'a list ⇒ bool" where
"is_sol x cs xs = (Suc (length xs) = length cs ∧ eq x (dot cs (xs @ [1])))"

(*
is_sols ys A xs :=  ys = A * (xs @ [1])

*)
fun is_sols :: "'a list ⇒ 'a list list ⇒ 'a list ⇒ bool" where
"is_sols (a#as) (eqn # eqns) sol = (is_sol a eqn sol ∧ is_sols as eqns sol)" |
"is_sols [] [] sol = True" |
"is_sols _  [] sol = False" |
"is_sols []  _ sol = False"

text ‹equivalent formulations›
fun is_sols2 where
"is_sols2 as eqns sol = (length as = length eqns ∧ list_all2 (λs eq. is_sol s eq sol) as eqns)"
fun is_sols3 where
"is_sols3 sol eqns = (length sol = length eqns ∧ list_all2 (λs eq. is_sol s eq sol) sol eqns)"

(*
lemma is_sols_length: "is_sols as eqns sol ⟹  length as = length eqns"
  apply(induction as eqns sol rule: is_sols.induct )
  by auto

lemma is_sols_append: "is_sols as1 eqns1 sol ⟹  is_sols as2 eqns2 sol ⟹  is_sols (as1@as2) (eqns1@eqns2) sol"
  apply(induction as1 eqns1 sol rule: is_sols.induct)
  by auto
*)


lemma wrong_len_not_sol: "length sol ≠ length eqns ⟹  ¬is_sols sol eqns sol2"
  apply(induction rule: is_sols.induct)
  by simp+


text ‹equivalence proof›
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

text ‹
Elimination of a variable.

Given the equations:
xi \<equiv> c0 * x0 + c1 * x1 + ... + cn * xn + b
x0 \<equiv> d1 * x1 + ... + dn * xn + b

one can substitute to get

xi \<equiv> e1 * x1 + ... + en * xn + b

eliminating the variable x0

where ‹ds› = [d1, ..., dn, b]
      ‹cs› = [c1, ..., cn, b]
      ‹c›  = c0
      ‹es› = [e1, ..., en, b]

return coefficients es
›
fun subst :: "'a list ⇒ 'a list ⇒ 'a list" where
"subst ds (c#cs) = map2 (+) (mult1 c ds) cs"

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
    have l1: "length (mult1 (φ c) (map φ ds)) = length (map φ cs)"
      using 2(1) unfolding mult1_def comp_def by simp
    have l2: "length (map φ cs) = length (map φ ys @ [1])"
      using 2(2) by simp
    have  "φ x = φ (dot (map2 (+) (mult1 c ds) cs) (ys @ [1]))" using 2(4) by auto
    hence "φ x = dot (map φ (map2 (+) (mult1 c ds) cs)) (map φ (ys @ [1]))" unfolding φ_dot[OF φ0] by simp
    hence "φ x = dot (map φ (map2 (+) (mult1 c ds) cs)) (map φ ys @ [1])" using φ by simp
    hence "φ x = dot (map2 (+) (map φ (mult1 c ds)) (map φ cs)) (map φ ys @ [1])" unfolding φ_map2_sum[OF φ0] by simp
    hence "φ x = dot (map2 (+) (mult1 (φ c) (map φ ds)) (map φ cs)) (map φ ys @ [1])" using φ_mult1[OF φ0] by simp
    hence "φ x = dot (mult1 (φ c) (map φ ds)) (map φ ys @ [1]) + dot (map φ cs) (map φ ys @ [1])" using dot_map2_plus[OF l1 l2] by simp
    hence "φ x = φ c * dot (map φ ds) (map φ ys @ [1]) + dot (map φ cs) (map φ ys @ [1])" unfolding mult1_def comp_def sym[OF dot_mult] by simp
    hence "φ x = φ c * φ (dot ds (ys @ [1])) + φ (dot cs (ys @ [1]))" using φ_dot[OF φ0] φ by simp
    hence "φ x = φ c * φ y + φ (dot cs (ys @ [1]))" using 2(3) by simp
    hence "φ x = φ (dot (c # cs) (y # (ys@ [1])))" using φ_dot_Cons[OF φ0] by simp
    thus  "φ x = φ (dot (c # cs) ((y # ys) @ [1]))" by simp
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
  have "list_all2 (λs eq. is_sol s eq (y # ys)) xs eqs"
    proof
      have "list_all2 (λs eq. is_sol s (subst ds eq) ys) xs eqs"
        using 1 by (simp add: list_all2_map2)
      then show "list_all2 (λs eq. is_sol s (subst ds eq) ys ∧ length eq = b+2) xs eqs"
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
        using subst_correct[OF ‹length ds = length cs› ‹length cs = length ys + 1›, of  y x c] unfolding ccs
        using ‹eq y (dot ds (ys@[1]))› ‹is_sol x (subst ds Cs) ys ∧ length Cs = b + 2› by blast
    qed
  then show ?case using 1 by simp
qed




(*
I think these properties hold.
But additional assumptions about lengths might be needed
they are not required for the correctness proof
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


(*

‹X#Xs› are a solution of the system of equations
they exist but are not known to the algo

(c#cs) are the coefficients of the first equation
ds     are the coefficients with the first variable eliminated
    aka where the system has been solve1 ed for that variable

(e#es)   are the coefficients of some other equation
  where we want to eliminate the first variable

Y is the solution of that equation

*)

text ‹
  ‹solves [] eqns› solves the system of equations given by eqns
  using an accumulator

  In each step the current equation is solved using solve1
  then the variable is eliminated in all equations
›

fun solves :: "'a list list ⇒ 'a list list ⇒ 'a list list" where
"solves sols [] = sols" |
"solves sols ((c # cs) # eqs) =
 (let sol = solve1 c cs;
      eqs' = map (subst sol) eqs;
      sols' = sol # map (subst sol) sols
  in solves sols' eqs')"



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

lemma mx_solves:
  assumes "mx n (Suc n) eqns"
    and "mx m (Suc n) sols"
  shows "mx (n+m) (Suc 0) (solves sols eqns)"
  using length_in_solves[OF assms] mx_def length_solves[OF assms] by blast


lemma length_map_subst: "⟦ mx n b eqns; length sol = b-1 ; length sol ≠ 0 ⟧ ⟹  mx n (b-1) (map (subst sol) eqns)"
unfolding mx_def
apply(induction eqns)
using length_subst
apply auto
apply (metis One_nat_def linordered_nonzero_semiring_class.zero_le_one list.size(3))
by (metis One_nat_def le0 length_subst)

lemma dot_one: "φ (dot (x#xs) [1]) = φ x"
  unfolding dot_def apply auto
  unfolding φ_add φ_zero φ_mul φ_one
  by simp

lemma dot_one_hd: "length xs > 0 ⟹  φ (dot xs [1]) = φ (hd xs)"
  using dot_one apply(cases xs) by simp+


text ‹
The solutions of systems of equations with 0 variables
are trivial to obtain
›

lemma is_sols_trivial: "is_sols ys eqns [] ⟹  map φ ys = map (φ o hd) eqns"
unfolding is_sols2_eqiv is_sols2.simps is_sol_def eq.simps
proof-
  assume "length ys = length eqns ∧ list_all2 (λs eq. Suc (length []) = length eq ∧ φ s = φ (dot eq ([] @ [1]))) ys eqns"
  then have "list_all2 (λs eq. 1 = length eq ∧ φ s = φ (dot eq [1])) ys eqns"
    by simp
  then have "list_all2 (λs eq. φ s = φ (hd eq)) ys eqns"
    using dot_one_hd by (smt (verit) less_numeral_extra(1) list_all2_mono)
  then show "map φ ys = map (φ ∘ hd) eqns"
    apply(induction) by simp+
qed

lemma is_sols_trivial2: "list_all (λeq. length eq = 1) eqns ⟹  map φ ys = map (φ o hd) eqns ⟹  is_sols ys eqns []"
unfolding is_sols2_eqiv is_sols2.simps is_sol_def eq.simps
proof-
  assume l: "list_all (λeq. length eq = 1) eqns"
     and mp: "map φ ys = map (φ ∘ hd) eqns"
  then have len: "length ys = length eqns"
    using map_eq_imp_length_eq by simp

  then have l2: "list_all2 (λs eq. 1 = length eq ∧ φ s = φ (hd eq)) ys eqns"
    using mp l apply(induction ys eqns rule: list_induct2) by simp+
  then have "list_all2 (λs eq. 0 < length eq ∧ φ s = φ (hd eq)) ys eqns"
    by (metis (mono_tags, lifting) less_numeral_extra(1) list_all2_mono)
  then have "list_all2 (λs eq. φ s = φ (dot eq [1])) ys eqns"
    using dot_one_hd list_all2_mono by force
  then have "list_all2 (λs eq. 1 = length eq ∧ φ s = φ (dot eq [1])) ys eqns"
    by (smt (verit, ccfv_SIG) l2 dot_one_hd less_numeral_extra(1) list_all2_mono)
  then show "length ys = length eqns ∧ list_all2 (λs eq. Suc (length []) = length eq ∧ φ s = φ (dot eq ([] @ [1]))) ys eqns"
    using len l by simp
qed


lemma is_sol_eq: "is_sol x ds xs ⟹  eq x y ⟹  is_sol y ds xs"
  unfolding eq.simps is_sol_def by simp

lemma solve1_correct: "⟦ is_sol X (solve1 c cs) Xs ⟧ ⟹  is_sol X (c#cs) (X#Xs) "
  unfolding is_sol_def using solve1_c by (simp add: length_solve1)

text ‹
To prove that a solution of the trivial system returned by the algorithm
is also a solution of the input, we need to generalize to non-empty accumulator values.
›

theorem solves_correct:
  "⟦ b = n+1; mx n b eqns; mx m b sols; length Ys = n;
    is_sols (Xs@Ys) (rev (solves sols eqns)) []
    ⟧ ⟹
    is_sols Ys eqns Ys ∧ is_sols (rev Xs) sols Ys
     "
proof(induction sols eqns arbitrary: Xs Ys n m b rule: solves.induct)
  case (2 sols c cs eqs)
  define sol where "sol = solve1 c cs"
  define eqs' where "eqs' = map (subst sol) eqs"
  define sols' where "sols' = sol # map (subst sol) sols"

  obtain y ys where yys: "y#ys = Ys" by (metis "2.prems"(2,4) length_Cons list.size(3) mx_def nat.simps(3) neq_Nil_conv)

  have [simp]: "length ys = n - 1" using ‹length Ys = n› yys by auto
  have "length cs = b - 1"
    by (metis "2.prems"(2) One_nat_def add_diff_cancel_right' list.set_intros(1) list.size(4) mx_def)
  then have [simp]: "length sol = b - 1"
    using length_solve1 sol_def by presburger
  then have "length sol > 0" using "2.prems"(1,2) mx_def by force

  have mx_eqs: "mx (n-1) b eqs" using "2.prems" unfolding mx_def by auto
  then have "mx (n-1) (b-1) (map (subst sol) eqs)" using length_map_subst ‹length sol = b - 1› ‹length sol > 0› by simp
  then have mx_eqs'[simp]: "mx (n-1) (b-1) eqs'" using eqs'_def by simp
  have "b-1 = n-1+1" using ‹b = n + 1› by (metis "2.prems"(2) One_nat_def add_diff_cancel_right' list.size(4) mx_def)
  have "length cs > 0"
    using ‹length sol > 0› length_solve1 sol_def by auto
  have "mx m (b-1) (map (subst sol) sols)" using "2.prems"(3) ‹length sol = b - 1› ‹length sol > 0› length_map_subst by blast
  then have mx_sols'[simp]: "mx (m+1) (b-1) sols'" using sols'_def by (simp add: ‹length sol = b - 1› mx_def)



  have "is_sols ((Xs @ [y]) @ ys) (rev (solves sols ((c # cs) # eqs))) []"
    using "2.prems" yys by simp
  then have "is_sols ((Xs @ [y]) @ ys) (rev (solves sols' eqs')) []"
    by (metis eqs'_def sol_def sols'_def solves.simps(2))
  then have IH: "is_sols ys eqs' ys ∧ is_sols (rev (Xs @ [y])) sols' ys"
    using "2.IH"[of sol eqs' sols' "b-1" "n-1" "m+1" ys "Xs @ [y]"]
    using sol_def eqs'_def sols'_def ‹b-1 = n-1+1› mx_eqs' mx_sols'
    by simp


  have "is_sols (y # rev Xs) (sol # map (subst sol) sols) ys"
    using IH sols'_def by simp
  then have "is_sol y sol ys"
    by simp
  then have "is_sol y (solve1 c cs) ys"
    using sol_def by simp
  then have "is_sol y (c#cs) (y#ys)"
    using solve1_correct by simp

  moreover have "eq y (dot sol (ys @ [1]))"
    using ‹is_sol y sol ys›
    unfolding is_sol_def by simp

  moreover have "is_sols (rev Xs) (map (subst sol) sols) ys"
    using ‹is_sols (y # rev Xs) (sol # map (subst sol) sols) ys› by simp
  then have "is_sols (rev Xs) sols (y# ys)"
    using map_subst_correct[OF _ _ _ ‹eq y (dot sol (ys @ [1]))› ‹is_sols (rev Xs) (map (subst sol) sols) ys›]
    by (metis "2.prems"(1,3) Suc_eq_plus1 ‹b - 1 = n - 1 + 1› ‹length sol = b - 1› ‹length ys = n - 1› add_2_eq_Suc' add_implies_diff)

  moreover have "is_sols ys (map (subst sol) eqs) ys"
    using eqs'_def IH by simp
  then have "is_sols ys eqs (y#ys)"
    using map_subst_correct[OF _ _ _ ‹eq y (dot sol (ys @ [1]))› ‹is_sols ys (map (subst sol) eqs) ys›, of "n-1" "n-1"]
    by (metis "2.prems"(1,4) One_nat_def Suc_eq_plus1 ‹b - 1 = n - 1 + 1› ‹length sol = b - 1› ‹length ys = n - 1› mx_eqs add_2_eq_Suc' list.size(4) yys)

  ultimately show ?case using yys by auto
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
  ⟦ mx n (Suc n) eqns; length Ys = n;
    is_sols Ys (rev (solves [] eqns)) []
    ⟧ ⟹
    is_sols Ys eqns Ys
     "
using solves_correct[of "n+1" n eqns 0 "[]" Ys "[]"] by (simp add: mx_def)


lemma is_sols_rev: "is_sols (rev Ys) (rev eqns) Xs = is_sols Ys eqns Xs"
  unfolding is_sols2_eqiv by simp

lemma solves_correct'':
assumes mx_eqns: "mx n (Suc n) eqns"
  and Ys: "Ys = rev (map hd (solves [] eqns))"
  shows "is_sols Ys eqns Ys"
proof-
  have mx_sols: "mx 0 (Suc n) []"
    using mx_def by fastforce

  have lenYs: "length Ys = n"
    using Ys length_solves mx_eqns mx_sols by fastforce

  thm mx_solves[OF mx_eqns mx_sols]

  have len1: "list_all (\<lambda>eq. length eq = 1) (solves [] eqns)"
    using mx_solves[OF mx_eqns mx_sols] by (simp add: Ball_set mx_def)
  have "map \<phi> (rev Ys) = map (\<phi> \<circ> hd) (solves [] eqns)"
    by (simp add: Ys)
  then have "is_sols (rev Ys) (solves [] eqns) []"
    using is_sols_trivial2[OF len1] by simp
  then have "is_sols Ys (rev (solves [] eqns)) []"
    using is_sols_rev by fastforce
  then show "is_sols Ys eqns Ys"
    using solves_correct'[OF mx_eqns lenYs]
    by simp
qed


end

text ‹Lang wrapper to define + and *›
datatype 'a langR = Lang "'a list set"
fun unLang where "unLang (Lang x) = x"
abbreviation L where "L ≡ λx. Lang (lang x)"

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

instantiation rexp :: (type) plus begin
  definition plus_rexp where "plus_rexp ≡ Plus" instance ..
end
instantiation rexp :: (type) zero begin
  definition zero_rexp where "zero_rexp ≡ Zero" instance ..
end
instantiation rexp :: (type) one begin
  definition one_rexp where "one_rexp ≡ One" instance ..
end
instantiation rexp :: (type) times begin
  definition times_rexp where "times_rexp ≡ Times" instance ..
end

global_interpretation Gauss
where solve1 = "λr cs. map (λc. Times (Star r) c) cs"
  and φ = "λr. Lang (lang r)"
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
  then have "L X = L (dot (map (times (Star c)) cs) (Xs @ [1]))"
    by (metis map_eq_conv times_rexp_def)

  then have "L X = L (Star c) * L (dot cs (Xs@[1]))"
    using φ_dot_mult[of L] unfolding plus_langR_def plus_rexp_def times_langR_def times_rexp_def zero_langR_def zero_rexp_def
    by fastforce
  then have "lang X = star (lang c) @@ unLang (L (dot cs (Xs@[1])))"
    by (simp add: times_langR_def)
  then have "lang X = lang c @@ lang X ∪ unLang (L (dot cs (Xs@[1])))"
    using Ardens by auto
  then have "L X = L c * L X + L (dot (cs) ((Xs@[1])))"
    by (simp add: plus_langR_def times_langR_def)
  then show "L X = L (dot (c # cs) (X # Xs @ [1]))"
    using φ_dot_Cons[of L] unfolding plus_langR_def plus_rexp_def times_langR_def times_rexp_def zero_langR_def zero_rexp_def
    by fastforce

qed

value "solves_r [] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [[x,y,z]] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [] [[a00,a01,b0]]"

