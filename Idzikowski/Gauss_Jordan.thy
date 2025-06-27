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

(*equivalent zu foldr, mit foldr beweis leichter*)
definition dot where
"dot as bs = foldl (+) 0 (map2 mult as bs)"


locale Gauss =
fixes solve1 :: "'a :: {one, zero, plus, times} ⇒ 'a list ⇒ 'a list"
and γ :: "'a  ⇒ 'b :: semiring_1"
assumes length_solve1: "length(solve1 a cs) = length cs"
and γ_add: "γ (a + b) = γ a + γ b"
and γ_mul: "γ (a * b) = γ a * γ b"
and γ_zero: "γ 0 = 0"

begin
text ‹We work on a matrix representation of ‹X = A*X+B› where the matrix is ‹(A|B)›.
In each step, ‹solve1 a b› solves an equation ‹X_i = a*X_i + b›
 where b is a list of coefficients of the remaining variables (and the additive constant).›


fun eq where "eq a b = (γ a = γ b) "

(*
is_sol x ds xs :=   x = ds * (xs @ [1])
*)
definition is_sol :: "'a ⇒ 'a list ⇒ 'a list ⇒ bool" where
"is_sol a cs sol = eq a (dot cs sol)"

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


lemma map2_Cons: "map2 f (a#as) (b#bs) = f a b # (map2 f as bs)"
  by simp

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

definition mult1 where
"mult1 = map o mult"

fun subst :: "'a list ⇒ 'a list ⇒ 'a list" where
"subst sol (c#cs) = map2 (+) (mult1 c sol) cs"



(*
TODO
wie mache ich das zu einem lemma im locale?
wie benutze ich da schon is_sol?
*)
lemma solve1_correct: "is_sol X (c#cs) (X#Xs) \<Longrightarrow>  is_sol X (solve1 c cs) Xs"
  sorry

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
lemma subst_correct:
  assumes (*maybe not needed*) "is_sol X cs (X#Xs)"
          "is_sol X ds Xs"
          "is_sol Y es (X#Xs)"
  shows "is_sol Y (subst ds es) Xs"
using assms unfolding is_sol_def
  sorry

lemma map_subst_correct: "⟦
  is_sol x ds xs ;
  is_sols ys eqs (x#xs)
⟧ ⟹  is_sols ys (map (subst ds) eqs) xs"
proof(induction eqs)
  case Nil
  then show ?case using append_is_Nil_conv is_sols_length by fastforce
next
  case (Cons a eqs)
  then show ?case sorry
qed




fun solves :: "'a list list ⇒ 'a list list ⇒ 'a list list" where
(* would it be a good idea to map hd here? *)
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

lemma length_map_subst: "⟦ mx n b eqns; length sol = b-1 ; length sol ≠ 0 ⟧ ⟹  mx n (b-1) (map (subst sol) eqns)"
unfolding mx_def
apply(induction eqns)
using length_subst
apply auto
apply (metis One_nat_def linordered_nonzero_semiring_class.zero_le_one list.size(3))
by (metis One_nat_def le0 length_subst)

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

theorem solves_is_sols:
  shows "⟦ b = n+1; mx n b eqns; mx m b sols;
    is_sols Ys eqns Ys;
    is_sols (rev Xs) sols Ys ⟧
    ⟹  is_sols (Xs@Ys) (rev (solves sols eqns)) []"
proof(induction sols eqns arbitrary: Xs Ys n m b rule: solves.induct)
  case (1 sols)
  then have "Ys = []" using is_sols_length by fastforce
  then show ?case using 1 unfolding is_sols2_eqiv by (simp add: list_all2_rev1)
next
  case (2 sols c cs eqs)
  obtain sol where sol: "sol = solve1 c cs" by auto
  obtain eqs' where eqs': "eqs' = map (subst sol) eqs" by auto
  obtain sols' where sols': "sols' = sol # map (subst sol) sols" by auto

  obtain y ys where yys: "y#ys = Ys" by (metis "2.prems"(4) is_sols.simps(4) neq_Nil_conv)

  have "length cs = b - 1"
    by (metis "2.prems"(2) One_nat_def add_diff_cancel_right' list.set_intros(1) list.size(4) mx_def)
  then have "length sol = b - 1"
    using length_solve1 sol by presburger


  have "length sol ≠ 0" by (metis "2.prems"(1,2) ‹length sol = b - 1› add_diff_cancel_right' length_0_conv list.distinct(1) mx_def)

  have "mx (n-1) b eqs" using ‹mx n b ((c # cs) # eqs)› unfolding mx_def by auto
  then have "mx (n-1) (b-1) (map (subst sol) eqs)" using length_map_subst[OF ‹mx (n-1) b eqs› ‹length sol = b - 1› ‹length sol ≠ 0›] by simp
  then have "mx (n-1) (b-1) eqs'" using eqs' by simp


  have "b-1 = n-1+1" using ‹b = n + 1› by (metis "2.prems"(2) One_nat_def add_diff_cancel_right' list.size(4) mx_def)



  have "is_sol y (c#cs) (y#ys)" using yys ‹is_sols Ys ((c # cs) # eqs) Ys›
    by auto
  then have "is_sol y sol ys"
    using solve1_correct sol by simp

  have "is_sols ys eqs (y#ys)" using ‹is_sols Ys ((c # cs) # eqs) Ys› yys by auto
  then have "is_sols ys eqs' ys" using eqs' map_subst_correct[OF ‹is_sol y sol ys› ‹is_sols ys eqs (y#ys)›] by simp

  have "is_sols (rev Xs) (map (subst sol) sols) ys" using ‹is_sols (rev Xs) sols Ys› map_subst_correct ‹is_sol y sol ys› yys by blast
  then have "is_sols (rev (Xs @ [y])) sols' ys" by (simp add: ‹is_sol y sol ys› sols')

  have "mx m (b-1) (map (subst sol) sols)" using "2.prems"(3) ‹length sol = b - 1› ‹length sol ≠ 0› length_map_subst by blast
  then have "mx (m+1) (b-1) sols'" using sols' by (simp add: ‹length sol = b - 1› mx_def)

  show ?case using "2.IH"[OF sol eqs' sols' ‹b-1 = n-1+1› ‹mx (n - 1) (b - 1) eqs'› ‹mx (m+1) (b - 1) sols'› ‹is_sols ys eqs' ys› ‹is_sols (rev (Xs @ [y])) sols' ys›]
    by (metis append_Cons append_assoc eq_Nil_appendI eqs' sol sols' solves.simps(2) yys)
next
  case (3 a va)
  have "b = 0" using ‹mx n b ([] # va)› unfolding mx_def by simp
  then have "Ys = []" by (simp add: "3.prems"(1))
  then show ?case using "3.prems"(4) by auto
qed







end

datatype 'a langR = Lang "'a list set"
fun unLang where "unLang (Lang x) = x"

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
qed

value "solves_r [] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [[x,y,z]] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [] [[a00,a01,b0]]"

