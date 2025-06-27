theory Gauss_Jordan
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

text \<open>Solver for a system of linear equations \<open>xi = a0 * x0 + ... + an*xn + b\<close>
where \<open>+, * :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> are parameters.
The system is represented in matrix form: \<open>X = A*X + B\<close> where the matrix is of type \<open>'a list list\<close>
and we work with only a single matrix \<open>A\<close> augmented with the vector \<open>B\<close>.
In each step, the solver eliminates one variable. This step must be supplied as a parameter
\<open>solve1\<close> that solves \<open>x = a * x + rest\<close> for \<open>x\<close>. Here, \<open>rest\<close> is of the form \<open>ak*xk + ... + an*xn+b\<close>
and given as the list \<open>[ak,...,an,b]\<close>.
The solution is returned in fully substituted, not triangular form.
The order of the variables/equations is reversed.\<close>

definition "mx m n xss = (length xss = m \<and> (\<forall>xs \<in> set xss. length xs = n))"

locale Gauss =
fixes zero :: 'a
and add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
and mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
and solve1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
assumes length_solve1: "length(solve1 a cs) = length cs"
begin
text \<open>We work on a matrix representation of \<open>X = A*X+B\<close> where the matrix is \<open>(A|B)\<close>.
In each step, \<open>solve1 a b\<close> solves an equation \<open>X_i = a*X_i + b\<close>
 where b is a list of coefficients of the remaining variables (and the additive constant).\<close>

(*equivalent zu foldr, mit foldr beweis leichter*)
definition dot :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a" where
"dot as bs = foldl add zero (map2 mult as bs)"


definition zipSum :: "'a list ⇒ 'a list ⇒ 'a list" (infixl "+z+" 65) where
"zipSum = map2 add"

lemma zipSumCons: "(a#as) +z+ (b#bs) = add a b # (as+z+bs)"
  unfolding zipSum_def by simp

(*
is_sol x ds xs :=   x = ds * (xs @ [1])
*)
definition is_sol :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sol a cs sol = eq a (dot cs sol)"

(*
is_sols ys M xs :=  ys = M * (xs @ [1])

*)
fun is_sols :: "'a list \<Rightarrow> 'a list list ⇒ 'a list \<Rightarrow> bool" where
"is_sols (a#as) (eqn # eqns) sol = (is_sol a eqn sol \<and> is_sols as eqns sol)" |
"is_sols [] [] sol = True" |
"is_sols _  [] sol = False" |
"is_sols []  _ sol = False"

lemma is_sols_length: "is_sols as eqns sol \<Longrightarrow> length as = length eqns"
  apply(induction as eqns sol rule: is_sols.induct )
  by auto

lemma is_sols_append: "is_sols as1 eqns1 sol \<Longrightarrow> is_sols as2 eqns2 sol \<Longrightarrow> is_sols (as1@as2) (eqns1@eqns2) sol"
  apply(induction as1 eqns1 sol rule: is_sols.induct)
  by auto


fun is_sols2 where
"is_sols2 as eqns sol = (length as = length eqns \<and> list_all2 (λs eq. is_sol s eq sol) as eqns)"

(*maybe better with ∀*)
fun is_sols3 where
"is_sols3 sol eqns = (length sol = length eqns \<and> list_all2 (λs eq. is_sol s eq sol) sol eqns)"

lemma wrong_len_not_sol: "length sol \<noteq> length eqns \<Longrightarrow> \<not>is_sols sol eqns sol2"
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
    have "is_sols2 (a # as) (eqn # eqns) sol = list_all2 (\<lambda>x y. is_sol x y sol) (a # as) (eqn # eqns)"
      using 1 by simp
    also have "\<dots> = (is_sol a eqn sol \<and> is_sols2 as eqns sol)"
      using len by simp
    then show ?case using 1 by simp
  qed simp+
qed (simp add: wrong_len_not_sol)

corollary is_sols3_eqiv: "is_sols3 sols eqns = is_sols sols eqns sols"
  by (simp add: is_sols2_eqiv)

definition mult1 where
"mult1 = map o mult"

fun subst :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"subst sol (c#cs) = map2 add (mult1 c sol) cs"




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

lemma map_subst_correct: "\<lbrakk>
  is_sol x ds xs ;
  is_sols ys eqs (x#xs)
\<rbrakk> \<Longrightarrow> is_sols ys (map (subst ds) eqs) xs"
proof(induction eqs)
  case Nil
  then show ?case using append_is_Nil_conv is_sols_length by fastforce
next
  case (Cons a eqs)
  then show ?case sorry
qed



lemma solve1_correct:
  assumes "is_sol X (c#cs) (X#Xs)"
  shows "is_sol X (solve1 c cs) Xs"
  sorry


fun solves :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
(* would it be a good idea to map hd here? *)
"solves sols [] = sols" |
"solves sols ((c # cs) # eqs) =
 (let sol = solve1 c cs;
      eqs' = map (subst sol) eqs;
      sols' = sol # map (subst sol) sols
  in solves sols' eqs')"

lemma length_subst:
  "\<lbrakk> length sol = length cs - 1; length cs \<noteq> 0 \<rbrakk> \<Longrightarrow> length(subst sol cs) = length sol"
by(auto simp: neq_Nil_conv mult1_def)

lemma length_solves:
  "\<lbrakk> mx k (Suc k) eqs; mx n (Suc k) sols \<rbrakk> \<Longrightarrow> length(solves sols eqs) = k+n"
proof(induction sols eqs arbitrary: k n rule: solves.induct)
  case (1 sols)
  then show ?case by(auto simp: mx_def)
next
  case (2 sols c cs eqs)
  show ?case using "2.prems" "2.IH"[OF refl refl refl, of "k-1" "n+1"]
    by(auto simp add: length_solve1 length_subst mx_def Let_def)
qed (auto simp: mx_def)

lemma length_in_solves:
  "\<lbrakk> mx k (Suc k) eqs; mx n (Suc k) sols; cs \<in> set(solves sols eqs) \<rbrakk> \<Longrightarrow> length cs = Suc 0"
proof(induction sols eqs arbitrary: cs k n rule: solves.induct)
  case (1 sols)
  then show ?case by(auto simp: mx_def)
next
  case (2 sols c cs eqs as)
  show ?case using "2.prems"
    using  "2.IH"[OF refl refl refl, of "k-1" "n+1" as]
    by(auto simp add: length_solve1 length_subst mx_def Let_def)
qed (auto simp: mx_def)

lemma length_map_subst: "\<lbrakk> mx n b eqns; length sol = b-1 ; length sol \<noteq> 0 \<rbrakk> \<Longrightarrow>  mx n (b-1) (map (subst sol) eqns)"
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
  shows "\<lbrakk> b = n+1; mx n b eqns; mx m b sols;
    is_sols Ys eqns Ys;
    is_sols (rev Xs) sols Ys \<rbrakk>
    \<Longrightarrow> is_sols (Xs@Ys) (rev (solves sols eqns)) []"
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


  have "length sol \<noteq> 0" by (metis "2.prems"(1,2) \<open>length sol = b - 1\<close> add_diff_cancel_right' length_0_conv list.distinct(1) mx_def)

  have "mx (n-1) b eqs" using ‹mx n b ((c # cs) # eqs)› unfolding mx_def by auto
  then have "mx (n-1) (b-1) (map (subst sol) eqs)" using length_map_subst[OF ‹mx (n-1) b eqs› ‹length sol = b - 1› ‹length sol \<noteq> 0›] by simp
  then have "mx (n-1) (b-1) eqs'" using eqs' by simp


  have "b-1 = n-1+1" using ‹b = n + 1› by (metis "2.prems"(2) One_nat_def add_diff_cancel_right' list.size(4) mx_def)



  have "is_sol y (c#cs) (y#ys)" using yys ‹is_sols Ys ((c # cs) # eqs) Ys›
    by auto
  then have "is_sol y sol ys"
    using solve1_correct sol by simp

  have "is_sols ys eqs (y#ys)" using ‹is_sols Ys ((c # cs) # eqs) Ys› yys by auto
  then have "is_sols ys eqs' ys" using eqs' map_subst_correct[OF ‹is_sol y sol ys› ‹is_sols ys eqs (y#ys)›] by simp

  have "is_sols (rev Xs) (map (subst sol) sols) ys" using ‹is_sols (rev Xs) sols Ys› map_subst_correct \<open>is_sol y sol ys\<close> yys by blast
  then have "is_sols (rev (Xs @ [y])) sols' ys" by (simp add: \<open>is_sol y sol ys\<close> sols')

  have "mx m (b-1) (map (subst sol) sols)" using "2.prems"(3) \<open>length sol = b - 1\<close> \<open>length sol \<noteq> 0\<close> length_map_subst by blast
  then have "mx (m+1) (b-1) sols'" using sols' by (simp add: \<open>length sol = b - 1\<close> mx_def)

  show ?case using "2.IH"[OF sol eqs' sols' ‹b-1 = n-1+1› ‹mx (n - 1) (b - 1) eqs'› ‹mx (m+1) (b - 1) sols'› ‹is_sols ys eqs' ys› ‹is_sols (rev (Xs @ [y])) sols' ys›]
    by (metis append_Cons append_assoc eq_Nil_appendI eqs' sol sols' solves.simps(2) yys)
next
  case (3 a va)
  have "b = 0" using ‹mx n b ([] # va)› unfolding mx_def by simp
  then have "Ys = []" by (simp add: "3.prems"(1))
  then show ?case using "3.prems"(4) by auto
qed









end




global_interpretation Gauss where zero = Zero and add = Plus and mult = Times and
solve1 = "\<lambda>r cs. map (\<lambda>c. Times (Star r) c) cs" and eq = "\<lambda>r s. lang r = lang s"
defines solves_r = solves and subst_r = subst and mult1_r = mult1
proof (standard, goal_cases)
  case (1 a cs)
  then show ?case by simp
qed

value "solves_r [] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [[x,y,z]] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [] [[a00,a01,b0]]"
