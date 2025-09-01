(* Author: Aleksy Idzikowski and Tobias Nipkow *)

theory Gauss_Jordan
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

text \<open>Solver for a system of linear equations \<open>xi = a0 * x0 + ... + an*xn + b\<close>
where \<open>+, * :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> are type classes.
The system is represented in matrix form: \<open>X = A*X + B\<close> where the matrix is of type \<open>'a list list\<close>
and we work with only a single matrix \<open>A\<close> augmented with the vector \<open>B\<close>.
In each step, the solver eliminates one variable. This step must be supplied as a parameter
\<open>solve1\<close> that solves \<open>x = a * x + rest\<close> for \<open>x\<close>. Here, \<open>rest\<close> is of the form \<open>ak*xk + ... + an*xn+b\<close>
and given as the list \<open>[ak,...,an,b]\<close>.
The solution is returned in fully substituted, not triangular form.
The order of the variables/equations is reversed.

We work with equivalence classes given by an abstraction function \<open>\<phi>\<close> which must be supplied as a parameter.
This is needed because regular expressions do not have the required algebraic structure.
Only the languages they represent do.
\<close>

definition "mx m n xss = (length xss = m \<and> (\<forall>xs \<in> set xss. length xs = n))"


text \<open>scalar * vector\<close>
definition mult1 :: "'a::times \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"mult1 = map \<circ> times"

text \<open>Dot product of two vectors represented as lists:\<close>
definition dot :: "'a :: {zero, plus, times} list \<Rightarrow> 'a list \<Rightarrow> 'a" where
"dot as bs = foldr (+) (map2 times as bs) 0"

lemma dot_mult: "(c :: 'a :: semiring_1) * (dot as bs) = (dot (map (times c) as) bs)"
  unfolding dot_def proof(induction as bs rule: list_induct2')
    case (4 x xs y ys)
    then show ?case by (auto simp add: distrib_left mult.assoc)
  qed simp+

lemma dot_map2_plus:
  assumes "length as = length bs"
  and "length bs = length cs"
  shows "dot (map2 (+) as bs) (cs :: 't :: semiring_1 list) = dot as cs + dot bs cs"
using assms unfolding dot_def proof(induction as bs cs rule: list_induct3)
  case (Cons x xs y ys z zs)
  then show ?case by (auto simp add: add.assoc add.left_commute combine_common_factor)
qed simp

text \<open>
Distributivity lemmas for the abstraction function \<phi>.
They are provided outside the Gauss locale, because they are useful for proving \<open>solve1\<close> correct.
\<close>
locale Abstraction =
fixes \<phi> :: "'a :: {one, zero, plus, times} \<Rightarrow> 'b :: semiring_1"
assumes \<phi>_add: "\<phi> (a + b) = \<phi> a + \<phi> b"
and \<phi>_mul: "\<phi> (a * b) = \<phi> a * \<phi> b"
and \<phi>_zero: "\<phi> 0 = 0"
and \<phi>_one: "\<phi> 1 = 1"
begin

lemmas \<phi>0 = \<phi>_add \<phi>_mul \<phi>_zero
lemmas \<phi> = \<phi>0 \<phi>_one

lemma \<phi>_dot: "\<phi> (dot as bs) = dot (map \<phi> as) (map \<phi> bs)"
  unfolding dot_def apply(induction as bs rule: list_induct2') by (simp add: \<phi>0)+

lemma \<phi>_dot_Cons: "\<phi> (dot (a#as) (b#bs)) = \<phi> a*\<phi> b + \<phi> (dot as bs)"
  by (simp add: \<phi>0 dot_def)

lemma \<phi>_map2_sum: "map \<phi> (map2 (+) as bs) = map2 (+) (map \<phi> as) (map \<phi> bs)"
    apply(induction as bs rule: list_induct2') by (simp add: \<phi>0)+

lemma \<phi>_map_mult: "map \<phi> (map (times c) as) = map (times (\<phi> c)) (map \<phi> as)"
  apply(induction as) by (simp add: \<phi>0)+

lemma \<phi>_mult1: "map \<phi> (mult1 c as) = (mult1 (\<phi> c) (map \<phi> as))"
  by (simp add: mult1_def comp_def \<phi>0 \<phi>_map_mult)

lemma \<phi>_dot_mult: "\<phi> c * \<phi> (dot as bs) = \<phi> (dot (map (times c) as) bs)"
  by (metis \<phi>_dot \<phi>_map_mult dot_mult)

lemma dot_one: "\<phi> (dot (x#xs) [1]) = \<phi> x"
  unfolding dot_def by (auto simp add: \<phi>)

lemma dot_one_hd: "length xs > 0 \<Longrightarrow>  \<phi> (dot xs [1]) = \<phi> (hd xs)"
  using dot_one by(cases xs) simp+

end


locale Gauss = Abstraction \<phi> for \<phi>:: "'a :: {one, zero, plus, times} \<Rightarrow> 'b :: semiring_1"  +
fixes solve1 :: "'a :: {one, zero, plus, times} \<Rightarrow> 'a list \<Rightarrow> 'a list"
assumes length_solve1: "length(solve1 a cs) = length cs"
and solve1_c: "\<phi> X = \<phi> (dot (solve1 c cs) Xs) \<Longrightarrow>  \<phi> X = \<phi> (dot (c#cs) (X#Xs))"

begin
text \<open>We work on a matrix representation of \<open>X = A*X+B\<close> where the matrix is \<open>(A|B)\<close>.
In each step, \<open>solve1 a b\<close> solves an equation \<open>X_i = a*X_i + b\<close>
 where b is a list of coefficients of the remaining variables (and the additive constant).\<close>

text \<open>We define our equality relation based on \<open>\<phi>\<close>\<close>
fun eq where "eq a b = (\<phi> a = \<phi> b)"

text \<open>
\<open>is_sol x cs xs\<close> holds if \<open>x = a1*x1 + ... + an*xn + b\<close>
where \<open>cs\<close> are the coefficients \<open>[a1, \<dots>, an, b]\<close>
\<close>
definition is_sol :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sol x cs xs = (length cs = length xs + 1 \<and> eq x (dot cs (xs @ [1])))"

text\<open>
\<open>is_sols ys A xs\<close> holds if \<open>ys = A * (xs @ [1])\<close>
In words: \<open>is_sols\<close> holds if \<open>ys\<close> is the vector obtained by plugging \<open>xs\<close> into the system of equations \<open>A\<close>.
Since we are solving fixed point equations \<open>ys\<close> and \<open>xs\<close> should be equivalent once we have found a solution,
but the more general version is needed to describe the state, while the algorithm is running.
\<close>

fun is_sols where
"is_sols as eqns sol = list_all2 (\<lambda>s eq. is_sol s eq sol) as eqns"

text \<open>
Elimination of a variable.

Given the equations:
\<open>xi = c0 * x0 + c1 * x1 + ... + cn * xn + b\<close>
\<open>x0 = d1 * x1 + ... + dn * xn + d\<close> (the result of solving the original \<open>x0 = a0*x0 + ...\<close>)

one can substitute for \<open>x0\<close> in the \<open>xi\<close> equation to get

\<open>xi = e1 * x1 + ... + en * xn + e\<close>

where, \<open>ej\<close> = \<open>c0 * dj + cj\<close>, \<open>e\<close> = \<open>c0 * d + b\<close>, thus eliminating the variable \<open>x0\<close>.

where \<open>ds\<close> = \<open>[d1, ..., dn, d]\<close>
      \<open>cs\<close> = \<open>[c1, ..., cn, b]\<close>
      \<open>c\<close>  = \<open>c0\<close>
      \<open>es\<close> = \<open>[e1, ..., en, e]\<close>
\<close>
fun subst :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"subst ds (c#cs) = map2 (+) (mult1 c ds) cs"

lemma subst_correct:
 "\<lbrakk> length ds = length cs;
    length cs = length ys + 1;
    eq y (dot ds (ys@[1]));
    is_sol x (subst ds (c#cs)) ys
  \<rbrakk> \<Longrightarrow>  is_sol x (c#cs) (y#ys)"
unfolding eq.simps is_sol_def subst.simps eq.simps proof(standard, goal_cases)
    case 1
    show ?case using \<open>length cs = length ys + 1\<close> by simp
  next
    case 2
    have l1: "length (mult1 (\<phi> c) (map \<phi> ds)) = length (map \<phi> cs)"
      using 2(1) unfolding mult1_def comp_def by simp
    have l2: "length (map \<phi> cs) = length (map \<phi> ys @ [1])"
      using 2(2) by simp
    have  "\<phi> x = \<phi> (dot (map2 (+) (mult1 c ds) cs) (ys @ [1]))" using 2(4) by auto
    also have "\<dots> = dot (map \<phi> (map2 (+) (mult1 c ds) cs)) (map \<phi> (ys @ [1]))" unfolding \<phi>_dot by simp
    also have "\<dots> = dot (map \<phi> (map2 (+) (mult1 c ds) cs)) (map \<phi> ys @ [1])" using \<phi> by simp
    also have "\<dots> = dot (map2 (+) (map \<phi> (mult1 c ds)) (map \<phi> cs)) (map \<phi> ys @ [1])" unfolding \<phi>_map2_sum by simp
    also have "\<dots> = dot (map2 (+) (mult1 (\<phi> c) (map \<phi> ds)) (map \<phi> cs)) (map \<phi> ys @ [1])" using \<phi>_mult1 by simp
    also have "\<dots> = dot (mult1 (\<phi> c) (map \<phi> ds)) (map \<phi> ys @ [1]) + dot (map \<phi> cs) (map \<phi> ys @ [1])" using dot_map2_plus[OF l1 l2] by simp
    also have "\<dots> = \<phi> c * dot (map \<phi> ds) (map \<phi> ys @ [1]) + dot (map \<phi> cs) (map \<phi> ys @ [1])" unfolding mult1_def comp_def dot_mult by simp
    also have "\<dots> = \<phi> c * \<phi> (dot ds (ys @ [1])) + \<phi> (dot cs (ys @ [1]))" using \<phi>_dot \<phi> by simp
    also have "\<dots> = \<phi> c * \<phi> y + \<phi> (dot cs (ys @ [1]))" using 2(3) by simp
    also have "\<dots> = \<phi> (dot (c # cs) (y # (ys@ [1])))" using \<phi>_dot_Cons by simp
    finally show "\<phi> x = \<phi> (dot (c # cs) ((y # ys) @ [1]))" by simp
  qed

lemma map_subst_correct:
 "\<lbrakk> length ys = b;
    eq y (dot ds (ys@[1]));
    mx n (b+2) eqns;
    length ds = b+1;
    is_sols xs (map (subst ds) eqns) ys
  \<rbrakk> \<Longrightarrow> is_sols xs eqns (y#ys)"
unfolding is_sols.simps proof(goal_cases)
  case 1
  have "list_all2 (\<lambda>s eq. is_sol s eq (y # ys)) xs eqns"
    proof
      have "list_all2 (\<lambda>s eq. is_sol s (subst ds eq) ys) xs eqns"
        using 1 by (simp add: list_all2_map2)
      then show "list_all2 (\<lambda>s eq. is_sol s (subst ds eq) ys \<and> length eq = b+2) xs eqns"
        using \<open>mx n (b+2) eqns\<close> unfolding mx_def using list.rel_mono_strong by fastforce
    next
      fix x Cs
      assume "is_sol x (subst ds Cs) ys \<and> length Cs = b+2"
      then have "length Cs = b+2" by simp
      then obtain c cs where ccs: "c#cs = Cs" by (metis add_2_eq_Suc' list.size(3) nat.distinct(1) neq_Nil_conv)
      then have "length cs = b+1"
        using \<open>length Cs = b+2\<close> by fastforce
      then have "length ds = length cs"
        using "1"(4) by simp

      have "length cs = length ys + 1"
        using \<open>length cs = b+1\<close> \<open>length ys = b\<close> by simp

      show "is_sol x Cs (y # ys)"
        using subst_correct[OF \<open>length ds = length cs\<close> \<open>length cs = length ys + 1\<close>, of  y x c] unfolding ccs
        using \<open>eq y (dot ds (ys@[1]))\<close> \<open>is_sol x (subst ds Cs) ys \<and> length Cs = b + 2\<close> by blast
    qed
  then show ?case using 1 by simp
qed

text \<open>
  \<open>solves [] eqns\<close> solves the system of equations given by \<open>eqns\<close> using an accumulator.
  In each step the current equation is solved using \<open>solve1\<close>
  then the variable is eliminated in all other equations
\<close>

fun solves :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
"solves sols [] = sols" |
"solves sols ((c # cs) # eqns) =
 (let sol = solve1 c cs;
      eqns' = map (subst sol) eqns;
      sols' = sol # map (subst sol) sols
  in solves sols' eqns')"


lemma length_subst:
  "\<lbrakk> length sol = length cs - 1; length cs \<noteq> 0 \<rbrakk> \<Longrightarrow> length(subst sol cs) = length sol"
by(auto simp: neq_Nil_conv mult1_def)

lemma length_solves:
  "\<lbrakk> mx k (k+1) eqns; mx n (k+1) sols \<rbrakk> \<Longrightarrow> length(solves sols eqns) = k+n"
proof(induction sols eqns arbitrary: k n rule: solves.induct)
  case (1 sols)
  then show ?case by(auto simp: mx_def)
next
  case (2 sols c cs eqns)
  show ?case using "2.prems" "2.IH"[OF refl refl refl, of "k-1" "n+1"]
    by(auto simp: length_solve1 length_subst mx_def Let_def)
qed (auto simp: mx_def)

lemma length_in_solves:
  "\<lbrakk> mx k (k+1) eqns; mx n (k+1) sols; cs \<in> set(solves sols eqns) \<rbrakk> \<Longrightarrow> length cs = 1"
proof(induction sols eqns arbitrary: cs k n rule: solves.induct)
  case (1 sols)
  then show ?case by(auto simp: mx_def)
next
  case (2 sols c cs eqns as)
  show ?case using "2.prems"
    using  "2.IH"[OF refl refl refl, of "k-1" "n+1" as]
    by(auto simp: length_solve1 length_subst mx_def Let_def)
qed (auto simp: mx_def)

lemma mx_solves:
  assumes "mx n (n+1) eqns"
    and "mx m (n+1) sols"
  shows "mx (n+m) 1 (solves sols eqns)"
  using length_in_solves[OF assms] mx_def length_solves[OF assms]
  by (metis)

lemma length_map_subst: "\<lbrakk> mx n (b+1) eqns; length sol = b; length sol \<noteq> 0 \<rbrakk>
  \<Longrightarrow> mx n b (map (subst sol) eqns)"
unfolding mx_def
proof(induction eqns)
  case (Cons)
  then show ?case by (simp add: length_subst)
qed simp


text \<open>The solutions of systems of equations with no variables are trivial to obtain:\<close>

lemma is_sols_trivial2:
  "\<lbrakk> list_all (\<lambda>eq. length eq = 1) eqns;  map \<phi> ys = map (\<phi> o hd) eqns \<rbrakk> \<Longrightarrow> is_sols ys eqns []"
unfolding is_sols.simps is_sol_def eq.simps
proof-
  assume l: "list_all (\<lambda>eq. length eq = 1) eqns"
     and mp: "map \<phi> ys = map (\<phi> \<circ> hd) eqns"
  then have len: "length ys = length eqns"
    using map_eq_imp_length_eq by simp

  then have l2: "list_all2 (\<lambda>s eq. length eq = 1 \<and> \<phi> s = \<phi> (hd eq)) ys eqns"
    using mp l apply(induction ys eqns rule: list_induct2) by simp+
  then have "list_all2 (\<lambda>s eq. 0 < length eq \<and> \<phi> s = \<phi> (hd eq)) ys eqns"
    by (metis (mono_tags, lifting) less_numeral_extra(1) list_all2_mono)
  then have "list_all2 (\<lambda>s eq. \<phi> s = \<phi> (dot eq [1])) ys eqns"
    using dot_one_hd list_all2_mono by force
  then have "list_all2 (\<lambda>s eq. length eq = 1 \<and> \<phi> s = \<phi> (dot eq [1])) ys eqns"
    by (smt (verit, ccfv_SIG) l2 dot_one_hd less_numeral_extra(1) list_all2_mono)
  then show "list_all2 (\<lambda>s eq. length eq = length [] + 1  \<and> \<phi> s = \<phi> (dot eq ([] @ [1]))) ys eqns"
    using len l by simp
qed

lemma solve1_correct: "\<lbrakk> is_sol X (solve1 c cs) Xs \<rbrakk> \<Longrightarrow> is_sol X (c#cs) (X#Xs)"
  unfolding is_sol_def using solve1_c by (simp add: length_solve1)

text \<open>
To prove that a solution of the trivial system returned by the algorithm
is also a solution of the input, we need to generalize to non-empty accumulator values.
\<close>

theorem solves_sound_generalization:
  "\<lbrakk> mx n (n+1) eqns; mx m (n+1) sols; length Ys = n;
    is_sols (Xs@Ys) (rev (solves sols eqns)) []
   \<rbrakk> \<Longrightarrow> is_sols Ys eqns Ys \<and> is_sols (rev Xs) sols Ys"
proof(induction sols eqns arbitrary: Xs Ys n m rule: solves.induct)
  case (2 sols c cs eqns)
  let ?sol = "solve1 c cs"
  let ?eqns' = "map (subst ?sol) eqns"
  let ?sols' = "?sol # map (subst ?sol) sols"

  obtain n' where n': "Suc n' = n"
    by (metis "2.prems"(1) length_Cons mx_def)
  obtain y ys where yys: "y#ys = Ys"
    by (metis "2.prems"(3) length_Suc_conv n')

  then have len_ys[simp]: "length ys = n'" using n' 2 by auto
  have "length cs = n"
    using "2.prems"(1) unfolding mx_def by simp
  then have len_sol[simp]: "length ?sol = n"
    using length_solve1 "2.prems"(1) by presburger

  have mx_eqns: "mx n' (Suc n) eqns" using "2.prems" unfolding mx_def using n' by auto
  then have "mx n' n (map (subst ?sol) eqns)" using length_map_subst n' by auto
  then have mx_eqns'[simp]: "mx n' n ?eqns'" by simp

  have "mx m n (map (subst ?sol) sols)" using length_map_subst "2.prems"(2) n' by simp
  then have mx_sols': "mx (Suc m) n ?sols'" by (simp add: mx_def)

  have "is_sols ((Xs @ [y]) @ ys) (rev (solves sols ((c # cs) # eqns))) []"
    using "2.prems" yys by simp
  then have "is_sols ((Xs @ [y]) @ ys) (rev (solves ?sols' ?eqns')) []"
    by (metis solves.simps(2))
  then have IH: "is_sols ys ?eqns' ys \<and> is_sols (rev (Xs @ [y])) ?sols' ys"
    using "2.IH"[of ?sol ?eqns' ?sols' "n'" "Suc m" ys "Xs @ [y]"]
    using n' mx_eqns' mx_sols' "2.prems"(1)
    by simp

  have sol_yXs: "is_sols (y # rev Xs) (?sol # map (subst ?sol) sols) ys"
    using IH by simp
  then have "is_sol y ?sol ys"
    by simp
  then have "is_sol y (c#cs) (y#ys)"
    using solve1_correct by simp

  moreover have y: "eq y (dot ?sol (ys @ [1]))"
    using \<open>is_sol y ?sol ys\<close>
    unfolding is_sol_def by simp

  moreover have "is_sols (rev Xs) (map (subst ?sol) sols) ys"
    using sol_yXs by simp
  then have "is_sols (rev Xs) sols (y#ys)"
    using map_subst_correct[OF len_ys y] "2.prems"(2) n' by simp

  moreover have "is_sols ys (map (subst ?sol) eqns) ys"
    using IH by simp
  then have "is_sols ys eqns (y#ys)"
    using map_subst_correct[OF len_ys y] mx_eqns n' by auto

  ultimately show ?case using yys by auto
next
  case (1 sols)
  have "n = 0" using \<open>mx n (n+1) []\<close> mx_def by (metis length_0_conv)
  then have "Ys = []" using "1.prems"(3) by auto
  then have "is_sols Ys [] Ys" by simp
  moreover have "is_sols Xs (rev sols) []"
    using "1.prems" \<open>Ys = []\<close> by simp
  ultimately show ?case using \<open>Ys = []\<close> by (simp add: list_all2_rev1)
next
  case (3 a va)
  then show ?case by (simp add: mx_def)
qed

text \<open>The special case we are actually interested in\<close>
corollary solves_sound:
  "\<lbrakk> mx n (n+1) eqns; length Ys = n;
    is_sols Ys (rev (solves [] eqns)) [] \<rbrakk>
   \<Longrightarrow> is_sols Ys eqns Ys"
using solves_sound_generalization[of n eqns 0 "[]" Ys "[]"] by (simp add: mx_def)

text \<open>Finally we can show, that the output of the algorithm is a solution:\<close>

lemma solves_rec_sound:
assumes mx_eqns: "mx n (n+1) eqns"
  and Ys: "Ys = rev (map hd (solves [] eqns))"
  shows "is_sols Ys eqns Ys"
proof-
  have mx_sols: "mx 0 (n+1) []"
    using mx_def by fastforce

  have lenYs: "length Ys = n"
    using Ys length_solves mx_eqns mx_sols by fastforce

  have len1: "list_all (\<lambda>eq. length eq = 1) (solves [] eqns)"
    using mx_solves[OF mx_eqns mx_sols] by (simp add: Ball_set mx_def)
  have "map \<phi> (rev Ys) = map (\<phi> \<circ> hd) (solves [] eqns)"
    by (simp add: Ys)
  then have "is_sols (rev Ys) (solves [] eqns) []"
    using is_sols_trivial2[OF len1] by simp
  then have "is_sols Ys (rev (solves [] eqns)) []"
    by (simp add: list_all2_rev1)
  then show "is_sols Ys eqns Ys"
    using solves_sound[OF mx_eqns lenYs]
    by simp
qed

end

text \<open>We now instantiate the locales for regular expressions\<close>

text \<open>Lang wrapper to define + and *\<close>
datatype 'a langR = Lang "'a list set"
fun unLang where "unLang (Lang x) = x"
abbreviation L where "L \<equiv> \<lambda>x. Lang (lang x)"

instantiation langR :: (type) semiring_1
begin
definition times_langR :: "'a langR \<Rightarrow> 'a langR \<Rightarrow> 'a langR"
  where "A * B \<equiv> Lang (unLang A @@ unLang B)"
definition plus_langR :: "'a langR \<Rightarrow> 'a langR \<Rightarrow> 'a langR"
  where "A + B \<equiv> Lang (unLang A \<union> unLang B)"
definition zero_langR where "zero_langR \<equiv> Lang {}"
definition one_langR where "one_langR \<equiv> Lang {[]}"

instance proof(standard, goal_cases)
  case (1 a b c)
  then show ?case by (simp add: times_langR_def conc_assoc)
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
    by (simp add: times_langR_def)
next
  case (8 a)
  then show ?case unfolding zero_langR_def
    by (simp add: times_langR_def)
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


instantiation rexp :: (type) plus begin
  definition plus_rexp where "plus_rexp \<equiv> Plus" instance ..
end
instantiation rexp :: (type) zero begin
  definition zero_rexp where "zero_rexp \<equiv> Zero" instance ..
end
instantiation rexp :: (type) one begin
  definition one_rexp where "one_rexp \<equiv> One" instance ..
end
instantiation rexp :: (type) times begin
  definition times_rexp where "times_rexp \<equiv> Times" instance ..
end

lemmas rexp_defs = times_rexp_def plus_rexp_def zero_rexp_def

global_interpretation Abstraction
where \<phi> = "\<lambda>r. Lang (lang r)"
proof(standard, goal_cases)
  case (1 a b)
  then show ?case by (simp add: plus_langR_def plus_rexp_def)
next
  case (2 a b)
  then show ?case by (simp add: times_langR_def times_rexp_def)
next
  case 3
  then show ?case by (simp add: zero_langR_def zero_rexp_def)
next
  case 4
  then show ?case by (simp add: one_langR_def one_rexp_def)
qed

text\<open>We use Arden's lemma to prove \<open>solve1\<close> correct:\<close>

global_interpretation Gauss
where \<phi> = "\<lambda>r. Lang (lang r)" and solve1 = "\<lambda>r cs. map (\<lambda>c. Times (Star r) c) cs"
defines solves_r = solves and subst_r = subst
proof (standard, goal_cases)
  case 1
  then show ?case by auto
next
  case (2 X c cs Xs)
  assume "L X = L (dot (map (Times (Star c)) cs) Xs)"
  then have "L X = L (dot (map (times (Star c)) cs) Xs)"
    by (metis times_rexp_def)

  then have "L X = L (Star c) * L (dot cs Xs)"
    by (metis \<phi>_dot_mult)
  then have "lang X = star (lang c) @@ unLang (L (dot cs Xs))"
    by (simp add: times_langR_def)
  then have "lang X = lang c @@ lang X \<union> unLang (L (dot cs Xs))"
    using Arden_star_is_sol by auto
  then have "L X = L c * L X + L (dot cs Xs)"
    by (simp add: plus_langR_def times_langR_def)
  then show "L X = L (dot (c # cs) (X # Xs))"
    by (simp add: \<phi>_dot_Cons)
qed

value "solves_r [] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [[x,y,z]] [[a00,a01,b0], [a10,a11,b1]]"
value "solves_r [] [[a00,a01,b0]]"

