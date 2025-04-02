theory Gauss_Jordan
imports "Regular-Sets.Regular_Exp"

begin

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

definition dot :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a" where
"dot as bs = foldl add zero (map2 mult as bs)"

definition is_sol :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sol a cs sol = eq a (dot cs sol)"

fun is_sols :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> bool" where
"is_sols sol (c#cs) (eqn # eqns) = (is_sol c eqn sol \<and> is_sols sol cs eqns)" |
"is_sols sol _ [] = True"

definition mult1 where
"mult1 = map o mult"

fun subst :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"subst sol (c#cs) = map2 add (mult1 c sol) cs"

fun solves :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
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
