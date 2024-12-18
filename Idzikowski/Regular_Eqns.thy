theory Regular_Eqns
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

text \<open>Substitute regular expressions for variables in a regular expression:\<close>
fun subst_rexp :: "('a * 'a rexp) list \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
"subst_rexp _ Zero = Zero" |
"subst_rexp _ One = One" |
"subst_rexp ars (Atom a) = (case map_of ars a of None \<Rightarrow> Atom a | Some r \<Rightarrow> r)" |
"subst_rexp ars (Plus r s) = Plus (subst_rexp ars r)(subst_rexp ars s)" |
"subst_rexp ars (Times r s) = Times (subst_rexp ars r)(subst_rexp ars s)" |
"subst_rexp ars (Star r) = Star (subst_rexp ars r)"

(* "eqns" often just means "righ-hand sides" *)

text \<open>The equations \<open>zip vars eqns\<close> are solved by the association list \<open>zip vars sols\<close>:\<close>
definition solves :: "'a list \<Rightarrow> 'a rexp list \<Rightarrow> 'a rexp list \<Rightarrow> bool" where
"solves vars eqns sols = (length sols = length vars \<and> length eqns = length vars \<and>
  (\<forall>i < length vars. lang (sols!i) = lang (subst_rexp (zip vars sols) (eqns!i))))"

text \<open>Solve a single equation \<open>v = rhs\<close>:\<close>
definition solve1 :: "'a \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
"solve1 v rhs = undefined"

text \<open>Solve a simultaneous list of equations:\<close>
fun solve :: "'a list \<Rightarrow> 'a rexp list \<Rightarrow> 'a rexp list" where
"solve [] [] = []"

theorem solve_correct:
assumes "length vars = length eqns"
shows "solves vars eqns (solve vars eqns)"
sorry

end