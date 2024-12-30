theory Regular_Eqns
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

fun times :: "'a rexp => 'a rexp => 'a rexp" where
"times Zero x = Zero" |
"times x Zero = Zero" |
"times x One = x" |
"times One x = x" |
"times a b = Times a b"
lemma lang_times: "lang (times a b) = lang (Times a b)"
  sorry

fun plus :: "'a rexp => 'a rexp => 'a rexp" where
"plus x Zero = x" |
"plus Zero x = x" |
"plus a b = Plus a b"
lemma lang_plus: "lang (plus a b) = lang (Plus a b)"
  sorry

(*TODO: subscripts in this text*)
text \<open>
We model equations of the form Xi = r1 X1 | r2 X2 | ... | rn Xn | r
to represent the rhs we only need to save r and a list containing ri
\<close>
type_synonym 'a eq_rhs = "'a rexp \<times> 'a rexp list"

text \<open>Substitute regular expressions for variables in a eq_rhs:\<close>
fun rhs_re_imp :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> (nat \<Rightarrow> 'a rexp) \<Rightarrow> 'a rexp" where
"rhs_re_imp i (r,[]) s = r" |
"rhs_re_imp i (r,(x#xs)) s = Plus (Times x (s i)) (rhs_re_imp (Suc i) (r,xs) s)"

fun rhs_re :: "'a eq_rhs \<Rightarrow> (nat \<Rightarrow> 'a rexp) \<Rightarrow> 'a rexp" where
"rhs_re (r,rs) s = rhs_re_imp 0 (r,rs) s"

(*
fun mapi :: "(nat => 'a => 'b) => 'a list => 'b list" where
"mapi f [] = []" |
"mapi f (x#xs) = f 0 x # mapi (\<lambda>i x. f (Suc i) x) xs"

fun mapi :: "(nat => 'a => 'b) => 'a list => 'b list" where
"mapi f xs = map (\<lambda>(i,x). f i x) (enumerate 0 xs)"

*)



fun mapi_imp :: "nat => (nat => 'a => 'b) => 'a list => 'b list" where
"mapi_imp i f [] = []" |
"mapi_imp i f (x#xs) = f i x # mapi_imp (Suc i) f xs"

fun mapi :: "(nat => 'a => 'b) => 'a list => 'b list" where
"mapi f xs = mapi_imp 0 f xs"

abbreviation isum where
"isum f r rs \<equiv> foldr Plus (mapi f rs) r"

lemma rhs_re_foldr: "rhs_re (r,rs) s = isum (\<lambda> i x. (Times x (s i))) r rs"
proof-
  obtain i where "i = (0::nat)" by simp
  then have "rhs_re (r,rs) s = rhs_re_imp i (r,rs) s" by simp
  also have "\<dots> = foldr Plus (mapi_imp i (\<lambda> i x. (Times x (s i))) rs) r"
    apply(induction rs arbitrary: i) by auto
  finally show ?thesis using \<open>i=0\<close> by simp
qed

value "subst_rexp [(''b'', One), (''a'', Zero)] (Plus (Atom ''a'') (Atom ''b''))"

(* "eqns" often just means "righ-hand sides" *)

(*
informally
the solution of equation i must be equivalent
to the original equation i with all other solutions substituted in for variables
for all i
*)


(*
the rhs of an eqation is represented as a list

r0 | r1 X1 | r2 X2 | r3 X3 | ... | rn Xn

where rn are regular expressions without variables

i is the variable index on the lhs

TODO: check precondition for the lemmas validity

*)
fun ardens_subst :: "nat \<Rightarrow> 'a rexp list \<Rightarrow> 'a rexp list" where
"ardens_subst i rhs = mapi (\<lambda> j e. if j = i then Zero else (Times (Star (rhs!i)) e)) rhs"



text \<open>Solve a single equation \<open>v = rhs\<close>:\<close>
fun solve1 :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"solve1 v (r,rs) = (if rexp_empty (rs!v) then (r,rs) else if nullable (rs!v) then undefined else (r,ardens_subst v rs))"



(*put v = src into dst*)
(*
fun var_subst :: "'a rexp list \<Rightarrow> nat \<Rightarrow> 'a rexp list \<Rightarrow> 'a rexp list" where
"var_subst dst v src = map2 (\<lambda> d s. (Plus d (Times (dst!v) s))) dst src"
*)
fun var_subst :: "'a eq_rhs \<Rightarrow> nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"var_subst (d,ds) v (s,src) = (Plus d (Times (ds!v) s), map2 (\<lambda> r_d r_s. (Plus r_d (Times (ds!v) r_s))) ds src)"


text \<open>Solve a simultaneous list of equations:\<close>

fun solve_imp :: "nat \<Rightarrow> 'a eq_rhs list \<Rightarrow> 'a eq_rhs list" where
"solve_imp v [] = []" |
"solve_imp v (e#es) = (let sol = solve1 v e in sol # solve_imp (Suc v) (map (\<lambda>e. var_subst e v sol) es))"

fun double_rev :: "'a eq_rhs list \<Rightarrow> 'a eq_rhs list" where
"double_rev lst = rev (map (\<lambda>(r,rs). (r,rev rs)) lst)"

(*
 needs zeros in upper right diagonal
*)
fun backsubst where
"backsubst [] s i = []" |
"backsubst (e#es) s i = rhs_re e s # backsubst es (s(i := rhs_re e s)) (Suc i)"

lemma length_backsubst[simp]: "length (backsubst lst s i) = length lst"
    apply(induction lst arbitrary: s i)
    by auto

lemma length_solve_imp[simp]: "length (solve_imp v lst) = length lst"
sorry


fun solve :: "'a eq_rhs list \<Rightarrow> 'a rexp list" where
"solve es = rev (backsubst (double_rev (solve_imp 0 es)) (\<lambda>x. Zero) 0)"


(*

backsubst eqs =

for(i = length eqs; i --> 0;)
    for(j = i+1; j < length eqs; j++)
        eqs!i := var_subst (eqs!i) j (eqs!j)
*)


(*
value "
let eqns =
[(Zero,[Zero,  One,        Zero,       Zero,       Zero,       Zero])
,(Zero,[Zero,  Zero,       Atom ''a'', Atom ''b'', Zero,       One])
,(Zero,[Zero,  Atom ''a'', Zero,       Atom ''b'', Zero,       Zero])
,(Zero,[Zero,  Zero,       Atom ''b'', Zero,       Atom ''a'', Zero])
,(Zero,[Zero,  Atom ''b'', Zero,       Atom ''a'', Zero,       Zero])
,(One, [Zero,  Zero,       Zero,       Zero      , Zero,       Zero])
]
in solve eqns
"
*)

fun eq_holds :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> (nat \<Rightarrow> 'a rexp) \<Rightarrow> bool" where
"eq_holds v (r,rs) s = (lang (rhs_re (r,rs) s) = lang (s v))"

definition solves :: "('a eq_rhs) list \<Rightarrow> 'a rexp list \<Rightarrow> bool" where
"solves eqns sols = (length sols = length eqns \<and> (\<forall>i < length sols. eq_holds i (eqns!i) (\<lambda>v. sols!v)))"

lemma lang_foldr_Plus: "lang (foldr Plus lst Zero) = foldr (\<lambda>r a. lang r \<union> a) lst {}"
apply(induction lst)
using foldr_Cons by auto

lemma isum_lang: "lang (isum s r rs) = foldr (\<union>) (mapi (\<lambda>i x. lang (s i x)) rs) (lang r)"
  sorry

print_theorems


fun all where
"all P [] = True" |
"all P (x#xs) = (P x \<and> all P xs)"

lemma TimesZero: "lang (Times a Zero) = lang Zero" by simp
lemma ZeroTimes: "lang (Times Zero a) = lang Zero" by simp
lemma PlusZero: "lang (Plus a Zero) = lang a" by simp
lemma ZeroPlus: "lang (Plus Zero a) = lang a" by simp

lemma trivial_eq_holds:
 fixes s v
 assumes "lang (s v) = lang r"
 and "all (\<lambda>x. lang x = {}) rs"
 shows "eq_holds v (r,rs) s"
proof-
  obtain i where "i = (0 :: nat)" by simp
  have "lang (rhs_re_imp i (r,rs) s) = lang (s v)"
    using assms apply (induction rs arbitrary: i) by auto
  then have "lang (rhs_re (r,rs) s) = lang (s v)"
    using \<open>i=0\<close> by auto
  then show ?thesis by auto
qed

lemma var_subst_preserve:
    fixes dst src vd va s
    assumes "length ds = length as"
    and "eq_holds vd (d,ds) s"
    and "eq_holds va (a,as) s"
    shows "eq_holds vd (var_subst (d,ds) va (a,as)) s"
proof-

  have "lang (s vd) = lang (rhs_re (d,ds) s)"
    using assms by auto
  also have "\<dots> = lang (foldr Plus (mapi (\<lambda> i x. (Times x (s i))) ds) d)"
    using rhs_re_foldr[of d ds s] by auto
  also have "\<dots> = foldr (\<union>) (mapi (\<lambda> i x. lang (Times x (s i))) ds) (lang d)"
    sorry

  have "rhs_re (var_subst (d,ds) va (a,as)) = rhs_re (Plus d (Times (ds!va) a), map2 (\<lambda> r_d r_s. (Plus r_d (Times (ds!va) r_s))) ds as)" by auto

  show ?thesis sorry
qed

lemma ardens_preserve:
    fixes vd s
    assumes "eq_holds vd (d,ds) s"
    and "\<not>nullable (ds!vd)"
    shows "eq_holds vd (d, ardens_subst vd ds) s"
    sorry

lemma solve_preserve_length[simp]: "length (solve eqns) = length eqns"
  by auto

theorem solve_correct:
assumes "\<exists>s_lst. solves eqns s_lst"
shows "solves eqns (solve eqns)"
proof-
  let ?sols = "solve eqns"
  obtain s_lst where s_lst: "solves eqns s_lst"
    using assms by auto
  let ?s = "\<lambda>v. s_lst!v"

  have "\<forall>i < length eqns. eq_holds i (eqns!i) ?s"
    using solves_def[of eqns] s_lst by auto

  have "\<forall>i < length ?sols. eq_holds i (eqns!i) (\<lambda>v. ?sols!v)" sorry
  then show ?thesis using solve_preserve_length solves_def by blast
qed


end
