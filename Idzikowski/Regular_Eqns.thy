theory Regular_Eqns
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

(*TODO: subscripts in this text*)
text \<open>
We model equations of the form Xi = r1 X1 | r2 X2 | ... | rn Xn | r
to represent the rhs we only need to save r and a list containing ri
\<close>
type_synonym 'a eq_rhs = "'a rexp \<times> ('a rexp \<times> nat) list"

abbreviation rsum where "rsum \<equiv> foldr Plus"
abbreviation lsum where "lsum \<equiv> foldr (\<union>)"

fun var_prefix :: "nat ⇒ 'a eq_rhs ⇒ 'a rexp" where
"var_prefix v (r,rs) = rsum (map fst (filter (λ(_,i). i=v) rs)) Zero"

fun mre :: "('a \<Rightarrow> 'b rexp) \<Rightarrow> 'b rexp \<times> 'a \<Rightarrow> 'b rexp" where
"mre s (x,i) = Times x (s i)"

text \<open>Substitute regular expressions for variables in a eq_rhs:\<close>
fun rhs_re :: "'a eq_rhs \<Rightarrow> (nat \<Rightarrow> 'a rexp) \<Rightarrow> 'a rexp" where
"rhs_re (r,rs) s = rsum (map (mre s) rs) r"


abbreviation eq_lang where
"eq_lang eq s \<equiv> lang (rhs_re eq s)"

lemma lang_Union_eq_lang: "lang a \<union> eq_lang (b, bs) s = eq_lang (Plus a b, bs) s"
apply(induction bs)
by auto

lemma eq_lang_Cons: "eq_lang (r,(x,i)#xs) s = lang x @@ lang (s i) \<union> eq_lang (r,xs) s"
by auto

lemma lang_Union_eq_lang_Zero: "lang a \<union> eq_lang (Zero, bs) s = eq_lang (a, bs) s"
apply(induction bs)
by auto

lemma eq_lang_conc[simp]: "eq_lang (a,as@bs) s = eq_lang (a, as) s \<union> eq_lang (Zero, bs) s"
proof(induction as)
  case Nil
  then show ?case using lang_Union_eq_lang_Zero by auto
qed auto

lemma lsum_conc: "lsum rs r @@ b = lsum (map (λa. a @@ b) rs) (r @@ b)"
proof(induction rs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  have "lsum (x # xs) r @@ b = x @@ b \<union> lsum xs r @@ b" by auto
  also have "\<dots> = x @@ b \<union> lsum (map (\<lambda>a. a @@ b) xs) (r @@ b)"
    using Cons.IH by auto
  also have "\<dots> = lsum (map (\<lambda>a. a @@ b) (x#xs)) (r @@ b)"
    by auto
  finally show ?case by simp
qed

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


lemma lang_rsum[simp]: "lang (rsum rs r) = (lsum (map lang rs) (lang r))"
apply(induction rs)
by auto

lemma Arden_star_is_sol:
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

fun eq_times :: "'a rexp ⇒ 'a eq_rhs ⇒ 'a eq_rhs" where
"eq_times a (b,bs) = (Times a b, map (λ(r,i). (Times a r, i)) bs)"

lemma lang_eq_times[simp]: "eq_lang (eq_times a (b,bs)) s = lang a @@ eq_lang (b,bs) s"
proof(induction bs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  have "\<exists>r i. x = (r,i)" by auto
  then obtain r i where ri: "(r,i) = x" by blast

  let ?ys = "map (λ(r,i). (Times a r, i)) xs"

  have "eq_lang (eq_times a (b, x # xs)) s = eq_lang (eq_times a (b, (r,i) # xs)) s"
    using ri by auto
  also have "\<dots> = eq_lang (Times a b, map (λ(r,i). (Times a r, i)) ((r,i)#xs)) s"
    by auto
  also have "\<dots> = eq_lang (Times a b, (Times a r, i) # ?ys) s"
    by auto
  also have "\<dots> = lang (Times a r) @@ lang (s i) \<union> eq_lang (Times a b, ?ys) s"
    using eq_lang_Cons by auto
  also have "\<dots> = lang (Times a r) @@ lang (s i) \<union> eq_lang (eq_times a (b,xs)) s"
    by auto
  also have "\<dots> = lang (Times a r) @@ lang (s i) \<union> lang a @@ eq_lang (b, xs) s"
    using Cons.IH by auto
  also have "\<dots> = lang a @@ lang r @@ lang (s i) \<union> lang a @@ eq_lang (b, xs) s"
    using conc_assoc by auto
  also have "\<dots> = lang a @@ (lang r @@ lang (s i) \<union> eq_lang (b, xs) s)"
    using conc_Un_distrib by auto
  also have "\<dots> = lang a @@ eq_lang (b, (r,i) # xs) s"
    using eq_lang_Cons by auto
  finally show "eq_lang (eq_times a (b, x # xs)) s = lang a @@ eq_lang (b, x # xs) s"
    using ri by auto
qed


(*
lemma lang_eq_times2[simp]: "eq_lang (eq_times a bs) s = lang a @@ eq_lang bs s"
using lang_eq_times by (metis eq_times.elims)
*)


fun eq_plus :: "'a eq_rhs ⇒ 'a eq_rhs ⇒ 'a eq_rhs" where
"eq_plus (a,as) (b,bs) = (Plus a b, as @ bs)"

lemma lang_eq_plus[simp]: "eq_lang (eq_plus (a,as) (b,bs)) s = eq_lang (a,as) s \<union> eq_lang (b,bs) s"
proof(induction as)
  case Nil
  thus ?case
  apply(induction bs) by auto
qed auto


fun ardens_subst :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"ardens_subst v (r,rs) = (
    let (as,bs) = partition (λ(r,j). j=v) rs
    in eq_times (Star (rsum (map fst as) Zero)) (r,bs)
)"



text \<open>Solve a single equation \<open>v = rhs\<close>:\<close>
fun solve1 :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"solve1 v (r,rs) = (if rexp_empty (fst (rs!v)) then (r,rs) else ardens_subst v (r,rs))"



(* substitute (f,fs) for v in (t,ts) *)
fun var_subst :: "'a eq_rhs ⇒ nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"var_subst (t,ts) v (f,fs) = (
    let (as,bs) = partition (λ(r,i). i=v) ts
    in eq_plus (t,bs) (eq_times (rsum (map fst as) Zero) (f,fs))
)"


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

fun solve :: "'a eq_rhs list \<Rightarrow> 'a rexp list" where
"solve es = rev (backsubst (double_rev (solve_imp 0 es)) (\<lambda>x. Zero) 0)"

lemma length_backsubst[simp]: "length (backsubst lst s i) = length lst"
    apply(induction lst arbitrary: s i)
    by auto

lemma length_solve_imp[simp]: "length (solve_imp v lst) = length lst"
proof-
    obtain n where "n = length lst" by auto
    then show ?thesis proof(induction n arbitrary: lst v)
      case 0
      then show ?case by auto
    next
      case (Suc n)
      then obtain x xs where "x#xs = lst"
        by (metis length_Suc_conv)
      let ?sol = "solve1 v x"
      obtain xs' where xs': "xs' = (map (\<lambda>e. var_subst e v ?sol) xs)" by auto
      then have "n = length xs'" using Suc.prems ‹x#xs = lst› by auto

      have "length (solve_imp v lst) = length (solve_imp v (x#xs))" using ‹x#xs=lst› by auto
      also have "\<dots> = length (let sol = solve1 v x in sol # solve_imp (Suc v) (map (\<lambda>e. var_subst e v sol) xs))" by auto
      also have "\<dots> = length (?sol # solve_imp (Suc v) xs')" using xs' by metis
      also have "\<dots> = Suc (length xs')" using length_Cons Suc.IH[OF ‹n=length xs'›] by simp
      finally show ?case using ‹x#xs=lst› Suc.prems \<open>n = length xs'\<close> by argo
    qed
qed




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
"eq_holds v (r,rs) s = ((eq_lang (r,rs) s) = lang (s v))"


definition solves :: "('a eq_rhs) list \<Rightarrow> 'a rexp list \<Rightarrow> bool" where
"solves eqns sols = (length sols = length eqns \<and> (\<forall>i < length sols. eq_holds i (eqns!i) (\<lambda>v. sols!v)))"

lemma partition_rsum:
    assumes "(as,bs) = partition p rs"
    shows "lang (rsum (map f (as@bs)) r) = lang (rsum (map f rs) r)"
using assms proof(induction rs arbitrary: as bs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case
  proof(cases "p x")
    case True
    then obtain ass where "x#ass = as"
        using Cons.prems by auto
    then have ass: "(ass, bs) = partition p xs"
        using Cons.prems True by auto

    have "lang (rsum (map f (x # xs)) r) = lang (rsum (map f xs) r) \<union> lang (f x)" by auto
    also have "\<dots> = lang (rsum (map f (ass @ bs)) r) \<union> lang (f x)"
        using ass Cons.IH by blast
    also have "\<dots> = lang (rsum (map f (x#(ass @ bs))) r)"
        by auto
    finally show ?thesis using ‹x#ass = as› by force
  next
    case False
    then obtain bss where "x#bss = bs"
        using Cons.prems by auto
    then have bss: "(as, bss) = partition p xs"
        using Cons.prems False by auto

    have "lang (rsum (map f (x # xs)) r) = lang (rsum (map f xs) r) \<union> lang (f x)" by auto
    also have "\<dots> = lang (rsum (map f (as @ bss)) r) \<union> lang (f x)"
        using bss Cons.IH by blast
    also have "\<dots> = lang (rsum (map f (as @ x#bss)) r)"
        apply(induction as) by auto
    finally show ?thesis using ‹x#bss = bs› by force
  qed
qed

lemma TimesZero: "lang (Times a Zero) = lang Zero" by simp
lemma ZeroTimes: "lang (Times Zero a) = lang Zero" by simp
lemma PlusZero: "lang (Plus a Zero) = lang a" by simp
lemma ZeroPlus: "lang (Plus Zero a) = lang a" by simp

lemma list_all_filter: "list_all p (filter p lst)"
apply(induction lst)
by auto

(*can't think of a good name*)
lemma list_var_dist:
    assumes "list_all (λ(x,i). i=v) rs"
    shows "lsum (map lang (map (mre s) rs)) {} = lsum (map lang (map fst rs)) {} @@ lang (s v)"
using assms proof(induction rs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)

  have "\<exists>r i. x = (r,i)" by auto
  then obtain r i where ri: "(r,i) = x" by blast

  have "lsum (map lang (map (mre s) (x # xs))) {} = lsum (lang (mre s x) # (map lang (map (mre s) xs))) {}" by auto
  also have "\<dots> = lang (mre s (r,i)) \<union> lsum (map lang (map (mre s) xs)) {}" using ri by auto
  also have "\<dots> = lang r @@ lang(s i) \<union> lsum (map lang (map (mre s) xs)) {}" by auto
  also have "\<dots> = lang r @@ lang(s i) \<union> lsum (map lang (map fst xs)) {} @@ lang (s v)"
    using Cons by auto
  also have "\<dots> = lang r @@ lang(s v) \<union> lsum (map lang (map fst xs)) {} @@ lang (s v)"
    using Cons.prems ri by auto
  also have "\<dots> = (lang r \<union> lsum (map lang (map fst xs)) {}) @@ lang (s v)"
    using conc_Un_distrib by auto
  also have "\<dots> = (lang (fst x) \<union> lsum (map lang (map fst xs)) {}) @@ lang (s v)"
    using ri by auto
  finally have "lsum (map lang (map (mre s) (x # xs))) {} = lsum (map lang (map fst (x # xs))) {} @@ lang (s v)" by auto
  then show ?case by simp
qed

lemma partition_eq_lang:
    assumes "(as,bs) = partition p rs"
    shows "eq_lang (r,rs) s = eq_lang (Zero,as) s \<union> eq_lang (r,bs) s"
proof-
    have "eq_lang (r,rs) s = lang (rsum (map (mre s) rs) r)" by auto
    also have "\<dots> = lang (rsum ((map (mre s) as) @ (map (mre s) bs)) r)"
        using partition_rsum[OF assms] by auto
    also have "\<dots> = lsum (map (lang o (mre s)) as @ map (lang o (mre s)) bs) (lang r)"
        by auto
    also have "\<dots> = lsum (map (lang o (mre s)) as) {} \<union> lsum (map (lang o (mre s)) bs) (lang r)"
        apply(induction as) by auto
    also have "\<dots> = eq_lang (Zero,as) s \<union> eq_lang (r,bs) s"
        by auto
    finally show "eq_lang (r,rs) s = eq_lang (Zero,as) s \<union> eq_lang (r,bs) s"
        by auto
qed

lemma ardens_subst_correct:
    assumes "eq_holds v (ardens_subst v (r,rs)) s"
    shows "eq_holds v (r,rs) s"
proof-
    obtain as bs where ab: "(as,bs) = partition (λ(r,j). j=v) rs" by auto
    have "as = filter (λ(r,j). j=v) rs" using ab by auto
    then have as_all: "list_all (λ(r,j). j=v) as" using list_all_filter by auto

    have "ardens_subst v (r,rs) = eq_times (Star (rsum (map fst as) Zero)) (r,bs)"
        using ab by auto
    then have "eq_holds v (eq_times (Star (rsum (map fst as) Zero)) (r,bs)) s"
        using assms by argo
    then have "lang (s v) = eq_lang (eq_times (Star (rsum (map fst as) Zero)) (r,bs)) s"
        by auto
    also have "\<dots> = lang (Star (rsum (map fst as) Zero)) @@ eq_lang (r,bs) s"
        using lang_eq_times by blast
    also have "\<dots> = (star (lsum (map lang(map fst as)) {})) @@ eq_lang (r,bs) s"
        by auto
    finally have "lang (s v) = (star (lsum (map lang (map fst as)) {})) @@ eq_lang (r,bs) s"
        by auto
    then have "lang (s v) = (lsum (map lang (map fst as)) {}) @@ (lang (s v)) \<union> eq_lang (r,bs) s"
        using Arden_star_is_sol by auto
    then have "lang (s v) = lsum (map lang (map (mre s) as)) {} \<union> eq_lang (r,bs) s"
        using list_var_dist[OF as_all] by auto
    then have "lang (s v) = eq_lang (Zero,as) s \<union> eq_lang (r,bs) s"
        by auto
    then have "eq_lang (r,rs) s = lang (s v)"
        using partition_eq_lang[OF ab] by auto
    then show ?thesis by simp
qed

lemma ardens_subst_Zeros: "lang (var_prefix v (ardens_subst v (r,rs))) = {}"
proof-
    obtain as bs where ab: "(as,bs) = partition (λ(r,j). j=v) rs" by auto
    have "bs = filter (Not o (λ(r,j). j=v)) rs" using ab by auto
    then have bs_all: "list_all (Not o (λ(r,j). j=v)) bs" using list_all_filter by auto

    let ?a = "Star (rsum (map fst as) Zero)"
    have "lang (var_prefix v (ardens_subst v (r,rs))) = lang (var_prefix v (eq_times ?a (r,bs)))"
        using ab by auto
    also have "\<dots> = lang (var_prefix v (Times ?a r, map (λ(r,i). (Times ?a r, i)) bs))"
        by auto
    also have "\<dots> = lang (rsum (map fst (filter (λ(_,i). i=v) (map (λ(r,i). (Times ?a r, i)) bs))) Zero)"
        by auto
    also have "\<dots> = lang (rsum (map fst []) Zero)"
        using bs_all apply(induction bs) by auto
    finally show ?thesis by auto
qed

lemma var_subst_correct:
    assumes "eq_holds vt (var_subst (t,ts) vf (f,fs)) s"
    and "eq_holds vf (f,fs) s"
    shows "eq_holds vt (t,ts) s"
proof-
    obtain as bs where ab: "(as,bs) = partition (λ(r,j). j=vf) ts" by auto
    have "as = filter (λ(r,j). j=vf) ts" using ab by auto
    then have as_all: "list_all (λ(r,j). j=vf) as" using list_all_filter by auto

    have "eq_lang (var_subst (t,ts) vf (f,fs)) s = eq_lang (eq_plus (t,bs) (eq_times (rsum (map fst as) Zero) (f,fs))) s"
        using ab by auto
    also have "\<dots> = eq_lang (t,bs) s \<union> eq_lang (eq_times (rsum (map fst as) Zero) (f,fs)) s"
        using lang_eq_plus[of t bs] by (rule rhs_re.induct)
    also have "\<dots> = eq_lang (t,bs) s \<union> lang (rsum (map fst as) Zero) @@ eq_lang (f,fs) s"
        using lang_eq_times[of _ f fs s] by blast
    also have "\<dots> = eq_lang (t,bs) s \<union> lang (rsum (map fst as) Zero) @@ lang (s vf)"
        using assms by auto
    also have "\<dots> = eq_lang (t,bs) s \<union> (lsum (map lang (map fst as)) {}) @@ lang (s vf)"
        by auto
    also have "\<dots> = eq_lang (t,bs) s \<union> (eq_lang (Zero,as) s)"
        using list_var_dist[OF as_all] by auto
    also have "\<dots> = eq_lang (t,ts) s"
        using partition_eq_lang[OF ab] by auto
    finally have "eq_lang (t,ts) s = lang (s vt)" using assms by auto
    thus ?thesis by auto
qed

lemma solve_preserve_length[simp]: "length (solve eqns) = length eqns"
  by auto

lemma solve1_preserve:
    assumes "eq_holds v (r,rs) s"
    shows "eq_holds v (solve1 v (r,rs)) s"
proof(cases "rexp_empty (fst(rs!v))")
  case True
  then show ?thesis using assms by auto
next
  case False
  then show ?thesis using assms ardens_preserve[OF ‹eq_holds v (r,rs) s›] by auto
qed


lemma solve_imp_preserve:
    assumes "\<forall>i < length eqns. eq_holds (v+i) (eqns!i) s"
    shows "\<forall>i < length eqns. eq_holds (v+i) ((solve_imp v eqns)!i) s"
proof-
    obtain n where "n = length eqns" by auto
    then show ?thesis
    using assms proof(induction n arbitrary: eqns v)
      case 0 thus ?case by auto
    next
      case (Suc n)
      then obtain e es where "e#es = eqns"
        by (metis length_Suc_conv)

      let ?sol = "solve1 v e"
      obtain es' where es': "es' = (map (\<lambda>e. var_subst e v ?sol) es)" by auto

      have "n = length es'" using es' ‹e#es = eqns› Suc by fastforce

      have "\<forall>i<length es'. eq_holds ((Suc v) + i) (solve_imp (Suc v) es' ! i) s"
        using Suc.IH[OF ‹n = length es'›, of "Suc v"] subst_preserve_lift[of eqns s v ?sol] Suc.prems(2) sorry


      then have "\<forall>i < length (e#es). eq_holds (v + i) ((?sol # solve_imp (Suc v) es')!i) s"
        sorry
      then have "\<forall>i < length (e#es). eq_holds (v + i) (solve_imp v (e#es) ! i) s"
        using es' by (metis solve_imp.simps(2))
      then show ?case using ‹e#es = eqns› by auto
    qed
qed

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
  then have "\<forall>i < length eqns. eq_holds i ((solve_imp 0 eqns)!i) ?s"
    using solve_imp_preserve by auto

  have "\<forall>i < length eqns. eq_holds i (eqns!i) (\<lambda>v. (solve eqns)!v)" sorry
  then show ?thesis using solve_preserve_length solves_def by metis
qed


end
