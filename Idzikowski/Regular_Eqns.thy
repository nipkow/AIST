theory Regular_Eqns
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

text \<open>
We model equations of the form Xi = r1 X1 | r2 X2 | ... | rn Xn | r
variables are represented by natural numbers

a system of equations is modeled as a list of right hand sides
the variable on the left hand side is the index
\<close>
type_synonym 'a eq_rhs = "'a rexp \<times> ('a rexp \<times> nat) list"

abbreviation rsum where "rsum \<equiv> foldr Plus"
abbreviation lsum where "lsum \<equiv> foldr (\<union>)"

lemma lang_rsum: "lang (rsum rs r) = \<Union>{lang x | x. x \<in> set rs} \<union> lang r"
apply(induction rs)
by auto


text \<open>return α where (r,rs) = α v | β\<close>
fun var_prefix :: "nat ⇒ 'a eq_rhs ⇒ 'a rexp" where
"var_prefix v (_,rs) = rsum (map fst (filter (λ(_,i). i=v) rs)) Zero"

lemma lang_var_prefix:
    "lang (var_prefix v (r,rs)) = \<Union> {lang x | x. (x,v) \<in> set rs}"
apply(induction rs)
by auto

text \<open>Regular expression represented by single monomial given variable mapping s\<close>
fun mre :: "('a \<Rightarrow> 'b rexp) \<Rightarrow> 'b rexp \<times> 'a \<Rightarrow> 'b rexp" where
"mre s (x,i) = Times x (s i)"

lemma lang_mre: "lang (mre s (x,i)) = lang x @@ lang (s i)" by auto

text \<open>Regular expression represented by eq_rhs given variable mapping s\<close>
fun rhs_re :: "'a eq_rhs \<Rightarrow> (nat \<Rightarrow> 'a rexp) \<Rightarrow> 'a rexp" where
"rhs_re (r,rs) s = rsum (map (mre s) rs) r"


text ‹list to function helper›
fun l2f where "l2f l = (λi. l!i)"


text ‹lift lang to rhs_re, needs a variable mapping s›
abbreviation eq_lang where
"eq_lang eq s \<equiv> lang (rhs_re eq s)"

lemma eq_lang: "eq_lang (r,rs) s = \<Union> {lang x @@ lang (s v) | x v. (x,v) \<in> set rs} \<union> lang r"
proof-
    have "eq_lang (r,rs) s = \<Union> {lang x |x. x \<in> set (map (mre s) rs)} \<union> lang r"
        using lang_rsum[of "(map (mre s) rs)" r] unfolding rhs_re.simps by blast
    also have "\<dots> = \<Union> {lang (mre s x) |x. x \<in> set rs} \<union> lang r"
        by fastforce
    finally show ?thesis by simp
qed

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

lemma lang_rsum2[simp]: "lang (rsum rs r) = (lsum (map lang rs) (lang r))"
apply(induction rs)
by auto


text ‹lift Times to eq_rhs on one side›
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

text ‹lift Plus to eq_rhs›
fun eq_plus :: "'a eq_rhs ⇒ 'a eq_rhs ⇒ 'a eq_rhs" where
"eq_plus (a,as) (b,bs) = (Plus a b, as @ bs)"

lemma lang_eq_plus[simp]: "eq_lang (eq_plus (a,as) (b,bs)) s = eq_lang (a,as) s \<union> eq_lang (b,bs) s"
proof(induction as)
  case Nil
  thus ?case
  apply(induction bs) by auto
qed auto

text ‹Ardens Lemma›

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

text ‹Perform the substitution v = α v | β   ⇒   v = α*v β ›

fun ardens_subst :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"ardens_subst v (r,rs) = (
    let (as,bs) = partition (λ(r,j). j=v) rs
    in eq_times (Star (rsum (map fst as) Zero)) (r,bs)
)"



text \<open>Solve a single equation \<open>v = rhs\<close>:\<close>
fun solve1 :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"solve1 v (r,rs) = (if rexp_empty (var_prefix v (r,rs)) then (r,rs) else ardens_subst v (r,rs))"



text ‹
substitute (f,fs) for variable v in (t,ts)
letters mnemonic for "from" and "to"
›
fun var_subst :: "'a eq_rhs ⇒ nat \<Rightarrow> 'a eq_rhs \<Rightarrow> 'a eq_rhs" where
"var_subst (t,ts) v (f,fs) = (
    let (as,bs) = partition (λ(r,i). i=v) ts
    in eq_plus (t,bs) (eq_times (rsum (map fst as) Zero) (f,fs))
)"

text ‹Substitute sol for v in all eqns after v›
fun var_subst_after where
"var_subst_after v sol eqns = (take (Suc v) eqns) @ map (\<lambda>e. var_subst e v sol) (drop (Suc v) eqns)"

text \<open>Solve a simultaneous list of equations using an algorithm very simmilar to Gaussian elimination\<close>

text ‹
Single forward elimination step

the if condition is always true but it makes a proof easier
›
fun fwd_elim_step :: "nat ⇒ 'a eq_rhs list ⇒ 'a eq_rhs list" where
"fwd_elim_step v eqns = (if v < length eqns then
(let sol = solve1 v (eqns!v)
   ; eqns2 = eqns[v := sol]
   in var_subst_after v sol eqns2
) else eqns)"


corollary fwd_elim_step_nolet:
"fwd_elim_step v eqns = var_subst_after v (solve1 v (eqns!v)) (eqns[v := solve1 v (eqns!v)])"
apply auto by metis

text ‹we assume equation v is already solved, meaning it does not depend on any variables›

fun back_subst_step :: "nat ⇒ 'a eq_rhs list ⇒ 'a eq_rhs list" where
"back_subst_step v eqns = (if v < length eqns then
(let val = (fst (eqns!v), [])
    in map (\<lambda>e. var_subst e v val) eqns
) else eqns)"

text ‹reverse for loop›
fun forloop_down :: "nat ⇒ (nat ⇒ 'a ⇒ 'a) ⇒ 'a ⇒ 'a" where
"forloop_down 0 f x = x" |
"forloop_down (Suc i) f x = forloop_down i f (f i x)"

text ‹
forward for loop
for(nat i = 0; i < n; i++){
    x = f i x;
}
return x;
›
(*
fun forloop where
"forloop n f x = forloop_down n (λi x. f (n - Suc i) x) x"
*)
fun forloop where
"forloop 0 f x = x" |
"forloop (Suc n) f x = f n (forloop n f x)"

value "forloop 10 (λi x. x@[i]) []"

fun fwd_elim where
"fwd_elim eqns = forloop (length eqns) fwd_elim_step  eqns"

lemma forloop_down_preserve_back:
    assumes "\<And>x i. (i < i0 \<Longrightarrow> P (f i x) \<Longrightarrow> P x)"
    and "P (forloop_down i0 f x)"
    shows "P x"
using assms proof(induction i0 arbitrary: x)
  case (Suc i)
  then have "P (forloop_down (Suc i) f x)" by blast
  then have "P (forloop_down i f (f i x))" by auto
  then show ?case using Suc less_Suc_eq by blast
qed auto

lemma forloop_preserve_back:
    assumes "\<forall>x i. (P (f i x) \<longrightarrow> P x)"
    and "P (forloop i0 f x)"
    shows "P x"
using assms proof(induction i0 arbitrary: x)
  case (Suc i)
  then have "P (forloop (Suc i) f x)" by blast
  then have "P (f i (forloop i f x))" by auto
  then show ?case using Suc less_Suc_eq by blast
qed auto

lemma forloop_down_preserve_fwd:
    assumes "\<forall>x i. (P x \<longrightarrow> P (f i x))"
    and "P x"
    shows "P (forloop_down i f x)"
using assms apply(induction i arbitrary: x) by auto

lemma forloop_preserve_fwd:
    assumes "\<forall>x i. (P x \<longrightarrow> P (f i x))"
    and "P x"
    shows "P (forloop i f x)"
using assms apply(induction i arbitrary: x) by auto

lemma forall_i_Cons:
    assumes "p 0 x"
    and "\<forall>i < length xs. p (Suc i) (xs!i)"
    shows "\<forall>i < length (x#xs). p i ((x#xs)!i)"
using assms less_Suc_eq_0_disj by force

lemma forloop_down_accumulate:
    assumes conserve: "\<forall>x i j. (P i x --> P i (f j x))"
    and create: "\<And>i x. P i (f i x)"
    shows "\<forall> i < i0. P i (forloop_down i0 f x)"
proof(induction i0 arbitrary: x)
  case (Suc i0)
  have "forloop_down (Suc i0) f x = forloop_down i0 f (f i0 x)" by auto
  moreover have "P i0 (f i0 x)" using create by auto
  then have "P i0 (forloop_down i0 f (f i0 x))"
    using forloop_down_preserve_fwd conserve by metis
  moreover have "\<forall>i<i0. P i (forloop_down i0 f (f i0 x))"
    using Suc by auto
  ultimately show ?case using less_Suc_eq by presburger
qed auto

lemma forloop_accumulate:
    assumes conserve: "\<And>x i j. (j > i --> P i x --> P i (f j x))"
    and create: "\<And>i x. P i (f i x)"
    shows "\<forall>i < i0. P i (forloop i0 f x)"
proof(induction i0 arbitrary: x)
  case (Suc i0)
  have "forloop (Suc i0) f x = f i0 (forloop i0 f x)" by auto
  moreover have "P i0 (f i0 (forloop i0 f x))" using create by auto
  moreover have "\<forall>i<i0. P i (f i0 (forloop i0 f x))"
    using conserve Suc by auto
  ultimately show ?case using less_Suc_eq by presburger
qed auto


fun backsubst where
"backsubst eqns = forloop_down (length eqns) back_subst_step eqns"

text ‹
First do forward elimination
then do backward substitution
finally extract values, assuming all equations are of the solved form Xi = r
›
fun solve :: "'a eq_rhs list \<Rightarrow> 'a rexp list" where
"solve eqns = (map fst (backsubst (fwd_elim eqns)))"

text ‹Does equation v = (r,rs) hold for the variable assignment s›
fun eq_holds :: "nat \<Rightarrow> 'a eq_rhs \<Rightarrow> (nat \<Rightarrow> 'a rexp) \<Rightarrow> bool" where
"eq_holds v (r,rs) s = ((eq_lang (r,rs) s) = lang (s v))"

fun eq_holds_tup where
"eq_holds_tup (v,es) s = eq_holds v es s"

definition solves :: "'a rexp list ⇒ ('a eq_rhs) list \<Rightarrow> bool" where
"solves sols eqns = (length sols = length eqns \<and> (\<forall>i < length sols. eq_holds i (eqns!i) (\<lambda>v. sols!v)))"
definition solves_fn :: "(nat ⇒ 'a rexp) ⇒ ('a eq_rhs) list \<Rightarrow> bool" where
"solves_fn s eqns = (\<forall>i < length eqns. eq_holds i (eqns!i) s)"

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
    and "lang (var_prefix v (ardens_subst v (r,rs))) = {}"
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
    then show "eq_holds v (r,rs) s" by simp
next
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
    finally show "lang (var_prefix v (ardens_subst v (r,rs))) = {}" by auto
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

corollary var_subst_correct2:
    assumes "eq_holds vt (var_subst ts vf fs) s"
    and "eq_holds vf fs s"
    shows "eq_holds vt ts s"
using assms var_subst_correct apply(cases ts) apply(cases fs) by blast



lemma solve1_preserve:
    assumes "eq_holds v (solve1 v (r,rs)) s"
    shows "eq_holds v (r,rs) s"
proof(cases "rexp_empty (var_prefix v (r,rs))")
  case True
  then show ?thesis using assms by auto
next
  case False
  then have "solve1 v (r,rs) = ardens_subst v (r,rs)" by auto
  then show ?thesis using assms ardens_subst_correct by metis
qed

corollary solve1_preserve2:
    assumes "eq_holds v (solve1 v es) s"
    shows "eq_holds v es s"
using assms solve1_preserve apply(cases es) by blast


lemma map_lift:
    assumes "\<forall>x i. (P i x \<longrightarrow> Q i (f x))"
    and "\<forall>i < length lst. P i (lst!i)"
    shows "\<forall>i < length lst. Q i ((map f lst)!i)"
proof
    fix i
    show "i < length lst \<longrightarrow> Q i (map f lst ! i)" proof
    assume "i < length lst"
    show "Q i (map f lst ! i)" using assms by (simp add: \<open>i < length lst›)
    qed
qed

lemma map_lift2:
    assumes "\<forall>x i. (Q i (f x) \<longrightarrow> P i x)"
    and "\<forall>i < length lst. Q i ((map f lst)!i)"
    shows "\<forall>i < length lst. P i (lst!i)"
proof
    fix i
    show "i < length lst \<longrightarrow> P i (lst!i)" proof
    assume "i < length lst"
    show "P i (lst ! i)" using assms by (simp add: \<open>i < length lst›)
    qed
qed

lemma var_subst_map_correct:
    assumes "solves_fn s (map (\<lambda>e. var_subst e v sol) eqns)"
    and "eq_holds v sol s"
    shows "solves_fn s eqns"
using assms map_lift2[of "(λv e. eq_holds v e s)" "(\<lambda>e. var_subst e v sol)" "(λv e. eq_holds v e s)" eqns]
using var_subst_correct2 length_map unfolding solves_fn_def by metis

lemma length_var_subst_after[simp]: "length (var_subst_after v sol eqns) = length eqns" by simp
lemma length_fwd_elim_step[simp]: "length (fwd_elim_step v eqns) = length eqns" unfolding fwd_elim_step_nolet by simp

lemma nth_var_subst_after:
    assumes "n < length eqns"
    shows "(var_subst_after v sol eqns)!n = (if n \<le> v then eqns!n else (var_subst (eqns!n) v sol))"
proof-
    let ?xs = "(take (Suc v) eqns)"
    let ?ys = "map (\<lambda>e. var_subst e v sol) (drop (Suc v) eqns)"
    let ?full = "(?xs @ ?ys)"
    have "(var_subst_after v sol eqns)!n = ?full!n" by auto
    also have "\<dots> = (if n < length ?xs then ?xs!n else ?ys!(n - length ?xs))"
        using nth_append by blast
    also have "\<dots> = (if n \<le> v then ?xs!n else ?ys!(n - Suc v))"
        using assms by simp
    also have "\<dots> = (if n \<le> v then ?xs!n else (drop (Suc v) (map (\<lambda>e. var_subst e v sol) eqns))!(n - Suc v))"
        using drop_map by metis
    also have "\<dots> = (if n \<le> v then ?xs!n else (map (\<lambda>e. var_subst e v sol) eqns)!n)"
        using assms by simp
    also have "\<dots> = (if n \<le> v then ?xs!n else var_subst (eqns!n) v sol)"
        using nth_map[of n eqns "\<lambda>e. var_subst e v sol"] assms by auto
    finally show ?thesis by auto
qed

corollary var_subst_after_v:
    assumes "v < length eqns"
    shows "(var_subst_after v sol eqns)!v = eqns!v"
using nth_var_subst_after by (metis assms dual_order.refl)

lemma var_prefix_eq_plus: "lang (var_prefix v (eq_plus (a,as) (b,bs))) = lang (var_prefix v (a,as)) \<union> lang (var_prefix v (b,bs))"
apply(induction as) by auto

lemma var_prefix_eq_times: "lang (var_prefix v (eq_times a (b,bs))) = lang a @@ lang (var_prefix v (b,bs))"
proof(induction bs)
  case (Cons x xs)
  have "lang (var_prefix v (eq_times a (b, x # xs))) = lang (var_prefix v (Times a b, map (λ(r,i). (Times a r, i)) (x#xs)))"
    by auto
  also have "\<dots> = \<Union> {lang xa |xa. (xa, v) \<in> set (map (λ(r,i). (Times a r, i)) (x#xs))}"
    using lang_var_prefix unfolding eq_times.simps by metis
  also have "\<dots> = \<Union> {lang xa |xa. (xa, v) \<in> set ((λ(r,i). (Times a r, i)) x # map (λ(r,i). (Times a r, i)) (xs))}"
    by simp
  also have "\<dots> = \<Union> {lang xa |xa. (xa, v) \<in> set ((Times a (fst x), (snd x)) # map (λ(r,i). (Times a r, i)) (xs))}"
    by (simp add: case_prod_unfold)
  also have "\<dots> = \<Union> {lang xa |xa. (xa, v) \<in> set [(Times a (fst x), (snd x))] \<union> set (map (λ(r,i). (Times a r, i)) (xs))}"
    by simp
  also have "\<dots> = \<Union> {lang xa |xa. (xa, v) \<in> set [(Times a (fst x), (snd x))]} \<union> \<Union> {lang xa |xa. (xa, v) \<in> set (map (λ(r,i). (Times a r, i)) (xs))}"
    by blast
  also have "\<dots> = \<Union> {lang xa |xa. (xa, v) \<in> set [(Times a (fst x), (snd x))]} \<union> lang (var_prefix v (eq_times a (b,xs)))"
    using lang_var_prefix[of v _ "map (λ(r,i). (Times a r, i)) (xs)"] by simp
  also have "\<dots> = lang a @@ (if (snd x) = v then lang (fst x) else {}) \<union> lang (var_prefix v (eq_times a (b,xs)))"
    by simp
  also have "\<dots> = lang a @@ (if (snd x) = v then lang (fst x) else {}) \<union> lang a @@ lang (var_prefix v (b, xs))"
    using Cons.IH by simp
  also have "\<dots> = lang a @@ ((if (snd x) = v then lang (fst x) else {}) \<union> lang (var_prefix v (b, xs)))"
    by auto
  finally show ?case by auto
qed auto

lemma var_subst_preserve_zero:
    assumes "lang (var_prefix j (f,fs)) = {}"
    and "lang (var_prefix j (t,ts)) = {}"
    shows "lang (var_prefix j (var_subst (t,ts) v (f,fs))) = {}"
proof-
    obtain as bs where ab: "(as,bs) = partition (λ(r,i). i=v) ts"
        by auto
    then have bs_lang: "lang (var_prefix j (t, bs)) = {}"
        using assms unfolding lang_var_prefix by auto

    have "lang (var_prefix j (var_subst (t,ts) v (f,fs))) = lang (var_prefix j (eq_plus (t, bs) (eq_times (rsum (map fst as) Zero) (f, fs))))"
        unfolding var_subst.simps using ab by simp
    also have "\<dots> = lang (var_prefix j (t, bs)) \<union> (lang (rsum (map fst as) Zero) @@ lang (var_prefix j (f, fs)))"
        using var_prefix_eq_plus var_prefix_eq_times by (metis eq_times.simps)
    also have "\<dots> = lang (var_prefix j (t, bs))"
        using assms by simp
    also have "\<dots> = {}"
        using ab assms bs_lang by simp
    finally show ?thesis by blast
qed

corollary var_subst_preserve_zero2:
    assumes "lang (var_prefix j fs) = {}"
    and "lang (var_prefix j ts) = {}"
    shows "lang (var_prefix j (var_subst ts v fs)) = {}"
using var_subst_preserve_zero assms by (metis prod.exhaust_sel)

text ‹
var_subst_after
does not change the solution because it only does var_subst
›

lemma var_subst_after_preserve:
    assumes "solves s (var_subst_after v sol eqns)"
    and "eq_holds v sol (l2f s)"
    shows "solves s eqns"
unfolding solves_def proof
    show "length s = length eqns"
        using length_var_subst_after assms by (metis solves_def)
next
    show "\<forall>i<length s. eq_holds i (eqns ! i) ((!) s)"
proof
    have "length s = length eqns" using length_var_subst_after assms by (metis solves_def)

    fix i
    show "i < length s \<longrightarrow> eq_holds i (eqns ! i) ((!) s)" proof
        assume "i < length s"
        have ass: "(var_subst_after v sol eqns)!i = (if i \<le> v then eqns ! i else var_subst (eqns ! i) v sol)"
            using nth_var_subst_after ‹length s = length eqns› by (metis ‹i < length s›)
        show "eq_holds i (eqns ! i) ((!) s)"
        proof(cases "i \<le> v")
            case True
            then show ?thesis by (metis \<open>i < length s\<close> ass assms(1) solves_def)
            next
            case False
            then show ?thesis using assms ass unfolding solves_def var_subst_preserve_zero2
            by (metis \<open>i < length s\<close> l2f.elims var_subst_correct2)
        qed
        qed
    qed
qed


lemma fwd_elim_step_preserve:
    assumes "solves s (fwd_elim_step v eqns)"
    shows "solves s eqns"
proof(cases "v < length eqns")
    case True
    let ?nolet = "var_subst_after v (solve1 v (eqns!v)) (eqns[v := solve1 v (eqns!v)])"
    have nolet: "solves s ?nolet"
        using assms unfolding fwd_elim_step_nolet by simp

    have "eq_holds v (?nolet!v) (l2f s)"
        using nolet ‹v < length eqns› unfolding solves_def by auto
    then have sol: "eq_holds v (solve1 v (eqns!v)) (l2f s)"
        using var_subst_after_v assms True
        by (metis length_list_update nth_list_update_eq)

    then have "solves s (eqns[v := solve1 v (eqns!v)])"
        using nolet var_subst_after_preserve solve1_preserve sol by blast
    then show ?thesis using sol unfolding solves_def l2f.simps by (metis length_list_update nth_list_update_neq solve1_preserve2)
next
    case False
    then show ?thesis using assms by simp
qed

lemma fwd_elim_preserve:
    assumes "solves s (fwd_elim eqns)"
    shows "solves s eqns"
proof-
    let ?P = "solves s"
    have "?P (fwd_elim eqns)" using assms by auto
    then have "?P (forloop (length eqns) fwd_elim_step eqns)" by (metis fwd_elim.elims)
    then show ?thesis using fwd_elim_step_preserve forloop_preserve_back[]
    by metis
qed

text ‹the proof should be quite simmilar to fwd_elim_preserve›

lemma backsubst_preserve:
    assumes "solves s (backsubst eqns)"
    shows "solves s eqns"
sorry

text ‹
We want the equations to be triangular after forward elimination
meaning, every equation only depends on variables after it
›

text ‹
the zero column created by the vth iteration during forward elimination

it only starts at the diagonal
›


definition zero_col where
"zero_col v eqns = (\<forall>i < length eqns. i \<ge> v --> lang (var_prefix v (eqns!i)) = {})"


definition triangular where
"triangular eqns = (\<forall>i < length eqns. zero_col i eqns)"

value "fwd_elim ([(Zero, [(Zero, 0)]), (Zero, [(One, 1)])] :: (int rexp \<times> (int rexp \<times> nat) list) list)"
value "let sol = fwd_elim ([(Zero, [(Zero, 0)]), (Zero, [(One, 1)])] :: (int rexp \<times> (int rexp \<times> nat) list) list)
in lang (var_prefix 1 (sol!1))"

value "fwd_elim ([(Atom 6, []), (Atom 6, [(One, 0)])] :: (int rexp \<times> (int rexp \<times> nat) list) list)"

lemma solve1_create_zero:
    "lang (var_prefix v (solve1 v (r,rs))) = {}"
proof(cases "rexp_empty (var_prefix v (r,rs))")
  case True
  then show ?thesis using rexp_empty_iff by (metis solve1.simps)
next
  case False
  then show ?thesis using ardens_subst_correct by simp
qed



lemma var_subst_propagate_zero:
    assumes "lang (var_prefix v (f,fs)) = {}"
    shows "lang (var_prefix v (var_subst (t,ts) v (f,fs))) = {}"
proof-
    obtain as bs where ab: "(as,bs) = partition (λ(r,i). i=v) ts"
        by auto

    have "lang (var_prefix v (var_subst (t,ts) v (f,fs))) = lang (var_prefix v (eq_plus (t, bs) (eq_times (rsum (map fst as) Zero) (f, fs))))"
        unfolding var_subst.simps using ab by simp
    also have "\<dots> = lang (var_prefix v (t, bs)) \<union> (lang (rsum (map fst as) Zero) @@ lang (var_prefix v (f, fs)))"
        using var_prefix_eq_plus var_prefix_eq_times by (metis eq_times.simps)
    also have "\<dots> = lang (var_prefix v (t, bs))"
        using assms by simp
    also have "\<dots> = {}"
        using ab by simp
    finally show ?thesis by blast
qed

corollary var_subst_propagate_zero2:
    assumes "lang (var_prefix v fs) = {}"
    shows "lang (var_prefix v (var_subst ts v fs)) = {}"
using var_subst_propagate_zero by (metis assms prod.exhaust_sel)


text ‹
solve1 creates a zero on the diagonal
var_subst_after propagates it to the whole column
›
lemma fwd_elim_step_create_zero_column:
    "zero_col v (fwd_elim_step v eqns)"
proof-
    obtain sol where sol: "sol = solve1 v (eqns!v)" by auto
    then have "lang (var_prefix v sol) = {}"
        using solve1_create_zero by (metis prod.exhaust_sel)

    have len: "length (fwd_elim_step v eqns) = length eqns" unfolding fwd_elim_step_nolet by simp

    show ?thesis unfolding zero_col_def proof
        fix i
        show "i < length (fwd_elim_step v eqns) \<longrightarrow> v \<le> i \<longrightarrow> lang (var_prefix v (fwd_elim_step v eqns ! i)) = {}"
        proof
            assume "i < length (fwd_elim_step v eqns)"
            then have "i < length eqns" using len by simp
            show "v \<le> i \<longrightarrow> lang (var_prefix v (fwd_elim_step v eqns ! i)) = {}"
            proof
                assume "v \<le> i"
                then have "v < length eqns" using \<open>i < length (fwd_elim_step v eqns)\<close> len by simp

                have "lang (var_prefix v (var_subst_after v sol (eqns[v := sol]) ! v)) = {}"
                    unfolding sol by (metis \<open>lang (var_prefix v sol) = {}\<close> \<open>v < length eqns\<close> length_list_update nth_list_update_eq sol var_subst_after_v)
                then have "lang (var_prefix v (var_subst_after v sol (eqns[v := sol]) ! i)) = {}"
                proof(cases "i = v")
                  case False
                  then have "v < i" using ‹v \<le> i› by simp
                  have "var_subst_after v sol (eqns[v := sol]) ! i = (if i \<le> v then (eqns[v:=sol]) ! i else var_subst ((eqns[v:=sol]) ! i) v sol)"
                    using nth_var_subst_after[of i "eqns[v:=sol]" v sol] by (simp add: \<open>i < length eqns›)
                  then show ?thesis using var_subst_propagate_zero2[OF ‹lang (var_prefix v sol) = {}›] ‹v < i› by simp
                qed auto
                then show "lang (var_prefix v (fwd_elim_step v eqns ! i)) = {}"
                    unfolding fwd_elim_step_nolet sol by simp
            qed
        qed
    qed
qed

lemma solve1_preserve_zero:
    assumes "lang (var_prefix j (r,rs)) = {}"
    and "j \<noteq> v"
    shows "lang (var_prefix j (solve1 v (r,rs))) = {}"
using assms proof(cases "rexp_empty (var_prefix v (r,rs))")
    case False
    obtain as bs where ab: "(as,bs) = partition (λ(r,j). j=v) rs" by auto
    then have lang_bs: "lang (var_prefix j (r,bs)) = {}"
        using assms unfolding lang_var_prefix by simp

    have "lang (var_prefix j (ardens_subst v (r,rs))) = lang (var_prefix j (eq_times (Star (rsum (map fst as) Zero)) (r,bs)))"
        using ab by simp
    also have "\<dots> = lang (Star (rsum (map fst as) Zero)) @@ lang (var_prefix j (r, bs))"
        using var_prefix_eq_times[of j "Star (rsum (map fst as) Zero)" r bs] by simp
    also have "\<dots> = {}"
        using lang_bs by simp
    finally have "lang (var_prefix j (ardens_subst v (r,rs))) = {}"
        by blast
    then show ?thesis by (metis False solve1.simps)
qed auto

corollary solve1_preserve_zero2:
    assumes "lang (var_prefix j eq) = {}"
    shows "lang (var_prefix j (solve1 v eq)) = {}"
proof(cases "j = v")
  case True
  then show ?thesis using solve1_create_zero by (metis prod.exhaust_sel)
next
  case False
  then show ?thesis using solve1_preserve_zero by (metis assms eq_times.elims)
qed


text ‹
forward elimination does not modify earlier columns at all
so it preserves zero entries
›
lemma fwd_elim_step_preserve_zero_column:
    assumes "j < v"
    and "zero_col j eqns"
    shows "zero_col j (fwd_elim_step v eqns)"
unfolding zero_col_def proof(cases "v < length eqns")
    case True
    show "\<forall>i<length (fwd_elim_step v eqns). j \<le> i \<longrightarrow> lang (var_prefix j (fwd_elim_step v eqns ! i)) = {}"
    proof
    obtain sol where sol: "sol = solve1 v (eqns!v)" by auto
    then have "lang (var_prefix v sol) = {}"
        using solve1_create_zero by (metis prod.exhaust_sel)

    have len: "length (fwd_elim_step v eqns) = length eqns" unfolding fwd_elim_step_nolet by simp
    fix i
    show "i < length (fwd_elim_step v eqns) \<longrightarrow> j \<le> i \<longrightarrow> lang (var_prefix j (fwd_elim_step v eqns ! i)) = {}"
    proof
        assume "i < length (fwd_elim_step v eqns)"
        show "j \<le> i \<longrightarrow> lang (var_prefix j (fwd_elim_step v eqns ! i)) = {}"
        proof
            assume "j \<le> i"
            then have "i < length eqns" using \<open>i < length (fwd_elim_step v eqns)\<close> len by simp
            have "lang (var_prefix j (var_subst_after v sol (eqns[v := sol]) ! i)) = {}"
                proof(cases "j = v")
                  case True
                  then show ?thesis using ‹lang (var_prefix v sol) = {}› using assms by blast
                next
                  case False
                  have p: "var_subst_after v sol (eqns[v := sol]) ! i = (if i \<le> v then (eqns[v:=sol]) ! i else var_subst ((eqns[v:=sol]) ! i) v sol)"
                    using nth_var_subst_after[of i "eqns[v:=sol]" v sol] by (simp add: \<open>i < length eqns\<close>)
                  then show ?thesis using assms proof(cases "i = v")
                    case True
                    then have "var_subst_after v sol (eqns[v := sol]) ! i = (eqns[v:=sol]) ! i" using p by simp
                    also have "\<dots> = sol" using True \<open>i < length eqns\<close> by auto
                    finally show ?thesis using sol assms solve1_preserve_zero2 zero_col_def True ‹i < length eqns› ‹j \<le> i› by metis
                  next
                    case False
                    then show ?thesis proof(cases "i \<le> v")
                      case True
                      then have "var_subst_after v sol (eqns[v := sol]) ! i = (eqns[v:=sol]) ! i" using p by simp
                      also have "\<dots> = eqns!i" using False by auto
                      finally show ?thesis unfolding zero_col_def
                        using \<open>i < length eqns\<close> \<open>j \<le> i\<close> using assms zero_col_def by auto
                    next
                      case False
                      then have "var_subst_after v sol (eqns[v := sol]) ! i = var_subst ((eqns[v:=sol]) ! i) v sol" using p by simp
                      also have "\<dots> = var_subst (eqns ! i) v sol" using False by auto
                      finally show ?thesis using var_subst_preserve_zero2
                        by (metis True \<open>i < length eqns\<close> \<open>j \<le> i\<close> assms order.strict_implies_order sol solve1_preserve_zero2 zero_col_def)
                    qed
                  qed
                qed
            then show "lang (var_prefix j (fwd_elim_step v eqns ! i)) = {}"
                unfolding fwd_elim_step_nolet sol by simp
        qed
    qed
qed
next
    case False
    then show "\<forall>i<length (fwd_elim_step v eqns). j \<le> i \<longrightarrow> lang (var_prefix j (fwd_elim_step v eqns ! i)) = {}"
        using assms unfolding zero_col_def by simp
qed

lemma triangular_fwd_elim: "triangular (fwd_elim eqns)"
proof-
    have "length (fwd_elim eqns) = length eqns"
        unfolding fwd_elim.simps using forloop_preserve_fwd[of "λx. length x = length eqns"] length_fwd_elim_step by metis
    then show ?thesis
    unfolding triangular_def fwd_elim.simps
    using
        forloop_accumulate[of zero_col fwd_elim_step "length (fwd_elim eqns)" eqns]
        fwd_elim_step_create_zero_column
        fwd_elim_step_preserve_zero_column
    by (metis fwd_elim.simps)
qed

text ‹We call a system of equations triavial if all equations are of the form x = r›
abbreviation trivial where "trivial eqns \<equiv> (\<forall>i < length eqns.\<forall>v. lang (var_prefix v (eqns!i)) = {})"

text ‹
The system of equations becomes trivial column by column during backward substitution
so we want a column wise definition
›
definition zero_col_full where
"zero_col_full v eqns = (\<forall>i < length eqns. lang (var_prefix v (eqns!i)) = {})"

lemma trivial_columnwise: "(\<forall>i < length eqns. zero_col_full i eqns) \<Longrightarrow> trivial eqns"
proof
    fix j
    assume ass: "\<forall>i<length eqns. zero_col_full i eqns"
    show "j < length eqns \<longrightarrow> (\<forall>v. lang (var_prefix v (eqns ! j)) = {})" proof
        assume "j < length eqns"
        show "\<forall>v. lang (var_prefix v (eqns ! j)) = {}" proof
            fix v
            show "lang (var_prefix v (eqns ! j)) = {}"
                using ass unfolding zero_col_full_def sorry
        qed
    qed
qed


lemma trivial_lang:
    assumes "\<forall>i. lang (var_prefix i (r,rs)) = {}"
    shows "eq_lang (r,rs) s = lang r"
proof-
    have "\<forall>(x,i) \<in> set rs. lang x = {}"
        using assms lang_var_prefix[of _ r rs] by blast
    then show "eq_lang (r,rs) s = lang r"
        apply(induction rs)
        by auto
qed


lemma solve_trivial:
    assumes "trivial eqns"
    shows "solves (map fst eqns) eqns"
proof-
    let ?s = "l2f (map fst eqns)"
    have "\<forall>i<length (map fst eqns). eq_holds i (l2f eqns i) (l2f (map fst eqns))" proof
        fix i
        show "i < length (map fst eqns) \<longrightarrow> eq_holds i (l2f eqns i) (l2f (map fst eqns))"
        proof
            assume "i < length (map fst eqns)"
            have "\<exists>r rs. eqns!i = (r,rs)" by simp
            then obtain r rs where rs: "eqns!i = (r,rs)" by blast

            have "lang (?s i) = lang (l2f (map fst eqns) i)" by auto
            then have "\<dots> = lang (fst (eqns!i))" using \<open>i < length (map fst eqns)\<close> by auto
            then have "\<dots> = lang r" using rs by simp
            then have "lang (?s i) = lang r" using \<open>i < length (map fst eqns)\<close> by auto

            from ‹i < length (map fst eqns)› have "i < length eqns" by simp
            then have "eq_lang (r,rs) ?s = lang r"
                using ‹trivial eqns› trivial_lang rs by metis
            then show "eq_holds i (l2f eqns i) ?s" using rs ‹lang (?s i) = lang r› by simp
        qed
    qed
    then show ?thesis unfolding solves_def
    using length_map by auto
qed

text ‹backward substitution turns a triangular system of equations into a trivial one›

lemma trivial_backsubst:
    assumes "triangular eqns"
    shows "trivial (backsubst eqns)"
sorry

theorem solve_correct:
shows "solves (solve eqns) eqns "
proof-
    have "triangular (fwd_elim eqns)"
        using triangular_fwd_elim by simp
    then have "trivial (backsubst (fwd_elim eqns))"
        using trivial_backsubst by auto
    then have "solves (solve eqns) (backsubst (fwd_elim eqns))"
        using solve_trivial by auto
    then have "solves (solve eqns) (fwd_elim eqns)"
        using backsubst_preserve by auto
    then show ?thesis using fwd_elim_preserve by auto
qed


end
