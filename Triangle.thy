theory Triangle
imports GNF
begin
(*
Conjecture: fully expanded form is unique
*)

definition "hd_nts R = {B. \<exists>A w. (A,N B # w) \<in> R}"
definition hd_nts_list :: "('n \<times> ('n, 't) symb list) list \<Rightarrow> 'n list" where
"hd_nts_list R = [B. (A,N B # w) \<leftarrow> R]"

fun exp_hd :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"exp_hd A [] R = R" |
"exp_hd A (S#Ss) R =
 (let R' = exp_hd A Ss R;
      X = {(Al,Bw) \<in> R'. Al=A \<and> (\<exists>w. Bw = N S # w)};
      Y = {(A,v@w) |v w. \<exists>B. (A,N B # w) \<in> X \<and> (B,v) \<in> R'}
  in R' - X \<union> Y)"

fun hd_in_As where
"hd_in_As As [] = True" |
"hd_in_As As (T _ # _) = True" |
"hd_in_As As (N B # _) = (B \<in> set As)"

fun exp_hd_list :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"exp_hd_list A [] R = R" |
"exp_hd_list A (S#Ss) R =
  (let R' = exp_hd_list A Ss R;
       X = [(Al,N B # w) . (Al,N B # w) \<leftarrow> R', Al=A, B = S] in
  [(B,w) \<leftarrow> R'. (B,w) \<notin> set X] @
  [(A,v@w). (_,N B # w) \<leftarrow> X, (C,v) \<leftarrow> R', B = C])"

value "exp_hd_list (1::int)[3,2][(1, [N 2]::(int,int)symb list)]"


lemma "set(exp_hd_list A As R) = exp_hd A As (set R)"
nitpick
oops

definition rm_lrec ::  "'n \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"rm_lrec A R = R - {(A,N A # v)|v. True}"

fun hd_not_NA where
"hd_not_NA A w = (\<not>(\<exists>u. w = N A # u))"

fun hd_not_NA_list where
"hd_not_NA_list A [] = True" |
"hd_not_NA_list A (T _ # _) = True" |
"hd_not_NA_list A (N B # _) = (B\<noteq>A)"

lemma hd_not_NA_list: "hd_not_NA_list A w = hd_not_NA A w"
by(induction A w rule: hd_not_NA_list.induct) auto

definition rm_lrec_list ::  "'n \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"rm_lrec_list A R = [(B,w) \<leftarrow> R. B=A \<longrightarrow> hd_not_NA_list A w]"

lemma "set(rm_lrec_list A R) = rm_lrec A (set R)"
by(auto simp: rm_lrec_list_def rm_lrec_def hd_not_NA_list)

(* split into A \<rightarrow> u | Av; retain A \<rightarrow> u; add A \<rightarrow> uA', A' \<rightarrow> v | vA' *)

definition rrec_of_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"rrec_of_lrec A A' R =
  (let V = {v. (A,N A # v) \<in> R \<and> v \<noteq> []};
       U = {u. (A,u) \<in> R \<and> \<not>(\<exists>v. u = N A # v) }
  in (\<Union>u\<in>U. {(A,u)}) \<union> (\<Union>u\<in>U. {(A,u@[N A'])}) \<union> (\<Union>v\<in>V. {(A',v)}) \<union> (\<Union>v\<in>V. {(A',v @ [N A'])}))"

definition rrec_of_lrec_list ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"rrec_of_lrec_list A A' R =
  (let V = [v. (Al,N Ar # v) \<leftarrow> R, Al=A, Ar=A, v \<noteq> []];
       U = [u. (Al,u) \<leftarrow> R, Al=A, hd_not_NA_list A u]
  in [(A,u). u \<leftarrow> U] @ [(A,u@[N A']). u \<leftarrow> U] @ [(A',v). v \<leftarrow> V] @ [(A',v @ [N A']). v \<leftarrow>V])"
(*
lemma "set(rrec_of_lrec_list A A' R) = rrec_of_lrec A A' (set R)"
apply(auto simp: rrec_of_lrec_def rrec_of_lrec_list_def Let_def image_def hd_not_NA_list)
apply blast
  apply blast
  apply blast
apply(auto simp: rrec_of_lrec_def rrec_of_lrec_list_def Let_def image_def hd_not_NA_list
  split: prod.splits if_splits intro:)[]
  apply (metis list.set_intros(1))
apply(auto simp: rrec_of_lrec_def rrec_of_lrec_list_def Let_def image_def hd_not_NA_list
  split: prod.splits list.splits symb.splits if_splits)
  apply (metis list.set_intros(1))
apply (smt (verit) Pair_inject list.distinct(1) list.set_intros(1) list.simps(1) symb.simps(2,4)) 
apply (smt (verit) Pair_inject list.distinct(1) list.set_intros(1) list.simps(1) symb.simps(2,4))
  apply (metis list.set_intros(1))
  by (metis list.set_intros(1))
*)
definition solve_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"solve_lrec A A' R = rm_lrec A R \<union> rrec_of_lrec A A' R"

definition solve_lrec_list ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"solve_lrec_list A A' R = rm_lrec_list A R @ rrec_of_lrec_list A A' R"

fun solve_tri where
"solve_tri [] _ R = R" |
"solve_tri (A#As) (A'#As') R = solve_tri As As' (solve_lrec A A' (exp_hd A As R))"

fun solve_tri_list where
"solve_tri_list [] _ R = R" |
"solve_tri_list (A#As) (A'#As') R = solve_tri_list As As' (solve_lrec_list A A' (exp_hd_list A As R))"

lemma "set(solve_tri_list As As' R) = solve_tri As As' (set R)"
nitpick
oops

definition dep_on :: "('n,'t) prods \<Rightarrow> 'n \<Rightarrow> 'n set" where
"dep_on R A = {B. \<exists>w. (A,N B # w) \<in> R}"

definition dep_on_list :: "('n,'t) prod list \<Rightarrow> 'n \<Rightarrow> 'n list" where
"dep_on_list R A = [B. (Al,N B # _) \<leftarrow> R, Al=A]"

lemma "set(dep_on_list R A) = dep_on (set R) A"
by(auto simp: dep_on_def dep_on_list_def)

fun triangular :: "'n list \<Rightarrow> ('n \<times> ('n, 't) symb list) set \<Rightarrow> bool" where
"triangular [] R = True" |
"triangular (A#As) R = (dep_on R A \<inter> ({A} \<union> set As) = {} \<and> triangular As R)"
(*
fun triangular :: "'n list \<Rightarrow> 'n set \<Rightarrow> ('n \<times> ('n, 't) symb list) set \<Rightarrow> bool" where
"triangular [] S R = True" |
"triangular (A#As) S R = (dep_on R A \<inter> ({A} \<union> S) = {} \<and> triangular As ({A} \<union> S) R)"
*)
fun triangular_list :: "'a list \<Rightarrow> 'a set \<Rightarrow> ('a \<times> ('a, 'b) symb list) list \<Rightarrow> bool" where
"triangular_list [] S R = True" |
"triangular_list (A#As) S R = (set(dep_on_list R A) \<inter> ({A} \<union> S) = {} \<and> triangular_list As ({A} \<union> S) R)"

lemma exp_hd_preserves: "(A, N S # w) \<in> R \<Longrightarrow> S \<notin> set Ss \<Longrightarrow> (A, N S # w) \<in> exp_hd A Ss R"
proof(induction A Ss R rule: exp_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A S Ss R)
  then show ?case
    by(auto simp: Let_def)
qed

lemma exp_hd_preserves_neq: "B \<noteq> A \<Longrightarrow> (B,w) \<in> exp_hd A Ss R \<longleftrightarrow> (B,w) \<in> R"
sorry

lemma eps_free_exp_hd: "eps_free R \<Longrightarrow> eps_free (exp_hd A Ss R)"
sorry

(*
lemma dep_on_exp_hd:
  "\<lbrakk> eps_free_list R; triangular_list (rev Bs) S R; distinct Bs; A \<notin> set Bs \<rbrakk>
 \<Longrightarrow> set(dep_on_list (exp_hd_list A Bs R) A) \<subseteq> (set(dep_on_list R A) \<union> (\<Union>B\<in>set Bs. set(dep_on_list R B))) - set Bs"
quickcheck
value "exp_hd_list (1::int)[3][(1, [N 2]::(int,int)symb list),(2,[N 3])]"
oops
*)
lemma dep_on_exp_hd:
  "\<lbrakk> eps_free R; triangular Bs R; distinct Bs; A \<notin> set Bs \<rbrakk>
 \<Longrightarrow> dep_on (exp_hd A Bs R) A \<subseteq> (dep_on R A \<union> (\<Union>B\<in>set Bs. dep_on R B)) - set Bs"
proof(induction A Bs R arbitrary: S rule: exp_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A B Bs R)
  then show ?case
    by(fastforce simp add: Let_def dep_on_def Cons_eq_append_conv eps_free_exp_hd eps_free_Nil exp_hd_preserves_neq set_eq_iff)
qed

lemma dep_on_exp_hd_step:
  "\<lbrakk> dep_on R B \<inter> ({B} \<union> set Ts) = {}; distinct (B#Ts); A \<notin> set(B#Ts) \<rbrakk> \<Longrightarrow> dep_on (exp_hd A (B#Ts) R) A = dep_on(exp_hd A Ts R) A - {B}"
apply(simp add: Let_def)
sorry

lemma "\<lbrakk> eps_free R; A \<notin> set Ts \<union> S; dep_on R A \<inter> S = {} ; triangular Ts S R; distinct Ts \<rbrakk> \<Longrightarrow> dep_on (exp_hd A Ts R) A \<inter> (set Ts \<union> S) = {}"
(*nitpick*)
proof(induction A Ts R arbitrary: S rule: exp_hd.induct)
  case (1 A R)
  then show ?case by auto
next
  case (2 A T Ts R)
  then show ?case
apply(simp add: Let_def del: exp_hd.simps)
apply safe
apply (clarsimp simp add: dep_on_def Let_def)
apply(erule disjE)
apply safe[]
apply (auto simp: exp_hd_preserves)[]
apply safe[]
apply(simp add: Cons_eq_append_conv)
apply safe[]
    apply (meson eps_free_Nil eps_free_exp_hd)
apply(simp add: exp_hd_preserves_neq)
apply (clarsimp simp del: exp_hd.simps)
apply(subst (asm) dep_on_exp_hd_step)
apply simp
apply(erule disjE)
apply safe[]
apply(erule_tac x="insert T S" in meta_allE)
apply(auto)[]

 sorry
qed
nitpick

lemma "\<lbrakk> length As \<le> length As'; distinct(As @ As'); Nt R \<subseteq> set As \<rbrakk>
  \<Longrightarrow> triangular As (solve_tri As As' R)"
nitpick
oops

lemma eps_free_exp_hd[simp]: "eps_free (exp_hd A As R) = eps_free R"
by(auto simp: eps_free_def exp_hd_def)

lemma dep_on_Un: "dep_on (R \<union> S) A = dep_on R A \<union> dep_on S A"
by(auto simp add: dep_on_def)

lemma dep_on_UN: "dep_on (\<Union>RR) A = (\<Union>R\<in>RR. dep_on R A)"
by(auto simp add: dep_on_def)

lemma dep_on_solve_lrec1:
  "\<lbrakk> eps_free R; A \<noteq> A' \<rbrakk> \<Longrightarrow> dep_on (solve_lrec A A' R) A \<subseteq> dep_on R A - {A}"
by(fastforce simp add:solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def dep_on_def dest: eps_freeE_Cons)

lemma dep_on_solve_lrec2:
  "\<lbrakk> B \<noteq> A; B \<noteq> A' \<rbrakk> \<Longrightarrow> dep_on (solve_lrec A A' R) B = dep_on R B"
by(auto simp:solve_lrec_def dep_on_def rm_lrec_def rrec_of_lrec_def Let_def)
(*R is lrec for B not in As. rule out*)
lemma dep_on_exp_hd1:
  "set(dep_on_list (exp_hd_list A As R) A) = set([B \<leftarrow> dep_on_list R A. B \<in> set (As)]
  @ (if A \<in> set(dep_on_list R A) then [A] else[]))"
nitpick
by(auto simp: exp_hd_def dep_on_def Let_def)

lemma dep_on_exp_hd2:
  "B \<noteq> A \<Longrightarrow> dep_on (exp_hd A As R) B = dep_on R B"
by(auto simp: exp_hd_def dep_on_def)

lemma dep_on_solve_tri: "\<lbrakk> length As = length As'; A \<notin> set As \<union> set As' \<rbrakk>
  \<Longrightarrow> dep_on (solve_tri As As' R) A = dep_on R A"
proof(induction As As' arbitrary: R rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons A As A' As')
  then show ?case by (simp add: dep_on_solve_lrec2 dep_on_exp_hd2)
qed

lemma "A \<notin> set As \<Longrightarrow>dep_on (solve_tri As As' R) A = dep_on R A"
oops

lemma "\<lbrakk> length As = length As'; distinct(As @ As'); eps_free R \<rbrakk>
  \<Longrightarrow> triangular As (solve_tri As As' R)"
proof(induction As As' arbitrary: R rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons A As A' As')
  then show ?case using dep_on_solve_lrec1[of "exp_hd A As R" A A']
apply (simp add: dep_on_solve_tri )
 sorry
qed
lemma "\<lbrakk> eps_free (set R); length As \<le> length As'; distinct(As @ As'); Nt (set R) \<subseteq> set As \<rbrakk>
 \<Longrightarrow> triangular_list As (solve_tri_list As As' R)"
quickcheck
oops

value "dep_on_list [(1,[T 5]::(int,int)symb list)] 1 []"
value "hd_nts_list[(1,[T 5]::(int,int)symb list)]"
value "solve_tri_list [1] [2] [(1,[N 1, N 1]::(int,int)symb list)]"

lemma hd_nts_exp_hd: "eps_free R \<Longrightarrow> hd_nts (exp_hd A As R) \<subseteq> hd_nts R"
by(fastforce simp: hd_nts_def exp_hd_def dest: eps_freeE_Cons)

(* used? *)
lemma hd_nts_solve_lrec: "hd_nts (solve_lrec A A' R) \<subseteq> Nt R"
by(auto simp: hd_nts_def solve_lrec_def rrec_of_lrec_def rm_lrec_def Cons_eq_append_conv
   dest: eps_freeE_Cons dest: hd_in_Nt hd2_in_Nt)

lemma eps_free_Un: "eps_free (R \<union> S) = (eps_free R \<and> eps_free S)"
by(auto simp: eps_free_def)

lemma eps_free_UN: "eps_free (\<Union>RR) = (\<forall>R \<in> RR. eps_free R)"
by(auto simp: eps_free_def)

lemma eps_free_rm_lrec[simp]: "eps_free R \<Longrightarrow> eps_free (rm_lrec A R)"
by(auto simp: rm_lrec_def eps_free_def)

lemma eps_free_rrec_of_lrec[simp]: "eps_free R \<Longrightarrow> eps_free (rrec_of_lrec A A' R)"
by(auto simp: rrec_of_lrec_def eps_free_def)

lemma eps_free_solve_lrec[simp]: "eps_free R \<Longrightarrow> eps_free (solve_lrec A A' R)"
by(auto simp: solve_lrec_def eps_free_Un)

lemma eps_free_exp_hd[simp]: "eps_free R \<Longrightarrow> eps_free (exp_hd A As R)"
by(auto simp: exp_hd_def eps_free_def split: prod.splits)

lemma hd_nts_exp_hd_Un: "\<lbrakk> eps_free R; A' \<notin> Nt R; A' \<notin> hd_nts RA'; \<forall>(A,w) \<in> RA'. A=A' \<rbrakk>
 \<Longrightarrow> hd_nts (exp_hd A' {} (R \<union> RA')) \<subseteq> hd_nts R"
by(auto simp add: exp_hd_def hd_nts_def Nt_def subset_iff eps_free_def Cons_eq_append_conv split: prod.splits)

corollary hd_nts_exp_hd_solve_lrec: "\<comment>\<open>\<lbrakk> eps_free R; A' \<notin> Nt R; A' \<notin> hd_nts RA'; \<forall>(A,w) \<in> RA'. A=A' \<rbrakk>
 \<Longrightarrow>\<close> hd_nts (exp_hd A' {} (solve_lrec A A' R)) \<subseteq> hd_nts R"
unfolding solve_lrec_def
sorry(*
apply(rule hd_nts_exp_hd_Un)
by(auto simp add: exp_hd_def hd_nts_def Nt_def subset_iff eps_free_def Cons_eq_append_conv split: prod.splits)
*)
lemma "\<lbrakk> eps_free R; length As = length As' \<rbrakk> \<Longrightarrow> hd_nts (solve_tri As As' R) \<subseteq> hd_nts R - set As"
proof(induction As As' R rule: solve_tri.induct)
  case (2 A As A' As' R)
  then show ?case
 using hd_nts_exp_hd[of R A "set As"]
apply (simp)
apply (simp add: solve_lrec_def)
apply (auto simp add: eps_free_UN)
unfolding solve_lrec_def Let_def
    using hd_nts_solve_lrec  by fas tforce
qed auto

apply simp
apply simp
apply(rule subset_trans)
apply(erule meta_allE)
apply(erule meta_mp)
  apply (simp add: eps_free_solve_lrec eps_free_exp_hd)
  using hd_nts_solve_lrec ldep_on_exp_hd by fa stforce

lemma "eps_free R \<Longrightarrow> hd_nts (solve_tri As R) \<subseteq> hd_nts R - set As"
apply(induction As arbitrary: R)
apply simp
apply simp
apply(rule subset_trans)
apply(erule meta_allE)
apply(erule meta_mp)
  apply (simp add: eps_free_solve_lrec eps_free_exp_hd)
  using hd_nts_solve_lrec ldep_on_exp_hd by fastforce

  by (metis bot.extremum_uniqueI solve_lrec_def empty_Diff eps_free_solve_lrec hd_nts_solve_lrec subsetI subset_Diff_insert)

type_synonym 'a ix = "'a * nat"

fun rt :: "('n,'t)symbs \<Rightarrow> bool" where
"rt [] = True" |
"rt (T _ # _) = True" |
"rt _ = False"

fun rtp :: "('n,'t)prod \<Rightarrow> bool" where
"rtp (_, w) = rt w"

definition rtps :: "('n,'t)prods \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> set ps. rtp p)"

fun lnts :: "('n \<times> ('n, 't) symbs) list \<Rightarrow> 'n list" where
"lnts [] = []" |
"lnts ((_,[]) # ps) = lnts ps" |
"lnts ((_, T a # w) # ps) = lnts ps" |
"lnts ((_, N B # w) # ps) = List.insert B (lnts ps)"

definition rtps2 :: "'n set \<Rightarrow> ('n,'t)prods \<Rightarrow> bool" where
"rtps2 M ps = (set (lnts ps) \<subseteq> M)"

lemma rtps_if_lnts_Nil: "lnts ps = [] \<Longrightarrow> rtps ps"
apply(induction ps rule: lnts.induct)
apply (auto simp: rtps_def List.insert_def split: if_splits)
done

theorem GNF:
fixes P :: "('n ix,'t)prods"
(*assumes "\<not>(\<exists>(A,w) \<in> set(prods G). w=[])"*)
shows "\<exists>P'::('n ix,'t)prods. Lang S P' = Lang S P \<and> rtps P'"
proof (induction "lnts P" arbitrary: P)
  case Nil
  then have "rtps P" by (simp add: rtps_if_lnts_Nil)
  then show ?case by blast
next
  case (Cons A As)
  let ?X = 
  let ?P = undefined
  have "Lang S ?P = Lang S P" sorry
  moreover
  have "lnts ?P = As" sorry
  ultimately show ?case using Cons(1) by blast
qed

fun deleft :: "('n,'t) cfg \<Rightarrow> 'n \<Rightarrow> ('n,'t) cfg" where
"deleft G A = (let )"

end