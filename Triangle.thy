theory Triangle
imports CFG
begin

(* The algorithm and an initial part of the proof. So far I have only tried to show that
the result is of the right form (triangular). I have not tried to show that the language stays
unchanged. That will be harder.*)

(* The "real" functions are on sets, but there is often a list version as well.
The list version is intended for quickcheck test only (because quickcheck cannot deal with set comprehension {x. ...}.
Sometimes I have proved equivalence with the set version, but that is merely a sanity check.
Testing with nitpick is possible also for sets, but seems to work less well than quickcheck *)

definition "hdNts R = {B. \<exists>A w. (A,Nt B # w) \<in> R}"
definition hdNts_list :: "('n \<times> ('n, 't) sym list) list \<Rightarrow> 'n list" where
"hdNts_list R = [B. (A,Nt B # w) \<leftarrow> R]"

text \<open>"Expand head: Replace all rules \<open>A \<rightarrow> B w\<close> where \<open>B \<in> Ss\<close> (\<open>Ss\<close> = solved Nts)
by \<open>A \<rightarrow> v w\<close> where \<open>B \<rightarrow> v\<close>. Starting from the end of \<open>Ss\<close>\<close>
fun exp_hd :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"exp_hd A [] R = R" |
"exp_hd A (S#Ss) R =
 (let R' = exp_hd A Ss R;
      X = {(Al,Bw) \<in> R'. Al=A \<and> (\<exists>w. Bw = Nt S # w)};
      Y = {(A,v@w) |v w. \<exists>B. (A,Nt B # w) \<in> X \<and> (B,v) \<in> R'}
  in R' - X \<union> Y)"

fun exp_hd_list :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"exp_hd_list A [] R = R" |
"exp_hd_list A (S#Ss) R =
  (let R' = exp_hd_list A Ss R;
       X = [(Al,Nt B # w) . (Al,Nt B # w) \<leftarrow> R', Al=A, B = S] in
  [(B,w) \<leftarrow> R'. (B,w) \<notin> set X] @
  [(A,v@w). (_,Nt B # w) \<leftarrow> X, (C,v) \<leftarrow> R', B = C])"

value "exp_hd_list (1::int) [2,3] [(1, [Nt 2,Tm 0]::(int,int)sym list), (2,[Nt 3]), (3,[Tm 1])]"
value "exp_hd_list (1::int) [3,2] [(1, [Nt 2]::(int,int)sym list)]"

lemma "set(exp_hd_list A As R) = exp_hd A As (set R)"
(*nitpick*)
oops

text \<open>Remove left-recursive rules\<close>
definition rm_lrec ::  "'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"rm_lrec A R = R - {(A,Nt A # v)|v. True}"

fun hd_not_NA where
"hd_not_NA A w = (\<not>(\<exists>u. w = Nt A # u))"

fun hd_not_NA_list where
"hd_not_NA_list A [] = True" |
"hd_not_NA_list A (Tm _ # _) = True" |
"hd_not_NA_list A (Nt B # _) = (B\<noteq>A)"

lemma hd_not_NA_list: "hd_not_NA_list A w = hd_not_NA A w"
by(induction A w rule: hd_not_NA_list.induct) auto

definition rm_lrec_list ::  "'n \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"rm_lrec_list A R = [(B,w) \<leftarrow> R. B=A \<longrightarrow> hd_not_NA_list A w]"

lemma "set(rm_lrec_list A R) = rm_lrec A (set R)"
by(auto simp: rm_lrec_list_def rm_lrec_def hd_not_NA_list)

text \<open>Conversion from left-recursion to right-recursion:
Split \<open>A\<close>-rules into \<open>A \<rightarrow> u\<close> and \<open>A \<rightarrow> A v\<close>.
Keep \<open>A \<rightarrow> u\<close> but replace \<open>A \<rightarrow> A v\<close> by \<open>A \<rightarrow> u A'\<close>, \<open>A' \<rightarrow> v\<close>, \<open>A' \<rightarrow> v A'\<close>:\<close>
definition rrec_of_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"rrec_of_lrec A A' R =
  (let V = {v. (A,Nt A # v) \<in> R \<and> v \<noteq> []};
       U = {u. (A,u) \<in> R \<and> \<not>(\<exists>v. u = Nt A # v) }
  in (\<Union>u\<in>U. {(A,u)}) \<union> (\<Union>u\<in>U. {(A,u@[Nt A'])}) \<union> (\<Union>v\<in>V. {(A',v)}) \<union> (\<Union>v\<in>V. {(A',v @ [Nt A'])}))"

definition rrec_of_lrec_list ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"rrec_of_lrec_list A A' R =
  (let V = [v. (Al,Nt Ar # v) \<leftarrow> R, Al=A, Ar=A, v \<noteq> []];
       U = [u. (Al,u) \<leftarrow> R, Al=A, hd_not_NA_list A u]
  in [(A,u). u \<leftarrow> U] @ [(A,u@[Nt A']). u \<leftarrow> U] @ [(A',v). v \<leftarrow> V] @ [(A',v @ [Nt A']). v \<leftarrow>V])"

text \<open>Dealing with ("solving") Nt A. The new Nt A' is also given as a parameter.\<close>
definition solve_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"solve_lrec A A' R = rm_lrec A R \<union> rrec_of_lrec A A' R"

definition solve_lrec_list ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)prod list \<Rightarrow> ('n,'t)prod list" where
"solve_lrec_list A A' R = rm_lrec_list A R @ rrec_of_lrec_list A A' R"

text \<open>Put \<open>R\<close> into triangular form wrt \<open>As\<close> (using the new Nts \<open>As'\<close>).
That means that \<open>As\<close> are the Nts that still have to be solved.
In each step \<open>A#As\<close>, first the remaining \<open>As\<close> are solved, then \<open>A\<close> is solved.
This should mean that in the result of the outermost \<open>exp_hd A As\<close>, \<open>A\<close> only depends on \<open>A\<close>,
i.e. the \<open>A\<close> rules in the result of \<open>solve_lrec A A'\<close> are already in GNF. More precisely:
the result should be in triangular form.\<close>
fun solve_tri where
"solve_tri [] _ R = R" |
"solve_tri (A#As) (A'#As') R = solve_lrec A A' (exp_hd A As (solve_tri As As' R))"

fun solve_tri_list where
"solve_tri_list [] _ R = R" |
"solve_tri_list (A#As) (A'#As') R = solve_lrec_list A A' (exp_hd_list A As (solve_tri_list As As' R))"

lemma "set(solve_tri_list As As' R) = solve_tri As As' (set R)"
(*nitpick*)
oops

text \<open>\<open>A\<close> depends on \<open>B\<close> if there is a rule \<open>A \<rightarrow> B w\<close>:\<close>
definition dep_on :: "('n,'t) Prods \<Rightarrow> 'n \<Rightarrow> 'n set" where
"dep_on R A = {B. \<exists>w. (A,Nt B # w) \<in> R}"

definition dep_on_list :: "('n,'t) prod list \<Rightarrow> 'n \<Rightarrow> 'n list" where
"dep_on_list R A = [B. (Al,Nt B # _) \<leftarrow> R, Al=A]"

lemma "set(dep_on_list R A) = dep_on (set R) A"
by(auto simp: dep_on_def dep_on_list_def)

text \<open>Triangular form wrt \<open>[A1,\<dots>,An]\<close> means that \<open>Ai\<close> must not depend on \<open>Ai, \<dots>, An\<close>.
In particular: \<open>A0\<close> does not depend on any \<open>Ai\<close>: its rules are already in GNF.
Therefore one can convert a triangular form into GNF by backwards substitution:
the rules for \<open>Ai\<close> are used to expand the heads of all \<open>A(i+1),\<dots>,An\<close> rules,
starting with \<open>A0\<close>.\<close>

fun triangular :: "'n list \<Rightarrow> ('n \<times> ('n, 't) sym list) set \<Rightarrow> bool" where
"triangular [] R = True" |
"triangular (A#As) R = (dep_on R A \<inter> ({A} \<union> set As) = {} \<and> triangular As R)"

fun triangular_list :: "'a list \<Rightarrow> ('a \<times> ('a, 'b) sym list) list \<Rightarrow> bool" where
"triangular_list [] R = True" |
"triangular_list (A#As) R = (set(dep_on_list R A) \<inter> ({A} \<union> set As) = {} \<and> triangular_list As R)"

lemma exp_hd_preserves: "(A, Nt S # w) \<in> R \<Longrightarrow> S \<notin> set Ss \<Longrightarrow> (A, Nt S # w) \<in> exp_hd A Ss R"
proof(induction A Ss R rule: exp_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A S Ss R)
  then show ?case
    by(auto simp: Let_def)
qed

(* Should be true. Easy induction? *)
lemma exp_hd_preserves_neq: "B \<noteq> A \<Longrightarrow> (B,w) \<in> exp_hd A Ss R \<longleftrightarrow> (B,w) \<in> R"
sorry

(* True! Later *)
lemma Eps_free_exp_hd: "Eps_free R \<Longrightarrow> Eps_free (exp_hd A Ss R)"
sorry

text \<open>Let \<open>R\<close> be epsilon-free and in triangular form wrt \<open>Bs\<close>.
After \<open>exp_hd A Bs R\<close>, \<open>A\<close> depends only on what \<open>A\<close> depended on before or
what one of the \<open>B \<in> Bs\<close> depends on, but \<open>A\<close> does not depend on the \<open>Bs\<close>:\<close>
lemma dep_on_exp_hd:
  "\<lbrakk> Eps_free R; triangular Bs R; distinct Bs; A \<notin> set Bs \<rbrakk>
 \<Longrightarrow> dep_on (exp_hd A Bs R) A \<subseteq> (dep_on R A \<union> (\<Union>B\<in>set Bs. dep_on R B)) - set Bs"
proof(induction A Bs R rule: exp_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A B Bs R)
  then show ?case
    by(fastforce simp add: Let_def dep_on_def Cons_eq_append_conv Eps_free_exp_hd Eps_free_Nil exp_hd_preserves_neq set_eq_iff)
qed

(* ? *)
lemma dep_on_exp_hd_step:
  "\<lbrakk> dep_on R B \<inter> ({B} \<union> set Ts) = {}; distinct (B#Ts); A \<notin> set(B#Ts) \<rbrakk> \<Longrightarrow> dep_on (exp_hd A (B#Ts) R) A = dep_on(exp_hd A Ts R) A - {B}"
apply(simp add: Let_def)
oops

(* ? *)
lemma "\<lbrakk> Eps_free R; A \<notin> set Ts \<union> S; dep_on R A \<inter> S = {} ; triangular Ts R; distinct Ts \<rbrakk> \<Longrightarrow> dep_on (exp_hd A Ts R) A \<inter> (set Ts \<union> S) = {}"
(*nitpick*)
oops

lemma "\<lbrakk> eps_free R; length As \<le> length As'; distinct(As @ As'); nts R \<subseteq> set As \<rbrakk>
  \<Longrightarrow> triangular_list As (solve_tri_list As As' R)"
(* quickcheck  no counterexample found - not clear if that means much here *)
oops

(* This is the first key result we need: \<open>solve_tri\<close> produces a triangular form *)
lemma triangular_solve_tri:  "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As'); Nts R \<subseteq> set As \<rbrakk>
  \<Longrightarrow> triangular As (solve_tri As As' R)"
(* nitpick  no counterexample found - not clear if that means much here *)

oops

lemma Eps_free_exp_hd[simp]: "Eps_free (exp_hd A As R) = Eps_free R"
by(auto simp: Eps_free_def exp_hd_def)

lemma dep_on_Un: "dep_on (R \<union> S) A = dep_on R A \<union> dep_on S A"
by(auto simp add: dep_on_def)

lemma dep_on_UN: "dep_on (\<Union>RR) A = (\<Union>R\<in>RR. dep_on R A)"
by(auto simp add: dep_on_def)

lemma dep_on_solve_lrec1:
  "\<lbrakk> Eps_free R; A \<noteq> A' \<rbrakk> \<Longrightarrow> dep_on (solve_lrec A A' R) A \<subseteq> dep_on R A - {A}"
by(fastforce simp add:solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def dep_on_def dest: Eps_freeE_Cons)

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

lemma "\<lbrakk> length As = length As'; distinct(As @ As'); Eps_free R \<rbrakk>
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
lemma "\<lbrakk> Eps_free (set R); length As \<le> length As'; distinct(As @ As'); Nt (set R) \<subseteq> set As \<rbrakk>
 \<Longrightarrow> triangular_list As (solve_tri_list As As' R)"
quickcheck
oops

value "dep_on_list [(1,[T 5]::(int,int)symb list)] 1 []"
value "hdNts_list[(1,[T 5]::(int,int)symb list)]"
value "solve_tri_list [1] [2] [(1,[N 1, N 1]::(int,int)symb list)]"

lemma hdNts_exp_hd: "Eps_free R \<Longrightarrow> hdNts (exp_hd A As R) \<subseteq> hdNts R"
by(fastforce simp: hdNts_def exp_hd_def dest: Eps_freeE_Cons)

(* used? *)
lemma hdNts_solve_lrec: "hdNts (solve_lrec A A' R) \<subseteq> Nt R"
by(auto simp: hdNts_def solve_lrec_def rrec_of_lrec_def rm_lrec_def Cons_eq_append_conv
   dest: Eps_freeE_Cons dest: hd_in_Nt hd2_in_Nt)

lemma Eps_free_Un: "Eps_free (R \<union> S) = (Eps_free R \<and> Eps_free S)"
by(auto simp: Eps_free_def)

lemma Eps_free_UN: "Eps_free (\<Union>RR) = (\<forall>R \<in> RR. Eps_free R)"
by(auto simp: Eps_free_def)

lemma Eps_free_rm_lrec[simp]: "Eps_free R \<Longrightarrow> Eps_free (rm_lrec A R)"
by(auto simp: rm_lrec_def Eps_free_def)

lemma Eps_free_rrec_of_lrec[simp]: "Eps_free R \<Longrightarrow> Eps_free (rrec_of_lrec A A' R)"
by(auto simp: rrec_of_lrec_def Eps_free_def)

lemma Eps_free_solve_lrec[simp]: "Eps_free R \<Longrightarrow> Eps_free (solve_lrec A A' R)"
by(auto simp: solve_lrec_def Eps_free_Un)

lemma Eps_free_exp_hd[simp]: "Eps_free R \<Longrightarrow> Eps_free (exp_hd A As R)"
by(auto simp: exp_hd_def Eps_free_def split: prod.splits)

lemma hdNts_exp_hd_Un: "\<lbrakk> Eps_free R; A' \<notin> Nt R; A' \<notin> hdNts RA'; \<forall>(A,w) \<in> RA'. A=A' \<rbrakk>
 \<Longrightarrow> hdNts (exp_hd A' {} (R \<union> RA')) \<subseteq> hdNts R"
by(auto simp add: exp_hd_def hdNts_def Nt_def subset_iff Eps_free_def Cons_eq_append_conv split: prod.splits)

corollary hdNts_exp_hd_solve_lrec: "\<comment>\<open>\<lbrakk> Eps_free R; A' \<notin> Nt R; A' \<notin> hdNts RA'; \<forall>(A,w) \<in> RA'. A=A' \<rbrakk>
 \<Longrightarrow>\<close> hdNts (exp_hd A' {} (solve_lrec A A' R)) \<subseteq> hdNts R"
unfolding solve_lrec_def
sorry(*
apply(rule hdNts_exp_hd_Un)
by(auto simp add: exp_hd_def hdNts_def Nt_def subset_iff Eps_free_def Cons_eq_append_conv split: prod.splits)
*)
lemma "\<lbrakk> Eps_free R; length As = length As' \<rbrakk> \<Longrightarrow> hdNts (solve_tri As As' R) \<subseteq> hdNts R - set As"
proof(induction As As' R rule: solve_tri.induct)
  case (2 A As A' As' R)
  then show ?case
 using hdNts_exp_hd[of R A "set As"]
apply (simp)
apply (simp add: solve_lrec_def)
apply (auto simp add: Eps_free_UN)
unfolding solve_lrec_def Let_def
    using hdNts_solve_lrec  by fas tforce
qed auto

apply simp
apply simp
apply(rule subset_trans)
apply(erule meta_allE)
apply(erule meta_mp)
  apply (simp add: Eps_free_solve_lrec Eps_free_exp_hd)
  using hdNts_solve_lrec ldep_on_exp_hd by fa stforce

lemma "Eps_free R \<Longrightarrow> hdNts (solve_tri As R) \<subseteq> hdNts R - set As"
apply(induction As arbitrary: R)
apply simp
apply simp
apply(rule subset_trans)
apply(erule meta_allE)
apply(erule meta_mp)
  apply (simp add: Eps_free_solve_lrec Eps_free_exp_hd)
  using hdNts_solve_lrec ldep_on_exp_hd by fastforce

  by (metis bot.extremum_uniqueI solve_lrec_def empty_Diff Eps_free_solve_lrec hdNts_solve_lrec subsetI subset_Diff_insert)

type_synonym 'a ix = "'a * nat"

fun rt :: "('n,'t)symbs \<Rightarrow> bool" where
"rt [] = True" |
"rt (T _ # _) = True" |
"rt _ = False"

fun rtp :: "('n,'t)prod \<Rightarrow> bool" where
"rtp (_, w) = rt w"

definition rtps :: "('n,'t)Prods \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> set ps. rtp p)"

fun lnts :: "('n \<times> ('n, 't) symbs) list \<Rightarrow> 'n list" where
"lnts [] = []" |
"lnts ((_,[]) # ps) = lnts ps" |
"lnts ((_, T a # w) # ps) = lnts ps" |
"lnts ((_, N B # w) # ps) = List.insert B (lnts ps)"

definition rtps2 :: "'n set \<Rightarrow> ('n,'t)Prods \<Rightarrow> bool" where
"rtps2 M ps = (set (lnts ps) \<subseteq> M)"

lemma rtps_if_lnts_Nil: "lnts ps = [] \<Longrightarrow> rtps ps"
apply(induction ps rule: lnts.induct)
apply (auto simp: rtps_def List.insert_def split: if_splits)
done

theorem GNF:
fixes P :: "('n ix,'t)Prods"
(*assumes "\<not>(\<exists>(A,w) \<in> set(Prods G). w=[])"*)
shows "\<exists>P'::('n ix,'t)Prods. Lang S P' = Lang S P \<and> rtps P'"
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