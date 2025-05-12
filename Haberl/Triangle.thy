theory Triangle
imports "../CFG"
begin

(* The algorithms and an initial part of the proof. So far I have only tried to show that
the result is of the right form (triangular). The first important result you should try to prove
is lemma triangular_solve_tri (below).
I have not tried to show that the language stays unchanged. That will be harder.

Warning: until everything is proved, there may still be problems in the algorithms!
*)

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

lemma dep_on_Un: "dep_on (R \<union> S) A = dep_on R A \<union> dep_on S A"
by(auto simp add: dep_on_def)

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
  by(induction A Ss R rule: exp_hd.induct)  (auto simp add: Let_def)

(* True! Later *)
lemma Eps_free_exp_hd: "Eps_free R \<Longrightarrow> Eps_free (exp_hd A Ss R)"
proof (induction A Ss R rule: exp_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A S Ss R)
  then show ?case by (auto simp add: Eps_free_def Let_def)
qed

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


text \<open>WIP Section \<close>


text \<open> Eps_free preservation \<close>

lemma Eps_free_solve_lrec: "Eps_free R \<Longrightarrow> Eps_free (solve_lrec A A' R)"
  by (auto simp add: solve_lrec_def rrec_of_lrec_def Eps_free_def Let_def rm_lrec_def)

lemma Eps_free_solve_tri: "Eps_free R \<Longrightarrow> length As \<le> length As' \<Longrightarrow> Eps_free (solve_tri As As' R)"
  by (induction As As' R rule: solve_tri.induct) (auto simp add: Eps_free_solve_lrec Eps_free_exp_hd)

lemma dep_on_exp_hd_simp2: "B \<noteq> A \<Longrightarrow> dep_on (exp_hd A As R) B = dep_on R B"
  by (auto simp add: dep_on_def rm_lrec_def rrec_of_lrec_def Let_def exp_hd_preserves_neq)

text  \<open> exp_hd keeps triangular, if it does not expand a Nt considered in triangular\<close>
lemma triangular_exp_hd: "\<lbrakk>A \<notin> set As; triangular As R\<rbrakk> \<Longrightarrow> triangular As (exp_hd A Bs R)"
proof(induction As)
  case Nil
  then show ?case by simp
next
  case (Cons a As)
  have "triangular (a # As) (exp_hd A Bs R) = (dep_on (exp_hd A Bs R) a \<inter> ({a} \<union> set As) = {} \<and> triangular As (exp_hd A Bs R))" by simp
  also have "... = (dep_on (exp_hd A Bs R) a \<inter> ({a} \<union> set As) = {})" using Cons by simp
  also have "... = (dep_on R a \<inter> ({a} \<union> set As) = {})" using dep_on_exp_hd_simp2 Cons
    by (metis list.set_intros(1))
  then show ?case using Cons by auto
qed


lemma dep_on_solve_lrec_simp2: "A \<noteq> B \<Longrightarrow> A' \<noteq> B \<Longrightarrow> dep_on (solve_lrec A A' R) B = dep_on R B"
  by (auto simp add: solve_lrec_def dep_on_def rm_lrec_def rrec_of_lrec_def Let_def)

lemma triangular_solve_lrec: "\<lbrakk>A \<notin> set As; A' \<notin> set As; triangular As R\<rbrakk> \<Longrightarrow> triangular As (solve_lrec A A' R)"
proof(induction As)
  case Nil
  then show ?case by simp
next
  case (Cons a As)
  have "triangular (a # As) (solve_lrec A A' R) = (dep_on (solve_lrec A A' R) a \<inter> ({a} \<union> set As) = {} \<and> triangular As (solve_lrec A A' R))" by simp
  also have "... = (dep_on (solve_lrec A A' R) a \<inter> ({a} \<union> set As) = {})" using Cons by auto
  also have "... = (dep_on R a \<inter> ({a} \<union> set As) = {})" using Cons dep_on_solve_lrec_simp2
    by (metis list.set_intros(1))
  then show ?case using Cons by auto
qed

text \<open> shows that solving more Nts does not remove the triangular property of previously solved Nts \<close>
lemma part_triangular_induct_step: "\<lbrakk>Eps_free R; distinct ((A#As)@(A'#As')); triangular As (solve_tri As As' R)\<rbrakk>
   \<Longrightarrow> triangular As (solve_tri (A#As) (A'#As') R)"
proof(cases "As = []")
  case True
  then show ?thesis by auto
next
  case False
  assume assms: "Eps_free R" "triangular As (solve_tri As As' R)" "distinct ((A#As)@(A'#As'))"
  then show ?thesis by (auto simp add: triangular_exp_hd triangular_solve_lrec)
qed

text \<open> Couple of small lemmas about dep_on \<close>
lemma rm_lrec_rem_own_dep: "A \<notin> dep_on (rm_lrec A R) A"
  by (auto simp add: dep_on_def rm_lrec_def)

lemma rrec_of_lrec_has_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (rrec_of_lrec A A' R) A"
  apply (auto simp add: dep_on_def rrec_of_lrec_def Let_def)
  by (metis append_eq_Cons_conv list.inject sym.inject(1))

lemma solve_lrec_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (solve_lrec A A' R) A"
  by (auto simp add: dep_on_Un solve_lrec_def rm_lrec_rem_own_dep rrec_of_lrec_has_no_own_dep)

lemma dep_on_rem_lrec_simp: "dep_on (rm_lrec A R) A = dep_on R A - {A}"
  by (auto simp add: dep_on_def rm_lrec_def)

lemma dep_on_rrec_of_lrec_simp: "Eps_free R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> dep_on (rrec_of_lrec A A' R) A = dep_on R A - {A}"
  apply (auto simp add: dep_on_def rrec_of_lrec_def Let_def)
  apply (metis Eps_free_Nil butlast.simps(2) butlast_snoc)
  by (metis Eps_freeE_Cons hd_append list.sel(1) sym.inject(1))

text \<open> Half an Isar proof for dep_on_rrec_of_lrec_simp\<close>
(*lemma "Eps_free R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> dep_on (rrec_of_lrec A A' R) A = dep_on R A - {A}"
proof
  show "Eps_free R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> dep_on (rrec_of_lrec A A' R) A \<subseteq> dep_on R A - {A}"
  proof 
    fix x
    assume 1: "A \<noteq> A'" and 2: "x \<in> dep_on (rrec_of_lrec A A' R) A" and 3: "Eps_free R"
    then show "x \<in> dep_on R A - {A}"
    proof (cases "x=A")
      case True
      then show ?thesis using rrec_of_lrec_has_no_own_dep 1 2
        by metis
    next
      case False
      then show ?thesis using 1 2 3 apply (auto simp add: dep_on_def rrec_of_lrec_def Let_def) apply -
        by (metis Eps_free_Nil append_Nil2 butlast.simps(2) butlast_append)
      qed
  qed
next
  assume "A \<noteq> A'"
  then show "dep_on R A - {A} \<subseteq> dep_on (rrec_of_lrec A A' R) A"
    by (auto simp add: dep_on_def rrec_of_lrec_def Let_def)
qed*)

lemma dep_on_solve_lrec_simp: "Eps_free R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> dep_on (solve_lrec A A' R) A = dep_on R A - {A}"
  by (simp add: dep_on_rem_lrec_simp dep_on_rrec_of_lrec_simp dep_on_Un solve_lrec_def)


lemma triangular_dep_on_induct_step: "\<lbrakk>Eps_free R; length As \<le> length As'; distinct ((A # As) @ A' # As'); triangular As (solve_tri As As' R)\<rbrakk>
   \<Longrightarrow> (dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {})"
proof(cases "As = []")
  case True
  assume assms: "triangular As (solve_tri As As' R)" "Eps_free R" "distinct ((A # As) @ A' # As')"
  then show ?thesis using True solve_lrec_no_own_dep by fastforce
next
  case False
  assume assms: "triangular As (solve_tri As As' R)" "Eps_free R" "distinct ((A # As) @ A' # As')" "length As \<le> length As'"
  have "Eps_free (solve_tri As As' R)"
    using assms Eps_free_solve_tri by auto
  then have test: "X \<in> set As \<Longrightarrow> X \<notin> dep_on (exp_hd A As (solve_tri As As' R)) A" for X
    using assms dep_on_exp_hd
    by (metis distinct.simps(2) distinct_append insert_Diff subset_Diff_insert)

  have A: "triangular As (solve_tri (A # As) (A' # As') R)" using part_triangular_induct_step assms by metis

  have "dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) 
        = (dep_on (exp_hd A As (solve_tri As As' R)) A - {A}) \<inter> ({A} \<union> set  As)"
    using assms by (simp add: dep_on_solve_lrec_simp Eps_free_solve_tri Eps_free_exp_hd)
  also have "... = dep_on (exp_hd A As (solve_tri As As' R)) A \<inter> set As"
    using assms by auto
  also have "... = {}" using test by fastforce
  finally show ?thesis by auto
qed

text \<open> stronger than triangular_solve_tri (one less assumption)\<close>
lemma part_triangular_solve_tri:  "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As')\<rbrakk>
  \<Longrightarrow> triangular As (solve_tri As As' R)"
proof(induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 A As A' As' R)
  then have "length As \<le> length As' \<and> distinct (As @ As')" by auto
  then have A: "triangular As (solve_tri (A # As) (A' # As') R)" using part_triangular_induct_step 2 "2.IH" by metis

  have "(dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {})"
    using triangular_dep_on_induct_step 2 by (metis \<open>length As \<le> length As' \<and> distinct (As @ As')\<close>) 
  then show ?case using A by simp
next
  case (3 v va c)
  then show ?case by simp
qed

(* This is the first key result we need: \<open>solve_tri\<close> produces a triangular form *)
(*lemma triangular_solve_tri:  "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As'); Nts R \<subseteq> set As \<rbrakk>
  \<Longrightarrow> triangular As (solve_tri As As' R)"
proof(induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 A As A' As' R)
  then have "triangular As (solve_tri (A # As) (A' # As') R)" using test1
  have "triangular (A # As) (solve_tri (A # As) (A' # As') R) = (dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {} \<and> triangular As (solve_tri (A # As) (A' # As') R))"
    by simp
  also have "... = (dep_on (solve_tri (A # As) (A' # As') R) A \<inter> ({A} \<union> set As) = {})" using test1 2 by auto
  then show ?case using test1
next
  case (3 v va c)
  then show ?case by simp
qed*)

text \<open> Section Language equivalence \<close>


text \<open> Subset Relation of all Derivations implies a Subset Relation of the Languages \<close>
lemma Ders_sub_Lang_sub: "Ders R A \<subseteq> Ders R' A \<Longrightarrow> Lang R A \<subseteq> Lang R' A"
  by (auto simp add: Lang_def Ders_def)


text \<open> If there es a derivation from u to v where u and v start with different non-terminals then
 the derivation can be split into two parts,
 where the first is a left-derivation which only replaces the starting non-terminal  of u left-recursively
 and the second goes from this result to v.
 
 The left-derivation is given as a list of intermediary words
 which all but the last start with the same non-terminal as u \<close>
lemma test1: "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> hd p = Nt A \<Longrightarrow> hd q \<noteq> Nt A \<Longrightarrow> R \<turnstile> p \<Rightarrow>(n) q \<Longrightarrow>
  (\<exists>ds pp qq. ds \<noteq> [] \<and> hd ds = p \<and> (\<forall>i < length ds - 1. hd (ds ! i) = Nt A \<and> (ds ! i) \<noteq> [] \<and> R \<turnstile> ds ! i \<Rightarrow>l ds ! Suc i) \<and> last ds = pp \<and> R \<turnstile> pp \<Rightarrow>l qq \<and> R \<turnstile> qq \<Rightarrow>* q \<and> hd pp = Nt A \<and> hd qq \<noteq> Nt A)"
proof (induction n arbitrary: p)
  case 0
  then have pq_not_Nil: "p \<noteq> [] \<and> q \<noteq> []" using Eps_free_derives_Nil
    by simp

  have "p = q" using 0 by auto
  then show ?case using pq_not_Nil 0 by auto
next
  case (Suc n)
  then have pq_not_Nil: "p \<noteq> [] \<and> q \<noteq> []" using Eps_free_derives_Nil
    by (metis deriven_from_empty relpowp_imp_rtranclp)

  have ex_p': "\<exists>p'. p = Nt A # p'" using pq_not_Nil Suc
    by (metis hd_Cons_tl)
  then obtain p' where P: "p = Nt A # p'" by blast
  have "\<nexists>q'. q = Nt A # q'" using pq_not_Nil Suc
    by fastforce

  then have "\<exists>n1 n2 \<alpha> q1 q2. Suc n = Suc (n1 + n2) \<and> q = q1 @ q2 \<and> 
   (A,\<alpha>) \<in> R \<and> R \<turnstile> \<alpha> \<Rightarrow>(n1) q1 \<and> R \<turnstile> p' \<Rightarrow>(n2) q2" using P ex_p' deriven_Cons_decomp[of "Suc n" R "Nt A" p' q] Suc by auto
  then have "\<exists>\<alpha> p''. p = Nt A # p'' \<and> R \<turnstile> \<alpha> @ p'' \<Rightarrow>(n) q \<and> (A, \<alpha>) \<in> R"
    using P deriven_append_decomp by fastforce
  then obtain \<alpha> p'' where deriven_p_IH: " p = Nt A # p'' \<and> R \<turnstile> \<alpha> @ p'' \<Rightarrow>(n) q" and A\<alpha>_R:  "(A, \<alpha>) \<in> R" by blast
  have p_derivel_ap'': "R \<turnstile> p \<Rightarrow>l \<alpha> @ p''" using deriven_p_IH A\<alpha>_R
      by (simp add: derivel_Nt_Cons derivel_imp_derive)
  show ?case
  proof (cases "hd \<alpha> = Nt A")
    case True
    have \<alpha>_not_Nil: "\<alpha> \<noteq> []" using "Suc.prems"(1) A\<alpha>_R by (auto simp add: Eps_free_def)
    then have "\<exists>ds pp qq. ds \<noteq> [] \<and> hd ds = (\<alpha> @ p'') \<and> (\<forall> i < length ds - 1. hd (ds ! i) = Nt A \<and> (ds ! i) \<noteq> [] \<and> R \<turnstile> ds ! i \<Rightarrow>l ds ! Suc i) \<and> last ds = pp \<and> R \<turnstile> pp \<Rightarrow>l qq \<and> R \<turnstile> qq \<Rightarrow>* q \<and> hd pp = Nt A \<and> hd qq \<noteq> Nt A"
      using Suc deriven_p_IH True by auto
    then obtain ds pp qq where P: "ds \<noteq> [] \<and> hd ds = (\<alpha> @ p'') \<and> (\<forall> i < length ds - 1. hd (ds ! i) = Nt A \<and> (ds ! i) \<noteq> [] \<and> R \<turnstile> ds ! i \<Rightarrow>l ds ! Suc i) \<and> last ds = pp \<and> R \<turnstile> pp \<Rightarrow>l qq \<and> R \<turnstile> qq \<Rightarrow>* q \<and> hd pp = Nt A \<and> hd qq \<noteq> Nt A" by blast
    then have 1: "(p#ds) \<noteq> [] \<and> hd (p#ds) = p \<and> last (p#ds) = pp"
      by auto
    
    then have 2: "(i < length (p#ds) - 1 \<longrightarrow> hd ((p#ds) ! i) = Nt A \<and> ((p#ds) ! i) \<noteq> [] \<and> R \<turnstile> (p#ds) ! i \<Rightarrow>l (p#ds) ! Suc i)" for i
      using Suc P p_derivel_ap'' \<alpha>_not_Nil by (cases i) (auto simp flip: hd_conv_nth)
    then show ?thesis using 1 2 P by blast
  next
    case False
    have \<alpha>_not_Nil: "\<alpha> \<noteq> []" using "Suc.prems"(1) A\<alpha>_R by (auto simp add: Eps_free_def)
    
    have 3: "[p] \<noteq> [] \<and> hd [p] = p \<and> (\<forall> i < length [p] - 1. hd ([p] ! i) = Nt A \<and> ([p] ! i) \<noteq> [] \<and> R \<turnstile> [p] ! i \<Rightarrow>l [p] ! Suc i) \<and> last [p] = p"
      by auto
    have "R \<turnstile> p \<Rightarrow>l (\<alpha> @ p'') \<and> R \<turnstile> (\<alpha> @ p'') \<Rightarrow>* q \<and> hd p = Nt A \<and> hd (\<alpha> @ p'') \<noteq> Nt A"
      using p_derivel_ap'' \<alpha>_not_Nil deriven_p_IH False by (auto simp add: relpowp_imp_rtranclp)
    then show ?thesis using 3 by blast
  qed
qed


text \<open> TODO
    this lemma should prove that if a left-recursive derivation exists
   then there exists a right-recursive derivation for the set of productions produced by solve_lrec \<close>
lemma derivel_R_imp_deriver_solve_lrec_R:
  "(ds \<noteq> [] \<and> hd ds = [Nt A] \<and> (\<forall>i < length ds - 1. hd (ds ! i) = Nt A \<and> (ds ! i) \<noteq> [] \<and> R \<turnstile> ds ! i \<Rightarrow>l ds ! Suc i) \<and> last ds = Nt A # q')
  \<Longrightarrow> (\<exists>dsr. dsr \<noteq> [] \<and> hd dsr = [Nt A'] \<and> (\<forall>i < length dsr - 1. last (dsr ! i) = Nt A' \<and> (dsr ! i) \<noteq> [] \<and>  (solve_lrec A A' R) \<turnstile> dsr ! i \<Rightarrow>r dsr ! Suc i) \<and> last dsr = q' @ [Nt A'])"
proof (induction "length ds" arbitrary: ds q')
  case 0
  then show ?case by simp
next
  case ind: (Suc x)
  then have "\<exists>frt lst. ds = frt @ [lst]"
    by (metis append_butlast_last_id)
  then obtain frt lst where ds_decomp: "ds = frt @ [lst]" by blast
  then show ?case
  proof (cases x)
    case 0
    then show ?thesis sorry
  next
    case (Suc nat)
    then have 1: "frt \<noteq> []"
      using ds_decomp ind.hyps(2) by fastforce
    then have 2: "i < length frt - 1 \<Longrightarrow> frt ! i = ds ! i \<and> frt ! Suc i = ds ! Suc i" for i
      using ds_decomp by (auto simp add: nth_append_left)
    have "hd (last frt) = Nt A \<and> last frt \<noteq> []" using 1 ds_decomp ind by (auto simp add: last_conv_nth nth_append_left)
    then have "\<exists>p'. last frt = Nt A # p'"
      by (metis hd_Cons_tl)
    then obtain p' where "last frt = Nt A # p'" by blast
    then have "x = length frt \<Longrightarrow>
    frt \<noteq> [] \<and>
    hd frt = [Nt A] \<and>
    (\<forall>i<length frt - 1. hd (frt ! i) = Nt A \<and> frt ! i \<noteq> [] \<and> R \<turnstile> frt ! i \<Rightarrow>l frt ! Suc i) \<and> last frt = Nt A # p'"
      using ds_decomp ind 1 2 by (auto simp add: last_conv_nth)
    then have "\<exists>dsr. dsr \<noteq> [] \<and>
        hd dsr = [Nt A'] \<and>
        (\<forall>i<length dsr - 1. last (dsr ! i) = Nt A' \<and> dsr ! i \<noteq> [] \<and> solve_lrec A A' R \<turnstile> dsr ! i \<Rightarrow>r dsr ! Suc i) \<and>
        last dsr = p' @ [Nt A']" using ind ds_decomp by auto
    then obtain dsr where dsr_props: "dsr \<noteq> [] \<and>
        hd dsr = [Nt A'] \<and>
        (\<forall>i<length dsr - 1. last (dsr ! i) = Nt A' \<and> dsr ! i \<noteq> [] \<and> solve_lrec A A' R \<turnstile> dsr ! i \<Rightarrow>r dsr ! Suc i) \<and>
        last dsr = p' @ [Nt A']" by blast
    let ?dsr = "dsr @ [q' @ [Nt A']]"
    have 1: "?dsr \<noteq> [] \<and> hd ?dsr = [Nt A'] \<and> last ?dsr = q' @ [Nt A']" using dsr_props by auto
    have 2: "(i<length ?dsr - 1 \<longrightarrow> last (?dsr ! i) = Nt A' \<and> ?dsr ! i \<noteq> [] \<and> solve_lrec A A' R \<turnstile> ?dsr ! i \<Rightarrow>r ?dsr ! Suc i)" for i
    proof (cases "i = length dsr - 1")
      case True
      then have "last (?dsr ! i) = Nt A' \<and> ?dsr ! i \<noteq> []" using dsr_props by (auto simp add: nth_append_left last_conv_nth)
      have "(solve_lrec A A' R \<turnstile> ?dsr ! i \<Rightarrow>r ?dsr ! Suc i) = (solve_lrec A A' R \<turnstile> last dsr \<Rightarrow>r last ?dsr)" 
        using True dsr_props by (auto simp add: nth_append_left last_conv_nth)
      also have "... = (solve_lrec A A' R \<turnstile> p' @ [Nt A'] \<Rightarrow>r q' @ [Nt A'])" using dsr_props by auto
      then show ?thesis sorry
    next
      case False
      then show ?thesis using dsr_props by (auto simp add: nth_append_left)
    qed
    have "?dsr \<noteq> [] \<and>
          hd ?dsr = [Nt A'] \<and>
          (\<forall>i<length ?dsr - 1. last (?dsr ! i) = Nt A' \<and> ?dsr ! i \<noteq> [] \<and> solve_lrec A A' R \<turnstile> ?dsr ! i \<Rightarrow>r ?dsr ! Suc i) \<and>
          last ?dsr = q' @ [Nt A']" sorry
    then show ?thesis sorry
  qed
qed

text \<open> Helper lemma which could be moved to CFG.thy \<close>
lemma Eps_free_deriven_Nil:
  assumes R: "Eps_free R" "R \<turnstile> l \<Rightarrow>(n) []" shows "l = []"
proof (rule ccontr)
  assume l1: "l \<noteq> []"
  have "R \<turnstile> l \<Rightarrow>* []" using R
    by (simp add: relpowp_imp_rtranclp)
  then show "False" using l1 Eps_free_derives_Nil
    using assms by auto
qed

text \<open> Helper lemma which could be moved to CFG.thy \<close>
lemma deriven_Tm_prepend: "R \<turnstile> map Tm t @ u \<Rightarrow>(n) v \<Longrightarrow> \<exists>v1. v = map Tm t @ v1 \<and> R \<turnstile> u \<Rightarrow>(n) v1"
  by (induction t arbitrary: v) (auto simp add: deriven_Tm_Cons)  

text \<open> TODO
  this lemma will be the heart of the prove of "Lang R A" \<subseteq> "Lang (solve_lrec R) A"
  it should boil down to couple of case distinctions and the lemmas test1 and derivel_R_imp_deriver_solve_lrec_R \<close>
lemma "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> p \<noteq> [] \<Longrightarrow> R \<turnstile> p \<Rightarrow>(n) map Tm q \<Longrightarrow> (solve_lrec B B' R) \<turnstile> p \<Rightarrow>* map Tm q"
proof (induction n arbitrary: p q rule: nat_less_induct)
  case (1 n)
  then show ?case
  proof (cases "\<exists>pt. p = map Tm pt")
    case True
    then obtain pt where "p = map Tm pt" by blast
    then have "map Tm q = p"
      using deriven_from_TmsD "1.prems"(5) by blast
    then show ?thesis by simp
  next
    case False
    then have "\<exists>C pt p2. p = map Tm pt @ Nt C # p2" sorry
    then obtain C pt p2 where P: "p = map Tm pt @ Nt C # p2" by blast
    then have "R \<turnstile> map Tm pt @ Nt C # p2 \<Rightarrow>l(n) map Tm q" using 1 by (simp add: deriveln_iff_deriven)
    then have "\<exists>q2. map Tm q = map Tm pt @ q2 \<and> R \<turnstile> Nt C # p2 \<Rightarrow>l(n) q2"
      by (simp add: deriveln_map_Tm_append[of "n" R "pt" "Nt C # p2" "map Tm q"])
    then obtain q2 where P1: "map Tm q = map Tm pt @ q2 \<and> R \<turnstile> Nt C # p2 \<Rightarrow>l(n) q2" by blast
    then have "n \<noteq> 0"
      by (metis False P relpowp_0_E)
    then have "\<exists>m. n = Suc m"
      by (meson old.nat.exhaust)
    then obtain m where n_Suc: "n = Suc m" by blast
    have "\<exists>q2t. q2 = map Tm q2t"
      by (metis P1 append_eq_map_conv)
    then obtain q2t where q2_tms: "q2 = map Tm q2t" by blast
    then show ?thesis
    proof (cases "C = B")
      case True
      then show ?thesis sorry
    next
      case C_not_B: False
      then have "\<exists>w. (C, w) \<in> R \<and> R \<turnstile> w @ p2 \<Rightarrow>l(m) q2"
        by (metis P1 derivel_Nt_Cons relpowp_Suc_D2 n_Suc)
      then obtain w where P2: "(C, w) \<in> R \<and> R \<turnstile> w @ p2 \<Rightarrow>l(m) q2" by blast
      then have rule_in_solve_lrec: "(C, w) \<in> (solve_lrec B B' R)" using C_not_B by (auto simp add: solve_lrec_def rm_lrec_def)
      have derivem: "R \<turnstile> w @ p2 \<Rightarrow>(m) q2" using q2_tms P2 by (auto simp add: deriveln_iff_deriven)
      have "w @ p2 \<noteq> []"
        using "1.prems"(1) Eps_free_Nil P2 by fastforce
      then have "(solve_lrec B B' R) \<turnstile> w @ p2 \<Rightarrow>* q2" using 1 q2_tms n_Suc derivem
        by auto
      then have "(solve_lrec B B' R) \<turnstile> Nt C # p2 \<Rightarrow>* q2" using rule_in_solve_lrec by (auto simp add: derives_Cons_rule)
      then show ?thesis
        by (simp add: P P1 derives_prepend)
    qed
  qed
qed


lemma "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> Lang (solve_lrec B B' R) A \<subseteq> Lang R A"
  sorry

lemma "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> Lang (solve_lrec B B' R) A \<supseteq> Lang R A"
  sorry

find_theorems name: "exp_hd.induct"

text \<open> Section exp_hd Language equivalence \<close>


text \<open> every righthand side of an "exp_hd R" production is derivable by R \<close>
lemma exp_hd_is_deriveable: "(A, w) \<in> exp_hd B As R \<Longrightarrow> R \<turnstile> [Nt A] \<Rightarrow>* w"
proof (induction B As R arbitrary: A w rule: exp_hd.induct)
  case (1 B R)
  then show ?case
    by (simp add: bu_prod derives_if_bu)
next
  case (2 B S Ss R)
  then show ?case
  proof (cases "B = A")
    case True
    then have Aw_or_ACv: "(A, w) \<in> exp_hd A Ss R \<or> (\<exists>C v. (A, Nt C # v) \<in> exp_hd A Ss R)"
      using 2 by (auto simp add: Let_def)
    then show ?thesis
    proof (cases "(A, w) \<in> exp_hd A Ss R")
      case True
      then show ?thesis using 2 True by (auto simp add: Let_def)
    next
      case False
      then have "\<exists> v wv. w = v @ wv \<and> (A, Nt S # wv) \<in> exp_hd A Ss R \<and> (S, v) \<in> exp_hd A Ss R"
        using 2 True by (auto simp add: Let_def)
      then obtain v wv where P: "w = v @ wv \<and> (A, Nt S # wv) \<in> exp_hd A Ss R \<and> (S, v) \<in> exp_hd A Ss R" by blast
      then have tr: "R \<turnstile> [Nt A] \<Rightarrow>* [Nt S] @ wv" using 2 True by simp
      have "R \<turnstile> [Nt S] \<Rightarrow>* v" using 2 True P by simp
      then show ?thesis using P tr derives_append
        by (metis rtranclp_trans)
    qed
  next
    case False
    then show ?thesis using 2 by (auto simp add: Let_def)
  qed
qed


lemma exp_hd_incl1: "Lang (exp_hd B As R) A \<subseteq> Lang R A"
proof -
  have "Ders (exp_hd B As R) A \<subseteq> Ders R A" using exp_hd_is_deriveable
    by (smt (verit, best) DersD DersI derives_simul_rules subsetI)
  then show "Lang (exp_hd B As R) A \<subseteq> Lang R A" using Ders_sub_Lang_sub
    by metis
qed

text \<open>Sentential form that derives to terminals and has a Nt in it has a derivation that starts with some rule acting on that Nt \<close>
lemma deriven_start_sent: "R \<turnstile> u @ Nt V # w \<Rightarrow>(Suc n) map Tm x \<Longrightarrow> \<exists>v. (V, v) \<in> R \<and> R \<turnstile> u @ v @ w \<Rightarrow>(n) map Tm x"
proof -
  assume assm: "R \<turnstile> u @ Nt V # w \<Rightarrow>(Suc n) map Tm x"
  then have "\<exists>n1 n2 xu xvw. Suc n = n1 + n2 \<and> map Tm x = xu @ xvw \<and> R \<turnstile> u \<Rightarrow>(n1) xu \<and> R \<turnstile> Nt V # w \<Rightarrow>(n2) xvw" by (simp add: deriven_append_decomp)
  then obtain n1 n2 xu xvw where P1: "Suc n = n1 + n2 \<and> map Tm x = xu @ xvw \<and> R \<turnstile> u \<Rightarrow>(n1) xu \<and> R \<turnstile> Nt V # w \<Rightarrow>(n2) xvw" by blast
  then have t: "\<nexists>t. xvw = Nt V # t"
    by (metis append_eq_map_conv map_eq_Cons_D sym.distinct(1))
  then have "(\<exists>n3 n4 v xv xw. n2 = Suc (n3 + n4) \<and> xvw = xv @ xw \<and> (V,v) \<in> R \<and> R \<turnstile> v \<Rightarrow>(n3) xv \<and> R \<turnstile> w \<Rightarrow>(n4) xw)" 
    using P1 t by (simp add: deriven_Cons_decomp)
  then obtain n3 n4 v xv xw where P2: "n2 = Suc (n3 + n4) \<and> xvw = xv @ xw \<and> (V,v) \<in> R \<and> R \<turnstile> v \<Rightarrow>(n3) xv \<and> R \<turnstile> w \<Rightarrow>(n4) xw" by blast
  then have "R \<turnstile> v @ w \<Rightarrow>(n3 + n4) xvw" using P2
    using deriven_append_decomp diff_Suc_1 by blast
  then have "R \<turnstile> u @ v @ w \<Rightarrow>(n1 + n3 + n4) map Tm x" using P1 P2 deriven_append_decomp
    using ab_semigroup_add_class.add_ac(1) by blast
  then have "R \<turnstile> u @ v @ w \<Rightarrow>(n) map Tm x" using P1 P2
    by (simp add: add.assoc)
  then show ?thesis using P2 by blast
qed

find_theorems name: "deriven_start"

text \<open>This lemma expects a Set of quadruples (A, a1, B, a2). 
  Each quadruple encodes a specific terminal in a specific rule (A, a1 @ Nt B # a2) (here Nt B)
   which should be expanded, by replacing the Nt with every rule for that Nt and then removing the original rule.
  This expansion contains the original productions Language\<close>
lemma exp_includes_Lang: "\<forall>x \<in> S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> R
  \<Longrightarrow> Lang R A \<subseteq> Lang (R - {x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> S } \<union> {x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> S \<and> (B,v) \<in> R}) A"
proof
  fix x
  assume x_Lang: "x \<in> Lang R A" and S_props: "\<forall>x \<in> S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> R"
  let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> S }"
  let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> S \<and> (B,v) \<in> R}"
  let ?subst = "R - ?S' \<union> ?E"
  have S'_sub: "?S' \<subseteq> R" using S_props by auto
  have "(N, ts) \<in> ?S' \<Longrightarrow> \<exists>B. B \<in> nts_syms ts" for N ts by fastforce
  then have terminal_prods_stay: "(N, ts) \<in> R \<Longrightarrow> nts_syms ts = {} \<Longrightarrow> (N, ts) \<in> ?subst" for N ts
    by auto

  have "R \<turnstile> p \<Rightarrow>(n) map Tm x \<Longrightarrow> ?subst \<turnstile> p \<Rightarrow>* map Tm x" for p n
  proof (induction n arbitrary: p x rule: nat_less_induct)
    case (1 n)
    then show ?case
    proof (cases "\<exists>pt. p = map Tm pt")
      case True
      then obtain pt where "p = map Tm pt" by blast
      then show ?thesis using "1.prems" deriven_from_TmsD derives_from_Tms_iff by blast
    next
      case False
      then have "\<exists>uu V ww. p = uu @ Nt V # ww"
        by (smt (verit, best) "1.prems" deriven_Suc_decomp_left relpowp_E)
      then obtain uu V ww where p_eq: "p = uu @ Nt V # ww" by blast
      then have "\<not> R \<turnstile> p \<Rightarrow>(0) map Tm x"
        using False by auto
      then have "\<exists>m. n = Suc m"
        using "1.prems" old.nat.exhaust by blast
      then obtain m where n_Suc: "n = Suc m" by blast
      then have "\<exists>v. (V, v) \<in> R \<and> R \<turnstile> uu @ v @ ww \<Rightarrow>(m) map Tm x" using 1 p_eq by (auto simp add: deriven_start_sent)
      then obtain v where start_deriven: "(V, v) \<in> R \<and> R \<turnstile> uu @ v @ ww \<Rightarrow>(m) map Tm x" by blast
      then show ?thesis
      proof (cases "(V, v) \<in> ?S'")
        case True
        then have "\<exists>a1 B a2. v = a1 @ Nt B # a2 \<and> (V, a1, B, a2) \<in> S" by blast
        then obtain a1 B a2 where v_eq: "v = a1 @ Nt B # a2 \<and> (V, a1, B, a2) \<in> S" by blast
        then have m_deriven: "R \<turnstile> (uu @ a1) @ Nt B # (a2 @ ww) \<Rightarrow>(m) map Tm x" using start_deriven by auto
        then have "\<not> R \<turnstile> (uu @ a1) @ Nt B # (a2 @ ww) \<Rightarrow>(0) map Tm x"
          by (metis (mono_tags, lifting) append.left_neutral append_Cons derive.intros insertI1 not_derive_from_Tms
              relpowp.simps(1))
        then have "\<exists>k. m = Suc k"
          using m_deriven "1.prems" old.nat.exhaust by blast
        then obtain k where m_Suc: "m = Suc k" by blast
        then have "\<exists>b. (B, b) \<in> R \<and> R \<turnstile> (uu @ a1) @ b @ (a2 @ ww) \<Rightarrow>(k) map Tm x"
          using m_deriven deriven_start_sent[where ?u = "uu@a1" and ?w = "a2 @ ww"] by (auto simp add: m_Suc)
        then obtain b where second_deriven: "(B, b) \<in> R \<and> R \<turnstile> (uu @ a1) @ b @ (a2 @ ww) \<Rightarrow>(k) map Tm x" by blast
        then have expd_rule_subst: "(V, a1 @ b @ a2) \<in> ?subst" using v_eq by auto
        have "k < n" using n_Suc m_Suc by auto
        then have subst_derives: "?subst \<turnstile> uu @ a1 @ b @ a2 @ ww \<Rightarrow>* map Tm x" using 1 second_deriven by (auto)
        have "?subst \<turnstile> [Nt V] \<Rightarrow>* a1 @ b @ a2" using expd_rule_subst
          by (meson derive_singleton r_into_rtranclp)
        then have "?subst \<turnstile> [Nt V] @ ww \<Rightarrow>* a1 @ b @ a2 @ ww" using derives_append[of ?subst "[Nt V]" "a1 @ b @ a2"] by simp
        then have "?subst \<turnstile> Nt V # ww \<Rightarrow>* a1 @ b @ a2 @ ww"
          by simp
        then have "?subst \<turnstile> uu @ Nt V # ww \<Rightarrow>* uu @ a1 @ b @ a2 @ ww" using derives_prepend[of ?subst "[Nt V] @ ww"] by simp
        then show ?thesis using subst_derives by (auto simp add: p_eq v_eq)
      next
        case False
        then have Vv_subst: "(V,v) \<in> ?subst" using S_props start_deriven by auto
        then have "?subst \<turnstile> uu @ v @ ww \<Rightarrow>* map Tm x" using 1 start_deriven n_Suc by auto
        then show ?thesis using Vv_subst derives_append_decomp
          by (metis (no_types, lifting) derives_Cons_rule p_eq)
      qed
    qed
  qed

  then have "R \<turnstile> p \<Rightarrow>* map Tm x \<Longrightarrow> ?subst \<turnstile> p \<Rightarrow>* map Tm x" for p
    by (meson rtranclp_power)

  then show "x \<in> Lang ?subst A" using x_Lang by (auto simp add: Lang_def)
qed


text \<open> this inclusion uses exp_includes_Lang lemma
  so it constructs sets that encode the expansions done by exp_hd in a form that is needed for the exp_includes_Lang lemma
  Then only equivalence of the encoded set with the "exp_hd R" set has to be proven (by fastforce)\<close>
lemma exp_hd_incl2: "Lang (exp_hd B As R) A \<supseteq> Lang R A"
proof (induction B As R rule: exp_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 C H Ss R)
  let ?R' = "exp_hd C Ss R"
  let ?X = "{(Al,Bw) \<in> ?R'. Al=C \<and> (\<exists>w. Bw = Nt H # w)}"
  let ?Y = "{(C,v@w) |v w. \<exists>B. (C,Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"
  have "exp_hd C (H # Ss) R = ?R' - ?X \<union> ?Y" by (simp add: Let_def)

  let ?S = "{x. \<exists>A w. x = (A, [], H, w) \<and> (A, Nt H # w) \<in> ?X}"
  let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> ?S}"
  let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> ?S \<and> (B,v) \<in> ?R'}"

  have S'_eq_X: "?S' = ?X" by fastforce
  have E_eq_Y: "?E = ?Y" by fastforce

  have "\<forall>x \<in> ?S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> ?R'" by fastforce
  then have Lang_sub: "Lang ?R' A \<subseteq> Lang (?R' - ?S' \<union> ?E) A"
    using exp_includes_Lang[of ?S] by auto

  have "Lang R A \<subseteq> Lang ?R' A" using 2 by simp
  also have "... \<subseteq> Lang (?R' - ?S' \<union> ?E) A" using Lang_sub by simp
  also have "... \<subseteq> Lang (?R' - ?X \<union> ?Y) A" using S'_eq_X E_eq_Y by simp
  finally show ?case by (simp add: Let_def)
qed

lemma "Lang R A = Lang (exp_hd B As R) A"
  using exp_hd_incl1[of B As R A] exp_hd_incl2[of R A B As] by auto


text \<open> Section Lang solve_tri equivalence \<close>

lemma "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As')\<rbrakk> \<Longrightarrow> Lang (solve_tri As As' R) A \<subseteq> Lang R A"
  sorry

lemma "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As')\<rbrakk> \<Longrightarrow> Lang (solve_tri As As' R) A \<supseteq> Lang R A"
  sorry


lemma "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As')\<rbrakk> \<Longrightarrow> Lang (solve_tri As As' R) A = Lang R A"
  sorry
  

(* nitpick  no counterexample found - not clear if that means much here *)

text \<open> Unused lemmas \<close>

text \<open> proves that a expanding a single production keeps the language
    not very usefull for proving exp_hd, as it expands multiple productions at the same time
    and repeated use of this lemma does not work for this usecase, since the Productions change with every expansion
    (now proven with exp_includes_Lang lemma, was proven simmilarly to that lemma first)  \<close>
lemma single_exp_keeps_Lang: "(A, v @ Nt B # w) \<in> R \<Longrightarrow> Lang R S \<subseteq> Lang (R - {(A, v @ Nt B # w)} \<union> {x. \<exists>b. x = (A, v @ b @ w) \<and> (B, b) \<in> R}) S"
proof-
  assume assm: "(A, v @ Nt B # w) \<in> R"

  let ?S = "{(A, v, B, w)}"
  let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> ?S}"
  let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> ?S \<and> (B,v) \<in> R}"

  have 1: "?S' = {(A, v @ Nt B # w)}" by fastforce
  have 2: "?E = {x. \<exists>b. x = (A, v @ b @ w) \<and> (B, b) \<in> R}" by fastforce

  have "\<forall>x \<in> ?S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> R" using assm by auto
  then have "Lang R S \<subseteq> Lang (R - ?S' \<union> ?E) S" using exp_includes_Lang[of ?S] by auto
  then show "Lang R S \<subseteq> Lang (R - {(A, v @ Nt B # w)} \<union> {x. \<exists>b. x = (A, v @ b @ w) \<and> (B, b) \<in> R}) S" using 1 2 by simp
qed

text \<open> proves that doing every expansion of a set of rules the original Language is included
    this is overly restricitve of a statement and is mostly useless \<close>
lemma Lang_includes_exp: "S \<subseteq> R \<Longrightarrow> Lang R A \<supseteq> Lang (R - S \<union> {(A,a1@v@a2) |A v a1 a2. \<exists>B. (A, a1 @ Nt B # a2) \<in> S \<and> (B,v) \<in> R}) A"
proof -
  let ?subst = "(R - S \<union> {(A,a1@v@a2) |A v a1 a2. \<exists>B. (A, a1 @ Nt B # a2) \<in> S \<and> (B,v) \<in> R})"
  assume S_sub_R: "S \<subseteq> R"
  have "(V, v) \<in> ?subst \<Longrightarrow> R \<turnstile> [Nt V] \<Rightarrow>* v" for V v
  proof-
    assume assm: "(V, v) \<in> ?subst"
    show ?thesis
    proof (cases "(V,v) \<in> R - S")
      case True
      then have "(V,v) \<in> R" by auto
      then show ?thesis
        by (simp add: bu_prod derives_if_bu)
    next
      case False
      then have "(V,v) \<in> {(A,a1@v@a2) |A v a1 a2. \<exists>B. (A, a1 @ Nt B # a2) \<in> S \<and> (B,v) \<in> R}" using assm by auto
      then have "\<exists>A a1 vv a2 B. V = A \<and> v = a1 @ vv @ a2 \<and> (V, a1 @ Nt B # a2) \<in> S \<and> (B, vv) \<in> R" by blast
      then obtain A a1 vv a2 B where P: "V = A \<and> v = a1 @ vv @ a2 \<and> (V, a1 @ Nt B # a2) \<in> S \<and> (B, vv) \<in> R" by blast
      then have "(V, a1 @ Nt B # a2) \<in> R \<and> (B, vv) \<in> R" using S_sub_R by auto
      then have "R \<turnstile> [Nt V] \<Rightarrow>* a1 @ vv @ a2"
        by (meson Nitpick.rtranclp_unfold bu_prod derives_bu_iff derives_rule)
      then show ?thesis using P by simp
    qed
  qed
  then have "?subst \<turnstile> p \<Rightarrow>* q \<Longrightarrow> R \<turnstile> p \<Rightarrow>* q" for p q
    by (meson derives_simul_rules)
  then have "Ders ?subst A \<subseteq> Ders R A" by (auto simp add: Ders_def)
  then show "Lang ?subst A \<subseteq> Lang R A"  by (auto simp add: Ders_sub_Lang_sub)
qed

text \<open> This lemma shows that a derivation from a single non-terminal must have a last step as well, where a non-terminal is replaced by only terminals
  unsure if this be will usefull anywhere\<close>
lemma last_derive_is_term: "(derive R^^(Suc n)) [Nt S] (map Tm x) \<Longrightarrow> \<exists>x1 N x2 t. R \<turnstile> [Nt S] \<Rightarrow>(Suc n) (map Tm x) \<and> (map Tm x) = x1 @ t @ x2 \<and> R \<turnstile> [Nt S] \<Rightarrow>(n) (x1@[Nt N]@x2) \<and> (N, t) \<in> R \<and> nts_syms t = {}" for S n
  proof -
    assume assm: "(derive R^^(Suc n)) [Nt S] (map Tm x)"
    then have "(deriver R^^(Suc n)) [Nt S] (map Tm x)" by (auto simp flip: derivern_iff_deriven)
    then have "\<exists>ww. (deriver R^^n) [Nt S] ww \<and> deriver R ww (map Tm x)"
      by (meson relpowp_Suc_E)
    then obtain ww where P1: "(deriver R^^n) [Nt S] ww \<and> deriver R ww (map Tm x)" by blast
    then have "deriver R ww (map Tm x)" by blast
    then have "\<exists>(N, t) \<in> R. \<exists>u1 u2. ww = u1 @ Nt N # (map Tm u2) \<and> (map Tm x) = u1 @ t @ map Tm u2" using deriver_iff
      by blast
    then obtain N t u1 u2 where P2: "ww = u1 @ Nt N # (map Tm u2) \<and> (map Tm x) = u1 @ t @ map Tm u2 \<and> (N, t) \<in> R" by blast
    then have "\<exists>t1. u1 = map Tm t1"
      using map_eq_append_conv by blast
    then obtain t1 where P3: "u1 = map Tm t1" by blast
    have "\<exists>tt. t = map Tm tt" using P2 map_eq_append_conv
      by metis
    then have "nts_syms t = {}"
      by auto
    then have "\<exists>N x1 x2 t. (deriver R^^n) [Nt S] ((map Tm x1)@Nt N#(map Tm x2)) \<and> (map Tm x) = (map Tm x1)@t @ (map Tm x2) \<and> (N, t) \<in> R \<and> nts_syms t = {}" using P1 P2 P3 by auto
    then show ?thesis using derivern_iff_deriven
      using assm derivern_imp_deriven by fastforce
  qed

text \<open> Broken Lemmas or not looked at \<close>

lemma Eps_free_exp_hd_simp[simp]: "Eps_free (exp_hd A As R) = Eps_free R"
by(auto simp: Eps_free_def) sorry

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
by(auto simp: dep_on_def Let_def)


lemma dep_on_solve_tri: "\<lbrakk> length As = length As'; A \<notin> set As \<union> set As' \<rbrakk>
  \<Longrightarrow> dep_on (solve_tri As As' R) A = dep_on R A"
proof(induction As As' arbitrary: R rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons A As A' As')
  then show ?case by (simp add: dep_on_solve_lrec2 dep_on_exp_hd_simp2)
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
lemma "\<lbrakk> Eps_free (set R); length As \<le> length As'; distinct(As @ As'); Nts (set R) \<subseteq> set As \<rbrakk>
 \<Longrightarrow> triangular_list As (solve_tri_list As As' R)"
quickcheck
oops

value "dep_on_list [(1,[T 5]::(int,int)sym list)] 1"
value "hdNts_list[(1,[T 5]::(int,int)sym list)]"
value "solve_tri_list [1] [2] [(1,[N 1, N 1]::(int,int)sym list)]"

lemma hdNts_exp_hd: "Eps_free R \<Longrightarrow> hdNts (exp_hd A As R) \<subseteq> hdNts R"
by(fastforce simp: hdNts_def dest: Eps_freeE_Cons)

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
by(auto simp: Eps_free_def split: prod.splits)

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

fun rt :: "('n,'t)syms \<Rightarrow> bool" where
"rt [] = True" |
"rt (Tm _ # _) = True" |
"rt _ = False"

fun rtp :: "('n,'t)prod \<Rightarrow> bool" where
"rtp (_, w) = rt w"

definition rtps :: "('n,'t)Prods \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> ps. rtp p)"

fun lnts :: "('n \<times> ('n, 't) syms) list \<Rightarrow> 'n list" where
"lnts [] = []" |
"lnts ((_,[]) # ps) = lnts ps" |
"lnts ((_, Tm a # w) # ps) = lnts ps" |
"lnts ((_, Nt B # w) # ps) = List.insert B (lnts ps)"

definition rtps2 :: "'n set \<Rightarrow> ('n,'t)prods \<Rightarrow> bool" where
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