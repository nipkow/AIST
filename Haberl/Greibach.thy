theory Greibach
imports "Context_Free_Grammar.Context_Free_Grammar"
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

abbreviation "lrec_prods R A S \<equiv> {(A',Bw) \<in> R. A'=A \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> S)}"

text \<open>"Expand head: Replace all rules \<open>A \<rightarrow> B w\<close> where \<open>B \<in> Ss\<close> (\<open>Ss\<close> = solved Nts)
by \<open>A \<rightarrow> v w\<close> where \<open>B \<rightarrow> v\<close>. Starting from the end of \<open>Ss\<close>\<close>
fun exp_hd :: "'n \<Rightarrow> 'n list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"exp_hd A [] R = R" |
"exp_hd A (S#Ss) R =
 (let R' = exp_hd A Ss R;
      X = lrec_prods R' A {S};
      Y = {(A,v@w) |v w. \<exists>B. (A,Nt B # w) \<in> X \<and> (B,v) \<in> R'}
  in R' - X \<union> Y)"

text \<open>Code:\<close>

lemma Rhss_code[code]: "Rhss P A = snd ` {Aw \<in> P. fst Aw = A}"
by(auto simp add: Rhss_def image_iff)

declare exp_hd.simps(1)[code]
lemma exp_hd_Cons_code[code]: "exp_hd A (S#Ss) R =
 (let R' = exp_hd A Ss R;
      X = {w \<in> Rhss R' A. w \<noteq> [] \<and> hd w = Nt S};
      Y = (\<Union>(B,v) \<in> R'. \<Union>w \<in> X. if hd w \<noteq> Nt B then {} else {(A,v @ tl w)})
  in R' - ({A} \<times> X) \<union> Y)"
by(simp add: Rhss_def Let_def neq_Nil_conv Ball_def hd_append split: if_splits, safe, force+)

text \<open>Remove left-recursive rules\<close>
definition rm_lrec ::  "'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"rm_lrec A R = R - {(A,Nt A # v)|v. True}"

lemma rm_lrec_code[code]:
  "rm_lrec A R = {Aw \<in> R. let (A',w) = Aw in A' \<noteq> A \<or> w = [] \<or> hd w \<noteq> Nt A}"
by(auto simp add: rm_lrec_def neq_Nil_conv)

fun hd_not_NA where
"hd_not_NA A w = (\<not>(\<exists>u. w = Nt A # u))"

text \<open>Conversion from left-recursion to right-recursion:
Split \<open>A\<close>-rules into \<open>A \<rightarrow> u\<close> and \<open>A \<rightarrow> A v\<close>.
Keep \<open>A \<rightarrow> u\<close> but replace \<open>A \<rightarrow> A v\<close> by \<open>A \<rightarrow> u A'\<close>, \<open>A' \<rightarrow> v\<close>, \<open>A' \<rightarrow> v A'\<close>:\<close>
definition rrec_of_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"rrec_of_lrec A A' R =
  (let V = {v. (A,Nt A # v) \<in> R \<and> v \<noteq> []};
       U = {u. (A,u) \<in> R \<and> \<not>(\<exists>v. u = Nt A # v) }
  in (\<Union>u\<in>U. {(A,u)}) \<union> (\<Union>u\<in>U. {(A,u@[Nt A'])}) \<union> (\<Union>v\<in>V. {(A',v)}) \<union> (\<Union>v\<in>V. {(A',v @ [Nt A'])}))"

lemma rrec_of_lrec_code[code]: "rrec_of_lrec A A' R =
  (let RA = Rhss R A;
       V = (\<Union> w \<in> RA. if w \<noteq> [] \<and> hd w = Nt A \<and> tl w \<noteq> [] then {tl w} else {});
       U = {u \<in> RA. u = [] \<or> hd u \<noteq> Nt A }
  in ({A} \<times> U) \<union> (\<Union>u\<in>U. {(A,u@[Nt A'])}) \<union> ({A'} \<times> V) \<union> (\<Union>v\<in>V. {(A',v @ [Nt A'])}))"
by(auto simp add: rrec_of_lrec_def Let_def Rhss_def neq_Nil_conv)

text \<open>Dealing with ("solving") Nt A. The new Nt A' is also given as a parameter.\<close>
definition solve_lrec ::  "'n \<Rightarrow> 'n \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"solve_lrec A A' R = rm_lrec A R \<union> rrec_of_lrec A A' R"

text \<open>Put \<open>R\<close> into triangular form wrt \<open>As\<close> (using the new Nts \<open>As'\<close>).
That means that \<open>As\<close> are the Nts that still have to be solved.
In each step \<open>A#As\<close>, first the remaining \<open>As\<close> are solved, then \<open>A\<close> is solved.
This should mean that in the result of the outermost \<open>exp_hd A As\<close>, \<open>A\<close> only depends on \<open>A\<close>,
i.e. the \<open>A\<close> rules in the result of \<open>solve_lrec A A'\<close> are already in GNF. More precisely:
the result should be in triangular form.\<close>
fun solve_tri :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) Prods \<Rightarrow> ('a, 'b) Prods" where
"solve_tri [] _ R = R" |
"solve_tri (A#As) (A'#As') R = solve_lrec A A' (exp_hd A As (solve_tri As As' R))"

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

text \<open>exp_hd preserves epsilon free-ness\<close>
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


text \<open>lemmas about Nts in the grammar\<close>

lemma Nts_set_dif_subset: "Nts (G - H) \<subseteq> Nts G"
  by (auto simp add: Nts_def)

lemma dep_on_subs_Nts: "dep_on R A \<subseteq> Nts R"
  by (auto simp add: Nts_def dep_on_def)

text \<open> exp_hd does not add any new Nts \<close>
lemma Nts_exp_hd_sub: "Nts (exp_hd A As R) \<subseteq> Nts R"
proof (induction A As R rule: exp_hd.induct)
  case (1 A R)
  then show ?case by simp
next
  case (2 A S Ss R)
  let ?R' = "exp_hd A Ss R"
  let ?X = "{(Al, Bw). (Al, Bw) \<in> ?R' \<and> Al = A \<and> (\<exists>w. Bw = Nt S # w)}"
  let ?Y = "{(A, v @ w) |v w. (A, Nt S # w) \<in> ?R' \<and> (S, v) \<in> ?R'}"

  have lhs_sub: "Lhss ?Y \<subseteq> Lhss ?R'" by (auto simp add: Lhss_def)

  have "B \<notin> Rhs_Nts ?R' \<longrightarrow> B \<notin> Rhs_Nts ?Y" for B by (fastforce simp add: Rhs_Nts_def split: prod.splits)
  then have "B \<in> Rhs_Nts ?Y \<longrightarrow> B \<in> Rhs_Nts ?R'" for B by blast
  then have rhs_sub: "Rhs_Nts ?Y \<subseteq> Rhs_Nts ?R'" by auto

  have "Nts ?Y \<subseteq> Nts ?R'" using lhs_sub rhs_sub by (auto simp add: Nts_Lhss_Rhs_Nts)
  then have "Nts ?Y \<subseteq> Nts R" using 2 by auto
  then show ?case using Nts_set_dif_subset[of ?R' ?X] 2 by (auto simp add: Let_def Nts_Un)
qed
  
text \<open> Nts of solve_lrec are a subset of Nts R and the newly added one \<close>
lemma Nts_solve_lrec_sub: "Nts (solve_lrec A A' R) \<subseteq> Nts R \<union> {A'}"
proof-
  have 1: "Nts (rm_lrec A R) \<subseteq> Nts R" using Nts_set_dif_subset[of R] by (auto simp add: rm_lrec_def)

  have 2: "Lhss (rrec_of_lrec A A' R) \<subseteq> Lhss R \<union> {A'}" by (auto simp add: rrec_of_lrec_def Let_def Lhss_def)
  have 3: "Rhs_Nts (rrec_of_lrec A A' R) \<subseteq> Rhs_Nts R \<union> {A'}" by (auto simp add: rrec_of_lrec_def Let_def Rhs_Nts_def)

  have "Nts (rrec_of_lrec A A' R) \<subseteq> Nts R \<union> {A'}" using 2 3 by (auto simp add: Nts_Lhss_Rhs_Nts)
  then show ?thesis using 1 by (auto simp add: solve_lrec_def Nts_Un)
qed

text \<open> Nts of solve_tri are a subset of Nts R and newly added ones \<close>
lemma Nts_solve_tri_sub: "length As \<le> length As' \<Longrightarrow> Nts (solve_tri As As' R) \<subseteq> Nts R \<union> set As'"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 A As A' As' R)
  have "Nts (solve_tri (A # As) (A' # As') R) = Nts (solve_lrec A A' (exp_hd A As (solve_tri As As' R)))" by simp
  also have "... \<subseteq> Nts (exp_hd A As (solve_tri As As' R)) \<union> {A'}"
    using Nts_solve_lrec_sub[of A A' "exp_hd A As (solve_tri As As' R)"] by simp
  also have "... \<subseteq> Nts (solve_tri As As' R) \<union> {A'}" using Nts_exp_hd_sub[of A As "solve_tri As As' R"] by auto
  finally show ?case using 2 by auto
next
  case (3 v va c)
  then show ?case by simp
qed

text \<open> lemmas about rule inclusions in solve_lrec \<close>

lemma solve_lrec_rule_simp1: "A \<noteq> B \<Longrightarrow> A \<noteq> B' \<Longrightarrow> (A, w) \<in> solve_lrec B B' R \<longleftrightarrow> (A, w) \<in> R"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def)

lemma solve_lrec_rule_simp2: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> w \<noteq> [] \<Longrightarrow> (A', w @ [Nt A']) \<in> solve_lrec A A' R \<longleftrightarrow> (A, Nt A # w) \<in> R"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def)  

lemma solve_lrec_rule_simp3: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> w \<noteq> [] \<Longrightarrow> last w \<noteq> Nt A' \<Longrightarrow> (A, w) \<in> solve_lrec A A' R \<Longrightarrow> (A, w) \<in> R"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def)

lemma solve_lrec_rule_simp4: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> Eps_free R \<Longrightarrow> (A, [Nt A']) \<notin> solve_lrec A A' R"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def Eps_free_def)

lemma solve_lrec_rule_simp5: "A' \<notin> Nts R \<Longrightarrow> (A, w @ [Nt A']) \<in> solve_lrec A A' R \<Longrightarrow> (A, w) \<in> R"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def)

lemma solve_lrec_rule_simp6: "A' \<notin> Nts R \<Longrightarrow> (A',w @ [Nt A']) \<in> (solve_lrec A A' R) \<Longrightarrow> A' \<notin> nts_syms w"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def nts_syms_def)

lemma solve_lrec_rule_simp7: "A' \<notin> Nts R \<Longrightarrow> last w \<noteq> Nt A'  \<Longrightarrow> (A',w) \<in> (solve_lrec A A' R) \<Longrightarrow> A' \<notin> nts_syms w"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def nts_syms_def)

lemma solve_lrec_rule_simp8: "A' \<noteq> A \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> (A', Nt A' # w) \<notin> (solve_lrec A A' R)"
proof (rule ccontr)
  assume assms: "A' \<noteq> A" "A' \<notin> Nts R" "\<not>(A', Nt A' # w) \<notin> (solve_lrec A A' R)"
  then have "(A', Nt A' # w) \<in> (solve_lrec A A' R)" by simp
  have "(A, Nt A # x) \<in> R \<and> x \<noteq> [] \<and> Nt A' # w = x @ [Nt A'] \<longrightarrow> False" for x
  proof
    fix x
    assume assm: "(A, Nt A # x) \<in> R \<and> x \<noteq> [] \<and> Nt A' # w = x @ [Nt A']"
    then have "hd x = Nt A'"
      by (metis hd_append list.sel(1))
    then have "Nt A' \<in> set x" using assm hd_in_set by fastforce
    then have "A' \<in> nts_syms (Nt A # x)"  by (auto simp add: nts_syms_def)
    then have "A' \<in> Nts R" using assm solve_lrec_rule_simp6 by (fastforce simp add: Nts_def split: prod.split)
    then show "False" using assms by blast
  qed
  then show "False" using assms by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def nts_syms_def split: prod.splits)
qed

lemma solve_lrec_rule_simp9: "A' \<notin> Nts R \<Longrightarrow> B \<noteq> A' \<Longrightarrow> B \<noteq> A \<Longrightarrow> (B, Nt A' # w) \<notin> (solve_lrec A A' R)"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def nts_syms_def split: prod.splits)

text \<open>Section Eps_free preservation \<close>

lemma Eps_free_solve_lrec: "Eps_free R \<Longrightarrow> Eps_free (solve_lrec A A' R)"
  by (auto simp add: solve_lrec_def rrec_of_lrec_def Eps_free_def Let_def rm_lrec_def)

lemma Eps_free_solve_tri: "Eps_free R \<Longrightarrow> length As \<le> length As' \<Longrightarrow> Eps_free (solve_tri As As' R)"
  by (induction As As' R rule: solve_tri.induct) (auto simp add: Eps_free_solve_lrec Eps_free_exp_hd)

lemma dep_on_exp_hd_simp2: "B \<noteq> A \<Longrightarrow> dep_on (exp_hd A As R) B = dep_on R B"
  by (auto simp add: dep_on_def rm_lrec_def rrec_of_lrec_def Let_def exp_hd_preserves_neq)

text  \<open> exp_hd keeps triangular, if it does not expand a Nt considered in triangular\<close>
lemma triangular_exp_hd: "\<lbrakk>A \<notin> set As; triangular As R\<rbrakk> \<Longrightarrow> triangular As (exp_hd A Bs R)"
  by (induction As) (auto simp add: dep_on_exp_hd_simp2)
(*proof(induction As)
  case Nil
  then show ?case by simp
next
  case (Cons a As)
  have "triangular (a # As) (exp_hd A Bs R) = (dep_on (exp_hd A Bs R) a \<inter> ({a} \<union> set As) = {} \<and> triangular As (exp_hd A Bs R))" by simp
  also have "... = (dep_on (exp_hd A Bs R) a \<inter> ({a} \<union> set As) = {})" using Cons by simp
  also have "... = (dep_on R a \<inter> ({a} \<union> set As) = {})" using dep_on_exp_hd_simp2 Cons
    by (metis list.set_intros(1))
  then show ?case using Cons by auto
qed*)


lemma dep_on_solve_lrec_simp2: "A \<noteq> B \<Longrightarrow> A' \<noteq> B \<Longrightarrow> dep_on (solve_lrec A A' R) B = dep_on R B"
  by (auto simp add: solve_lrec_def dep_on_def rm_lrec_def rrec_of_lrec_def Let_def)

text \<open> solving a Nt not considered by triangular preserves the triangular property \<close>
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

text \<open> Couple of small lemmas about dep_on and the solving of left-recursion\<close>
lemma rm_lrec_rem_own_dep: "A \<notin> dep_on (rm_lrec A R) A"
  by (auto simp add: dep_on_def rm_lrec_def)

lemma rrec_of_lrec_has_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (rrec_of_lrec A A' R) A"
  apply (auto simp add: dep_on_def rrec_of_lrec_def Let_def)
  by (metis append_eq_Cons_conv list.inject sym.inject(1))

lemma solve_lrec_no_own_dep: "A \<noteq> A' \<Longrightarrow> A \<notin> dep_on (solve_lrec A A' R) A"
  by (auto simp add: dep_on_Un solve_lrec_def rm_lrec_rem_own_dep rrec_of_lrec_has_no_own_dep)

lemma solve_lrec_no_new_own_dep: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> A' \<notin> dep_on (solve_lrec A A' R) A'"
  by (auto simp add: dep_on_def solve_lrec_rule_simp8)  
  
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


lemma dep_on_solve_tri_simp: "B \<notin> set As \<Longrightarrow> B \<notin> set As' \<Longrightarrow> length As \<le> length As' \<Longrightarrow> dep_on (solve_tri As As' R) B = dep_on R B"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 A As A' As' R)
  have "dep_on (solve_tri (A # As) (A' # As') R) B = dep_on (exp_hd A As (solve_tri As As' R)) B" 
    using 2 by (auto simp add: dep_on_solve_lrec_simp2)
  then show ?case using 2 by (auto simp add: dep_on_exp_hd_simp2)
next
  case (3 v va c)
  then show ?case by simp
qed

text \<open> induction step for showing that solve_tri removes dependencies of previously solved Nts\<close>
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

text \<open> solve_tri brings an epsilon free grammar into triangular form\<close>
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



text \<open> Section Language equivalence \<close>


text \<open> Subset Relation of all Derivations implies a Subset Relation of the Languages \<close>
lemma Ders_sub_Lang_sub: "Ders R A \<subseteq> Ders R' A \<Longrightarrow> Lang R A \<subseteq> Lang R' A"
  by (auto simp add: Lang_def Ders_def)


text \<open> This function removes all productions of the form \<open>A \<longrightarrow> A\<close> \<close>
definition rem_self_loops :: "('n,'t) Prods \<Rightarrow> ('n,'t) Prods" where
  "rem_self_loops P = P - {x. (\<exists>A. x = (A, [Nt A]) \<and> x \<in> P)}"

text \<open> if there exists a derivation from \<open>u\<close> to \<open>v\<close> then there exists one which does not use productions of the form \<open>A \<rightarrow> A\<close> \<close>
lemma rem_self_loops_derivels: "P \<turnstile> u \<Rightarrow>l(n) v \<Longrightarrow> (rem_self_loops P) \<turnstile> u \<Rightarrow>l* v"
proof(induction n arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "\<exists>w. P \<turnstile> u \<Rightarrow>l w \<and> P \<turnstile> w \<Rightarrow>l(n) v"
    by (simp add: relpowp_Suc_D2)
  then obtain w where W: "P \<turnstile> u \<Rightarrow>l w \<and> P \<turnstile> w \<Rightarrow>l(n) v" by blast
  then have "\<exists> (A,x) \<in> P. \<exists>u1 u2. u = map Tm u1 @ Nt A # u2 \<and> w = map Tm u1 @ x @ u2" by (simp add: derivel_iff)
  then obtain A x u1 u2 where prod: "u = map Tm u1 @ Nt A # u2 \<and> w = map Tm u1 @ x @ u2 \<and> (A, x) \<in> P" by blast
  then show ?case
  proof(cases "x = [Nt A]")
    case True
    then have "u = w" using prod by auto
    then show ?thesis using Suc W by auto
  next
    case False
    then have "(A, x) \<in> (rem_self_loops P)" using prod by (auto simp add: rem_self_loops_def)
    then show ?thesis using Suc W
      by (metis converse_rtranclp_into_rtranclp derivel.intros prod)
  qed
qed


text \<open> restricted to productions with one Lhs (\<open>A\<close>), and no \<open>A \<longrightarrow> A\<close> productions
      if there is a derivation from \<open>u\<close> to \<open>Nt A # v\<close> then \<open>u\<close> must start with \<open>Nt A\<close> \<close>
lemma lrec_lemma1: "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)}  \<Longrightarrow> (rem_self_loops S) \<turnstile> u \<Rightarrow>l(n) Nt A # v  \<Longrightarrow> \<exists>u'. u = Nt A # u'"
proof (rule ccontr)
  assume assms: "S = {x. \<exists>v. x = (A, v) \<and> x \<in> R}" "rem_self_loops S \<turnstile> u \<Rightarrow>l(n) Nt A # v"  "\<nexists>u'. u = Nt A # u'"
  show "False"
  proof (cases "u = []")
    case True
    then show ?thesis using assms by simp
  next
    case False
    then show ?thesis
    proof (cases "\<exists>t. hd u = Tm t")
      case True
      then show ?thesis using assms
        by (metis (no_types, lifting) False deriveln_Tm_Cons hd_Cons_tl list.inject)
    next
      case False
      then have "\<exists>B u'. u = Nt B # u' \<and> B \<noteq> A" using assms
        by (metis deriveln_from_empty list.sel(1) neq_Nil_conv sym.exhaust)
      then obtain B u' where B_not_A: "u = Nt B # u' \<and> B \<noteq> A" by blast
      then have "\<exists>w. (B, w) \<in> rem_self_loops S" using assms
        by (metis (no_types, lifting) derivels_Nt_Cons relpowp_imp_rtranclp)
      then obtain w where elem: "(B, w) \<in> rem_self_loops S" by blast
      have "(B, w) \<notin> rem_self_loops S" using B_not_A assms by (auto simp add: rem_self_loops_def)
      then show ?thesis using elem by simp
    qed
  qed
qed


text \<open> restricted to productions with one Lhs (\<open>A\<close>), and no \<open>A \<longrightarrow> A\<close> productions
      if there is a derivation from \<open>u\<close> to \<open>Nt A # v\<close> then \<open>u\<close> must start with \<open>Nt A\<close> and there 
      exists a prefix of \<open>Nt A#v\<close> s.t. a left-derivation from \<open>[Nt A]\<close> to that prefix exists  \<close>
lemma  lrec_lemma2:"S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)} \<Longrightarrow> Eps_free R \<Longrightarrow> A' \<notin> Nts R  \<Longrightarrow> (rem_self_loops S) \<turnstile> u \<Rightarrow>l(n) Nt A # v  
\<Longrightarrow> \<exists>u' v'. u = Nt A # u' \<and> v = v' @ u' \<and> (rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v'"
proof (induction n arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "\<exists>u'. u = Nt A # u'" using lrec_lemma1[of S] Suc by auto
  then obtain u' where u'_prop: "u = Nt A # u'" by blast
  then have "\<exists>w. (A,w) \<in> (rem_self_loops S) \<and> (rem_self_loops S) \<turnstile> w @ u' \<Rightarrow>l(n) Nt A # v" using Suc by (auto simp add: deriveln_Nt_Cons split: prod.split)
  then obtain w where w_prop: "(A,w) \<in> (rem_self_loops S) \<and> (rem_self_loops S) \<turnstile> w @ u' \<Rightarrow>l(n) Nt A # v" by blast
  then have "\<exists>u'' v''. w @ u' = Nt A # u'' \<and>  v = v'' @ u'' \<and> (rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v''" using Suc.IH Suc by auto
  then obtain u'' v'' where u''_prop: "w @ u' = Nt A # u'' \<and>  v = v'' @ u''" and ln_derive: "(rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # v''" by blast
  have "w \<noteq> [] \<and> w \<noteq> [Nt A]" using Suc w_prop by (auto simp add: Eps_free_Nil rem_self_loops_def split: prod.splits)
  then have "\<exists>u1. u1 \<noteq> [] \<and> w = Nt A # u1 \<and> u'' = u1 @ u'" using u''_prop
    by (metis Cons_eq_append_conv)
  then obtain u1 where u1_prop: "u1 \<noteq> [] \<and> w = Nt A # u1 \<and> u'' = u1 @ u'" by blast
  then have 1: "u = Nt A # u' \<and> v = (v'' @ u1) @ u'" using u'_prop u''_prop by auto
  
  have 2: "(rem_self_loops S) \<turnstile> [Nt A] @ u1 \<Rightarrow>l(n) Nt A # v'' @ u1" using ln_derive deriveln_append
    by fastforce
  have "(rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l [Nt A] @ u1" using w_prop u''_prop u1_prop
    by (simp add: derivel_Nt_Cons)
  then have "(rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(Suc n) Nt A # v'' @ u1" using ln_derive
    by (meson 2 relpowp_Suc_I2)
  then show ?case using 1 by blast
qed

text \<open> restricted to productions with one Lhs (\<open>A\<close>), and no \<open>A \<longrightarrow> A\<close> productions
      if there is a left-derivation from \<open>[Nt A]\<close> to \<open>Nt A # u\<close> 
      then there exists a derivation from  \<open>[Nt A']\<close> to \<open>u@[Nt A]\<close> and if \<open>u \<noteq> []\<close> also to \<open>u\<close> in solve_lrec\<close>
lemma lrec_lemma3: "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)} \<Longrightarrow> Eps_free R \<Longrightarrow> A' \<notin> Nts R  \<Longrightarrow> (rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u  
  \<Longrightarrow> (solve_lrec A A' S) \<turnstile> [Nt A'] \<Rightarrow>(n) u @ [Nt A'] \<and> (u \<noteq> [] \<longrightarrow> (solve_lrec A A' S) \<turnstile> [Nt A'] \<Rightarrow>(n) u)"
proof(induction n arbitrary: u)
  case 0
  then show ?case by (simp)
next
  case (Suc n)
  then have "\<exists>w. (A,w) \<in> (rem_self_loops S) \<and> (rem_self_loops S) \<turnstile> w \<Rightarrow>l(n) Nt A # u"
    by (auto simp add: deriveln_Nt_Cons split: prod.splits)
  then obtain w where w_prop1: "(A,w) \<in> (rem_self_loops S) \<and> (rem_self_loops S) \<turnstile> w \<Rightarrow>l(n) Nt A # u" by blast
  then have "\<exists>w' u'. w = Nt A # w' \<and> u = u' @ w' \<and> (rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u'" using lrec_lemma2[of S] Suc by auto
  then obtain w' u' where w_prop2: "w = Nt A # w' \<and> u = u' @ w'" and ln_derive: "(rem_self_loops S) \<turnstile> [Nt A] \<Rightarrow>l(n) Nt A # u'" by blast
  then have "w' \<noteq> []" using w_prop1 Suc by (auto simp add: rem_self_loops_def)
  have "(A, w) \<in> S" using Suc.prems(1) w_prop1 by (auto simp add: rem_self_loops_def)
  then have prod_in_solve_lrec: "(A', w' @ [Nt A']) \<in> solve_lrec A A' S" using w_prop2 \<open>w' \<noteq> []\<close> by (auto simp add: solve_lrec_def rrec_of_lrec_def rm_lrec_def Let_def)

  have 1: "(solve_lrec A A' S) \<turnstile> [Nt A'] \<Rightarrow>(n) u' @ [Nt A']" using Suc.IH Suc ln_derive by auto
  then have 2: "(solve_lrec A A' S) \<turnstile> [Nt A'] \<Rightarrow>(Suc n) u' @ w' @ [Nt A']" using prod_in_solve_lrec
    by (simp add: derive_prepend derive_singleton relpowp_Suc_I)

  have "(A', w') \<in> solve_lrec A A' S" using w_prop2 \<open>w' \<noteq> []\<close> \<open>(A, w) \<in> S\<close> by (auto simp add: solve_lrec_def rrec_of_lrec_def rm_lrec_def Let_def)
  then have "(solve_lrec A A' S) \<turnstile> [Nt A'] \<Rightarrow>(Suc n) u' @ w'" using 1
    by (simp add: derive_prepend derive_singleton relpowp_Suc_I)
  then show ?case using w_prop2 2 by simp
qed


text \<open> a left derivation from \<open>p\<close> (\<open>hd p = Nt A\<close>) to \<open>q\<close> (\<open>hd q \<noteq> Nt A\<close>) can be split into 
  a left-recursive part, only using left-recursive productions \<open>A \<rightarrow> Nt A # as\<close>, 
  one left derivation step consuming \<open>Nt A\<close> using some rule \<open>A \<rightarrow> B # as\<close> where \<open>B \<noteq> Nt A\<close>
  and a left-derivation comprising the rest of the derivation\<close>
lemma lrec_decomp: "S = {x. (\<exists>v. x = (A, v) \<and> x \<in> R)} \<Longrightarrow> Eps_free R \<Longrightarrow> hd p = Nt A \<Longrightarrow> hd q \<noteq> Nt A \<Longrightarrow> R \<turnstile> p \<Rightarrow>l(n) q 
  \<Longrightarrow> \<exists>u w m k. S \<turnstile> p \<Rightarrow>l(m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w \<and> hd w \<noteq> Nt A \<and> R \<turnstile> w \<Rightarrow>l(k) q \<and> n = m + k + 1"
proof (induction n arbitrary: p)
  case 0
  then have pq_not_Nil: "p \<noteq> [] \<and> q \<noteq> []" using Eps_free_derives_Nil
    by simp

  have "p = q" using 0 by auto
  then show ?case using pq_not_Nil 0 by auto
next
  case (Suc n)
  then have pq_not_Nil: "p \<noteq> [] \<and> q \<noteq> []"
    using Eps_free_deriveln_Nil by fastforce

  have ex_p': "\<exists>p'. p = Nt A # p'" using pq_not_Nil Suc
    by (metis hd_Cons_tl)
  then obtain p' where P: "p = Nt A # p'" by blast
  have "\<nexists>q'. q = Nt A # q'" using pq_not_Nil Suc
    by fastforce

  then have "\<exists>w. (A,w) \<in> R \<and> R \<turnstile> w @ p' \<Rightarrow>l(n) q" using Suc P by (auto simp add: deriveln_Nt_Cons)
  then obtain w where w_prop: "(A,w) \<in> R \<and> R \<turnstile> w @ p' \<Rightarrow>l(n) q" by blast
  then have prod_in_S: "(A, w) \<in> S" using Suc by auto

  show ?case
  proof (cases "\<exists>w'. w = Nt A # w'")
    case True
    then obtain w' where "w = Nt A # w'" by blast
    then have "\<exists>u w'' m k. S \<turnstile> w @ p' \<Rightarrow>l(m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w'' \<and> hd w'' \<noteq> Nt A \<and> R \<turnstile> w'' \<Rightarrow>l(k) q \<and> n = m + k + 1"
      using Suc.IH Suc.prems w_prop by auto
    then obtain u w'' m k where propo: "S \<turnstile> w @ p' \<Rightarrow>l(m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w'' \<and> hd w'' \<noteq> Nt A \<and> R \<turnstile> w'' \<Rightarrow>l(k) q \<and> n = m + k + 1" by blast
    then have "S \<turnstile> Nt A # p' \<Rightarrow>l(Suc m) Nt A # u" using prod_in_S P
      by (meson derivel_Nt_Cons relpowp_Suc_I2)
  
    then have "S \<turnstile> p \<Rightarrow>l(Suc m) Nt A # u \<and> S \<turnstile> Nt A # u \<Rightarrow>l w'' \<and> hd w'' \<noteq> Nt A \<and> R \<turnstile> w'' \<Rightarrow>l(k) q \<and> Suc n = Suc m + k + 1" using P propo by auto
    then show ?thesis by blast
  next
    case False
    then have "w \<noteq> [] \<and> hd w \<noteq> Nt A" using Suc w_prop
      by (metis Eps_free_Nil list.collapse)
    then have "S \<turnstile> p \<Rightarrow>l(0) Nt A # p' \<and> S \<turnstile> Nt A # p' \<Rightarrow>l w @ p' \<and> hd (w @ p') \<noteq> Nt A \<and> R \<turnstile> w @ p' \<Rightarrow>l(n) q \<and> Suc n = 0 + n + 1"
        using P w_prop prod_in_S by (auto simp add: derivel_Nt_Cons)
    then show ?thesis by blast
  qed
qed


(* should be moved to CFG.thy *)
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

(* should be moved to CFG.thy *)
text \<open> Helper lemma which could be moved to CFG.thy \<close>
lemma deriven_Tm_prepend: "R \<turnstile> map Tm t @ u \<Rightarrow>(n) v \<Longrightarrow> \<exists>v1. v = map Tm t @ v1 \<and> R \<turnstile> u \<Rightarrow>(n) v1"
  by (induction t arbitrary: v) (auto simp add: deriven_Tm_Cons)  


text \<open> something that is not a word has a first Nt \<close>
lemma non_word_has_first_Nt: "\<nexists>pt. p = map Tm pt \<Longrightarrow> \<exists>C pt p2. p = map Tm pt @ Nt C # p2"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then show ?case
  proof (cases "\<exists>C. a = Nt C")
    case True
    then obtain C where " a = Nt C" by blast
    then have "a # list = map Tm [] @ Nt C # list" using Cons by auto
    then show ?thesis by blast
  next
    case False
    then have "\<exists>t. a = Tm t"
      by (meson sym.exhaust)
    then obtain t where terminal: "a = Tm t" by blast
    have "\<nexists>pt. list = map Tm pt" using Cons
      by (metis False list.simps(9) sym.exhaust)
    then have "\<exists>C pt p2. list = map Tm pt @ Nt C # p2" using Cons by auto
    then obtain C pt p2 where "list = map Tm pt @ Nt C # p2" by blast
    then have "a # list = map Tm (t # pt) @ Nt C # p2" using terminal by auto
    then show ?thesis by blast
  qed
qed

text \<open> every derivation resulting in a word has a derivation in solve_lrec R \<close>
lemma tm_derive_impl_solve_lrec_derive:
  "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> p \<noteq> [] \<Longrightarrow> R \<turnstile> p \<Rightarrow>(n) map Tm q \<Longrightarrow> (solve_lrec B B' R) \<turnstile> p \<Rightarrow>* map Tm q"
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
    then have "\<exists>C pt p2. p = map Tm pt @ Nt C # p2" using non_word_has_first_Nt by auto
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
      then have n_derive: "R \<turnstile> Nt B # p2 \<Rightarrow>(n) q2" using P1
        by (simp add: deriveln_imp_deriven)
      have "\<nexists>v2. q2 = Nt B #v2 \<and> R \<turnstile> p2 \<Rightarrow>(n) v2" using q2_tms by auto
      then have "\<exists>n1 n2 w v1 v2. n = Suc (n1 + n2) \<and> q2 = v1 @ v2 \<and>
          (B,w) \<in> R \<and> R \<turnstile> w \<Rightarrow>(n1) v1 \<and> R \<turnstile> p2 \<Rightarrow>(n2) v2" using n_derive deriven_Cons_decomp
        by (smt (verit) sym.inject(1))
      then obtain n1 n2 w v1 v2 where decomp: "n = Suc (n1 + n2) \<and> q2 = v1 @ v2 \<and>
          (B,w) \<in> R \<and> R \<turnstile> w \<Rightarrow>(n1) v1 \<and> R \<turnstile> p2 \<Rightarrow>(n2) v2" by blast
      then have derive_from_singleton: "R \<turnstile> [Nt B] \<Rightarrow>(Suc n1) v1"
        using deriven_Suc_decomp_left by force

      have "v1 \<noteq> []"
        using "1.prems"(1) Eps_free_deriven_Nil derive_from_singleton by auto
      then have "\<exists>v1t. v1 = map Tm v1t"
        using decomp append_eq_map_conv q2_tms by blast
      then obtain v1t where v1_tms: "v1 = map Tm v1t" by blast
      then have v1_hd: "hd v1 \<noteq> Nt B"
        by (metis Nil_is_map_conv \<open>v1 \<noteq> []\<close> hd_map sym.distinct(1))

      have deriveln_from_singleton: "R \<turnstile> [Nt B] \<Rightarrow>l(Suc n1) v1" using v1_tms derive_from_singleton
        by (simp add: deriveln_iff_deriven)

      text \<open> This is the interesting bit where we use other lemmas to prove that we can replace 
              a specific part of the derivation which is a left-recursion by a right-recursion in the new productions \<close>
      let ?S = "{x. (\<exists>v. x = (B, v) \<and> x \<in> R)}"
      have "\<exists>u w m k. ?S \<turnstile> [Nt B] \<Rightarrow>l(m) Nt B # u \<and> ?S \<turnstile> Nt B # u \<Rightarrow>l w \<and> hd w \<noteq> Nt B \<and> R \<turnstile> w \<Rightarrow>l(k) v1 \<and> Suc n1 = m + k + 1"
        using deriveln_from_singleton v1_hd 1 lrec_decomp[of ?S B R "[Nt B]" v1 "Suc n1"] by auto
      then obtain u w2 m2 k where l_decomp: "?S \<turnstile> [Nt B] \<Rightarrow>l(m2) Nt B # u \<and> ?S \<turnstile> Nt B # u \<Rightarrow>l w2 \<and> hd w2 \<noteq> Nt B \<and> R \<turnstile> w2 \<Rightarrow>l(k) v1 \<and> Suc n1 = m2 + k + 1" by blast
      then have "\<exists>w2'. (B,w2') \<in> ?S \<and> w2 = w2' @ u" by (simp add: derivel_Nt_Cons)
      then obtain w2' where w2'_prod: "(B,w2') \<in> ?S \<and> w2 = w2' @ u" by blast
      then have w2'_props: "w2' \<noteq> [] \<and> hd w2' \<noteq> Nt B"
        by (metis (mono_tags, lifting) "1.prems"(1) Eps_free_Nil l_decomp hd_append mem_Collect_eq)

      have solve_lrec_subset: "solve_lrec B B' ?S \<subseteq> solve_lrec B B' R" by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def)

      have "solve_lrec B B' ?S \<turnstile> [Nt B] \<Rightarrow>* w2"
        proof(cases "u = []")
          case True
          have "(B, w2') \<in> solve_lrec B B' ?S"using  w2'_props w2'_prod by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def)
          then show ?thesis
            by (simp add: True bu_prod derives_if_bu w2'_prod)
        next
          case False
          have solved_prod: "(B, w2' @ [Nt B']) \<in> solve_lrec B B' ?S"using  w2'_props w2'_prod by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def)
          have "rem_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l* Nt B # u" using l_decomp rem_self_loops_derivels by auto
          then have "\<exists>ln. rem_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l(ln) Nt B # u"
            by (simp add: rtranclp_power)
          then obtain ln where "rem_self_loops ?S \<turnstile> [Nt B] \<Rightarrow>l(ln) Nt B # u" by blast
          then have "(solve_lrec B B' ?S) \<turnstile> [Nt B'] \<Rightarrow>(ln) u" using lrec_lemma3[of ?S B R B' ln u] 1 False by auto
          then have rrec_derive: "(solve_lrec B B' ?S) \<turnstile> w2' @ [Nt B'] \<Rightarrow>(ln) w2' @ u"
            by (simp add: deriven_prepend)
          have "(solve_lrec B B' ?S) \<turnstile> [Nt B] \<Rightarrow> w2' @ [Nt B']" using solved_prod
            by (simp add: derive_singleton)
          then have "(solve_lrec B B' ?S) \<turnstile> [Nt B] \<Rightarrow>* w2' @ u" using rrec_derive
            by (simp add: converse_rtranclp_into_rtranclp relpowp_imp_rtranclp)
          then show ?thesis using w2'_prod by auto
        qed
      then have 2: "solve_lrec B B' R \<turnstile> [Nt B] \<Rightarrow>* w2" using solve_lrec_subset
        by (simp add: derives_mono)

      text \<open> from here on all the smaller derivations are concatenated again after applying the IH \<close>
      have fact2: "R \<turnstile> w2 \<Rightarrow>l(k) v1 \<and> Suc n1 = m2 + k + 1" using l_decomp by auto
      then have "k < n"
        using decomp by linarith
      then have 3: "solve_lrec B B' R \<turnstile> w2 \<Rightarrow>* v1" using "1.IH" 1 v1_tms fact2
        by (metis deriveln_iff_deriven derives_from_empty relpowp_imp_rtranclp)

      have 4: "solve_lrec B B' R \<turnstile> [Nt B] \<Rightarrow>* v1" using 2 3
        by auto

      have "\<exists>v2t. v2 = map Tm v2t" using decomp append_eq_map_conv q2_tms by blast
      then obtain v2t where v2_tms: "v2 = map Tm v2t" by blast
      have "n2 < n" using decomp by auto
      then have 5: "solve_lrec B B' R \<turnstile> p2 \<Rightarrow>* v2" using "1.IH" 1 decomp v2_tms
        by (metis derives_from_empty relpowp_imp_rtranclp)

      have "solve_lrec B B' R \<turnstile> Nt B # p2 \<Rightarrow>* q2" using 4 5 decomp
        by (metis append_Cons append_Nil derives_append_decomp)
      then show ?thesis
        by (simp add: P P1 True derives_prepend)
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


text \<open> right recursive lemmas for \<open>solve_lrec A A' R\<close> \<close>

text \<open> restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>)
      if there is a right-derivation from \<open>u\<close> to \<open>v @ [Nt A']\<close> then u ends in \<open>Nt A'\<close> \<close>
lemma rrec_lemma1: "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)} \<Longrightarrow> S \<turnstile> u \<Rightarrow>r(n) v @ [Nt A']  \<Longrightarrow> \<exists>u'. u = u' @ [Nt A']"
proof (rule ccontr)
  assume assms: "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)}" "S \<turnstile> u \<Rightarrow>r(n) v @ [Nt A']"  "\<nexists>u'. u = u' @ [Nt A']"
  show "False"
  proof (cases "u = []")
    case True
    then show ?thesis using assms derivern_imp_deriven by fastforce
  next
    case u_not_Nil: False
    then show ?thesis
    proof (cases "\<exists>t. last u = Tm t")
      case True
      then show ?thesis using assms
        by (metis (lifting) u_not_Nil append_butlast_last_id derivern_snoc_Tm last_snoc)
    next
      case False
      then have "\<exists>B u'. u = u' @ [Nt B] \<and> B \<noteq> A'" using assms u_not_Nil
        by (metis append_butlast_last_id sym.exhaust)
      then obtain B u' where B_not_A': "u = u' @ [Nt B] \<and> B \<noteq> A'" by blast
      then have "\<exists>w. (B, w) \<in> S" using assms
        by (metis (lifting) derivers_snoc_Nt relpowp_imp_rtranclp)
      then obtain w where elem: "(B, w) \<in> S" by blast
      have "(B, w) \<notin> S" using B_not_A' assms by auto
      then show ?thesis using elem by simp
    qed
  qed
qed

text \<open> solve_lrec does not add productions of the form \<open>A' \<rightarrow> Nt A'\<close> \<close>
lemma solve_lrec_no_self_loop: "Eps_free R \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> (A', [Nt A']) \<notin> solve_lrec A A' R"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Eps_free_def Nts_def split: prod.splits)

text \<open> helper lemma that could be moved to CFG.thy \<close>
lemma derivern_prepend: "R \<turnstile> u \<Rightarrow>r(n) v \<Longrightarrow> R \<turnstile> p @ u \<Rightarrow>r(n) p @ v"
  by (fastforce simp: derivern_iff_rev_deriveln rev_map deriveln_append rev_eq_append_conv)

text \<open> restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>)
      if there is a right-derivation from \<open>u\<close> to \<open>v @ [Nt A']\<close> then u ends in \<open>Nt A'\<close> 
      and there exists a suffix of \<open>v @ [Nt A']\<close> s.t. there is a right-derivation from \<open>[Nt A']\<close> to that suffix\<close>
lemma  rrec_lemma2:"S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)} \<Longrightarrow> Eps_free R \<Longrightarrow> A' \<notin> Nts R  \<Longrightarrow> S \<turnstile> u \<Rightarrow>r(n) v @ [Nt A']
\<Longrightarrow> \<exists>u' v'. u = u' @ [Nt A'] \<and> v = u' @ v' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v' @ [Nt A']"
proof (induction n arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "\<exists>u'. u = u' @ [Nt A']" using rrec_lemma1[of S] Suc by auto
  then obtain u' where u'_prop: "u = u' @ [Nt A']" by blast
  then have "\<exists>w. (A',w) \<in> S \<and> S \<turnstile> u' @ w \<Rightarrow>r(n) v @ [Nt A']" using Suc by (auto simp add: derivern_snoc_Nt)
  then obtain w where w_prop: "(A',w) \<in> S \<and> S \<turnstile> u' @ w \<Rightarrow>r(n) v @ [Nt A']" by blast
  then have "\<exists>u'' v''. u' @ w = u'' @ [Nt A'] \<and>  v = u'' @ v'' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v'' @ [Nt A']" using Suc.IH Suc by auto
  then obtain u'' v'' where u''_prop: "u' @ w = u'' @ [Nt A'] \<and>  v = u'' @ v'' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v'' @ [Nt A']" by blast
  have "w \<noteq> [] \<and> w \<noteq> [Nt A']" using Suc w_prop solve_lrec_no_self_loop
    by fastforce
  then have "\<exists>u1. u1 \<noteq> [] \<and> w = u1 @ [Nt A'] \<and> u'' = u' @ u1" using u''_prop
    by (metis (no_types, opaque_lifting) append.left_neutral append1_eq_conv append_assoc rev_exhaust)
  then obtain u1 where u1_prop: "u1 \<noteq> [] \<and> w = u1 @ [Nt A'] \<and> u'' = u' @ u1" by blast
  then have 1: "u = u' @ [Nt A'] \<and> v = u' @ (u1 @ v'')" using u'_prop u''_prop by auto
  
  have 2: "S \<turnstile> u1 @ [Nt A'] \<Rightarrow>r(n) u1 @ v'' @ [Nt A']" using u''_prop derivern_prepend
    by fastforce
  have "S \<turnstile> [Nt A'] \<Rightarrow>r u1 @ [Nt A']" using w_prop u''_prop u1_prop
    by (simp add: deriver_singleton)
  then have "S \<turnstile> [Nt A'] \<Rightarrow>r(Suc n) u1 @ v'' @ [Nt A']" using u''_prop
    by (meson 2 relpowp_Suc_I2)
  then show ?case using 1
    by auto
qed

text \<open> restricted to right-recursive productions of one Nt (\<open>A' \<rightarrow> w @ [Nt A']\<close>)
      if there is a restricted right-derivation in solve_lrec from \<open>[Nt A']\<close> to \<open>u @ [Nt A']\<close> 
      then there exists a derivation in R from \<open>[Nt A]\<close> to \<open>Nt A # u\<close> to that suffix\<close>
lemma rrec_lemma3: "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)} \<Longrightarrow> Eps_free R \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> S \<turnstile> [Nt A'] \<Rightarrow>r(n) u @ [Nt A'] \<Longrightarrow> R \<turnstile> [Nt A] \<Rightarrow>(n) Nt A # u"
proof(induction n arbitrary: u)
  case 0
  then show ?case by (simp)
next
  case (Suc n)
  then have "\<exists>w. (A',w) \<in> S \<and> S \<turnstile> w \<Rightarrow>r(n) u @ [Nt A']"
    by (auto simp add: derivern_singleton split: prod.splits)
  then obtain w where w_prop1: "(A',w) \<in> S \<and> S \<turnstile> w \<Rightarrow>r(n) u @ [Nt A']" by blast
  then have "\<exists>u' v'. w = u' @ [Nt A'] \<and> u = u' @ v' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v' @ [Nt A']" using rrec_lemma2[of S] Suc by auto
  then obtain u' v' where u'v'_prop: "w = u' @ [Nt A'] \<and> u = u' @ v' \<and> S \<turnstile> [Nt A'] \<Rightarrow>r(n) v' @ [Nt A']" by blast
  then have 1: "R \<turnstile> [Nt A] \<Rightarrow>(n) Nt A # v'" using Suc.IH Suc.prems by auto

  have "(A', u' @ [Nt A']) \<in> solve_lrec A A' R \<longrightarrow> (A, Nt A # u') \<in> R" using Suc by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def)
  then have "(A, Nt A # u') \<in> R" using u'v'_prop Suc.prems(1) w_prop1 by auto

  then have "R \<turnstile> [Nt A] \<Rightarrow> Nt A # u'"
    by (simp add: derive_singleton)
  then have "R \<turnstile> [Nt A] @ v' \<Rightarrow> Nt A # u' @ v'"
    by (metis Cons_eq_appendI derive_append)
  then have "R \<turnstile> [Nt A] \<Rightarrow>(Suc n) Nt A # (u' @ v')" using 1
    by (simp add: relpowp_Suc_I)
  then show ?case using u'v'_prop by simp
qed


text \<open> a right derivation from \<open>p@[Nt A']\<close> to \<open>q\<close> (\<open>last q \<noteq> Nt A'\<close>) can be split into 
  a right-recursive part, only using right-recursive productions with \<open>Nt A'\<close>, 
  one right derivation step consuming \<open>Nt A'\<close> using some rule \<open>A' \<rightarrow> as@[B]\<close> where \<open>B \<noteq> Nt A'\<close>
  and a right-derivation comprising the rest of the derivation\<close>
lemma rrec_decomp: "S = {x. (\<exists>v. x = (A', v @ [Nt A']) \<and> x \<in> solve_lrec A A' R)} \<Longrightarrow> Eps_free R \<Longrightarrow> A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> A' \<notin> nts_syms p \<Longrightarrow> last q \<noteq> Nt A' \<Longrightarrow> solve_lrec A A' R \<turnstile> p @ [Nt A'] \<Rightarrow>r(n) q 
  \<Longrightarrow> \<exists>u w m k. S \<turnstile> p @ [Nt A'] \<Rightarrow>r(m) u @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w \<and> A' \<notin> nts_syms w \<and> solve_lrec A A' R \<turnstile> w \<Rightarrow>r(k) q \<and> n = m + k + 1"
proof (induction n arbitrary: p)
  case 0
  then have pq_not_Nil: "p @ [Nt A'] \<noteq> [] \<and> q \<noteq> []" using Eps_free_derives_Nil
    by auto

  have "p = q" using 0 by auto
  then show ?case using pq_not_Nil 0 by auto
next
  case (Suc n)
  then have pq_not_Nil: "p @ [Nt A'] \<noteq> [] \<and> q \<noteq> []"
    using Eps_free_deriven_Nil Eps_free_solve_lrec derivern_imp_deriven
    by (metis (no_types, lifting) snoc_eq_iff_butlast)

  have "\<nexists>q'. q = q' @ [Nt A']" using pq_not_Nil Suc
    by fastforce

  then have "\<exists>w. (A',w) \<in> (solve_lrec A A' R) \<and> (solve_lrec A A' R) \<turnstile> p @ w \<Rightarrow>r(n) q" using Suc by (auto simp add: derivern_snoc_Nt)
  then obtain w where w_prop: "(A',w) \<in> (solve_lrec A A' R) \<and> solve_lrec A A' R \<turnstile> p @ w \<Rightarrow>r(n) q" by blast

  show ?case
  proof (cases "(A', w) \<in> S")
    case True
    then have "\<exists>w'. w = w' @ [Nt A']"
      by (simp add: Suc.prems(1))
    then obtain w' where w_decomp: "w = w' @ [Nt A']" by blast
    then have "A' \<notin> nts_syms (p @ w')" using Suc True by (auto simp add: solve_lrec_rule_simp6)
    then have "\<exists>u w'' m k. S \<turnstile> p @ w \<Rightarrow>r(m) u @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w'' \<and> A' \<notin> nts_syms w'' \<and> solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> n = m + k + 1"
      using Suc.IH Suc.prems w_prop w_decomp by (metis (lifting) append_assoc)
    then obtain u w'' m k where propo: "S \<turnstile> p @ w \<Rightarrow>r(m) u @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w'' \<and> A' \<notin> nts_syms w'' \<and> solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> n = m + k + 1" by blast
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(Suc m) u @ [Nt A']" using True
      by (meson deriver_snoc_Nt relpowp_Suc_I2)
  
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(Suc m) u @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> u @ [Nt A'] \<Rightarrow>r w'' \<and> A' \<notin> nts_syms w'' \<and> solve_lrec A A' R \<turnstile> w'' \<Rightarrow>r(k) q \<and> Suc n = Suc m + k + 1" using propo by auto
    then show ?thesis by blast
  next
    case False
    then have "last w \<noteq> Nt A'"
      by (metis (mono_tags, lifting) Eps_freeE_Cons Eps_free_solve_lrec Suc.prems(1,2) append_butlast_last_id list.distinct(1) mem_Collect_eq w_prop)
    then have "A' \<notin> nts_syms w" using Suc w_prop by (auto simp add: solve_lrec_rule_simp7)
    then have "w \<noteq> [] \<and> A' \<notin> nts_syms w" using Suc w_prop False
      by (metis (mono_tags, lifting) Eps_free_Nil Eps_free_solve_lrec)
    then have "S \<turnstile> p @ [Nt A'] \<Rightarrow>r(0) p @ [Nt A'] \<and> solve_lrec A A' R \<turnstile> p @ [Nt A'] \<Rightarrow>r p @ w \<and> A' \<notin> nts_syms (p @ w) \<and> solve_lrec A A' R \<turnstile> p @ w \<Rightarrow>r(n) q \<and> Suc n = 0 + n + 1"
      using w_prop Suc by (auto simp add: deriver_snoc_Nt)
    then show ?thesis by blast
  qed
qed

text \<open> if something is not a word it must have a last terminal \<close>
lemma non_word_has_last_Nt: "\<nexists>pt. p = map Tm pt \<Longrightarrow> \<exists>C pt p2. p = p2 @ [Nt C] @ map Tm pt"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a list)
  then show ?case
    by (metis append.left_neutral append_Cons list.simps(9) sym.exhaust)
qed

text \<open> a decomposition of a derivation from a sentential form to a word into multiple derivations that derive words \<close>
lemma derivern_snoc_Nt_Tms_decomp1: "R \<turnstile> p @ [Nt A] \<Rightarrow>r(n) map Tm q \<Longrightarrow> \<exists>pt At w k m. R \<turnstile> p \<Rightarrow>(k) map Tm pt \<and> R \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (A, w) \<in> R \<and> q = pt @ At \<and> n = Suc(k + m)"
proof-
  assume assm: "R \<turnstile> p @ [Nt A] \<Rightarrow>r(n) map Tm q"
  then have "R \<turnstile> p @ [Nt A] \<Rightarrow>(n) map Tm q" by (simp add: derivern_iff_deriven)
  then have "\<exists>n1 n2 q1 q2. n = n1 + n2 \<and> map Tm q = q1 @ q2 \<and> R \<turnstile> p \<Rightarrow>(n1) q1 \<and> R \<turnstile> [Nt A] \<Rightarrow>(n2) q2"
    using deriven_append_decomp by blast
  then obtain n1 n2 q1 q2 where decomp1: "n = n1 + n2 \<and> map Tm q = q1 @ q2 \<and> R \<turnstile> p \<Rightarrow>(n1) q1 \<and> R \<turnstile> [Nt A] \<Rightarrow>(n2) q2" by blast
  then have "\<exists>pt At. q1 = map Tm pt \<and> q2 = map Tm At \<and> q = pt @ At"
    by (meson map_eq_append_conv)
  then obtain pt At where decomp_tms: "q1 = map Tm pt \<and> q2 = map Tm At \<and> q = pt @ At" by blast
  then have "\<exists>w m. n2 = Suc m \<and> R \<turnstile> w \<Rightarrow>(m) (map Tm At) \<and> (A,w) \<in> R" using decomp1 by (auto simp add: deriven_start1)
  then obtain w m where "n2 = Suc m \<and> R \<turnstile> w \<Rightarrow>(m) (map Tm At) \<and> (A,w) \<in> R" by blast
  then have "R \<turnstile> p \<Rightarrow>(n1) map Tm pt \<and> R \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (A, w) \<in> R \<and> q = pt @ At \<and> n = Suc(n1 + m)" using decomp1 decomp_tms by auto
  then show ?thesis by blast
qed

text \<open> a decomposition of a derivation from a sentential form to a word into multiple derivations that derive words \<close>
lemma word_decomp1: "R \<turnstile> p @ [Nt A] @ map Tm ts \<Rightarrow>(n) map Tm q \<Longrightarrow>
   \<exists>pt At w k m. R \<turnstile> p \<Rightarrow>(k) map Tm pt \<and> R \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (A, w) \<in> R \<and> q = pt @ At @ ts \<and> n = Suc(k + m)"
proof -
  assume assm: "R \<turnstile> p @ [Nt A] @ map Tm ts \<Rightarrow>(n) map Tm q"
  then have "\<exists>q1 q2 n1 n2. R \<turnstile> p @ [Nt A] \<Rightarrow>(n1) q1 \<and> R \<turnstile> map Tm ts \<Rightarrow>(n2) q2 \<and> map Tm q = q1 @ q2 \<and> n = n1 + n2"
    using deriven_append_decomp[of n R "p @ [Nt A]" "map Tm ts" "map Tm q"] by auto
  then obtain q1 q2 n1 n2 where P: "R \<turnstile> p @ [Nt A] \<Rightarrow>(n1) q1 \<and> R \<turnstile> map Tm ts \<Rightarrow>(n2) q2 \<and> map Tm q = q1 @ q2 \<and> n = n1 + n2" by blast
  then have "(\<exists>q1t q2t. q1 = map Tm q1t \<and> q2 = map Tm q2t \<and> q = q1t @ q2t)"
    using deriven_from_TmsD map_eq_append_conv by blast
  then obtain q1t q2t where P1: "q1 = map Tm q1t \<and> q2 = map Tm q2t \<and> q = q1t @ q2t" by blast
  then have "q2 = map Tm ts" using P
    using deriven_from_TmsD by blast
  then have 1: "ts = q2t" using P1
    by (metis list.inj_map_strong sym.inject(2))
  then have "n1 = n" using P
    by (metis add.right_neutral not_derive_from_Tms relpowp_E2)
  then have "\<exists>pt At w k m. R \<turnstile> p \<Rightarrow>(k) map Tm pt \<and> R \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (A, w) \<in> R \<and> q1t = pt @ At \<and> n = Suc(k + m)"
    using P P1 derivern_snoc_Nt_Tms_decomp1[of n R p A q1t] derivern_iff_deriven by blast
  then obtain pt At w k m where P2: "R \<turnstile> p \<Rightarrow>(k) map Tm pt \<and> R \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (A, w) \<in> R \<and> q1t = pt @ At \<and> n = Suc(k + m)" by blast
  then have "q = pt @ At @ ts" using P1 1 by auto
  then show ?thesis using P2 by blast
qed


text \<open> every word derived by solve_lrec R can be derived by R \<close>
lemma tm_solve_lrec_derive_impl_derive:
 "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> p \<noteq> [] \<Longrightarrow> B' \<notin> nts_syms p \<Longrightarrow> (solve_lrec B B' R) \<turnstile> p \<Rightarrow>(n) map Tm q \<Longrightarrow> R \<turnstile> p \<Rightarrow>* map Tm q"
proof (induction arbitrary: p q rule: nat_less_induct)
  case (1 n)
  let ?R' = "(solve_lrec B B' R)"
  show ?case
  proof (cases "\<exists>pt. p = map Tm pt")
    case True
    then show ?thesis
      using "1.prems"(6) deriven_from_TmsD derives_from_Tms_iff by blast
  next
    case False
    then have "\<exists>C pt p2. p = p2 @ [Nt C] @ map Tm pt" using non_word_has_last_Nt by auto
    then obtain C pt p2 where p_decomp: "p = p2 @ [Nt C] @ map Tm pt" by blast
    then have "\<exists>pt' At w k m. ?R' \<turnstile> p2 \<Rightarrow>(k) map Tm pt' \<and> ?R' \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (C, w) \<in> ?R' \<and> q = pt' @ At @ pt \<and> n = Suc(k + m)"
      using 1 word_decomp1[of n ?R' p2 C pt q] by auto
    then obtain pt' At w k m where P: "?R' \<turnstile> p2 \<Rightarrow>(k) map Tm pt' \<and> ?R' \<turnstile> w \<Rightarrow>(m) map Tm At \<and> (C, w) \<in> ?R' \<and> q = pt' @ At @ pt \<and> n = Suc(k + m)" by blast
    then have pre1: "m < n" by auto

    have "B' \<notin> nts_syms p2 \<and> k < n" using P 1 p_decomp by auto
    then have p2_not_Nil_derive: "p2 \<noteq> [] \<longrightarrow> R \<turnstile> p2 \<Rightarrow>* map Tm pt'" using 1 P by blast

    have "p2 = [] \<longrightarrow> map Tm pt' = []" using P
      by auto
    then have p2_derive: "R \<turnstile> p2 \<Rightarrow>* map Tm pt'" using p2_not_Nil_derive by auto

    have "R \<turnstile> [Nt C] \<Rightarrow>* map Tm At"
    proof(cases "C = B")
      case C_is_B: True
      then show ?thesis
      proof (cases "last w = Nt B'")
        case True
        let ?S = "{x. (\<exists>v. x = (B', v @ [Nt B']) \<and> x \<in> solve_lrec B B' R)}"

        have "\<exists>w1. w = w1 @ [Nt B']" using True
          by (metis "1.prems"(1) Eps_free_Nil Eps_free_solve_lrec P append_butlast_last_id)
        then obtain w1 where w_decomp: "w = w1 @ [Nt B']" by blast
        then have "\<exists>w1' b k1 m1. ?R' \<turnstile> w1 \<Rightarrow>(k1) w1' \<and> ?R' \<turnstile> [Nt B'] \<Rightarrow>(m1) b \<and> map Tm At = w1' @ b \<and> m = k1 + m1"
          using P deriven_append_decomp by blast
        then obtain w1' b k1 m1 where w_derive_decomp: "?R' \<turnstile> w1 \<Rightarrow>(k1) w1' \<and> ?R' \<turnstile> [Nt B'] \<Rightarrow>(m1) b \<and> map Tm At = w1' @ b \<and> m = k1 + m1" by blast
        then have "\<exists>w1t bt. w1' = map Tm w1t \<and> b = map Tm bt"
          by (meson map_eq_append_conv)
        then obtain w1t bt where tms: "w1' = map Tm w1t \<and> b = map Tm bt" by blast

        have pre1: "k1 < n \<and> m1 < n" using w_derive_decomp P by auto
        have pre2: "w1 \<noteq> []" using w_decomp C_is_B P 1 by (auto simp add: solve_lrec_rule_simp4)
        have Bw1_in_R: "(B, w1) \<in> R" using w_decomp P C_is_B 1 by (auto simp add: solve_lrec_rule_simp5 nts_syms_def)
        then have pre3: "B' \<notin> nts_syms w1" using 1 by (auto simp add: nts_syms_def Nts_def)

        have "R \<turnstile> w1 \<Rightarrow>* map Tm w1t" using pre1 pre2 pre3 w_derive_decomp 1 tms by blast
        then have w1'_derive: "R \<turnstile> [Nt B] \<Rightarrow>* w1'" using Bw1_in_R tms
          by (simp add: derives_Cons_rule)

        have "last [Nt B'] = Nt B' \<and> last (map Tm bt) \<noteq> Nt B'" 
          by (metis "1.prems"(1) Eps_free_deriven_Nil Eps_free_solve_lrec last_ConsL last_map list.map_disc_iff not_Cons_self2 sym.distinct(1) tms w_derive_decomp)
        then have "\<exists>u v m2 k2. ?S \<turnstile> [Nt B'] \<Rightarrow>r(m2) u @ [Nt B'] \<and> ?R' \<turnstile> u @ [Nt B'] \<Rightarrow>r v \<and> B' \<notin> nts_syms v \<and> ?R' \<turnstile> v \<Rightarrow>r(k2) map Tm bt \<and> m1 = m2 + k2 + 1"
          using rrec_decomp[of ?S B' B R "[]" "map Tm bt" m1] w_derive_decomp 1 tms by (simp add: derivern_iff_deriven)
        then obtain u v m2 k2 where rec_decomp: "?S \<turnstile> [Nt B'] \<Rightarrow>r(m2) u @ [Nt B'] \<and> ?R' \<turnstile> u @ [Nt B'] \<Rightarrow>r v \<and> B' \<notin> nts_syms v \<and> ?R' \<turnstile> v \<Rightarrow>r(k2) map Tm bt \<and> m1 = m2 + k2 + 1" by blast
        then have Bu_derive: "R \<turnstile> [Nt B] \<Rightarrow>(m2) Nt B # u"
          using "1.prems"(1,2,3) rrec_lemma3 by fastforce

        have "\<exists>v'. (B', v') \<in> ?R' \<and> v = u @ v'" using rec_decomp
          by (simp add: deriver_snoc_Nt)
        then obtain v' where v_decomp: "(B', v') \<in> ?R' \<and> v = u @ v'" by blast
        then have "(B, Nt B # v') \<in> R" using "1.prems" rec_decomp by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def Nts_def nts_syms_def)
        then have "R \<turnstile> [Nt B] \<Rightarrow> Nt B # v'"
          by (simp add: derive_singleton)
        then have "R \<turnstile> [Nt B] @ v' \<Rightarrow>* Nt B # u @ v'"
          by (metis Bu_derive append_Cons derives_append rtranclp_power)
        then have Buv'_derive: "R \<turnstile> [Nt B] \<Rightarrow>* Nt B # u @ v'"
          using \<open>R \<turnstile> [Nt B] \<Rightarrow> Nt B # v'\<close> by force

        have pre2: "k2 < n" using rec_decomp pre1 by auto
        have "v \<noteq> []" using rec_decomp
          by (metis (lifting) "1.prems"(1) Eps_free_deriven_Nil Eps_free_solve_lrec deriven_from_TmsD derivern_imp_deriven list.simps(8) not_Cons_self2 tms
              w_derive_decomp)
        then have "R \<turnstile> v \<Rightarrow>* map Tm bt" using "1.IH" 1 pre2 rec_decomp by (auto simp add: derivern_iff_deriven)
        then have "R \<turnstile> [Nt B] \<Rightarrow>* Nt B # map Tm bt" using Buv'_derive v_decomp
          by (meson derives_Cons rtranclp_trans)
        then have "R \<turnstile> [Nt B] \<Rightarrow>* [Nt B] @ map Tm bt" by auto
        then have "R \<turnstile> [Nt B] \<Rightarrow>* w1' @ map Tm bt" using w1'_derive derives_append
          by (metis rtranclp_trans)
        then show ?thesis using tms w_derive_decomp C_is_B by auto
      next
        case False
        have pre2: "w \<noteq> []" using P "1.prems"(1)
          by (meson Eps_free_Nil Eps_free_solve_lrec)
        then have 2: "(C, w) \<in> R" using P False "1.prems" p_decomp C_is_B by (auto simp add: solve_lrec_rule_simp3)
        then have pre3: "B' \<notin> nts_syms w" using P "1.prems"(3) by (auto simp add: Nts_def)

        have "R \<turnstile> w \<Rightarrow>* map Tm At" using "1.IH" "1.prems" pre1 pre2 pre3 P by blast
        then show ?thesis using 2
          by (meson bu_prod derives_bu_iff rtranclp_trans)
      qed
    next
      case False
      then have 2: "(C, w) \<in> R" using P "1.prems"(5) p_decomp by (auto simp add: solve_lrec_rule_simp1)
      then have pre2: "B' \<notin> nts_syms w" using P "1.prems"(3) by (auto simp add: Nts_def)
      have pre3: "w \<noteq> []" using "1.prems"(1) 2 by (auto simp add: Eps_free_def)

      have "R \<turnstile> w \<Rightarrow>* map Tm At" using "1.IH" "1.prems" pre1 pre2 pre3 P by blast
      then show ?thesis using 2
        by (meson bu_prod derives_bu_iff rtranclp_trans)
    qed

    
    then show ?thesis using p2_derive
      by (metis P derives_append derives_append_decomp map_append p_decomp)
  qed
qed

text \<open> Language inclusion of \<open>solve_lrec R\<close> in \<open>R\<close> \<close>
lemma Lang_solve_lrec_incl_Lang: "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R; A \<noteq> B'\<rbrakk> \<Longrightarrow> Lang (solve_lrec B B' R) A \<subseteq> Lang R A"
proof
  fix x
  assume assms: "x \<in> Lang (solve_lrec B B' R) A" "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R" "A \<noteq> B'"

  then have "(solve_lrec B B' R) \<turnstile> [Nt A] \<Rightarrow>* map Tm x" by (simp add: Lang_def)
  then have "\<exists>n. (solve_lrec B B' R) \<turnstile> [Nt A] \<Rightarrow>(n) map Tm x"
    by (simp add: rtranclp_power)
  then obtain n where "(solve_lrec B B' R) \<turnstile> [Nt A] \<Rightarrow>(n) map Tm x" by blast
  then have "R \<turnstile> [Nt A] \<Rightarrow>* map Tm x" using tm_solve_lrec_derive_impl_derive[of R] assms by auto

  then show "x \<in> Lang R A" by (simp add: Lang_def)
qed

text \<open> Language inclusion of \<open>R\<close> in \<open>solve_lrec R\<close> \<close>
lemma Lang_incl_Lang_solve_lrec: "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R\<rbrakk> \<Longrightarrow> Lang (solve_lrec B B' R) A \<supseteq> Lang R A"
proof
  fix x
  assume assms: "x \<in> Lang R A" "Eps_free R" "B \<noteq> B'" "B' \<notin> Nts R"

  then have "R \<turnstile> [Nt A] \<Rightarrow>* map Tm x" using assms by (auto simp add: Lang_def)
  then have "\<exists>n. R \<turnstile> [Nt A] \<Rightarrow>(n) map Tm x"
    by (simp add: rtranclp_imp_relpowp) 
  then obtain n where "R \<turnstile> [Nt A] \<Rightarrow>(n) map Tm x" by blast
  then show "x \<in> Lang (solve_lrec B B' R) A" using tm_derive_impl_solve_lrec_derive[of R B B' "[Nt A]" n x] assms by (auto simp add: Lang_def) 
qed

text \<open> solve_lrec does not change language \<close>
lemma solve_lrec_Lang: "\<lbrakk> Eps_free R; B \<noteq> B'; B' \<notin> Nts R; A \<noteq> B'\<rbrakk> \<Longrightarrow> Lang (solve_lrec B B' R) A = Lang R A"
  using Lang_solve_lrec_incl_Lang Lang_incl_Lang_solve_lrec by fastforce


text \<open> Section exp_hd Language equivalence \<close>


text \<open> every righthand side of an \<open>exp_hd R\<close> production is derivable by \<open>R\<close> \<close>
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

(* TODO should be moved to CFG.thy*)
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


text \<open>This lemma expects a Set of quadruples \<open>(A, a1, B, a2)\<close>. 
  Each quadruple encodes a specific terminal in a specific rule \<open>(A, a1 @ Nt B # a2)\<close> (this encodes \<open>Nt B\<close>)
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
  Then only equivalence of the encoded set with the \<open>exp_hd R\<close> set has to be proven \<close>
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

text \<open> Language equivalence of \<open>exp_hd R\<close> and \<open>R\<close> \<close>
lemma exp_hd_Lang: "Lang (exp_hd B As R) A = Lang R A"
  using exp_hd_incl1[of B As R A] exp_hd_incl2[of R A B As] by auto


text \<open> Section Lang solve_tri equivalence \<close>    

lemma "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As'); A \<notin> set As'\<rbrakk> \<Longrightarrow> Lang (solve_tri As As' R) A \<subseteq> Lang R A"
  sorry

lemma "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As'); A \<notin> set As'\<rbrakk> \<Longrightarrow> Lang (solve_tri As As' R) A \<supseteq> Lang R A"
  sorry

text \<open> solve_tri does not change the Language \<close>
lemma solve_tri_Lang: "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As'); Nts R \<inter> set As' = {}; A \<notin> set As'\<rbrakk> \<Longrightarrow> Lang (solve_tri As As' R) A = Lang R A"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by simp
next
  case (2 Aa As A' As' R)
  then have e_free1: "Eps_free (exp_hd Aa As (solve_tri As As' R))" by (simp add: Eps_free_exp_hd Eps_free_solve_tri)
  have "length As \<le> length As'" using 2 by simp
  then have "Nts (exp_hd Aa As (solve_tri As As' R)) \<subseteq> Nts R \<union> set As'" using 2 Nts_exp_hd_sub Nts_solve_tri_sub
    by (metis subset_trans)
  then have nts1: " A' \<notin> Nts (exp_hd Aa As (solve_tri As As' R))" using 2 Nts_exp_hd_sub Nts_solve_tri_sub by auto
  
  have "Lang (solve_tri (Aa # As) (A' # As') R) A = 
             Lang (solve_lrec Aa A' (exp_hd Aa As (solve_tri As As' R))) A" by simp
  also have "... = Lang (exp_hd Aa As (solve_tri As As' R)) A"
    using nts1 e_free1 2 solve_lrec_Lang[of "exp_hd Aa As (solve_tri As As' R)" Aa A' A] by (simp)
  also have "... = Lang (solve_tri As As' R) A" by (simp add: exp_hd_Lang)
  finally show ?case using 2 by (auto)
next
  case (3 v va c)
  then show ?case by simp
qed
  
  
text \<open>Section Bringing triangular grammar into GNF form\<close>

text \<open> this function expands all head-Nts of productions with Lhs given in the list 
  If the Productions were in a triangular form beforehand this function returns productions in GNF \<close>
fun exp_triangular :: "'n list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"exp_triangular [] R = R" |
"exp_triangular (S#Ss) R =
 (let R' = exp_triangular Ss R;
      X = lrec_prods R' S (set Ss);
      Y = {(S,v@w) |v w. \<exists>B. (S, Nt B # w) \<in> X \<and> (B,v) \<in> R'}
  in R' - X \<union> Y)"

declare exp_triangular.simps(1)[code]
lemma exp_triangular_Cons_code[code]: "exp_triangular (S#Ss) R =
 (let R' = exp_triangular Ss R;
      X = {w \<in> Rhss R' S. w \<noteq> [] \<and> hd w \<in> Nt ` (set Ss)};
      Y = (\<Union>(B,v) \<in> R'. \<Union>w \<in> X. if hd w \<noteq> Nt B then {} else {(S,v @ tl w)})
  in R' - ({S} \<times> X) \<union> Y)"
by(simp add: Let_def Rhss_def neq_Nil_conv Ball_def, safe, force+)

text \<open> GNF property, that all productions start with a Tm \<close>
definition GNF_hd :: "('n,'t)Prods \<Rightarrow> bool" where 
"GNF_hd R = (\<forall>(A, w) \<in> R. \<exists>t. hd w = Tm t)"

text \<open> GNF property expressed using dep_on, all Nt depend on no Nt\<close>
definition GNF_hd_dep_on :: "('n,'t)Prods \<Rightarrow> bool" where
"GNF_hd_dep_on R = (\<forall>A \<in> Nts R. dep_on R A = {})"
 
fun GNF :: "('n,'t)Prods \<Rightarrow> bool" where 
"GNF R = (GNF_hd R)" 
(* \<and> tms_syms (tl w) = {}*)


(*fun replace_tl_tms_by_Nts :: "'n list \<Rightarrow> 't list \<Rightarrow> ('n,'t)Prods \<Rightarrow> ('n,'t)Prods" where 
"replace_tl_tms_by_Nts _ [] R = R" |
"replace_tl_tms_by_Nts (S#Ss) (T#Ts) R = 
 (let R' = replace_tl_tms_by_Nts Ss Ts R;
      X = {(Al,Bw) \<in> R'. (\<exists>A. Al=A) \<and> (\<exists>v w. tl Bw = v @ Tm T # w)};
      Y = {(A,x) | A x. (\<exists>y. (A, y) \<in> X \<and> x = substs (Tm T) [Nt S] y)}
  in R' - X \<union> Y \<union> {(S, [Tm T])})"*)

lemma dep_on_helper: "dep_on R A = {} \<Longrightarrow> (A, w) \<in> R \<Longrightarrow> w = [] \<or> (\<exists>T wt. w = Tm T # wt)"
proof -
  assume assms: "dep_on R A = {}"  "(A, w) \<in> R"
  show "w = [] \<or> (\<exists>T wt. w = Tm T # wt)"
  proof (rule ccontr)
    assume "\<not>(w = [] \<or> (\<exists>T wt. w = Tm T # wt))"
    then have "\<exists>B wb. w = Nt B # wb"
      by (metis destTm.cases neq_Nil_conv)
    then obtain B wb where "w = Nt B # wb" by blast
    then show "False" using assms by (auto simp add: dep_on_def)
  qed
qed

text \<open> both definitions of the GNF property are equivalent \<close>
lemma GNF_hd_iff_dep_on: "Eps_free R \<Longrightarrow> GNF_hd R \<longleftrightarrow> (\<forall>A \<in> Nts R. dep_on R A = {})"
proof
  assume "GNF_hd R"
  then show "(\<forall>A \<in> Nts R. dep_on R A = {})" by (auto simp add: GNF_hd_def dep_on_def)
next
  assume assm: "(\<forall>A \<in> Nts R. dep_on R A = {})" "Eps_free R"
  have 1: "\<forall>(B, w) \<in> R. \<exists>T wt. w = Tm T # wt \<or> w = []"
  proof
    fix x
    assume "x \<in> R"
    then have "case x of (B, w) \<Rightarrow> dep_on R B = {}" using assm by (auto simp add: Nts_def)
    then show "case x of (B, w) \<Rightarrow> \<exists>T wt. w = Tm T # wt \<or> w = []" using \<open>x \<in> R\<close> dep_on_helper by fastforce
  qed
  have 2: "\<forall>(B, w) \<in> R. w \<noteq> []" using assm by (auto simp add: Eps_free_def)
  have "\<forall>(B, w) \<in> R. \<exists>T wt. w = Tm T # wt" using 1 2 by auto
  then show "GNF_hd R" by (auto simp add: GNF_hd_def)
qed

text \<open> eps_free preservation \<close>
lemma exp_triangular_Eps_free: "Eps_free R \<Longrightarrow> Eps_free (exp_triangular As R)"
  by (induction As R rule: exp_triangular.induct) (auto simp add: Let_def Eps_free_def)


lemma helper_tri1: "triangular (As @ [A]) R \<Longrightarrow> triangular As R"
proof(induction As R rule: triangular.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 A As R)
  then show ?case by simp
qed

lemma helper_exp_tri1: "A \<notin> set As \<Longrightarrow> (A, w) \<in> exp_triangular As R \<Longrightarrow> (A, w) \<in> R"
  by (induction As R rule: exp_triangular.induct) (auto simp add: Let_def)


text \<open> if none of the expanded Nts depend on \<open>A\<close> then any rule depending on \<open>A\<close> in \<open>exp_triangular As R\<close> must already have been in \<open>R\<close> \<close>
lemma helper_exp_tri2: "Eps_free R \<Longrightarrow> A \<notin> set As \<Longrightarrow> \<forall>C \<in> set As. A \<notin> (dep_on R C) \<Longrightarrow> B \<noteq> A \<Longrightarrow> (B, Nt A # w) \<in> exp_triangular As R \<Longrightarrow> (B, Nt A # w) \<in> R"
proof (induction As R arbitrary: B w rule: exp_triangular.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  have "(B, Nt A # w) \<in> exp_triangular Ss R"
  proof (cases "B = S")
    case B_is_S: True
    let ?R' = "exp_triangular Ss R"
    let ?X = "{(Al,Bw) \<in> ?R'. Al=S \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set (Ss))}"
    let ?Y = "{(S,v@w) |v w. \<exists>B. (S, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"
    have "(B, Nt A # w) \<notin> ?X" using 2 by auto
    then have 3: "(B, Nt A # w) \<in> ?R' \<or> (B, Nt A # w) \<in> ?Y" using 2 by (auto simp add: Let_def)
    then show ?thesis
    proof (cases "(B, Nt A # w) \<in> ?R'")
      case True
      then show ?thesis by simp
    next
      case False
      then have "(B, Nt A # w) \<in> ?Y" using 3 by simp
      then have "\<exists>v wa Ba. Nt A # w = v @ wa \<and> (S, Nt Ba # wa) \<in> exp_triangular Ss R \<and> Ba \<in> set Ss \<and> (Ba, v) \<in> exp_triangular Ss R" by (auto simp add: Let_def)
      then obtain v wa Ba where P: "Nt A # w = v @ wa \<and> (S, Nt Ba # wa) \<in> exp_triangular Ss R \<and> Ba \<in> set Ss \<and> (Ba, v) \<in> exp_triangular Ss R" by blast
      have "Eps_free (exp_triangular Ss R)" using 2 by (auto simp add: exp_triangular_Eps_free)
      then have "v \<noteq> []" using P by (auto simp add: Eps_free_def)
      then have v_hd: "hd v = Nt A" using P by (metis hd_append list.sel(1))
      then have "\<exists>va. v = Nt A # va"
        by (metis \<open>v \<noteq> []\<close> list.collapse)
      then obtain va where P2: "v = Nt A # va" by blast
      then have "(Ba, v) \<in> R" using 2 P
        by (metis list.set_intros(2))
      then have "A \<in> dep_on R Ba" using v_hd P2 by (auto simp add: dep_on_def)
      then show ?thesis using 2 P by auto
    qed
  next
    case False
    then show ?thesis using 2 by (auto simp add: Let_def)
  qed

  then show ?case using 2 by auto
qed 

text \<open> in a triangular form no Nts depend on the last Nt in the list \<close>
lemma triangular_snoc_dep_on: "triangular (As@[A]) R \<Longrightarrow> \<forall>C \<in> set As. A \<notin> (dep_on R C)"
  by (induction As) auto

lemma triangular_helper1: "triangular As R \<Longrightarrow> A \<in> set As \<Longrightarrow> A \<notin> dep_on R A"
  by (induction As) auto


lemma dep_on_A'_solve_lrec_Nts: "A \<noteq> A' \<Longrightarrow> A' \<notin> Nts R \<Longrightarrow> dep_on (solve_lrec A A' R) A' \<subseteq> Nts R"
proof -
  assume assms: "A \<noteq> A'" "A' \<notin> Nts R"
  have 1: "dep_on (solve_lrec A A' R) A' \<subseteq> Nts R \<union> {A'}"
    using Nts_solve_lrec_sub dep_on_subs_Nts by fastforce
  have "A' \<notin> dep_on (solve_lrec A A' R) A'" using assms by (auto simp add: solve_lrec_no_new_own_dep)
  then show ?thesis using 1 by auto
qed
  

lemma dep_on_solve_tri_Nts_R: "Eps_free R \<Longrightarrow> B \<in> set As \<Longrightarrow> distinct (As @ As') \<Longrightarrow> set As' \<inter> Nts R = {} \<Longrightarrow> length As \<le> length As' \<Longrightarrow> dep_on (solve_tri As As' R) B \<subseteq> Nts R"
proof (induction As As' R arbitrary: B rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by (simp add: dep_on_subs_Nts)
next
  case (2 A As A' As' R)
  then have F1: "dep_on (solve_tri As As' R) B \<subseteq> Nts R"
    by (cases "B = A") (simp_all add: dep_on_solve_tri_simp dep_on_subs_Nts)
  then have F2: "dep_on (exp_hd A As (solve_tri As As' R)) B \<subseteq> Nts R"
  proof (cases "B = A")
    case True
    have "triangular As (solve_tri As As' R)" using 2 by (auto simp add: part_triangular_solve_tri)
    then have "dep_on (exp_hd A As (solve_tri As As' R)) B \<subseteq> dep_on (solve_tri As As' R) B \<union> \<Union> (dep_on (solve_tri As As' R) ` set As) - set As"
      using 2 True by (auto simp add: dep_on_exp_hd Eps_free_solve_tri)
    also have "... \<subseteq> Nts R" using "2.IH" 2 F1 by auto
    finally show ?thesis.
  next
    case False
    then show ?thesis using F1 by (auto simp add: dep_on_exp_hd_simp2)
  qed
  then have "dep_on (solve_lrec A A' (exp_hd A As (solve_tri As As' R))) B \<subseteq> Nts R"
  proof (cases "B = A")
    case True
    then show ?thesis using 2 F2 by (auto simp add: dep_on_solve_lrec_simp Eps_free_solve_tri Eps_free_exp_hd)
  next
    case False
    have "B \<noteq> A'" using 2 by auto
    then show ?thesis using 2 F2 False by (simp add: dep_on_solve_lrec_simp2)
  qed
  then show ?case by simp
next
  case (3 v va c)
  then show ?case by simp
qed

text \<open> in triangular form Nts do not depend on Nts later in the list \<close>
lemma middle_triangular_dep_on: "triangular (As@[A]@Bs) R \<Longrightarrow> dep_on R A \<inter> (set Bs \<union> {A}) = {}"
  by (induction As) auto

text \<open> if the full set of productions is in triangular form Nts only depend on Nts earlier in the list \<close>
lemma "triangular (As@[A]@Bs) R \<Longrightarrow> Nts R \<subseteq> set (As@[A]@Bs) \<Longrightarrow> dep_on R A \<subseteq> set As"
proof -
  assume tri: "triangular (As@[A]@Bs) R" and Nts_sub: "Nts R \<subseteq> set (As@[A]@Bs)"
  have "dep_on R A \<subseteq> Nts R" by (simp add: dep_on_subs_Nts)
  then have 1: "dep_on R A \<subseteq> set (As@[A]@Bs)" using Nts_sub by simp
  have "dep_on R A \<inter> (set Bs \<union> {A}) = {}" using tri middle_triangular_dep_on by simp
  then show "dep_on R A \<subseteq> set As" using 1 by auto
qed

text \<open> if two parts of the productions are triangular and no Nts from the first part depend on ones of the second they are also triangular when put together \<close>
lemma triangular_append: "triangular As R \<Longrightarrow> triangular Bs R \<Longrightarrow> \<forall>A\<in>set As. dep_on R A \<inter> set Bs = {} \<Longrightarrow> triangular (As@Bs) R"
  by (induction As) auto

lemma help1: "set As \<inter> Nts R = {} \<Longrightarrow> triangular As R"
proof (induction As)
  case Nil
  then show ?case by auto
next
  case (Cons a As)
  have "dep_on R a \<subseteq> Nts R" by (simp add: dep_on_subs_Nts)
  then have "dep_on R a \<inter> (set As  \<union> {a}) = {}" using Cons by auto
  then show ?case using Cons by auto
qed

text \<open> the newly added Nts in solve_lrec are in triangular form wrt \<open>rev As'\<close> \<close>
lemma triangular_rev_As'_solve_tri: "set As' \<inter> Nts R = {} \<Longrightarrow> distinct (As @ As') \<Longrightarrow> length As \<le> length As' \<Longrightarrow> triangular (rev As') (solve_tri As As' R)"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by (auto simp add: help1)
next
  case (2 A As A' As' R)
  then have "triangular (rev As') (solve_tri As As' R)" by simp
  then have "triangular (rev As') (exp_hd A As (solve_tri As As' R))" using 2 by (auto simp add: triangular_exp_hd)
  then have F1: "triangular (rev As') (solve_tri (A#As) (A'#As') R)" using 2 by (auto simp add: triangular_solve_lrec)
  have "Nts (solve_tri As As' R) \<subseteq> Nts R \<union> set As'" using 2 by (auto simp add: Nts_solve_tri_sub)
  then have F_nts: "Nts (exp_hd A As (solve_tri As As' R)) \<subseteq> Nts R \<union> set As'"
    using Nts_exp_hd_sub[of A As "(solve_tri As As' R)"] by auto
  then have "A' \<notin> dep_on (solve_lrec A A' (exp_hd A As (solve_tri As As' R))) A'" 
    using 2 solve_lrec_no_new_own_dep[of A A'] by auto
  then have F2: "triangular [A'] (solve_tri (A#As) (A'#As') R)" by auto
  have "\<forall>a\<in>set As'. dep_on (solve_tri (A#As) (A'#As') R) a \<inter> set [A'] = {}"
  proof
    fix a
    assume "a \<in> set As'"
    then have "A' \<notin> Nts (exp_hd A As (solve_tri As As' R)) \<and> a \<noteq> A" using F_nts 2 by auto
    then show "dep_on (solve_tri (A#As) (A'#As') R) a \<inter> set [A'] = {}" 
      using 2 solve_lrec_rule_simp9[of A' "(exp_hd A As (solve_tri As As' R))" a A] solve_lrec_rule_simp8[of A'] 
      by (cases "a = A'") (auto simp add: dep_on_def)
  qed
    
  then have "triangular (rev (A'#As')) (solve_tri (A#As) (A'#As') R)" using F1 F2 by (auto simp add: triangular_append)
  then show ?case by auto
next
  case (3 v va c)
  then show ?case by auto
qed

text \<open> the entire set of productions is in triangular form after solve_tri wrt \<open>As@(rev As')\<close> \<close>
lemma triangular_As_As'_solve_tri: "\<lbrakk> Eps_free R; length As \<le> length As'; distinct(As @ As'); Nts R \<subseteq> set As\<rbrakk> \<Longrightarrow> triangular (As@(rev As')) (solve_tri As As' R)"
proof-
  assume assms: "Eps_free R" "length As \<le> length As'" "distinct (As@As')" "Nts R \<subseteq> set As"
  then have 1: "triangular As (solve_tri As As' R)" by (auto simp add: part_triangular_solve_tri)
  have "set As' \<inter> Nts R = {}" using assms by auto
  then have 2: "triangular (rev As') (solve_tri As As' R)" using assms by (auto simp add: triangular_rev_As'_solve_tri)
  have "set As' \<inter> Nts R = {}" using assms by auto
  then have "\<forall>A\<in>set As. dep_on (solve_tri As As' R) A \<subseteq> Nts R" using assms by (auto simp add: dep_on_solve_tri_Nts_R)
  then have "\<forall>A\<in>set As. dep_on (solve_tri As As' R) A \<inter> set As' = {}" using assms by auto
  then show ?thesis using 1 2 by (auto simp add: triangular_append)
qed

text \<open> given \<open>triangular As\<close> then \<open>exp_triangular (rev As)\<close> brings the set of productions \<open>As\<close> into GNF form\<close>
lemma dep_on_exp_tri: "\<lbrakk>Eps_free R; triangular (rev As) R; distinct As; A \<in> set As\<rbrakk> \<Longrightarrow> dep_on (exp_triangular As R) A \<inter> set As = {}"
proof(induction As R arbitrary: A rule: exp_triangular.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  then have Eps_free_exp_Ss: "Eps_free (exp_triangular Ss R)"
    by (simp add: exp_triangular_Eps_free)
  have dep_on_fact: "\<forall>C \<in> set Ss. S \<notin> (dep_on R C)" using 2 by (auto simp add: triangular_snoc_dep_on)
  then show ?case
  proof (cases "A = S")
    case True
    have F1: "(S, Nt S # w) \<notin> exp_triangular Ss R" for w
    proof(rule ccontr)
      assume "\<not>((S, Nt S # w) \<notin> exp_triangular Ss R)"
      then have "(S, Nt S # w) \<in> R" using 2 by (auto simp add: helper_exp_tri1)
      then have N: "S \<in> dep_on R A" using True by (auto simp add: dep_on_def)
      have "S \<notin> dep_on R A" using 2 True by (auto simp add: triangular_helper1)
      then show "False" using N by simp
    qed

    have F2: "(S, Nt S # w) \<notin> exp_triangular (S#Ss) R" for w
    proof(rule ccontr)
      assume "\<not>((S, Nt S # w) \<notin> exp_triangular (S#Ss) R)"
      then have "\<exists>v wa B. Nt S # w = v @ wa \<and> B \<in> set Ss \<and> (S, Nt B # wa) \<in> exp_triangular Ss R \<and> (B, v) \<in> exp_triangular Ss R"
        using 2 F1 by (auto simp add: Let_def)
      then obtain v wa B where v_wa_B_P: "Nt S # w = v @ wa \<and> B \<in> set Ss \<and> (S, Nt B # wa) \<in> exp_triangular Ss R \<and> (B, v) \<in> exp_triangular Ss R" by blast
      then have "v \<noteq> [] \<and> (\<exists>va. v = Nt S # va)" using Eps_free_exp_Ss
        by (metis Eps_free_Nil append_eq_Cons_conv)
      then obtain va where vP: "v \<noteq> [] \<and> v = Nt S # va" by blast
      then have "(B, v) \<in> R" using v_wa_B_P 2 dep_on_fact helper_exp_tri2[of R S Ss B] True by auto
      then have "S \<in> dep_on R B" using vP by (auto simp add: dep_on_def)
      then show "False" using dep_on_fact v_wa_B_P by auto
    qed

    have "x \<in> set Ss \<longrightarrow> (S, Nt x # w) \<notin> exp_triangular (S#Ss) R" for x w
    proof (rule ccontr)
      assume "\<not> (x \<in> set Ss \<longrightarrow> (S, Nt x # w) \<notin> exp_triangular (S # Ss) R)"
      then have assm: "x \<in> set Ss \<and> (S, Nt x # w) \<in> exp_triangular (S # Ss) R" by blast
      then have "\<exists>v wa B. Nt x # w = v @ wa \<and> (S, Nt B # wa) \<in> exp_triangular Ss R \<and> B \<in> set Ss \<and> (B, v) \<in> exp_triangular Ss R"
        using 2 by (auto simp add: Let_def)
      then obtain v wa B where v_wa_B_P:"Nt x # w = v @ wa \<and> (S, Nt B # wa) \<in> exp_triangular Ss R \<and> B \<in> set Ss \<and> (B, v) \<in> exp_triangular Ss R" by blast
      then have dep_on_IH: "dep_on (exp_triangular Ss R) B \<inter> set Ss = {}" using 2 by (auto simp add: helper_tri1)
      have "v \<noteq> [] \<and> (\<exists>va. v = Nt x # va)" using Eps_free_exp_Ss v_wa_B_P
        by (metis Eps_free_Nil append_eq_Cons_conv)
      then obtain va where vP: "v \<noteq> [] \<and> v = Nt x # va" by blast
      then have "x \<in> dep_on (exp_triangular Ss R) B" using v_wa_B_P by (auto simp add: dep_on_def)
      then show "False" using dep_on_IH v_wa_B_P assm by auto
    qed

    then show ?thesis using 2 True F2 by (auto simp add: Let_def dep_on_def)
  next
    case False
    have "(A, Nt S # w) \<notin> exp_triangular Ss R" for w
    proof (rule ccontr)
      assume "\<not> (A, Nt S # w) \<notin> exp_triangular Ss R"
      then have "(A, Nt S # w) \<in> R" using 2 helper_exp_tri2 dep_on_fact
        by (metis False distinct.simps(2))
      then have F: "S \<in> dep_on R A" by (auto simp add: dep_on_def)
      have "S \<notin> dep_on R A" using dep_on_fact False 2 by auto
      then show "False" using F by simp
    qed
    then show ?thesis using 2 False by (auto simp add: helper_tri1 Let_def dep_on_def)
  qed
qed
 
text \<open>Section on exp_triangular does not change the set of Nts\<close>

lemma Lhss_exp_tri: "Lhss (exp_triangular As R) \<subseteq> Lhss R"
  by (induction As R rule: exp_triangular.induct) (auto simp add: Lhss_def Let_def)

lemma Rhs_Nts_exp_tri: "Rhs_Nts (exp_triangular As R) \<subseteq> Rhs_Nts R"
proof (induction As R rule: exp_triangular.induct)
  case (1 R)
  then show ?case by simp
next
  case (2 S Ss R)
  let ?X = "{(Al, Bw). (Al, Bw) \<in> exp_triangular Ss R \<and> Al = S \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set Ss)}"
  let ?Y = "{(S, v @ w) |v w. \<exists>B. (S, Nt B # w) \<in> exp_triangular Ss R \<and> B \<in> set Ss \<and> (B, v) \<in> exp_triangular Ss R}"
  have F1: "Rhs_Nts ?X \<subseteq> Rhs_Nts R" using 2 by (auto simp add: Rhs_Nts_def)
  have "Rhs_Nts ?Y \<subseteq> Rhs_Nts R"
  proof
    fix x
    assume "x \<in> Rhs_Nts ?Y"
    then have "\<exists>y ys. (y, ys) \<in> ?Y \<and> x \<in> nts_syms ys" by (auto simp add: Rhs_Nts_def)
    then obtain y ys where P1: "(y, ys) \<in> ?Y \<and> x \<in> nts_syms ys" by blast
    then show "x \<in> Rhs_Nts R" using P1 2 Rhs_Nts_def by fastforce
  qed
  then show ?case using F1 2 by (auto simp add: Rhs_Nts_def Let_def)
qed 

lemma Nts_exp_tri: "Nts (exp_triangular As R) \<subseteq> Nts R"
  by (metis Lhss_exp_tri Nts_Lhss_Rhs_Nts Rhs_Nts_exp_tri Un_mono)

text \<open> if the entire triangular form is expanded the full set of productions is in GNF form \<close>
lemma GNF_hd_exp_tri: "\<lbrakk>Eps_free R; triangular (rev As) R; distinct As; Nts R \<subseteq> set As\<rbrakk> \<Longrightarrow> GNF_hd (exp_triangular As R)"
proof -
  assume assms: "Eps_free R" "triangular (rev As) R" "distinct As" "Nts R \<subseteq> set As"
  then have "x \<in> Nts R \<Longrightarrow> dep_on (exp_triangular As R) x = {}" for x
  proof -
    assume "x \<in> Nts R"
    then have "dep_on (exp_triangular As R) x \<inter> set As = {}" using dep_on_exp_tri assms
      by (metis subsetD)
    then show ?thesis using dep_on_subs_Nts Nts_exp_tri assms(4) by fastforce 
  qed

  then show ?thesis using GNF_hd_iff_dep_on assms
    by (metis Nts_exp_tri exp_triangular_Eps_free subset_iff)
qed

text \<open> any set of productions can be transformed into GNF via \<open>exp_triangular (solve_tri)\<close> \<close>
theorem GNF_of_R: "\<lbrakk>Eps_free R; distinct (As @ As'); Nts R \<subseteq> set As; length As \<le> length As'\<rbrakk> 
\<Longrightarrow> GNF (exp_triangular (As' @ rev As) (solve_tri As As' R))"
proof -
  assume assms: "Eps_free R" "distinct (As @ As')" "Nts R \<subseteq> set As" "length As \<le> length As'"
  then have tri: "triangular (As @ rev As') (solve_tri As As' R)"
    by (simp add: Int_commute triangular_As_As'_solve_tri)
  have "Nts (solve_tri As As' R) \<subseteq> set As \<union> set As'" using assms Nts_solve_tri_sub by fastforce 
  then show ?thesis using GNF_hd_exp_tri[of "(solve_tri As As' R)" "(As' @ rev As)"] assms tri by (auto simp add: Eps_free_solve_tri)
qed

text \<open> Section Language equivalence of \<open>exp_triangular\<close> \<close>

lemma exp_tri_prods_deirvable: "(B, bs) \<in> (exp_triangular As R) \<Longrightarrow> R \<turnstile> [Nt B] \<Rightarrow>* bs"
proof (induction As R arbitrary: B bs rule: exp_triangular.induct)
  case (1 R)
  then show ?case
    by (simp add: bu_prod derives_if_bu)
next
  case (2 A As R)
  then show ?case
  proof (cases "B \<in> set (A#As)")
    case True
    then show ?thesis 
    proof (cases "B = A")
      case True
      then have "\<exists>C cw v. (bs = cw @ v \<and> (B, Nt C # v) \<in> (exp_triangular As R) \<and> (C, cw) \<in> (exp_triangular As R)) \<or> (B, bs) \<in> (exp_triangular As R)"
        using 2 by (auto simp add: Let_def)
      then obtain C cw v where "(bs = cw @ v \<and> (B, Nt C # v) \<in> (exp_triangular As R) \<and> (C, cw) \<in> (exp_triangular As R)) \<or> (B, bs) \<in> (exp_triangular As R)" by blast
      then have "(bs = cw @ v \<and> R \<turnstile> [Nt B] \<Rightarrow>* [Nt C] @ v \<and> R \<turnstile> [Nt C] \<Rightarrow>* cw) \<or> R \<turnstile> [Nt B] \<Rightarrow>* bs" using "2.IH" by auto       
      then show ?thesis by (meson derives_append rtranclp_trans)
    next
      case False
      then have "(B, bs) \<in> (exp_triangular As R)" using 2 by (auto simp add: Let_def)
      then show ?thesis using "2.IH" by (simp add: bu_prod derives_if_bu)
    qed
  next
    case False
    then have "(B, bs) \<in> R" using 2 by (auto simp only: helper_exp_tri1)
    then show ?thesis by (simp add: bu_prod derives_if_bu)
  qed
qed

lemma exp_tri_Lang: "Lang (exp_triangular As R) A = Lang R A"
proof
  have "(B, bs) \<in> (exp_triangular As R) \<Longrightarrow> R \<turnstile> [Nt B] \<Rightarrow>* bs" for B bs
    by (simp add: exp_tri_prods_deirvable)
  then have "exp_triangular As R \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<Longrightarrow> R \<turnstile> [Nt A] \<Rightarrow>* map Tm x" for x
    using derives_simul_rules by blast
  then show "Lang (exp_triangular As R) A \<subseteq> Lang R A"  by(auto simp add: Lang_def)
next
  show "Lang R A \<subseteq> Lang (exp_triangular As R) A"
  proof (induction As R rule: exp_triangular.induct)
    case (1 R)
    then show ?case by simp
  next
    case (2 D Ds R)
    let ?R' = "exp_triangular Ds R"
    let ?X = "{(Al,Bw) \<in> ?R'. Al=D \<and> (\<exists>w B. Bw = Nt B # w \<and> B \<in> set (Ds))}"
    let ?Y = "{(D,v@w) |v w. \<exists>B. (D, Nt B # w) \<in> ?X \<and> (B,v) \<in> ?R'}"
    have F1: "exp_triangular (D#Ds) R = ?R' - ?X \<union> ?Y" by (simp add: Let_def)

    let ?S = "{x. \<exists>A w H. x = (A, [], H, w) \<and> (A, Nt H # w) \<in> ?X}"
    let ?S' = "{x. \<exists>A a1 B a2. x = (A, a1 @ Nt B # a2) \<and> (A, a1, B, a2) \<in> ?S}"
    let ?E = "{x. \<exists>A v a1 a2 B. x = (A,a1@v@a2) \<and> (A, a1, B, a2) \<in> ?S \<and> (B,v) \<in> ?R'}"
  
    have S'_eq_X: "?S' = ?X" by fastforce
    have E_eq_Y: "?E = ?Y" by fastforce

    have "\<forall>x \<in> ?S. \<exists>A a1 B a2. x = (A, a1, B, a2) \<and> (A, a1 @ Nt B # a2) \<in> ?R'" by fastforce
    have "Lang R A \<subseteq> Lang (exp_triangular Ds R) A" using 2 by simp
    also have "... \<subseteq> Lang (?R' - ?S' \<union> ?E) A"
      using exp_includes_Lang[of ?S] by auto
    also have "... = Lang (exp_triangular (D#Ds) R) A" using S'_eq_X E_eq_Y F1 by fastforce
    finally show ?case.
  qed
qed

text \<open> putting the productions into GNF via \<open>exp_triangular (solve_tri)\<close> preserves the language \<close>
theorem GNF_of_R_Lang: "\<lbrakk>Eps_free R; distinct (As @ As'); Nts R \<inter> set As' = {}; A \<notin> set As'; length As \<le> length As'\<rbrakk> 
\<Longrightarrow> Lang (exp_triangular (As' @ rev As) (solve_tri As As' R)) A = Lang R A"
proof -
  assume "Eps_free R" "distinct (As @ As')" "Nts R \<inter> set As' = {}" "A \<notin> set As'" "length As \<le> length As'"
  then have "Lang (solve_tri As As' R) A = Lang R A" using solve_tri_Lang by simp
  then show ?thesis using exp_tri_Lang[of "(As' @ rev As)"] by auto
qed

text \<open> any epsilon free Grammar can be brought into GNF while preserving the Language \<close>
theorem GNF_Lang: "\<lbrakk>Eps_free (Prods G); distinct (As @ As'); Nts (Prods G) \<subseteq> set As; Start G \<notin> set As'; length As \<le> length As'\<rbrakk>
 \<Longrightarrow> Lang (Prods G) (Start G) = Lang (exp_triangular (As' @ rev As) (solve_tri As As' (Prods G))) (Start G) 
      \<and> GNF ((exp_triangular (As' @ rev As) (solve_tri As As' (Prods G))))"
proof -
  assume assms: "Eps_free (Prods G)" "distinct (As @ As')" "Nts (Prods G) \<subseteq> set As" "Start G \<notin> set As'" "length As \<le> length As'"
  then have "Nts (Prods G) \<inter> set As' = {} \<and> (Start G) \<notin> set As'" by (auto simp add: Nts_def)
  then show ?thesis using GNF_of_R_Lang[of "(Prods G)"] GNF_of_R[of "(Prods G)"] assms by auto  
qed

text \<open> Section on Grammar size \<close>
(*WIP*)

fun bad_grammar :: "'n list \<Rightarrow> ('n, nat)Prods" where
 "bad_grammar [] = {}"
|"bad_grammar [A] = {(A, [Tm 0]), (A, [Tm 1])}"
|"bad_grammar (A#B#As) = {(A, Nt B # [Tm 0]), (A, Nt B # [Tm 1])} \<union> (bad_grammar (B#As))"


lemma test1: "A \<notin> set As \<Longrightarrow> triangular As (insert (A, Bs) R) = triangular As R"
  by (induction As arbitrary: Bs) (auto simp add: dep_on_def)

lemma test2: "distinct As \<Longrightarrow> (A, Nt A # Bs) \<notin> (bad_grammar As)"
  by (induction As rule: bad_grammar.induct) (auto simp add: dep_on_def)

lemma test3: "distinct (A#As) \<Longrightarrow> (B, Nt A # Bs) \<notin> (bad_grammar As)"
  by (induction As rule: bad_grammar.induct) (auto simp add: dep_on_def)

lemma bad_grammar_triangular: "distinct As \<Longrightarrow> triangular (rev As) (bad_grammar As)"
proof (induction As rule: bad_grammar.induct)
  case 1
  then show ?case by (auto simp add: dep_on_def)
next
  case (2 A)
  then show ?case by (auto simp add: dep_on_def)
next
  case (3 A B As)
  then have 4: "triangular ((rev As)@[B]) (bad_grammar (A#B#As))" by (auto simp add: test1)
  from 3 have 5: "triangular [A] (bad_grammar (A#B#As))" by (auto simp add: test2 dep_on_def)
  from 3 have "\<forall>C\<in>set (B#As). dep_on (bad_grammar (A#B#As)) C \<inter> set [A] = {}" by (auto simp add: dep_on_def test3)
  then show ?case using 4 5 triangular_append
    by (metis rev.simps(2) set_rev)
qed

lemma test4: "dep_on R A \<inter> set As = {} \<Longrightarrow> exp_hd A As R = R"
  by (induction As) (auto simp add: dep_on_def)


lemma exp_hd_triangular: "triangular As R \<Longrightarrow> exp_hd (hd As) (tl As) R = R"
proof (induction As)
  case Nil
  then show ?case by simp
next
  case Cons
  then show ?case by (auto simp add: test4)
qed

lemma exp_hd_triangular1: "triangular (A#As) R \<Longrightarrow> exp_hd A As R = R"
  using exp_hd_triangular 
  by (metis list.sel(1,3))

lemma solve_lrec_triangular: "A \<notin> dep_on R A \<Longrightarrow> R \<subseteq> solve_lrec A A' R"
  by (auto simp add: solve_lrec_def rm_lrec_def rrec_of_lrec_def Let_def dep_on_def)

lemma "Eps_free R \<Longrightarrow> length As \<le> length As' \<Longrightarrow> distinct (As @ As') \<Longrightarrow> triangular As R \<Longrightarrow> R \<subseteq> solve_tri As As' R"
proof (induction As As' R rule: solve_tri.induct)
  case (1 uu R)
  then show ?case by auto
next
  case (2 A As A' As' R)
  then show ?case sorry
next
  case (3 v va c)
  then show ?case by auto
qed

(*incorect as A \<longrightarrow> u gets solved to A \<longrightarrow> u and A \<longrightarrow> u @ [Nt A'] even if there is no left-recursion*)
lemma "length As \<le> length As' \<Longrightarrow> solve_tri As As' (bad_grammar As) = bad_grammar As"
  oops

lemma "length As = n \<Longrightarrow> n \<ge> 1 \<Longrightarrow> distinct (As @ As') 
\<Longrightarrow> card (bad_grammar As) = 2*n \<and> card (exp_triangular (As' @ rev As) (solve_tri As As' (bad_grammar As))) = 2 ^ n"
  sorry



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
end
