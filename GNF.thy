theory GNF
imports CFG
begin

fun nt :: "('n,'t)symb \<Rightarrow> 'n set" where
"nt(N A) = {A}" |
"nt(T a) = {}"

fun rt :: "('n,'t)symbs \<Rightarrow> bool" where
"rt [] = True" |
"rt (T _ # _) = True" |
"rt _ = False"

definition rtps :: "('n,'t)prods \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> ps. rt(snd p))"

definition Lnt :: "('n, 't) prods \<Rightarrow> ('n * 'n * ('n,'t)symbs)set" where
"Lnt P = {(A,B,w). (A, N B # w) \<in> P}"

lemma [code]: "Lnt P = \<Union> ((\<lambda>(A,w). case w of N B#v \<Rightarrow> {(A,B,v)} | _ \<Rightarrow> {}) ` P)"
  by (auto simp: Lnt_def split: list.splits symb.splits)

definition rule where "rule = (\<lambda>(A, B, w). (A, N B # w))"

lemma Lnt_Un: "Lnt (A \<union> B) = Lnt A \<union> Lnt B"
by(auto simp: Lnt_def)

lemma Lnt_Diff: "Lnt (A - B) = Lnt A - Lnt B"
by(auto simp: Lnt_def)

lemma Lnt_rule: "Lnt(rule ` S) = S"
by(auto simp: Lnt_def rule_def image_def split:prod.splits)

(*
fun lnt :: "('n,'t)prod \<Rightarrow> 'n option" where
"lnt(_,N A # _) = Some A" |
"lnt _ = None"

definition "has_lnt p = (\<exists>A u. snd p = N A # u)"

lemma has_lnt_iff_lnt_split_Some: "has_lnt p = (\<exists>A. lnt_split p = Some A)"
by(cases p rule: lnt_split.cases) (auto simp: has_lnt_def)
*)
declare [[simproc add: finite_Collect]]

lemma inj_Lnt: "inj rule"
by(simp add: inj_def rule_def)

lemma finite_Lnt: "finite P \<Longrightarrow> finite(Lnt P)"
by(auto simp: Lnt_def finite_vimageI inj_Lnt[simplified rule_def])

lemma rtps_if_Lnt_empty: "Lnt P = {} \<Longrightarrow> rtps P"
by(auto simp: Lnt_def rtps_def elim!:  rt.elims(3)) (metis rt.elims(3))

definition eps_free where "eps_free R = (\<forall>(_,r) \<in> R. r \<noteq> [])"

lemma "\<exists>R'. eps_free R' \<and> (\<forall>A. Lang R' A = Lang R A - {[]})"
sorry

lemma eps_free_Nil: "eps_free R \<Longrightarrow> (A,[]) \<notin> R"
sorry

lemma eps_freeE_Cons: "eps_free R \<Longrightarrow> (A,w) \<in> R \<Longrightarrow> \<exists>a u. w = a#u"
sorry

definition "rhs1 = fst o snd"
definition "Rhs1 R = rhs1 ` Lnt R"

lemma lem: "A - {x. P x} = {x\<in>A. \<not>P x}"
by auto

lemma Rhs1_subsetD: "Rhs1 R \<subseteq> M \<Longrightarrow> (A, N B # w) \<in> R \<Longrightarrow> B \<in> M"
sorry
(*
definition "uphill R As \<longleftrightarrow>
  (\<forall>i j. i < length As \<longrightarrow> j < length As \<longrightarrow>
  (\<exists>w. (As!i,As!j,w) \<in> Lnt R) \<longrightarrow> i < j)"
*)
fun uphill where
  "uphill R [] As = True" |
  "uphill R (A#Ps) As =
 ((\<forall>B w. (A,B,w) \<in> Lnt R \<longrightarrow> B \<in> set As) \<and> uphill R Ps (A#As))"

lemma assumes "uphill R Ps As" and "P \<in> set Ps" and "(P,B,w) \<in> Lnt R"
  shows "B \<in> set Ps"
  using assms(1,2) proof (induction R Ps As rule: uphill.induct)
  case (1 R As)
  then show ?case by simp
next
  case (2 R A Ps As)
  then show ?case apply auto sorry
qed

lemma uphill_Un:
  "uphill (R \<union> S) Ps As \<longleftrightarrow> uphill R Ps As \<and> uphill S Ps As"
  apply (induction R Ps As rule: uphill.induct) by (auto simp: Lnt_Un)

lemma uphill_UN:
"uphill (\<Union>RR) Ps As \<longleftrightarrow> (\<forall>R \<in> RR. uphill R Ps As)"
  apply (induction "\<Union>RR" Ps As rule: uphill.induct)
  by (auto simp: Lnt_def)

lemma Lnt_subset: "R \<subseteq> S \<Longrightarrow> Lnt R \<subseteq> Lnt S"
  by (auto simp: Lnt_def)

lemma uphill_subset:
  "R \<subseteq> S \<Longrightarrow> uphill S Ps As \<Longrightarrow> uphill R Ps As"
proof (induction S Ps As arbitrary: R rule: uphill.induct)
  case (1 S As)
  then show ?case by simp
next
  case (2 S A Ps As)
  then show ?case by (fastforce dest: Lnt_subset)
qed

lemma uphill_triv:
  assumes "\<And>l w. (l,w)\<in>R \<Longrightarrow> l \<notin> set Ps"
  shows "uphill R Ps As"
  using assms apply (induct Ps arbitrary: As) by (auto simp: Lnt_def)

lemma Rhs1_subset: "R \<subseteq> S \<Longrightarrow> Rhs1 R \<subseteq> Rhs1 S"
  by (auto simp: Rhs1_def Lnt_def)

lemma Rhs1_Un: "Rhs1 (R \<union> S) = Rhs1 R \<union> Rhs1 S"
  by (auto simp: Rhs1_def Lnt_def)

definition remove_self_rec_set where
  "remove_self_rec_set R A A' = (
  let X = {(A,N A # w) | w. (A, N A # w) \<in> R} in
  R - X \<union> {(A, w@[N A']) |w. (A,w) \<in> R - X} \<union>
  \<Union>{{(A',w), (A',w@[N A'])} | w. (A,N A # w) \<in> R \<and> w \<noteq> []})"

definition "diff_list = fold removeAll"

lemma set_diff_list[simp]: "set(diff_list xs ys) = set ys - set xs"
unfolding diff_list_def
proof(induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed 

fun starts_with where "starts_with A (N B # w) \<longleftrightarrow> A = B"
  | "starts_with _ _ = False"

definition Rhs1s where "Rhs1s R = [A. (B,N A # w) \<leftarrow> R]"

lemma set_Rhs1s: "set (Rhs1s R) = Rhs1 (set R)"
  by (auto simp: Rhs1s_def Rhs1_def Lnt_def rhs1_def image_Collect)

definition "eps_free_list R = (\<forall>(A,w) \<in> set R. w \<noteq> [])"

definition unwind where
  "unwind R A A' = (
  let X = [(A,w). (B,w) \<leftarrow> R, B = A \<and> starts_with A w] in
  diff_list X R @
  [(A, w@[N A']). (B,w) \<leftarrow> R, B = A \<and> \<not> starts_with A w] @
  concat [[(A',w), (A',w@[N A'])]. (B,N C # w) \<leftarrow> R, B = A \<and> C = A \<and> w \<noteq> []])"

definition Rex :: "(int,int) prod list"
  where "Rex = [
  (1,[N 2, N 2]), (1, [T 0]),
  (2, [N 2, N 2, N 2]), (2, [T 0, N 2]), (2, [T 1])]"

definition Rex2 :: "(int,int) prod list"
  where "Rex2 = [
  (1, [N 2, T 0]),
  (2, [N 1, T 2]), (2, [T 1, N 1]), (2, [T 3])]"

value "unwind Rex 2 3"

definition Nts where "Nts R = concat [A#[B. N B \<leftarrow> w]. (A,w) \<leftarrow> R]"

lemma assumes "A' \<notin> set (Nts R)"
  shows "(A,N A # w) \<notin> set (unwind R A A')"
  sorry

definition "expand_rec R A = (
  let X = filter (\<lambda>(B,w). starts_with A w) R in
  diff_list X R @ [(B,v@w). (B,N C # w) \<leftarrow> R, C = A, (D,v) \<leftarrow> R, D = A]
)"

value "expand_rec Rex2 1"

lemma
  assumes "eps_free_list R"
    and "\<forall>(B,w) \<in> set R. B = A \<longrightarrow> \<not>starts_with A w"
    and "(B,w) \<in> set (expand_rec R A)"
  shows "\<not>starts_with A w"
  sorry

fun hdnt where
    "hdnt (N A#w) = Some A"
  | "hdnt _ = None"

definition "expand_all R As = (
  [(B,w). (B,w) \<leftarrow> R, hdnt w \<notin> Some ` set As] @
  [(B,v@w). (B,N C # w) \<leftarrow> R, C \<in> set As, (D,v) \<leftarrow> R, D = C]
)"

definition "unwind_expand R As A A' = expand_all (unwind R A A') (As)"

definition "solved R As \<longleftrightarrow>
  (\<forall> B \<in> set As. \<forall>(A,w) \<in> set R. \<not>starts_with B w)"

lemma
  assumes "eps_free_list R" and "A' \<notin> set (Nts R) \<union> set As"
    and "solved R As"
  shows "solved (unwind_expand R As A A') As"
  sorry

definition step
  where "step R As A A' = expand_all (unwind_expand R As A A') [A]"

lemma
  assumes "eps_free_list R" and "A' \<notin> set (Nts R) \<union> set As"
    and "solved R As"
  shows "solved (step R As A A') (A'#A#As)"
  sorry

value "unwind_expand [(1,[N 1 :: (int,int)symb, N 1])] [] 1 2"




locale foo = fixes R :: "(nat,nat) prod set" and A :: "nat" and Ps :: "nat list"
begin

definition X where "X = rule ` {(B,A,w) | B w. (B,A,w) \<in> Lnt R \<and> B \<noteq> A}"

definition R'2 where
  "R'2 = {(C, w@w') | C w w'. (C,N A # w') \<in> R \<and> (A,w) \<in> R }"

definition R' where "R' = R - X \<union> R'2"

context
  assumes inv: "Rhs1 R \<subseteq> set (A#Ps)" and eps: "eps_free R"
begin

lemma Rhs1R'2: "Rhs1 R'2 \<subseteq> set (A # Ps)"
  using inv eps
  by (auto simp: R'2_def Rhs1_def Lnt_def rhs1_def Cons_eq_append_conv eps_free_Nil image_Collect)

lemma invR': "Rhs1 R' \<subseteq> set (A#Ps)"
  using inv Rhs1R'2 Rhs1_subset
  apply (auto simp: R'_def  Rhs1_Un)
  by (smt (verit) Diff_subset Rhs1_subset insert_iff subsetD)

lemma assumes "(B,A,w) \<in> Lnt R'" shows "B = A"

lemma 
fixes R :: "('n,'t)prods" and new :: "'n set \<Rightarrow> 'n"
assumes "\<And>X. finite X \<Longrightarrow> new (X) \<notin> X"
assumes "finite R" and "eps_free R" and "uphill R Ps As"
  and "distinct (Ps @ As)"
shows "\<exists>R'. Lang S R' = Lang S R \<and> uphill R' (As@Ps) []"
using assms(2-) proof (induction As arbitrary: R Ps)
  case Nil
  then show ?case by auto
next
  case (Cons A As)
  then have "A \<notin> set Ps" by auto
(*  from \<open>distinct (A#Ps)\<close> have "distinct Ps" by simp *)
  let ?X = "rule ` {(A',B,w) \<in> Lnt R. A' = A \<and> B \<in> set Ps}"
  let ?R'2 = "{(A, w@w') | w w'. \<exists>B. (A,N B # w') \<in> R \<and> (B,w) \<in> R \<and> B \<in> set Ps }"
  define R' where "R' = R - ?X \<union> ?R'2"
  have "uphill (R - ?X) Ps (A#As)"
    using uphill_subset[OF _ \<open>uphill R Ps (A # As)\<close>] by auto
  moreover
  have R'2: "uphill ?R'2 Ps (A#As)" using \<open>A \<notin> set Ps\<close> 
    by (auto simp: Lnt_def intro:uphill_triv)
  ultimately
  have invR': "uphill R' Ps (A#As)"
    by (auto simp: R'_def uphill_Un simp del: uphill.simps)
  have "eps_free R'" sorry
  have "\<forall>B w. (A,B,w) \<in> Lnt (R - ?X) \<longrightarrow> B=A \<or> B \<notin> set Ps"
    by(auto simp add: Lnt_Diff Lnt_rule)
  moreover
  have "B=A \<or> B \<in> set As" if asm: "(A,B,w) \<in> Lnt ?R'2" for B w
  proof -
    from asm \<open>eps_free R\<close>
    obtain w1 w2 C
      where "(A,N C#w1) \<in> R" "(C,N B#w2) \<in> R" "w = w2@w1" "C \<in> set Ps"
      by (auto simp: Lnt_def rule_def image_Collect  split: prod.splits dest:eps_freeE_Cons)
    with \<open>uphill R Ps (A#As)\<close> show ?thesis
      apply(auto simp: Lnt_def rule_def image_Collect split: prod.splits dest:eps_free_Nil)
      by (mes on R'2 that uphill.simps(2))
  qed
  then have 1: "B \<in> set (A # As)" if asm: "(A,B,w) \<in> Lnt R'" for B w
    using asm unfolding R'_def apply (auto simp: Lnt_Un Lnt_def image_Collect rule_def)
*)
  have R'R: "Lang S R' = Lang S R"
    sorry
  define A' where "A' = new (\<Union>(A,w) \<in> R. insert A (\<Union>(set(map nt w))))"
  have A': "A' \<noteq> A" "A' \<notin> set As" "A' \<notin> set Ps" sorry
  let ?X' = "{(A,N A#w) | w. (A,N A#w) \<in> R'}"
  let ?R''2 = "{(A,w@[N A']) | w . (A,w) \<in> R'-?X'}"
  let ?R''3 = "\<Union>{{(A',w), (A',w@[N A'])} | w. (A,N A # w) \<in> R' \<and> w \<noteq> []}"
  define R'' where "R'' = R'-?X' \<union> ?R''2 \<union> ?R''3"
  have R''R': "Lang S R'' = Lang S R'"
    sorry
  have "uphill (R'-?X') (A#Ps) As"
    using uphill_subset[OF _  invR'] apply (auto simp: Lnt_def) sorry
  moreover have "uphill ?R''2 (A#Ps) As"
    apply (auto simp: Lnt_def Cons_eq_append_conv) using invR' \<open>eps_free R'\<close> Cons.prems(4)
       apply (auto simp: Lnt_def dest: eps_free_Nil intro:)
    apply (intro uphill_triv) by auto
  moreover have "uphill ?R''3 (A#Ps) As" using A'
    by (auto simp add: uphill_UN Lnt_def Cons_eq_append_conv intro: uphill_triv)
  ultimately
  have invR'': "uphill R'' (A#Ps) As"
    by (auto simp add: R''_def uphill_Un simp del: uphill.simps)
  then have *: "uphill R'' Ps (A#As)" by simp
  have "finite R''" sorry
  have \<open>eps_free R''\<close> sorry
  from Cons.IH[OF \<open>finite R''\<close> \<open>eps_free R''\<close> * \<open>distinct Ps\<close>] R''R' R'R 
  show ?case apply metis


  let ?X''= "{p \<in> R''. \<exists>B w. p = (A',N B#w) \<and> B \<notin> set As}"
  let ?R = "R'' - ?X'' \<union> {(A', w'@w) | w w'. \<exists>B. (A',N B # w) \<in> ?X'' \<and> (B,w') \<in> R''}"
  have "B = A' \<or> C \<in> set As" if asm: "(B, N C # w) \<in> R''" for B C w
  proof -
    from asm have "(B, N C # w) \<in> ?R''3 \<Longrightarrow> B = A'" by(auto)
    moreover
    have "(B, N C # w) \<in> R'-?X' \<Longrightarrow> ?thesis"
      using Cons.prems(2) invR' 
 apply(auto simp:  Cons_eq_append_conv image_Collect rule_def dest: eps_freeE Rhs1_subsetD)
apply(au to simp add: R'_def image_Collect rule_def)[1]
    moreover
    have "(B, N x # w) \<in> ?R''2 \<Longrightarrow> ?thesis"
      using  Cons.prems(2)
      by(fa stforce simp: R'_def image_Collect rule_def Cons_eq_append_conv eps_freeE)
    ultimately show ?thesis using asm unfolding R''_def by bl ast
  qed
  have 1: "\<exists>a b. (a, N x # b) \<in> R" if asm: "(B, N x # w) \<in> R''" "B \<noteq> A'" for B w x
  proof -
    from asm(2) have "(B, N x # w) \<notin> ?R''3" by(auto)
    moreover
    have "(B, N x # w) \<in> R'-?X' \<Longrightarrow> ?thesis"
      using Cons.prems(2) by(auto simp: R'_def Cons_eq_append_conv dest: eps_freeE)
    moreover
    have "(B, N x # w) \<in> ?R''2 \<Longrightarrow> ?thesis"
      using  Cons.prems(2)
      by(fastforce simp: R'_def image_Collect rule_def Cons_eq_append_conv eps_freeE)
    ultimately show ?thesis using asm unfolding R''_def by blast
  qed
  have 2: "\<exists>a b. (a, N x # b) \<in> R" if asm: "(B, N x # w) \<in> R''" "x \<in> set As" for B w x
  proof -
    from asm(2) have "(B, N x # w) \<notin> ?R''3" by(auto)
    moreover
    have "(B, N x # w) \<in> R'-?X' \<Longrightarrow> ?thesis"
      using Cons.prems(2) by(auto simp: R'_def Cons_eq_append_conv dest: eps_freeE)
    moreover
    have "(B, N x # w) \<in> ?R''2 \<Longrightarrow> ?thesis"
      using  Cons.prems(2)
      by(fastforce simp: R'_def image_Collect rule_def Cons_eq_append_conv eps_freeE)
    ultimately show ?thesis using asm unfolding R''_def by blast
  qed
  have "rhs1 ` Lnt (R'' - ?X'') \<subseteq> rhs1 ` Lnt R - {A}"  using A'
apply( simp add: Lnt_Un  image_Un lem)
apply(auto simp add: Lnt_def image_Collect)
 using A'
  then have "(fst o snd) ` Lnt (?R'' - ?X'') \<subseteq> set As" using Cons.prems(3) by auto
  have "(fst o snd) ` Lnt ?R \<subseteq> set As"

 sorry

  have "finite ?R" sorry
  moreover
  have "eps_free ?R" sorry
  moreover
  have "Lang S ?R = Lang S R" sorry
  moreover
  ultimately show ?case using Cons.IH[of ?R] Cons.prems(4) by auto
  then show ?case sorry
qed

theorem GNF:
fixes R :: "('n,'t)prods" and new :: "'n set \<Rightarrow> 'n"
assumes "\<And>X. finite X \<Longrightarrow> new (X) \<notin> X"
assumes "finite R" and "eps_free R" and "Rhs1 R \<subseteq> set As" "distinct As"
shows "\<exists>R'::('n ,'t)prods. Lang S R' = Lang S R \<and> rtps R'"
using assms(2-) proof (induction As arbitrary: R)
  case Nil
  then have "rtps R" using finite_Lnt[of R] by (auto simp: Rhs1_def rtps_if_Lnt_empty)
  then show ?case by blast
next
  case (Cons A As)
  let ?X = "rule ` {(A',B,w) \<in> Lnt R. A' = A \<and> A \<noteq> B \<and> B \<notin> set As}"
  let ?R'2 = "{(A, w@w') | w w'. \<exists>B. (A,N B # w') \<in> R \<and> (B,w) \<in> R \<and> B \<noteq> A \<and> B \<notin> set As }"
  define R' where "R' = R - ?X \<union> ?R'2"
  have invR': "Rhs1 R' \<subseteq> set (A#As)" using Cons.prems unfolding R'_def Rhs1_def
    apply(simp add: Lnt_Un Lnt_Diff Lnt_rule image_Un)
    apply (auto simp: Lnt_def image_def eps_free_def rhs1_def split: prod.splits)
    by auto
  have "\<forall>B w. (A,B,w) \<in> Lnt (R - ?X) \<longrightarrow> B=A \<or> B \<in> set As"
    by(auto simp add: Lnt_Diff Lnt_rule)
  moreover
  have "B=A \<or> B \<in> set As" if asm: "(A,B,w) \<in> Lnt ?R'2" for B w
  proof -
    from asm \<open>eps_free R\<close> obtain w1 w2 C where "(A,N C#w1) \<in> R" "C \<noteq> A" "(C,N B#w2) \<in> R" "w = w2@w1"
      by (auto simp: Lnt_def rule_def image_Collect  split: prod.splits dest:eps_freeE_Cons)
    thus ?thesis
      using Cons.prems(3) by(auto simp: Lnt_def rule_def image_Collect split: prod.splits dest:eps_freeE)
  qed
  ultimately have 1: "B \<in> set (A # As)" if asm: "(A,B,w) \<in> Lnt R'" for B w
    using asm unfolding R'_def by (auto simp: Lnt_Un)
  have "Lang S R' = Lang S R"
    sorry
  define A' where "A' = new (\<Union>(A,w) \<in> R. insert A (\<Union>(set(map nt w))))"
  have A': "A' \<noteq> A" "A' \<notin> set As" sorry
  let ?X' = "{(A,N A#w) | w. (A,N A#w) \<in> R'}"
  let ?R''2 = "{(A,w@[N A']) | w . (A,w) \<in> R'-?X'}"
  let ?R''3 = "\<Union>{{(A',w), (A',w@[N A'])} | w. (A,N A # w) \<in> R' \<and> w \<noteq> []}"
  define R'' where "R'' = R'-?X' \<union> ?R''2 \<union> ?R''3"
  have R''R': "Lang S R'' = Lang S R'"
    sorry
  let ?X''= "{p \<in> R''. \<exists>B w. p = (A',N B#w) \<and> B \<notin> set As}"
  let ?R = "R'' - ?X'' \<union> {(A', w'@w) | w w'. \<exists>B. (A',N B # w) \<in> ?X'' \<and> (B,w') \<in> R''}"
  have "B = A' \<or> C \<in> set As" if asm: "(B, N C # w) \<in> R''" for B C w
  proof -
    from asm have "(B, N C # w) \<in> ?R''3 \<Longrightarrow> B = A'" by(auto)
    moreover
    have "(B, N C # w) \<in> R'-?X' \<Longrightarrow> ?thesis"
      using Cons.prems(2) invR' 
 apply(auto simp:  Cons_eq_append_conv image_Collect rule_def dest: eps_freeE Rhs1_subsetD)
apply(auto simp add: R'_def image_Collect rule_def)[1]
    moreover
    have "(B, N x # w) \<in> ?R''2 \<Longrightarrow> ?thesis"
      using  Cons.prems(2)
      by(fastforce simp: R'_def image_Collect rule_def Cons_eq_append_conv eps_freeE)
    ultimately show ?thesis using asm unfolding R''_def by bl ast
  qed
  have 1: "\<exists>a b. (a, N x # b) \<in> R" if asm: "(B, N x # w) \<in> R''" "B \<noteq> A'" for B w x
  proof -
    from asm(2) have "(B, N x # w) \<notin> ?R''3" by(auto)
    moreover
    have "(B, N x # w) \<in> R'-?X' \<Longrightarrow> ?thesis"
      using Cons.prems(2) by(auto simp: R'_def Cons_eq_append_conv dest: eps_freeE)
    moreover
    have "(B, N x # w) \<in> ?R''2 \<Longrightarrow> ?thesis"
      using  Cons.prems(2)
      by(fastforce simp: R'_def image_Collect rule_def Cons_eq_append_conv eps_freeE)
    ultimately show ?thesis using asm unfolding R''_def by blast
  qed
  have 2: "\<exists>a b. (a, N x # b) \<in> R" if asm: "(B, N x # w) \<in> R''" "x \<in> set As" for B w x
  proof -
    from asm(2) have "(B, N x # w) \<notin> ?R''3" by(auto)
    moreover
    have "(B, N x # w) \<in> R'-?X' \<Longrightarrow> ?thesis"
      using Cons.prems(2) by(auto simp: R'_def Cons_eq_append_conv dest: eps_freeE)
    moreover
    have "(B, N x # w) \<in> ?R''2 \<Longrightarrow> ?thesis"
      using  Cons.prems(2)
      by(fastforce simp: R'_def image_Collect rule_def Cons_eq_append_conv eps_freeE)
    ultimately show ?thesis using asm unfolding R''_def by blast
  qed
  have "rhs1 ` Lnt (R'' - ?X'') \<subseteq> rhs1 ` Lnt R - {A}"  using A'
apply( simp add: Lnt_Un  image_Un lem)
apply(auto simp add: Lnt_def image_Collect)
 using A'
  then have "(fst o snd) ` Lnt (?R'' - ?X'') \<subseteq> set As" using Cons.prems(3) by auto
  have "(fst o snd) ` Lnt ?R \<subseteq> set As"

 sorry

  have "finite ?R" sorry
  moreover
  have "eps_free ?R" sorry
  moreover
  have "Lang S ?R = Lang S R" sorry
  moreover
  ultimately show ?case using Cons.IH[of ?R] Cons.prems(4) by auto
qed

end