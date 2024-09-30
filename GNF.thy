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

lemma eps_freeE: "eps_free R \<Longrightarrow> (A,[]) \<notin> R"
sorry

lemma eps_freeE_Cons: "eps_free R \<Longrightarrow> (A,w) \<in> R \<Longrightarrow> \<exists>a u. w = a#u"
sorry

definition "rhs1 = fst o snd"
definition "Rhs1 R = rhs1 ` Lnt R"

lemma lem: "A - {x. P x} = {x\<in>A. \<not>P x}"
by auto

lemma Rhs1_subsetD: "Rhs1 R \<subseteq> M \<Longrightarrow> (A, N B # w) \<in> R \<Longrightarrow> B \<in> M"
sorry

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