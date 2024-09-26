theory GNF
imports CFG
begin

type_synonym 'a ix = "'a * nat"

fun rt :: "('n,'t)symbs \<Rightarrow> bool" where
"rt [] = True" |
"rt (T _ # _) = True" |
"rt _ = False"

definition rtps :: "('n,'t)prods \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> ps. rt(snd p))"

definition Lnt :: "('n, 't) prods \<Rightarrow> 'n set" where
"Lnt P = {B. \<exists>A w. (A, N B # w) \<in> P}"

lemma Lnt_image_filter:
  "Lnt P = (\<lambda>(_,w). case w of N A # _ \<Rightarrow> A) ` Set.filter (\<lambda>(_,w). \<exists>A u. w = N A # u) P"
by(fastforce simp: Lnt_def image_iff Bex_def)

lemma finite_Lnt: "finite P \<Longrightarrow> finite(Lnt P)"
unfolding Lnt_image_filter by auto

lemma rtps_if_Lnt_empty: "Lnt P = {} \<Longrightarrow> rtps P"
by(auto simp: Lnt_def rtps_def elim!:  rt.elims(3)) (metis rt.elims(3))

theorem GNF:
fixes P :: "('n ix,'t)prods"
assumes "finite P"
shows "\<exists>P'::('n ix,'t)prods. Lang S P' = Lang S P \<and> rtps P'"
using assms proof (induction "card (Lnt P)" arbitrary: P)
  case 0
  then have "rtps P" using finite_Lnt[of P] by (auto simp add: rtps_if_Lnt_empty)
  then show ?case by blast
next
  case (Suc n)
  then obtain A M where "Lnt P = insert A M" "card M = n"
    by (metis card_eq_SucD)
  let ?P = undefined
  have "finite ?P" sorry
  moreover
  have "Lang S ?P = Lang S P" sorry
  moreover
  have "Lnt ?P = M" sorry
  ultimately show ?case using Suc(1)[of ?P] \<open>card M = n\<close> by auto
qed

end