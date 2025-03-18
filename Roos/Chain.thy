theory Chain
imports Main
begin


fun chain :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool\<close> where
\<open>chain R [] = True\<close> | 
\<open>chain R [x] = True\<close> | 
\<open>chain R (x # y # zs) = (R x y \<and> chain R (y#zs))\<close>



lemma chain_Cons[intro]: \<open>chain R xs \<Longrightarrow> R x (hd xs) \<Longrightarrow> chain R (x # xs)\<close>
apply(induction R xs rule: chain.induct) by auto


lemma chain_append[intro]: \<open>chain R xs \<Longrightarrow> chain R ys \<Longrightarrow> R (last xs) (hd ys) \<Longrightarrow> chain R (xs@ys)\<close>
apply(induction R xs rule: chain.induct) by auto

lemma [simp]: \<open>chain R [x, y] = R x y\<close> by auto

lemma \<open>\<not>(R x y) \<Longrightarrow> \<not>(chain R [x, y])\<close> by simp


lemma chain_drop_right[elim]:
assumes \<open>chain R (xs@ys)\<close>
obtains \<open>chain R xs\<close>
using assms apply(induction R xs rule: chain.induct) by auto

lemma chain_drop_left_cons: \<open>chain R (x # xs) \<Longrightarrow> chain R xs\<close>
apply(induction xs) by auto

lemma chain_drop_left[elim]:
assumes \<open>chain R (xs@ys)\<close>
obtains \<open>chain R ys\<close>
using assms proof(induction xs arbitrary: ys)
  case (Cons x xs)
  then show ?case using chain_drop_left_cons[of R x \<open>xs@ys\<close>] by auto
qed auto



lemma chain_iff: \<open>(chain R xs) =  (\<forall>(a,b) \<in> set (zip xs (tl xs)). R a b )\<close>
apply(induction R xs rule: chain.induct) by auto

lemma chain_bridge_one[intro]: \<open>chain R (xs @ [x]) \<Longrightarrow> chain R (x # ys) \<Longrightarrow> chain R (xs @ x # ys)\<close>
apply(induction R xs rule: chain.induct) by auto

lemma chain_bridge[intro]: \<open>w \<noteq> [] \<Longrightarrow> chain R w \<Longrightarrow> chain R (xs@w) \<Longrightarrow> chain R (w@ys) \<Longrightarrow> chain R (xs@w@ys)\<close>
proof(induction w arbitrary: xs)
  case Nil
  then show ?case sorry
next
  case (Cons a w)
  then show ?case
  proof(cases \<open>w = []\<close>)
    case True
    then show ?thesis using Cons by auto
  next
    case False
    have \<open>chain R (w @ ys)\<close> and \<open>chain R w\<close> using Cons.prems(4) chain_drop_left_cons by fastforce+
    then show \<open>chain R (xs @ (a # w) @ ys)\<close> using Cons.IH Cons.prems(3) False by (metis append.assoc append_Cons append_Nil)
  qed
qed
 
lemma chainE[elim]: 
assumes \<open>chain R (xs@x#[y]@ys)\<close>
obtains \<open>R x y\<close>
using assms by auto

lemma chainE_hd[elim]:
assumes \<open>chain R (xs@x#y@ys)\<close>
and \<open>y \<noteq> []\<close>
obtains \<open>R x (hd y)\<close>
using assms by (metis Cons_eq_appendI chain.simps(3) chain_drop_left list.exhaust_sel)
end