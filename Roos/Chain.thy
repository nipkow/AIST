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





end