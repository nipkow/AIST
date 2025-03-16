theory AdjacentProperties
imports Main
begin

(* Define a predicate for adjacent elements *)
definition adjacent_prop :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "adjacent_prop xs P \<equiv> \<forall>i. i < length xs - 1 \<longrightarrow> P (xs ! i) (xs ! (i + 1))"

lemma adjacent_propI[intro]:
assumes \<open>\<And>i. i < length xs -1 \<Longrightarrow> P (xs ! i) (xs ! (i + 1))\<close>
shows \<open>adjacent_prop xs P\<close>
using assms unfolding adjacent_prop_def by blast

lemma adjacent_propD[dest]:
assumes \<open>adjacent_prop xs P\<close>
and \<open>i < length xs -1\<close>
shows \<open>P (xs ! i) (xs ! (i + 1))\<close>
using assms unfolding adjacent_prop_def by blast

lemmas adjacent_propE = adjacent_propD[elim_format]


text\<open>Prove that concatenation preserves the property (if it holds at the boundarys).\<close>
lemma adjacent_prop_append[intro]:
  assumes "adjacent_prop xs P" 
  assumes "adjacent_prop ys P"
  assumes "P (last xs) (hd ys)"
  shows "adjacent_prop (xs @ ys) P"
proof -
  consider (xs_empty) \<open>xs = []\<close> | (ys_empty) \<open>ys = []\<close> | (both_not_empty) \<open>xs \<noteq> [] \<and> ys \<noteq> []\<close> by blast
  then show ?thesis
  proof(cases)
    case xs_empty
    then show ?thesis by (simp add: assms(2))
  next
    case ys_empty
    then show ?thesis by (simp add: assms(1))
  next
    case both_not_empty
    then show ?thesis
    proof
    assume not_empty: \<open>xs \<noteq> []\<close> \<open>ys \<noteq> []\<close>
    have "\<forall>i. i < length (xs @ ys) - 1 \<longrightarrow> P ((xs @ ys) ! i) ((xs @ ys) ! (i + 1))"
  proof (intro allI impI)
    fix i
    assume "i < length (xs @ ys) - 1"
    
    consider (in_xs) "i < length xs - 1" | 
             (boundary) "i = length xs - 1" |
             (in_ys) "i \<ge> length xs" by linarith
    
    thus "P ((xs @ ys) ! i) ((xs @ ys) ! (i + 1))"
    proof cases
      case in_xs
      then have "i < length xs - 1" by simp
      hence "P (xs ! i) (xs ! (i + 1))" using assms(1) unfolding adjacent_prop_def by blast
      moreover have "(xs @ ys) ! i = xs ! i" using in_xs by (simp add: nth_append_left)
      moreover have "(xs @ ys) ! (i + 1) = xs ! (i + 1)" using in_xs by (simp add: nth_append_left)
      ultimately show ?thesis by simp
    next
      case boundary
      then have "i = length xs - 1" by simp
      hence "i + 1 = length xs" using \<open>xs \<noteq> []\<close> by simp

      have "xs ! i = last xs" using boundary assms(3) by (simp add: last_conv_nth not_empty(1))

      moreover have "(xs @ ys) ! (i + 1) = ys ! 0" using boundary by (metis \<open>i + 1 = length xs\<close> cancel_comm_monoid_add_class.diff_cancel dual_order.refl nth_append_right)
      moreover have "ys ! 0 = hd ys" by (simp add: hd_conv_nth not_empty(2))
      ultimately show ?thesis by (metis \<open>i + 1 = length xs\<close> assms(3) less_add_one nth_append_left)
    next
      case in_ys
      then have "i \<ge> length xs" by simp
      let ?j = "i - length xs"
      
      have h1: "(xs @ ys) ! i = ys ! ?j" using in_ys by (simp add: nth_append)
      have h2: "(xs @ ys) ! (i + 1) = ys ! (?j + 1)" using in_ys by (simp add: Suc_diff_le nth_append)
      
      have "?j < length ys - 1" using `i < length (xs @ ys) - 1` in_ys by simp
      hence h3: "P (ys ! ?j) (ys ! (?j + 1))" using assms(2) unfolding adjacent_prop_def by blast
      
      show ?thesis using h1 h2 h3 by presburger
    qed
  qed
  thus ?thesis unfolding adjacent_prop_def by blast
qed
  qed
  qed



corollary adjacent_prop_append2[intro]:
  assumes "adjacent_prop xs P" 
  assumes "adjacent_prop ys P"
  assumes "adjacent_prop zs P"
  assumes "P (last xs) (hd ys)"
  assumes "P (last ys) (hd zs)"
  and \<open>ys \<noteq> []\<close>
  shows "adjacent_prop (xs @ ys @ zs) P"
proof-
  have \<open>adjacent_prop (xs@ys) P\<close> by (simp add: adjacent_prop_append assms(1,2,4))
  moreover have \<open>last (xs @ ys) = last ys\<close> using \<open>ys \<noteq> []\<close> by simp
  ultimately show \<open>adjacent_prop (xs@ys@zs) P\<close> using adjacent_prop_append[of \<open>xs@ys\<close> P zs] assms by simp
qed


end
