theory util
  imports Main
begin

(* Some utility lemmas that did not fit into other files. *)

(* currently unused *)
lemma append_sets_disjoint:
  assumes "a @ b = u @ v"
      and "set a \<inter> set v = {}"
      and "set b \<inter> set u = {}"
    shows "b = v"
using assms
proof (induction "a @ b" arbitrary: a u)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  then show ?case
  proof (cases "a = []")
    case True
    with Cons show ?thesis
      by simp
  next
    case False
    with Cons have "\<exists>d. a = c # d" 
      by (metis Cons_eq_append_conv)
    then obtain d where "a = c # d"
      by auto
    with Cons have cs1: "cs = d @ b" by simp
    show ?thesis
    proof (cases "u = []")
      case True
      show ?thesis using Cons.prems(1) Cons.prems(2) True by force
    next
      case False
      with Cons have "\<exists>e. u = c # e" 
        by (metis Cons_eq_append_conv)
      then obtain e where "u = c # e"
        by auto
      with Cons have cs2: "cs = e @ v" by simp
      with Cons(1)[where a=d and u=e] cs1 cs2 have "set d \<inter> set v = {} \<Longrightarrow> set b \<inter> set e = {} \<Longrightarrow> b = v" by simp

      moreover from \<open>a = c # d\<close> have "set d \<subseteq> set a" by auto
      with \<open>set a \<inter> set v = {}\<close> have "set d \<inter> set v = {}" by auto
      moreover from \<open>u = c # e\<close> have "set e \<subseteq> set u" by auto
      with \<open>set b \<inter> set u = {}\<close> have "set b \<inter> set e = {}" by auto

      ultimately show ?thesis by auto
    qed
  qed
qed


lemma append_sets_disjoint_middle:
  assumes "a @ A # b = u @ v"
      and "set a \<inter> set v = {}"
      and "A \<notin> set u"
    shows "A # b = v"
proof -
  from assms show ?thesis
  proof (induction "a @ A # b" arbitrary: a A b u v)
    case Nil
    then show ?case by auto
  next
    case (Cons x1 xs)
    then show ?case
    proof (cases a)
      case Nil
      with Cons have "A # b = u @ v" by simp
      then show ?thesis
        using Cons.prems(3) Cons_eq_append_conv by fastforce
    next
      case innerCons: Cons
      show ?thesis
        using Cons innerCons by (cases u,force+)
    qed
  qed
qed


(* custom integer induction rule which also has a case for 1 *)
lemma nat_induct_with_1 [case_names 0 1 Suc]:
  fixes n
  assumes "P 0" "P 1" and "\<And>n. P 1 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
  using assms nat_induct by auto


end
