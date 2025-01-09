theory Unit
imports
  Closure
  Epsilon
  "../CFG"
begin

hide_const (open) Topological_Spaces.closed

text \<open>Unit closure\<close>

definition unit_subst :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) Prods" where
"unit_subst P = {(A, \<alpha>). \<exists> B. (A,[Nt B]) \<in> P \<and> (B,\<alpha>) \<in> P}"

definition "unit_closure P = closure unit_subst P"

lemma mono_unit_subst: "mono unit_subst"
unfolding unit_subst_def mono_def by fastforce

(* One direction is easy *)
lemma unit_closure_incr: "P \<subseteq> unit_closure P"
unfolding unit_closure_def by (simp add: closure_incr)

lemma Lang_unit_closure_incr: "Lang P A \<subseteq> Lang (unit_closure P) A"
by (simp add: unit_closure_incr Lang_mono)

lemma derivs_if_derives_unit_closure_one_step: "(A,w) \<in> unit_closure P \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* w"
unfolding unit_closure_def proof (induction "(A,w)" arbitrary: A w rule: closure_induct)
  case mono
  then show ?case using mono_unit_subst by simp
next
  case base
  then show ?case by (simp add: derives_Cons_rule)
next
  case (step A')
  then have "(A,w) \<in> unit_subst A'"
    by simp
  then obtain B where "(A,[Nt B]) \<in> A'" and "(B,w) \<in> A'"
    unfolding unit_subst_def by auto
  then have "P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
    using step.hyps(1) by auto
  moreover have "P \<turnstile> [Nt B] \<Rightarrow>* w"
    using \<open>(B, w) \<in> A'\<close> step.hyps by auto
  ultimately show ?case 
    by simp
qed

(* This direction is slightly more interesting *)
theorem derivs_if_derives_unit_closure: "unit_closure P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case
    by simp
next
  case (step u A v w)
  then show ?case
    using derivs_if_derives_unit_closure_one_step
    by (metis derives_append derives_prepend rtranclp_trans)
qed

lemma Lang_unit_closure_subset: "Lang (unit_closure P) A \<subseteq> Lang P A"
unfolding Lang_def using derivs_if_derives_unit_closure by blast

(* The final theorem: *)
theorem Lang_unit_closure: "Lang (unit_closure P) A = Lang P A"
by (metis antisym[OF Lang_unit_closure_subset Lang_unit_closure_incr])

lemma closed_unit_subst_unit_closure: "closed unit_subst (unit_closure P)"
  unfolding unit_closure_def using closure_closed[OF mono_unit_subst] by blast

definition "rm_unit P = {p \<in> unit_closure P .\<forall>B. snd p \<noteq> [Nt B]}"

definition "unit w = (\<exists>B. w = [Nt B])"

(* as written, this lemma does not hold, but a modified version of it might
be helpful for proving the subsequent lemma*)
lemma derivs_rm_unit_if_derives_unit_closure_one_step: 
  "(A,w) \<in> unit_closure P \<Longrightarrow> rm_unit P \<turnstile> [Nt A] \<Rightarrow>* w"
unfolding unit_closure_def proof (induction "(A,w)" rule: closure_induct)
  case mono
  then show ?case using mono_unit_subst by simp
next
  case base
  then show ?case
  oops

(* I think this should be provable *)
lemma derivs_rm_unit_if_derives_unit_closure: 
  "unit_closure P \<turnstile> \<alpha> \<Rightarrow>* map Tm \<beta> \<Longrightarrow> rm_unit P \<turnstile> \<alpha> \<Rightarrow>* map Tm \<beta>"
proof (induction rule: derives_induct')
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case 
  sorry
  qed

text \<open>The main theorem:\<close>
theorem "Lang (rm_unit P) A = Lang P A"
proof
  show "Lang (rm_unit P) A \<subseteq> Lang P A"
    by (metis (mono_tags) Collect_subset Lang_mono Lang_unit_closure rm_unit_def)
next
  have "\<And> w. w \<in> Lang (unit_closure P) A \<Longrightarrow> w \<in> Lang (rm_unit P) A"
    proof -
      fix w
      assume "w \<in> Lang (unit_closure P) A"
      then have "unit_closure P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        unfolding Lang_def by auto
      then have "rm_unit P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        using derivs_rm_unit_if_derives_unit_closure by auto
      then show "w \<in> Lang (rm_unit P) A"
      unfolding Lang_def by simp
    qed
  then have "Lang (unit_closure P) A \<subseteq> Lang (rm_unit P) A"
    by auto
  then show "Lang P A \<subseteq> Lang (rm_unit P) A"
    using Lang_unit_closure by fastforce
qed
end