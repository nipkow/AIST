theory Epsilon
imports
  Closure
  "../CFG"
begin

hide_const (open) Topological_Spaces.closed

text \<open>Epsilon closure\<close>

definition eps_subst :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) Prods" where
"eps_subst P = {(A,\<alpha> @ \<beta>)|A \<alpha> \<beta>. \<exists>B. (A,\<alpha> @ [Nt B] @ \<beta>) \<in> P \<and> (B,[]) \<in> P}"

definition "eps_closure P = closure eps_subst P"

lemma mono_eps_subst: "mono eps_subst"
unfolding eps_subst_def mono_def by fastforce

(* One direction is easy *)
lemma eps_closure_incr: "P \<subseteq> eps_closure P"
unfolding eps_closure_def by (simp add: closure_incr)

lemma Lang_mono: "P \<subseteq> P' \<Longrightarrow> Lang P A \<subseteq> Lang P' A"
apply(auto simp: Lang_def)
by (metis Un_derive mono_rtranclp sup.orderE)

lemma Lang_eps_closure_incr: "Lang P A \<subseteq> Lang (eps_closure P) A"
by (simp add: eps_closure_incr Lang_mono)

(* This direction is slightly more interesting *)
theorem derivs_if_derives_eps_closure: "eps_closure P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
(* should work *)
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case
    by simp
next
  case (step u A v w)
  then show ?case sorry
qed

lemma Lang_eps_closure_subset: "Lang (eps_closure P) A \<subseteq> Lang P A"
unfolding Lang_def using derivs_if_derives_eps_closure by blast

(* The final theorem: *)
theorem Lang_eps_closure: "Lang (eps_closure P) A = Lang P A"
by (metis antisym[OF Lang_eps_closure_subset Lang_eps_closure_incr])

lemma closed_eps_subst_eps_closure: "closed eps_subst (eps_closure P)"
unfolding eps_closure_def using closure_closed[OF mono_eps_subst] by blast

definition "rm_eps P = {p \<in> eps_closure P . snd p \<noteq> []}"

text \<open>The main theorem:\<close>
theorem "Lang (rm_eps P) A = Lang P A - {[]}"
sorry
(* maybe follows easily (but not directly) from \<open>Lang_eps_closure\<close>.
Probably need to prove both directions separately.
*)

end