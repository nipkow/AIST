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

lemma derivs_if_derives_eps_closure_one_step: "(A,w) \<in> eps_closure P \<Longrightarrow> P \<turnstile> [Nt A] \<Rightarrow>* w"
unfolding eps_closure_def proof (induction "(A,w)" arbitrary: A w rule: closure_induct)
  case mono
  then show ?case using mono_eps_subst by auto
next
  case base
  then show ?case by (simp add: derives_Cons_rule)
next
  case (step A')
  then have "(A,w) \<in> eps_subst A'"
    by simp
  then obtain \<gamma> \<delta> B where "w = \<gamma> @ \<delta>" and "(A, \<gamma> @ [Nt B] @ \<delta>) \<in> A'" and "(B, []) \<in> A'"
    unfolding eps_subst_def by auto
  then have "P \<turnstile> [Nt A] \<Rightarrow>* \<gamma> @ [Nt B] @ \<delta>"
    using step.hyps(1) by auto
  moreover have "P \<turnstile> [Nt B] \<Rightarrow>* []"
    using \<open>(B, []) \<in> A'\<close> step.hyps by auto
  ultimately have "P \<turnstile> [Nt A] \<Rightarrow>* \<gamma> @ \<delta>"
    by (metis append_self_conv2 bu_embed derives_bu_if derives_if_bu)
  then show ?case
    using \<open>w = \<gamma> @ \<delta>\<close> by (meson bu_embed derives_bu_if derives_if_bu step.hyps)
qed

(* This direction is slightly more interesting *)
theorem derivs_if_derives_eps_closure: "eps_closure P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<Longrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case
    by simp
next
  case (step u A v w)
  then show ?case
    using derivs_if_derives_eps_closure_one_step step.IH 
    by (metis derives_append derives_prepend rtranclp_trans)
qed

lemma Lang_eps_closure_subset: "Lang (eps_closure P) A \<subseteq> Lang P A"
  unfolding Lang_def using derivs_if_derives_eps_closure by blast

(* The final theorem: *)
theorem Lang_eps_closure: "Lang (eps_closure P) A = Lang P A"
  by (metis antisym[OF Lang_eps_closure_subset Lang_eps_closure_incr])

lemma closed_eps_subst_eps_closure: "closed eps_subst (eps_closure P)"
  unfolding eps_closure_def using closure_closed[OF mono_eps_subst] by blast

definition "rm_eps P = {p \<in> eps_closure P . snd p \<noteq> []}"


(* I thought the next lemma would follow from this one in a similar fashion
to the proof above, but either it doesn't follow or requires more work to
show that it does follow than I thought *)
lemma derivs_rm_eps_if_derives_eps_closure_one_step: 
  "\<lbrakk>(A,w) \<in> eps_closure P; w \<noteq> []\<rbrakk> \<Longrightarrow> rm_eps P \<turnstile> [Nt A] \<Rightarrow>* w"
  oops

(* should be provable, but I'm not sure if it's the best way to prove the
final theorem.  I've also included 2 other of my failed attempts at proving
the main theorem below, commented out, which may be of some use (but may also
be wastes of time) *)
lemma derivs_rm_eps_if_derives_eps_closure: 
  "\<lbrakk>eps_closure P \<turnstile> \<alpha> \<Rightarrow>* \<beta> ; \<beta> \<noteq> []\<rbrakk> \<Longrightarrow> (rm_eps P \<turnstile> \<alpha> \<Rightarrow>* \<beta>)"
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case 
    using derives_append derives_prepend rtranclp_trans
        sorry
  qed

text \<open>The main theorem:\<close>
theorem "Lang (rm_eps P) A = Lang P A - {[]}"
proof
  have "\<forall> a. (a,[]) \<notin> rm_eps P"
    unfolding rm_eps_def by simp
  then have "[] \<notin> Lang (rm_eps P) A"
    unfolding rm_eps_def Lang_def using CollectD Eps_freeI Eps_free_derives_Nil 
    by (metis (no_types, lifting) list.map_disc_iff not_Cons_self2)
  moreover have "Lang (rm_eps P) A \<subseteq> Lang P A"
    unfolding rm_eps_def using Lang_eps_closure Lang_mono mem_Collect_eq subsetI 
    by (metis (lifting))
  ultimately show "Lang (rm_eps P) A \<subseteq> Lang P A - {[]}"
    by auto
next
  have "\<And> w. w \<in> Lang (eps_closure P) A - {[]} \<Longrightarrow> w \<in> Lang (rm_eps P) A"
    proof -
      fix w
      assume "w \<in> Lang (eps_closure P) A - {[]}"
      then have "eps_closure P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        unfolding Lang_def by simp
      moreover have "w \<noteq> []"
        using \<open>w \<in> Lang (eps_closure P) A - {[]}\<close> by simp
      ultimately have "rm_eps P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        using derivs_rm_eps_if_derives_eps_closure by auto
      then show "w \<in> Lang (rm_eps P) A"
      unfolding Lang_def by auto
    qed
  then show "Lang P A - {[]} \<subseteq> Lang (rm_eps P) A"
    by (simp add: Lang_eps_closure subset_eq)
qed
  (*
  have "\<And> w. w \<in> Lang P A - {[]} \<Longrightarrow> w \<in> Lang (rm_eps P) A"
    proof -
      fix w
      assume "w \<in> Lang P A - {[]}"
      then have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        unfolding Lang_def by simp
      then have "eps_closure P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        by (metis (no_types, lifting) Collect_mono_iff Lang_def Lang_eps_closure_incr)
      moreover have "map Tm w \<noteq> []"
        using \<open>w \<in> Lang P A - {[]}\<close> by blast
      ultimately have "rm_eps P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        proof (induction rule: rtrancl_derive_induct)
          case base
          then show ?case by simp
        next
          case (step u A' v w)
          show ?case 
            proof (cases)
              assume wEps: "w = []"
              then have "(A',[]) \<in> eps_closure P"
                using step.hyps by auto
              moreover have "eps_closure P \<turnstile> [Nt A] \<Rightarrow>* u @ [Nt A'] @ v"
                using step.hyps(1) by auto
              ultimately obtain B x y \<alpha> \<beta> where 
                "(B, x @ y) \<in> eps_closure P" and "(B, x @ [Nt A'] @ y) \<in> eps_closure P"
                and "x@y \<noteq> []"
                and "\<alpha> @ x = u" and 
                "y @ \<beta> = v" and "eps_closure P \<turnstile> \<alpha> @ [Nt B] @ \<beta> \<Rightarrow>* u @ [Nt A'] @ v" 
                and "eps_closure P \<turnstile> [Nt A] \<Rightarrow>* \<alpha> @ [Nt B] @ \<beta>"
                unfolding eps_closure_def eps_subst_def closure_def
                sorry
                then have "(B,x@y) \<in> rm_eps P"
                  by (simp add: rm_eps_def)
                then have "rm_eps P \<turnstile> [Nt A] \<Rightarrow>* \<alpha> @ [Nt B] @ \<beta>"
                  unfolding rm_eps_def eps_closure_def closure_def eps_subst_def try
              then show ?case 
                sorry
            next
              assume NotwEps: "w \<noteq> []"
              then show ?case 
                by (smt (verit, del_insts) Nil_is_append_conv derive.intros mem_Collect_eq not_Cons_self2 rm_eps_def rtranclp.simps snd_conv step.IH step.hyps(2))
            qed
        qed
      then show "w \<in> Lang (rm_eps P) A"
        unfolding Lang_def rm_eps_def eps_closure_def
        by simp
    qed
  then show "Lang P A - {[]} \<subseteq> Lang (rm_eps P) A"
    by auto
    *)



 (* 
  have "\<And> w. w \<in> Lang P A - {[]} \<Longrightarrow> w \<in> Lang (rm_eps P) A"
    proof -
      fix w
      assume "w \<in> Lang P A - {[]}"
      then have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        unfolding Lang_def by simp
      then have "eps_closure P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        by (metis (no_types, lifting) Collect_mono_iff Lang_def Lang_eps_closure_incr)
      then have "rm_eps P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        proof (induction rule: rtrancl_derive_induct)
          case base
          then show ?case by simp
        next
          case (step u A' v w)
          show ?case 
            proof (cases)
              assume wEps: "w = []"
              then have "(A',[]) \<in> eps_closure P"
                using step.hyps by auto
              (* then have "eps_closure P \<turnstile> [Nt A] \<Rightarrow>* u @ [] @ v" *)
              (*   using step.IH by (meson derive.intros rtranclp.simps step.hyps(1)) *)
              (* then have "eps_closure P \<turnstile> [Nt> A] \<Rightarrow>* u @ v" *)
              (*   by simp *)
              moreover have "rm_eps P \<turnstile> [Nt A] \<Rightarrow>* u @ [Nt A'] @ v"
                using step.IH by blast
              ultimately have "rm_eps P \<turnstile> [Nt A] \<Rightarrow>* u @ v"
                unfolding rm_eps_def
                sorry
              then show ?thesis 
                using wEps by auto
            next
              assume NotwEps: "w \<noteq> []"
              then show ?thesis 
              by (metis (mono_tags, lifting) derive.intros mem_Collect_eq rm_eps_def rtranclp.rtrancl_into_rtrancl snd_conv step.IH step.hyps(2))
            qed
        qed
      then show "w \<in> Lang (rm_eps P) A"
        unfolding Lang_def rm_eps_def eps_closure_def
        by simp
    qed
*)
end