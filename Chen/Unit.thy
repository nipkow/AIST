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
proof (induction rule: derives_induct)
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

(* Lemmas added by TN *)

lemma deriven_append2:
  "\<lbrakk> P \<turnstile> u1 \<Rightarrow>(n1) v1; P \<turnstile> u2 \<Rightarrow>(n2) v2 \<rbrakk> \<Longrightarrow> P \<turnstile> u1 @ u2 \<Rightarrow>(n1+n2) v1 @ v2"
using deriven_append_decomp by blast

(* The key lemma *)
lemma deriven_rm_unit_if_unit_closure:
  "unit_closure P \<turnstile> \<alpha> \<Rightarrow>(n) map Tm \<beta> \<Longrightarrow> \<exists>m\<le>n. rm_unit P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm \<beta>"
proof (induction n arbitrary: \<alpha> rule: less_induct)
  case (less n)
  have cl: "\<And>A B \<alpha>. (A,[Nt B]) \<in> unit_closure P \<and> (B,\<alpha>) \<in> unit_closure P \<Longrightarrow> (A,\<alpha>) \<in> unit_closure P"
    using closed_unit_subst_unit_closure[of P] unfolding unit_subst_def by blast
  show ?case
  proof (cases "n=0")
    case True
    then show ?thesis
      using less.prems by auto
  next
    case False
    with less.prems obtain u v A w
      where *: "(A,w) \<in> unit_closure P" "\<alpha> = u @ [Nt A] @ v" "unit_closure P \<turnstile> u @ w @ v \<Rightarrow>(n-1) map Tm \<beta>"
      by (smt (verit, ccfv_SIG) One_nat_def derive.cases diff_Suc_1' relpowp_E2)
    obtain m where "m \<le> n-1" and **: "rm_unit P \<turnstile> u @ w @ v \<Rightarrow>(m) map Tm \<beta>"
      using less.IH[OF _ *(3)] False by auto
    show ?thesis
    proof (cases "unit w")
      case True
      then obtain B where [simp]: "w = [Nt B]" unfolding unit_def by auto
      obtain u' wv' mu mwv where "\<beta> = u' @ wv'" "m = mu + mwv" and
        u: "rm_unit P \<turnstile> u \<Rightarrow>(mu) map Tm u'" and wv: "rm_unit P \<turnstile> [Nt B] @ v \<Rightarrow>(mwv) map Tm wv'"
        using deriven_append_decomp[THEN iffD1, OF **]
          by(auto simp: map_eq_append_conv)
      obtain w' v' mw mv where "wv' = w' @ v'" "mwv = mw + mv" and
        w: "rm_unit P \<turnstile> [Nt B] \<Rightarrow>(mw) map Tm w'" and v: "rm_unit P \<turnstile> v \<Rightarrow>(mv) map Tm v'"
        using deriven_append_decomp[THEN iffD1, OF wv]
          by(auto simp: map_eq_append_conv)
      have "mw > 0"
        using not_one_le_zero w by fastforce
      have "mu + mw + mv \<le> n"
        using \<open>m = mu + mwv\<close> \<open>m \<le> n - 1\<close> \<open>mwv = mw + mv\<close> by linarith
      from w obtain wb where
        "(B,wb)\<in> rm_unit P" and wb: "rm_unit P \<turnstile> wb \<Rightarrow>(mw-1) map Tm w'"
        using deriven_start1 by fastforce
      have "(A,wb) \<in> rm_unit P" using  *(1) \<open>(B, wb) \<in> rm_unit P\<close> \<open>w = [Nt B]\<close> cl
        by (metis (lifting) ext mem_Collect_eq rm_unit_def snd_conv)
      then have 1: "rm_unit P \<turnstile> [Nt A] \<Rightarrow>(1) wb"
        by (metis derive_singleton Transitive_Closure.relpowp_1)
       have "rm_unit P \<turnstile> \<alpha> \<Rightarrow>(1 + mu + (mw-1) + mv) map Tm \<beta>" unfolding \<open>\<alpha> = _\<close> \<open>\<beta> = _\<close>
         using relpowp_trans[OF deriven_prepend[OF deriven_append[OF 1]]
                 deriven_append2[OF u deriven_append2[OF wb v]]]
         by (simp add: \<open>wv' = _\<close> add_ac)
      also have "1 + mu + (mw-1) + mv = mu + mw + mv \<and> mu + mw + mv \<le> n"
        using \<open>mw > 0\<close> \<open>m = mu + mwv\<close> \<open>m \<le> n - 1\<close> \<open>mwv = mw + mv\<close> by linarith
      ultimately show ?thesis by metis
    next
      have "m+1 \<le> n" using False \<open>m \<le> n - 1\<close> by auto
      case False
      hence "(A,w) \<in> rm_unit P" using \<open>(A,w) \<in> unit_closure P\<close> unfolding unit_def rm_unit_def by auto
      thus ?thesis using *(2) ** \<open>m+1 \<le> n\<close>
        by (metis Suc_eq_plus1 derive.intros relpowp_Suc_I2)
    qed
  qed
qed

lemma derives_rm_unit_if_unit_closure: 
  "unit_closure P \<turnstile> \<alpha> \<Rightarrow>* map Tm \<beta> \<Longrightarrow> rm_unit P \<turnstile> \<alpha> \<Rightarrow>* map Tm \<beta>"
by (meson deriven_rm_unit_if_unit_closure rtranclp_power)
(* end of TN lemmas *)

(* I think this should be provable
lemma derivs_rm_unit_if_derives_unit_closure: 
  "unit_closure P \<turnstile> \<alpha> \<Rightarrow>* map Tm \<beta> \<Longrightarrow> rm_unit P \<turnstile> \<alpha> \<Rightarrow>* map Tm \<beta>"
(* I think this is the induction rule we needed, although I can't be sure *)
proof (induction rule: converse_derives_induct )
    case base
  then show ?case by simp
next
  case (step u A v w)
  show ?case
  (* I couldn't figure out exactly how to prove this step, potentially could
  be an induction on (A,w) with the closure_induct rule, although I didn't manage
  to make that work, and I'm not sure if that was a good path to go down *)
  sorry
qed
 *)
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

      (* This is the step relying on the unproven lemma - now proved TN *)
      then have "rm_unit P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
        using derives_rm_unit_if_unit_closure by blast

      then show "w \<in> Lang (rm_unit P) A"
      unfolding Lang_def by simp
    qed
  then have "Lang (unit_closure P) A \<subseteq> Lang (rm_unit P) A"
    by auto
  then show "Lang P A \<subseteq> Lang (rm_unit P) A"
    using Lang_unit_closure by fastforce
qed
end