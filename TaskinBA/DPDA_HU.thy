theory DPDA_HU
  imports PDA
begin

definition the_elem_opt :: "'a set \<Rightarrow> 'a option" where 
  "the_elem_opt X \<equiv> (if X = {} then None else Some (SOME x. x : X))"

lemma the_elem_opt_eq [simp]: "the_elem_opt {x} = Some x"
  by (simp add: the_elem_opt_def)

lemma the_elem_opt_elem: "the_elem_opt A = Some x \<Longrightarrow> x \<in> A"
  unfolding the_elem_opt_def using some_in_eq[of A] by (auto split: if_splits)

locale dpda = pda M for M :: "('q :: finite, 'a :: finite, 's :: finite) pda" +
  assumes true_sgn: "trans_fun M q a Z = {} \<or> (\<exists>p \<gamma>. trans_fun M q a Z = {(p, \<gamma>)})"
      and eps_sgn: "eps_fun M q Z = {} \<or> (\<exists>p \<gamma>. eps_fun M q Z = {(p, \<gamma>)})"
      and true_or_eps: "trans_fun M q a Z \<noteq> {} \<Longrightarrow> eps_fun M q Z = {}"
begin

lemma dpda_step: "step (q, w, Z#\<alpha>) = {} \<or> (\<exists>p y \<gamma>. step (q, w, Z#\<alpha>) = {(p, y, \<gamma>)})"
proof (cases w)
  case Nil
  then show ?thesis
    using eps_sgn by fastforce
next
  case (Cons a z)
  then show ?thesis proof (cases)
    assume "trans_fun M q a Z = {}"
    with Cons show ?thesis
      using eps_sgn[of q Z] by auto
  next
    assume tr_ne: "trans_fun M q a Z \<noteq> {}"
    from tr_ne have *: "\<exists>p \<gamma>. trans_fun M q a Z = {(p, \<gamma>)}"
      using true_sgn by auto
    from tr_ne have **: "eps_fun M q Z = {}"
      using true_or_eps by simp
    from Cons * ** show ?thesis by auto
  qed
qed

fun det_step\<^sub>1 :: "'q \<times> 'a list \<times> 's list \<Rightarrow> ('q \<times> 'a list \<times> 's list) option"
  where "det_step\<^sub>1 cf = the_elem_opt (step cf)"

lemma step\<^sub>1_det_step\<^sub>1_some: "step\<^sub>1 (p, w, \<alpha>) (q, y, \<gamma>) \<longleftrightarrow> det_step\<^sub>1 (p, w, \<alpha>) = Some (q, y, \<gamma>)" (is "?l \<longleftrightarrow> ?r")
proof (rule iffI)
  assume l: ?l
  from l obtain Z \<alpha>' where [simp]: "\<alpha> = Z#\<alpha>'"
    using step\<^sub>1_nonempty_stack by blast
  from l have "(q, y, \<gamma>) \<in> step (p, w, \<alpha>)" by simp
  hence "step (p, w, \<alpha>) = {(q, y, \<gamma>)}"
    using dpda_step[of p w Z \<alpha>'] by auto
  then show ?r by simp
next
  show "?r \<Longrightarrow> ?l"
    using the_elem_opt_elem[of "step (p, w, \<alpha>)"] by auto
qed

lemma dpda_step\<^sub>1_det:
  assumes "step\<^sub>1 (p, w, \<alpha>) (q, y, \<gamma>)"
      and "step\<^sub>1 (p, w, \<alpha>) (q', y', \<gamma>')"
    shows "q = q' \<and> y = y' \<and> \<gamma> = \<gamma>'"
  using assms step\<^sub>1_det_step\<^sub>1_some by simp

lemma det_step\<^sub>1_rule_ext: "det_step\<^sub>1 (p, w, \<alpha>) = Some (q, y, \<gamma>) \<longleftrightarrow> (\<exists>Z' \<alpha>'. \<alpha> = Z' # \<alpha>' \<and>
                                                     ((\<exists>\<beta>. y = w \<and> \<gamma> = \<beta> @ \<alpha>' \<and> (q, \<beta>) \<in> eps_fun M p Z') \<or>
                                                      (\<exists>a \<beta>. w = a # y \<and> \<gamma> = \<beta> @ \<alpha>' \<and> (q, \<beta>) \<in> trans_fun M p a Z')))"
  using step\<^sub>1_det_step\<^sub>1_some step\<^sub>1_rule_ext by simp

lemma step\<^sub>1_det_step\<^sub>1_none: "(\<forall>q y \<gamma>. \<not>step\<^sub>1 (p, w, \<alpha>) (q, y, \<gamma>)) \<longleftrightarrow> det_step\<^sub>1 (p, w, \<alpha>) = None"
  by (auto simp: the_elem_opt_def split: if_splits)

fun det_stepn :: "nat \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> ('q \<times> 'a list \<times> 's list) option" where
  "det_stepn 0 (p, w, \<alpha>) = Some (p, w, \<alpha>)"
| "det_stepn (Suc n) (p, w, \<alpha>) = 
    (case det_step\<^sub>1 (p, w, \<alpha>) of None \<Rightarrow> None | Some (q, y, \<gamma>) \<Rightarrow> det_stepn n (q, y, \<gamma>))"

lemma stepn_det_stepn_some: "stepn n (p, w, \<alpha>) (q, y, \<gamma>) \<longleftrightarrow> det_stepn n (p, w, \<alpha>) = Some (q, y, \<gamma>)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    by (induction rule: stepn_induct) (use step\<^sub>1_det_step\<^sub>1_some in auto)
next
  show "?r \<Longrightarrow> ?l"
  proof (induction n "(p, w, \<alpha>)" arbitrary: p w \<alpha> rule: det_stepn.induct)
    case (2 n p w \<alpha>)
    from 2(2) obtain q' y' \<gamma>' where fs: "det_step\<^sub>1 (p, w, \<alpha>) = Some (q', y', \<gamma>')" and lss: "det_stepn n (q', y', \<gamma>') = Some (q, y, \<gamma>)"
      by (auto split: option.splits)

    from 2(1)[OF fs _ _ lss] have "stepn n (q', y', \<gamma>') (q, y, \<gamma>)" by blast

    moreover from fs have "step\<^sub>1 (p, w, \<alpha>) (q', y', \<gamma>')"
      using step\<^sub>1_det_step\<^sub>1_some by blast

    ultimately show ?case
      using stepn_split_first by blast
  qed simp
qed

lemma steps_det_stepn_some: "steps (p, w, \<alpha>) (q, y, \<gamma>) \<longleftrightarrow> (\<exists>n. det_stepn n (p, w, \<alpha>) = Some (q, y, \<gamma>))"
  using stepn_det_stepn_some stepn_steps by simp

lemma dpda_stepn_det:
  assumes "stepn n (p, w, \<alpha>) (q, y, \<gamma>)"
      and "stepn n (p, w, \<alpha>) (q', y', \<gamma>')"
    shows "q = q' \<and> y = y' \<and> \<gamma> = \<gamma>'"
  using assms stepn_det_stepn_some by simp

lemma stepn_det_stepn_none: "(\<forall>q y \<gamma>. \<not>stepn n (p, w, \<alpha>) (q, y, \<gamma>)) \<longleftrightarrow> det_stepn n (p, w, \<alpha>) = None"
  using stepn_det_stepn_some[of n p w \<alpha>] by (metis not_None_eq prod_cases3)

end
end