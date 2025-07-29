theory DPDA
  imports PDA
begin

datatype 'a input_with_marker = Input 'a | End_marker

instance input_with_marker :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>a. t = Input a} \<union> {End_marker}"
    by auto (metis input_with_marker.exhaust)
  show "finite (UNIV :: 'a input_with_marker set)"
    by (simp add: * full_SetCompr_eq)
qed

abbreviation word_with_end :: "'a list \<Rightarrow> 'a input_with_marker list" where 
  "word_with_end w \<equiv> map Input w @ [End_marker]"

lemma card_leq_1: 
  assumes "finite A"
      and "card A \<le> 1"
    shows "A = {} \<or> (\<exists>a. A = {a})"
proof (cases)
  assume "card A = 1"
  then show ?thesis
    using card_1_singletonE[of A] by auto
next
  assume "\<not>(card A = 1)"
  with assms(2) have "card A = 0" by simp
  with assms(1) show ?thesis by simp
qed

definition the_elem_opt :: "'a set \<Rightarrow> 'a option" where 
  "the_elem_opt X \<equiv> (if X = {} then None else Some (SOME x. x : X))"

lemma the_elem_opt_eq [simp]: "the_elem_opt {x} = Some x"
  by (simp add: the_elem_opt_def)

lemma the_elem_opt_elem: "the_elem_opt A = Some x \<Longrightarrow> x \<in> A"
  unfolding the_elem_opt_def using some_in_eq[of A] by (auto split: if_splits)

locale dpda = pda M for M :: "('q :: finite, ('a :: finite) input_with_marker, 's :: finite) pda" +
  assumes det: "card (trans_fun M q a Z) + card (eps_fun M q Z) = 1"
      and init_trans: "(q, \<alpha>) \<in> trans_fun M p a (init_symbol M) \<Longrightarrow> \<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
      and init_eps: "(q, \<alpha>) \<in> eps_fun M p (init_symbol M) \<Longrightarrow> \<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
begin

(* TODO: show that every pda with the assumption det has a dpda accepting the same set and vice versa *)

lemma trans_or_eps_singleton: 
    "(\<exists>p \<alpha>. trans_fun M q a Z = {} \<and> eps_fun M q Z = {(p, \<alpha>)}) \<or>
       (\<exists>p \<alpha>. trans_fun M q a Z = {(p, \<alpha>)} \<and> eps_fun M q Z = {})"
proof (cases "trans_fun M q a Z = {}")
  case True
  hence "card (trans_fun M q a Z) = 0" by simp
  hence "card (eps_fun M q Z) = 1"
    using det[of q a Z] by simp
  hence "\<exists>p \<alpha>. eps_fun M q Z = {(p, \<alpha>)}" 
    by (simp add: card_1_singleton_iff)
  with True show ?thesis by simp
next
  case False
  hence *: "card (trans_fun M q a Z) = 1"
    using det[of q a Z] finite_trans by (simp add: add_is_1)
  hence 1: "\<exists>p \<alpha>. trans_fun M q a Z = {(p, \<alpha>)}" 
    by (simp add: card_1_singleton_iff)
  from * have "card (eps_fun M q Z) = 0"
    using det[of q a Z] by simp
  hence "eps_fun M q Z = {}"
    using finite_eps by simp
  with 1 show ?thesis by simp
qed

lemma dpda_step_empty_word: "step (p, [], Z#\<alpha>) = {} \<or> (\<exists>p' w' \<alpha>'. step (p, [], Z#\<alpha>) = {(p', w', \<alpha>')})"
  using trans_or_eps_singleton[of p _ Z] by fastforce

lemma dpda_step_nonempty_word: "\<exists>p' w' \<alpha>'. step (p, a#w, Z#\<alpha>) = {(p', w', \<alpha>')}"
  using trans_or_eps_singleton[of p a Z] by auto

lemma dpda_step_elem: "(q, y, \<gamma>) \<in> step (p, w, \<alpha>) \<Longrightarrow> step (p, w, \<alpha>) = {(q, y, \<gamma>)}" (is "?asm \<Longrightarrow> _")
proof -
  assume asm: ?asm
  then obtain Z' \<alpha>' where [simp]: "\<alpha> = Z'#\<alpha>'"
    using step\<^sub>1_nonempty_stack[of p w \<alpha> q y \<gamma>] by auto
  with asm have "\<exists>p' w' \<alpha>'. step (p, w, \<alpha>) = {(p', w', \<alpha>')}"
    using dpda_step_empty_word[of p Z' \<alpha>'] dpda_step_nonempty_word[of p _ _ Z' \<alpha>'] by (cases w) auto
  with asm show ?thesis by auto
qed

fun det_step\<^sub>1 :: "'q \<times> 'a input_with_marker list \<times> 's list \<Rightarrow> ('q \<times> 'a input_with_marker list \<times> 's list) option" 
  where "det_step\<^sub>1 cf = the_elem_opt (step cf)"

lemma step\<^sub>1_det_step\<^sub>1_some: "step\<^sub>1 (p, w, \<alpha>) (q, y, \<gamma>) \<longleftrightarrow> det_step\<^sub>1 (p, w, \<alpha>) = Some (q, y, \<gamma>)"
  apply (rule iffI)
  apply (simp add: dpda_step_elem[of q y \<gamma> p w \<alpha>] the_elem_opt_eq[of "step (p, w, \<alpha>)"])
  apply (simp add: the_elem_opt_elem[of "step (p, w, \<alpha>)"])
  done

lemma dpda_step\<^sub>1_det:
  assumes "step\<^sub>1 (p, w, \<alpha>) (q, y, \<gamma>)"
      and "step\<^sub>1 (p, w, \<alpha>) (q', y', \<gamma>')"
    shows "q = q' \<and> y = y' \<and> \<gamma> = \<gamma>'"
using assms step\<^sub>1_det_step\<^sub>1_some by simp

lemma det_step\<^sub>1_rule_ext: "det_step\<^sub>1 (p, w, \<alpha>) = Some (q, y, \<gamma>) \<longleftrightarrow> (\<exists>Z' \<alpha>'. \<alpha> = Z' # \<alpha>' \<and>
                                                     ((\<exists>\<beta>. y = w \<and> \<gamma> = \<beta> @ \<alpha>' \<and> (q, \<beta>) \<in> eps_fun M p Z') \<or>
                                                      (\<exists>a \<beta>. w = a # y \<and> \<gamma> = \<beta> @ \<alpha>' \<and> (q, \<beta>) \<in> trans_fun M p a Z')))"
  using step\<^sub>1_det_step\<^sub>1_some step\<^sub>1_rule_ext by simp

lemma det_step\<^sub>1_init_bottom:
  assumes "det_step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ [init_symbol M]) = Some (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>\<gamma>. \<alpha>\<^sub>2 = \<gamma> @ [init_symbol M]"
by (cases \<alpha>\<^sub>1) (use assms det_step\<^sub>1_rule_ext init_trans init_eps in auto)

lemma step\<^sub>1_det_step\<^sub>1_none: "(\<forall>q y \<gamma>. \<not>step\<^sub>1 (p, w, \<alpha>) (q, y, \<gamma>)) \<longleftrightarrow> det_step\<^sub>1 (p, w, \<alpha>) = None"
  by (auto simp: the_elem_opt_def split: if_splits)

fun det_stepn :: "nat \<Rightarrow> 'q \<times> 'a input_with_marker list \<times> 's list \<Rightarrow> ('q \<times> 'a input_with_marker list \<times> 's list) option" where
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

lemma det_stepn_init_bottom: 
  assumes "det_stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ [init_symbol M]) = Some (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>\<gamma>. \<alpha>\<^sub>2 = \<gamma> @ [init_symbol M]"
using assms by (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ [init_symbol M])" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: det_stepn.induct) (auto split: option.splits, use det_step\<^sub>1_init_bottom in fastforce)

lemma stepn_det_stepn_none: "(\<forall>q y \<gamma>. \<not>stepn n (p, w, \<alpha>) (q, y, \<gamma>)) \<longleftrightarrow> det_stepn n (p, w, \<alpha>) = None"
  using stepn_det_stepn_some[of n p w \<alpha>] by (metis not_None_eq prod_cases3)

definition det_final_accept :: "'a list set" where
  "det_final_accept \<equiv> {w | w q n \<gamma>. q \<in> final_states M \<and> det_stepn n (init_state M, word_with_end w, [init_symbol M]) = Some (q, [], \<gamma>)}"

end
end