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

locale dpda = pda M for M :: "('q :: finite, ('a :: finite) input_with_marker, 's :: finite) pda" +
  assumes det: "card (trans_fun M q a Z) + card (eps_fun M q Z) = 1"
      and init_trans: "(q, \<alpha>) \<in> trans_fun M p a (init_symbol M) \<Longrightarrow> \<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
      and init_eps: "(q, \<alpha>) \<in> eps_fun M p (init_symbol M) \<Longrightarrow> \<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
begin

(* TODO: show that every pda with the assumption det has a dpda accepting the same set and vice versa *)

lemma dpda_step_empty_word: "step (p, [], Z#\<alpha>) = {} \<or> (\<exists>p' w' \<alpha>'. step (p, [], Z#\<alpha>) = {(p', w', \<alpha>')})"
proof -
  have "card (step (p, [], Z#\<alpha>)) = card (eps_fun M p Z)"
    using card_empty_step by simp
  also have "... \<le> 1"
    using det[where ?q = p and ?Z = Z] by fastforce
  finally show ?thesis
    using card_leq_1[OF finite_step[of _ "[]"]] by simp
qed

lemma dpda_step_nonempty_word: "\<exists>p' w' \<alpha>'. step (p, a#w, Z#\<alpha>) = {(p', w', \<alpha>')}"
proof -
  have "card (step (p, a#w, Z#\<alpha>)) = card (trans_fun M p a Z) + card (eps_fun M p Z)"
    using card_nonempty_step by simp
  also have "... = 1"
    using det by simp
  finally show ?thesis
    by (simp add: card_1_singleton_iff)
qed

lemma dpda_step_det:
  assumes "step\<^sub>1 (p, w, \<alpha>) (q, y, \<gamma>)"
      and "step\<^sub>1 (p, w, \<alpha>) (q', y', \<gamma>')"
    shows "q = q' \<and> y = y' \<and> \<gamma> = \<gamma>'"
proof (cases w)
  case Nil
  with assms(1) have "step (p, w, \<alpha>) = {} \<or> (\<exists>p' w' \<alpha>'. step (p, w, \<alpha>) = {(p', w', \<alpha>')})"
    using step\<^sub>1_nonempty_stack[of p w \<alpha> q y \<gamma>] dpda_step_empty_word[of p] by blast
  with assms show ?thesis by auto
next
  case (Cons a w')
  with assms(1) have "\<exists>p' w' \<alpha>'. step (p, w, \<alpha>) = {(p', w', \<alpha>')}"
    using step\<^sub>1_nonempty_stack[of p w \<alpha> q y \<gamma>] dpda_step_nonempty_word by blast
  with assms show ?thesis by auto
qed

lemma stepn_det:
  assumes "stepn n (p, w, \<alpha>) (q, y, \<gamma>)"
      and "stepn n (p, w, \<alpha>) (q', y', \<gamma>')"
    shows "q = q' \<and> y = y' \<and> \<gamma> = \<gamma>'"
using assms by (induction n "(p, w, \<alpha>)" "(q, y, \<gamma>)" arbitrary: q y \<gamma> q' y' \<gamma>' rule: stepn.induct) (fastforce simp: dpda_step_det)+

lemma step\<^sub>1_init_bottom:
  assumes "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ [init_symbol M]) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>\<gamma>. \<alpha>\<^sub>2 = \<gamma> @ [init_symbol M]"
using assms step\<^sub>1_rule init_trans init_eps by (cases \<alpha>\<^sub>1) auto

lemma steps_init_bottom: 
  assumes "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ [init_symbol M]) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>\<gamma>. \<alpha>\<^sub>2 = \<gamma> @ [init_symbol M]"
using assms by (induction "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ [init_symbol M])" " (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: steps_induct) 
                 (fastforce simp: step\<^sub>1_init_bottom)+

abbreviation word_with_end :: "'a list \<Rightarrow> 'a input_with_marker list" where 
  "word_with_end w \<equiv> map Input w @ [End_marker]"

definition final_accept_det :: "'a list set" where
  "final_accept_det \<equiv> {w | w q \<gamma>. q \<in> final_states M \<and> steps (init_state M, word_with_end w, [init_symbol M]) (q, [], \<gamma>)}"

end
end