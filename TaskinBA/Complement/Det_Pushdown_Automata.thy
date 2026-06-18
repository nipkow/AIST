theory Det_Pushdown_Automata
  imports Pushdown_Automata.Pushdown_Automata
begin 

definition the_elem_opt :: "'a set \<Rightarrow> 'a option" where
  "the_elem_opt A \<equiv> (if A = {} then None else Some (SOME a. a : A))"

text \<open>The definition @{const the_elem_opt} is intended to extract the element out of a singleton set. We will need this later as the
      function @{const pda.step} (hopefully) produces either the empty set or a singleton set.\<close>

lemma the_elem_opt_eq [simp]: "the_elem_opt {a} = Some a"
  by (simp add: the_elem_opt_def)

lemma the_elem_opt_inv: "the_elem_opt A = Some a \<Longrightarrow> a \<in> A"
  unfolding the_elem_opt_def using some_in_eq[of A] by (auto split: if_splits)

section \<open>A locale for deterministic pushdown automata\<close>

locale dpda = pda M for M :: "('q :: finite, 'a :: finite, 's :: finite) pda" +
  assumes \<delta>_nonempty: "\<delta> M q a X \<noteq> {} \<longrightarrow> \<delta>\<epsilon> M q X = {}"
      and \<delta>_singleton: "\<delta> M q a X = {} \<or> (\<exists>p \<gamma>. \<delta> M q a X = {(p, \<gamma>)})"
      and \<delta>\<epsilon>_singleton: "\<delta>\<epsilon> M q X = {} \<or> (\<exists>p \<gamma>. \<delta>\<epsilon> M q X = {(p, \<gamma>)})"
begin

text \<open>In a configuration:
      * The property @{thm \<delta>_nonempty} prevents the automaton to freely choose from an epsilon step and a true step.
      * The property @{thm \<delta>_singleton} allows for at most one true step.
      * The property @{thm \<delta>\<epsilon>_singleton} allows for at most one epsilon step.\<close>

section \<open>Definitions\<close>

definition det_step :: "'q \<times> 'a list \<times> 's list \<Rightarrow> ('q \<times> 'a list \<times> 's list) option" where
  "det_step cf = the_elem_opt (step cf)"

abbreviation det_step\<^sub>1 ("(_ \<leadsto>\<^sub>d _)" [50, 50] 50) where
  "cf \<leadsto>\<^sub>d cf' \<equiv> det_step cf = Some cf'"

abbreviation det_nstep\<^sub>1 ("(_ \<leadsto>\<^sub>d)" [50] 50) where
  "cf \<leadsto>\<^sub>d \<equiv>  det_step cf = None"

fun det_stepn :: "nat \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> ('q \<times> 'a list \<times> 's list) option" where
  "det_stepn 0 cf = Some cf"
| "det_stepn (Suc n) cf =
    (case det_stepn n cf of None \<Rightarrow> None | Some cf' \<Rightarrow> det_step cf')"

abbreviation det_stepn\<^sub>1 ("(_ /\<leadsto>\<^sub>d'(_')/ _)" [50, 0, 50] 50) where
  "cf \<leadsto>\<^sub>d(n) cf' \<equiv> det_stepn n cf = Some cf'"

abbreviation det_nstepn\<^sub>1 ("(_ /\<leadsto>\<^sub>d'(_')/ )" [50, 0] 50) where
  "cf \<leadsto>\<^sub>d(n) \<equiv> det_stepn n cf = None"

(* TODO *)
(* (q, \<alpha>) \<leadsto> (p, \<gamma>) for (q, [], \<alpha>) \<leadsto> (p, [], \<gamma>) *)

section \<open>Lemmas\<close>

text \<open>The function @{const step} is indeed of deterministic nature under the locale assumptions.\<close>
lemma dpda_step: "step (q, w, X#\<alpha>) = {} \<or> (\<exists>p u \<gamma>. step (q, w, X#\<alpha>) = {(p, u, \<gamma>)})"
proof (cases w)
  case Nil
  with \<delta>\<epsilon>_singleton[of q X] 
  show ?thesis by auto
next
  case [simp]: (Cons a w')
  then show ?thesis proof (cases)
    assume "\<delta> M q a X = {}"
    with \<delta>\<epsilon>_singleton[of q X]
    show ?thesis by auto
  next
    assume a: "\<delta> M q a X \<noteq> {}"
    from a \<delta>_singleton have *: "\<exists>p \<gamma>. \<delta> M q a X = {(p, \<gamma>)}" by auto
    from a \<delta>_nonempty have **: "\<delta>\<epsilon> M q X = {}" by simp
    from * ** show ?thesis by auto
  qed
qed

text \<open>Equivalence of the definitions @{const step\<^sub>1} and @{const det_step\<^sub>1}\<close>
lemma step\<^sub>1_det_step\<^sub>1: "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>) \<longleftrightarrow> (q, w, \<alpha>) \<leadsto>\<^sub>d (p, u, \<gamma>)" (is "?l \<longleftrightarrow> ?r")
proof (rule iffI)
  assume l: ?l
  obtain X \<alpha>' where [simp]: "\<alpha> = X#\<alpha>'"
    using step\<^sub>1_nonempty_stack[OF l] by blast
  from l have "(p, u, \<gamma>) \<in> step (q, w, \<alpha>)" by simp
  hence "step (q, w, \<alpha>) = {(p, u, \<gamma>)}"
    using dpda_step[of q w X \<alpha>'] by auto
  thus ?r by (simp add: det_step_def)
next
  show "?r \<Longrightarrow> ?l"
    using the_elem_opt_inv[of "step (q, w, \<alpha>)"] by (simp add: det_step_def)
qed

text \<open>Equivalence of the definitions @{const det_step\<^sub>1} and @{const det_stepn}}}\<close>
lemma det_step\<^sub>1_det_stepn_one: "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>\<^sub>d (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<leadsto>\<^sub>d(1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by simp

text \<open>A step in the automaton is deterministic.\<close>
lemma dpda_step\<^sub>1_det:
  assumes "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>)"
      and "(q, w, \<alpha>) \<leadsto> (p', u', \<gamma>')"
    shows "p = p' \<and> u = u' \<and> \<gamma> = \<gamma>'"
using assms step\<^sub>1_det_step\<^sub>1 by simp

text \<open>Equivalence of the definitions @{const stepsn} and @{const det_stepn\<^sub>1}\<close>
lemma stepn_det_stepn\<^sub>1: "(q, w, \<alpha>) \<leadsto>(n) (p, u, \<gamma>) \<longleftrightarrow> (q, w, \<alpha>) \<leadsto>\<^sub>d(n) (p, u, \<gamma>)"
proof (induction n arbitrary: p u \<gamma>)
  case 0
  then show ?case by auto
next
  case (Suc n)
  have "(q, w, \<alpha>) \<leadsto>(Suc n) (p, u, \<gamma>) \<longleftrightarrow> (\<exists>r v \<beta>. (q, w, \<alpha>) \<leadsto>(n) (r, v, \<beta>) \<and> (r, v, \<beta>) \<leadsto> (p, u, \<gamma>))" by auto
  also
  from Suc.IH have "... \<longleftrightarrow> (\<exists>r v \<beta>. (q, w, \<alpha>) \<leadsto>\<^sub>d(n) (r, v, \<beta>) \<and> (r, v, \<beta>) \<leadsto> (p, u, \<gamma>))" by simp
  also
  have "... \<longleftrightarrow> (\<exists>r v \<beta>. (q, w, \<alpha>) \<leadsto>\<^sub>d(n) (r, v, \<beta>) \<and> (r, v, \<beta>) \<leadsto>\<^sub>d (p, u, \<gamma>))"
    using step\<^sub>1_det_step\<^sub>1 by simp
  also
  have "... \<longleftrightarrow> (q, w, \<alpha>) \<leadsto>\<^sub>d(Suc n) (p, u, \<gamma>)" by (auto split: option.split)
  finally show ?case .
qed

text \<open>Multiple steps in the automaton are deterministic.\<close>
lemma dpda_stepn_det:
  assumes "(q, w, \<alpha>) \<leadsto>(n) (p, u, \<gamma>)"
      and "(q, w, \<alpha>) \<leadsto>(n) (p', u', \<gamma>')"
    shows "p = p' \<and> u = u' \<and> \<gamma> = \<gamma>'"
using assms stepn_det_stepn\<^sub>1 by simp

end
end