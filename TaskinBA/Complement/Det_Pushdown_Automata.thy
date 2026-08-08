section \<open>Deterministic Pushdown Automata\<close>

theory Det_Pushdown_Automata
  imports Pushdown_Automata.Pushdown_Automata
begin

subsection \<open>Definition\<close>

text \<open>The following definition of a deterministic pushdown automaton has been introduced by Hopcroft and Ullman\cite{hopcroftullman}:\<close>

locale dpda = pda M for M :: "('q :: finite, 'a :: finite, 's :: finite) pda" +
  assumes \<delta>_nonempty: "\<delta> M q a X \<noteq> {} \<longrightarrow> \<delta>\<epsilon> M q X = {}"
      and \<delta>_singleton: "\<delta> M q a X = {} \<or> (\<exists>p \<gamma>. \<delta> M q a X = {(p, \<gamma>)})"
      and \<delta>\<epsilon>_singleton: "\<delta>\<epsilon> M q X = {} \<or> (\<exists>p \<gamma>. \<delta>\<epsilon> M q X = {(p, \<gamma>)})"
begin

text \<open>\noindent Given a configuration:
      \begin{itemize}
        \item The property @{thm [source] \<delta>_nonempty} prevents the automaton to freely choose from an epsilon step and a true step.
        \item The property @{thm [source] \<delta>_singleton} allows for at most one true step.
        \item The property @{thm [source] \<delta>\<epsilon>_singleton} allows for at most one epsilon step.
      \end{itemize}\<close>

subsection \<open>Determinism\<close>

text \<open>The automaton can take at most one step in a given configuration:\<close>
lemma dpda_step: "step (q, w, \<alpha>) = {} \<or> (\<exists>p u \<gamma>. step (q, w, \<alpha>) = {(p, u, \<gamma>)})"
proof (cases \<alpha>)
  case [simp]: (Cons X \<alpha>')
  show ?thesis proof (cases w)
    case Nil
    then show ?thesis
      using \<delta>\<epsilon>_singleton[of q X] by auto
  next
    case [simp]: (Cons a w')
    consider (a) "\<delta> M q a X = {}" | (b) "\<delta> M q a X \<noteq> {}" by satx
    then show ?thesis proof cases
      case a
      then show ?thesis
        using \<delta>\<epsilon>_singleton[of q X] by auto
    next
      case b
      then show ?thesis
        using \<delta>_nonempty[of q a X] \<delta>_singleton[of q a X] by auto
    qed
  qed
qed auto

text \<open>A step of the automaton is indeed deterministic:\<close>
lemma dpda_step\<^sub>1_det:
  assumes "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>)"
      and "(q, w, \<alpha>) \<leadsto> (p', u', \<gamma>')"
    shows "p = p' \<and> u = u' \<and> \<gamma> = \<gamma>'"
using assms dpda_step by fastforce

lemma dpda_stepn_det:
  assumes "(q, w, \<alpha>) \<leadsto>(n) (p, u, \<gamma>)"
      and "(q, w, \<alpha>) \<leadsto>(n) (p', u', \<gamma>')"
    shows "p = p' \<and> u = u' \<and> \<gamma> = \<gamma>'"
using assms proof (induction "(q, w, \<alpha>)" "(p, u, \<gamma>)" arbitrary: q w \<alpha> rule: stepn_induct)
  case (stepn n q w \<alpha> r u \<beta>)
  from stepn(4) have *: "(r, u, \<beta>) \<leadsto>(n) (p', u', \<gamma>')"
    using stepn_split_first[of q w \<alpha> n p' u' \<gamma>'] dpda_step\<^sub>1_det[OF stepn(1)] by auto
  from stepn(3)[OF *] show ?case .
qed auto

end
end