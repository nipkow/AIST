section\<open>Finite Automata\<close>

text\<open>
  The fact that for a regular language \<open>L\<close>, the predecessors with respect to a context-free grammar
  \<open>pre\<^sup>*(L)\<close> is also regular has been discovered independently by many authors \cite{book1993string, buchi3105regular, caucal1992regular}.
  This represents a key closure property, since the word-problem for regular languages is
  inherently decidable, as are many other problems.
  To reason about regular languages, a simple model of a non-deterministic finite automaton (NFA)
  without \<open>\<epsilon>\<close>-transitions is defined.
\<close>

theory FiniteAutomaton
  imports Main
begin \<comment>\<open>begin-theory FiniteAutomaton\<close>

subsection\<open>Definition\<close>

text\<open>
  In this theory, an NFA \<open>M\<close> is defined as the \<open>3\<close>-tuple \<open>(\<delta>, S, F)\<close>, where \<open>\<delta>\<close> are the transitions,
  \<open>S\<close> is the starting symbol and \<open>F\<close> are the final states. The state-domain \<open>Q\<close> and alphabet \<open>\<Sigma>\<close>
  are not explicitly given, since the type-theory still allows for proof of formal correctness.
\<close>

record ('s, 't) nfa =
  transitions :: "('s \<times> 't \<times> 's) set"
  start :: 's
  finals :: "'s set"

subsection\<open>Step Relation\<close>

text\<open>
  The following two lemmas ensure that Isabelle can automatically evaluate set expressions with
  \<open>2\<close>-tuples and \<open>3\<close>-tuples, which will be used thouroughly within this project.
\<close>

lemma [code_unfold]:
  "{(x,y) \<in> A. P x y} = {p \<in> A. P (fst p) (snd p)}"
  by fastforce

lemma [code_unfold]:
  "{(x,y,z) \<in> A. P x y z} = {p \<in> A. P (fst p) (fst (snd p)) (snd (snd p))}"
  by fastforce

text\<open>
  A step from a single state \<open>q\<close> over a single symbol \<open>c\<close> is the set of all \<open>q'\<close>, where \<open>(q, c, q') \<in> \<delta>\<close>:
\<close>

definition step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's \<Rightarrow> 's set" where
  "step T c s = (\<lambda>(q, c, q'). q') ` {(q, c', q') \<in> T. c = c' \<and> q = s}"

text\<open>
  A step of a single symbol \<open>c\<close> from a set of states \<open>S\<close> is the union of @{term step} over \<open>S\<close>:
\<close>

definition Step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Step T c S = \<Union>((\<lambda>s. step T c s) ` S)"

text\<open>
  Repeated steps of a word \<open>w\<close> consisting of multiple letters is achieved using a standard @{term fold}:
\<close>

definition Steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Steps T w s = fold (Step T) w s"

text\<open>
  However, we often only regard a single-starting state, for which the following abbreviation is introduced:
\<close>

abbreviation steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's \<Rightarrow> 's set" where
  "steps T w s \<equiv> Steps T w {s}"

lemma Step_union: "Step T w (S\<^sub>1 \<union> S\<^sub>2) = Step T w S\<^sub>1 \<union> Step T w S\<^sub>2"
  unfolding Step_def by blast

lemma Steps_mono: "s\<^sub>1 \<subseteq> s\<^sub>2 \<Longrightarrow> Steps T w s\<^sub>1 \<subseteq> Steps T w s\<^sub>2"
proof (induction w arbitrary: s\<^sub>1 s\<^sub>2)
  case Nil thus ?case by (simp add: Steps_def)
next
  case (Cons w ws)

  define s\<^sub>1' where [simp]: "s\<^sub>1' \<equiv> Step T w s\<^sub>1"
  define s\<^sub>2' where [simp]: "s\<^sub>2' \<equiv> Step T w s\<^sub>2"
  
  have "s\<^sub>1' \<subseteq> s\<^sub>2'"
    by (simp add: Step_def, use \<open>s\<^sub>1 \<subseteq> s\<^sub>2\<close> in blast)
  then have "Steps T ws s\<^sub>1' \<subseteq> Steps T ws s\<^sub>2'"
    by (elim Cons.IH)
  moreover have "Steps T (w#ws) s\<^sub>1 = Steps T ws s\<^sub>1'"
    by (simp add: Steps_def)
  moreover have "Steps T (w#ws) s\<^sub>2 = Steps T ws s\<^sub>2'"
    by (simp add: Steps_def)
  ultimately show ?case
    by simp
qed

lemma [mono]: "mono (Steps T w)" (* TODO: give proper name to lemma *)
  by (intro monoI, elim Steps_mono)

lemma Steps_path:
  assumes "q\<^sub>f \<in> Steps T w s"
  shows "\<exists>q\<^sub>0 \<in> s. q\<^sub>f \<in> steps T w q\<^sub>0"
proof (insert assms; induction w arbitrary: s)
  case Nil thus ?case by (simp add: Steps_def)
next
  case (Cons w ws)
  then have "q\<^sub>f \<in> Steps T ws (Step T w s)"
    by (simp add: Steps_def)
  moreover obtain q\<^sub>0 where "q\<^sub>0 \<in> (Step T w s)" and "q\<^sub>f \<in> steps T ws q\<^sub>0"
    using Cons.IH calculation by blast
  ultimately obtain q' where "q\<^sub>0 \<in> step T w q'" and "q' \<in> s"
    unfolding Steps_def Step_def by blast

  note \<open>q\<^sub>0 \<in> step T w q'\<close> and \<open>q\<^sub>f \<in> steps T ws q\<^sub>0\<close>
  then have "q\<^sub>f \<in> Steps T ws (step T w q')"
    using Steps_mono[of "{q\<^sub>0}"] by blast
  moreover have "Steps T ws (step T w q') = steps T (w#ws) q'"
    by (simp add: Steps_def step_def Step_def)
  ultimately show ?case
    using \<open>q' \<in> s\<close> by blast
qed

lemma Steps_split:
  assumes "q\<^sub>f \<in> Steps T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
  shows "\<exists>q'. q' \<in> Steps T w\<^sub>1 Q\<^sub>0 \<and> q\<^sub>f \<in> steps T w\<^sub>2 q'"
proof -
  define Q\<^sub>f where [simp]: "Q\<^sub>f = Steps T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
  define Q' where [simp]: "Q' = Steps T w\<^sub>1 Q\<^sub>0"
  have "Q\<^sub>f = Steps T w\<^sub>2 Q'"
    by (simp add: Steps_def)
  then obtain q' where "q' \<in> Q'" and "q\<^sub>f \<in> steps T w\<^sub>2 q'"
    using assms Steps_path by force
  moreover have "q' \<in> Steps T w\<^sub>1 Q\<^sub>0"
    using calculation by simp
  ultimately show ?thesis
    by blast
qed

lemma Steps_join:
  assumes "q' \<in> Steps T w\<^sub>1 Q\<^sub>0" and "q\<^sub>f \<in> steps T w\<^sub>2 q'"
  shows "q\<^sub>f \<in> Steps T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
proof -
  define Q' where [simp]: "Q' = Steps T w\<^sub>1 Q\<^sub>0"
  define Q\<^sub>f where [simp]: "Q\<^sub>f = Steps T w\<^sub>2 Q'"

  have "{q'} \<subseteq> Q'"
    using assms(1) by simp
  then have "Steps T w\<^sub>2 {q'} \<subseteq> Steps T w\<^sub>2 Q'"
    using Steps_mono by blast
  then have "q\<^sub>f \<in> Steps T w\<^sub>2 Q'"
    using assms(2) by fastforce
  moreover have "Q\<^sub>f = Steps T (w\<^sub>1@w\<^sub>2) Q\<^sub>0"
    by (simp add: Steps_def)
  ultimately show ?thesis
    by simp
qed

lemma Steps_split3:
  assumes "q\<^sub>f \<in> Steps T (w\<^sub>1@w\<^sub>2@w\<^sub>3) Q\<^sub>0"
  shows "\<exists>q' q''. q' \<in> Steps T w\<^sub>1 Q\<^sub>0 \<and> q'' \<in> steps T w\<^sub>2 q' \<and> q\<^sub>f \<in> steps T w\<^sub>3 q''"
proof -
  obtain q' where "q' \<in> Steps T (w\<^sub>1@w\<^sub>2) Q\<^sub>0 \<and> q\<^sub>f \<in> steps T w\<^sub>3 q'"
    using assms Steps_split[where w\<^sub>1 = "w\<^sub>1@w\<^sub>2"] by fastforce
  moreover obtain q'' where "q'' \<in> Steps T w\<^sub>1 Q\<^sub>0 \<and> q' \<in> steps T w\<^sub>2 q''"
    using calculation Steps_split by fast
  ultimately show ?thesis
    by blast
qed

lemma Steps_join3:
  assumes "q' \<in> steps T w\<^sub>1 q\<^sub>0" and "q'' \<in> steps T w\<^sub>2 q'" and "q\<^sub>f \<in> steps T w\<^sub>3 q''"
  shows "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2@w\<^sub>3) q\<^sub>0"
proof -
  have "q\<^sub>f \<in> steps T (w\<^sub>2@w\<^sub>3) q'"
    using assms(2) assms(3) Steps_join by fast
  moreover have "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2@w\<^sub>3) q\<^sub>0"
    using calculation assms(1) Steps_join by fast
  ultimately show ?thesis
    by blast
qed

subsection\<open>Language\<close>

abbreviation accepts :: "('s \<times> 't \<times> 's) set \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> 't list \<Rightarrow> bool" where
  "accepts T s F w \<equiv> (steps T w s \<inter> F \<noteq> {})"

lemma accepts_split3:
  assumes "accepts T s F (w\<^sub>1@w\<^sub>2@w\<^sub>3)"
  shows "\<exists>q' q'' q\<^sub>f. q' \<in> steps T w\<^sub>1 s \<and> q'' \<in> steps T w\<^sub>2 q' \<and> q\<^sub>f \<in> steps T w\<^sub>3 q'' \<and> q\<^sub>f \<in> F"
  using assms Steps_split3 by fast

definition lang' :: "('s \<times> 't \<times> 's) set \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> ('t list) set" where
  "lang' T S F \<equiv> { w | w. accepts T S F w }"

abbreviation lang :: "('s, 't) nfa \<Rightarrow> ('t list) set" where
  "lang M \<equiv> lang' (transitions M) (start M) (finals M)"

lemma nfa_lang_trans:
  assumes "s' \<in> steps T w\<^sub>1 s" and "w\<^sub>2 \<in> lang' T s' F"
  shows "(w\<^sub>1@w\<^sub>2) \<in> lang' T s F"
proof -
  obtain q\<^sub>f where "q\<^sub>f \<in> steps T w\<^sub>2 s'" and "q\<^sub>f \<in> F"
    using assms(2) unfolding lang'_def by blast
  moreover have "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2) s"
    using assms(1) \<open>q\<^sub>f \<in> steps T w\<^sub>2 s'\<close> by (rule Steps_join)
  ultimately show ?thesis
    unfolding lang'_def using \<open>q\<^sub>f \<in> F\<close> by blast
qed

lemma nfa_lang_split:
  assumes "(w\<^sub>1@w\<^sub>2) \<in> lang' T q F"
  obtains q' where "q' \<in> steps T w\<^sub>1 q" and "w\<^sub>2 \<in> lang' T q' F"
proof -
  obtain q\<^sub>f where "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2) q" and "q\<^sub>f \<in> F"
    using assms unfolding lang'_def by blast
  then obtain q' where "q' \<in> steps T w\<^sub>1 q" and "q\<^sub>f \<in> steps T w\<^sub>2 q'"
    using Steps_split by fast
  moreover have "w\<^sub>2 \<in> lang' T q' F"
    unfolding lang'_def using \<open>q\<^sub>f \<in> F\<close> calculation by blast
  ultimately show ?thesis
    using that by blast
qed

lemma nfa_mono':
  assumes "T\<^sub>1 \<subseteq> T\<^sub>2" and "q\<^sub>1 \<subseteq> q\<^sub>2"
  shows "Steps T\<^sub>1 w q\<^sub>1 \<subseteq> Steps T\<^sub>2 w q\<^sub>2"
proof (insert assms(2); induction w arbitrary: q\<^sub>1 q\<^sub>2)
  case Nil thus ?case by (simp add: Steps_def)
next
  case (Cons w ws)
  have "Step T\<^sub>1 w q\<^sub>1 \<subseteq> Step T\<^sub>2 w q\<^sub>2"
    unfolding Step_def step_def using assms(1) Cons(2) by blast
  then have "Steps T\<^sub>1 ws (Step T\<^sub>1 w q\<^sub>1) \<subseteq> Steps T\<^sub>1 ws (Step T\<^sub>2 w q\<^sub>2)"
    by (rule Steps_mono)
  then have "Steps T\<^sub>1 ws (Step T\<^sub>1 w q\<^sub>1) \<subseteq> Steps T\<^sub>2 ws (Step T\<^sub>2 w q\<^sub>2)"
    using Cons(1) by blast
  then show ?case
    by (simp add: Steps_def)
qed

lemma nfa_mono: "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> steps T\<^sub>1 w q \<subseteq> steps T\<^sub>2 w q"
  using nfa_mono'[of T\<^sub>1 T\<^sub>2 "{q}" "{q}" w] by simp

lemma nfa_steps_mono: "\<delta>\<^sub>1 \<subseteq> \<delta>\<^sub>2 \<Longrightarrow> q' \<in> steps \<delta>\<^sub>1 w q \<Longrightarrow> q' \<in> steps \<delta>\<^sub>2 w q"
proof -
  assume "\<delta>\<^sub>1 \<subseteq> \<delta>\<^sub>2"
  then have "steps \<delta>\<^sub>1 w q \<subseteq> steps \<delta>\<^sub>2 w q"
    by (rule nfa_mono)
  then show "q' \<in> steps \<delta>\<^sub>1 w q \<Longrightarrow> q' \<in> steps \<delta>\<^sub>2 w q"
    by blast
qed

lemma nfa_steps_union: "q' \<in> steps \<delta> w q \<Longrightarrow> q' \<in> steps (\<delta> \<union> \<delta>') w q"
proof -
  have "\<delta> \<subseteq> (\<delta> \<union> \<delta>')"
    by simp
  then show "q' \<in> steps \<delta> w q \<Longrightarrow> q' \<in> steps (\<delta> \<union> \<delta>') w q"
    by (rule nfa_steps_mono)
qed

lemma nfa_lang_mono: "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> lang' T\<^sub>1 s f \<subseteq> lang' T\<^sub>2 s f"
  unfolding lang'_def using nfa_mono[of T\<^sub>1 T\<^sub>2] by fast

subsection\<open>Reachable States\<close>

type_synonym ('s, 't) Trans = "('s \<times> 't \<times> 's) set"

definition reachable_from :: "('s, 't) Trans \<Rightarrow> 's \<Rightarrow> 's set" where
  "reachable_from \<delta> q \<equiv> {q'. \<exists>w. q' \<in> steps \<delta> w q}"

lemma reachable_from_computable: "reachable_from \<delta> q \<subseteq> {q} \<union> (snd ` snd ` \<delta>)"
proof
  fix q'
  assume "q' \<in> reachable_from \<delta> q"
  then obtain w where w_def: "q' \<in> steps \<delta> w q"
    unfolding reachable_from_def by blast
  then consider "w = []" | "\<exists>ws c. w = ws@[c]"
    by (meson rev_exhaust)
  then show "q' \<in> {q} \<union> (snd ` snd ` \<delta>)"
  proof (cases)
    case 1
    then show ?thesis
      using w_def Steps_def by force
  next
    case 2
    then obtain ws c where "w = ws@[c]"
      by blast
    then obtain q1 where "q1 \<in> steps \<delta> ws q" and "q' \<in> steps \<delta> [c] q1"
      using Steps_split w_def by fast
    then have "(q1, c, q') \<in> \<delta>"
      by (auto simp: Steps_def Step_def step_def)
    then show ?thesis
      by force
  qed
qed

lemma reachable_from_trans[trans]:
  assumes "q1 \<in> reachable_from \<delta> q0" and "q2 \<in> reachable_from \<delta> q1"
  shows "q2 \<in> reachable_from \<delta> q0"
  using assms Steps_join unfolding reachable_from_def by fast

lemma reachable_add_trans:
  assumes "\<forall>(q1, _, q2) \<in> \<delta>'. \<exists>w. q2 \<in> steps \<delta> w q1"
  shows "reachable_from \<delta> q = reachable_from (\<delta> \<union> \<delta>') q"
proof (standard; standard)
  fix q'
  assume "q' \<in> reachable_from \<delta> q"
  then show "q' \<in> reachable_from (\<delta> \<union> \<delta>') q"
    unfolding reachable_from_def using nfa_steps_union by fast
next
  fix q'
  assume "q' \<in> reachable_from (\<delta> \<union> \<delta>') q"
  then obtain w where "q' \<in> steps (\<delta> \<union> \<delta>') w q"
    unfolding reachable_from_def by blast
  then have "\<exists>w'. q' \<in> steps \<delta> w' q"
  proof (induction w arbitrary: q)
    case Nil
    then have "q = q'" and "q \<in> steps \<delta> [] q"
      unfolding Steps_def by simp+
    then show ?case
      by blast
  next
    case (Cons c w)
    then obtain q1 where "q' \<in> steps (\<delta> \<union> \<delta>') w q1" and "q1 \<in> steps (\<delta> \<union> \<delta>') [c] q"
      using Steps_split[where w\<^sub>1="[c]" and w\<^sub>2=w] by force
    then obtain w' where w'_def: "q' \<in> steps \<delta> w' q1"
      using Cons by blast

    have "q1 \<in> step (\<delta> \<union> \<delta>') c q"
      using \<open>q1 \<in> steps (\<delta> \<union> \<delta>') [c] q\<close> by (simp add: Steps_def Step_def)
    then consider "q1 \<in> step \<delta> c q" | "q1 \<in> step \<delta>' c q"
      unfolding step_def by blast
    then show ?case
    proof (cases)
      case 1
      then have "q1 \<in> steps \<delta> [c] q"
        by (simp add: Steps_def Step_def)
      then have "q' \<in> steps \<delta> (c#w') q"
        using w'_def Steps_join by force
      then show ?thesis
        by blast
    next
      case 2
      then have "(q, c, q1) \<in> \<delta>'"
        by (auto simp: step_def)
      then obtain w'' where "q1 \<in> steps \<delta> w'' q"
        using assms by blast
      then have "q' \<in> steps \<delta> (w''@w') q"
        using w'_def Steps_join by fast
      then show ?thesis
        by blast
    qed
  qed
  then show "q' \<in> reachable_from \<delta> q"
    by (simp add: reachable_from_def)
qed

end \<comment>\<open>end-theory FiniteAutomaton\<close>
