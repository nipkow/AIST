section\<open>Finite Automata\<close>

theory FiniteAutomaton
  imports Main
begin \<comment>\<open>begin-theory FiniteAutomaton\<close>

text\<open>
  The fact that for a regular language \<open>L\<close>, the predecessors with respect to a context-free grammar
  \<open>pre\<^sup>*(L)\<close> is also regular has been discovered independently by many authors \cite{book1993string, buchi3105regular, caucal1992regular}.
  This represents a key closure property, since the word-problem for regular languages is
  inherently decidable, as are many other problems.
  To reason about regular languages, a simple model of a non-deterministic finite automaton (NFA)
  without \<open>\<epsilon>\<close>-transitions is defined.
\<close>

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
  A step from a state \<open>q\<close> over a single symbol \<open>c\<close> is the set of all \<open>q'\<close>, such that \<open>(q, c, q') \<in> \<delta>\<close>:
\<close>

definition step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's \<Rightarrow> 's set" where
  "step T c s = (\<lambda>(q, c, q'). q') ` {(q, c', q') \<in> T. c = c' \<and> q = s}"

text\<open>
  A step of a single symbol \<open>c\<close> from a set of states \<open>S\<close> is the union of @{term step} over \<open>S\<close>:
\<close>

definition Step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Step T c S = \<Union>(step T c ` S)"

text\<open>
  Repeated steps of a word \<open>w\<close> consisting of multiple letters is achieved using a standard @{term fold}:
\<close>

definition Steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Steps T w s = fold (Step T) w s"

text\<open>
  Often, merely a single starting-state is of relevance:
\<close>

abbreviation steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's \<Rightarrow> 's set" where
  "steps T w s \<equiv> Steps T w {s}"

text\<open>
  We now prove some key properties of this step relation:
\<close>

lemma Step_union: "Step T w (S\<^sub>1 \<union> S\<^sub>2) = Step T w S\<^sub>1 \<union> Step T w S\<^sub>2"
  unfolding Step_def by blast

lemma Steps_subset: "s\<^sub>1 \<subseteq> s\<^sub>2 \<Longrightarrow> Steps T w s\<^sub>1 \<subseteq> Steps T w s\<^sub>2"
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

lemma Steps_mono[mono]: "mono (Steps T w)"
  by (intro monoI, elim Steps_subset)

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
    using Steps_subset[of "{q\<^sub>0}"] by blast
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
    using Steps_subset by blast
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

lemma Steps_noState: "Steps \<delta> w {} = {}"
proof (induction w)
  case Nil
  then show ?case
    by (simp add: Steps_def)
next
  case (Cons w ws)
  moreover have "Steps \<delta> [w] {} = {}"
    by (simp add: Steps_def Step_def)
  ultimately show ?case
    by (simp add: Steps_def)
qed

subsection\<open>Language\<close>

text\<open>
  The language \<open>L(M)\<close> of a given automata \<open>M\<close> is defined as the set of words, that
  reach at least one final state from a given starting state:
\<close>

abbreviation trans_accepts :: "('s \<times> 't \<times> 's) set \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> 't list \<Rightarrow> bool" where
  "trans_accepts T s F w \<equiv> (steps T w s \<inter> F \<noteq> {})"

abbreviation nfa_accepts :: "('s, 't) nfa \<Rightarrow> 't list \<Rightarrow> bool" where
  "nfa_accepts M \<equiv> trans_accepts (transitions M) (start M) (finals M)"

lemma accepts_split3:
  assumes "trans_accepts T s F (w\<^sub>1@w\<^sub>2@w\<^sub>3)"
  shows "\<exists>q' q'' q\<^sub>f. q' \<in> steps T w\<^sub>1 s \<and> q'' \<in> steps T w\<^sub>2 q' \<and> q\<^sub>f \<in> steps T w\<^sub>3 q'' \<and> q\<^sub>f \<in> F"
  using assms Steps_split3 by fast

abbreviation trans_lang :: "('s \<times> 't \<times> 's) set \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> ('t list) set" where
  "trans_lang T S F \<equiv> { w. trans_accepts T S F w }"

abbreviation nfa_lang :: "('s, 't) nfa \<Rightarrow> ('t list) set" where
  "nfa_lang M \<equiv> trans_lang (transitions M) (start M) (finals M)"

lemma nfa_lang_trans:
  assumes "s' \<in> steps T w\<^sub>1 s" and "w\<^sub>2 \<in> trans_lang T s' F"
  shows "(w\<^sub>1@w\<^sub>2) \<in> trans_lang T s F"
proof -
  obtain q\<^sub>f where "q\<^sub>f \<in> steps T w\<^sub>2 s'" and "q\<^sub>f \<in> F"
    using assms(2) by blast
  moreover have "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2) s"
    using assms(1) \<open>q\<^sub>f \<in> steps T w\<^sub>2 s'\<close> by (rule Steps_join)
  ultimately show ?thesis
    using \<open>q\<^sub>f \<in> F\<close> by blast
qed

lemma nfa_lang_split:
  assumes "(w\<^sub>1@w\<^sub>2) \<in> trans_lang T q F"
  obtains q' where "q' \<in> steps T w\<^sub>1 q" and "w\<^sub>2 \<in> trans_lang T q' F"
proof -
  obtain q\<^sub>f where "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2) q" and "q\<^sub>f \<in> F"
    using assms by blast
  then obtain q' where "q' \<in> steps T w\<^sub>1 q" and "q\<^sub>f \<in> steps T w\<^sub>2 q'"
    using Steps_split by fast
  moreover have "w\<^sub>2 \<in> trans_lang T q' F"
    using \<open>q\<^sub>f \<in> F\<close> calculation by blast
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
    by (rule Steps_subset)
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

lemma nfa_lang_mono: "T\<^sub>1 \<subseteq> T\<^sub>2 \<Longrightarrow> trans_lang T\<^sub>1 s f \<subseteq> trans_lang T\<^sub>2 s f"
  using nfa_mono[of T\<^sub>1 T\<^sub>2] by fast

subsection\<open>Reachable States\<close>

text\<open>
  The automata model is designed to work with datatypes with a potentially infinite universe.
  Generating a finite set of reachable states (i.e., filter out the states that are of no interest)
  is therefore a key factor to allow for automatic execution:
\<close>

definition reachable_from :: "('s \<times> 't \<times> 's) set \<Rightarrow> 's \<Rightarrow> 's set" where
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

subsection\<open>Merging Automata\<close>

text\<open>
  We will later provide concrete example of automata accepting specific languages.
  While proving words that satisfy certain requirements are contained within a language
  often is straight-forward, proving that the language only contains words satisfying
  these requirements is a much more difficult task. The below lemma provides a powerful
  tool to make these proofs manageable.
\<close>

text\<open>
  Vividly speaking, this lemma shows that when two disjunct NFAs (or rather sets of transitions),
  i.e. no states are shared, are connected via a single uni-directional bridge, every word that
  reaches from the first set of states to the a state within the second state must, at some point,
  pass this bridge, and have a prefix within the first set of states and a suffix within the
  second set.
\<close>

text\<open>
  This fact can later be used to prove behavior of inductively defined or merged automata.
\<close>

lemma nfa_merge:
  assumes "s\<^sub>A \<in> A" and "f\<^sub>A \<in> A" and "s\<^sub>B \<in> B" and "f\<^sub>B \<in> B" and "A \<inter> B = {}"
    and sideA: "\<forall>(q,c,q') \<in> \<delta>\<^sub>A. q \<in> A \<and> q' \<in> A"
    and sideB: "\<forall>(q,c,q') \<in> \<delta>\<^sub>B. q \<in> B \<and> q' \<in> B"
    and "f\<^sub>B \<in> steps (\<delta>\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> \<delta>\<^sub>B) w s\<^sub>A"
  shows "\<exists>w\<^sub>A w\<^sub>B. w = w\<^sub>A@[c]@w\<^sub>B \<and> f\<^sub>A \<in> steps \<delta>\<^sub>A w\<^sub>A s\<^sub>A \<and> f\<^sub>B \<in> steps \<delta>\<^sub>B w\<^sub>B s\<^sub>B"
proof (insert assms; induction w arbitrary: s\<^sub>A)
  case Nil
  then have "steps (\<delta>\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> \<delta>\<^sub>B) [] s\<^sub>A = {s\<^sub>A}"
    by (simp add: Steps_def)
  then show ?case
    using Nil(8) Nil(1,4,5) by fast
next
  case (Cons a w)
  define \<delta> where "\<delta> \<equiv> \<delta>\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> \<delta>\<^sub>B"

  \<comment> \<open>Obtain intermediate state after reading \<open>a\<close>:\<close>
  note \<open>f\<^sub>B \<in> steps (\<delta>\<^sub>A \<union> {(f\<^sub>A, c, s\<^sub>B)} \<union> \<delta>\<^sub>B) (a#w) s\<^sub>A\<close>
  then obtain q where a_step: "q \<in> steps \<delta> [a] s\<^sub>A"
    and w_step: "f\<^sub>B \<in> steps \<delta> w q"
    unfolding \<delta>_def using Steps_split by force

  \<comment> \<open>There are now two options:\<close>
  \<comment> \<open>1. \<open>a\<close> directly traverses the bridge to \<open>B\<close>, so \<open>a = c\<close>.\<close>
  \<comment> \<open>2. \<open>a\<close> remains within \<open>A\<close> and we can use the IH.\<close>
  then show ?case
  proof (cases "(s\<^sub>A, a, q) \<notin> \<delta>\<^sub>A")
    case True
    moreover have "(s\<^sub>A, a, q) \<notin> \<delta>\<^sub>B"
      using Cons(2,6,8) by fast
    moreover have "(s\<^sub>A, a, q) \<in> \<delta>"
      using a_step by (auto simp: Steps_def Step_def step_def)
    ultimately have "s\<^sub>A = f\<^sub>A" and "a = c" and "q = s\<^sub>B"
      unfolding \<delta>_def by simp+

    have inB: "s\<^sub>B \<in> B \<Longrightarrow> f\<^sub>B \<in> steps \<delta> w s\<^sub>B \<Longrightarrow> f\<^sub>B \<in> steps \<delta>\<^sub>B w s\<^sub>B"
    proof (induction w arbitrary: s\<^sub>B)
      case Nil
      then show ?case
        by (simp add: Steps_def)
    next
      case (Cons x xs)
      then obtain q where "f\<^sub>B \<in> steps \<delta> xs q" and "q \<in> steps \<delta> [x] s\<^sub>B"
        using Steps_split by force
      then have "(s\<^sub>B, x, q) \<in> \<delta>"
        by (auto simp: Steps_def Step_def step_def)
      moreover have "s\<^sub>B \<in> B"
        using Cons by simp
      ultimately have "(s\<^sub>B, x, q) \<in> \<delta>\<^sub>B" and "q \<in> B"
        unfolding \<delta>_def using assms(2,5,6,7) by blast+
      then have "q \<in> steps \<delta>\<^sub>B [x] s\<^sub>B"
        by (auto simp: Steps_def Step_def step_def) force
      moreover have "f\<^sub>B \<in> steps \<delta>\<^sub>B xs q"
        using \<open>f\<^sub>B \<in> steps \<delta> xs q\<close> \<open>q \<in> B\<close> Cons by simp
      ultimately show ?case
        using Steps_join by force
    qed

    \<comment> \<open>The bridge is directly traversed, so \<open>A\<close> can be ignored:\<close>
    have "a#w = []@[c]@w"
      by (simp add: \<open>a = c\<close>)
    moreover have "f\<^sub>A \<in> steps \<delta>\<^sub>A [] s\<^sub>A"
      by (simp add: \<open>s\<^sub>A = f\<^sub>A\<close> Steps_def)
    moreover have "f\<^sub>B \<in> steps \<delta>\<^sub>B w s\<^sub>B"
      using w_step assms(3) inB by (simp add: \<open>q = s\<^sub>B\<close>)
    ultimately show ?thesis
      by blast
  next
    case False
    then have a_step': "q \<in> steps \<delta>\<^sub>A [a] s\<^sub>A"
      by (auto simp: Steps_def Step_def step_def, force)
    then have "q \<in> A"
      using False Cons(7) by fast

    \<comment> \<open>Introduce the IH:\<close>
    then have "\<exists>w\<^sub>A w\<^sub>B. w = w\<^sub>A @[c]@w\<^sub>B \<and> f\<^sub>A \<in> steps \<delta>\<^sub>A w\<^sub>A q \<and> f\<^sub>B \<in> steps \<delta>\<^sub>B w\<^sub>B s\<^sub>B"
      by (rule Cons.IH; use Cons.prems w_step[unfolded \<delta>_def] in simp)
    then obtain w\<^sub>A w\<^sub>B where "w = w\<^sub>A @[c]@w\<^sub>B" and "f\<^sub>A \<in> steps \<delta>\<^sub>A w\<^sub>A q" and "f\<^sub>B \<in> steps \<delta>\<^sub>B w\<^sub>B s\<^sub>B"
      by blast
    moreover have "f\<^sub>A \<in> steps \<delta>\<^sub>A (a#w\<^sub>A) s\<^sub>A"
      using a_step' calculation(2) Steps_join by force
    ultimately have "a#w = a#w\<^sub>A@[c]@w\<^sub>B \<and> f\<^sub>A \<in> steps \<delta>\<^sub>A (a#w\<^sub>A) s\<^sub>A \<and> f\<^sub>B \<in> steps \<delta>\<^sub>B w\<^sub>B s\<^sub>B"
      by simp
    then show ?thesis
      by (intro exI) auto
  qed
qed

subsection\<open>Concrete Automata\<close>

text\<open>
  We now present three concrete automata that accept certain languages.
\<close>

subsubsection\<open>Universe over specific Alphabet\<close>

text\<open>
  This automaton acceptes exactly the words that only contains
  letters from a given alphabet.
\<close>

definition nfa_univ_trans :: "'s \<Rightarrow> 'a set \<Rightarrow> ('s \<times> 'a \<times> 's) set" where
  "nfa_univ_trans q U \<equiv> {q} \<times> U \<times> {q}"

lemma nfa_univ_trans_fin: "finite U \<Longrightarrow> finite (nfa_univ_trans q U)"
  by (simp add: nfa_univ_trans_def)

lemma nfa_univ_trans_correct1: "set w \<subseteq> U \<Longrightarrow> steps (nfa_univ_trans q U) w q = {q}"
proof (induction w)
  case Nil
  then show ?case
    by (simp add: Steps_def)
next
  case (Cons w ws)
  then have "steps (nfa_univ_trans q U) [w] q = {q}"
    unfolding nfa_univ_trans_def Steps_def Step_def step_def by fastforce
  moreover have "steps (nfa_univ_trans q U) ws q = {q}"
    using Cons by simp
  ultimately show ?case
    by (simp add: Steps_def)
qed

lemma nfa_univ_trans_correct2: "\<not> set w \<subseteq> U \<Longrightarrow> steps (nfa_univ_trans q U) w q = {}"
proof (induction w)
  case Nil
  then show ?case 
    by simp
next
  case (Cons w ws)
  then consider "w \<notin> U" | "\<not> set ws \<subseteq> U"
    by auto
  then show ?case
  proof (cases)
    case 1
    then have "steps (nfa_univ_trans q U) [w] q = {}"
      by (auto simp: nfa_univ_trans_def Steps_def Step_def step_def)
    moreover have "Steps (nfa_univ_trans q U) ws {} = {}"
      by (meson Steps_path ex_in_conv)
    ultimately show ?thesis
      by (metis Steps_split all_not_in_conv append_Cons append_Nil)
  next
    case 2
    then have "steps (nfa_univ_trans q U) ws q = {}"
      using Cons by simp
    moreover have "steps (nfa_univ_trans q U) [w] q \<subseteq> {q}"
      by (cases "w \<in> U") (auto simp: nfa_univ_trans_def Steps_def Step_def step_def)
    ultimately show ?thesis
      by (metis Steps_def Steps_subset Un_insert_right ex_in_conv fold_simps(1,2) insert_absorb insert_not_empty sup.absorb_iff1)
  qed
qed

lemmas nfa_univ_trans_correct = nfa_univ_trans_correct1 nfa_univ_trans_correct2

definition nfa_univ :: "'a set \<Rightarrow> (unit, 'a) nfa" where
  "nfa_univ U \<equiv> \<lparr>
    transitions = nfa_univ_trans () U,
    start = (),
    finals = {()}
  \<rparr>"

lemma nfa_univ_lang[simp]: "nfa_lang (nfa_univ U) = {w. set w \<subseteq> U}"
proof -
  define \<delta> where "\<delta> \<equiv> nfa_univ_trans () U"
  have "\<And>w. set w \<subseteq> U \<longleftrightarrow> () \<in> steps \<delta> w ()"
    unfolding \<delta>_def using nfa_univ_trans_correct by fast
  then show ?thesis
    by (auto simp: \<delta>_def nfa_univ_def)
qed

subsubsection\<open>Fixed Character with arbitrary prefix/suffix\<close>

text\<open>
  Similarily to the automaton above, this automaton accepts exactly those words,
  that contain a specific letter \<open>c\<close> at some point, and whose prefix and suffix
  are contained within the provided alphabets \<open>PU\<close> and \<open>SU\<close>.
\<close>

definition nfa_fixc_ps_trans :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> (nat \<times> 'a \<times> nat) set" where
  "nfa_fixc_ps_trans c PU SU \<equiv> nfa_univ_trans 0 PU \<union> {(0, c, 1)} \<union> nfa_univ_trans 1 SU"

lemma nfa_fixc_ps_trans_fin: "finite PU \<Longrightarrow> finite SU \<Longrightarrow> finite (nfa_fixc_ps_trans c PU SU)"
  by (auto intro: nfa_univ_trans_fin simp: nfa_fixc_ps_trans_def)

lemma nfa_fixc_ps_trans_correct1:
  "(\<exists>p s. w = p@[c]@s \<and> set p \<subseteq> PU \<and> set s \<subseteq> SU) \<Longrightarrow> 1 \<in> steps (nfa_fixc_ps_trans c PU SU) w 0"
proof -
  assume "\<exists>p s. w = p@[c]@s \<and> set p \<subseteq> PU \<and> set s \<subseteq> SU"
  then obtain p s where "w = p@[c]@s" and "set p \<subseteq> PU" and "set s \<subseteq> SU"
    by blast
  moreover have "0 \<in> steps (nfa_fixc_ps_trans c PU SU) p 0"
    by (metis calculation(2) nfa_fixc_ps_trans_def nfa_steps_union nfa_univ_trans_correct1 singletonI)
  moreover have "1 \<in> steps (nfa_fixc_ps_trans c PU SU) [c] 0"
    unfolding nfa_fixc_ps_trans_def Steps_def Step_def step_def by force
  moreover have "1 \<in> steps (nfa_fixc_ps_trans c PU SU) s 1"
    by (metis calculation(3) inf_sup_ord(3) insertI1 nfa_fixc_ps_trans_def nfa_steps_mono nfa_univ_trans_correct1 sup_commute)
  ultimately show "1 \<in> steps (nfa_fixc_ps_trans c PU SU) w 0"
    using Steps_join by meson
qed

lemma nfa_fixc_ps_trans_correct2:
  assumes "1 \<in> steps (nfa_fixc_ps_trans c PU SU) w 0"
  shows "\<exists>p s. w = p@[c]@s \<and> set p \<subseteq> PU \<and> set s \<subseteq> SU"
proof -
  define \<delta>\<^sub>A where [simp]: "\<delta>\<^sub>A \<equiv> nfa_univ_trans (0::nat) PU"
  define \<delta>\<^sub>B where [simp]: "\<delta>\<^sub>B \<equiv> nfa_univ_trans (1::nat) SU"

  have "1 \<in> steps (\<delta>\<^sub>A \<union> {(0, c, 1)} \<union> \<delta>\<^sub>B) w 0"
    using assms by (simp add: nfa_fixc_ps_trans_def)
  then have "\<exists>w\<^sub>A w\<^sub>B. w = w\<^sub>A@[c]@w\<^sub>B \<and> 0 \<in> steps \<delta>\<^sub>A w\<^sub>A 0 \<and> 1 \<in> steps \<delta>\<^sub>B w\<^sub>B 1"
    by (intro nfa_merge[where A="{0}" and B="{1}"]) (simp add: nfa_univ_trans_def)+
  then obtain w\<^sub>A w\<^sub>B where w_split: "w = w\<^sub>A@[c]@w\<^sub>B" and "0 \<in> steps \<delta>\<^sub>A w\<^sub>A 0" and "1 \<in> steps \<delta>\<^sub>B w\<^sub>B 1"
    by blast
  then have "set w\<^sub>A \<subseteq> PU" and "set w\<^sub>B \<subseteq> SU"
    using nfa_univ_trans_correct2 by fastforce+
  then show ?thesis
    using w_split by blast
qed

lemmas nfa_fixc_ps_trans_correct = nfa_fixc_ps_trans_correct1 nfa_fixc_ps_trans_correct2

definition nfa_fixc_ps :: "'a \<Rightarrow> 'a set \<Rightarrow> (nat, 'a) nfa" where
  "nfa_fixc_ps c U \<equiv> \<lparr>
    transitions = nfa_fixc_ps_trans c U U,
    start = 0,
    finals = {1}
  \<rparr>"

lemma nfa_fixc_ps_lang: "nfa_lang (nfa_fixc_ps c U) = { \<alpha>@[c]@\<beta> | \<alpha> \<beta>. set \<alpha> \<subseteq> U \<and> set \<beta> \<subseteq> U }"
  using nfa_fixc_ps_trans_correct unfolding nfa_fixc_ps_def
  by (metis (lifting) disjoint_insert(2) inf_bot_right select_convs(1,2,3))

subsubsection\<open>Singleton Language\<close>

text\<open>
  Last but not least, the automaton accepting exactly a single word can be inductively defined.
\<close>

lemma nfa_steps_empty_trans: "w \<noteq> [] \<Longrightarrow> steps {} w q\<^sub>0 = {}"
proof (induction w)
  case Nil
  then show ?case
    by simp
next
  case (Cons w ws)
  moreover have "Steps {} [w] {q\<^sub>0} = {}"
    by (simp add: Steps_def Step_def step_def)
  moreover have "Steps {} ws {} = {}"
    using Steps_noState by fast
  ultimately show ?case
    by (simp add: Steps_def)
qed

fun nfa_word_trans :: "'a list \<Rightarrow> (nat \<times> 'a \<times> nat) set" where
  "nfa_word_trans (w#ws) = nfa_word_trans ws \<union> {(Suc (length ws), w, length ws)}" |
  "nfa_word_trans [] = {}"

lemma nfa_word_trans_domain:
  "(q, c, q') \<in> nfa_word_trans ws \<Longrightarrow> q \<le> length ws \<and> q' \<le> length ws"
  by (induction ws) auto

definition nfa_word :: "'a list \<Rightarrow> (nat, 'a) nfa" where
  "nfa_word ws \<equiv> \<lparr> transitions = nfa_word_trans ws, start = length ws, finals = {0} \<rparr>"

lemma nfa_word_trans_correct1:
  "0 \<in> steps (nfa_word_trans ws) ws (length ws)"
proof (induction ws)
  case Nil
  then show ?case
    by (simp add: Steps_def)
next
  case (Cons w ws)
  have "0 \<in> steps (nfa_word_trans ws) ws (length ws)"
    using Cons.IH(1) by blast
  then have "0 \<in> steps (nfa_word_trans (w#ws)) ws (length ws)"
    using nfa_steps_mono by (metis nfa_word_trans.simps(1) sup_ge1)
  moreover have "length ws \<in> steps (nfa_word_trans (w#ws)) [w] (Suc (length ws))"
  proof -
    have "(Suc (length ws), w, length ws) \<in> nfa_word_trans (w#ws)"
      by simp
    then show ?thesis
      unfolding Steps_def Step_def step_def by force
  qed
  ultimately show ?case
    using Steps_join by force
qed

lemma nfa_word_trans_correct2:
  "0 \<in> steps (nfa_word_trans ws) ws' (length ws) \<Longrightarrow> ws = ws'"
proof (induction ws arbitrary: ws')
  case Nil
  then show ?case
    by (simp, metis equals0D nfa_steps_empty_trans)
next
  case (Cons w ws)

  \<comment> \<open>Preparation to use \texttt{nfa\_merge} lemma:\<close>
  define \<delta>\<^sub>B where [simp]: "\<delta>\<^sub>B \<equiv> nfa_word_trans ws"
  define B where [simp]: "B \<equiv> {n. n \<le> length ws}"
  define \<delta> where [simp]: "\<delta> \<equiv> {} \<union> {(Suc (length ws), w, length ws)} \<union> \<delta>\<^sub>B"

  \<comment> \<open>Apply the \texttt{nfa\_merge} lemma:\<close>
  have "0 \<in> steps \<delta> ws' (length (w#ws))"
    using Cons.prems by simp
  moreover have "\<forall>(q, c, q')\<in>\<delta>\<^sub>B. q \<in> B \<and> q' \<in> B"
    using nfa_word_trans_domain by force
  ultimately have "\<exists>w\<^sub>A w\<^sub>B. ws' = w\<^sub>A@[w]@w\<^sub>B \<and> (Suc (length ws)) \<in> steps {} w\<^sub>A (Suc (length ws)) \<and> 0 \<in> steps \<delta>\<^sub>B w\<^sub>B (length ws)"
    by (intro nfa_merge[where A="{Suc (length ws)}" and B=B]) simp+
  then obtain w\<^sub>A w\<^sub>B where ws'_split: "ws' = w\<^sub>A@[w]@w\<^sub>B"
      and w\<^sub>A_step: "(length (w#ws)) \<in> steps {} w\<^sub>A (length (w#ws))"
      and w\<^sub>B_step: "0 \<in> steps \<delta>\<^sub>B w\<^sub>B (length ws)"
    by force

  \<comment> \<open>Deduce that \<open>w\<^sub>A = []\<close>:\<close>
  have "w\<^sub>A = []"
    using w\<^sub>A_step nfa_steps_empty_trans by fast

  \<comment> \<open>Use IH to show that \<open>w\<^sub>B = ws\<close>:\<close>
  have "ws = w\<^sub>B"
    by (intro Cons.IH, use w\<^sub>B_step in simp)

  then show ?case
    using ws'_split by (simp add: \<open>w\<^sub>A = []\<close> \<open>ws = w\<^sub>B\<close>)
qed

lemmas nfa_word_trans_correct = nfa_word_trans_correct1 nfa_word_trans_correct2

lemma nfa_word_lang[simp]: "nfa_lang (nfa_word w) = {w}"
  unfolding nfa_word_def using nfa_word_trans_correct[of w] by fastforce

lemma nfa_word_finite_trans: "finite (transitions (nfa_word w))"
proof -
  have "finite (nfa_word_trans w)"
    by (induction w) simp+
  then show ?thesis
    by (simp add: nfa_word_def)
qed

end \<comment>\<open>end-theory FiniteAutomaton\<close>
