section\<open>Finite Automata\<close>

theory FiniteAutomaton
  imports "HOL-Data_Structures.Define_Time_Function"
begin \<comment>\<open>begin-theory FiniteAutomaton\<close>

subsection\<open>Definition\<close>

record ('s, 't) nfa =
  transitions :: "('s \<times> 't \<times> 's) set"
  start :: 's
  finals :: "'s set"

subsection\<open>Step Relation\<close>

definition step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's \<Rightarrow> 's set" where
  "step T c s = { s' | s'. (s, c, s') \<in> T }"

definition Step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Step T c s = { s' | s'. \<exists>s\<^sub>0 \<in> s. s' \<in> step T c s\<^sub>0 }"

definition Steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's set \<Rightarrow> 's set" where
  "Steps T w s = fold (Step T) w s"

abbreviation steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's \<Rightarrow> 's set" where
  "steps T w s \<equiv> Steps T w {s}"

lemma Steps_mono:
  assumes "s\<^sub>1 \<subseteq> s\<^sub>2"
  shows "Steps T w s\<^sub>1 \<subseteq> Steps T w s\<^sub>2"
proof (insert assms; induction w arbitrary: s\<^sub>1 s\<^sub>2)
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

\<comment>\<open>Sanity check that a monotonicity rule is really defined:\<close>
lemma [mono]: "mono (Steps T w)"
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
  using assms Steps_split by meson

lemma Steps_join3:
  assumes "q' \<in> steps T w\<^sub>1 q\<^sub>0" and "q'' \<in> steps T w\<^sub>2 q'" and "q\<^sub>f \<in> steps T w\<^sub>3 q''"
  shows "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2@w\<^sub>3) q\<^sub>0"
  using assms Steps_join by metis

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

end \<comment>\<open>end-theory FiniteAutomaton\<close>
