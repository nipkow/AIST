section\<open>Finite Automata\<close>

theory FiniteAutomaton
  imports "HOL-Data_Structures.Define_Time_Function"
begin \<comment>\<open>begin-theory FiniteAutomaton\<close>

record ('s, 't) nfa =
  transitions :: "('s \<times> 't \<times> 's) set"
  start :: 's
  finals :: "'s set"

definition nfa_invar :: "('s, 't) nfa \<Rightarrow> bool" where
  "nfa_invar M \<equiv> finite (transitions M)"

fun step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's \<Rightarrow> 's set" where
  "step T c s = { s' | s'. (s, c, s') \<in> T }"

fun step' :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's set \<Rightarrow> 's set" where
  "step' T c s = { s' | s'. \<exists>s\<^sub>0 \<in> s. s' \<in> step T c s\<^sub>0 }"

fun steps':: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's set \<Rightarrow> 's set" where
  "steps' T w s = fold (step' T) w s"

fun steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's \<Rightarrow> 's set" where
  "steps T w s = steps' T w {s}"

lemma steps'_mono:
  assumes "s\<^sub>1 \<subseteq> s\<^sub>2"
  shows "steps' T w s\<^sub>1 \<subseteq> steps' T w s\<^sub>2"
proof (insert assms; induction w arbitrary: s\<^sub>1 s\<^sub>2)
  case Nil thus ?case by simp
next
  case (Cons a w)
  then show ?case
    by (smt (verit) fold_simps(2) mem_Collect_eq step'.simps steps'.simps subset_eq)
qed

lemma steps'_startExists:
  assumes "q\<^sub>f \<in> steps' T w s"
  shows "\<exists>q\<^sub>0 \<in> s. q\<^sub>f \<in> steps T w q\<^sub>0"
proof (insert assms; induction w arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons a w)
  then have "q\<^sub>f \<in> steps' T w (steps' T [a] s)"
    by simp
  then obtain q' where "q' \<in> steps' T [a] s" and "q\<^sub>f \<in> steps T w q'"
    using Cons by blast
  then have "q' \<in> step' T a s"
    by simp
  then obtain q\<^sub>0 where "q\<^sub>0 \<in> s" and "q' \<in> step T a q\<^sub>0"
    by fastforce
  then have "q' \<in> steps T [a] q\<^sub>0"
    by simp

  have "q\<^sub>f \<in> steps' T w (step T a q\<^sub>0)"
    using \<open>q\<^sub>f \<in> steps T w q'\<close> \<open>q' \<in> step T a q\<^sub>0\<close>
    by (metis (no_types, opaque_lifting) bot.extremum insert_subset steps'_mono steps.elims subset_eq)
  then have "q\<^sub>f \<in> steps' T w (steps T [a] q\<^sub>0)"
    by simp
  then have "q\<^sub>f \<in> steps T (a#w) q\<^sub>0"
    by simp
  then show ?case
    using \<open>q\<^sub>0 \<in> s\<close> by blast
qed

lemma steps_split:
  assumes "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2) q\<^sub>0"
  shows "\<exists>q'. q' \<in> steps T w\<^sub>1 q\<^sub>0 \<and> q\<^sub>f \<in> steps T w\<^sub>2 q'"
proof -
  define s\<^sub>f where [simp add]: "s\<^sub>f = steps T (w\<^sub>1@w\<^sub>2) q\<^sub>0"
  define s' where [simp add]: "s' = fold (step' T) w\<^sub>1 {q\<^sub>0}"

  have "s\<^sub>f = fold (step' T) (w\<^sub>1@w\<^sub>2) {q\<^sub>0}"
    by simp
  then have "q\<^sub>f \<in> s\<^sub>f"
    using assms by simp

  have "s\<^sub>f = fold (step' T) w\<^sub>2 s'"
    by simp
  then have "s\<^sub>f = steps' T w\<^sub>2 s'"
    by simp
  then obtain q' where "q' \<in> s'" and "q\<^sub>f \<in> steps T w\<^sub>2 q'"
    using steps'_startExists assms by fastforce
  moreover have "q' \<in> steps T w\<^sub>1 q\<^sub>0"
    using calculation by simp
  ultimately show ?thesis
    by blast
qed

lemma steps_split3:
  assumes "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2@w\<^sub>3) q\<^sub>0"
  shows "\<exists>q' q''. q' \<in> steps T w\<^sub>1 q\<^sub>0 \<and> q'' \<in> steps T w\<^sub>2 q' \<and> q\<^sub>f \<in> steps T w\<^sub>3 q''"
  using assms steps_split by metis

lemma steps_join:
  assumes "q' \<in> steps T w\<^sub>1 q\<^sub>0" and "q\<^sub>f \<in> steps T w\<^sub>2 q'"
  shows "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2) q\<^sub>0"
proof -
  define s' where [simp add]: "s' = steps T w\<^sub>1 q\<^sub>0"
  define s\<^sub>f where [simp add]: "s\<^sub>f = steps' T w\<^sub>2 s'"

  have "{q'} \<subseteq> s'"
    using assms(1) by simp
  then have "steps' T w\<^sub>2 {q'} \<subseteq> steps' T w\<^sub>2 s'"
    using steps'_mono by blast
  then have "q\<^sub>f \<in> steps' T w\<^sub>2 s'"
    using assms(2) by fastforce
  moreover have "s\<^sub>f = steps T (w\<^sub>1@w\<^sub>2) q\<^sub>0"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma steps_join3:
  assumes "q' \<in> steps T w\<^sub>1 q\<^sub>0" and "q'' \<in> steps T w\<^sub>2 q'" and "q\<^sub>f \<in> steps T w\<^sub>3 q''"
  shows "q\<^sub>f \<in> steps T (w\<^sub>1@w\<^sub>2@w\<^sub>3) q\<^sub>0"
  using assms steps_join by metis

fun accepts :: "('s, 't) nfa \<Rightarrow> 't list \<Rightarrow> bool" where
  "accepts M w = (steps (transitions M) w (start M) \<inter> finals M \<noteq> {})"

lemma accepts_split3:
  assumes "accepts M (w\<^sub>1@w\<^sub>2@w\<^sub>3)"
  shows "\<exists>q' q'' q\<^sub>f. q' \<in> steps (transitions M) w\<^sub>1 (start M) \<and> q'' \<in> steps (transitions M) w\<^sub>2 q' \<and> q\<^sub>f \<in> steps (transitions M) w\<^sub>3 q'' \<and> q\<^sub>f \<in> finals M"
  using assms steps_split3 accepts.simps by (metis Int_emptyI)

definition lang :: "('s, 't) nfa \<Rightarrow> ('t list) set" where
  "lang M \<equiv> { w | w. accepts M w }"

end \<comment>\<open>end-theory FiniteAutomaton\<close>
