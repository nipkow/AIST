section\<open>Computation\<close>

text\<open>In this theory, we show a core theorem:
the predecessors of a regular language w.r.t. to a context-free grammar
also form a regular language. The regular languages are represented as automata.
\<close>

theory Algorithm
  imports Definition FiniteAutomaton "HOL-Library.While_Combinator"
begin

text\<open>
  Particularly, we formalise an algorithm proposed by Book and Otto \cite{book1993string},
  which takes as input a non-deterministic finite automaton \<open>M\<close> and modifies it to
  another automaton \<open>M'\<close> such that \<open>L(M') = pre\<^sup>*(L(M))\<close>.
\<close>

subsection\<open>Definition as Fixpoint\<close>

text\<open>
  The algorithm works by repeatedly adding transitions, such that at after every step,
  the NFA accepts the original language and its \textbf{direct} predecessors.
\<close>

text\<open>
  Since no new states are added, the amount of transitions that can ever be added are finitely bounded,
  which allow to both prove termination and the property of a fixpoint:
  At some point, adding another layor of direct predecessors no-longer changes anything,
  so the reflexive transitive closure of \<open>pre\<^sup>*\<close> is achieved.
\<close>

type_synonym ('s, 't) Trans = "('s \<times> 't \<times> 's) set"

definition prestar_step :: "('n, 't) Prods \<Rightarrow> 's set
    \<Rightarrow> ('s, ('n, 't) sym) Trans \<Rightarrow> ('s, ('n, 't) sym) Trans" where
  "prestar_step P Q \<delta> = { (q, Nt A, q') | q q' A. \<exists>\<beta>.
    (A, \<beta>) \<in> P \<and> q' \<in> steps \<delta> \<beta> q \<and> q \<in> Q \<and> q' \<in> Q }"

lemma prestar_step_code'[code]: "prestar_step P Q \<delta> =
   (\<lambda>(q, q', A\<beta>). (q, Nt (fst A\<beta>), q')) ` {(q, q', A\<beta>) \<in> Q \<times> Q \<times> P. q' \<in> steps \<delta> (snd A\<beta>) q}"
  unfolding prestar_step_def image_def by(auto)

definition prestar_while :: "('n, 't) Prods \<Rightarrow> 's set
    \<Rightarrow> ('s, ('n, 't) sym) Trans \<Rightarrow> ('s, ('n, 't) sym) Trans option" where
  "prestar_while P Q \<equiv> while_option (\<lambda>\<delta>. \<delta> \<union> prestar_step P Q \<delta> \<noteq> \<delta>) (\<lambda>\<delta>. \<delta> \<union> prestar_step P Q \<delta>)"

(* A random example, needs the types! *)
value "prestar_while {(0::int,[Tm(1::nat)])} {True} {}"

lemma prestar_while_rule:
  assumes "(\<And>\<delta>. H \<delta> \<Longrightarrow> \<delta> \<union> prestar_step P Q \<delta> \<noteq> \<delta> \<Longrightarrow> H (\<delta> \<union> prestar_step P Q \<delta>))"
    and "prestar_while P Q \<delta> = Some \<delta>'" and "H \<delta>"
  shows "H \<delta>'"
  using assms unfolding prestar_while_def by (rule while_option_rule)

lemma prestar_while_fp: "prestar_while P Q \<delta> = Some \<delta>' \<Longrightarrow> \<delta>' \<union> (prestar_step P Q \<delta>') = \<delta>'"
  unfolding prestar_while_def using while_option_stop by fast

lemma prestar_while_mono: "prestar_while P Q \<delta> = Some \<delta>' \<Longrightarrow> \<delta> \<subseteq> \<delta>'"
  by (rule prestar_while_rule) blast+

subsection\<open>Propagation of Reachability\<close>

text\<open>
  No new states are added. Expressing this fact within the used NFA model is to show that the
  set of reachable states from any given starting state remains unaltered.
\<close>

lemma prestar_step_reachable:
  "reachable_from \<delta> q = reachable_from (\<delta> \<union> prestar_step P Q \<delta>) q"
  unfolding prestar_step_def by (rule reachable_add_trans) blast

lemma prestar_while_reachable:
  assumes "prestar_while P Q \<delta> = Some \<delta>'"
  shows "reachable_from \<delta> q = reachable_from \<delta>' q"
  by (rule prestar_while_rule; use assms prestar_step_reachable in fast)

lemma prestar_while_inQ:
  assumes "prestar_while P Q \<delta> = Some \<delta>'" and "\<forall>(q,_,q') \<in> \<delta>. q \<in> Q \<and> q' \<in> Q"
  shows "\<forall>(q,_,q') \<in> \<delta>'. q \<in> Q \<and> q' \<in> Q"
  apply (rule prestar_while_rule)
  unfolding prestar_step_def by (use assms prestar_step_def in fast)+

subsection\<open>Correctness\<close>

lemma prestar_step_keeps:
  assumes "q' \<in> steps \<delta> \<beta> q"
  shows "q' \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) \<beta> q"
  using assms nfa_mono by (metis insert_absorb insert_subset sup_ge1)

lemma prestar_step_prod:
  assumes "(A, \<beta>) \<in> P" and "q \<in> Q" and "q' \<in> Q" and "q' \<in> steps \<delta> \<beta> q"
  shows "q' \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) [Nt A] q"
  using assms unfolding prestar_step_def Steps_def Step_def step_def by force

lemma prestar_step_pre:
  assumes "P \<turnstile> w\<^sub>\<alpha> \<Rightarrow> w\<^sub>\<beta>" and "reachable_from \<delta> q \<subseteq> Q" and "q' \<in> steps \<delta> w\<^sub>\<beta> q"
  shows "q' \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) w\<^sub>\<alpha> q"
proof -
  obtain w\<^sub>p w\<^sub>s A \<beta> where prod: "(A, \<beta>) \<in> P"
      and w\<^sub>\<alpha>_split: "w\<^sub>\<alpha> = w\<^sub>p@[Nt A]@w\<^sub>s"
      and w\<^sub>\<beta>_split: "w\<^sub>\<beta> = w\<^sub>p@\<beta>@w\<^sub>s"
    using assms(1) by (meson derive.cases)

  obtain q1 q2 where step_w\<^sub>p: "q1 \<in> steps \<delta> w\<^sub>p q"
      and step_\<beta>: "q2 \<in> steps \<delta> \<beta> q1"
      and step_w\<^sub>s: "q' \<in> steps \<delta> w\<^sub>s q2"
    using Steps_split3 assms(3)[unfolded w\<^sub>\<beta>_split] by fast
  then have q1_reach: "q1 \<in> reachable_from \<delta> q" and "q2 \<in> reachable_from \<delta> q1"
    using assms(2) unfolding reachable_from_def by blast+
  then have q2_reach: "q2 \<in> reachable_from \<delta> q"
    using assms(2) reachable_from_trans by fast

  have "q2 \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) [Nt A] q1"
    by (rule prestar_step_prod; use q1_reach q2_reach assms(2) prod step_\<beta> in blast)
  moreover have "q1 \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) w\<^sub>p q"
      and "q' \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) w\<^sub>s q2"
    using step_w\<^sub>p step_w\<^sub>s prestar_step_keeps by fast+
  ultimately have "q' \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) w\<^sub>\<alpha> q"
    unfolding w\<^sub>\<alpha>_split using Steps_join3 by fast
  then show ?thesis .
qed

lemma prestar_step_fp:
  assumes "P \<turnstile> w\<^sub>\<alpha> \<Rightarrow>* w\<^sub>\<beta>" and "reachable_from \<delta> q \<subseteq> Q" and "q' \<in> steps \<delta> w\<^sub>\<beta> q"
    and fp: "\<delta> \<union> prestar_step P Q \<delta> = \<delta>"
  shows "q' \<in> steps \<delta> w\<^sub>\<alpha> q"
proof (insert assms, induction rule: converse_rtranclp_induct[where r="derive P"])
  case base thus ?case by simp
next
  case (step y z)
  then show ?case
    using prestar_step_pre by fastforce
qed

lemma prestar_step_while:
  assumes "P \<turnstile> w\<^sub>\<alpha> \<Rightarrow>* w\<^sub>\<beta>" and "reachable_from \<delta> q \<subseteq> Q" and "q' \<in> steps \<delta> w\<^sub>\<beta> q"
    and "prestar_while P Q \<delta> = Some \<delta>'"
  shows "q' \<in> steps \<delta>' w\<^sub>\<alpha> q"
proof -
  have "\<delta>' \<union> prestar_step P Q \<delta>' = \<delta>'"
    using assms(4) by (rule prestar_while_fp)
  moreover have "reachable_from \<delta>' q \<subseteq> Q"
    using assms(2,4) prestar_while_reachable by fast
  moreover have "q' \<in> steps \<delta>' w\<^sub>\<beta> q"
    by (rule nfa_steps_mono[where \<delta>\<^sub>1=\<delta>]; use assms(3,4) prestar_while_mono in blast)
  ultimately show ?thesis
    using assms(1) prestar_step_fp by fast
qed

lemma prestar_step_sub_aux:
  assumes "q' \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) w q"
  shows "\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps \<delta> w' q"
proof (insert assms, induction w arbitrary: q)
  case Nil
  then show ?case
    by (simp add: Steps_def)
next
  case (Cons c w)
  then obtain q1 where step_w: "q' \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) w q1"
      and step_c: "q1 \<in> steps (\<delta> \<union> prestar_step P Q \<delta>) [c] q"
    using Steps_split by (metis (no_types, lifting) append_Cons append_Nil)

  obtain w' where "q' \<in> steps \<delta> w' q1" and "P \<turnstile> w \<Rightarrow>* w'"
    using Cons step_w by blast

  have "\<exists>c'. q1 \<in> steps \<delta> c' q \<and> P \<turnstile> [c] \<Rightarrow>* c'"
  proof (cases "q1 \<in> steps \<delta> [c] q")
    case True
    then show ?thesis
      by blast
  next
    case False
    then have "q1 \<in> steps (prestar_step P Q \<delta>) [c] q"
      using step_c unfolding Steps_def Step_def step_def by force
    then have "(q, c, q1) \<in> prestar_step P Q \<delta>"
      by (auto simp: Steps_def Step_def step_def)
    then obtain A \<beta> where "(A, \<beta>) \<in> P" and "c = Nt A" and "q1 \<in> steps \<delta> \<beta> q"
      unfolding prestar_step_def by blast
    moreover have "P \<turnstile> [c] \<Rightarrow>* \<beta>"
      using calculation by (simp add: derive_singleton r_into_rtranclp)
    ultimately show ?thesis
      by blast
  qed
  then obtain c' where "q1 \<in> steps \<delta> c' q" and "P \<turnstile> [c] \<Rightarrow>* c'"
    by blast

  have "q' \<in> steps \<delta> (c'@w') q"
    using \<open>q1 \<in> steps \<delta> c' q\<close> \<open>q' \<in> steps \<delta> w' q1\<close> Steps_join by fast
  moreover have "P \<turnstile> (c#w) \<Rightarrow>* (c'@w')"
    using \<open>P \<turnstile> [c] \<Rightarrow>* c'\<close> \<open>P \<turnstile> w \<Rightarrow>* w'\<close>
    by (metis (no_types, opaque_lifting) Cons_eq_appendI derives_append_decomp self_append_conv2)
  ultimately show ?case
    by blast
qed

lemma prestar_step_sub:
  assumes "\<forall>w. (q' \<in> steps \<delta>' w q) \<longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps \<delta> w' q)"
    and "q' \<in> steps (\<delta>' \<union> prestar_step P Q \<delta>') w q"
  shows "\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps \<delta> w' q"
proof -
  obtain w' where "P \<turnstile> w \<Rightarrow>* w'" and "q' \<in> steps \<delta>' w' q"
    using prestar_step_sub_aux assms by fast
  then obtain w'' where "P \<turnstile> w' \<Rightarrow>* w''" and "q' \<in> steps \<delta> w'' q"
    using assms(1) by blast
  moreover have "P \<turnstile> w \<Rightarrow>* w''"
    using \<open>P \<turnstile> w \<Rightarrow>* w'\<close> calculation(1) by simp
  ultimately show ?thesis
    by blast
qed

lemma prestar_while_sub:
  assumes "prestar_while P Q \<delta> = Some \<delta>'"
  shows "(q' \<in> steps \<delta>' w q) \<Longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps \<delta> w' q)"
proof -
  let ?I = "\<lambda>\<delta>'. \<forall>w. (q' \<in> steps \<delta>' w q) \<longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps \<delta> w' q)"
  have "\<And>\<delta>'. ?I \<delta>' \<Longrightarrow> ?I (\<delta>' \<union> prestar_step P Q \<delta>')"
    by (simp add: prestar_step_sub[where \<delta>=\<delta>])
  then have "?I \<delta>'"
    by (rule prestar_while_rule[where \<delta>=\<delta> and \<delta>'=\<delta>']; use assms in blast)
  then show "(q' \<in> steps \<delta>' w q) \<Longrightarrow> (\<exists>w'. P \<turnstile> w \<Rightarrow>* w' \<and> q' \<in> steps \<delta> w' q)"
    by simp
qed

lemma prestar_while_correct:                 
  assumes "reachable_from \<delta> q\<^sub>0 \<subseteq> Q" and "prestar_while P Q \<delta> = Some \<delta>'"
  shows "lang_trans \<delta>' q\<^sub>0 F = pre_star P (lang_trans \<delta> q\<^sub>0 F)"
proof (standard; standard)
  fix w
  assume "w \<in> lang_trans \<delta>' q\<^sub>0 F"
  then obtain q\<^sub>f where "q\<^sub>f \<in> steps \<delta>' w q\<^sub>0" and "q\<^sub>f \<in> F"
    by blast
  then obtain w' where "P \<turnstile> w \<Rightarrow>* w'" and "q\<^sub>f \<in> steps \<delta> w' q\<^sub>0"
    using prestar_while_sub assms by fast
  moreover have "w' \<in> lang_trans \<delta> q\<^sub>0 F"
    using calculation \<open>q\<^sub>f \<in> F\<close> by blast
  ultimately show "w \<in> pre_star P (lang_trans \<delta> q\<^sub>0 F)"
    unfolding pre_star_def by blast
next
  fix w
  assume "w \<in> pre_star P (lang_trans \<delta> q\<^sub>0 F)"
  then obtain w' where "P \<turnstile> w \<Rightarrow>* w'" and "w' \<in> lang_trans \<delta> q\<^sub>0 F"
    unfolding pre_star_def by blast
  then obtain q\<^sub>f where "q\<^sub>f \<in> steps \<delta> w' q\<^sub>0" and "q\<^sub>f \<in> F"
    by blast
  then have "q\<^sub>f \<in> steps \<delta>' w' q\<^sub>0"
    using nfa_mono prestar_while_mono assms by (metis in_mono)
  moreover have "reachable_from \<delta>' q\<^sub>0 \<subseteq> Q"
    using assms prestar_while_reachable by fast
  moreover have "\<delta>' \<union> prestar_step P Q \<delta>' = \<delta>'"
    by (rule prestar_while_fp; use assms(2) in simp)
  moreover note \<open>P \<turnstile> w \<Rightarrow>* w'\<close>
  ultimately have "q\<^sub>f \<in> steps \<delta>' w q\<^sub>0"
    by (elim prestar_step_fp) simp+
  with \<open>q\<^sub>f \<in> F\<close> show "w \<in> lang_trans \<delta>' q\<^sub>0 F"
    by blast
qed

subsection\<open>Termination\<close>

lemma while_option_finite_subset_Some':
  fixes C :: "'a set"
  assumes "mono f" and "\<And>X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C" and "S \<subseteq> C" and "\<And>X. X \<subseteq> f X"
  shows "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f S = Some P"
proof (rule measure_while_option_Some[where
    f= "%A::'a set. card C - card A" and P= "%A. A \<subseteq> C \<and> A \<subseteq> f A" and s=S])
  fix A assume A: "A \<subseteq> C \<and> A \<subseteq> f A" "f A \<noteq> A"
  show "(f A \<subseteq> C \<and> f A \<subseteq> f (f A)) \<and> card C - card (f A) < card C - card A"
    (is "?L \<and> ?R")
  proof
    show ?L by (metis A(1) assms(2) monoD[OF \<open>mono f\<close>])
    show ?R by (metis A assms(2,3) card_seteq diff_less_mono2 equalityI linorder_le_less_linear rev_finite_subset)
  qed
qed (simp add: assms)

lemma prestar_while_terminates:
  fixes P :: "('n, 't) Prods" and Q :: "'s set" and \<delta>\<^sub>0 :: "('s, ('n, 't) sym) Trans"
  assumes "finite P" and "finite Q" and "finite \<delta>\<^sub>0"
  shows "\<exists>\<delta>. prestar_while P Q \<delta>\<^sub>0 = Some \<delta>"
proof -
  define b :: "('s, ('n, 't) sym) Trans \<Rightarrow> bool" where
    [simp]: "b = (\<lambda>\<delta>. \<delta> \<union> prestar_step P Q \<delta> \<noteq> \<delta>)"
  define f :: "('s, ('n, 't) sym) Trans \<Rightarrow> ('s, ('n, 't) sym) Trans" where
    [simp]: "f = (\<lambda>\<delta>. \<delta> \<union> prestar_step P Q \<delta>)"
  then have "mono f"
    unfolding mono_def prestar_step_def
    by (smt (verit, ccfv_threshold) UnCI UnE in_mono mem_Collect_eq nfa_mono' subsetI)

  define U :: "('s, ('n, 't) sym) Trans" where
    "U = { (q, Nt A, q') | q q' A. \<exists>\<beta>. (A, \<beta>) \<in> P \<and> q \<in> Q \<and> q' \<in> Q } \<union> \<delta>\<^sub>0"
  moreover have "\<And>\<delta>. prestar_step P Q \<delta> \<subseteq> U"
    unfolding U_def prestar_step_def by blast
  ultimately have U_bounds: "\<And>X. X \<subseteq> U \<Longrightarrow> f X \<subseteq> U"
    by simp

  have "finite U"
  proof -
    define U' :: "('s, ('n, 't) sym) Trans" where
      [simp]: "U' = Q \<times> ((\<lambda>(A,_). Nt A) ` P) \<times> Q"
    have "finite ((\<lambda>(A,_). Nt A) ` P)"
      using assms(1) by simp
    then have "finite U'"
      using assms(2) U'_def by blast

    define \<delta>' :: "('s, ('n, 't) sym) Trans" where
      [simp]: "\<delta>' = { (q,Nt A,q') | q q' A. \<exists>\<beta>. (A, \<beta>) \<in> P \<and> q \<in> Q \<and> q' \<in> Q }"
    then have "\<delta>' \<subseteq> U'"
      unfolding \<delta>'_def U'_def using assms(1) by fast
    moreover note \<open>finite U'\<close>
    ultimately have "finite \<delta>'"
      using rev_finite_subset[of U' \<delta>'] by blast
    then show "finite U"
      by (simp add: U_def assms(3))
  qed

  note criteria = \<open>finite U\<close> U_def f_def U_bounds \<open>mono f\<close>
  have "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f \<delta>\<^sub>0 = Some P"
    by (rule while_option_finite_subset_Some'[where C=U]; use criteria in blast)
  then show ?thesis
    by (simp add: prestar_while_def)
qed

subsection\<open>Computability\<close>

text\<open>
  While the definition of @{term prestar_step} is semantically correct,
  Isabelle cannot automatically compute it.
  The following code equations ensure computability, as long as \<open>P\<close>, \<open>Q\<close> and \<open>\<delta>\<close> are finite.
\<close>

definition prestar_step_prod_code :: "('s, ('n, 't) sym) Trans \<Rightarrow> 's set \<Rightarrow> ('n, 't) prod \<Rightarrow> ('s, ('n, 't) sym) Trans" where
  "prestar_step_prod_code \<delta> Q p \<equiv> (\<lambda>(s\<^sub>1, s\<^sub>2). (s\<^sub>1, Nt (fst p), s\<^sub>2)) ` {(s\<^sub>1, s\<^sub>2) \<in> Q \<times> Q. s\<^sub>2 \<in> steps \<delta> (snd p) s\<^sub>1}"

definition prestar_step_code :: "('s, ('n, 't) sym) Trans \<Rightarrow> 's set \<Rightarrow> ('n, 't) Prods \<Rightarrow> ('s, ('n, 't) sym) Trans" where
  "prestar_step_code \<delta> Q P \<equiv> \<Union>(prestar_step_prod_code \<delta> Q ` P)"

lemma prestar_step_prod_code_correct:
  "prestar_step_prod_code \<delta> Q p = { (q, Nt (fst p), q') | q q'. q' \<in> steps \<delta> (snd p) q \<and> q \<in> Q \<and> q' \<in> Q }"
  by (auto simp: prestar_step_prod_code_def)

lemma prestar_step_code_correct: "(q, X, q') \<in> prestar_step_code \<delta> Q P \<longleftrightarrow> (q, X, q') \<in> prestar_step P Q \<delta>"
  unfolding prestar_step_code_def prestar_step_def prestar_step_prod_code_correct by force

lemma prestar_step_code[code]: "prestar_step P Q \<delta> = prestar_step_code \<delta> Q P"
  using prestar_step_code_correct by fast

definition prestar_code :: "('n, 't) Prods \<Rightarrow> ('s, ('n, 't) sym) nfa \<Rightarrow> ('s, ('n, 't) sym) nfa" where
  "prestar_code P M \<equiv> (
    let Q = {start M} \<union> (snd ` snd ` (transitions M)) in
    case prestar_while P Q (transitions M) of
      Some \<delta>' \<Rightarrow> M \<lparr> transitions := \<delta>' \<rparr>
  )"

lemma prestar_code_correct:
  assumes "finite P" and "finite (transitions M)"
  shows "lang_nfa (prestar_code P M) = pre_star P (lang_nfa M)"
proof -
  define \<delta> where "\<delta> \<equiv> transitions M"
  define Q where "Q \<equiv> {start M} \<union> (snd ` snd ` \<delta>)"
  then have "finite Q"
    unfolding \<delta>_def using assms(2) by simp
  then have "reachable_from \<delta> (start M) \<subseteq> Q"
    using reachable_from_computable Q_def by fast
  moreover obtain \<delta>' where \<delta>'_def: "prestar_while P Q \<delta> = Some \<delta>'"
    using prestar_while_terminates assms \<open>finite Q\<close> \<delta>_def by blast
  ultimately have "lang_trans \<delta>' (start M) (finals M) = pre_star P (lang_trans \<delta> (start M) (finals M))"
    by (rule prestar_while_correct)
  then have "lang_nfa (M \<lparr> transitions := \<delta>' \<rparr>) = pre_star P (lang_nfa M)"
    by (simp add: \<delta>_def)
  then show ?thesis
    unfolding prestar_code_def using Q_def \<delta>'_def \<delta>_def by force
qed

subsection\<open>Properties\<close>

lemma prestar_while_refl:
  assumes "prestar_while P Q \<delta> = Some \<delta>'" and "(A, []) \<in> P" and "q \<in> Q"
  shows "(q, Nt A, q) \<in> \<delta>'"
proof -
  have "q \<in> steps \<delta>' [] q"
    unfolding Steps_def using assms by force
  then have "(q, Nt A, q) \<in> prestar_step P Q \<delta>'"
    unfolding prestar_step_def using assms by blast
  moreover have "\<delta>' = \<delta>' \<union> (prestar_step P Q \<delta>')"
    using prestar_while_fp assms(1) by blast
  ultimately show ?thesis
    by blast
qed

lemma prestar_while_singleton:
  assumes "prestar_while P Q \<delta> = Some \<delta>'" and "(A, [B]) \<in> P"
    and "(q, B, q') \<in> \<delta>'" and "q \<in> Q" and "q' \<in> Q"
  shows "(q, Nt A, q') \<in> \<delta>'"
proof -
  have "q' \<in> steps \<delta>' [B] q"
    unfolding Steps_def Step_def step_def using assms by force
  then have "(q, Nt A, q') \<in> prestar_step P Q \<delta>'"
    unfolding prestar_step_def using assms by blast
  moreover have "\<delta>' = \<delta>' \<union> (prestar_step P Q \<delta>')"
    using prestar_while_fp assms(1) by blast
  ultimately show ?thesis
    by blast
qed

lemma prestar_while_impl:
  assumes "prestar_while P Q \<delta> = Some \<delta>'" and "(A, [B, C]) \<in> P"
    and "(q, B, q') \<in> \<delta>'" and "(q', C, q'') \<in> \<delta>'"
    and "q \<in> Q" and "q' \<in> Q" and "q'' \<in> Q"
  shows "(q, Nt A, q'') \<in> \<delta>'"
proof -
  have "q'' \<in> steps \<delta>' [B, C] q"
    unfolding Steps_def Step_def step_def using assms by force
  then have "(q, Nt A, q'') \<in> prestar_step P Q \<delta>'"
    unfolding prestar_step_def using assms by blast
  moreover have "\<delta>' = \<delta>' \<union> (prestar_step P Q \<delta>')"
    using prestar_while_fp assms(1) by blast
  ultimately show ?thesis
    by blast
qed

end \<comment>\<open>end-theory Algorithm\<close>
