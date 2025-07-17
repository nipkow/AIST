section\<open>A Criterion the for Finiteness of Context-Free Languages\<close>

theory Finiteness
  imports Definition
begin \<comment>\<open>begin-theory Finiteness\<close>

text\<open>
  A later result of a possible application of \<open>pre\<^sup>*\<close> will be determining whether a
  context-free language is finite or infinite.
  To formally prove this a criterion describing the finiteness of a context-free language
  has to be established first.
  Let \<open>G = (V, T, P, S)\<close> be a context-free language.
  In this section we will show, that \<open>L(G)\<close> is infinite if, and only if, there exists
  a non-terminal \<open>X \<in> V\<close> for which there exists a production:
  $$X \; \Rightarrow^* \; \alpha X \beta$$
  with \<open>\<alpha>, \<beta> \<in> (V \<union> T)\<^sup>*\<close> and \<open>\<alpha>\<beta> \<noteq> \<epsilon>\<close>.
  This represents the widely used criterion for the finiteness of a context-free language,
  however it has yet to be formally verified.
\<close>

subsection\<open>Preliminaries\<close>

text\<open>
  For the criterion to be correct, it is required that the context-free grammar only
  contains useful non-terminals (i.e. every non-terminal is reachable and productive),
  and that every non-terminal is non-nullable.
  In general, there exist algorithms that can reduce an arbitrary context-free grammar \<open>G\<close>
  to another context-free grammar \<open>G'\<close> with \<open>L(G') = L(G) \<setminus> {\<epsilon>}\<close> that only contains useful
  and non-nullable terminals.
  The language is only altered if \<open>\<epsilon> \<in> L(G)\<close>, otherwise it remains identical.
  This can be circumvented by explicitely allowing the single production \<open>S \<Rightarrow> \<epsilon>\<close>.
  However, for this specific use-case, we can generally ignore this edge case,
  since \<open>|L(G)| = \<infinity> \<longleftrightarrow> |L(G) \<setminus> {\<epsilon>}| = |L(G')| = \<infinity>\<close>,
  i.e. removing a single word does not affect the finiteness.
\<close>

text\<open>
  We use the definitions @{term is_useful} and @{term is_nullable} from the previous section
  and expand them to all non-terminals.
\<close>

definition (in CFG) is_useful_all :: "bool" where
  "is_useful_all \<equiv> (\<forall>X::'n. is_useful X)"

definition (in CFG) is_non_nullable_all :: "bool" where
  "is_non_nullable_all \<equiv> (\<forall>X::'n. \<not> is_nullable X)"

text\<open>
  A few lemmas are needed for more elegant reasoning of transitions.
\<close>

lemma (in CFG) derives_concat:
  assumes "X\<^sub>1 \<Rightarrow>\<^sup>* w\<^sub>1" and "X\<^sub>2 \<Rightarrow>\<^sup>* w\<^sub>2"
  shows "(X\<^sub>1@X\<^sub>2) \<Rightarrow>\<^sup>* (w\<^sub>1@w\<^sub>2)"
  using assms derives_append_decomp derives_eq by blast

lemma (in CFG) derives_split:
  assumes "X \<Rightarrow>\<^sup>* w"
  shows "\<exists>X\<^sub>1 X\<^sub>2 w\<^sub>1 w\<^sub>2. X = X\<^sub>1@X\<^sub>2 \<and> w = w\<^sub>1@w\<^sub>2 \<and> X\<^sub>1 \<Rightarrow>\<^sup>* w\<^sub>1 \<and> X\<^sub>2 \<Rightarrow>\<^sup>* w\<^sub>2"
  using assms by blast

lemma (in CFG) derives_step:
  assumes "X \<Rightarrow>\<^sup>* (\<alpha>@w\<^sub>1@\<beta>)" and "w\<^sub>1 \<Rightarrow>\<^sup>* w\<^sub>2"
  shows "X \<Rightarrow>\<^sup>* (\<alpha>@w\<^sub>2@\<beta>)"
  by (meson assms CFG_axioms derives_concat Nitpick.rtranclp_unfold rtranclp_trans)

text\<open>
  The necessity of only having useful non-terminals comes from the implication we will
  prove now: that every non-terminal can be resolved to a word.
  This can be extended to the following fact: every list of non-terminals and terminals
  can be resolved to a word.
  This removes the unfortunate case of ending up with a string of non-terminals and terminals,
  which contains an unresolvable non-terminal, practically leading to a dead end.
\<close>

lemma (in CFG) is_useful_all_derive:
  assumes "is_useful_all"
  shows "\<exists>w. xs \<Rightarrow>\<^sup>* map_word w"
using assms proof (induction xs)
  case Nil
  moreover have "[] \<Rightarrow>\<^sup>* map_word []"
    by simp
  ultimately show ?case
    by (elim exI)
next
  case (Cons a xs)
  then obtain w' where w'_def: "xs \<Rightarrow>\<^sup>* map_word w'"
    by blast

  have "\<exists>w. [a] \<Rightarrow>\<^sup>* map_word w"
  proof (cases a)
    case (Nt X)
    then have "is_productive X"
      using Cons(2) by (simp add: is_useful_all_def is_useful_def)
    then show ?thesis
      by (simp add: Nt is_productive_def)
  next
    case (Tm c)
    then have "[Tm c] \<Rightarrow>\<^sup>* map_word [c]"
      by simp
    then show ?thesis
      using Tm by blast
  qed
  then obtain w where w_def: "[a] \<Rightarrow>\<^sup>* map_word w"
    by blast

  from w_def w'_def have "(a#xs) \<Rightarrow>\<^sup>* map_word (w@w')"
    using derives_concat by fastforce
  then show ?case
    by blast
qed

text\<open>
  The second requirement, having no nullable non-terminals, has the benefit of preventing
  any string of non-terminals and terminals to shrink.
  This allows the criterion for the finiteness to be able to ``pump'' a string up to
  an arbitrary length, before resolving it to only terminals, without loosing any length to it.
\<close>

lemma (in CFG) is_non_nullable_all_derive:
  assumes "is_non_nullable_all" and "xs \<Rightarrow>\<^sup>* w"
  shows "xs = [] \<longleftrightarrow> w = []"
proof -
  have "\<And>X. \<not> [Nt X] \<Rightarrow>\<^sup>* []"
    using assms(1) by (simp add: is_non_nullable_all_def is_nullable_def)
  moreover have "\<And>c. \<not> [Tm c] \<Rightarrow>\<^sup>* []"
    using derives_eq by force
  ultimately have nonNullAll: "\<And>x. \<not> [x] \<Rightarrow>\<^sup>* []"
    using sym.exhaust by metis

  have thm1: "xs = [] \<Longrightarrow> w = []"
    using assms(2) derives_eq derives_from_empty by blast

  have thm2: "xs \<noteq> [] \<Longrightarrow> w \<noteq> []"
  proof
    assume "xs \<noteq> []"
    then obtain x xs' where "xs = x#xs'"
      using list.exhaust by blast
    moreover have "([x]@xs') \<Rightarrow>\<^sup>* [] \<Longrightarrow> ([x] \<Rightarrow>\<^sup>* [] \<and> xs' \<Rightarrow>\<^sup>* [])"
      using derives_split by (metis Nil_is_append_conv derives_append_decomp derives_eq)
    moreover have "\<not> [x] \<Rightarrow>\<^sup>* []"
      by (simp add: nonNullAll)
    ultimately show "w = [] \<Longrightarrow> False"
      using assms(2) by simp
  qed

  show ?thesis
    using thm1 thm2 by blast
qed

subsection\<open>The Criteria\<close>

text\<open>
  Finally, we introduce the definition @{term is_infinite}, which instead of making use
  of the language set, uses the criterion introduced above.
\<close>

definition (in CFG) is_infinite :: "bool" where
  "is_infinite \<equiv> (\<exists>X \<alpha> \<beta>. [Nt X] \<Rightarrow>\<^sup>* (\<alpha>@[Nt X]@\<beta>) \<and> \<alpha>@\<beta> \<noteq> [])"

fun (in CFG) is_infinite_derives :: "'n \<Rightarrow> ('n, 't) sym list \<Rightarrow> ('n, 't) sym list \<Rightarrow> nat \<Rightarrow> ('n, 't) sym list" where
  "is_infinite_derives X \<alpha> \<beta> (Suc n) = \<alpha>@(is_infinite_derives X \<alpha> \<beta> n)@\<beta>" |
  "is_infinite_derives X \<alpha> \<beta> 0 = [Nt X]"

fun (in CFG) is_infinite_words :: "'t list \<Rightarrow> 't list \<Rightarrow> 't list \<Rightarrow> nat \<Rightarrow> 't list" where
  "is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta> (Suc n) = w\<^sub>\<alpha>@(is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta> n)@w\<^sub>\<beta>" |
  "is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta> 0 = w\<^sub>X"

theorem (in CFG) is_infinite:
  assumes "is_useful_all" and "is_non_nullable_all"
  shows "\<not> finite (Lang P S) \<longleftrightarrow> is_infinite"
proof
  assume "\<not> finite (Lang P S)"
  show "is_infinite"
    sorry \<comment>\<open>This proof seems rather difficult.\<close>
next
  assume "is_infinite"
  then obtain X \<alpha> \<beta> where deriveX: "[Nt X] \<Rightarrow>\<^sup>* (\<alpha>@[Nt X]@\<beta>)" and "\<alpha>@\<beta> \<noteq> []"
    unfolding is_infinite_def by blast

  obtain w\<^sub>X where w\<^sub>X_def: "[Nt X] \<Rightarrow>\<^sup>* map_word w\<^sub>X"
    using assms(1) is_useful_all_derive by blast

  obtain w\<^sub>\<alpha> w\<^sub>\<beta> where w\<^sub>\<alpha>_def: "\<alpha> \<Rightarrow>\<^sup>* map_word w\<^sub>\<alpha>" and w\<^sub>\<beta>_def: "\<beta> \<Rightarrow>\<^sup>* map_word w\<^sub>\<beta>"
    using assms(1) is_useful_all_derive by blast+
  then have "w\<^sub>\<alpha>@w\<^sub>\<beta> \<noteq> []"
    using \<open>\<alpha>@\<beta> \<noteq> []\<close> by (simp add: assms(2) is_non_nullable_all_derive)

  define f\<^sub>d where "f\<^sub>d \<equiv> is_infinite_derives X \<alpha> \<beta>"
  define f\<^sub>w where "f\<^sub>w \<equiv> is_infinite_words w\<^sub>X w\<^sub>\<alpha> w\<^sub>\<beta>"

  have "is_reachable X"
    using assms(1) by (simp add: is_useful_all_def is_useful_def)
  then obtain p s where "[Nt S] \<Rightarrow>\<^sup>* (p@[Nt X]@s)"
    unfolding is_reachable_def by blast
  moreover obtain w\<^sub>p where w\<^sub>p_def: "p \<Rightarrow>\<^sup>* map_word w\<^sub>p"
    using assms(1) is_useful_all_derive by blast
  moreover obtain w\<^sub>s where w\<^sub>s_def: "s \<Rightarrow>\<^sup>* map_word w\<^sub>s"
    using assms(1) is_useful_all_derive by blast
  ultimately have fromS: "[Nt S] \<Rightarrow>\<^sup>* (map_word w\<^sub>p@[Nt X]@map_word w\<^sub>s)"
    by (meson local.derives_concat rtranclp.rtrancl_refl rtranclp_trans)

  have "\<And>i. [Nt X] \<Rightarrow>\<^sup>* f\<^sub>d i"
    subgoal for i
      apply (induction i; simp_all add: f\<^sub>d_def)
      apply (meson deriveX local.derives_concat rtranclp.rtrancl_refl rtranclp_trans)
      done
    done
  moreover have "\<And>i. f\<^sub>d i \<Rightarrow>\<^sup>* map_word (f\<^sub>w i)"
    subgoal for i
      by (induction i; simp add: f\<^sub>d_def f\<^sub>w_def w\<^sub>X_def w\<^sub>\<alpha>_def w\<^sub>\<beta>_def CFG_axioms derives_concat)
    done
  ultimately have "\<And>i. [Nt X] \<Rightarrow>\<^sup>* map_word (f\<^sub>w i)"
    using rtranclp_trans by fast
  then have "\<And>i. [Nt S] \<Rightarrow>\<^sup>* (map_word w\<^sub>p@map_word (f\<^sub>w i)@map_word w\<^sub>s)"
    using fromS derives_step by presburger
  then have "\<And>i. [Nt S] \<Rightarrow>\<^sup>* (map_word (w\<^sub>p@(f\<^sub>w i)@w\<^sub>s))"
    by simp
  moreover define f\<^sub>w' where f\<^sub>w'_def: "f\<^sub>w' = (\<lambda>i. w\<^sub>p @ (f\<^sub>w i) @ w\<^sub>s)"
  ultimately have "\<And>i. [Nt S] \<Rightarrow>\<^sup>* map_word (f\<^sub>w' i)"
    by simp
  then have "\<And>i. f\<^sub>w' i \<in> Lang P S"
    by (simp add: Lang_def derives_eq)
  then have "range f\<^sub>w' \<subseteq> Lang P S"
    by blast

  have "\<And>i. length (f\<^sub>w i) < length (f\<^sub>w (i+1))"
    subgoal for i
      by (induction i; use f\<^sub>w_def \<open>w\<^sub>\<alpha>@w\<^sub>\<beta> \<noteq> []\<close> in simp)
    done
  then have x: "\<And>i. length (f\<^sub>w' i) < length (f\<^sub>w' (i+1))"
    by (simp add: f\<^sub>w'_def)
  then have "\<And>i n. 0 < n \<Longrightarrow> length (f\<^sub>w' i) < length (f\<^sub>w' (i+n))"
    subgoal for i n
      apply (induction n, auto)
      apply (metis Suc_lessD add_cancel_left_right gr_zeroI less_trans_Suc)
      done
    done
  then have f\<^sub>w'_order: "\<And>i\<^sub>1 i\<^sub>2. i\<^sub>1 < i\<^sub>2 \<Longrightarrow> length (f\<^sub>w' i\<^sub>1) < length (f\<^sub>w' i\<^sub>2)"
    using less_imp_add_positive by blast

  have "inj f\<^sub>w'"
  proof (simp add: inj_def, rule allI, rule allI, rule impI)
    fix x y
    assume "f\<^sub>w' x = f\<^sub>w' y"
    then have "length (f\<^sub>w' x) = length (f\<^sub>w' y)"
      by simp
    then show "x = y"
      using f\<^sub>w'_order by (metis linorder_cases nless_le)
  qed

  have "infinite (Lang P S)"
    using \<open>range f\<^sub>w' \<subseteq> Lang P S\<close> \<open>inj f\<^sub>w'\<close> infinite_iff_countable_subset by blast
  then show "\<not> finite (Lang P S)"
    by simp
qed

end \<comment>\<open>end-theory Finiteness\<close>
 