section\<open>Definition\<close>

theory Definition
imports
  "Context_Free_Grammar.Context_Free_Grammar"
begin \<comment>\<open>begin-theory Definition\<close>

text\<open>
  The predecessors of a set of strings \<open>C\<close> is defined, with respect to a context-free grammar
  \<open>G = (V, \<Sigma>, P, S)\<close>, as the set of all strings \<open>c'\<close>, for which there exists at least one \<open>c \<in> C\<close>,
  such that \<open>c\<close> can be derived from \<open>c'\<close> using the productions of \<open>G\<close>:
\<close>

definition "pre_star P C \<equiv> {c'. \<exists>c \<in> C. P \<turnstile> c' \<Rightarrow>* c}"

text\<open>
  In general, the @{typ "('n, 't) syms"} datatype is used, which combines both non-terminals \<open>V\<close>
  and terminals \<open>\<Sigma>\<close>. This is because the productions \<open>P\<close> generally produce both during derivation.
\<close>

text\<open>
  However, sometimes a strict string containing only terminals is required.
  These strings specify the words within a context-free language \<open>L(G)\<close>.
  To convert these strings back into the dual-datatype,
  the following two abbreviations are introduced for convenience:
\<close>

abbreviation map_word :: "'t list \<Rightarrow> ('n, 't) syms" where
  "map_word w \<equiv> map Tm w"

abbreviation map_lang :: "'t list set \<Rightarrow> ('n, 't) syms set" where
  "map_lang L \<equiv> map_word ` L"

subsection\<open>General Properties\<close>

text\<open>
  A straight-forward property is monotonicity:
\<close>

lemma pre_star_subset: "L\<^sub>1 \<subseteq> L\<^sub>2 \<Longrightarrow> pre_star P L\<^sub>1 \<subseteq> pre_star P L\<^sub>2"
  unfolding pre_star_def by blast

lemma pre_star_mono[mono]: "mono (pre_star P)"
  unfolding mono_def using pre_star_subset by blast

text\<open>
  Furthermore, checking whether certain strings are contained within \<open>pre\<^sup>*(L)\<close> of a given \<open>L\<close>
  provides a criterion for different properties of the context-free grammar itself:
\<close>

lemma pre_star_term:
  "x \<in> pre_star P L \<longleftrightarrow> (\<exists>w. w \<in> L \<and> P \<turnstile> x \<Rightarrow>* w)"
  unfolding pre_star_def by blast

lemma pre_star_word:
  "[Nt S] \<in> pre_star P (map_lang L) \<longleftrightarrow> (\<exists>w. w \<in> L \<and> w \<in> Lang P S)"
  unfolding Lang_def pre_star_def by blast

lemma pre_star_lang:
  "Lang P S \<inter> L = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map_lang L)"
  using pre_star_word[where P=P] by blast

text\<open>
  We will later show in section \ref{sec:applications}, that these properties can be used
  to formulate different problems of context-free languages.
\<close>

subsection\<open>Properties of Non-Terminal Symbols\<close>

text\<open>
  Some properties of non-terminals are also of interest, particularly reachability,
  productiveness, usefulness and nullability.
\<close>

definition is_reachable_from :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool"
    ("(2_ \<turnstile>/ (_/ \<Rightarrow>\<^sup>? / _))" [50, 0, 50] 50) where
  "(P \<turnstile> X \<Rightarrow>\<^sup>? Y) \<equiv> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt X] \<Rightarrow>* (\<alpha>@[Nt Y]@\<beta>))"

\<comment>\<open>\<open>X \<in> V\<close> is productive, iff a string of terminals \<open>w \<in> \<Sigma>\<^sup>*\<close> can be derived:\<close>
definition is_productive :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> bool" where
  "is_productive P X \<equiv> (\<exists>w. P \<turnstile> [Nt X] \<Rightarrow>* map_word w)"

\<comment>\<open>\<open>X \<in> V\<close> is useful, iff \<open>V\<close> can be reached from \<open>S\<close> and it is productive:\<close>
definition is_useful :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> bool" where
  "is_useful P S X \<equiv> (P \<turnstile> S \<Rightarrow>\<^sup>? X) \<and> is_productive P X"

\<comment>\<open>\<open>X \<in> V\<close> is nullable, iff \<open>\<epsilon>\<close> can be derived:\<close>
definition is_nullable :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> bool" where
  "is_nullable P X \<equiv> (P \<turnstile> [Nt X] \<Rightarrow>* [])"

end \<comment>\<open>end-theory Definition\<close>
