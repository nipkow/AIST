section\<open>Constructing $pre^*(L)$\<close>

theory Definition
imports
  "CFG.CFG"
  "Labeled_Transition_Systems.LTS"
begin \<comment>\<open>begin-theory Definition\<close>

text\<open>
  For the remainder of this work we will implicitely work with an arbitrary context-free grammar
  \<open>G = (V, T, P, S)\<close>, where \<open>V\<close> are the variables, \<open>T\<close> the terminal symbols, \<open>P\<close> is the set
  of productions and \<open>S \<in> V\<close> is the start symbol. We define \<open>\<Sigma> := V \<union> T\<close>.
\<close>

subsection\<open>Conversion to a Labeled Transition System\<close>

(*
  's is \<Sigma> = V \<union> T

  Assume \<alpha> and \<gamma> \<in> \<Sigma>\<^sup>*:
  If A \<rightarrow> \<beta> \<in> P, then \<alpha>A\<gamma> \<Rightarrow> \<alpha>\<beta>\<gamma> is a transition.
*)
inductive_set prods_to_lts :: "('n, 't) Prods \<Rightarrow> (('n,'t) syms, unit) transition set" for P where
  "(A, \<beta>) \<in> P \<Longrightarrow> (\<alpha>@[Nt A]@\<gamma>, (), \<alpha>@\<beta>@\<gamma>) \<in> prods_to_lts P"

locale CFG =
  fixes P :: "('n, 't) Prods"
    and S :: "'n"
  assumes "finite P" (* not sure if we need this, but have this for completeness *)
    and "finite (UNIV::'n set)"
    and "finite (UNIV::'t set)"
begin \<comment>\<open>begin-locale CFG\<close>

definition "transition_relation \<equiv> prods_to_lts P"

sublocale LTS transition_relation .

notation step_relp (infix \<open>\<Rightarrow>\<close> 80)
notation step_starp (infix \<open>\<Rightarrow>\<^sup>*\<close> 80)

lemma
  fixes \<alpha> :: "('n,'t) syms" and \<gamma> :: "('n,'t) syms"
  assumes "(A, \<beta>) \<in> P"
  shows "(\<alpha>@[Nt A]@\<gamma>) \<Rightarrow> (\<alpha>@\<beta>@\<gamma>)"
  unfolding transition_relation_def LTS.step_relp_def
  using assms prods_to_lts.simps by blast

abbreviation map_word :: "'t list \<Rightarrow> ('n, 't) syms" where
  "map_word w \<equiv> map Tm w"

abbreviation map_lang :: "'t list set \<Rightarrow> ('n, 't) syms set" where
  "map_lang L \<equiv> {map_word w | w. w \<in> L}"

subsection\<open>Simple Derivation Rules\<close>

lemma derive_eq: "(P \<turnstile> a \<Rightarrow> b) \<longleftrightarrow> a \<Rightarrow> b"
  (* by (simp add: derive.simps prods_to_lts.simps LTS.step_relp_def transition_relation_def) *)
proof (auto)
  assume assm: "P \<turnstile> a \<Rightarrow> b"
  then have "(a, (), b) \<in> prods_to_lts P"
    by (simp add: derive.simps prods_to_lts.simps)
  then show "a \<Rightarrow> b"
    by (simp add: LTS.step_relp_def transition_relation_def)
next
  assume "a \<Rightarrow> b"
  then have "(a, (), b) \<in> prods_to_lts P"
    by (simp add: LTS.step_relp_def transition_relation_def)
  then show "P \<turnstile> a \<Rightarrow> b"
    by (simp add: derive.simps prods_to_lts.simps)
qed

lemma derives_eq: "(P \<turnstile> \<alpha> \<Rightarrow>* \<gamma>) \<longleftrightarrow> \<alpha> \<Rightarrow>\<^sup>* \<gamma>"
  (* by (auto; induction set: rtranclp; simp add: derive_eq) *)
proof (auto)
  assume "P \<turnstile> \<alpha> \<Rightarrow>* \<gamma>" thus "\<alpha> \<Rightarrow>\<^sup>* \<gamma>"
  proof (induction set: rtranclp)
    case base thus ?case by simp
  next
    case (step y z)
    thus ?case by (simp add: derive_eq)
  qed
next
  assume "\<alpha> \<Rightarrow>\<^sup>* \<gamma>" thus "P \<turnstile> \<alpha> \<Rightarrow>* \<gamma>"
  proof (induction set: rtranclp)
    case base thus ?case by simp
  next
    case (step y z)
    thus ?case by (simp add: derive_eq)
  qed
qed

subsection\<open>General Properties\<close>

lemma pre_star_subset:
  assumes "L\<^sub>1 \<subseteq> L\<^sub>2"
  shows "pre_star L\<^sub>1 \<subseteq> pre_star L\<^sub>2"
  unfolding pre_star_def using assms by blast

lemma pre_star_word:
  "[Nt S] \<in> pre_star (map_lang L) \<longleftrightarrow> (\<exists>w. w \<in> L \<and> w \<in> Lang P S)"
  unfolding Lang_def pre_star_def derives_eq by blast

lemma pre_star_term:
  "x \<in> pre_star L \<longleftrightarrow> (\<exists>w. w \<in> L \<and> x \<Rightarrow>\<^sup>* w)"
  unfolding Lang_def pre_star_def derives_eq by blast

lemma pre_star_lang: "Lang P S \<inter> L = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star (map_lang L)"
  (* using pre_star_word by blast *)
proof (standard)
  assume "[Nt S] \<notin> pre_star (map_lang L)"
  then have "\<nexists>w. w \<in> L \<and> w \<in> Lang P S"
    using pre_star_word by simp
  then show "Lang P S \<inter> L = {}"
    by blast
next
  assume "Lang P S \<inter> L = {}"
  then have "\<nexists>w. w \<in> L \<and> w \<in> Lang P S"
    by blast
  then show "[Nt S] \<notin> pre_star (map_lang L)"
    using pre_star_word by simp
qed

subsection\<open>Properties of Non-Terminal Symbols\<close>

definition is_reachable_from :: "'n \<Rightarrow> 'n \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>?" 80) where
  "(X \<Rightarrow>\<^sup>? Y) \<equiv> (\<exists>\<alpha> \<beta>. [Nt X] \<Rightarrow>\<^sup>* (\<alpha>@[Nt Y]@\<beta>))"

definition is_reachable :: "'n \<Rightarrow> bool" where
  "is_reachable X \<equiv> (S \<Rightarrow>\<^sup>? X)"

definition is_productive :: "'n \<Rightarrow> bool" where
  "is_productive X \<equiv> (\<exists>w. [Nt X] \<Rightarrow>\<^sup>* map_word w)"

definition is_useful :: "'n \<Rightarrow> bool" where
  "is_useful X \<equiv> is_reachable X \<and> is_productive X"

definition (in CFG) is_nullable :: "'n \<Rightarrow> bool" where
  "is_nullable X \<equiv> ([Nt X] \<Rightarrow>\<^sup>* [])"

end \<comment>\<open>end-locale CFG\<close>

end \<comment>\<open>end-theory Definition\<close>
