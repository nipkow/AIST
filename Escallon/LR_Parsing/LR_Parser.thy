theory LR_Parser 
  imports 
    Context_Free_Grammar.Context_Free_Grammar 
    Context_Free_Grammar.Chomsky_Normal_Form
    Finite_Automata_HF.Finite_Automata_HF 
    Fresh_Identifiers.Fresh
begin

datatype ('n, 't) item = Item 'n  "('n, 't) syms"  "('n, 't) syms"

notation Item  ("[_ \<rightarrow> _ . _]" 100)

definition It :: "('n, 't) Cfg \<Rightarrow> ('n, 't) item set" where
  "It G = {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> Prods G}"

lemma prod_items_finite:
  "finite {[A \<rightarrow> \<alpha> . \<beta>] | \<alpha> \<beta>. (A, \<alpha>@\<beta>) = (A, w)}"
proof (induction w)
  case (Cons a w)
  let ?it = "{[A \<rightarrow> \<alpha> . \<beta>] |\<alpha> \<beta>. (A, \<alpha> @ \<beta>) = (A, w)}"
  have "{[A \<rightarrow> \<alpha> . \<beta>] |\<alpha> \<beta>. (A, \<alpha> @ \<beta>) = (A, a # w)} 
        = {[A \<rightarrow> (a#\<alpha>) . \<beta>]|\<alpha> \<beta>. [A \<rightarrow> \<alpha> . \<beta>]\<in>?it} \<union> {[A \<rightarrow> [] . (a#\<beta>)]|\<beta>. [A \<rightarrow> [] . \<beta>]\<in>?it}" 
    (is "?cons = ?app_\<alpha> \<union> ?app_\<beta>")
  proof
    show "?cons \<subseteq> ?app_\<alpha> \<union> ?app_\<beta>"
    proof
      fix i
      assume in_cons: "i \<in> ?cons"
      then obtain \<alpha> \<beta> where \<alpha>\<beta>: "i = [A \<rightarrow> \<alpha> . \<beta>]" "\<alpha> @ \<beta> = a # w"
        by blast
      show "i \<in> ?app_\<alpha> \<union> ?app_\<beta>" using \<alpha>\<beta> by (cases \<alpha>) auto
    qed
  next
    show "?app_\<alpha> \<union> ?app_\<beta> \<subseteq> ?cons" 
    proof
      fix i 
      assume in_apps: "i \<in> ?app_\<alpha> \<union> ?app_\<beta>"
      then consider (in_app_\<alpha>) "i \<in> ?app_\<alpha>" | (in_app_\<beta>) "i \<in> ?app_\<beta>" by blast
      then show "i \<in> ?cons" by cases fastforce+
    qed
  qed
  moreover have "bij_betw (\<lambda>i. case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> [A \<rightarrow> (a#\<alpha>) . \<beta>]) ?it ?app_\<alpha>" 
    (is "bij_betw ?f _ _")
  proof -
    have "inj_on ?f ?it" 
      by (smt (verit, del_insts) inj_onCI item.case item.exhaust item.inject list.inject)
    moreover have "?f ` ?it = ?app_\<alpha>" by force
    ultimately show ?thesis unfolding bij_betw_def by simp
  qed
  moreover have "finite ?app_\<beta>" 
  proof -
    have "{[A \<rightarrow> [] . \<beta>]|\<beta>. [A \<rightarrow> [] . \<beta>]\<in>?it} \<subseteq> ?it" by blast
    moreover have 
      "bij_betw (\<lambda>i. case i of [A \<rightarrow> \<alpha> . \<beta>] \<Rightarrow> [A \<rightarrow> \<alpha> . a#\<beta>]) {[A \<rightarrow> [] . \<beta>]|\<beta>. [A \<rightarrow> [] . \<beta>]\<in>?it} ?app_\<beta>"
      by simp
    ultimately show ?thesis using Cons by simp
  qed
  ultimately show ?case using local.Cons bij_betw_finite by fastforce
qed simp


lemma It_finite:
  assumes "finite (Prods G)"
shows "finite (It G)"
proof -
  have "\<forall>P. finite P \<longrightarrow> finite {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> P}" 
  proof (rule allI, rule impI)
    fix P :: "('n, 't) Prods"
    assume fin: "finite P"
    show "finite {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> P}" (is "finite ?It")
    proof -
      have "?It = (\<Union>(A,w)\<in>P. {[A \<rightarrow> \<alpha> . \<beta>] | \<alpha> \<beta>. (A, \<alpha>@\<beta>) = (A, w)})" by auto
      with prod_items_finite show ?thesis using fin by fastforce
    qed
  qed
  with assms show ?thesis unfolding It_def by blast
qed


(* TODO: define \<Delta> and \<E> *)
definition char_fa :: "('n::fresh0, 't) Cfg \<Rightarrow> (('n, 't) syms, ('n, 't) item) nfa" where
  "char_fa G \<equiv> let 
      S = Start G; 
      P = Prods G;
      Q = {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> P};
      S' = [fresh0 (Nts P) \<rightarrow> [] . [Nt S]]; 
      F = {[S \<rightarrow> \<alpha> . []] | \<alpha>. (S, \<alpha>) \<in> P};
      \<Delta> = (\<lambda>s a. {s}); 
      \<E> = {} in
    \<lparr>nfa.states = Q \<union> {S'}, nfa.init = {S'}, nfa.final = F, nfa.nxt = \<Delta>, nfa.eps = \<E>\<rparr>"

lemma "nfa (char_fa G)"
proof (standard, goal_cases)
  case 1
  then show ?case sorry
next
  case 2
  then show ?case sorry
next
  case (3 q x)
  then show ?case sorry
next
  case 4
  then show ?case sorry
qed
