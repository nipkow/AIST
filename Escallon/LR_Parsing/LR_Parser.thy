theory LR_Parser 
  imports 
    Context_Free_Grammar.Context_Free_Grammar 
    Finite_Automata_HF 
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

(* Defining edge cases of \<Delta>: reject state? *)
definition char_fa :: "('n::fresh0, 't) Cfg \<Rightarrow> (('n, 't) sym, ('n, 't) item) nfa" where
  "char_fa G \<equiv> let 
      S = Start G; 
      P = Prods G;
      Q = It G;
      S' = [fresh0 (Nts P) \<rightarrow> [] . [Nt S]]; 
      F = {[X \<rightarrow> \<alpha> . []] |X \<alpha>. [X \<rightarrow> \<alpha> . []] \<in> It G};
      \<Delta> = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> {if a = Y \<and> ((X, \<alpha> @ (Y#\<beta>)) \<in> P) then [X \<rightarrow> \<alpha> @ [Y] . \<beta>] else s}| 
         _ \<Rightarrow> {s}); 
      \<E> = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> P \<and> (Y, \<gamma>) \<in> P} in
    \<lparr>nfa.states = Q \<union> {S'}, nfa.init = {S'}, nfa.final = F, nfa.nxt = \<Delta>, nfa.eps = \<E>\<rparr>"

lemma states_char_fa [simp]: 
  "nfa.states (char_fa G) = It G \<union> {[fresh0 (Nts (Prods G)) \<rightarrow> [] . [Nt (Start G)]]}"
  unfolding char_fa_def by (meson nfa.select_convs(1))

lemma init_char_fa [simp]:
  "nfa.init (char_fa G) = {[fresh0 (Nts (Prods G)) \<rightarrow> [] . [Nt (Start G)]]}"
  unfolding char_fa_def by (meson nfa.select_convs(2))

lemma final_char_fa [simp]:
  "nfa.final (char_fa G) = {[X \<rightarrow> \<alpha> . []] |X \<alpha>. [X \<rightarrow> \<alpha> . []] \<in> It G}"
  unfolding char_fa_def by (meson nfa.select_convs(3))

lemma nxt_char_fa [simp]:
  "nfa.nxt (char_fa G) = (\<lambda>s a. case s of 
        [X \<rightarrow> \<alpha> . Y # \<beta>]  \<Rightarrow> {if a = Y \<and> ((X, \<alpha> @ (Y#\<beta>)) \<in> Prods G) then [X \<rightarrow> \<alpha> @ [Y] . \<beta>] else s}| 
        _ \<Rightarrow> {s})"
  unfolding char_fa_def by (meson nfa.select_convs(4))

lemma eps_char_fa [simp]:
  "nfa.eps (char_fa G) 
    = {([X \<rightarrow> \<alpha> . Nt Y # \<beta>], [Y \<rightarrow> [] . \<gamma>]) | X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G \<and> (Y, \<gamma>) \<in> Prods G}"
  unfolding char_fa_def by (meson nfa.select_convs(5))

definition LR\<^sub>0 :: "('n::fresh0, 't) Cfg \<Rightarrow> (('n, 't) sym, ('n, 't) item set) dfa" where
  "LR\<^sub>0 G \<equiv> nfa.Power_dfa (char_fa G)"

locale finite_grammar =
  fixes G :: "('n::fresh0, 't) Cfg"
  assumes finite: "finite (Prods G)"
begin

sublocale char_fa: nfa "char_fa G"
proof (unfold_locales, goal_cases _ _ nxt_closed states_finite)
  case (nxt_closed q x)
  then obtain X \<alpha> \<beta> where q_def: "q = [X \<rightarrow> \<alpha> . \<beta>]" by (metis item.exhaust)
  consider (empty) "\<beta> = []" | (eq) xs where "\<beta> = x # xs" | (neq) y ys where "\<beta> = y # ys" "y \<noteq> x"
    by (metis list.exhaust)
  then show ?case 
  proof cases
    case eq
    consider (start) "q \<in> nfa.init (char_fa G)" | (It) "q \<in> It G"
      using nxt_closed by fastforce
    then show ?thesis 
      using eq nxt_closed q_def by cases (auto simp add: It_def)
  qed (use nxt_closed q_def in fastforce)+
qed (use It_finite[OF finite] in auto)


(* Using new lemma in Finite_Automata_HF (needed?) *)
sublocale canon_LR0: dfa "LR\<^sub>0 G" 
  unfolding LR\<^sub>0_def by (rule char_fa.Power_dfa_is_dfa)

end

end
