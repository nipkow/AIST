theory LR_Parser 
  imports 
    Context_Free_Grammar.Context_Free_Grammar 
    Pushdown_Automata.Pushdown_Automata
    Finite_Automata_HF 
begin

datatype ('n, 't) item = Item 'n  "('n, 't) syms"  "('n, 't) syms"

notation Item  ("[_ \<rightarrow> _ . _]" 100) 



definition items_of_Prods :: "('n, 't) Prods \<Rightarrow> ('n, 't) item set" where
  "items_of_Prods P = {[A \<rightarrow> \<alpha> . \<beta>] | A \<alpha> \<beta>. (A, \<alpha>@\<beta>) \<in> P}"

definition It :: "('n, 't) Cfg \<Rightarrow> ('n, 't) item set" where
  "It G = items_of_Prods (Prods G)"

(* make intro? *)
declare It_def[simp]

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

lemma items_of_Prods_finite:
  assumes "finite P"
shows "finite (items_of_Prods P)"
proof -
  have "items_of_Prods P = (\<Union>(A,w)\<in>P. {[A \<rightarrow> \<alpha> . \<beta>] | \<alpha> \<beta>. (A, \<alpha>@\<beta>) = (A, w)})" 
    unfolding items_of_Prods_def by auto
  with prod_items_finite show ?thesis using assms by fastforce
qed


corollary It_finite:
  assumes "finite (Prods G)"
shows "finite (It G)"
  using assms items_of_Prods_finite by auto


(* Problem when defining \<Delta>: IPDA uses \<Delta> :: 'q list \<Rightarrow> 'a \<Rightarrow> 'q list
                              (defined as \<Delta>: Q\<^sup>+ \<times> V\<^sub>T \<Rightarrow> Q\<^sup>* in the book)
Possible solutions: 
  1. Make Q ('n, 't) item list
  2. Since state = top of stack: instead of state q and stack q#qs do state q and stack qs
      \<Longrightarrow> problems with empty stack? (IPDA accepts with final state)

A definition with variant 2, using [S' \<rightarrow> [] . []] as a dummy starting stack symbol:
*)
definition IPDA :: "('n::fresh0, 't) Cfg \<Rightarrow> (('n, 't) item, 't, ('n, 't) item) pda" where
  "IPDA G \<equiv> let
    S = Start G;
    S' = fresh0 (Nts (Prods G));
    P' = Prods G \<union> {(S', [Nt S])};
    Q = items_of_Prods P'; 
    \<Delta> = (\<lambda>q a s. case q of [X \<rightarrow> \<beta> . Tm a' # \<gamma>] \<Rightarrow> 
            if a' = a then let r = [X \<rightarrow> \<beta> @ [Tm a] . \<gamma>] in {(r, [r])} else undefined);
    \<E> = (\<lambda>q s. case (q,s) of 
      ([X \<rightarrow> \<beta> . Nt Y # \<gamma>], _) \<Rightarrow> {([Y \<rightarrow> [] . \<alpha>], [X \<rightarrow> \<beta>@[Nt Y] . \<gamma>]#[s]) |\<alpha>. (Y,\<alpha>) \<in> P'} |
      ([Y \<rightarrow> \<alpha> . []], [X \<rightarrow> \<beta> . Nt Y' # \<gamma>]) 
        \<Rightarrow> {if Y = Y' then ([X \<rightarrow> \<beta>@[Nt Y] . \<gamma>], []) else undefined})        
in
  \<lparr>pda.init_state = [S' \<rightarrow> [] . [Nt S]], pda.init_symbol = [S' \<rightarrow> [] . []], 
    pda.final_states = {[S' \<rightarrow> [Nt S] . []]}, pda.delta = \<Delta>, pda.delta_eps = \<E>\<rparr>"

(* interpretation pda "IPDA G" - doesn't work, types must be finite (why?) *)

(* Defining edge cases of \<Delta>: reject state? (also for IPDA) *)
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

(* Better alternative? *)
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
      using eq nxt_closed q_def by cases (auto simp: items_of_Prods_def)

  qed (use nxt_closed q_def in fastforce)+
qed (use It_finite[OF finite] in auto)


(* Using new lemma in Finite_Automata_HF (needed?) *)
sublocale canon_LR0: dfa "LR\<^sub>0 G" 
  unfolding LR\<^sub>0_def by (rule char_fa.Power_dfa_is_dfa)

end


(* Formalizing \<epsilon>-transition counting for induction; unable to use notation in locale finite_grammar *)
context nfa 
begin

type_synonym ('b,'c) config = "'b \<times> 'c list"

inductive step :: "('s,'a) config \<Rightarrow> ('s,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 70) where
nxt[intro]:  "q \<in> nxt M p a \<Longrightarrow> (p,a#u) \<turnstile> (q,u)" |
eps[intro]:  "(p,q) \<in> eps M \<Longrightarrow> (p,w) \<turnstile> (q,w)"

inductive_cases step_nxtE[elim]: "(q,a#u) \<turnstile> (r,u)"
inductive_cases step_epsE[elim]: "(q,w) \<turnstile> (r,w)"

lemma step_equal_or_cons:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_cons[OF assms] by fastforce
  

abbreviation stepn  (\<open>_ \<turnstile>'(_') _\<close> 70) where
  "c0 \<turnstile>(n) c1 \<equiv> (step ^^ n) c0 c1"

abbreviation steps (infix \<open>\<turnstile>*\<close> 70) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by ((induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct),
  (use step_len_dec surj_pair le_trans in fastforce)+)


inductive eps_stepn :: "('s,'a) config \<Rightarrow> nat \<Rightarrow> ('s,'a) config \<Rightarrow> bool" (\<open>_ \<turnstile>\<epsilon>'(_') _\<close> 70) where
refl[intro]:  "(q,w) \<turnstile>\<epsilon>(0) (q,w)" |
nxt[intro]:  "\<lbrakk>(p,u) \<turnstile>\<epsilon>(n) (q,a#v); (q,a#v) \<turnstile> (r,v)\<rbrakk> \<Longrightarrow> (p,u) \<turnstile>\<epsilon>(n) (r,v)" |
eps[intro]:  "\<lbrakk>(p,u) \<turnstile>\<epsilon>(n) (q,v); (q,v) \<turnstile> (r,v)\<rbrakk> \<Longrightarrow> (p,u) \<turnstile>\<epsilon>(Suc n) (r,v)"



inductive_cases eps_stepn_reflE[elim]: "c \<turnstile>\<epsilon>(0) c"
inductive_cases eps_stepn_nxtE[elim]: "(q,a#u) \<turnstile>\<epsilon>(0) (r,u)"
inductive_cases eps_stepn_epsE[elim]: "c0 \<turnstile>\<epsilon>(Suc n) c1"
inductive_cases eps_stepn_eps2E[elim]: "(p,u) \<turnstile>\<epsilon>(Suc n) (q,v)"


lemma step_is_eps_stepn:
  assumes "c0 \<turnstile> c1"
  shows "(c0 \<turnstile>\<epsilon>(0) c1) \<or> (c0 \<turnstile>\<epsilon>(Suc 0) c1)"
  using assms by cases auto


lemma steps_impl_eps_stepn[elim]:
  assumes "c0 \<turnstile>* c1"
  obtains n where "c0 \<turnstile>\<epsilon>(n) c1"
  using assms proof (induction arbitrary: thesis)
  case base
  then show ?case using eps_stepn.refl surj_pair by metis
next
  case (step c1 c2)
  then obtain n where "c0 \<turnstile>\<epsilon>(n) c1" by blast
  from step(2) show ?case 
    by cases
      ((smt (verit, best) eps_stepn.simps step_is_eps_stepn step),
     (metis step(2,3,4) nfa.eps_stepn.eps nfa_axioms old.prod.exhaust))
qed

lemma eps_stepn_impl_steps: "c0 \<turnstile>\<epsilon>(n) c1 \<Longrightarrow> c0 \<turnstile>* c1" 
  by (induction rule: eps_stepn.induct) auto

(* To be used in proof of Theorem 3.4.1 *)
lemma last_eps_step:
  assumes "(p,u) \<turnstile>\<epsilon>(Suc n) (s,w)"
  obtains q r v where "(p, u) \<turnstile>\<epsilon>(n) (q,v)" "(q,v) \<turnstile> (r,v)" "(r,v) \<turnstile>\<epsilon>(0) (s,w)"
  using assms proof (induction "length u - length w" arbitrary: s w rule: less_induct)
  case less 
  from less(3) show ?case 
  proof cases
    case (nxt q a)
    with steps_len_dec eps_stepn_impl_steps have  "length u \<ge> length (a#w)" by blast
    then have len_less: "length u - length (a#w) < length u - length w" by auto
    then show ?thesis using less nxt by blast
  qed (use less in blast)
qed
  


end
 

(*

theorem rtranclp_induct [consumes 1, case_names base step, induct set: rtranclp]:
  assumes a: "r\<^sup>*\<^sup>* a b"
    and cases: "P a" "\<And>y z. r\<^sup>*\<^sup>* a y \<Longrightarrow> r y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
  using a by (induct x\<equiv>a b) (rule cases)+
*)



end
