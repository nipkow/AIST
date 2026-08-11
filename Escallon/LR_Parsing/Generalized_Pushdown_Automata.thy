theory Generalized_Pushdown_Automata
  imports
    Auxiliary
    Pushdown_Automata.Pushdown_Automata 
begin

record ('q, 'a) gpda = states :: "'q set"
                       init   :: 'q
                       final  :: "'q set"
                       nxt    :: "('q list \<times> 'a \<times> 'q list) set"
                       eps    :: "('q list \<times> 'q list) set"

locale gpda =
  fixes M :: "('q, 'a) gpda"
  assumes init:       "init M \<in> states M"
      and final:      "final M \<subseteq> states M"
      and nxt:        "(ps, a, qs) \<in> nxt M \<Longrightarrow> ps \<noteq> [] \<and> qs \<noteq> [] 
        \<and> set ps \<subseteq> states M \<and> set qs \<subseteq> states M"
      and eps:        "(ps, qs) \<in> eps M \<Longrightarrow> ps \<noteq> [] \<and> qs \<noteq> [] 
        \<and> set ps \<subseteq> states M \<and> set qs \<subseteq> states M"
      and finite:     "finite (states M)"
(* 
  Necessary only for L(GPDA) \<subseteq> L(PDA) to hold. 
      and finite_nxt: "finite (nxt M)"
      and finite_eps: "finite (eps M)"
*)
begin

type_synonym ('s, 'b) config = "'s list \<times> 'b list"

inductive step :: "('q,'a) config \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
step_nxt: "(ps, a, qs) \<in> nxt M \<Longrightarrow> (ps@rs, a#w) \<turnstile> (qs@rs, w)" |
step_eps: "(ps, qs) \<in> eps M \<Longrightarrow> (ps@rs, w) \<turnstile> (qs@rs, w)"

inductive_cases step_nxtE[elim]: "(ps, a#w) \<turnstile> (qs, w)"
inductive_cases step_epsE[elim]: "(ps, w) \<turnstile> (qs, w)"

lemma nxtI [intro]:
  "\<lbrakk>ps = ps' @ rs; qs = qs' @ rs; (ps', a, qs') \<in> nxt M\<rbrakk> \<Longrightarrow> (ps, a # w) \<turnstile> (qs, w)"
  using step_nxt by presburger

lemma epsI [intro]:
  "\<lbrakk>ps = ps' @ rs; qs = qs' @ rs; (ps', qs') \<in> eps M\<rbrakk> \<Longrightarrow> (ps, w) \<turnstile> (qs, w)"
  using step_eps by presburger

lemma step_states_imp_states:
  assumes "(ps, u) \<turnstile> (qs, v)"
    "set ps \<subseteq> states M"
  shows "set qs \<subseteq> states M"
  using assms nxt eps by cases auto

abbreviation steps :: "('q,'a) config \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

abbreviation stepn :: "('q,'a) config \<Rightarrow> nat \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (\<open>_ \<turnstile>'(_') _\<close> 55) where
  "c\<^sub>0 \<turnstile>(n) c\<^sub>1 \<equiv> (step ^^ n) c\<^sub>0 c\<^sub>1"

lemma reachable_imp_substring:
  assumes "(ps, w) \<turnstile>* (qs, v)"
  obtains u where "w = u @ v"
  using assms proof (induction "(qs, v)" arbitrary: qs v thesis rule: rtranclp_induct)
  case (step y)
  from step(2) show ?case proof cases
    case (step_nxt rs a ss ts)
    with step(3)[of _ "a # v"] step(4)[of "_ @ [a]"] show ?thesis by auto
  qed (use step in auto)
qed simp

lemma steps_states_imp_states:
  assumes "(ps, u) \<turnstile>* (qs, v)"
    "set ps \<subseteq> states M"
  shows "set qs \<subseteq> states M"
  using assms by (induction rule: rtranclp_induct2)
    (use step_states_imp_states in blast)+

corollary steps_init_imp_states:
  assumes "([init M], u) \<turnstile>* (qs, v)"
  shows "set qs \<subseteq> states M"
  using steps_states_imp_states[OF assms] init by auto

definition Lang :: "'a list set" where
  "Lang \<equiv> {w. \<exists>f \<in> final M. ([init M], w) \<turnstile>* ([f], [])}"

end
end
