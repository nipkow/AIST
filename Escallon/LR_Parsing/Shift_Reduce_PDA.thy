theory Shift_Reduce_PDA
  imports 
    Extended_Cfg
    Generalized_Pushdown_Automata
begin

datatype ('n, 't) srpda_state = Sym "('n, 't) sym" | Init | Final

fun destSym :: "('n, 't) srpda_state  \<Rightarrow> ('n, 't) sym" where 
\<open>destSym (Sym X) = X\<close>

definition SRPDA :: "('n, 't) Cfg \<Rightarrow> (('n, 't) srpda_state, 't) gpda" where
  "SRPDA G \<equiv> \<lparr>gpda.states = UNIV, init = Init, final = {Final}, 
    nxt = {([q], x, [Sym (Tm x), q])|x q. q \<in> UNIV \<and> x \<in> UNIV}, 
    eps = {(\<alpha>, [Sym (Nt A)])|A \<alpha>. (A, map destSym \<alpha>) \<in> Prods G} 
        \<union> {([Sym (Nt (Start G)), Init], [Final])}\<rparr>"

locale srpda = Extended_Cfg G for G :: "('n::fresh0, 't) Cfg" +
  fixes M :: "(('n, 't) srpda_state, 't) gpda"
  assumes srpda: "M = SRPDA G"
begin

type_synonym ('nts, 'tms) config = "('nts, 'tms) srpda_state list \<times> 'tms list"

inductive step :: "('n, 't) config \<Rightarrow> ('n, 't) config \<Rightarrow> bool" 
  (infix \<open>\<turnstile>\<close> 55) where
step_nxt[intro]: "(ps, a, qs) \<in> nxt M \<Longrightarrow> (ps@rs, a#w) \<turnstile> (qs@rs, w)" |
step_eps[intro]: "(ps, qs) \<in> eps M \<Longrightarrow> (ps@rs, w) \<turnstile> (qs@rs, w)"

abbreviation steps :: "('n, 't) config \<Rightarrow> ('n, 't) config \<Rightarrow> bool" (infix \<open>\<turnstile>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

abbreviation stepn :: "('n, 't) config \<Rightarrow> nat \<Rightarrow> ('n, 't) config \<Rightarrow> bool" (\<open>_ \<turnstile>'(_') _\<close> 55) where
  "c\<^sub>0 \<turnstile>(n) c\<^sub>1 \<equiv> (step ^^ n) c\<^sub>0 c\<^sub>1"

definition Lang :: "'t list set" where
  "Lang \<equiv> {w. ([init M], w) \<turnstile>* ([Final], [])}"

lemma in_Lang_imp_reaches_S:
  "w \<in> Lang \<Longrightarrow> ([init M], w) \<turnstile>* ([Sym (Nt (Start G)), Init], [])"
  sorry

lemma srpda_complete:
  "LangS G \<subseteq> Lang"
  sorry

end
end
