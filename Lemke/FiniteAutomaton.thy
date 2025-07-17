section\<open>Finite Automata\<close>

theory FiniteAutomaton
  imports "HOL-Data_Structures.Define_Time_Function"
begin \<comment>\<open>begin-theory FiniteAutomaton\<close>

record ('s, 't) nfa =
  transitions :: "('s \<times> 't \<times> 's) set"
  start :: 's
  finals :: "'s set"

fun step :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's \<Rightarrow> 's set" where
  "step T c s = { s' | s'. (s, c, s') \<in> T }"

fun step' :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't \<Rightarrow> 's set \<Rightarrow> 's set" where
  "step' T c s = { s' | s'. \<exists>s\<^sub>0 \<in> s. s' \<in> step T c s\<^sub>0 }"

fun steps :: "('s \<times> 't \<times> 's) set \<Rightarrow> 't list \<Rightarrow> 's \<Rightarrow> 's set" where
  "steps T w s = fold (step' T) w {s}"

fun accepts :: "('s, 't) nfa \<Rightarrow> 't list \<Rightarrow> bool" where
  "accepts M w = (steps (transitions M) w (start M) \<inter> finals M \<noteq> {})"

definition lang :: "('s, 't) nfa \<Rightarrow> ('t list) set" where
  "lang M \<equiv> { w | w. accepts M w }"

export_code accepts in Haskell

end \<comment>\<open>end-theory FiniteAutomaton\<close>
