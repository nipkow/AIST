subsection\<open>Example\<close>

text\<open>The algorithm is executable. This theory file shows a quick example.\<close>

theory AlgorithmExample
  imports Algorithm
begin \<comment>\<open>begin-theory AlgorithmExample\<close>

text\<open>Consider the following grammar, with \<open>V = {A,B}\<close> and \<open>\<Sigma> = {a,b}\<close>:\<close>

datatype n = A | B
datatype t = a | b

definition "P \<equiv> {
  \<comment> \<open>\<open>A \<rightarrow> a | BB\<close>\<close>
  (A, [Tm a]),
  (A, [Nt B, Nt B]),

  \<comment> \<open>\<open>B \<rightarrow> AB | b\<close>\<close>
  (B, [Nt A, Nt B]),
  (B, [Tm b])
}"

text\<open>The following NFA accepts the regular language, whose predecessors we want to find:\<close>

definition M :: "(nat, (n, t) sym) nfa" where "M \<equiv> \<lparr>
  transitions = {
    (0, Tm a, 1),
    (1, Tm b, 2),
    (2, Tm a, 1)
  },
  start = 0 :: nat,
  finals = {0, 1, 2}
\<rparr>"

value "compute_prestar P M"
text\<open>@{value "compute_prestar P M"}\<close>

end \<comment>\<open>end-theory AlgorithmExample\<close>
