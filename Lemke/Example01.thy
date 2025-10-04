theory Example01
  imports Algorithm
begin \<comment>\<open>begin-theory Example01\<close>

datatype n = A | B
datatype t = a | b

definition M :: "(nat, (n, t) sym) nfa" where "M \<equiv> \<lparr>
  transitions = {
    (0, Tm a, 1),
    (1, Tm b, 2),
    (2, Tm a, 1)
  },
  start = 0 :: nat,
  finals = {0, 1, 2}
\<rparr>"

definition P :: "(n, t) Prods" where "P \<equiv> {
  \<comment>\<open>\<open>A \<rightarrow> a | BB\<close>\<close>
  (A, [Tm a]),
  (A, [Nt B, Nt B]),

  \<comment>\<open>\<open>B \<rightarrow> AB | b\<close>\<close>
  (B, [Nt A, Nt B]),
  (B, [Tm b])
}"

value "compute_prestar P M"

text\<open>@{value "compute_prestar P M"}\<close>

end \<comment>\<open>end-theory Example01\<close>
