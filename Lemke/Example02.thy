theory Example02
  imports Algorithm
begin

datatype n = S | A
datatype t = a | b
datatype q = q0 | q1 | q2

value "c_prestar_while {q0, q1, q2} {
  \<comment>\<open>S \<rightarrow> AS | SA | a\<close>
  (S, [Nt A, Nt S]),
  (S, [Nt S, Nt A]),
  (S, [Tm a]),

  \<comment>\<open>A \<rightarrow> b\<close>
  (A, [Tm b])
} {
  (q0, Tm a, q0),
  (q0, Tm a, q1),
  (q1, Tm a, q2),
  (q2, Tm b, q1)
}"

end
