theory Two_way_DFA_HF
  imports "HereditarilyFinite.Ordinal"
begin

datatype dir = Left | Right
notation Left (\<open>\<turnstile>\<close>)
notation Right (\<open>\<stileturn>\<close>)

datatype 'a alphabet = Letter 'a | End dir

record 'a dfa2 = states :: "hf set"
                 init   :: "hf"
                 accept :: "hf"
                 reject :: "hf"
                 nxt    :: "hf \<Rightarrow> 'a alphabet \<Rightarrow> hf \<times> dir"

locale dfa2 =
  fixes M :: "'a dfa2"
  assumes init:   "init M \<in> states M"
      and accept: "accept M \<in> states M"
      and reject: "reject M \<in> states M"
      and finite: "finite (states M)"
      and nxt:    "\<And>q x. q \<in> states M \<Longrightarrow> fst (nxt M q x) \<in> states M"
      (*TODO: Left/Right marker reads and final states*)


end