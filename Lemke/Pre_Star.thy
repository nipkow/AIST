theory Pre_Star
imports
  CFG
begin

declare [[inductive_internals]]

inductive_set iter :: "('s * 'a * 's)set \<Rightarrow> ('s * 'a list * 's)set" for M where
"(s,[],s) \<in> iter M" |
"(s,a,t) \<in> M \<Longrightarrow> (t,xs,u) \<in> iter M \<Longrightarrow> (s,a#xs,u) \<in> iter M"
print_theorems

lemma iterp_mono: "M \<le> M' \<Longrightarrow> iterp M \<le> iterp M'"
unfolding iterp_def
by (rule lfp_mono)(smt (verit, best) le_funE le_funI predicate2D predicate2I)

inductive_set pre_star :: "('n,'a)Prods \<Rightarrow> ('s * 'a * 's)set \<Rightarrow> ('s * ('n,'a)sym * 's)set"
  for P T where
"(p,a,q) \<in> T \<Longrightarrow> (p, (Tm a), q) \<in> pre_star P T" |
"( p, w, q) \<in> iter(pre_star P T) \<Longrightarrow> (A,w) \<in> P \<Longrightarrow> (p, (Nt A), q) \<in> pre_star P T"
monos iterp_mono

end