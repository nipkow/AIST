section "Context-Free Languages"

theory CFL
imports
  "$AFP/Regular-Sets/Regular_Set"
  CFG
begin

definition Rhss :: "('b \<times> 'a) set \<Rightarrow> 'b \<Rightarrow> 'a set" where
"Rhss P A = {w. (A,w) \<in> P}"

definition inst :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) sym \<Rightarrow> 't lang" where
"inst L s = (case s of Tm a \<Rightarrow> {[a]} | Nt A \<Rightarrow> L A)"

definition concats :: "'a lang list \<Rightarrow> 'a lang" where
"concats = foldl (@@) {[]}"

definition insts :: "('n \<Rightarrow> 't lang) \<Rightarrow> ('n, 't) syms \<Rightarrow> 't lang" where
"insts L w = concats (map (inst L) w)"

definition subst_lang :: "('n,'t)Prods \<Rightarrow> ('n \<Rightarrow> 't lang) \<Rightarrow> ('n \<Rightarrow> 't lang)" where
"subst_lang P L = (\<lambda>A. \<Union>w \<in> Rhss P A. insts L w)"

definition Langs :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't lang" where
"Langs P = lfp (subst_lang P)"


text \<open>This definition is tricky to use because one needs to supply a type of nonterminals.\<close>

definition cfl :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"cfl (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S)"

text \<open>Ideally one would existentially quantify over 'n on the right-hand side, but we cannot
quantify over types in HOL.\<close>

text \<open>This is a demo how to use the definition.\<close>

lemma "cfl TYPE('a) L1 \<and> cfl TYPE('b) L2 \<Longrightarrow> cfl TYPE(('a+'b)option) (L1 \<union> L2)"
oops

end