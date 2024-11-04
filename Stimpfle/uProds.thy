theory uProds
  imports "../CFG" eProds
begin

(* TODO: maybe add tm, tms and allSyms to CFG.thy ? *)
fun tm :: "('n,'t)syms \<Rightarrow> 't set" where
  "tm [] = {}" |
  "tm (Nt A # v) = tm v" |
  "tm (Tm a # v) = {a} \<union> tm v"

definition tms :: "('n,'t)prodS \<Rightarrow> 't set" where 
  "tms P = (\<Union>(A,w)\<in>P. tm w)"

definition allSyms :: "('n,'t)prodS \<Rightarrow> ('n,'t) sym set" where 
  "allSyms P = (Nt ` nts P) \<union> (Tm ` tms P)"

(* Rules of the form A\<rightarrow>B, where A and B are in nonterminals G *)
definition unitProds :: "('n,'t) prods \<Rightarrow> ('n,'t) prodS" where
  "unitProds P = {(l,r). \<exists>B. r = [Nt B] \<and> (l,r) \<in> set P}"

(* A\<rightarrow>*B where A and B are in nonTerminals g *)
definition "allDeps P = {(a,b). set P \<turnstile> [a] \<Rightarrow>* [b] \<and> a \<in> allSyms (set P) \<and> b \<in> allSyms (set P)}"

definition "nonUnitProds P = (set P - (unitProds P))"

definition newProds :: "('n, 't) prods \<Rightarrow> ('n, 't) prodS \<Rightarrow> ('n, 't) prodS" where 
"newProds P P' = 
  {(a,r). \<exists>b ru. (b,r) \<in> P' \<and> (Nt a, Nt b) \<in> allDeps (ru) \<and> (set ru = unitProds P)}"

definition "uppr_rules P = (nonUnitProds P \<union> newProds P (nonUnitProds P))"

definition "uppr P P' = (set P' = uppr_rules P)"

(*
theorem thm4_4: 
  assumes "[] \<notin> L G"
    and "negr G0 G"
    and "upgr G G'"
  shows "L G = L G'"
  using assms sorry
*)

end