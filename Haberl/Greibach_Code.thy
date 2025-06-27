theory Greibach_Code
imports
  Greibach
  Fresh_Identifiers.Fresh_Nat
begin

subsection \<open>Fresh Nonterminals\<close>

(* TODO mv to CFG *)
definition nts_syms_list :: "('n,'t)syms \<Rightarrow> 'n list \<Rightarrow> 'n list" where
"nts_syms_list sys = foldr (\<lambda>sy ns. case sy of Nt A \<Rightarrow> List.insert A ns | Tm _ \<Rightarrow> ns) sys"

definition nts_prods_list :: "('n,'t)prods \<Rightarrow> 'n list" where
"nts_prods_list ps = foldr (\<lambda>(A,sys) ns. List.insert A (nts_syms_list sys ns)) ps []"

lemma set_nts_syms_list: "set(nts_syms_list sys ns) = nts_syms sys \<union> set ns"
unfolding nts_syms_list_def
by(induction sys arbitrary: ns) (auto split: sym.split)

lemma set_nts_prods_list: "set(nts_prods_list ps) = nts ps"
by(induction ps) (auto simp: nts_prods_list_def Nts_def set_nts_syms_list split: prod.splits)

lemma distinct_nts_syms_list: "distinct(nts_syms_list sys ns) = distinct ns"
unfolding nts_syms_list_def
by(induction sys arbitrary: ns) (auto split: sym.split)

lemma distinct_nts_prods_list: "distinct(nts_prods_list ps)"
by(induction ps) (auto simp: nts_prods_list_def distinct_nts_syms_list split: sym.split)
(* end *)

fun freshs :: "('a::fresh) set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" where
"freshs X a 0 = []" |
"freshs X a (Suc n) = (let x = Fresh.fresh X a in x # freshs (insert x X) x n)"

declare freshs.simps(1)[code]

lemma freshs_Suc_Code[code]:
  "freshs (set xs) a (Suc n) = (let x = Fresh.fresh (set xs) a in x # freshs (set(x # xs)) x n)"
by simp

value "freshs {1,3,5,7::nat} 3 4"

lemma length_freshs: "finite X \<Longrightarrow> length(freshs X a n) = n"
by(induction n arbitrary: X a)(auto simp: fresh_notIn Let_def)

lemma freshs_disj: "finite X \<Longrightarrow> X \<inter> set(freshs X a n) = {}"
proof(induction n arbitrary: X a)
  case (Suc n)
  then show ?case by(simp add: fresh_notIn Let_def) blast
qed simp

lemma freshs_distinct: "finite X \<Longrightarrow> distinct (freshs X a n)"
proof(induction n arbitrary: X a)
  case (Suc n)
  then show ?case
    using freshs_disj[of "insert (Fresh.fresh X a) X" "Fresh.fresh X a" n]
    by(auto simp: fresh_notIn Let_def)
qed simp

lemma distinct_lem: "\<lbrakk> As = nts_prods_list ps; As' = freshs (set (A#As)) A (length As) \<rbrakk> \<Longrightarrow>
   distinct (As @ As')"
using freshs_disj[of "insert A (set As)" A "length As"]
by (auto simp: distinct_nts_prods_list freshs_distinct)

lemma "\<lbrakk> As = nts_prods_list ps; As' = freshs (set (A#As)) A (length As) \<rbrakk> \<Longrightarrow>
   Nts (set ps) \<inter> set As' = {}"
  by (metis List.finite_set freshs_disj insert_disjoint(1) list.simps(15) set_nts_prods_list)

lemma "\<lbrakk> As = nts_prods_list ps; As' = freshs (set (A#As)) A (length As) \<rbrakk> \<Longrightarrow>
   A \<notin> set As'"
  by (metis freshs_disj finite_set list.simps(15) insert_disjoint(2))

text \<open>Top level function, not yet verified\<close>

definition gnf_hd :: "('n::fresh,'t)prods \<Rightarrow> ('n,'t)Prods" where
"gnf_hd ps =
  (let As = nts_prods_list ps;
       As' = freshs (set As) (hd As) (length As)
   in exp_triangular (As' @ rev As) (solve_tri As As' (set ps)))"

declare exp_triangular.simps(1)[code]
lemma exp_triangular_Cons_code[code]: "exp_triangular (S#Ss) R =
 (let R' = exp_triangular Ss R;
      X = {w \<in> Rhss R' S. w \<noteq> [] \<and> hd w \<in> Nt ` (set Ss)};
      Y = (\<Union>(B,v) \<in> R'. \<Union>w \<in> X. if hd w \<noteq> Nt B then {} else {(S,v @ tl w)})
  in R' - ({S} \<times> X) \<union> Y)"
by(simp add: Let_def Rhss_def neq_Nil_conv Ball_def, safe, force+)

text "Examples"

value "exp_hd 0 [1] {(0,[Nt 1,Tm 2]), (1,[Tm 3])} :: (nat,int)Prods"

definition P1 :: "(nat,int)Prods" where
"P1 = {(1, [Tm 2, Tm 1]), (1, [Nt 2, Nt 2]),
   (2, [Nt 1, Nt 2]), (2, [Tm 2])}"

value "solve_tri [1,2] [5,6] P1"
value "exp_triangular ([5,6] @ rev [1,2]) (solve_tri [1,2] [5,6] P1)"

definition P2 :: "(nat,int)Prods" where
"P2 = {(1, [Nt 2, Nt 3]),
   (2, [Nt 3, Nt 1]), (2, [Tm 2]),
   (3, [Nt 1, Nt 2]), (3, [Tm 1])}"

value "solve_tri [1,2,3] [5,6,7] P2"
value "exp_triangular ([5,6,7] @ rev [1,2,3]) (solve_tri [1,2,3] [5,6,7] P2)"

end
