theory Greibach_Code
imports
  Greibach
  Fresh_Identifiers.Fresh_Nat
begin

subsection \<open>Fresh Nonterminals\<close>

(* TODO rm after next release (is in AFP/devel/CFG) *)
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

(* TODO: unify fresh and fresh0 *)
class fresh0 = fresh +
  fixes fresh0 :: "'a set \<Rightarrow> 'a"
  assumes fresh0: "finite X \<Longrightarrow> fresh0 X \<notin> X"

instantiation nat :: fresh0
begin

definition fresh0_nat :: "nat set \<Rightarrow> nat" where
"fresh0_nat X \<equiv> fresh X 0"

instance by standard (simp add: fresh0_nat_def fresh_notIn)

end

(* TODO integrate into the Fresh theories in the AFP *)
fun freshs :: "('a::fresh0) set \<Rightarrow> nat \<Rightarrow> 'a list" where
"freshs X 0 = []" |
"freshs X (Suc n) = (let x = fresh0 X in x # freshs (insert x X) n)"

declare freshs.simps(1)[code]

lemma freshs_Suc_Code[code]:
  "freshs (set xs) (Suc n) = (let x = fresh0 (set xs) in x # freshs (set(x # xs)) n)"
by simp

value "freshs {0,1,3,5,7::nat} 4"

lemma length_freshs: "finite X \<Longrightarrow> length(freshs X n) = n"
by(induction n arbitrary: X a)(auto simp: fresh_notIn Let_def)

lemma freshs_disj: "finite X \<Longrightarrow> X \<inter> set(freshs X n) = {}"
proof(induction n arbitrary: X)
  case (Suc n)
  then show ?case by(simp add: fresh0 Let_def) blast
qed simp

lemma freshs_distinct: "finite X \<Longrightarrow> distinct (freshs X n)"
proof(induction n arbitrary: X)
  case (Suc n)
  then show ?case
    using freshs_disj[of "insert (fresh0 X) X" n]
    by(auto simp: fresh0 Let_def)
qed simp

lemma distinct_app_freshs: "\<lbrakk> As = nts_prods_list ps; As' = freshs (set As) (length As) \<rbrakk> \<Longrightarrow>
   distinct (As @ As')"
using freshs_disj[of "set As" "length As"]
by (auto simp: distinct_nts_prods_list freshs_distinct)

text \<open>Top level function:\<close>

definition gnf_hd :: "('n::fresh0,'t)prods \<Rightarrow> ('n,'t)Prods" where
"gnf_hd ps =
  (let As = nts_prods_list ps;
       As' = freshs (set As) (length As)
   in exp_triangular (As' @ rev As) (solve_tri As As' (set ps)))"

lemma GNF_hd_gnf_hd: "eps_free ps \<Longrightarrow> GNF_hd (gnf_hd ps)"
by(simp add: gnf_hd_def Let_def GNF_of_R[simplified]
  distinct_nts_prods_list freshs_distinct finite_nts freshs_disj set_nts_prods_list length_freshs)

lemma Lang_gnf_hd: "\<lbrakk> eps_free ps; A \<in> nts ps \<rbrakk> \<Longrightarrow> Lang (gnf_hd ps) A = lang ps A"
unfolding gnf_hd_def Let_def
by (metis GNF_of_R_Lang IntI distinct_app_freshs empty_iff finite_nts freshs_disj length_freshs order_refl
      set_nts_prods_list)


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
