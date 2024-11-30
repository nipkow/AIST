theory Right_Linear
imports "../Stimpfle/uProds" Binarize
begin

definition rlin :: "('n, 't) prodS \<Rightarrow> bool" where
"rlin ps = (\<forall>(A,w) \<in> ps. \<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B]))"

definition rlin_nounit :: "('n, 't) prodS \<Rightarrow> bool" where
"rlin_nounit ps = (\<forall>(A,w) \<in> ps. \<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"

definition rlin_eps :: "('n, 't) prodS \<Rightarrow> bool" where
"rlin_eps ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>B u. w = map Tm u @ [Nt B] \<and> length u > 0))"

definition rlin2 :: "('a, 't) prodS \<Rightarrow> bool" where
"rlin2 ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>a B. w = [Tm a, Nt B]))"

lemma "rlin2 ps \<Longrightarrow> rlin ps"
  unfolding rlin_def rlin2_def
  by (auto split: prod.splits) (metis (no_types, lifting) append_eq_Cons_conv map_eq_Cons_conv map_is_Nil_conv)

(* Idea:
   1) Let ps in rlin.
   2) Eliminate unit productions, the new production set satisfies rlin_nounit (not executable, with definition of uppr)
   3) Add a non-terminal to the end for every production that contains only terminals, the only production
      this new non-terminal have is the empty word (write a executable function or definition?), the new production set
      satisfies rlin_eps
   4) Binarize, the new production set satisfies rlin2

   lang preservation:
   2) proved.
   3) not proved.
   4) proved.

   2-3) clean?
*)

lemma
  "rlin ps \<Longrightarrow> rlin_nounit ps \<or> (\<forall>(l,r) \<in> ps. \<exists>A. r = [Nt A])"
lemma 
  "rlin_nounit ps \<or> (\<forall>(l,r) \<in> ps. \<exists>A. r = [Nt A]) \<Longrightarrow> rlin ps"
  using rlin_def rlin_nounit_def by force

lemma rlin_eq:
  "rlin ps \<longleftrightarrow> rlin_nounit ps \<or> (\<forall>(l,r) \<in> ps. \<exists>A. r = [Nt A])"
  sorry


lemma 
  assumes rlin_ps: "rlin (set ps')"
    and uppr_ps': "uppr ps' ps"
  shows "rlin_nounit (set ps)"
proof -
  from uppr_ps' have "set ps = uppr_rules ps'"
    by (simp add: uppr_def)
  then have 3: "set ps = (nonUnitProds ps' \<union> newProds ps')"
    by (simp add: uppr_rules_def)
  have 1: "rlin_nounit (nonUnitProds ps')"
    by (smt (z3) inNonUnitProds list.simps(8) mem_Collect_eq not_Cons_self2 rlin_def rlin_eq rlin_nounit_def rlin_ps split_conv)
  then have 2: "rlin_nounit (newProds ps')"
    by (smt (verit, del_insts) mem_Collect_eq newProds_def rlin_nounit_def split_conv split_def)
  from 1 2 have "rlin_nounit (nonUnitProds ps' \<union> newProds ps')"
    by (meson UnE rlin_nounit_def)
  with 3 show ?thesis by simp
qed


lemma 
  assumes "rlin_eps ps"
  shows "rlin2 (binarize ps)"
  sorry

definition clean :: "('n,'t)prods \<Rightarrow> ('n,'t)prods" where "clean = undefined"

lemma lang_clean: "lang ps A  = lang (clean ps) A"
  sorry

definition rlin2_of_rlin :: "('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"rlin2_of_rlin ps = undefined"

lemma rlin2_rlin2_of_rlin: assumes "rlin ps" shows "rlin2 (rlin2_of_rlin ps)"
sorry

lemma lang_rlin2_of_rlin: assumes "rlin ps" "A \<in> nts (set ps)"
shows "lang ps A = lang (rlin2_of_rlin ps) A"
sorry

end