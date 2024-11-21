theory Right_Linear
imports Binarize
begin

definition rlin :: "('n, 't) prods \<Rightarrow> bool" where
"rlin ps = (\<forall>(A,w) \<in> set ps. \<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [NT B]))"

definition rlin2 :: "('a, 't) prods \<Rightarrow> bool" where
"rlin2 ps = (\<forall>(A,w) \<in> set ps. w = [] \<or> (\<exists>a B. w = [Tm a, NT B]))"

lemma "rlin2 ps \<Longrightarrow> rlin ps"
unfolding rlin_def rlin2_def
apply(auto split: prod.splits)
by (metis (no_types, lifting) append_eq_Cons_conv map_eq_Cons_conv map_is_Nil_conv)

definition clean :: "('n,'t)prods \<Rightarrow> ('n,'t)prods" where "clean = undefined"

lemma lang_clean: "lang ps A  = lang (clean ps) A"
sorry
(*
lemma lengt_clean: "(A,w) \<in> set(binarize ps) \<Longrightarrow> length w \<le> 2"
by(induction ps rule: binarize.induct)(auto simp: Let_def)
*)

definition rlin2_of_rlin :: "('n,'t)prods \<Rightarrow> ('n,'t)prods" where
"rlin2_of_rlin ps = undefined"

lemma rlin2_rlin2_of_rlin: assumes "rlin ps" shows "rlin2 (rlin2_of_rlin ps)"
sorry

lemma lang_rlin2_of_rlin: assumes "rlin ps" "A \<in> nts (set ps)"
shows "lang ps A = lang (rlin2_of_rlin ps) A"
sorry

end