theory Binarize
imports "../CFG"
begin

fun binarize :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
"binarize ((A, s1 # s2 # s3 # w) # ps) =
 (let B = fresh ((A,s1 # s2 # s3 # w) # ps)
  in (A,[s1, NT B]) # binarize ((B, s2 # s3 # w) # ps))" |
"binarize (p # ps) = p # binarize ps" |
"binarize [] = []"

lemma length_binarize: "(A,w) \<in> set(binarize ps) \<Longrightarrow> length w \<le> 2"
by(induction ps rule: binarize.induct)(auto simp: Let_def)

lemma lang_binarize: assumes "A \<in> nts (set ps)"
shows "lang ps A = lang (binarize ps) A"
sorry

end