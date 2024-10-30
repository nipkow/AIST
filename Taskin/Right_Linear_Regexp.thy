theory Right_Linear_Regexp
imports "$AFP/Regular-Sets/Regular_Exp" Right_Linear
begin

definition rlin_of_rexp :: "'a rexp \<Rightarrow> (nat,'a)prods" where
"rlin_of_rexp r = undefined"

lemma rlin_rlin_of_rexp: 
shows "rlin (rlin_of_rexp r)"
sorry

lemma lang_rlin_of_rexp: 
shows "Regular_Exp.lang r = lang (rlin_of_rexp r) 0"
sorry

definition rexp_of_rlin2 :: "('n,'t)prods \<Rightarrow> 'a rexp" where
"rexp_of_rlin2 ps = undefined"

lemma lang_rlin2_of_rlin: assumes "rlin2 ps" "A \<in> nts (set ps)"
shows "lang ps A = lang (rlin2_of_rlin ps) A"
sorry

end