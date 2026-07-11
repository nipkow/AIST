theory Non_Terms
imports Main
begin

datatype t = A | B | C | D

instantiation t :: linorder
begin

fun less_eq_t :: "t \<Rightarrow> t \<Rightarrow> bool" where
"(A \<le> x) = True" |
"(B \<le> x) = (x \<noteq> A)" |
"(C \<le> x) = (x = C \<or> x = D)" |
"(D \<le> x) = (x = D)"

definition less_t :: "t \<Rightarrow> t \<Rightarrow> bool" where
"less_t x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof (standard, goal_cases)
   case (1 x y)
   then show ?case by(simp add: less_t_def)
next
   case (2 x)
   then show ?case by(cases x; auto)
next
   case (3 x y z)
   then show ?case by(cases x; cases y; cases z; auto)
next
   case (4 x y)
   then show ?case by(cases x; cases y; auto)
next
   case (5 x y)
   then show ?case by(cases x; cases y; auto)
qed


end

end