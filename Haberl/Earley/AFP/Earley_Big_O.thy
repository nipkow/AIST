theory Earley_Big_O
imports Earley_Recognizer_Time Big_O
begin

text \<open>This theory abstracts some of the complexity results for Earley's recognizer
to Big O notation for the purpose of presenting it in a paper.
It does so under the additional assumption that \<open>nth\<close> takes constant time.\<close>

locale Earley_Gw_eps_T1 = Earley_Gw_eps_T where ps = ps for ps :: "('n,'t) prods" +
  assumes T_nth_IL: "T_nth_IL i = 1"
begin

lemma T_steps_le_O: "(\<lambda>(Bs,il1,il2). T_steps2_IL Bs (il1, il2)) \<le>O (\<lambda>(Bs,il1,il2). (length Bs)^2)
  IF (\<lambda>(Bs,il1,il2). wf_bins1 (map set Bs) \<and> wf1_IL' Bs il1 \<and> wf1_IL' Bs il2
     \<and> inv_IL il1 \<and> inv_IL il2 \<and> (\<forall>i < length Bs. distinct (Bs ! i))
     \<and> set_IL il1 \<inter> set_IL il2 = {}
     \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs))" (is "?f \<le>O ?g IF ?Q")
proof -
  have 1: "?f \<le>O (\<lambda>(Bs,il1,il2). (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * 1 + 3 * L * Suc K + 7 + 2 * (K + 2))
   + 7 * 1 + 3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K)) IF ?Q"
    by(rule le_O_if_le3, elim conjE, rule T_steps2_IL_bound[unfolded T_nth_IL])
  also have 2: "\<dots> \<le>O (\<lambda>(Bs,il1,il2).
 (L * Suc K) * (Suc (length Bs) *
 (L * Suc K * Suc (length Bs) * (14 + 3 * L * Suc K + 2 * (K + 2))
  + 3 * Suc (length Bs) + 2 * L * Suc K + 14 + Suc K)))"
    unfolding split_def
    apply(rule le_O_if_le)
    by(simp add: algebra_simps)
  also
  have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). Suc (length Bs) *
 (L * Suc K * Suc (length Bs) * (14 + 3 * L * Suc K + 2 * (K + 2))
  + 3 * Suc (length Bs) + 2 * L * Suc K + 14 + Suc K)) IF ?Q"
    unfolding split_def by (rule le_O_mult_k[OF le_O_id])
  also have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). Suc (length Bs) *
 (L * Suc K * Suc (length Bs) * (14 + 3 * L * Suc K + 2 * (K + 2))
  + 3 * Suc (length Bs)))"
    unfolding split_def
    apply(rule le_O_multR)
     apply simp
    by(rule le_O_Is)+
  also have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). Suc (length Bs) * (L * Suc K * Suc (length Bs)
  + 3 * Suc (length Bs)))"
    unfolding split_def
    apply(rule le_O_multR)
     apply simp
    apply(rule le_O_add2L)
    apply (intro le_O_Is)
    done
  also have "\<dots> \<le>O (\<lambda>(Bs,il1,il2). (L * Suc K + 3) * (length Bs + 1)^2) IF ?Q"
    unfolding split_def
    apply(rule le_O_if_le)
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  also have 1: "\<dots> \<le>O (\<lambda>(Bs,il1,il2). (length Bs + 1)^2)"
    unfolding split_def
    by(rule le_O_Is)+
  also have 1: "\<dots> \<le>O ?g"
    unfolding split_def using le_O_trans2[OF le_O_id le_O_fstI[OF le_O_sq_plus1]] .
  finally show ?thesis .
qed

lemmas T_steps2_IL_O = BigO_if_le_O3[OF T_steps_le_O]


lemma T_bins_IL_le_O: "T_bins_IL \<le>O (\<lambda>k. k^3) IF (\<lambda>k. k \<le> length w)"
proof -
  note le_O_cube_SucSuc = le_O_trans[OF le_O_cube_Suc[of Suc] le_O_cube_Suc[of "\<lambda>x. x"]]
  have "T_bins_IL \<le>O (\<lambda>k. (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)))) IF (\<lambda>k. k \<le> length w)"
    by(rule le_O_if_le, rule T_bins_IL_bound)
  also have "\<dots> \<le>O (\<lambda>k. k^3)"
    apply (simp add: split_def T_nth_IL le_O_Is algebra_simps flip: power3_eq_cube)
    apply(rule le_O_Is le_O_cube_SucSuc)+
    done
  finally show ?thesis .
qed

lemmas T_bins_IL_O = BigO_if_le_O[OF T_bins_IL_le_O]


lemma T_isin_le_O: "(\<lambda>(il,x). T_isin_IL il x) \<le>O (\<lambda>(il,x). 1)
  IF \<lambda>(il,x). inv_IL il \<and> wf1_IL k il \<and> from x < length (froms il)" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(il,x). T_nth_IL (from x) + L * (Suc K) + 1) IF ?Q"
    by(rule le_O_if_le2, elim conjE, rule T_isin_IL_wf)
  also have "\<dots> \<le>O (\<lambda>(il,x). 1) IF ?Q"
    by(simp add: T_nth_IL split_def le_O_Is)
  finally show ?thesis .
qed

lemmas T_isin_O = BigO_if_le_O2[OF T_isin_le_O]


lemma T_insert_IL_le_O: "(\<lambda>(x,il). T_insert_IL x il) \<le>O (\<lambda>(x,il). 1)
  IF \<lambda>(x,il). inv_IL il \<and> wf1_IL k il \<and> from x < length (froms il)" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(x,il). 3 * T_nth_IL (from x) + L * (Suc K) + 1) IF ?Q"
    by(rule le_O_if_le2, elim conjE, rule T_insert_IL_less)
  also have "\<dots> \<le>O (\<lambda>(x,il). 1) IF ?Q"
    by(simp add: T_nth_IL split_def le_O_Is)
  finally show ?thesis .
qed

lemmas T_insert_IL_O = BigO_if_le_O2[OF T_insert_IL_le_O]


lemma T_step2_IL_bound: assumes "(list il1) \<noteq> []" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf1_IL' Bs il1" "inv_IL il1" "length (froms il1) = Suc (length Bs)"
  "wf1_IL' Bs il2" "inv_IL il2" "length (froms il2) = Suc (length Bs)"
shows "T_step2_IL Bs (il1, il2) 
    \<le> L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + id(7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
unfolding id_def using T_step2_IL_bound[OF assms] by linarith

lemma aux2: "(n::nat)*(n*m) = n^2 * m"
  by(simp add: power2_eq_square)

lemma T_step2_IL_bound_le_O: "(\<lambda>(Bs,il1,il2). T_step2_IL Bs (il1, il2)) \<le>O (\<lambda>(Bs,il1,il2). (length Bs))
  IF (\<lambda>(Bs,il1,il2). list il1 \<noteq> [] \<and> wf_bins1 (map set Bs) \<and>
  (\<forall>i < length Bs. distinct (Bs ! i)) \<and> wf1_IL' Bs il1 \<and> inv_IL il1 \<and>
  length (froms il1) = Suc (length Bs) \<and> wf1_IL' Bs il2 \<and> inv_IL il2 \<and>
  length (froms il2) = Suc (length Bs))" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(Bs,il1,il2).
    L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + (7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)) IF ?Q"
    by(rule le_O_if_le3, elim conjE, rule T_step2_IL_bound[unfolded id_def])
  also have "\<dots> \<le>O ?g"
    by (simp add: split_def T_nth_IL le_O_Is algebra_simps aux2 flip: power2_eq_square)
  finally show ?thesis .
qed

lemmas T_step2_IL_bound_O = BigO_if_le_O3[OF T_step2_IL_bound_le_O]

lemma T_union_LIL_wf_le_O:
  "(\<lambda>(as,il). T_union_LIL as il) \<le>O (\<lambda>(as,il). length as) IF
  (\<lambda>(as,il). inv_IL il \<and> wf1_IL (length (froms il) - 1) il \<and> wf_bin1 (length (froms il) - 1) (set as)
    \<and> (\<forall>a\<in>set as. from a < length (froms il)))" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(as,il). (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1)
    IF ?Q"
    apply(rule le_O_if_le2)
    apply(rule T_union_LIL_wf)
       apply blast+
    done
  also have "\<dots> \<le>O (\<lambda>(as,il). 3 * (length as * (1 + L * (Suc K) + 2)) + 1)"
    unfolding T_nth_IL split_def
    apply(rule le_O_if_le)
    by (simp add: algebra_simps)
  also have  "\<dots> \<le>O (\<lambda>(as,il). length as * (1 + L * (Suc K) + 2))"
    unfolding split_def
    by(rule le_O_Is)+
  also have  "\<dots> \<le>O ?g"
    unfolding split_def
    by(simp add: split_def le_O_Is)
  finally show ?thesis .
qed

lemmas T_union_LIL_wf_O =  BigO_if_le_O2[OF T_union_LIL_wf_le_O]


lemma T_minus_IL_wf_le_O:
  "(\<lambda>(il1,il2). T_minus_IL il1 il2) \<le>O (\<lambda>(il1,il2). length (list il1) + length (froms il1))
  IF (\<lambda>(il1,il2). length(froms il1) > 0 \<and>
  wf1_IL (length (froms il1) - 1) il1 \<and> inv_IL il1 \<and> inv_IL il2 \<and> wf1_IL (length (froms il1) - 1) il2
  \<and> length (froms il2) \<ge> length (froms il1))" (is "?f \<le>O ?g IF ?Q")
proof -
  have "?f \<le>O (\<lambda>(il1,il2). (length (list il1)) * (4 * T_nth_IL (length (froms il1) - 1) + 2*L * (Suc K) + 4) + (length (froms il1) - 1) + 3 + length (list il1) + length (froms il1))
    IF ?Q"
    apply(rule le_O_if_le2)
    apply(rule T_minus_IL_wf)
         apply blast+
    done
  also have "\<dots> \<le>O (\<lambda>(il1,il2). 4 * (length (list il1) * (2*L * (Suc K) + 4)) + 2*length (froms il1) + 3)"
  unfolding T_nth_IL split_def
  apply(rule le_O_if_le)
  by (simp add: algebra_simps)
  also have "\<dots> \<le>O (\<lambda>(il1,il2). length (list il1) + length (froms il1))"
  unfolding split_def
  apply(rule le_O_Is)
   apply(rule le_O_add1)
    apply(rule le_O_add_R1)
    apply(rule le_O_Is)
(*     apply(rule le_O_multR)
  apply(simp add: split_def T_minus_IL_wf_P_def)
  using EarleyWorklist.inv_IL.elims(2) apply fastforce*)
    apply(rule le_O_Is)
    apply(rule le_O_Is)
   apply(rule le_O_add_R2)
   apply(rule le_O_Is)+
  done
  finally show ?thesis .
qed

lemmas T_minus_IL_wf_O = BigO_if_le_O2[OF T_minus_IL_wf_le_O]

end

end