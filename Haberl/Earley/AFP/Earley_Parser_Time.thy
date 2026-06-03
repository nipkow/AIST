section \<open>Earley's Parser: Time Complexity\<close>

theory Earley_Parser_Time
imports
  "Earley_Recognizer_Time"
  "Earley_Parser"
begin

context Earley_Gw
begin

lemma length_fst_PIL: assumes "inv_PIL pil" "wf_PIL k pil"
  shows "length (list (fst pil)) \<le> L * Suc K * Suc k"
proof-
  from assms have "wf_bin1 k (set_IL (fst pil))" using wf_PIL_impl_wf1_IL by auto
  moreover have "distinct (list (fst pil))" using assms by (cases pil, cases "fst pil") auto
  ultimately show ?thesis using card_wf_bin1 distinct_card
    by fastforce
qed

lemma length_snd_PIL: assumes "inv_PIL pil" "wf_PIL k pil"
  shows "length (snd pil) \<le> L * Suc K * Suc k"
proof-
  from assms have "length (list (fst pil)) \<le> L * Suc K * Suc k" using length_fst_PIL by simp
  then show ?thesis using assms by (cases pil) auto
qed

end


subsection \<open>Running time analysis of list based Earley parser\<close>


subsubsection \<open>Time functions and simple bounds\<close>

context Earley_Gw_eps_T
begin
time_fun empty_PIL
time_fun insert_PIL
time_fun union_LPIL
time_fun isin_PIL
time_fun minus_LPIL
time_fun list2_PIL
time_fun minus_PIL
time_fun PIL_list
time_fun hd_PIL
time_fun list_PIL

time_fun Complete_PL
time_fun Scan_PL
time_fun Predict_PL
time_fun test2_PIL
time_fun step2_PIL

lemma T_rev_tree: 
  assumes "wf_item_P k pi" shows "T_rev (trees pi) \<le> 2 * K * K + 1" 
proof-
  obtain lh rh d T_nth_IL t where P: "pi = (Item (lh, rh) d T_nth_IL, t)"
    by (metis item.exhaust surj_pair)
  have "map root (rev t) = take d rh" using assms P by (auto simp add: \<alpha>_def rhs_def)
  then have "length t = length (take d rh)"
    by (metis length_map length_rev)
  moreover have "length rh \<le> K" using assms P prod_length_bound by (auto simp add: wf_item_def rhs_def)

  ultimately have 1: "length t \<le> K" by auto
  have "T_rev t \<le> Suc (length t * (length t * 2))" using T_rev_bound[of t] by auto
  also have "... \<le> Suc (K * (K * 2))" using 1 by (simp add: mult_le_mono)
  finally show ?thesis using P by simp
qed

lemma [simp]: "inv_PIL pil \<Longrightarrow> T_list2_PIL pil = (length (snd pil)) + 1"
  using T_zip by (cases pil) auto

lemma [simp]: 
  assumes "snd pil \<noteq> []" "inv_PIL pil" shows "T_hd_PIL pil = 0"
proof-
  obtain as m b bs where P1: "pil = (IL as m, (b#bs))"
    using assms by (metis T_last.cases set_PIL.cases snd_conv il_decomp)
  then have "as \<noteq> []" using assms by auto
  then obtain a ass where "as = a#ass"
    by (meson recognized_L.cases)
  then show ?thesis using P1 by auto
qed

(* For convenience, because of the proof structure *)
abbreviation "T_steps2_PIL2 Bs il12 n
  \<equiv> T_while_option2 test2_PIL (step2_PIL Bs) T_test2_PIL (T_step2_PIL Bs) (il12,n)"

(*assumes that the stop condition check takes 0 time*)
fun T_steps_PIL :: "('n, 't) item_P list list \<Rightarrow> ('n, 't) parseIL2 \<Rightarrow> nat" where
"T_steps_PIL Bs il12 = T_while_option test2_PIL (step2_PIL Bs) T_test2_PIL (T_step2_PIL Bs) il12"


time_fun close2_PIL
time_fun bins_PIL

subsubsection \<open>ParseIL time bounds\<close>

lemma T_insert_PIL_simp: "T_insert_PIL x pil \<le> T_isin_IL (fst pil) (fst x) + T_insert_IL (fst x) (fst pil)"
  by (cases pil, cases x) simp

corollary T_insert_PIL_bound: "inv_IL (fst pil) \<Longrightarrow> wf1_IL k (fst pil) \<Longrightarrow> from (fst x) <  length (froms (fst pil)) 
  \<Longrightarrow> T_insert_PIL x pil \<le> 4 * T_nth_IL (from (fst x)) + 2* L * Suc K + 2"
  using T_isin_IL_wf[of "fst pil" k "fst x"] T_insert_IL_less[of "fst pil" k  "fst x"] T_insert_PIL_simp[of x pil]
  by auto

lemma T_union_LPIL_bound: "inv_PIL pil \<Longrightarrow> wf_parse_bin1 (length (froms (fst pil)) - 1) (set xs) \<Longrightarrow> wf_PIL (length (froms (fst pil)) - 1) pil
  \<Longrightarrow> length (froms (fst pil)) > 0
  \<Longrightarrow> T_union_LPIL xs pil \<le> length xs * (4 * T_nth_IL (length (froms (fst pil)) - 1) + 2* L * Suc K + 2) + length xs + 1"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have ih: "T_union_LPIL xs pil \<le> length xs * (4 * T_nth_IL (length (froms (fst pil)) - 1) + 2 * L * Suc K + 2) + length xs + 1"
    by simp

  from Cons have 1: "inv_IL (fst pil)" by (cases pil) auto
  then have from_xs: "\<forall>a\<in>set (map item xs). from a < length (froms (fst pil))" 
    using forall_from_Suc_parse[OF Cons(3)] Cons(5) by (cases "fst pil") (auto simp del: wf_parse_bin1.simps)
  then have 2: "inv_IL (union_LIL (map item xs) (fst pil))"
    using LIL_union_inv Cons(2) by (cases pil) auto

  have a_le_leng: "from (fst a) < length (froms (fst pil))" 
    using forall_from_Suc_parse[OF Cons(3)] 1 Cons(5) by (cases "fst pil") (auto simp del: wf_parse_bin1.simps)
  then have 4: "from (fst a) \<le> length (froms (fst pil)) - 1" by auto
  
  have "wf1_IL (length (froms (fst pil)) - 1) (fst pil)" using Cons wf_PIL_impl_wf1_IL[of pil "length (froms (fst pil)) - 1"] by auto
  then have 3: "wf_bin1 (length (froms (fst pil)) - 1) (set (list (union_LIL (map item xs) (fst pil))))" 
    using 1 Cons from_xs wf1_IL_union_LIL[of "fst pil" "length (froms (fst pil)) - 1" "map item xs"] 
    by (auto simp add: wf_bin1_def)
  from 2 3 have "T_insert_PIL a (union_LPIL xs pil) \<le> 4 * T_nth_IL (from (fst a)) + 2* L * Suc K + 2"
    using "Cons.prems"(1) T_insert_PIL_bound[of "(union_LPIL xs pil)" "length (froms (fst pil)) - 1" a]
    a_le_leng by (auto simp add: wf_item1_def wf_item_def)
  then have "T_insert_PIL a (union_LPIL xs pil) \<le> 4 * T_nth_IL (length (froms (fst pil)) - 1) + 2* L * Suc K + 2"
    using mono_nth 4 monoD[of T_nth_IL "from (fst a)" "length (froms (fst pil)) - 1"] by (auto simp add: algebra_simps)
  then show ?case using ih by (auto simp add: algebra_simps)
qed

lemma T_minus_LPIL_bound: "inv_PIL pil \<Longrightarrow> wf_parse_bin1 k (set xs) \<Longrightarrow> wf_PIL k pil
  \<Longrightarrow> length (froms (fst pil)) \<ge> Suc k
 \<Longrightarrow> T_minus_LPIL k xs pil \<le> length xs * (5 * T_nth_IL k + 3 * L * Suc K + 3) + length xs + k + 2"
proof(induction k xs pil rule: T_minus_LPIL.induct)
  case (1 k pil)
  then show ?case by (simp del: T_empty_IL.simps)
next
  case (2 k a as pil)
  then have ih: "T_minus_LPIL k as pil \<le> length as * (5 * T_nth_IL k + 3 * L * Suc K + 3) + length as + k + 2"
    by auto

  from 2 have 3: "inv_IL (fst pil)" by (cases pil) auto
  have 4: "inv_IL (minus_LIL k (map item as) (fst pil))"
    using LIL_minus_inv forall_from_Suc_parse "2"(4) by auto

  have a_le_k: "from (fst a) \<le> k" using 2 by (auto simp add: wf_item1_def wf_item_def)
  have from_l: "\<forall>a\<in>set (map item as). from a < Suc k" using forall_from_Suc_parse "2"(4) by auto
  
  have "wf1_IL k (fst pil)" using 2 wf_PIL_impl_wf1_IL[of pil k] by auto
  then have 5: "wf_bin1 k (set (list (minus_LIL k (map item as) (fst pil))))" 
    using 2 3 from_l LIL_minus by (auto simp add: wf_bin1_def)
  have 6: "from (item a) < (length (froms (minus_LIL k (map item as) (fst pil))))" 
    using 2 le_imp_less_Suc 
    by (auto simp add: wf_item1_def wf_item_def)

  from 4 5 6 have "T_insert_PIL a (minus_LPIL k as pil) \<le> 4 * T_nth_IL (from (fst a)) + 2* L * Suc K + 2"
    using "2.prems"(1) T_insert_PIL_bound[of "(minus_LPIL k as pil)" k a] 
    by (auto simp add: wf_item1_def wf_item_def)
  then have 7: "T_insert_PIL a (minus_LPIL k as pil) \<le> 4 * T_nth_IL k + 2* L * Suc K + 2"
    using mono_nth a_le_k monoD[of T_nth_IL "from (fst a)" k] by (auto simp add: algebra_simps)

  have "T_isin_IL (fst pil) (fst a) \<le> T_nth_IL (from (fst a)) + L * Suc K + 1"
    using T_isin_IL_wf "2.prems"(4) "3" \<open>wf1_IL k (fst pil)\<close> a_le_k by auto
  then have "T_isin_PIL pil a \<le> T_nth_IL (from (fst a)) + L * Suc K + 1" by (cases pil, cases a) auto
  then have "T_isin_PIL pil a \<le> T_nth_IL k + L * Suc K + 1" 
    using mono_nth a_le_k monoD[of T_nth_IL "from (fst a)" k] by (auto simp add: algebra_simps)

  then show ?case using ih 7 by (auto simp add: algebra_simps)
qed

lemma T_minus_PIL_bound: 
  assumes "inv_PIL pil1" "inv_PIL pil2" "wf_PIL (length (froms (fst pil1)) - 1) pil1" 
    "wf_PIL (length (froms (fst pil1)) - 1) pil2" "length (froms (fst pil1)) \<le> length (froms (fst pil2))" "length (froms (fst pil1)) > 0"
  shows "T_minus_PIL pil1 pil2 \<le> length (snd pil1) * (5 * T_nth_IL (length (froms (fst pil1)) - 1) + 3 * L * Suc K + 3) + 2 * length (snd pil1) + 2 * (length (froms (fst pil1))) + 3"
proof-
  have "T_list2_PIL pil1 = length (snd pil1) + 1" using assms by auto

  moreover have "T_minus_LPIL (length (froms (fst pil1)) - 1) (list2_PIL pil1) pil2 
    \<le> length (list2_PIL pil1) * (5 * T_nth_IL (length (froms (fst pil1)) - 1) + 3 * L * Suc K + 3) + length (list2_PIL pil1) + (length (froms (fst pil1)) - 1) + 2" 
    using assms T_minus_LPIL_bound[of pil2 "length (froms (fst pil1)) - 1" "list2_PIL pil1"] wf_PIL_impl_wf1_IL by auto
  moreover have "length (list2_PIL pil1) = length (snd pil1)" using assms by (cases pil1) auto
  ultimately show ?thesis using assms(6) by (auto simp add: algebra_simps T_length)
qed

lemma T_PIL_list_bound: 
  assumes "wf_parse_bin1 k (set xs)"
  shows "T_PIL_list k xs \<le> length xs * (4 * T_nth_IL k + 2* L * Suc K + 2) + length xs + k + 2"
proof-
  have "inv_PIL (empty_PIL k)" and "wf_PIL k (empty_PIL k)"
    using wf_empty_PIL by (auto simp add: PIL_inv_empty)
  then have "T_union_LPIL xs (empty_PIL k) \<le> length xs * (4 * T_nth_IL k + 2* L * Suc K + 2) + length xs + 1"
    using T_union_LPIL_bound[of "empty_PIL k"] assms by auto
  then show ?thesis by (auto simp del: T_empty_IL.simps)
qed

subsubsection \<open>Earley parser time bounds\<close>

lemma T_Complete_PL_bound: 
  assumes "wf_parse_bins1 (map set Bs)" "from (item pi) < length Bs" "wf_item_P (length Bs) pi" "length (Bs ! from (item pi)) \<le> C"
  shows "T_Complete_PL Bs pi \<le> length Bs +  (2 * K * K + 2 * K + 5) * C + 2"
proof-
  let ?from_list = "Bs ! from (item pi)"
  let ?T_filt = "\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> T_next_sym p (Nt(lhs (prod (item pi)))) + (T_fst pi + T_prod (item pi) + T_fst (prod (item pi)))"
  let ?filtered = "filter (\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> next_sym p (Nt(lhs(prod(item pi))))) (Bs ! from (item pi))"
  let ?T_Pred = "\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> T_mv_dot p + (T_fst pi + T_prod (item pi) + T_fst (item.prod (item pi)) + (T_snd pi + T_rev (trees pi)))"
  have "\<forall>x \<in> set (Bs ! from (item pi)). ?T_filt x \<le> 2 * Suc K" 
    using assms T_next_symbol_bound by (fastforce simp add: wf_parse_bins1_def wf_item1_def wf_item_def)
  then have "T_filter ?T_filt ?from_list \<le> 2 * Suc K * (length ?from_list) + length ?from_list + 1"
    using T_filter_bound[of ?from_list ?T_filt "2 * Suc K"] by simp
  also have "... \<le> 2 * Suc K *  C + C + 1"
    using assms(4) length_filter_le mult_le_mono
    by (smt (verit, best) add_le_mono eq_imp_le le_trans)
  finally have 1: "T_filter ?T_filt ?from_list \<le> 2 * Suc K *  C + C + 1".

  have "\<forall>x \<in> set ?filtered. ?T_Pred x \<le> 2 * K * K + 1"
    using T_rev_tree assms by (auto simp add: wf_parse_bins1_def)
  then have "T_map ?T_Pred ?filtered \<le> (2 * K * K + 1) * length ?filtered + length ?filtered + 1"
    using T_map_bound[of ?filtered ?T_Pred "2 * K * K + 1"] by auto
  also have "... \<le> (2 * K * K + 1) * C + C + 1"
    using assms(4) length_filter_le mult_le_mono
    by (smt (verit, best) add_le_mono eq_imp_le le_trans)
  finally have 2: "T_map ?T_Pred ?filtered \<le> (2 * K * K + 1) * C + C + 1".

  have "T_nth Bs (from (item pi)) \<le> length Bs" 
    using assms T_nth[of "from (item pi)" Bs] by auto

  then show ?thesis using 1 2 by (auto simp add: algebra_simps)
qed

lemma T_Scan_PL_bound: 
  assumes "k < length w" "wf_parse_bin k (set Bs)" 
  shows "T_Scan_PL k Bs \<le> k + (2*K + 4) * (length Bs) + 3"
proof-
  have 1: "T_nth w k = k + 1" using assms by (auto simp add: T_nth)

  let ?T_filt = "\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_next_sym p (w!k)"
  have "\<forall>x \<in> set Bs. ?T_filt x \<le> 2 * Suc K" 
    using assms T_next_symbol_bound by (fastforce simp add: wf_item_def)
  then have 2: "T_filter ?T_filt Bs \<le> 2 * Suc K * (length Bs) + length Bs + 1"
    using T_filter_bound[of Bs ?T_filt "2 * Suc K"] by simp

  let ?filtered = "filter (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> next_sym p (w ! k)) Bs"
  let ?T_map = "\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p + T_the (Some (w ! k))"
  have "T_map (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p) ?filtered
  = T_map (\<lambda>y. 0) ?filtered" by auto
  also have "... \<le> length ?filtered + 1" using T_map_bound by fastforce
  also have "... \<le> length Bs + 1" by auto
  finally have "T_map (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p) ?filtered \<le> length Bs + 1".

  then show ?thesis using 1 2 by (auto simp add: algebra_simps)
qed

lemma T_Predict_PL_bound: 
  assumes "prod x \<in> P" shows "T_Predict_PL k x \<le> 2 * Suc K * L + 2*L + 2"
proof-
  have "T_filter (\<lambda>p. T_next_sym x (w!k) + T_fst p) ps \<le> 2 * Suc K * L + L + 1"
    using assms T_next_symbol_bound T_filter_bound[of ps "\<lambda>p. T_next_sym x (w!k) + T_fst p" "2 * Suc K"] 
    by (auto simp add: L_def)
  moreover have "T_map (\<lambda>p. 0) (filter (\<lambda>p. next_sym x (Nt(lhs p))) ps) \<le> L + 1"
    using T_map_bound[of "filter (\<lambda>p. next_sym x (Nt(lhs p))) ps" "\<lambda>p. 0" 0]
    by (metis (no_types, lifting) L_def add_le_mono dual_order.trans lambda_zero le_refl length_filter_le plus_nat.add_0)
  ultimately show ?thesis by (auto simp add: algebra_simps)
qed


lemma [simp]: 
  assumes "inv_PIL (il, t#ts)" shows "T_hd_PIL (il, t#ts) = 0"
proof-
  from assms have "list il \<noteq> []" by auto
  then obtain x xs m where "il = IL (x#xs) m"
    by (metis item_list.sel(1) il_decomp recognized_L.cases)    
  then show ?thesis by auto
qed

lemma parse_complete_length: "length (Complete_PL Bs pi) \<le> length (Bs ! from (item pi))"
  by (auto simp add: Complete_PL_def)

lemma parse_predict_length: "length (Predict_PL s n) \<le> L"
  by (auto simp add: Predict_PL_def L_def)

lemma T_parse_step2_IL_bound: 
  assumes cons: "list_PIL pil1 \<noteq> []"
  and invs: "inv_PIL pil1" "inv_PIL pil2"
  and lengs: "length (froms (fst pil1)) =  Suc (length Bs)" "length (froms (fst pil2)) =  Suc (length Bs)"
  and wf1: "wf_parse_bin1 (length Bs) (set_PIL pil1)" "wf_parse_bin1 (length Bs) (set_PIL pil2)" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
shows "T_step2_PIL Bs (pil1,pil2) 
    \<le> (2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7"
proof-
  from cons invs obtain x xs m t ts where P_pil1: "pil1 = (IL (x#xs) m, (t#ts))"
    by (metis list_PIL_Cons1 list_PIL_Cons2 prod.collapse recognized_L.cases)
  obtain il2 ts2 where P_pil2: "pil2 = (il2, ts2)"
    using set_PIL.cases by blast
  let ?b = "hd_PIL (IL (x#xs) m, (t#ts))"
  have b_simp: "?b = (x,t)" by simp

  have wf1_b: "wf_item_P1 (length Bs) ?b" using wf1 hd_PIL_in_set_PIL P_pil1 by auto
  then have 1: "T_is_complete (item ?b) \<le> K + 1" using T_is_complete_bound prod_length_bound P_pil1 
    by (auto simp add: wf_item1_def wf_item_def)

  have 2: "is_complete (item ?b) \<longrightarrow> T_Complete_PL Bs ?b \<le> length Bs +  (2 * K * K + 2 * K + 5) * C + 2"
    using wf1 wf1_b max_bin_size T_Complete_PL_bound[of Bs ?b C] by (auto simp add: wf_item1_def)

  moreover have "T_Predict_PL (length Bs) (item ?b) \<le> 2 * Suc K * L + 2 * L + 2" 
    using wf1_b T_Predict_PL_bound by (simp add: wf_item1_def wf_item_def)
  ultimately have 3: "(if is_complete (item ?b) then T_Complete_PL Bs ?b 
    else T_fst ?b + (T_length Bs + T_Predict_PL (length Bs) (item ?b)))
    \<le> length Bs + (2 * K * K + 2 * K + 5) * C + 2 * Suc K * L + 2 * L + 3"  
    by (auto simp add: T_length algebra_simps)

  let ?step = "PreCo_PL Bs ?b"
  have length_step: "length ?step \<le> max C L" 
    using parse_complete_length[of Bs "(x,t)"] parse_predict_length[of "length Bs" x] max_bin_size wf1_b 
    by (auto simp add: wf_item1_def)
  have wf_step: "wf_parse_bin1 (length Bs) (set ?step)"
    using wf1(3) wf1_Complete_PL wf1_Predict_PL wf1_b by presburger  
  then have "T_union_LPIL ?step pil1 \<le> length ?step * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + length ?step + 1"
    using T_union_LPIL_bound[of pil1 ?step] invs wf1 by (auto simp add: lengs simp del: wf_parse_bin1.simps)
  also have "... \<le> (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1"
    using length_step using mult_le_mono1[of "length ?step" "max C L"]
    by (meson add_le_mono le_numeral_extra(4))
  finally have 4: "T_union_LPIL ?step pil1 \<le> (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1".

  have from_b: "from (item ?b) < (length (froms il2))" using lengs wf1_b P_pil2 by (auto simp add: wf_item1_def wf_item_def)
  then have "T_insert_PIL ?b pil2 \<le> 4 * T_nth_IL (from (item ?b)) + 2 * L * Suc K + 2"
    using T_insert_PIL_bound[of pil2 "length Bs" ?b] invs wf1 P_pil2 wf_PIL_impl_wf1_IL by auto
  also have "... \<le> 4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2" using mono_nth wf1_b 
    by (auto simp add: monoD wf_item1_def wf_item_def)
  finally have 5: "T_insert_PIL ?b pil2 \<le> 4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2".
  
  have wf_PIL_union: "wf_PIL (length Bs) (union_LPIL ?step pil1)" 
    using wf1(1) wf_step wf_union_LPIL[of "length Bs" pil1 ?step] by simp
  moreover have inv_union: "inv_PIL (union_LPIL ?step pil1)" using PIL_inv_union_LPIL invs(1) 
    using forall_from_Suc_parse lengs(1) wf_step by auto 
  ultimately have length_snd_union: "length (snd(union_LPIL ?step pil1)) \<le> L * Suc K * Suc (length Bs)" 
    using length_snd_PIL[of "union_LPIL ?step pil1" "length Bs"] by simp

  have wf_PIL_insert: "wf_PIL (length Bs) (insert_PIL ?b pil2)" 
    using wf_PIL_insert[of "length Bs" pil2 ?b] wf1(2) wf1_b by fastforce
  have inv_insert: "inv_PIL (insert_PIL ?b pil2)" 
    using PIL_inv_insert[of pil2 ?b] invs(2) from_b P_pil2 by auto
  let ?length_list = "length (snd (union_LPIL ?step pil1))"
  let ?leng_il = "length (froms (fst (union_LPIL ?step pil1))) - 1"
  have "T_minus_PIL (union_LPIL ?step pil1) (insert_PIL ?b pil2)
    \<le>?length_list * (5 * T_nth_IL (?leng_il) + 3 * L * Suc K + 3) + 2 * ?length_list + 2*?leng_il + 5" 
    using T_minus_PIL_bound[of "union_LPIL ?step pil1" "insert_PIL ?b pil2"]
      wf_PIL_union inv_union wf_PIL_insert inv_insert length_union_LPIL[of ?step pil1] length_insert_parse[of ?b pil1] lengs
    wf_step by auto
  also have "... \<le> L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + 2*length Bs + 5"
    using mult_le_mono1[of ?length_list "L * Suc K * Suc (length Bs)" "(5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3)"] 
      mult_le_mono2[of ?length_list "L * Suc K * Suc (length Bs)" 2] 
      wf_step length_union_LPIL[of ?step pil1] add_mult_distrib lengs(1) length_snd_union by auto
  finally have 6: "T_minus_PIL (union_LPIL ?step pil1) (insert_PIL ?b pil2) \<le>
    L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + 2*length Bs + 5".

  have "T_step2_PIL Bs (pil1,pil2) \<le> 
    T_is_complete (item ?b)
    + (if is_complete (item ?b) then T_Complete_PL Bs ?b else T_fst ?b + (T_length Bs + T_Predict_PL (length Bs) (item ?b)))
    + T_union_LPIL ?step pil1
    + 2 * T_insert_PIL ?b pil2
    + T_minus_PIL (union_LPIL ?step pil1) (insert_PIL ?b pil2)"
    using P_pil1 by (auto simp add: Let_def)
  also have "... \<le> K + 1 + length Bs + (2 * K * K + 2 * K + 5) * C + 2 * Suc K * L + 2 * L + 3 
    + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1
    + 2 * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2)
    + L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + 2*length Bs + 5"
    using 1 3 4 5 6 by (auto simp only: algebra_simps)
  also have "... = 3 * length Bs + K + 14 + 6 * Suc K * L + 2 * L + (2 * K * K + 2 * K + 5) * C 
    + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3) + 8 * T_nth_IL (length Bs)
    + L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 5)"
    by (auto simp add: algebra_simps)
  also have "... \<le>  (2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7"
    by (auto simp add: algebra_simps)
  finally show ?thesis.
qed

lemma step2_PIL_set_inc:
  assumes "step2_PIL Bs (pil1, pil2) = (pil3, pil4)" "list_PIL pil1 \<noteq> []" "inv_PIL pil1" "inv_PIL pil2"
          "set (list_PIL pil1) \<inter> set (list_PIL pil2) = {}" "length (froms (fst pil2)) \<ge> length (froms (fst pil1))"
  shows "length (list_PIL pil4) = Suc (length (list_PIL pil2))"
proof-
  from assms(2,3) obtain x xs m t ts  ys m2 ts2 where "pil1 = (IL (x#xs) m, t#ts)" 
      and "pil2 = (IL ys m2, ts2)"
    using list_PIL_def list_PIL_Cons2
    by (metis item_list.sel(1) T_size_list.cases surjective_pairing il_decomp)
  then show ?thesis using assms by (auto simp add: Let_def list_PIL_def)
qed

lemma T_test2_PIL_0[simp]: "T_test2_PIL x = 0"
  by (cases x) simp

lemma step2_PIL_dist_sets:
  assumes "step2_PIL Bs (pil1, pil2) = (pil3, pil4 )" "list_PIL pil1 \<noteq> []" "inv_PIL pil1" "inv_PIL pil2"
    "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)" "wf_parse_bins1 (map set Bs)"
    "wf_PIL (length Bs) pil1"
  shows "set (list_PIL pil3) \<inter> set (list_PIL pil4) = {}"
proof-
  
  from assms(2,3) obtain x xs m t ts  il2 ts2 where P_il1: "pil1 = (IL (x#xs) m, t#ts)" 
      and P_il2: "pil2 = (il2, ts2)"
    using list_PIL_def list_PIL_Cons2
    by (metis item_list.sel(1) T_size_list.cases surjective_pairing il_decomp)
  let ?step = "PreCo_PL Bs (x,t)"
  let ?step1 = "if is_complete x then Complete_L (map (map item) Bs) x else Predict_L (length Bs) x"

  have m_ne: "m \<noteq> []" using P_il1 assms(5) by force
  have 3: "from x \<le> length Bs" using assms(8) P_il1 by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  have "wf_item_P1 (length Bs) (x,t)" using assms(8) P_il1 by auto
  then have wf: "wf_parse_bin1 (length Bs) (set ?step)" 
    using assms wf1_Complete_PL wf1_Predict_PL
    by (smt (verit) fst_conv)
  have steps_eq: "?step1 = map item ?step" 
    using PPredict_L_eq_Predict_L PComplete_L_eq_Complete_L assms(8) P_il1 
    by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have wf1: "wf_bin1 (length Bs) (set ?step1)" using wf by (auto simp add: wf_bin1_def)

  have 2: "\<forall>x\<in>set ?step. from (item x) < length (froms (fst pil1))" 
    using wf forall_from_Suc_parse assms(5) by auto
  have 4: "\<forall>x \<in> set ?step1. from x < length (froms (fst pil1))" 
    using wf1 forall_from_Suc assms(5) by auto
  
  have 1: "inv_PIL (union_LPIL ?step pil1)"
    using PIL_inv_union_LPIL 2 assms(3) by blast

  have "set (list_PIL pil3) = set (list (minus_IL (union_LIL (map item ?step) (fst pil1)) (insert_IL x (fst pil2))))"
    using assms 1 P_il1 by (auto simp add: Let_def list_PIL_def)
  also have "... = set (list (minus_IL (union_LIL ?step1 (fst pil1)) (insert_IL x (fst pil2))))"
    using steps_eq by auto
  finally have "set (list_PIL pil3) = set (list (minus_IL (union_LIL ?step1 (fst pil1)) (insert_IL x (fst pil2))))".
  moreover have "set (list_PIL pil4) = set (list (insert_IL x (fst pil2)))"
    using assms P_il1 3 by (auto simp add: Let_def list_PIL_def)
  ultimately show "set (list_PIL pil3) \<inter> set (list_PIL pil4) = {}"
    using IL_minus[of "insert_IL x (fst pil2)" "union_LIL ?step1 (fst pil1)"] assms 
        LIL_union_inv[OF _ 4] inv_insert_IL1 3 P_il1 P_il2 m_ne by auto
qed

lemma T_steps2_PIL2_bound:
  assumes k_bound:"k \<le> length (list_PIL pil2) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7)" 
  and res: "T_steps2_PIL2 Bs (pil1, pil2) k = Some ((pil3, pil4), k1)"
  and invs: "inv_PIL pil1" "inv_PIL pil2"
  and lengs: "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)"
  and wf1: "wf_PIL (length Bs) pil1" "wf_PIL (length Bs) pil2" "wf_parse_bins1 (map set Bs)"
  and distinct: "set (list_PIL pil1) \<inter> set (list_PIL pil2) = {}" 
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
  shows "k1 \<le> length (list_PIL pil4) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7)"
proof-
  let ?C = "(2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7"
  let ?P3 = "\<lambda>((pil1',pil2'),k). wf_PIL (length Bs) pil1' \<and> wf_PIL (length Bs) pil2' \<and> wf_parse_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((pil1',pil2'),k). wf_PIL (length Bs) pil1' \<and> wf_PIL (length Bs) pil2' \<and> wf_parse_bins1 (map set Bs) \<and> inv_PIL pil1' \<and> inv_PIL pil2' 
        \<and> length (froms (fst pil1')) = Suc (length Bs) \<and> length (froms (fst pil2')) = Suc (length Bs) \<and> (\<forall>i < length Bs. length (Bs ! i) \<le> C)  
        \<and> set (list_PIL pil1') \<inter> set (list_PIL pil2') = {}" 
  let ?P2 = "\<lambda>((pil1',pil2'),k). k \<le> length (list_PIL pil2') * (?C)"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((pil1,pil2),k). list_PIL pil1 \<noteq> [])"
  let ?c = "\<lambda>((pil1,pil2),k). (step2_PIL Bs (pil1,pil2), k + T_test2_PIL (pil1,pil2) + T_step2_PIL Bs (pil1,pil2))"

  (* neede to bridge different treatment of pairs *)
  have annoying_bridge: "T_steps2_PIL2 Bs x k =
  while_option (\<lambda>((B,C),n). list_PIL B \<noteq> [])
    (\<lambda>((x,y),n). (step2_PIL Bs (x,y), n + T_test2_PIL (x,y) + T_step2_PIL Bs (x,y))) (x,k)" for x
  by(simp add: T_while_option2_def test2_PIL_def split_def)

  have init: "?P ((pil1,pil2), k)" using assms by auto

  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y
    using PIL_inv_parse_step1' PIL_inv_parse_step2' wf_parse_step2' wf_parse_step1' length_parse_step1' 
      length_parse_step2' step2_PIL_dist_sets
    by (smt (verit) case_prodI2' case_prod_conv)
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_step2_PIL Bs (a, b) \<le> ?C" using T_parse_step2_IL_bound[of a b Bs C] by auto
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "step2_PIL Bs (a,b) = (a', b')" by auto
    then have "length (list_PIL b') = Suc (length (list_PIL b))" 
      using step2_PIL_set_inc  assms by auto
    then have 2: "length (list_PIL b') * ?C = length (list_PIL b) * ?C + ?C"
      by (metis add.commute mult_Suc)
    have "y' \<le> y + ?C" using P1 1 by auto
    also have "... \<le> length (list_PIL b) * ?C + ?C" 
      using assms by (auto simp add: add_mult_distrib2)
    also have "... = length (list_PIL b') * ?C" using 2 by auto
    finally have "y' \<le> length (list_PIL b') * ?C".
    then show "?P2 (?c ((a,b), y))" using P1
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
  qed

  then have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P (?c ((a,b), y)))" for a b y using P1 by auto
  then have "?P ((pil3,pil4), k1)"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((pil1,pil2),k)", where t="((pil3,pil4), k1)"] res init
    unfolding annoying_bridge by (auto simp only:)
  then show "k1 \<le> (length (list_PIL pil4)) * ?C"
    by auto
qed

lemma T_steps_PIL_bound: 
  assumes length_pil2: "length (list_PIL pil2) = 0"
  and invs: "inv_PIL pil1" "inv_PIL pil2"
  and lengs: "length(froms  (fst pil1)) = Suc (length Bs)" "length(froms  (fst pil2)) = Suc (length Bs)"
  and wf1: "wf_PIL (length Bs) pil1" "wf_PIL (length Bs) pil2" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
  shows "T_steps_PIL Bs (pil1, pil2) \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7)"
proof-
  obtain pil3 pil4 k where Psteps_time: "T_steps2_PIL2 Bs (pil1, pil2) 0 = Some ((pil3, pil4), k)" 
    and Psteps: "steps_PIL Bs (pil1, pil2) = Some (pil3, pil4)"
    using assms steps_PIL_NF T_while_option2_if_T_while_option
    unfolding steps_PIL_def by metis
  have "wf_PIL (length Bs) pil4" using Psteps steps_PIL_wf2 wf1 invs lengs by blast
  then have length_bound: "length (list_PIL pil4) \<le> L * Suc K * Suc (length Bs)" 
    using length_fst_PIL steps_PIL_inv2 invs Psteps lengs
    by (metis list_PIL_def wf1(1,3))
  have "T_steps_PIL Bs (pil1, pil2) \<le> length (list_PIL pil4) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7)"
    using assms Psteps_time T_steps2_PIL2_bound[of 0] by (auto simp: T_while_option_def)
  also have "... \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7)" using length_bound by simp
  finally show ?thesis.
qed

lemma T_close2_PIL_bound: 
  assumes invs: "inv_PIL pil1"
  and lengs: "length (froms (fst pil1)) = Suc (length Bs)" 
  and wf1: "wf_PIL (length Bs) pil1" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
shows "T_close2_PIL Bs pil1 \<le> length Bs + 1 + Suc (length Bs) + L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7) +  Suc (L * Suc K * Suc (length Bs))"
proof-
  have 2: "T_empty_PIL (length Bs) = length Bs + 1" by (simp del: T_empty_IL.simps)
  have 3: "T_length Bs = Suc (length Bs)" by (simp add: T_length)

  have empty_inv: "inv_PIL (empty_PIL (length Bs))" and "length (froms (fst (empty_PIL (length Bs)))) = Suc (length Bs)"
    and empty_wf: "wf_PIL (length Bs) (empty_PIL (length Bs))"
    and "length (list_PIL (empty_PIL (length Bs))) = 0"
    using PIL_inv_empty wf_empty_PIL by (auto simp add: list_PIL_def)
  then have 1: "T_steps_PIL Bs (pil1, empty_PIL (length Bs)) \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7)" using T_steps_PIL_bound assms by simp

  obtain a where Some_Psteps: "steps_PIL Bs (pil1, empty_PIL (length Bs)) = Some a"
    using steps_PIL_NF empty_inv empty_wf length_empty_PIL lengs invs wf1(1,2) by blast

  let ?result_PIL = "(snd (the (steps_PIL Bs (pil1, empty_PIL (length Bs)))))"
  have "wf_PIL (length Bs) ?result_PIL"
    using wf_close2_PIL assms by (auto simp add: close2_PIL_def simp del: wf_parse_bin1.simps)
  moreover have res_inv: "inv_PIL ?result_PIL" using  steps_PIL_inv2 invs empty_inv empty_wf length_empty_PIL
    by (metis steps_PIL_NF eq_snd_iff option.sel wf1(1,2) lengs)
  ultimately have "length (list (fst ?result_PIL)) \<le> L * Suc K * Suc (length Bs)" using length_fst_PIL by auto
  then have "T_list2_PIL ?result_PIL \<le> Suc (L * Suc K * Suc (length Bs))" using res_inv T_zip 
    by (cases ?result_PIL) fastforce
  moreover have "T_the (steps_PIL Bs (pil1, empty_PIL (length Bs))) = 0" using Some_Psteps by auto
  moreover have "T_snd (the (steps_PIL Bs (pil1, empty_PIL (length Bs)))) = 0" by simp
  ultimately show ?thesis using 1 2 3 unfolding T_close2_PIL.simps by presburger
qed

lemma length_close2_PIL: 
  assumes "inv_PIL pil" "wf_PIL (length Bs) pil" "wf_parse_bins1 (map set Bs)" "length (froms (fst pil)) = Suc (length Bs)"
  shows "length (close2_PIL Bs pil) \<le> L * Suc K * Suc (length Bs)"
proof-
  have empty_inv: "inv_PIL (empty_PIL (length Bs))" and empty_wf: "wf_PIL (length Bs) (empty_PIL (length Bs))"
    and empty_leng: "length (froms (fst (empty_PIL (length Bs)))) = Suc (length Bs)"
    using PIL_inv_empty wf_empty_PIL by auto

  let ?result_PIL = "(snd (the (steps_PIL Bs (pil, empty_PIL (length Bs)))))"
  have "wf_PIL (length Bs) ?result_PIL"
    using wf_close2_PIL assms by (auto simp add: close2_PIL_def simp del: wf_parse_bin1.simps)
  moreover have res_inv: "inv_PIL ?result_PIL" using  steps_PIL_inv2 empty_inv empty_wf empty_leng assms
    by (metis steps_PIL_NF eq_snd_iff option.sel)
  ultimately show "length (close2_PIL Bs pil) \<le> L * Suc K * Suc (length Bs)" 
    using length_snd_PIL by (cases ?result_PIL) (auto simp add: close2_PIL_def)
qed

lemma bins_PIL_lengths: "k \<le> length w \<Longrightarrow> \<forall> i < Suc k. length ((bins_PIL k) ! i) \<le> L * Suc K * Suc k"
proof(induction k)
  case 0
  have "length (close2_PIL [] (PIL_list 0 Init_PL)) \<le> L + L * K" 
    using length_close2_PIL[of "PIL_list 0 Init_PL" "[]"] PIL_inv_PIL_list[OF forall_from_Suc_parse]
      wf_PIL_list[of 0 Init_PL 0] wf1_Init_PL ex_map_conv in_set_conv_nth 
      less_nat_zero_code list.distinct(1) wf_parse_bins1_def by fastforce 
  then show ?case 
       by auto
next
  case (Suc k)
  then have ih: "\<forall> i < Suc k. length (bins_PIL (Suc k) ! i) \<le> L * Suc K * Suc (Suc k)" 
    by (auto simp add: Let_def nth_append_left)
  let ?scan_pil = "PIL_list (Suc k) (Scan_PL k (last (bins_PIL k)))"
  have "bins_P k \<noteq> []"
    by (metis length_parse_bins list.size(3) nat.distinct(1))
  then have "last (bins_PIL k) = bins_PIL k ! k" using Suc length_parse_bins last_conv_nth
    by (metis One_nat_def Zero_not_Suc diff_Suc_Suc length_bins_P list.size(3) minus_nat.diff_0)
  then have "wf_parse_bin1 k (set (last (bins_PIL k)))" 
    using Suc wf_parse_bins_IL unfolding wf_parse_bins1_def by (auto simp del: wf_parse_bin1.simps)
  then have 1: "wf_PIL (length (bins_PIL k)) ?scan_pil" using wf1_Scan_PL Suc wf_PIL_list
    using length_bins_P less_eq_Suc_le by presburger
  moreover have "inv_PIL ?scan_pil" using 1 PIL_inv_PIL_list[OF forall_from_Suc_parse]
    by (meson Suc.prems \<open>wf_parse_bin1 k (set (last (bins_PIL k)))\<close> less_eq_Suc_le wf1_Scan_PL)
  moreover have "wf_parse_bins1 (map set (bins_PIL k))" using Suc wf_parse_bins_IL by simp
  ultimately have 1: "length (close2_PIL (bins_PIL k) ?scan_pil) \<le> L * Suc K * Suc (Suc k)" 
    using length_close2_PIL[of ?scan_pil "bins_PIL k"] by auto
  then have "length (bins_PIL (Suc k) ! (Suc k)) \<le> L * Suc K * Suc (Suc k)" by (simp add: Let_def nth_append_right)
  then show ?case using ih not_less_less_Suc_eq by blast
qed



lemma T_bins_PIL_bound:
  assumes "k \<le> length w"
  shows "T_bins_PIL k 
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L) + L + 7 + k"
using assms proof(induction k)
  case 0
  have 1: "length Init_PL \<le> L" by (auto simp add: Init_PL_def L_def)
  have "T_PIL_list 0 Init_PL \<le> (length Init_PL) * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + length Init_PL + 2"
    using T_PIL_list_bound by (metis Nat.add_0_right  assms(1) wf1_Init_PL)
  also have "... \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + L + 2"
    using 1 mult_le_mono1[OF 1, of "(4 * T_nth_IL (0) + 2 * L * Suc K + 2)"] by auto
  finally have 2: "T_PIL_list 0 Init_PL \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + L + 2".

  have "wf_parse_bins1 (map set [])" by (auto simp add: wf_parse_bins1_def)
  moreover have "\<forall>i<length []. length ([] ! i) \<le> 0" by auto
  moreover have "wf_PIL 0 (PIL_list 0 Init_PL)" using wf_PIL_list wf1_Init_PL by blast
  moreover have "length (froms (fst (PIL_list 0 Init_PL))) = 1" 
    using length_PIL_list wf1_Init_PL by (auto simp add: wf_item1_def )
  ultimately have "T_close2_PIL [] (PIL_list 0 Init_PL) \<le> 1 + 1 + L * Suc K  
    * (L * (4 * T_nth_IL (0) + 2 * L * Suc K + 3)
    + Suc L * Suc K  * (13 * T_nth_IL (0) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7) +  Suc (L * Suc K)" 
    using T_close2_PIL_bound[of "PIL_list 0 Init_PL" "[]" 0] assms 
      PIL_inv_PIL_list[OF forall_from_Suc_parse] wf1_Init_PL
    by (auto simp del: T_close2_PIL.simps)
  also have "... \<le> L * Suc K  * (Suc L * Suc K  * (17 * T_nth_IL (0) + 5 * L * Suc K + 19)) + 3" 
    by (auto simp add: algebra_simps)
  finally have "T_close2_PIL [] (PIL_list 0 Init_PL) 
    \<le> L * Suc K  * (Suc L * Suc K  * (17 * T_nth_IL (0) + 5 * L * Suc K + 19)) + 3".

  then have "T_bins_PIL 0 \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + L + 3
    + L * Suc K  * (Suc L * Suc K  * (17 * T_nth_IL (0) + 5 * L * Suc K + 19)) + 3 + 1"
    using 2 by auto
  also have "... \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
    + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L) + L + 7" 
    by (auto simp add: algebra_simps)
  finally show ?case by auto
next  
  case (Suc k)
  let ?Bs = "bins_PIL k"
  have cons: "?Bs \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_bins_P)
  then have length_last: "length (last ?Bs) \<le> L * Suc K * Suc k" 
    using bins_PIL_lengths last_conv_nth Suc
    by (metis One_nat_def diff_Suc_1' length_bins_P less_eq_Suc_le order_le_less)
  have wf1_last: "wf_parse_bin1 k (set (last ?Bs))" 
    using length_bins_P wf_parse_bins_IL[of k] cons Suc
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_item_P1.simps)
  then have wf_last: "wf_parse_bin k (set (last ?Bs))" using Suc by (auto simp add: wf_item1_def)

  have 1: "T_length ?Bs = k + 2" by (auto simp add: T_length)
  have 2: "T_last ?Bs = k + 1" using T_last cons by auto
  have "T_Scan_PL k (last ?Bs) \<le> k + (2 * K + 4) * (length (last (bins_PIL k))) + 3"
    using wf_last Suc T_Scan_PL_bound
    by (auto simp add: w_def simp del: T_Scan_PL.simps)
  also have "... \<le> k + (2 * K + 4) * (L * Suc K * Suc k) + 3" using length_last by auto
  finally have 3: "T_Scan_PL k (last ?Bs) \<le> k + (2 * K + 4) * (L * Suc K * Suc k) + 3".

  let ?parse = "Scan_PL k (last ?Bs)"
  have "length ?parse \<le> length (last ?Bs)" 
    unfolding Scan_PL_def Let_def by simp
  then have length_parse: "length ?parse \<le> L * Suc K * Suc k" using length_last by auto
  have "T_PIL_list (length ?Bs) (Scan_PL k (last ?Bs)) 
    \<le> length ?parse * (4 * T_nth_IL (length ?Bs) + 2 * L * Suc K + 2) + length ?parse + length ?Bs + 3" 
    using T_PIL_list_bound[of "length ?Bs" ?parse] wf1_Scan_PL wf1_last Suc 
    by (auto simp del: T_PIL_list.simps wf_parse_bin1.simps)
  also have "... \<le> L * Suc K * Suc k * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 3" 
    using length_parse mult_le_mono1[OF length_parse, of "(4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2)"]
    by (auto simp add: algebra_simps)
  finally have 4: "T_PIL_list (length ?Bs) (Scan_PL k (last ?Bs))
    \<le> L * Suc K * Suc k * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 3".

  have 5: "T_append ?Bs [close2_PIL ?Bs (PIL_list (length ?Bs) (Scan_PL k (last ?Bs)))] 
    = k+2" by simp

  let ?parse_pil = "PIL_list (length ?Bs) (Scan_PL k (last ?Bs))"
  have wf1_parse: "wf_parse_bin1 (Suc k) (set ?parse)" using wf1_Scan_PL wf1_last Suc 
    by (auto simp del: wf_parse_bin1.simps)
  have "inv_PIL ?parse_pil" using PIL_inv_PIL_list[OF forall_from_Suc_parse]
    using length_bins_P wf1_parse by presburger
  moreover have "wf_PIL (Suc k) ?parse_pil" using wf_PIL_list wf1_Scan_PL wf1_last Suc 
    by (auto simp del: wf_parse_bin1.simps)
  moreover have "length (froms (fst ?parse_pil)) - 1 = Suc k" 
    using wf1_parse by (auto simp add: wf_item1_def)
  ultimately have "T_close2_PIL ?Bs (PIL_list (length ?Bs) (Scan_PL k (last ?Bs)))
    \<le> Suc k + 1 + Suc (Suc k) + L * Suc K * Suc (Suc k)
    * ((2 * K * K + 2 * K + 5) * (L * Suc K * Suc k) + (L * Suc K * Suc k) * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (Suc k) * (13 * T_nth_IL (Suc k) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 7) +  Suc (L * Suc K * Suc (Suc k))"
    using T_close2_PIL_bound[of ?parse_pil ?Bs "L * Suc K * Suc k"] bins_PIL_lengths wf_parse_bins_IL Suc 
    by (auto simp del: T_close2_PIL.simps wf_parse_bin1.simps)
  also have "... = L * Suc K * Suc (Suc k)
    * ((L * Suc K * Suc k) * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K * K + 2 * K + 8)
    + Suc L * Suc K * Suc (Suc k) * (13 * T_nth_IL (Suc k) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 8) + 2 * k + 5" by (auto simp add: algebra_simps)
  also have "... \<le> L * Suc K * Suc (Suc k)
    * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)) 
    + 2 * k + 5" by (auto simp add: algebra_simps)
  finally have 6:  "T_close2_PIL ?Bs (PIL_list (length ?Bs) (Scan_PL k (last ?Bs)))
    \<le> L * Suc K * Suc (Suc k)
      * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)) 
      + 2 * k + 5".

  have "T_bins_PIL k \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L) + L + 7 + k"
    using Suc by simp
  also have "... \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L) + L + 7 + k"
  proof-
    have "T_nth_IL k \<le> T_nth_IL (Suc k)" using mono_nth monoD[of T_nth_IL k "Suc k"] by simp
    then have 1: "4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20 \<le> 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20"
      by auto
    then have "17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24 
        \<le> 17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24" by auto
    then have "Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
        \<le> Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)"
      using mult_le_mono2 by blast
    then have "(Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
        \<le> (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20)" using 1 add_le_mono[OF _ 1] by (simp only:)
    then show ?thesis by auto
  qed
  finally have "T_bins_PIL k \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L) + L + 7 + k".

  then have "T_bins_PIL (Suc k)
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L) + L + 7 + k
      +
      k + 3 + k + 1 + k + (2 * K + 4) * (L * Suc K * Suc k) + 3
      + L * Suc K * Suc k * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 3
      + L * Suc K * Suc (Suc k)
      * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)) 
      + 2 * k + 5 + k + 1 + 1" unfolding T_bins_PIL.simps Let_def using 1 2 3 4 5 6 by presburger
  
  also have "... \<le> Suc k *
       (L * Suc K * Suc (Suc (Suc k)) *
        (Suc L * Suc K * Suc (Suc (Suc k)) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20) +
        7 * Suc k +
        16) +
       L * (4 * T_nth_IL 0 + 2 * L * Suc K + 2) +
       L * Suc K * (Suc L * Suc K * (21 * T_nth_IL 0 + 5 * L * Suc K + 19) + 2 * L) +
       L +
       7 +
       Suc k" by simp (simp add: algebra_simps)
  finally show ?case.
qed

subsubsection \<open>Nice time bounds\<close>

definition C3 where "C3 = 10 * (Suc L)^3 * (Suc K)^4"
definition C4 where "C4 = 10 * (Suc L)^2  * (Suc K)^3"
definition C6 where "C6 = 17 * (Suc L)^2 * (Suc K)^2"
definition C7 where "C7 = L * Suc K * 4"
definition C5 where "C5 = 10 * (Suc L)^3 * (Suc K)^3 + 25 * (Suc L)^2 * (Suc K)^2 * T_nth_IL (0)"


theorem T_bins_P_bound_nice:
  assumes "k \<le> length w"
  shows "T_bins_PIL k 
      \<le> (k+2)^3 * C3 + (k+2)^2 * C4 + (k+2) * 3 + C5 
        + (k+2)^3 * T_nth_IL (k) * C6 + (k+2)^2 * T_nth_IL (k) * C7"
proof-
  have "T_bins_PIL k 
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L) + L + 7 + k"
    using T_bins_PIL_bound assms by simp
  also have "... \<le> (k+2) * (L * Suc K * (k+2)
          * (Suc L * Suc K * (k+2) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * (k + 2) + 2)
        + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_IL (0) + 5 * L * Suc K + 20) + 2 * L) + L + 7 + k"
    by (auto simp add: algebra_simps)
  also have "... = (k+2) * (k+2) * (k+2) * (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))
    + (k+2) * (k+2) * (k+2) * (L * Suc K * Suc L * Suc K * 17 * T_nth_IL (k))
    + (k+2) * (k+2) * (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)
    + (k+2) * (k+2) * (L * Suc K * 4 * T_nth_IL (k))
    + (k+2) * 3
    + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_IL (0) + 5 * L * Suc K + 20) + 2 * L) + L + 5"
    by (auto simp add: algebra_simps)
  also have "... = (k+2)^3 * (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))
    + (k+2)^3 * (L * Suc K * Suc L * Suc K * 17 * T_nth_IL (k))
    + (k+2)^2 * (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)
    + (k+2)^2 * (L * Suc K * 4 * T_nth_IL (k))
    + (k+2) * 3 
    + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_IL (0) + 5 * L * Suc K + 20) + 2 * L) + L + 5" 
    by (simp only: monoid_mult_class.power3_eq_cube monoid_mult_class.power2_eq_square)
  also have "... \<le> (k+2)^3 * 10 * (Suc L * Suc L * Suc L) * (Suc K * Suc K * Suc K * Suc K)
    + (k+2)^3 * T_nth_IL (k) * 17  * (Suc L * Suc L) * (Suc K * Suc K)
    + (k+2)^2 * 10 * (Suc L * Suc L) * (Suc K * Suc K * Suc K)
    + (k+2)^2 * T_nth_IL (k) * L * Suc K * 4
    + (k+2) * 3 
    + 10 * (Suc L * Suc L * Suc L) * (Suc K * Suc K * Suc K) + 25 * (Suc L * Suc L) * (Suc K * Suc K) * T_nth_IL (0)"
    by (auto simp add: algebra_simps)
  also have "... = (k+2)^3 * 10 * (Suc L)^3 * (Suc K)^4
    + (k+2)^3 * T_nth_IL (k) * 17 * (Suc L)^2 * (Suc K)^2
    + (k+2)^2 * 10 * (Suc L)^2  * (Suc K)^3
    + (k+2)^2 * T_nth_IL (k) * L * Suc K * 4
    + (k+2) * 3
    + 10 * (Suc L)^3 * (Suc K)^3 + 25 * (Suc L)^2 * (Suc K)^2 * T_nth_IL (0)"
    by (simp only: monoid_mult_class.power3_eq_cube monoid_mult_class.power2_eq_square monoid_mult_class.power4_eq_xxxx)
  finally show ?thesis by (auto simp add: C3_def C4_def C5_def C6_def C7_def algebra_simps)
qed


time_fun get_parse_tree
time_fun get_parse_tree_w

lemma T_get_parse_tree_bound: "wf_parse_bin1 k (set xs) \<Longrightarrow> T_get_parse_tree xs \<le> Suc K * Suc (length xs) + 2 * K * K + 1 + Suc (length xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have 1: "T_get_parse_tree xs \<le> Suc K * Suc (length xs) + 2 * K * K + 1 + Suc (length xs)" by auto
  from Cons have 2: "T_is_final (item a) \<le> Suc K" using T_final_bound by (auto simp add: wf_item1_def wf_item_def)
  from Cons have "T_rev (trees a) \<le> 2 * K * K + 1" using T_rev_tree by (auto simp add: wf_item1_def)
  then show ?case using 1 2 by (simp del: T_is_final.simps)
qed

definition C8 where "C8 = 6 * Suc L * (Suc K)^2"

lemma T_ovrall_time_bound: "T_get_parse_tree_w w0 \<le>  
  (length w + 2)^3 * C3 + (length w + 2)^2 * C4 + (length w + 2) * C8 + C5 
        + (length w + 2)^3 * T_nth_IL (length w) * C6 + (length w + 2)^2 * T_nth_IL (length w) * C7"
proof-
  let ?C = "((length w)+2)^3 * C3 + ((length w)+2)^2 * C4 + ((length w)+2) * 3 + C5 
        + ((length w)+2)^3 * T_nth_IL ((length w)) * C6 + ((length w)+2)^2 * T_nth_IL ((length w)) * C7"
  have 1: "T_bins_PIL (length w) \<le> ?C  "
    using T_bins_P_bound_nice[of "length w"] by simp
  have ne: "(bins_PIL (length w)) \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_bins_P)
  then have wf_last: "wf_parse_bin1 (length w) (set (last (bins_PIL (length w))))"
    using wf_parse_bins_IL[of "length w"] 
    by (auto simp del: wf_parse_bin1.simps simp add: wf_parse_bins1_def last_conv_nth)
  have "length (last (bins_PIL (length w))) \<le> L * Suc K * Suc (length w)" 
    using bins_PIL_lengths ne w_def by (auto simp add: last_conv_nth)
  then have T_pt: "T_get_parse_tree (last (bins_PIL (length w))) 
    \<le> Suc K * Suc (L * Suc K * Suc (length w)) + 2 * K * K + 1 + Suc (L * Suc K * Suc (length w))"
    using T_get_parse_tree_bound[of "length w" "last (bins_PIL (length w))"] wf_last
    by (smt (verit, ccfv_SIG) Suc_le_mono Suc_mult_le_cancel1 add_le_mono add_le_mono1 le_trans)
  have T_l: "T_last (bins_PIL (length w)) = Suc (length w)" using ne T_last by auto
  then have "T_get_parse_tree_w w0 \<le> Suc (length w) + ?C + Suc (length w)
    + Suc K * Suc (L * Suc K * Suc (length w)) + 2 * K * K + 1 + Suc (L * Suc K * Suc (length w))" 
    unfolding T_get_parse_tree_w.simps using ne 1 T_length[of w] T_l T_pt by linarith
  also have "... \<le> (length w + 2)^3 * C3 + (length w + 2)^2 * C4 + (length w + 2) * (6 * Suc L * Suc K * Suc K) + C5 
        + (length w + 2)^3 * T_nth_IL (length w) * C6 + (length w + 2)^2 * T_nth_IL (length w) * C7"
    by (simp add: algebra_simps)
  finally show ?thesis by (simp only: C8_def monoid_mult_class.power2_eq_square)
qed

end

(*unused_thms*)

end