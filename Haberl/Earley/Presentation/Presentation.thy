(*<*)
theory Presentation
  imports
  "Earley.EarleyWorklist"
  Sugar
begin
section proofs
declare [[show_question_marks=false]]
declare [[names_short=true]]

(* to get rid of annoying eta-contraction *)
notation (output) id ("_")


lemma T_list_update_general: "T_list_update xs n a \<le> Suc n"
  by (induction xs arbitrary: n) (auto split: nat.split)

context Earley_Gw begin
(*definition X :: "nat \<Rightarrow> ('n,'a) item set"
  ("(\<S>\<^bsub>_\<^esub>)" [800] 1000) where
"(\<S>\<^bsub>i\<^esub>) = ({x. (x,i) \<in> Earley})"*)

definition paresIL_for_Typedef :: "('n, 'a) efficientItemList \<times> ('n, 'a) tree list list"
  where "paresIL_for_Typedef = (empty_IL 0, [[]])"

definition parseItem_for_Typedef :: "('n,'a) parseItem" 
  where "parseItem_for_Typedef = ((Earley.Item (hd (ps)) 0 0),([] :: ('n,'a) tree list))"

notation \<S> ("(\<S>\<^bsub>_\<^esub>)")
notation (latex) \<S> ("(\<S>\<^bsub>\<^latex>\<open>\\isavar{\\myscriptsize\<close>_\<^latex>\<open>}\<close>\<^esub>)" [800] 1000)

(*lemma Earley_eq_\<S>1: "(x,i) \<in> Earley \<longleftrightarrow> x \<in> \<S>\<^bsub>i\<^esub>"
by(simp add: X_def)*)

lemma Earley_predict: assumes "x \<in> (\<S>\<^bsub>i\<^esub>)" and "next_sym_Nt x A" and "p \<in> P" and "lhs p = A" shows "Item p 0 i \<in> \<S>\<^bsub>i\<^esub>"
  using Earley.Predict[of x i "Item p 0 i"] assms by (cases p) (auto simp add: \<S>_def Predict_def)

lemma Earley_complete_rule: assumes "x \<in> (\<S>\<^bsub>i\<^esub>)" "is_complete x" "from x = f" "y \<in> \<S>\<^bsub>f\<^esub>" "next_sym_Nt y (lhs (prod x))" shows "mv_dot y \<in> \<S>\<^bsub>i\<^esub>"
  using Earley.Complete[of x i] assms by (auto simp add: \<S>_def)

lemma Earley_init: assumes "p \<in> P" "lhs p = S" shows "Item p 0 0 \<in> \<S>\<^bsub>0\<^esub>"
  using Earley.Init[of "Item p 0 0"] assms by (cases p) (auto simp add: \<S>_def Init_def)

definition accepted2 where "accepted2 = (\<exists>x \<in> (\<S>\<^bsub>length w\<^esub>). is_final (id x))"

lemma accepted_def2: shows "accepted = (\<exists>x \<in> (id (\<S> (length w))). is_final (id x))" 
  unfolding accepted_def by (auto simp add: \<S>_def)


definition Complete_Th where "Complete_Th Bs y = {mv_dot x | x. x \<in> Bs ! from y \<and> next_sym_Nt x (lhs(prod y))}"

lemma "Earley_Gw.Complete_Th Bss y = Complete Bss y"
  by (auto simp add: Complete_def Complete_Th_def)

theorem Earley_complete_Th:
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* w"
  shows "accepted"
  using Earley_complete assms by (auto simp add: accepted_def recognized_def \<S>_def)

theorem Earley_correct_accepted:
  shows "accepted = (P \<turnstile> [Nt S] \<Rightarrow>* w)"
  using Earley_complete_Th accpted_sound by auto

fun inv_IL_display where
"inv_IL_display (ItemList as fs) = (mbox0 (0 < length fs \<and> (\<forall>x\<in>set as. from x < length fs)) \<and>
     (\<forall>i<length fs. set (fs ! i) = {x \<in> (set as). (from x = i)}) 
      \<and> (\<forall>i<length fs. distinct (fs ! i)) \<and> distinct as)"

lemma "inv_IL (ItemList as fs) = inv_IL_display (ItemList as fs)" by (simp add: mbox0_def)

definition get_parse_tree3 :: "('n, 'a) tree option"  where
"get_parse_tree3 = (let ts = (SOME t. \<exists>i. (i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i) in if (\<exists> i t. (i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i) then Some ( Rule S (rev ts)) else None)"


definition earley_recognized_Th :: "bool"  where
  "earley_recognized_Th = recognized_L (last (bins_L (length w)))"

notation earley_recognized_Th ("\<^latex>\<open>\\isaconst{\<close>earley'_recognized\<^latex>\<open>}\<close>")


(*List version*)
fun  Close2_L ("_ \<turnstile> _ \<rightarrow>\<^bsub>L\<^esub> _") where 
"Close2_L Bs (bs, cs) (bs', cs') = Close2 (map set Bs) (set bs, set cs) (set bs', set cs')"

abbreviation Close2_L_steps ("(_ \<turnstile> _ \<rightarrow>* _)" [50, 0, 50] 50) where
"Bs \<turnstile> p \<rightarrow>* p' \<equiv> (Close2_L Bs)^** p p'"

fun step_fun_L :: "('n,'a) item list list \<Rightarrow> ('n,'a) item list \<times> ('n,'a) item list \<Rightarrow> ('n,'a) item list \<times> ('n,'a) item list" where
  "step_fun_L Bs (b#bs, cs) = 
  (let nexts = (if is_complete b then Complete_L Bs b else Predict_L b (length Bs))
  in (diff_list (union_list nexts (b#bs)) (insert_list b cs), insert_list b cs))"

fun steps_L :: "('n,'a) item list list \<Rightarrow> ('n,'a) item list \<times> ('n,'a) item list \<Rightarrow> (('n,'a) item list \<times> ('n,'a) item list) option" where
  "steps_L Bs BC = while_option (\<lambda>(B',C'). B' \<noteq> []) (step_fun_L Bs) BC"

fun steps_L3 :: "('n,'a) item list list \<Rightarrow> ('n,'a) item list \<times> ('n,'a) item list \<Rightarrow> (('n,'a) item list \<times> ('n,'a) item list)" where
  "steps_L3 Bs BC = the (steps_L Bs BC)"

fun steps_L2 where
  "steps_L2 Bs (B,C) = (if B \<noteq> [] then steps_L3 Bs (step_fun_L Bs (B,C)) else (B,C))"

lemma test_Th_17: "steps_L2 Bs (B, C) = the (steps_L Bs (B,C))"
  by (auto simp add: while_option_unfold)

definition close2_L_Th where
"close2_L_Th Bs B = snd (the (steps_L Bs (B,[])))"

fun bins_L_Th where
"bins_L_Th 0 = [close2_L_Th [] Init_L]"
| "bins_L_Th (Suc k) = (let Bs = bins_L_Th k in Bs @[close2_L_Th Bs (Scan_L (last Bs) k)])"

definition earley_recognized1 where
"earley_recognized1 = earley_recognized"

fun minus_LIL_Th where
"minus_LIL_Th k [] il = empty_IL k" |
"minus_LIL_Th k (a#as) il = (if isin il a then minus_LIL_Th k as il else insert a (minus_LIL_Th k as il))"


lemma Close2_Predict_Th: "x \<in> B \<Longrightarrow> \<not> is_complete x \<Longrightarrow> Bs \<turnstile> (B, C) \<rightarrow> (B \<union> Predict x (length Bs) - (C \<union> {x}), C \<union> {x})"
  using Close2.Predict by (auto)


lemma step_fun_L_sound: "B \<noteq> [] \<Longrightarrow> wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) 
  \<Longrightarrow> step_fun_L Bs (B,C) = (B',C') \<Longrightarrow> Close2_L Bs (B,C) (B',C')"
proof-
  assume assms: "B \<noteq> []" "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "step_fun_L Bs (B,C) = (B',C')"
  then obtain b bs where P: "B = b#bs" by (auto simp add: neq_Nil_conv)
  then have "wf_item1 b (length Bs)" using assms by (auto simp add: wf_bin1_def)
  then show ?thesis using Close2.Complete Close2.Predict[of b "set (b#bs)" "map set Bs"] P assms Un_commute[of _ "set (b#bs)"]
    by (auto simp add: Let_def set_Predict_L set_Complete_L  list.set_intros(1) simp del: set_simps(2))
qed

lemma test_Th4: "B \<noteq> [] \<Longrightarrow> wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) 
  \<Longrightarrow> step_fun_L Bs (B,C) = (B',C') \<Longrightarrow> Close2 (map set Bs) (set B,set C) (set B',set C')"
  using step_fun_L_sound by auto

end


context Earley_Gw_eps
begin

lemma close2_eq_Close: "wf_bins1 Bs \<Longrightarrow> wf_bin1 B (length Bs) \<Longrightarrow> close2 Bs B = Close Bs B"
  by (auto simp add: close2_eq_Close1 Close1_eq_Close)

lemma step_fun_L_wf: 
  assumes "B \<noteq> []" "wf_bin1 (set B) (length Bs)" "wf_bins1 (map set Bs)" shows "wf_bin1 (set (fst (step_fun_L Bs (B, C)))) (length Bs)"
proof-
  obtain y ys where P: "B = y # ys" using assms(1) by (auto simp add: neq_Nil_conv)
  then have "wf_bin1 (set (if is_complete y then Complete_L Bs y else Predict_L y (length Bs))) (length Bs)"
    using wf1_Complete_L wf1_Predict_L assms[unfolded wf_bin1_def] by (auto simp add: )
  then show ?thesis using assms P
   by (auto simp add: wf1_Complete_L wf1_Predict_L wf_bin1_def if_split_mem2)
qed

lemma step_fun_L_wf1: 
  assumes "B \<noteq> []" "wf_bin1 (set B) (length Bs)" "wf_bin1 (set C) (length Bs)" "wf_bins1 (map set Bs)" shows "wf_bin1 (set (snd (step_fun_L Bs (B, C)))) (length Bs)"
proof-
  obtain y ys where P: "B = y # ys" using assms(1) by (auto simp add: neq_Nil_conv)
  then have "wf_bin1 (set (insert_list y C)) (length Bs)"
    using assms by (auto simp add: wf_bin1_def)
  then show ?thesis using assms P
   by (auto simp add:)
qed



lemma steps_L_Th_sound: assumes  "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "steps_L Bs (B,C) = Some (B',C')"
  shows "(Close2_L Bs)^** (B,C) ([],C')"
proof -
  let ?P = "\<lambda>(B',C'). (Close2_L Bs)^** (B,C) (B',C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)"
  have "\<And>B C. B\<noteq>[] \<Longrightarrow> ?P (B,C) \<Longrightarrow> ?P (step_fun_L Bs (B,C))"
    by (smt (verit) Transitive_Closure.rtranclp.simps case_prodI2 case_prod_conv fst_conv step_fun_L_sound step_fun_L_wf)
  thus ?thesis using while_option_rule[where P = ?P, OF _ assms(3)[unfolded steps_L.simps]] assms(1,2)
    while_option_stop[OF assms(3)[unfolded steps_L.simps]]
    by auto
qed

lemma steps_L_Th_sound1: assumes  "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "steps_L Bs (B,C) = Some ([],C')"
  shows "(Close2_L Bs)^** (B,C) ([],C')"
proof -
  let ?P = "\<lambda>(B',C'). (Close2_L Bs)^** (B,C) (B',C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)"
  have "\<And>B C. B\<noteq>[] \<Longrightarrow> ?P (B,C) \<Longrightarrow> ?P (step_fun_L Bs (B,C))"
    by (smt (verit) Transitive_Closure.rtranclp.simps case_prodI2 case_prod_conv fst_conv step_fun_L_sound step_fun_L_wf)
  thus ?thesis using while_option_rule[where P = ?P, OF _ assms(3)[unfolded steps_L.simps]] assms(1,2)
    while_option_stop[OF assms(3)[unfolded steps_L.simps]]
    by auto
qed

lemma test_Th5: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "steps_L Bs (B,C) = Some (B',C')"
  shows "(Close2 (map set Bs))^** (set B,set C) ({},set C')"
proof-
  let ?P = "\<lambda>(B',C'). (Close2 (map set Bs))^** (set B,set C) (set B',set C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)"
  have "\<And>B C. B\<noteq>[] \<Longrightarrow> ?P (B,C) \<Longrightarrow> ?P (step_fun_L Bs (B,C))"
    by (smt (verit) Transitive_Closure.rtranclp.simps case_prodI2 case_prod_conv fst_conv test_Th4 step_fun_L_wf)
  thus ?thesis using while_option_rule[where P = ?P, OF _ assms(3)[unfolded steps_L.simps]] assms(1,2)
    while_option_stop[OF assms(3)[unfolded steps_L.simps]]
    by auto
qed
  


definition Close2_L_Th_less :: "nat \<Rightarrow> ((('n,'a) item list \<times> ('n,'a) item list) \<times> (('n,'a) item list \<times> ('n,'a) item list)) set" where
"Close2_L_Th_less k = (\<lambda>(B,C). card({x. wf_item x k} - (set B \<union> set C))) <*mlex*> inv_image finite_psubset (set o fst)"

lemma wf_Close2_L_Th_less: "wf (Close2_L_Th_less k)"
by (simp add: Close2_L_Th_less_def wf_mlex) 

lemma Th_test1: assumes "B \<noteq> []" "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "wf_bin1 (set C) (length Bs)"
  shows "\<exists>B' C'. step_fun_L Bs (B,C) = (B',C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bin1 (set C') (length Bs)"
proof-
  from assms obtain b bs where P: "B = b#bs"
    using local.recognized_L.cases by blast
  let ?nexts = "if is_complete b then Complete_L Bs b else Predict_L b (length Bs)"
  let ?B = "diff_list (union_list ?nexts (b#bs)) (insert_list b C)"
  let ?C = "insert_list b C"
  have 1: "step_fun_L Bs (B,C) = (?B, ?C)" using P by simp
  moreover have "wf_bin1 (set ?B) (length Bs)" using step_fun_L_wf[of B Bs C] assms by (simp add: 1)
  moreover have "wf_bin1 (set ?C) (length Bs)" using step_fun_L_wf1[of B Bs C] assms by (simp add: 1)
  ultimately show ?thesis by auto
qed

lemma Th_test3: "((A, B), (C,D)) \<in> Close2_L_Th_less k \<longleftrightarrow> ((set A, set B), (set C, set D)) \<in> Close2_less k"
  by (simp add: Close2_L_Th_less_def Close2_less_def mlex_prod_def)

lemma Th_test2: assumes "B\<noteq>[]" "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "wf_bin1 (set C) (length Bs)"  "(B',C') = step_fun_L Bs (B,C)" 
  shows "((B',C'), (B,C)) \<in> Close2_L_Th_less (length Bs)"
proof-
  have "Close2 (map set Bs) (set B, set C) (set B', set C')"
    using step_fun_L_sound assms
    by simp
  then show ?thesis using assms Close2_less_step Th_test3 by (metis length_map)
qed

theorem Close2_L_Th_NF: "\<lbrakk>wf_bins1 (map set Bs); wf_bin1 (set B) (length Bs); wf_bin1 (set C) (length Bs)\<rbrakk>
  \<Longrightarrow> \<exists>B' C'. steps_L Bs (B,C) = Some (B',C')"
using wf_Close2_L_Th_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume ne: "B = []"
    thus ?thesis using while_option_unfold[of _ _ "(B,C)"] by(simp add: )
  next
    let ?steps = "while_option (\<lambda>(B, C). B \<noteq> []) (step_fun_L Bs)"
    assume cons: "B \<noteq> []"
    then obtain B' C'
      where "(B',C') = step_fun_L Bs (B,C)" and wf': "wf_bin1 (set B') (length Bs)" "wf_bin1 (set C') (length Bs)"
      using Th_test1[OF cons less.prems(1,2,3)] by fastforce
    then have "((B',C'), (B, C)) \<in> Close2_L_Th_less (length Bs)"
      using cons less.prems Th_test2 by auto
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf']
    show ?thesis
      by (simp add: \<open>(B',C') = step_fun_L Bs (B,C)\<close> while_option_unfold)
  qed
qed

corollary steps_L_Th_NF: "\<lbrakk>wf_bins1 (map set Bs); wf_bin1 (set B) (length Bs); wf_bin1 (set C) (length Bs)\<rbrakk>
  \<Longrightarrow> \<exists>C'. steps_L Bs (B,C) = Some ([],C')"
  using Close2_L_Th_NF while_option_stop by fastforce

lemma close2_L_Th_eq_close2: 
  assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)"
    shows "set (close2_L_Th Bs B) = close2 (map set Bs) (set B)"
proof-
  have "wf_bin1 (set []) (length Bs)" by (auto simp add: wf_bin1_def)
  then obtain B' C' where P: "steps_L Bs (B,[]) = Some (B', C')" using Close2_L_Th_NF assms by blast

  then have "(Close2 (map set Bs))^** (set B, {}) ({}, set C')" 
    using P test_Th5[of Bs B "[]" B' C', unfolded Close2_L.simps] assms by simp
  then have "set C' = Close1 (map set Bs) (set B)"
    by (simp add: Close1_subset_Close2 Close2_steps_subset_Close1' subset_antisym close2_L_Th_def )
  then have "set (close2_L_Th Bs B) = Close1 (map set Bs) (set B)"
    using P by (simp add: close2_L_Th_def)

  then show ?thesis
    by (simp add: assms(1,2) close2_eq_Close1) 
qed

lemma close2_L_Th_eq_Close1: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> set (close2_L_Th Bs B) = Close1 (map set Bs) (set B)"
  using close2_L_Th_eq_close2 close2_eq_Close1 by auto

lemma test_th_6: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> wf_bin1 (set (close2_L_Th Bs B)) (length Bs)"
  by (metis close2_L_Th_eq_Close1 length_map wf_bin1_def wf_item1_Close1)


lemma bins_L_Th_Suc[simp]: "length (bins_L_Th k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma bins_L_Th_eq_bins: "k \<le> length w \<Longrightarrow> map set (bins_L_Th k) = bins k"
proof(induction k)
  case 0
  have "wf_bin1 (set Init_L) 0" using Init_L_eq_Init
    by (simp add: wf_bin1_Init)
  then have "wf_bins1 (map set (bins_L_Th 0))" using "0" test_th_6[of "[]" "Init_L"] by (auto simp add: wf_bins1_def)
  then show ?case using 0 close2_L_Th_eq_Close1 Close1_eq_Close Init_L_eq_Init wf_bin1_Init wf_bins1_def by auto
next
  case (Suc k)
  have 2: "bins k \<noteq> []"
    by (simp add: bins_nonempty)
  have 1: "bins_L_Th k \<noteq> []" using bins_L_Th_Suc
    by (metis Zero_not_Suc length_0_conv)
  have "wf_bins1 (bins k)" using Suc
    using Suc_leD wf_bins1_bins by blast
  then have 3: "wf_bins1 (map set (bins_L_Th k))" using Suc by auto
  then have "wf_bin1 (set (Scan_L (last (bins_L_Th k)) k)) (length (bins_L_Th k))"
    using 1 wf_bin1_Scan Scan_L_eq_Scan Suc wf_bins1_def by (auto simp add: last_conv_nth simp flip: nth_map[of _ _ set])
  then show ?case using 1 2 close2_L_Th_eq_Close1[of "bins_L_Th k" "Scan_L (last (bins_L_Th k)) k"] Close1_eq_Close Suc 3 Scan_L_eq_Scan
     by (auto simp add: Let_def last_conv_nth simp flip: nth_map[of _ _ set])
 qed

lemma earley_correctness_Th: "earley_recognized1 \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using correctness_earley by (simp add: earley_recognized1_def)
end


context Earley_Gw_eps begin

(*(if (\<exists> i t. (i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i) 
    then Some ( Rule S (rev (SOME t. \<exists>i. (i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i))) else None)"*)

lemma fst_image: "x \<in> image fst Y \<Longrightarrow> \<exists>y. (x,y) \<in> Y"
  by auto

lemma get_parse_tree3_iff: "(\<exists>t. get_parse_tree3 = Some t) \<longleftrightarrow> (P \<turnstile> [Nt S] \<Rightarrow>* w)"
proof
  assume "\<exists>t. get_parse_tree3 = Some t"
  then obtain i t where "(i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i"
    using get_parse_tree3_def
    by fastforce
  then have "i \<in> last (map ((`) item) (Parse_bins (length w))) \<and> is_final i"
    by (metis (no_types, lifting) List.list.map_disc_iff bins_nonempty fst_conv image_eqI item_Pbins_eq_bins last_map nat_le_linear)
  then have "i \<in> last (bins (length w)) \<and> is_final i"
    using item_Pbins_eq_bins[of "length w"] by auto
  then have "i \<in> \<S> (length w) \<and> is_final i" using bins_eq_\<S> last_conv_nth length_bins
    by (metis Earley.Earley_Gw.bins_nonempty diff_add_inverse2 le_refl)
  then show "P \<turnstile> [Nt S] \<Rightarrow>* w"
    using accepted_def accpted_sound by auto
next
  assume "P \<turnstile> [Nt S] \<Rightarrow>* w"
  then obtain i where 1: "i \<in> \<S> (length w) \<and> is_final i"
    using accepted_def Earley_complete_Th by blast
  then have "i \<in> last (bins (length w)) \<and> is_final i"
    using bins_eq_\<S> last_conv_nth length_bins by (metis Earley.Earley_Gw.bins_nonempty diff_add_inverse2 le_refl)
  then have "i \<in> last (map ((`) item) (Parse_bins (length w))) \<and> is_final i"
    using item_Pbins_eq_bins[of "length w"] by auto
  then have "i \<in> item ` last (Parse_bins (length w))" using last_map length_parse_bins
    by (metis Earley.Earley_Gw.bins_nonempty EarleyWorklist.Earley_Gw_eps.item_Pbins_eq_bins Earley_Gw_eps_axioms List.list.simps(8)
        le_refl)
  then have "\<exists>t. (i,t) \<in> (last (Parse_bins (length w)))" using fst_image by auto
  then obtain t where "(i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i" using 1 by blast
  then show "\<exists>t. get_parse_tree3 = Some t"
    by (auto simp add: get_parse_tree3_def)
qed

lemma someI2_bex_Th: "\<exists>a b. (a,b)\<in>A \<and> T a \<Longrightarrow> (\<And>a b. (a,b) \<in> A \<and> T a \<Longrightarrow> Q b) \<Longrightarrow> Q (SOME b. \<exists>a. (a,b) \<in> A \<and> T a)"
  by (smt (verit) exE_some)

  

lemma test_Pt: "(s, ts) \<in> last (Parse_bins (length (w ))) \<and> is_final s \<Longrightarrow> valid_parse_tree P w S (Rule S (rev ts))"
proof-
  assume assm: "(s, ts) \<in> last (Parse_bins (length (w ))) \<and> is_final s"
  moreover have "Parse_bins (length w) \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_parse_bins)
  ultimately have "wf_parseItem1 (s, ts) (length w)" using parse_bins_wf1 length_parse_bins
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_parseItem1.simps)
  then show "valid_parse_tree P w S (Rule S (rev ts))" using assm 
    by (auto simp add: valid_parse_tree_def is_final_def wf_item1_def wf_item_def \<alpha>_def rhs_def is_complete_def)
qed

lemma get_parse_tree3_valid: "get_parse_tree3 = Some t \<Longrightarrow> valid_parse_tree P w S t"
proof (cases "\<exists>i ts. (i, ts) \<in> last (Parse_bins (length (w ))) \<and> is_final i")
  case True
  assume "get_parse_tree3 = Some t"

  moreover have "valid_parse_tree P w S (Rule S (rev (SOME t. \<exists>i. (i, t) \<in> last (Parse_bins (length w)) \<and> is_final i)))"
    using someI2_bex_Th[OF True test_Pt] test_Pt True by auto
  ultimately show ?thesis by (auto simp add: get_parse_tree3_def split: if_splits)
next
  case False
  assume assm: "get_parse_tree3 = Some t"
  have "get_parse_tree3 = None" using False by (auto simp add: get_parse_tree3_def)
  then show ?thesis using assm by (auto simp add: get_parse_tree3_def)
qed

lemma unambiguous_impl_P_set_eq_P_L: "G = Cfg P S \<Longrightarrow> unambiguous G \<Longrightarrow> get_parse_tree3 = parse_tree_w"
proof (cases "P \<turnstile> [Nt S] \<Rightarrow>* w")
  case True
  assume assms: "G = Cfg P S" "unambiguous G"
  obtain t1 where "get_parse_tree3 = Some t1" using True get_parse_tree3_iff by auto
  moreover then have "valid_parse_tree P w S t1" using get_parse_tree3_valid by auto
  moreover obtain t2 where "parse_tree_w = Some t2" using find_parse_tree_iff_w_in_L True w_def Lang_def
    using Earley_complete_Th accepted_implies_Some_tree by blast
  ultimately show ?thesis using assms
    using unambiguous_impl_the_parse_tree by auto
next
  case False
  then have "get_parse_tree3 = None" using get_parse_tree3_iff
    by simp
  moreover have "parse_tree_w = None" using find_parse_tree_iff_w_in_L w_def False Lang_def
    by (metis Option.option.exhaust mem_Collect_eq)
  ultimately show ?thesis by simp
qed


(*lemma "get_parse_tree3 = (get_parse_tree (last (Parse_bins_L (length w))))"*)

lemma step_fun_sound_il: "list il1 \<noteq> [] \<Longrightarrow> wf1_IL il1 (length Bs) \<Longrightarrow> wf_bins1 (map set Bs) \<Longrightarrow> inv_IL il1 \<Longrightarrow> inv_IL il2
  \<Longrightarrow> length (froms il1) = Suc (length Bs) \<Longrightarrow> length (froms il2) = Suc (length Bs)
 \<Longrightarrow> step_fun Bs (il1,il2) = (il1', il2')
 \<Longrightarrow> step_rel (map set Bs) (set_ItemList il1,set_ItemList il2) (set_ItemList il1', set_ItemList il2')"
  using il_decomp step_fun_sound
  by (metis (no_types, lifting) EarleyWorklist.efficientItemList.collapse local.set_ItemList.elims)

lemma steps_sound_il: "wf1_IL il1 (length Bs) \<Longrightarrow> wf_bins1 (map set Bs) \<Longrightarrow> length (froms il1) = Suc (length Bs) \<Longrightarrow> length (froms il2) = Suc (length Bs)
  \<Longrightarrow> inv_IL il1 \<Longrightarrow> inv_IL il2 \<Longrightarrow> steps Bs (il1, il2) = Some (il1', il2') 
  \<Longrightarrow> (step_rel (map set Bs))^** (set_ItemList il1, set_ItemList il2) ({}, set_ItemList il2')"
  using il_decomp steps_sound by (metis (no_types, lifting) EarleyWorklist.efficientItemList.collapse local.set_ItemList.elims)

lemma correctness_earley_Th:
  shows "earley_recognized_Th \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using correctness_earley unfolding earley_recognized_Th_def by blast

definition get_parse_tree_w where "get_parse_tree_w = parse_tree_w"

lemma get_parse_tree_Th: "(\<exists>t. get_parse_tree_w = Some t) \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using find_parse_tree_iff_w_in_L by (auto simp add: Lang_def w_def get_parse_tree_w_def)

lemma get_parse_tree_valid_Th: "get_parse_tree_w = Some t \<longrightarrow> valid_parse_tree P w S t"
  by (auto simp add: generated_parse_tree_is_valid get_parse_tree_w_def)
end

context Earley_Gw_eps_T begin
lemma T_minus_IL_wf_Th: 
  assumes "wf1_IL il1 (length (froms il1) - 1)" "inv_IL il1" "inv_IL il2" "wf1_IL il2 (length (froms il1) - 1)"
   "length (froms il2) \<ge> length (froms il1)"
 shows "T_minus_IL il1 il2 \<le> (length (list il1)) * (4 * T_nth_IL (length (froms il1) - 1) + 2*L * (Suc K) + 5)
    + mbox0 (2 * length (froms il1) + 3)"
  using T_minus_IL_wf[OF assms] by (auto simp add: algebra_simps mbox0_def)

definition T_step_fun_bound_Th_def :: "nat" where "T_step_fun_bound_Th_def = 0"

notation T_step_fun_bound_Th_def (\<open>\<^latex>\<open>\isaconst{\<close>T'_step'_fun'_bound\<^latex>\<open>}\<close>\<close>)

lemma T_close2_L_bound_Th_nice: 
  assumes "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)"  "wf1_IL il (length Bs)" "inv_IL il" "length (froms il) = Suc (length Bs)"
  shows "T_close2_L Bs il \<le> (L * Suc K * Suc (length Bs))^2 * (7 * T_nth_IL (length Bs) + 3 * (Suc L) * Suc K + 11)
  +  L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 2 * (Suc L) * Suc K + 7)
  + 2 * Suc (length Bs)"
proof-
  have 1: "L * Suc K * Suc (length Bs) * 3 * Suc (length Bs) \<le> L * Suc K * Suc (length Bs) * L * Suc K * Suc (length Bs) * 3"
    by (cases L) (auto simp add: algebra_simps)
  have "T_close2_L Bs il \<le> 
      (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) 
      + 7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K) + 2 * Suc (length Bs)"
    using T_close2_L_bound assms by simp
  also have "... \<le> L * Suc K * Suc (length Bs) * L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 10 + 2 * (K + 2))
                  + L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 2 * L * Suc K + 7 + Suc K)
                  + 2 * Suc (length Bs)"
    using 1 by (auto simp add: algebra_simps)
  also have "... = (L * Suc K * Suc (length Bs))^2 * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 10 + 2 * (K + 2))
  +  L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 2 * L * Suc K + 7 + Suc K)
  + 2 * Suc (length Bs)" by (simp only: monoid_mult_class.power2_eq_square)
  also have "... \<le> (L * Suc K * Suc (length Bs))^2 * (7 * T_nth_IL (length Bs) + 3 * (Suc L) * Suc K + 11)
  +  L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 2 * (Suc L) * Suc K + 7)
  + 2 * Suc (length Bs)" by (auto simp add: algebra_simps)
  finally show ?thesis.
qed

definition c1 where "c1 = 3 * (Suc L) * Suc K + 11"
definition c2 where "c2 = 2 * (Suc L) * Suc K + 7"

lemma T_close2_L_bound_Th_nice_short:
assumes "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)"  "wf1_IL il (length Bs)" "inv_IL il" "length (froms il) = Suc (length Bs)"
  shows "T_close2_L Bs il \<le> (L * Suc K * Suc (length Bs))^2 * (7 * T_nth_IL (length Bs) + c1)
  +  L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + c2)
  + 2 * Suc (length Bs)"
  using T_close2_L_bound_Th_nice[OF assms] by (auto simp add: c1_def c2_def algebra_simps)

lemma T_Parse_bins_bound_nice_Th: 
  assumes "k \<le> length w"
  shows "T_Parse_bins_L k 
      \<le> mbox0 ((k+2)^3 * C3 + (k+2)^2 * C4 + (k+2) * 3 + C5) 
        + mbox0 ((k+2)^3 * T_nth_IL (k) * C6 + (k+2)^2 * T_nth_IL (k) * C7)"
  using T_Parse_bins_bound_nice assms by (auto simp add: mbox0_def algebra_simps)

lemma T_ovrall_time_bound_Th: "T_get_parse_tree_w ps S w0 \<le>  
  mbox0 ((length w + 2)^3 * C3 + (length w + 2)^2 * C4 + (length w + 2) * C8 + C5 )
        + mbox0 ((length w + 2)^3 * T_nth_IL (length w) * C6 + (length w + 2)^2 * T_nth_IL (length w) * C7)"
  using T_ovrall_time_bound by (auto simp add: mbox0_def algebra_simps)
end



definition a_very_long_name_that_isnt_used_anywhere_else_qs where "a_very_long_name_that_isnt_used_anywhere_else_qs = [((0::nat), [Nt (0),Nt (1)]), (0, [Nt 1, Nt 0]), (0,[Tm ((0::nat))]), (1,[Tm (1)])]"
definition a_very_long_name_that_isnt_used_anywhere_else_s where "a_very_long_name_that_isnt_used_anywhere_else_s = 0"
definition a_very_long_name_that_isnt_used_anywhere_else_w1 where "a_very_long_name_that_isnt_used_anywhere_else_w1 = [0,1,0]"

global_interpretation Earley_Gw_eps 
  where ps = a_very_long_name_that_isnt_used_anywhere_else_qs 
    and S = a_very_long_name_that_isnt_used_anywhere_else_s 
    and w0 = a_very_long_name_that_isnt_used_anywhere_else_w1
proof
  show "eps_free a_very_long_name_that_isnt_used_anywhere_else_qs" 
    by (auto simp add: a_very_long_name_that_isnt_used_anywhere_else_qs_def Eps_free_def)
qed

value "bins_L 0"
(*P definition outside of Earley_Gw for certain uses*)
(*definition P where " P = {(1 :: nat, ([] :: (nat, 'b) sym list))}"*)

(*notation (latex) X ("(\<S>\<^bsub>\<^latex>\<open>\\isaconst{\<close>_\<^latex>\<open>}\<close>\<^esub>)" [0] 0)*)
(*abbreviation \<epsilon> where "\<epsilon> \<equiv> ([] :: 't list)"*)


translations (type) "('n, 'a) Prods" <= (type) "('n \<times> ('n1, 'a) sym list) set"
translations (type) "('n, 'a) prods" <= (type) "('n \<times> ('n1, 'a) sym list) list"

hide_const (open) \<alpha>
(*>*)

(*<*)
context Earley_Gw
begin

notation diff_list (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation union_list (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation insert_list (\<open>{_} \<union>\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub> _\<close> 65)
notation Close2_L (\<open>\<^latex>\<open>\isaconst{\<close>Close2\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation step_fun_L (\<open>\<^latex>\<open>\isaconst{\<close>step'_fun\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation steps_L (\<open>\<^latex>\<open>\isaconst{\<close>steps\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation steps_L2 (\<open>\<^latex>\<open>\isaconst{\<close>steps\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation steps_L3 (\<open>\<^latex>\<open>\isaconst{\<close>steps\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation Init_L (\<open>\<^latex>\<open>\isaconst{\<close>Init\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Predict_L (\<open>\<^latex>\<open>\isaconst{\<close>Predict\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Complete_L (\<open>\<^latex>\<open>\isaconst{\<close>Complete\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Scan_L (\<open>\<^latex>\<open>\isaconst{\<close>Scan\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation ItemList ("\<^latex>\<open>\\isaconst{\<close>IL\<^latex>\<open>}\<close>")

notation set_ItemList (\<open>\<^latex>\<open>\isaconst{\<close>set\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation empty_IL (\<open>\<^latex>\<open>\isaconst{\<close>empty\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation insert  (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation isin (\<open>\<^latex>\<open>\isaconst{\<close>isin\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation union_LIL (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\small \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation minus_LIL ("\<^latex>\<open>\\isaconst{\<close>diff\<^bsub>\<^latex>\<open>\\isaconst{\\myscriptsize \<close>LIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation minus_IL (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation minus_LIL_Th ("\<^latex>\<open>\\isaconst{\<close>diff\<^bsub>\<^latex>\<open>\\isaconst{\\myscriptsize \<close>LIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation inv_IL ("\<^latex>\<open>\\isaconst{\<close>inv\<^bsub>\<^latex>\<open>\\isaconst{\\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation inv_IL_display ("\<^latex>\<open>\\isaconst{\<close>inv\<^bsub>\<^latex>\<open>\\isaconst{\\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation wf1_IL ("\<^latex>\<open>\\isaconst{\<close>wf1\<^bsub>\<^latex>\<open>\\isaconst{\\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation step_fun (\<open>\<^latex>\<open>\isaconst{\<close>step'_fun\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation steps (\<open>\<^latex>\<open>\isaconst{\<close>steps\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation close2_L (\<open>\<^latex>\<open>\isaconst{\<close>close2\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation bins_L (\<open>\<^latex>\<open>\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation earley_recognized1 (\<open>\<^latex>\<open>\isaconst{\<close>accepted\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation Parse_Init (\<open>\<^latex>\<open>\isaconst{\<close>Init\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_Predict (\<open>\<^latex>\<open>\isaconst{\<close>Predict\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_Complete (\<open>\<^latex>\<open>\isaconst{\<close>Complete\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_Scan (\<open>\<^latex>\<open>\isaconst{\<close>Scan\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation Parse_Close (\<open>\<^latex>\<open>\isaconst{\<close>Close\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_bins (\<open>\<^latex>\<open>\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation inv_PIL (\<open>\<^latex>\<open>\isaconst{\<close>inv\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation set_PIL (\<open>\<^latex>\<open>\isaconst{\<close>set\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation wf_PIL (\<open>\<^latex>\<open>\isaconst{\<close>wf\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation isin_PIL (\<open>\<^latex>\<open>\isaconst{\<close>isin\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation insert_PIL  (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation hd_PIL (\<open>\<^latex>\<open>\isaconst{\<close>hd\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_bins_L (\<open>\<^latex>\<open>\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
end

context Earley_Gw_eps_T
begin
notation T_nth_IL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>nth\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_step_fun (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>step'_fun\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_steps (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>steps\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_close2_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>close2\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_bins_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>bins\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_earley_recognized1 (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>accepted\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_Init_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>Init\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_Predict_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>Predict\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_Complete_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>Complete\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_Scan_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>Scan\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_empty_IL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>empty\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_isin (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>isin\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_insert (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>#\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_union_LIL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>\<union>\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_minus_IL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>-\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_minus_LIL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>diff\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>LIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_nth (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>nth\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_list_update (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>list'_update\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_get_parse_tree_w (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\myscriptsize \<close>get'_parse'_tree'_w\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
end

section presentation
(*>*)

text (in Earley_Gw)\<open>
\begin{frame}
  \frametitle{Basic Notation}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \vspace{8mm}

    \mytext{Nts:} \<open>A, B, C \<close>\hspace{5mm} \mytext{Tms:} \<open>a, b, c\<close> \hspace{5mm} \mytext{Sententials:} \<open>\<alpha>, \<beta>\<close>\\
    \mytext{Derivations:} @{term "P"} \<open>\<turnstile> \<alpha> \<Rightarrow>* \<beta>\<close>\\
    \mytext{Productions:} \<open>A \<rightarrow> \<alpha>\<close>\\
    \mytext{Fixed constants:}\vspace{-4mm}
      \begin{itemize}
        \item \mytext{input word} $w = w_0 \dots w_{n-1}$
        \item \mytext{start Symbol:} \<open>S\<close>
        \item \mytext{set of Productions:} @{term "P"}
      \end{itemize}
    \mytext{Notation is mostly informal and lemmas and theorems are sometimes simplified by dropping assumptions about invariants or well-formedness, we drop explicit conversion from lists to sets}
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw)\<open>
\begin{frame}
  \frametitle{Earley Recognizer}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \vspace{8mm}

  
  \mytext{Compute item sets (bins) \<open>\<S>\<close>, Items consisting of a dotted production and a "}\emph{from}\mytext{" index indicating a previous bin (}\<open>A \<rightarrow> \<alpha>\<Zspot>\<beta>,\<close> \emph{from}\mytext{).}\\

  \mytext{Specification:} \<open>(A \<rightarrow> \<alpha>\<Zspot>\<beta>, k) \<in>\<close> @{term "\<S> i"} \<open>\<Longrightarrow>\<close> @{term "P"} \<open>\<turnstile> \<alpha> \<Rightarrow>*\<close> $w_{\text{\myscriptsize\itshape k}} \dots w_{{\text{\myscriptsize\itshape i}}-1}$
  
  \usebeamerfont{normal}
  {\sc Init}: \inferrule{\text{\<open>S \<rightarrow> \<alpha> \<in>\<close> @{term "P"}}
  }{\text{\<open>(S \<rightarrow> \<Zspot>\<alpha>, 0) \<in>\<close> @{term "\<S> 0"}}}
  \hspace{10mm}
  {\sc Predict}: \inferrule{\text{\<open>(A \<rightarrow> \<alpha>\<Zspot>B\<gamma>,  k) \<in>\<close> @{term "\<S> i"}}\\
    \text{\<open>B \<rightarrow> \<beta> \<in>\<close> @{term "P"}}}{\text{\<open>(B \<rightarrow> \<Zspot>\<beta>, i) \<in>\<close> @{term "\<S> i"}}}\\\vspace{4mm}

  {\sc Complete}: \inferrule{\text{\<open>(A \<rightarrow> \<alpha>\<Zspot>, k) \<in>\<close> @{term "\<S> i"}}\\
  \text{\<open>(B \<rightarrow> \<beta>\<Zspot>A\<gamma>, l) \<in>\<close> @{term "\<S> k"}}
  }{\text{\<open>(B \<rightarrow> \<beta>A\<Zspot>\<gamma>, l) \<in>\<close> @{term "\<S> i"}}}\\\vspace{4mm}

  {\sc Scan}: \inferrule{\text{\<open>(A \<rightarrow> \<alpha>\<Zspot>b\<beta>, l) \<in>\<close> @{term "\<S> i"}}\\
  \text{$w_{\text{\myscriptsize\itshape i}} = \text{\<open>b\<close>}$}
  }{\text{\<open>(A \<rightarrow> \<alpha>b\<Zspot>\<beta>, l) \<in>\<close> @{term "\<S> (i+1)"}}}

\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text  \<open>
\begin{frame}[plain, noframenumbering]
  \frametitle{\ }
  \vspace{30mm}
  \centering
  {\fontfamily{\familydefault}\fontsize{60}{60}\selectfont\upshape Prior Work}
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps) \<open>
\begin{frame}
  \frametitle{Prior Work}
  \vspace{8mm}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
   
  \mytext{Purely inductive definition of Earley recognizer for correctness proofs.}
  \begin{mydefinition}\vspace{1mm}
    @{const accepted} \<open>= (S \<rightarrow> \<alpha>\<Zspot>, 0) \<in>\<close> @{term "\<S> (length w)"}
  \end{mydefinition}
  \vspace{8mm}
  \begin{mylemma}\vspace{-3.5mm}
    @{const accepted} \<open>\<longleftrightarrow>\<close> @{term "P"} \<open>\<turnstile> S \<Rightarrow>*\<close> \usebeamerfont{big}$w$
  \end{mylemma}\vspace{-2mm}

  \mytext{Recursive computation of bins:\\
  Init and Scan compute starting set, which is then closed under Predict and Complete (using @{const Close})}
  \vspace{8mm}
  \begin{mylemma}\vspace{1mm}@{thm bins_eq_\<S>}\end{mylemma}
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
(*text (in Earley_Gw_eps) \<open>
\begin{frame}
  \frametitle{Prior Work}
  \vspace{8mm}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}

  @{const Close2} \<open>::\<close> @{typeof "x :: ('n,'a) item set list"} \<open>\<Rightarrow>\<close> @{typeof "x :: ('n,'a) item set \<times> ('n,'a) item set"}\\
  \hspace{5mm}\<open>\<Rightarrow>\<close> @{typeof "x :: ('n,'a) item set \<times> ('n,'a) item set"} \<open>\<Rightarrow>\<close> @{typeof "x :: bool"}\\
  @{thm Close2.Predict}\\
  @{thm Close2.Complete}\\
  \vspace{8mm}
  @{def close2}\\
  \vspace{16mm}
  \begin{mylemma}\vspace{1mm}@{thm close2_eq_Close}\end{mylemma}
\end{frame}
\clearpage
\<close>*)
(*------------------------------------------------------------------------------------------------*)
(*text (in Earley_Gw_eps) \<open>
\begin{frame}
  \frametitle{Prior Work}
  \vspace{8mm}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  {\fontfamily{\familydefault}\selectfont\upshape
  They formalize a one-pass workset algorithm for the closure using workset \<open>B\<close> and accumulator \<open>C\<close>. Each step:\vspace{-2mm}
  \begin{itemize}
    \item choose an item from \<open>B\<close> to be considered \<open>b \<in> B\<close>
    \item compute the set of items \<open>D\<close> added by \<open>b\<close> under \emph{Predict} or \emph{Complete}
    \item move \<open>b\<close> from \<open>B\<close> to \<open>C\<close> and add \<open>D\<close> to \<open>B\<close>, while making sure that \mbox{\<open>B \<inter> C = \<emptyset>\<close>} by the end 
  \end{itemize}\vspace{-2mm}
  The @{const Close2} relation captures transitions between states.
  Taking the accumulator from the transitive closure of @{const Close2}, where the workset is empty then gives the closed set.\\}\vspace{4mm}
  @{thm close2_def}\\
  \vspace{16mm}
  \begin{mylemma}\vspace{1mm}@{thm close2_eq_Close}\end{mylemma}
\end{frame}
\clearpage
\<close>*)
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps) \<open>
\begin{frame}
  \frametitle{Prior Work}
  \vspace{8mm}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{11}{17}\selectfont}
  
  \mytext{Refinement of closure in @{const Close2}, an inductively defined one-pass workset algorithm.}\\
  \mytext{Notation:} \<open>Bs:\<close> \mytext{list of bins,} \<open>B:\<close> \mytext{workset,} \<open>C:\<close> \mytext{result,} \<open>(B', C'):\<close> \mytext{next state}\\\vspace{12mm}
  \begin{mydefinition}\vspace{1mm}
  @{const Close2}\mytext{:} \<open>Bs \<turnstile> (B,C) \<rightarrow> (B', C')\<close>\\\vspace{2mm}
  @{thm (prem 1) Close2_Predict_Th} \<open>\<and>\<close> @{thm (prem 2) Close2_Predict_Th} \<open>\<Longrightarrow>\<close> @{thm (concl) Close2_Predict_Th}\\\vspace{2mm}
  @{thm (prem 1) Close2.Complete} \<open>\<and>\<close> @{thm (prem 2) Close2.Complete} \<open>\<Longrightarrow>\<close> @{thm (concl) Close2.Complete}
  \end{mydefinition}
  \mytext{Pick the result of the workset algorithm for a starting wrokset} \<open>B\<close>\\
  @{thm close2_def}\\
  \vspace{16mm}
  \begin{mylemma}\vspace{1mm}
    @{thm (prem 1) close2_eq_Close} \<open>\<and>\<close> @{thm (prem 2) close2_eq_Close} \<open>\<Longrightarrow>\<close> @{thm (concl) close2_eq_Close}
  \end{mylemma}
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text  \<open>
\begin{frame}[plain, noframenumbering]
  \frametitle{\ }
  \vspace{30mm}
  \centering
  {\fontfamily{\familydefault}\fontsize{60}{60}\selectfont\upshape Own Work}
\end{frame}
\clearpage
\<close>
text (in Earley_Gw)\<open>
\begin{frame}
  \frametitle{List Recognizer}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{11}{17}\selectfont}
  \vspace{8mm}
  {\fontfamily{\familydefault}\selectfont\upshape
  Towards executability we implement the Earley operations on Lists, using filtering and mapping.\vspace{-4mm}
  \begin{itemize}
    \item @{const Init_L} and @{const Predict_L} filter the productions for a specific Nt
    \item @{const Scan_L} filters a bin for items with a Tm after the dot
    \item @{const Complete_L} filters a previous bin for items with a specific Nt after the dot
  \end{itemize}\vspace{-4mm}
  We implement the closure, where each step emulates the @{const Close2} steps\\
  }\vspace{12mm}
  \begin{mydefinition}\vspace{-6mm}
  @{thm[display] step_fun_L.simps}\vspace{4mm}
  @{thm steps_L2.simps}
  \end{mydefinition}
\end{frame}
\clearpage\<close>
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps)\<open>
\begin{frame}
  \frametitle{List Recognizer}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{8mm}
  \mytext{We prove termination of @{const steps_L} and equivalence to @{const close2}}\\\vspace{16mm}
  \begin{mylemma}\vspace{2mm}
    \<open>\<exists> C'.\<close> @{const steps_L} \<open>Bs (B, C) = ([], C')\<close>\\\vspace{4mm}
    @{const steps_L} \<open>Bs (B, C) = ([], C')\<close> \<open>\<Longrightarrow>\<close> @{thm (concl) steps_L_Th_sound1}
  \end{mylemma}

  \mytext{@{const bins} using this closure is fully executable.\\\vspace{4mm}
    The running time is dominated by the list difference operation which is executed each step.}
  %\mytext{Replacing the closure algorithm in @{const bins} with this executable version gives us a fully executable recognizer.\\
  %The running time is dominated by the list difference operation which is executed each step.}
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text \<open>
\begin{frame}
  \frametitle{Efficient Item List Data Structure}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{8mm}

  \mytext{Earley proposes data structure using an array to achieve cubic running time\\\vspace{4mm}
    We stay purely functional and do a parameterized running time analysis instead.\\\vspace{4mm}

    Partition bin by the "from" index of items -> each part has constant size:}

    \<open>[(A \<rightarrow> a\<Zspot>bc, 0), (A \<rightarrow> B\<Zspot>A, 2), (B \<rightarrow> b\<Zspot>, 1), (A \<rightarrow> \<Zspot>abc, 2), (A \<rightarrow> a\<Zspot>a, 0)]\<close>\\
    
    \<open>[ [(A \<rightarrow> a\<Zspot>bc, 0), (A \<rightarrow> a\<Zspot>a, 0)],\<close>\\
    \hspace{4.38mm}\<open>  [(B \<rightarrow> b\<Zspot>, 1)],\<close>\\
    \hspace{4.38mm}\<open>  [(A \<rightarrow> B\<Zspot>A, 2), (A \<rightarrow> \<Zspot>abc, 2)] ]\<close>
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
(*text \<open>
\begin{frame}
  \frametitle{Efficient Item List Data Structure}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{8mm}
  {\fontfamily{\familydefault}\selectfont\upshape
    Bound the number of items per bin, each item consists of:\vspace{-4mm}
    \begin{itemize}
      \item a production p (bound by @{term "card P = L"})
      \item an index into its rhs (bound by $\max\limits_{p \in P}$ @{term "length (rhs p) = K"} )
      \item an index into a previous/current bin (bound by bin index)
    \end{itemize}\vspace{-4mm}
    So in a bin there are a constant number of items with a specific from-value and we can partition it:}\\
    \<open>[(A \<rightarrow> a\<Zspot>bc, 0), (A \<rightarrow> B\<Zspot>A, 2), (B \<rightarrow> b\<Zspot>, 1), (A \<rightarrow> \<Zspot>abc, 2), (A \<rightarrow> a\<Zspot>a, 0)]\<close>\\
    
    \<open>[ [(A \<rightarrow> a\<Zspot>bc, 0), (A \<rightarrow> a\<Zspot>a, 0)],\<close>\\
    \hspace{4.38mm}\<open>  [(B \<rightarrow> b\<Zspot>, 1)],\<close>\\
    \hspace{4.38mm}\<open>  [(A \<rightarrow> B\<Zspot>A, 2), (A \<rightarrow> \<Zspot>abc, 2)] ]\<close>
\end{frame}
\clearpage
\<close>*)
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps) \<open>
\begin{frame}
  \frametitle{Efficient Item List Data Structure}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{11}{17}\selectfont}
  \vspace{16mm}
  
  %\mytext{We use a functional list to store the partitions, but an array would be better.}\\
  \begin{mydefinition}\vspace{1mm}
  \isakeywordONE{datatype} efficientItemList \<open>=\<close> @{const ItemList} bin \<open>(\<close>parts list\<open>)\<close>\\
  \end{mydefinition}\vspace{-2mm}
  
  \mytext{Invariant to ensure validity of the data structure (}@{term "ItemList as fs"}\mytext{):}\\
  \<open>x \<in> as \<longleftrightarrow> x \<in> fs ! (from x)\<close>\\\vspace{16mm}

  \begin{mydefinition}\vspace{1mm}
  @{thm minus_LIL_Th.simps(1)}\\\vspace{2mm}
  @{thm minus_LIL_Th.simps(2)}
  \end{mydefinition}\vspace{12mm}

  \begin{mytheorem}\vspace{1mm}
  @{thm (prem 1) bins_L_eq_\<S>} \<open>\<and>\<close> @{thm (prem 2) bins_L_eq_\<S>} \<open>\<Longrightarrow>\<close> @{const bins_L} \<open>k ! i =\<close> @{term "\<S> i"}\\
  @{thm[mode=iffSpace] (lhs) earley_correctness_Th} \<open>\<longleftrightarrow>\<close> @{const P} \<open>\<turnstile> S \<Rightarrow>*\<close> \usebeamerfont{normal}$w$
  \end{mytheorem}
\end{frame}
\clearpage
\<close>
(*@{thm isin.simps}\\\vspace{5mm}

  @{thm insert.simps}\\\vspace{5mm}*)

(*------------------------------------------------------------------------------------------------*)
(*text (in Earley_Gw_eps) \<open>
\begin{frame}
  \frametitle{Efficient Item List Data Structure}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{24mm}
  {\fontfamily{\familydefault}\selectfont\upshape
  We can now replace the lists by item lists in the closure and prove equivalence to the other implementations:
  }\vspace{8mm}
  \begin{mytheorem}\vspace{1mm}
  @{thm (prem 1) bins_L_eq_\<S>} \<open>\<and>\<close> @{thm (prem 2) bins_L_eq_\<S>} \<open>\<Longrightarrow>\<close> @{const bins_L} \<open>k ! i =\<close> @{term "\<S> i"}\\\vspace{2mm}
  @{thm[mode=iffSpace] (lhs) earley_correctness_Th} \<open>\<longleftrightarrow>\<close> @{const P} \<open>\<turnstile> S \<Rightarrow>*\<close> \usebeamerfont{big}$w$
  \end{mytheorem}
  
\end{frame}
\clearpage
\<close>*)
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps_T) \<open>
\begin{frame}
  \frametitle{Running Time Analysis}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{6mm}
  \mytext{We perform a running time analysis with a parameter for the random access time of a part @{term T_nth_IL}, with the following assumptions:}
  \vspace{8mm}
  \begin{mydefinition}\vspace{1mm}
  @{const_typ T_nth_IL}\\\vspace{2mm}
  \begin{itemize}
    \item @{thm T_nth_Bound}\vspace{2mm}
    \item @{thm T_update_Bound}\vspace{2mm}
    \item @{thm mono_nth}
  \end{itemize}
  \end{mydefinition}
  \vspace{-4mm}
  \mytext{For lists:} @{term "T_nth_IL n = n"}\\
  \mytext{For arrays:} @{term "T_nth_IL n = 1"}\\
  \mytext{For trees:} @{term "T_nth_IL n"} \<open>=\<close> \isaconst{log} @{term "(length w)"}
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps_T) \<open>
\begin{frame}
  \frametitle{Running Time Analysis}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{16mm}
  \begin{mylemma}\vspace{1mm}
    \renewcommand{\arraystretch}{2}
    \begin{tabularx}{\textwidth}{lcX}
      @{thm (lhs) T_isin_wf} & @{text "\<le>"} & @{term "T_nth_IL"} \<open>(\<close>@{const from} \<open>x) + C\<close>\\
      @{thm (lhs) T_minus_LIL_wf} & @{text "\<le>"} & @{term "length as"} \<open>* (4 *\<close> @{term "T_nth_IL"} \<open>k + C) + k\<close>\\
      @{thm[break] (lhs) T_close2_L_bound_Th_nice_short} & @{text "\<le>"} & \<open>(C + C1 *\<close> @{term "T_nth_IL"} @{term "length Bs"}\<open>) *\<close> @{term "(length Bs)^2"} \<open>+ O(\<close>@{term "length Bs"}\<open>)\<close>
    \end{tabularx}
  \end{mylemma}\vspace{12mm}
  \begin{mytheorem}\vspace{1mm}
    \usebeamerfont{big}@{const T_earley_recognized1} @{const P} \<open>S\<close> $w$ \<open>\<le> (\<close>@{const "C1'"} \<open>+\<close> @{term C2} \<open>*\<close> @{term "T_nth_IL (length w)"}\<open>) *\<close> @{term "(length w)^3"}\\\vspace{4mm}
    \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{11}{17}\selectfont}
  @{thm C1'_def} \hspace{5mm} @{thm C2_def}
  \end{mytheorem}

\end{frame}
\clearpage
\<close>
(*%@{thm[break] (lhs) T_close2_L_bound_Th_nice_short} & @{text "\<le>"} & {\vspace{-9mm}@{thm[display] (rhs) T_close2_L_bound_Th_nice_short}}*)
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps_T) \<open>
\begin{frame}
  \frametitle{Parse Tree Basics}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{12mm}
  \begin{mydefinition}
    \usebeamerfont{big}\isakeywordONE{\usebeamerfont{big}datatype} parseTree \<open>=\<close> @{const Rule} Nt (parseTree list) \<open>|\<close> @{const Sym} Tm\\
  \end{mydefinition}

  @{const root} \mytext{= Nt or Tm at the root of the tree}\\
  @{const fringe} \mytext{= concatenation of Tms in the Sym leafs}\\
  @{term "valid_parse_tree P w A t"} \mytext{=} \<open>t\<close> \mytext{is a valid parse tree for} @{const P} \<open>\<turnstile> A \<Rightarrow>* \<close> \usebeamerfont{big}$w$\\
  

\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw) \<open>
\begin{frame}
  \frametitle{Augment to a Parser}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{11}{17}\selectfont}
  \vspace{8mm}
  {\fontfamily{\familydefault}\selectfont\upshape
  We save parse items that are an Earley item and parse trees. @{type parseItem} @{text "::"} \<open>item \<times> tree list\<close> \\
  Specification:}\\
   \<open>((A \<rightarrow> BC\<Zspot>Da, k), [t1,  t2]) \<in>\<close> @{term "\<S> i"} \<open>\<Longrightarrow>\<close>\\
    @{const P} \<open>\<turnstile> BC \<rightarrow>*\<close> $w_{\text{\myscriptsize\itshape k}} \dots w_{{\text{\myscriptsize\itshape i}}-1}$
    \<open>\<and>\<close> @{term "root t1 = B"} \<open>\<and>\<close> @{term "root t2 = C"} \<open>\<and>\<close> @{term "fringe t1 @ fringe t2"} \<open>=\<close> $w_{\text{\myscriptsize\itshape k}} \dots w_{{\text{\myscriptsize\itshape i}}-1}$
  
  \vspace{4mm}

  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \begin{figure}
  \centering
  \begin{tikzpicture}
    \node (item) at (0,0){\<open>((A \<rightarrow> BC\<Zspot>Da, k), [t1,  t2])\<close>};

    \node (rootNT) at (8,3){\<open>A\<close>};
    
    \node[minimum width=3cm,minimum height=2cm] (root) at (8,2.5){};

    \node (rootProd) at (8,2){\<open>B C D a\<close>};
    \node (t1) at (6.5,0){\<open>t1\<close>};
    \node (t2) at (7.75,0){\<open>t2\<close>};

    \draw[line width=1pt] (rootProd.south) + (-1.1,0) -- (t1.north) + (0.15,0);
    \draw[line width=1pt] (rootProd.south) + (-0.25,0) -- (t2.north);

    \draw[->, line width=1.5pt] (item.north west) + (2,0) -- (root.west);

    \draw[->, line width=1.5pt] (item.south east) + (-2.25,0) .. controls +(down:1cm) and +(down:1cm) .. (t1.south);
    \draw[->, line width=1.5pt] (item.south east) + (-1,0) .. controls +(down:1.5cm) and +(down:1.5cm) .. (t2.south);
  \end{tikzpicture}
  \caption{Visualization how the production and parse tree list represent one possibly incomplete parse tree.}
  \end{figure}
  \end{frame}
  \<close>
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps) \<open>
\begin{frame}
  \frametitle{Augment to a Parser}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{11}{17}\selectfont}
  \vspace{8mm}

  \mytext{We have to augment the recognizer operations, specifically Complete and Scan to add trees:}\\\vspace{6mm}

  {\sc Init}: \inferrule{\text{\<open>S \<rightarrow> \<alpha> \<in>\<close> @{term "P"}}
  }{\text{\<open>((S \<rightarrow> \<Zspot>\<alpha>, 0), []) \<in>\<close> @{term "\<S> 0"}}}
  \hspace{10mm}
  {\sc Predict}: \inferrule{\text{\<open>((A \<rightarrow> \<alpha>\<Zspot>B\<gamma>,  k), ts) \<in>\<close> @{term "\<S> i"}}\\
    \text{\<open>B \<rightarrow> \<beta> \<in>\<close> @{term "P"}}}{\text{\<open>((B \<rightarrow> \<Zspot>\<beta>, i), []) \<in>\<close> @{term "\<S> i"}}}\\\vspace{4mm}
  
  {\sc Complete}: \inferrule{\text{\<open>((A \<rightarrow> \<alpha>\<Zspot>, k), ts1) \<in>\<close> @{term "\<S> i"}}\\
  \text{\<open>((B \<rightarrow> \<beta>\<Zspot>A\<gamma>, l), ts2) \<in>\<close> @{term "\<S> k"}}
  }{\text{\<open>((B \<rightarrow> \<beta>A\<Zspot>\<gamma>, l),  ts2\<close> @ \<open>(\<close>@{const Rule} \<open>A ts1)) \<in>\<close> @{term "\<S> i"}}}\\\vspace{4mm}

  {\sc Scan}: \inferrule{\text{\<open>((A \<rightarrow> \<alpha>\<Zspot>b\<beta>, l), ts) \<in>\<close> @{term "\<S> i"}}\\
  \text{$w_{\text{\myscriptsize\itshape i}} = \text{\<open>b\<close>}$}
  }{\text{\<open>((A \<rightarrow> \<alpha>b\<Zspot>\<beta>, l), ts\<close> @ \<open>(\<close>@{const Sym} \<open>b)) \<in>\<close> @{term "\<S> (i+1)"}}}
  
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
(*<*)
translations (type) "('n, 'a) parseItem" <= (type) "('n, 'a) Earley.item \<times> ('b, 'c) tree list"
translations (type) "('n, 'a) parseIL" <= (type) "('n, 'a) efficientItemList \<times> ('b, 'c) tree list list"
(*>*)
text (in Earley_Gw) \<open>
  \begin{frame}
  \frametitle{Augment to a Parser}
  \usebeamerfont{normal}
  \isafontsize{\usebeamerfont{normal}}
  \setmyscriptsize{\fontsize{11}{17}\selectfont}
  \vspace{8mm}

  \mytext{We augment the item list to also store parse items, split into items and trees.}\\\vspace{12mm}

  \begin{mydefinition}
  @{type parseIL} @{text "::"} \<open>efficientItemList \<times> (parseTree list list)\<close>\\\vspace{2mm}
  @{thm set_PIL.simps}
  \end{mydefinition}\vspace{-2mm}
  \mytext{
  The parsing algorithm is the same as the recognizer, but uses the parse operations instead.\\\vspace{4mm}
  Top level function that returns a tree of a final item if it exists:}\\\vspace{12mm}

  \begin{mydefinition}
  @{const get_parse_tree_w} \<open>=\<close> \textsf{if} \<open>((S \<rightarrow> \<alpha>\<Zspot>, 0), ts) \<in>\<close> @{term "\<S> (length w)"} \textsf{then} @{const Some} \<open>(\<close>@{const Rule} \<open>S ts)\<close> \textsf{else} @{const None}
  \end{mydefinition}

  %\mytext{We prove correctness of the parser, by showing that the item list behaves the same as in the recognizer.}
\end{frame}
\clearpage
\<close>
(*------------------------------------------------------------------------------------------------*)
text (in Earley_Gw_eps_T) \<open>
\begin{frame}
  \frametitle{Augment to a Parser}
  \usebeamerfont{big}
  \isafontsize{\usebeamerfont{big}}
  \setmyscriptsize{\fontsize{14}{21}\selectfont}
  \vspace{16mm}
  
  \begin{mytheorem}\vspace{1mm}
    @{thm (lhs) get_parse_tree_Th}\hspace{2mm} \<open>\<longleftrightarrow>\<close>\hspace{1mm} @{const P} \<open>\<turnstile> S \<Rightarrow>*\<close> \usebeamerfont{big}$w$\\\vspace{2mm}
    @{thm get_parse_tree_valid_Th}
  \end{mytheorem}\vspace{2mm}\vspace{16mm}

  %@{thm valid_parse_tree_def}

  \begin{mytheorem}\vspace{1mm}%\vspace{-3mm}
    \usebeamerfont{big}@{const T_get_parse_tree_w} @{const P} \<open>S\<close> $w$ \<open>\<le> (C + C1 *\<close> @{term "T_nth_IL (length w)"} \<open>) *\<close> @{term "(length w)"}$^{\isadigit{3}}$ \<open>+ O(\<close>@{term "(length w)^2"}\<open>)\<close>\\ 
  \end{mytheorem}
\end{frame}
\clearpage
\<close>
(*%@{thm[display] T_ovrall_time_bound_Th}*)


(*<*)
end
(*>*)