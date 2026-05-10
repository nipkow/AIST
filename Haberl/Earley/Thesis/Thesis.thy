(*<*)
theory Thesis
imports
  "Earley.EarleyWorklist"
  Sugar
begin
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

definition my_Eps_free_def where
"my_Eps_free_def R = (\<forall>(_,r) \<in> R. r \<noteq> [])"

notation (latex) my_Eps_free_def ("(\<^latex>\<open>\\isaconst{\<close>Eps'_free _\<^latex>\<open>}\<close>)")

(*definition Predict :: "('n, 't) item \<Rightarrow> nat \<Rightarrow> ('n,'t) item set" where "Predict it i = undefined"*)
definition Predict' :: "('n, 't) item \<Rightarrow> nat \<Rightarrow> ('n,'t) item set" where "Predict' it i = undefined"

notation \<S> ("\<S>\<^bsub>_\<^esub>")
notation (latex) \<S> ("(\<S>\<^bsub>\<^latex>\<open>\\isavar{\<close>_\<^latex>\<open>}\<close>\<^esub>)" [0] 0)

(*lemma Earley_eq_\<S>1: "(x,i) \<in> Earley \<longleftrightarrow> x \<in> \<S>\<^bsub>i\<^esub>"
by(simp add: X_def)*)

lemma Earley_predict: assumes "x \<in> (\<S>\<^bsub>i\<^esub>)" and "next_sym_Nt x A" and "p \<in> P" and "lhs p = A" shows "Item p 0 i \<in> \<S>\<^bsub>i\<^esub>"
  using Earley.Predict[of x i "Item p 0 i"] assms by (cases p) (auto simp add: \<S>_def Predict_def)

lemma Earley_complete_rule: assumes "x \<in> (\<S>\<^bsub>i\<^esub>)" "is_complete x" "from x = f" "y \<in> \<S>\<^bsub>f\<^esub>" "next_sym_Nt y (lhs (prod x))" shows "mv_dot y \<in> \<S>\<^bsub>i\<^esub>"
  using Earley.Complete[of x i] assms by (auto simp add: \<S>_def)

lemma Earley_init: assumes "p \<in> P" "lhs p = S" shows "Item p 0 0 \<in> \<S>\<^bsub>0\<^esub>"
  using Earley.Init[of "Item p 0 0"] assms by (cases p) (auto simp add: \<S>_def Init_def)

lemma accepted_def2: shows "accepted = (\<exists>x \<in> (id (\<S>\<^bsub>length w\<^esub>)). is_final (id x))" 
  unfolding accepted_def by (auto simp add: \<S>_def)

lemma Close2_Predict_Th: "\<lbrakk> x \<in> B; \<not> is_complete x \<rbrakk> \<Longrightarrow>
    Close2 Bs (B,C) (B \<union> Predict x (length Bs) - (C \<union> {x}), C \<union> {x})" using Close2.Predict by (simp)


definition Complete_Th where "Complete_Th Bs y = {mv_dot x | x. x \<in> Bs ! from y \<and> next_sym_Nt x (lhs(prod y))}"

lemma "Earley_Gw.Complete_Th Bss y = Complete Bss y"
  by (auto simp add: Complete_def Complete_Th_def)

theorem Earley_complete_Th:
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* w"
  shows "accepted"
  using Earley_complete assms by (auto simp add: accepted_def recognized_def \<S>_def)


definition earley_recognized_Th :: "bool"  where
  "earley_recognized_Th = recognized_L (last (bins_L (length w)))"

notation earley_recognized_Th ("\<^latex>\<open>\\isaconst{\<close>earley'_recognized\<^latex>\<open>}\<close>")

lemma parse_tree_w_abbrev: "parse_tree_w \<equiv> get_parse_tree (last (Parse_bins_L (length w)))"
  by simp

definition parse_tree_w_Th where "parse_tree_w_Th = get_parse_tree (last (Parse_bins_L (length w)))"

notation (latex) parse_tree_w_Th (\<open>\<^latex>\<open>\isaconst{\<close>parse'_tree'_w\<^latex>\<open>}\<close>\<close>)

fun parseBin :: "nat \<Rightarrow> ('n, 't) parseItem set" ("\<P>\<^bsub>_\<^esub>") where
"parseBin k = (if k \<le> length w then (Parse_bins k ! k) else {})"

lemma PInit_Th: "p \<in> P \<Longrightarrow> lhs p = S \<Longrightarrow> (Item p 0 0, []) \<in> parseBin 0" using Parse_Close.Init by (cases p) (auto simp add: Parse_Init_def )

lemma length_parse_bins_Th: "length (Parse_bins i) = i + 1"
  by (induction i) (auto simp add: Let_def)

lemma parse_bins_ne_Th: "Parse_bins i \<noteq> []" by (induction i) (auto simp add: Let_def)

lemma PPredict_Th: "pi \<in> parseBin i \<Longrightarrow> p \<in> P \<Longrightarrow> next_sym_Nt (item pi) (lhs p) \<Longrightarrow> (Item p 0 i, []) \<in> parseBin i"
proof(cases i)
  case 0
  assume "pi \<in> parseBin i" "p \<in> P" "next_sym_Nt (item pi) (lhs p)"
  then show ?thesis using 0 Parse_Close.Predict[of pi "[]" Parse_Init "(Item p 0 0, [])"] by (cases pi, cases p) (auto simp add: Parse_Predict_def)
next
  case (Suc nat)
  assume "pi \<in> parseBin i" "p \<in> P" "next_sym_Nt (item pi) (lhs p)"
  then show ?thesis using Suc Parse_Close.Predict[of pi "Parse_bins nat" _ "(Item p 0 i, [])"] length_parse_bins_Th[of "nat"]
        by (cases pi, cases p) (auto simp add: Parse_Predict_def Let_def nth_append_right if_splits)
qed

end

context Earley_Gw_eps
begin

lemma find_parse_tree_iff_w_in_L_Th: "(\<exists>t. parse_tree_w_Th = Some t) \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using find_parse_tree_iff_w_in_L by (auto simp add: w_def Lang_def parse_tree_w_Th_def)


lemma generated_parse_tree_is_valid_Th: "parse_tree_w_Th = Some t \<longrightarrow> valid_parse_tree P w S t"
    using generated_parse_tree_is_valid by (simp add: parse_tree_w_Th_def)

lemma unambiguous_impl_the_parse_tree_Th: "unambiguous (Cfg P S) \<Longrightarrow> valid_parse_tree P w S t \<longleftrightarrow> parse_tree_w_Th = Some t"
  using unambiguous_impl_the_parse_tree by (simp add: parse_tree_w_Th_def)

lemma unambiguous_impl_P_set_eq_P_L_Th: "unambiguous (Cfg P S) \<Longrightarrow> get_parse_tree_set = parse_tree_w_Th"
  using unambiguous_impl_P_set_eq_P_L by (simp add: parse_tree_w_Th_def)



lemma test_Th_1: "f \<le> length w \<Longrightarrow> f \<le> i \<Longrightarrow> Parse_bins f ! f = Parse_bins i ! f"
  proof (induction i)
    case 0
    then show ?case by auto
  next
    case (Suc i)
    then show ?case
    proof (cases "f = Suc i")
      case True
      then show ?thesis by simp
    next
      case False
      then have "f < Suc i" using Suc by auto
      then show ?thesis using Suc length_parse_bins_Th[of "i"] by (simp add: Let_def nth_append_left)
    qed
  qed

lemma PComplete_Th: 
  assumes "pi \<in> parseBin i" "pi = (Item p d f, ts)" "is_complete (item pi)" "pi' \<in> parseBin f" "(lhs p) = A" "next_sym_Nt (item pi') A"
  shows "(mv_dot (item pi'), (Rule A (rev ts)) # (trees pi')) \<in> parseBin i"
proof(cases i)
  case 0
  have "wf_parse_bin1 (parseBin 0) 0"
    by (metis EarleyWorklist.Earley_Gw_eps.length_parse_bins Earley_Gw_eps_axioms Nat.less_eq_nat.simps(1) less_Suc0 local.parseBin.simps
        parse_bins_wf1 wf_parse_bins1_def)
  then have "from (item pi) < 0" using assms 0 by (auto simp add: wf_item1_def wf_item_def)
  then show ?thesis by auto
next
  case (Suc nat)
  have "wf_parse_bin1 (parseBin i) i"
    by (metis EarleyWorklist.Earley_Gw_eps.parse_bins_wf1_nth Earley_Gw_eps_axioms Suc Suc_leI assms(1) equals0D lessI
        local.parseBin.elims)
  then have "wf_parseItem1 pi i" using assms by auto
  then have "f < i" using assms by (auto simp add: wf_item1_def wf_item_def)
  then have "f \<le> nat" using Suc by auto
  moreover have "f \<le> length w" using assms by (auto simp add: if_splits)
  ultimately have "pi' \<in> Parse_bins nat ! f" using test_Th_1[of f nat] assms Suc by auto
  then have "pi' \<in> {x. x \<in> Parse_bins nat ! from (item pi) \<and> next_sym_Nt (fst x) A}" using assms by auto
  then have "(mv_dot (item pi'), (Rule A (rev (trees pi))) # (trees pi')) \<in> (\<lambda>x. case x of (p, t) \<Rightarrow> (mv_dot p, Rule A (rev (trees pi)) # t)) ` {x. x \<in> Parse_bins nat ! from (item pi) \<and> next_sym_Nt (fst x) A}"
    by auto
  then show ?thesis using assms Suc length_parse_bins_Th[of "nat"] Parse_Close.Complete[of pi "Parse_bins nat" "Parse_Scan (last (Parse_bins nat)) nat" "(mv_dot (item pi'), (Rule A (rev (trees pi))) # (trees pi'))"]
    by (cases pi, cases "prod (item (pi))", cases "nat + 1 \<le> length w") (auto simp add: Parse_Complete_def Let_def nth_append_right)
qed
end

context Earley_Gw 
begin

lemma PScan_Th: assumes "pi \<in> parseBin i" "i < length w" "next_symbol (item pi) = Some (w ! i)"
  shows "(mv_dot (item pi), (Sym (w!i)) # trees pi) \<in> parseBin (i+1)"
  using assms Parse_Close.Init[of "(mv_dot (item pi), Sym (w ! i) # (trees pi))" "Parse_Scan (last (Parse_bins i)) i" "Parse_bins i"] length_parse_bins_Th[of "i"] last_conv_nth[of "Parse_bins i"] parse_bins_ne_Th 
  by (cases pi) (auto simp add: Let_def Parse_Scan_def nth_append_right )

(*List version*)
fun  Close2_L  where 
"Close2_L Bs (bs, cs) (bs', cs') = Close2 (map set Bs) (set bs, set cs) (set bs', set cs')"

fun step_fun_L :: "('n,'t) item list list \<Rightarrow> ('n,'t) item list \<times> ('n,'t) item list \<Rightarrow> ('n,'t) item list \<times> ('n,'t) item list" where
  "step_fun_L Bs (b#bs, cs) = 
  (let nexts = (if is_complete b then Complete_L Bs b else Predict_L b (length Bs))
  in (diff_list (union_list nexts (b#bs)) (insert_list b cs), insert_list b cs))"

fun steps_L :: "('n,'t) item list list \<Rightarrow> ('n,'t) item list \<times> ('n,'t) item list \<Rightarrow> (('n,'t) item list \<times> ('n,'t) item list) option" where
  "steps_L Bs BC = while_option (\<lambda>(B',C'). B' \<noteq> []) (step_fun_L Bs) BC"

definition close2_L_Th where
"close2_L_Th Bs B = snd (the (steps_L Bs (B,[])))"

fun bins_L_Th where
"bins_L_Th 0 = [close2_L_Th [] Init_L]"
| "bins_L_Th (Suc k) = (let Bs = bins_L_Th k in Bs @[close2_L_Th Bs (Scan_L (last Bs) k)])"

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

lemma steps_L_Th_sound1: assumes  "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "steps_L Bs (B,C) = Some (B',C')"
  shows "(Close2_L Bs)^** (B,C) (B',C')"
proof -
  let ?P = "\<lambda>(B',C'). (Close2_L Bs)^** (B,C) (B',C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)"
  have "\<And>B C. B\<noteq>[] \<Longrightarrow> ?P (B,C) \<Longrightarrow> ?P (step_fun_L Bs (B,C))"
    by (smt (verit) Transitive_Closure.rtranclp.simps case_prodI2 case_prod_conv fst_conv step_fun_L_sound step_fun_L_wf)
  thus ?thesis using while_option_rule[where P = ?P, OF _ assms(3)[unfolded steps_L.simps]] assms(1,2)
    by auto
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
  

definition Close2_L_Th_less :: "nat \<Rightarrow> ((('n,'t) item list \<times> ('n,'t) item list) \<times> (('n,'t) item list \<times> ('n,'t) item list)) set" where
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
end


context Earley_Gw_eps begin

(*(if (\<exists> i t. (i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i) 
    then Some ( Rule S (rev (SOME t. \<exists>i. (i,t) \<in> (last (Parse_bins (length w))) \<and> is_final i))) else None)"*)

lemma fst_image: "x \<in> image fst Y \<Longrightarrow> \<exists>y. (x,y) \<in> Y"
  by auto




(*lemma "get_parse_tree_set = (get_parse_tree (last (Parse_bins_L (length w))))"*)

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
end

context Earley_Gw_eps_T begin
lemma T_minus_IL_wf_Th: 
  assumes "wf1_IL il1 (length (froms il1) - 1)" "inv_IL il1" "inv_IL il2" "wf1_IL il2 (length (froms il1) - 1)"
   "length (froms il2) \<ge> length (froms il1)" "length (froms il1) > 0"
 shows "T_minus_IL il1 il2 \<le> (length (list il1)) * (4 * T_nth_IL (length (froms il1) - 1) + 2*L * (Suc K) + 5)
    + mbox0 (2 * length (froms il1) + 3)"
  using T_minus_IL_wf[OF assms] by (auto simp add: algebra_simps mbox0_def)

definition T_step_fun_bound_Th_def :: "nat" where "T_step_fun_bound_Th_def = 0"

notation T_step_fun_bound_Th_def (\<open>\<^latex>\<open>\isaconst{\<close>T'_step'_fun'_bound\<^latex>\<open>}\<close>\<close>)

lemma T_close2_L_bound_Th_nice: 
  assumes "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)"  "wf1_IL il (length Bs)" "inv_IL il" "length (froms il) = Suc (length Bs)"
  shows "T_close2_L Bs il \<le> (L * Suc K * Suc (length Bs))^2 * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 10 + 2 * (K + 2))
  +  L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 2 * L * Suc K + 7 + Suc K)
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
  finally show ?thesis.
qed

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

translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"

hide_const (open) \<alpha>
(*>*)

(*type_synonym ('n, 't) sentential = "('n,'t) sym list"*)

text\<open>

\chapter{Introduction} \label{chap:Intro}
In informatics, context-free grammars are an important tool for describing the syntax of many different objects, such as programming languages and file and binary data formats.
 As such, the correct parsing of context-free grammars is vitally important in many situations. It is needed to ensure accurate program compilation and thus correct program behavior after compilation,
 and it is also security-relevant when used to parse file or binary formats that may have been supplied by a user.

Because of this, many different parsing algorithms exist for context-free languages, but only a few implementations have been formally proven correct.
 In the field of program parsing, the primary focus is performance. Thus, there exist many parsers designed for certain subclasses of context-free grammars that guarantee a linear running time.
 For example LR(k) \cite{deremer1969practical} or LL(k) \cite{Scott2010} parsing algorithms.

We focus on an all-purpose parser for context-free grammars, proposed by Earley in 1970 \cite{Earley1970}. It guarantees a worst-case cubic running time bound and better bounds for specific subclasses of grammars.
 The only formal verification of this algorithm we know of is the one on which our work is built. That verification was done by Nipkow and Rau \cite{Nipkow2024}, and was itself built on a paper by Jones \cite{Jones1972}.
 These formalizations did not yet yield an executable parser, as they used abstract set types and therefore did not formally analyze the running time bounds.
 Our thesis seeks to close this gap by implementing an executable, list-based version of the recognizer and parser and formally proving the cubic time bound put forth by Earley.

In this thesis, we start by providing a background on context-free grammars and parse trees in Isabelle in \autoref{chap:Background}.
 We then recap Earley's algorithm \cite{Earley1970} and the work of Nipkow and Rau \cite{Nipkow2024}, which serves as the basis for our implementations in \autoref{chap:Earley_formal}. 
 Our contributions start by refining the recognizer into a list-based executable version using the data structure proposed by Earley, and proving its correctness and termination in \autoref{chap:List_version}.
 In \autoref{chap:Runingtime_1}, we conduct a parameterized asymptotic analysis of the running time of our algorithm.
 We then augment this algorithm to function as a parser in \autoref{chap:Parse_trees}, implementing both a set- and a list-based version, 
 and perform a similar running time analysis to that in the recognizer case in \autoref{sec:Runingtime_2}. 
 Lastly, we provide an overview of related work, including other formally verified parsers, in \autoref{chap:related}.

\<close>

text (in Earley_Gw)\<open>
\chapter{Background} \label{chap:Background}

\section{Context-Free Grammars}

Languages are sets of words, which are strings made up of terminal symbols. The whole set of terminal symbols is called the alphabet $\Sigma$.
One way to define what words are in a language is context-free grammars (CFGs), which introduce new non-terminal symbols and productions 
that formalize how to transform a string of non-terminal and terminal symbols to derive words step by step, starting from a single non-terminal.
A production expresses one such possible step, where you replace one non-terminal symbol by a string of non-terminal and terminal symbols.
The Language of a CFG is then the set of strings containing only terminal symbols that can be reached from the starting non-terminal, following the modifications described by the productions.
Strings of non-terminals and terminals are called sentential forms, and strings of only terminal symbols are called sentences or words.

Formally, in Isabelle, strings are represented by lists, and so to represent sentential forms, non-terminals and terminals are grouped together into the wrapper symbol 
datatype @{type sym}, which can represent either a terminal (@{const Tm}) or non-terminal (@{const Nt}) symbol.
\begin{quote}
  @{datatype sym}
\end{quote}
Productions \<open>(A, \<alpha>)\<close> are a pair of a non-terminal \<open>A\<close> and a sentential \<open>\<alpha>\<close>, where the non-terminal is called the left-hand side (lhs) and the sentential is called the right-hand side (rhs) of the production.
In text, we will write productions like this \<open>(A \<rightarrow> \<alpha>)\<close>. Sets of productions have type @{type "Prods"} or @{type "prods"} when stored as lists.
A set of productions $\isaconst{P}$ then defines the so-called derivation relation @{term "P \<turnstile> u \<Rightarrow> v"}, which is formally defined as follows:
\begin{definition}
@{const_typ derive}\\[\funheadersep]
@{thm derive.simps[of P u v, rename_abs A \<beta> x y]}
\end{definition}
This represents one derivation step as described informally above. Context-free grammars consist of a set of productions $P$ 
and a non-terminal starting symbol, commonly named $\isavar{S}$. The Language of a CFG is then defined in terms of the transitive closure of the derivation relation @{term "P \<turnstile> u \<Rightarrow>* v"}. 
Specifically, it is the set of sentences that are reachable from the starting non-terminal $\isavar{S}$.
\begin{quote}
  @{datatype Cfg}
\end{quote}
\begin{definition}
  @{def Lang}\\[2.5mm]
  @{const_typ LangS}\\[\funheadersep]
  @{abbrev LangS}
\end{definition}

A CFG implicitly defines the sets of terminals and non-terminals by which appear in its productions.
\begin{quote}
  @{def Nts_syms}\\[1.5mm]
  @{def Nts}\\[3mm]
  @{def Tms_syms}\\[1.5mm]
  @{def Tms}
\end{quote}

There are many interesting computational questions concerning languages. One very natural question is, given a word $\isaconst{w}$, is it in the language given by a CFG?
This problem is called recognition. A natural continuation is asking about the derivation of such a word if it is in the language, which is called parsing.

%This relation takes a set of Productions and two sentential forms and returns true if and only if 
%there exists a production @{text "(Nt A, \<beta>)"}, @{text "Nt A"} appears in the first sentential form and is replaced by $\beta$ in the second sentential form.

\section{Parse Trees}

Parse trees are a way to encode a derivation as a tree structure. The inner nodes represent one production, and the leaves are symbols.
In Isabelle, there exists the parse tree datatype @{type tree}:
\begin{quote}
  @{datatype tree}
\end{quote}
A production, also called a @{const Rule} in the context of parse trees, consists of a non-terminal (the lhs) and a list of child trees, representing the symbols of the right-hand side in order.
So for every child, it has to hold that either it is a leaf of the corresponding symbol, or it is a rule with the corresponding non-terminal as its left-hand side. 
Thus, for a given set of productions, we can define the following predicate that a parse tree has to fulfill:
\begin{definition}
  @{const_typ parse_tree}\\[\funheadersep]
  @{thm parse_tree.simps(1)}\\
  @{thm (eta_expand t) parse_tree.simps(2)}
\end{definition}
There exist two access functions for the parse tree.
The projection @{const root} returns the non-terminal of a rule or the symbol of a leaf at the root of the tree, and @{const fringe} returns the concatenation of the symbols of the leaves of a parse tree.
\begin{quote}
  @{const_typ root}\\[\funheadersep]
  @{thm (dummy_pats) root.simps(1)}\\
  @{thm (dummy_pats) root.simps(2)}\\[2.5mm]
  @{const_typ fringe}\\[\funheadersep]
  @{thm (dummy_pats) fringe.simps(1)}\\
  @{thm (dummy_pats) fringe.simps(2)[show_abbrevs=false]}
\end{quote}
We use these to define the @{const valid_parse_tree} predicate that checks for a CFG, consisting of productions @{term "P"} 
 and starting symbol @{term "S"}, and a word @{const w}, that the parse tree is correct 
 and represents the derivation showing that $\isaconst{w}$ is a word of the CFG's language.
\begin{definition}
  @{const_typ[break, margin=80] valid_parse_tree}\\[\funheadersep]
  @{thm valid_parse_tree_def[where p=P and A=S and ws=w]}
\end{definition}

And finally, we prove that parse trees represent derivations by showing that for any derivation, there exists a valid parse tree and that the existence of a valid parse tree implies that there exists a derivation for its word.
\begin{lemma}\,\\[\funheadersep]
  @{thm parse_tree_if_derives}\\[2.5mm]
  @{thm fringe_steps_if_parse_tree}
\end{lemma}


While for every parse tree there exists a single derivation it represents, a derivation may have multiple different parse trees.
The existence of different parse trees for a word is a property of the grammar, and so we call grammars in which every word has exactly one parse tree \emph{unambiguous}.
\begin{definition}
  @{def unambiguous}
\end{definition}

%\begin{itemize}
%  \item CFG in Isabelle
%  \item Parse trees in Isabelle
%\end{itemize}
\<close>

text\<open>
\chapter{Earley Recognizer Formalization} \label{chap:Earley_formal}
In this thesis, we formalize a recognizer first proposed by Earley \cite{Earley1970}. Our contributions are based on prior work by Nipkow and Rau \cite{Nipkow2024}. 
 We present their work in a condensed form here, as it serves as an important basis for further proofs. 
 Our contributions start in \autoref{chap:List_version} and include a discussion of how to handle sets of productions that can derive the empty word in \autoref{sec:epsilon}.

We fix, for the following chapter, a word $\isaconst{w}$ and a CFG $C$ that induces the language $L$.
The CFG will have the starting symbol $\isavar{S}$ and either set $P$ or list $ps$ of productions.
Earley's recognizer builds sets of items (\<open>\<S>\<close>), also called bins, for each index of $\isaconst{w}$, where an item in one of these sets represents that a certain substring of $\isaconst{w}$ has been recognized.
These items consist of a production and two natural numbers called dot and from.\<close>

(*<*)
locale test
begin
(*>*)

text_raw \<open>\begin{quote}\isamarkuptrue\<close>
datatype ('n,'t) item = Item (prod: "('n,'t) prod") (dot : nat) ("from" : nat)
text_raw \<open>\end{quote}\<close>

(*<*)
end
(*>*)
(*datatype item*)
text (in Earley_Gw)\<open>
We will write an item \<open>Item p d f\<close> like this \<open>(A \<rightarrow> \<alpha>\<Zspot>\<beta>, f)\<close>, where the production is \<open>(A, \<alpha>\<beta>)\<close> and \<open>d = |\<alpha>|\<close>.
The idea behind the recognizer is that an item @{term "Item p k l"} in bin $\mathcal{S}_i$ symbolizes that we have recognized the substring of $\isaconst{w}$ 
starting at index $l$ and ending at index $i$, and that it can be derived from the partial right-hand side of $p$ that is left of the dot at position $k$.
We call this property soundness.
\begin{definition}[Soundness]\label{soundness}
  @{term "Item (p :: ('n,'t) prod) k l \<in> (\<S> i) \<Longrightarrow> P \<turnstile> slice 0 k (rhs p) \<Rightarrow>* slice l i w"}. %could use sound_item_def
\end{definition}
The function @{term "slice i k s"} returns the substring starting at index $i$ and ending at index $k-1$. It is equivalent to @{term "take k (drop i s)"}.

For better readability, we define some helper functions:
\begin{quote}
  @{def is_complete}\\[2.5mm]
  {\setlength{\parskip}{0pt}@{def next_symbol}}\\[2.5mm]
  @{abbrev next_sym_Nt}\\[2.5mm]
  @{def mv_dot} 
\end{quote}
The predicate @{const is_complete} checks whether the dot is at the end of the production, @{const next_symbol} returns an option of the symbol after the dot, 
@{const next_sym_Nt} checks if the next symbol is a specific non-terminal, and @{const mv_dot} moves the dot over the next symbol.\\
We also define a predicate to check whether an item is well-formed in the context of the recognizer algorithm, meaning we check what items could appear in a bin $\mathcal{S}_k$. We check that the production is part of the grammar, 
that the dot is a valid index into the right-hand side of the production, that the from-value is less than or equal to $k$, and that $k$ is less than or equal to the length of $\isaconst{w}$.
\begin{definition}
  @{def wf_item}
\end{definition}

Earley then defines three operations for the recognizer algorithm that generate items for these bins in an inductive manner. These operations are called \emph{Predict}, \emph{Complete}, and \emph{Scan}.
If we have an item in bin $\mathcal{S}_i$ with its dot in front of a non-terminal \<open>A\<close>, we predict. So we start recognizing a new a substring of $\isaconst{w}$, starting at index $i$, from the non-terminal $A$.
\begin{quote}
{\sc Predict}: $\inferrule{@{thm (prem 1) Earley_predict} \\
  @{thm (prem 2) Earley_predict}\\
  @{thm (prem 3) Earley_predict}\\
  @{thm (prem 4) Earley_predict}}{@{thm (concl) Earley_predict}}$
\end{quote}
%This means we add @{term "{Item p 0 i | p. p \<in> P \<and> lhs p = A}"} items to bin $\mathcal{S}_i$. 
Completion occurs when we have fully recognized an item \<open>(B \<rightarrow> \<alpha>\<Zspot>, f) \<in>\<close> @{term "\<S> i"}, meaning its dot is at the end of the right-hand side of the production.
In this case, we have recognized the substring of $\isaconst{w}$ from \<open>f\<close> to \<open>i\<close>. This recognition started with the non-terminal \<open>B\<close>, the one on the production's left-hand side.
So we can extend the recognition of substrings up to \<open>f\<close> \mbox{(@{term "P \<turnstile> u \<Rightarrow>* slice k f w"})} as follows: \mbox{@{term "P \<turnstile> u @ [Nt B] \<Rightarrow>* slice k i w"}}.
In terms of items, this means we take an item that recognizes a substring up to \<open>f\<close> from bin \<open>\<S>\<^sub>f\<close> and extend its recognition if the symbol after the dot is the non-terminal \<open>B\<close>.
\begin{quote}
{\sc Complete}: $\inferrule{@{thm (prem 1) Earley_complete_rule} \\
  @{thm (prem 2) Earley_complete_rule}\\
  @{thm (prem 3) Earley_complete_rule}\\\\
  @{thm (prem 4) Earley_complete_rule}\\
  @{thm (prem 5) Earley_complete_rule}}{@{thm (concl) Earley_complete_rule}}$
\end{quote}
%Formally: We add @{term "{mv_dot it | it. it \<in> \<S>\<^sub>k \<and> next_symbol it = Some (Nt B)}"} to \<open>\<S>\<^sub>i\<close>.
The last operation \emph{Scan} occurs when the next symbol of an item is a terminal. In this case, we can advance recognition of the substring if the next symbol in $\isaconst{w}$ is that terminal.
In this case, we add these items to the next bin $\mathcal{S}_{i+1}$, since the length of the recognized substring of $\isaconst{w}$ has increased by one.
\begin{quote}
{\sc Scan}: $\inferrule{@{thm (prem 1) Earley.Scan[simplified Earley_eq_\<S>]}\\
  @{thm (prem 2) Earley.Scan[simplified Earley_eq_\<S>]}\\
  @{thm (prem 3) Earley.Scan[simplified Earley_eq_\<S>]}}
  {@{thm (concl) Earley.Scan[simplified Earley_eq_\<S>]}}$
\end{quote}
%Formally: @{term "{mv_dot it | it. it \<in> \<S>\<^sub>i \<and> next_symbol it = Some (w ! i)}"} 
Lastly, we need a starting point for this inductive definition. For this, we use the result of applying the \emph{Predict} operation to the starting symbol. We will be referring to this as the fourth operation \emph{Init}.
\begin{quote}
  {\sc Init}: $\inferrule{@{thm (prem 1) Earley_init}\\
  {@{thm (prem 2) Earley_init}}}
  {@{thm (concl) Earley_init}}$
\end{quote}
%Formally: @{term "{Item p 0 0 | p. p \<in> P \<and> lhs p = S}"}

From these inductive definitions, we can derive the following functions that produce sets by applying the operations to a single item.
 For the definition of the @{const Complete} set, we get a list $\isavar{Bs}$ of computed bins for which @{prop "Bs ! i = \<S>\<^sub>i"} holds.
\begin{quote}
  @{thm Predict_def[of it i, rename_abs _ p]}\\[1ex]
  @{thm (lhs) Complete_def} @{text "="} @{thm (rhs) Complete_Th_def[rename_abs _ it]}\\[1ex]
  @{thm Scan_def[of \<S>\<^sub>i i, rename_abs _ it]}\\[1ex]
  @{thm Init_def[rename_abs _ p]}
\end{quote}
\<close>


text (in Earley_Gw) \<open>
We also define a top-level predicate for $\isaconst{w}$, called @{const accepted}, that returns true if we find a complete item with the start symbol as its left-hand side in the last bin @{term "\<S> (length w)"}.
By soundness, this means that @{term "P \<turnstile> [Nt S] \<Rightarrow>* w"} holds.
\begin{definition}
  @{thm (concl) accepted_def2}\\[1ex]
  where @{thm is_final_def}
\end{definition}
\<close>

text \<open>
We give an example to better understand and visualize the algorithm:
Given a CFG with productions \<open>P = {A \<rightarrow> AB, A \<rightarrow> BA, A \<rightarrow> a, B \<rightarrow> b}\<close> and starting non-terminal \<open>A\<close>, we get the following bins for the word "bab".\\
\begin{table}[h]
\begin{center}
\begin{tabularx}{12cm}{|X c|X c|X c|X c|}
\hline
  \multicolumn{2}{|c|}{$\mathcal{S}_0$} & \multicolumn{2}{|c|}{$\mathcal{S}_1$}  & \multicolumn{2}{|c|}{$\mathcal{S}_2$}  & \multicolumn{2}{|c|}{$\mathcal{S}_3$} \\
\hline
  \<open>A \<rightarrow> \<Zspot>AB\<close> & 0 & \<open>B \<rightarrow> b\<Zspot>\<close>  & 0 & \<open>A \<rightarrow> a\<Zspot>\<close>  & 1 & \<open>B \<rightarrow> b\<Zspot>\<close>  & 2 \\
  \<open>A \<rightarrow> \<Zspot>BA\<close> & 0 & \<open>A \<rightarrow> B\<Zspot>A\<close> & 0 & \<open>A \<rightarrow> BA\<Zspot>\<close> & 0 & \<open>A \<rightarrow> AB\<Zspot>\<close> & 1 \\
  \<open>A \<rightarrow> \<Zspot>a\<close>  & 0 & \<open>A \<rightarrow> \<Zspot>AB\<close> & 1 & \<open>A \<rightarrow> A\<Zspot>B\<close> & 1 & \<open>A \<rightarrow> AB\<Zspot>\<close> & 0 \\
  \<open>B \<rightarrow> \<Zspot>b\<close>  & 0 & \<open>A \<rightarrow> \<Zspot>BA\<close> & 1 & \<open>A \<rightarrow> A\<Zspot>B\<close> & 0 & \<open>A \<rightarrow> BA\<Zspot>\<close> & 0 \\
            &   & \<open>A \<rightarrow> \<Zspot>a\<close>  & 1 & \<open>B \<rightarrow> \<Zspot>b\<close>  & 2 & \<open>A \<rightarrow> A\<Zspot>B\<close> & 1 \\
            &   & \<open>B \<rightarrow> \<Zspot>b\<close>  & 1 &            &   & \<open>A \<rightarrow> A\<Zspot>B\<close> & 0 \\ 
            &   &            &   &           &   & \<open>B \<rightarrow> \<Zspot>b\<close> & 3 \\
\hline
\end{tabularx}
\end{center}
\caption{Example of the bins constructed by the Earley recognizer}
\end{table}
\<close>



text (in Earley_Gw)\<open>
\section{Inductive Definition}
Towards a formal proof of this recognizer, we define an inductive Earley set, which will be the union of all $\mathcal{S}_i$ where $i \leq |\isaconst{w}\,|$. 
To differentiate which bin each item is in, we will store pairs of and Earley item and a natural number indicating which bin it belongs to.
The full set is constructed inductively using the three operations and the initial bin discussed previously.
\begin{quote}
  @{const_typ Earley}
\end{quote}

For correctness, we need to prove the two directions of soundness and completeness. This means that if the recognizer accepts a word, it is in the language,
 and vice versa, that if a word is in the language, the recognizer accepts it.
Soundness is quite easy to prove for this definition. We only need to prove that the soundness predicate holds for every item added to this set, 
which is done by proving that all operations preserve soundness and showing that the initial set is sound. From these individual proofs, overall soundness follows:
\begin{theorem}\,\\[\funheadersep]
  @{thm accpted_sound}
\end{theorem}
To prove completeness, we show that if there is an item in the Earley set and the rest of the item's right-hand side after the dot can derive a substring of $\isaconst{w}$ following the substring already recognized by the item, 
then the completed item will also be in the set.
\begin{lemma}\,\\
  @{thm[break,margin=90] Earley_complete_induction}
\end{lemma}
This is proven using complete induction on the length of the derivation and an induction on the length of the rest of the right-hand side of the item.
%We sketch this proof. The base case where the remainder of the right-hand side is zero is trivial, as the item is complete and therefore the completed item is in the set.
%If the item is incomplete, we differentiate two cases based on if the next symbol is a terminal or a non-terminal
%could go into a bit more detail if necessary
From this, full completeness follows rather easily, as the initial set contains all possible incomplete items after one step of derivation. 
Therefore, if the entire word is derivable, one of these items will be complete in the final Earley-bin @{term "\<S> (length w)"}, and so the word is accepted by the recognizer.
\begin{theorem}\,\\[\funheadersep]
  @{thm Earley_complete_Th}
\end{theorem}
\<close>
(*Towards executability:
- First we change to an iterative computation of the Earley sets using an inductive closure algorithm (bins & Close)
- We constrain the input to epsilon-free grammars to achieve a one-pass closure (Close1)
- We make a nondeterministic worklist algorithm for the one pass closure  (Close2)*)
text (in Earley_Gw)\<open>
\section{Towards Executability}
While this theoretical Earley recognizer is well-suited for proofs, it is poorly suited for execution due to its inductive definition. 
Instead, the iterative bin computation suggested by Earley is better suited.
Looking at the four operations of the Earley algorithm, we see that only \emph{Predict} and \emph{Complete} add items to the current bin, 
while \emph{Init} is the starting set of the first bin, and \emph{Scan} adds items to the next bin, resulting in the starting set of the next bin.
Every operation also depends only on items in bins with an index lower than or equal to the current bin's index, allowing us to compute the bins in order.
So we can split the algorithm into two steps: first, compute the starting set for bin $\mathcal{S}_i$ using \emph{Init} or \emph{Scan}, 
and then compute the closure of this bin under \emph{Predict} and \emph{Complete}. We can repeat this until we have computed all bins.

%Going forward, we will call item sets \emph{bins}, to which we extend the well-formedness predicate. %TODO include maybe
The algorithm will follow this general form:
\begin{quote}
  @{const_typ bins}\\[\funheadersep]
  @{thm bins.simps(1)}\\
  @{thm bins.simps(2)}
\end{quote}
It computes a list of bins as described before, using @{const Close} to compute the closure. 
This way, we can refine the closure algorithm step by step while the underlying structure of the algorithm remains unchanged.
From now on, \<open>Bs\<close> will always refer to the previously computed list of bins.

To prove that this new algorithm computes the same bins as the fully inductive definition, we first use an inductive closure. It takes a starting set \<open>B\<close> --- either a result of \emph{Init} or \emph{Scan} --- 
and the previously computed list of bins \<open>Bs\<close>, and returns the closure \<open>C\<close> under \emph{Predict} and \emph{Complete}.
\begin{quote}
  @{const_typ Close}\\[\funheadersep]
  @{const Init}: $\inferrule{@{thm (prem 1) Close.Init}}
  {@{thm (concl) Close.Init}}$ \hspace{5mm}
  @{const Predict}: $\inferrule{@{thm (prem 1) Close.Predict}\\ @{thm (prem 2) Close.Predict}}
  {@{thm (concl) Close.Predict}}$\\[1ex]
  @{const Complete}: $\inferrule{@{thm (prem 1) Close.Complete}\\ @{thm (prem 2) Close.Complete}\\ @{thm (prem 3) Close.Complete}\\
  @{thm (prem 4) Close.Complete}\\ @{thm (prem 5) Close.Complete}}
  {@{thm (concl) Close.Complete}}$
\end{quote}

We then prove that the the @{const bins} function using @{const Close} is equivalent to the original Earley implementation.
\begin{theorem}\,\\[\funheadersep]
  @{thm bins_eq_\<S>}
\end{theorem}
%Here, the function \<open>\<S>\<close> collects all items of the fully inductive Earley set that are in the i-th set.
\<close>

text (in Earley_Gw_eps) \<open>
We are working towards a one-pass closure algorithm that only needs to consider every element exactly once.
This is possible if the items added by \emph{Predict} and \emph{Complete} do not depend on the items in the current bin closure we are computing.
This is the case for the \emph{Predict} operation, which only depends on the set of productions.
For the \emph{Complete} operation, it is only the case if the complete item's from-value is the index of a previous bin,
 which is true if the production has a length greater than zero. 
Handling the \emph{Complete} operation for length-zero productions is not straightforward, so we require the grammar to be epsilon-free.
\begin{definition}
  @{const_typ Eps_free}\\[\funheadersep]
  @{thm my_Eps_free_def_def[of P, rename_abs lhs rhs]}
\end{definition}
This way, we simplify the algorithm. We also provide options for handling grammars containing epsilon productions in \autoref{sec:epsilon}.

Under the epsilon-free assumption we can strengthen the @{const wf_item} predicate, as the from index of a completed item has to be strictly lower than the index of its bin, otherwise a Nt could derive the empty word.
This strengthend version is called @{const wf_item1} and is extended to bins in @{const wf_bin1} and @{const wf_bins1}.
\begin{definition}
  @{def wf_item1}\\[3mm]
  @{thm wf_bin1_def}\\[3mm]
  @{thm wf_bins1_def}
\end{definition}
Under the assumption of epsilon-freeness, we create another closure, @{const Close1}, which works the same as @{const Close}, but the \emph{Complete} operation is simplified, as we assume the grammar to be epsilon-free:
\begin{quote}
  @{const Complete} : $\inferrule{@{thm (prem 1) Close1.Complete}\\ @{thm (prem 2) Close1.Complete}\\\\ @{thm (prem 3) Close1.Complete}\\
  @{thm (prem 4) Close1.Complete}}
  {@{thm (concl) Close1.Complete}}$
\end{quote}
We prove equivalence to @{const Close} under the assumption of epsilon-freeness.
\begin{lemma}\,\\[\funheadersep]
  @{const Eps_free} @{const P} \<open>\<and>\<close> @{thm Close1_eq_Close}
\end{lemma}
Unless specified otherwise, we will assume that the grammar is epsilon-free from here on out and drop the @{term "my_Eps_free_def P"} assumption.
The next step towards executability is replacing the inductive closure with a one-pass workset algorithm.\<close> 


(*%One tricky detail is the handling of productions deriving the empty word. The \emph{Predict} operation only depends on the set of productions, which does not change
%and the \emph{complete} operation depends on the set, where its recognition started. For non-empty productions this is a bin that has already been fully constructed.
%In the case of an empty production we can get the item \<open>(A \<rightarrow> \<Zspot>, i)\<close>, which points into the current bin $i$. 
%So the set of items resulting of its \emph{completion} is not fully determined during the algorithm for closure.
%This means we have to deal with this special case differently. Some options are presented in \ref{sec:epsilon}.
%To simplify things we will focus on the case where the grammar is epsilon free, meaning it does not contain any productions that derive the empty word.\<close>*)


text (in Earley_Gw_eps)\<open>
\section{Workset Closure}
We keep track of a pair of sets, the workset \<open>B\<close> and the accumulator \<open>C\<close>.
The workset comprises items in the closure that have not yet been considered, while the accumulator keeps track of all previously considered items.
So at any step, \<open>B \<union> C\<close> are all items we know to be in the closure, and it should hold that \<open>B \<inter> C = \<emptyset>\<close>.
One step of this workset algorithm then looks like this:
\begin{itemize}\setlength\itemsep{0.1em}
  \item choose an item from \<open>B\<close> to be considered \<open>b \<in> B\<close>
  \item compute the set of items \<open>D\<close> added by \<open>b\<close> under \emph{Predict} or \emph{Complete}
  \item move \<open>b\<close> from \<open>B\<close> to \<open>C\<close> and add \<open>D\<close> to \<open>B\<close>, while making sure that \mbox{\<open>B \<inter> C = \<emptyset>\<close>} by the end
\end{itemize} 
The last step we do as follows @{term "((B \<union> D) - (C \<union> {b}), (C \<union> {b}))"}.
To formalize this approach, we define a step relation @{const Close2} \mbox{(@{term "Bs \<turnstile> (B, C) \<rightarrow> (B', C')"})} that relates any two such set pairs of workset and accumulator that differ by one step.
\begin{quote}
  {\setlength{\parskip}{0pt}@{const_typ [break] Close2}}\\[\funheadersep]
  Predict : $\inferrule{@{thm (prem 1) Close2_Predict_Th}\\ @{thm (prem 2) Close2_Predict_Th}}
  {@{thm (concl) Close2_Predict_Th}}$\\[1ex]
  Complete : $\inferrule{@{thm (prem 1) Close2.Complete}\\ @{thm (prem 2) Close2.Complete}}
  {@{thm (concl) Close2.Complete}}$
\end{quote}
The closure is then given by the set \<open>C\<close> when repeated steps result in \<open>B = \<emptyset>\<close>. This will always be the case, as the set of valid Earley items is finite.
More on this in \autoref{sec:space}.
Formally, this means we are looking for the accumulator \<open>C\<close> of a set pair \<open>(\<emptyset>, C)\<close> that is reachable from \<open>(B, \<emptyset>)\<close> under the step relation.
 Since this formalization is non-deterministic in the order that items are chosen from the workset, 
we require the Hilbert choice operator for the formalization to get a random but distinct set \<open>C\<close>, if it exists. In reality, this set is unique and always exists. %possibly refer to a lemma about that
\begin{quote}
  @{def close2}
\end{quote}
We again prove equivalence of @{const close2} and @{const Close1}.
\begin{lemma}\,\\[\funheadersep]
  @{thm close2_eq_Close1}
\end{lemma}\<close>

text (in Earley_Gw) \<open>
For this proof, we need two other lemmas. First, that @{const close2} terminates, and second that the result is equal to the set obtained by @{const Close1}.
We will first focus on the set equality. The direction that @{const close2} is a subset of @{const Close1} is simple, 
since the accumulator after one step is always a subset of the final result of @{const Close1}.
The other direction is a bit trickier. We do a proof by induction on the items in @{const Close1} and have to check three cases.
First, the initial items in \<open>B\<close> are also in the result of @{const close2}, which is easily apparent because any item in \<open>B\<close> is moved to \<open>C\<close> at some point.
Second, for the induction step, we have to prove that for any item \<open>x\<close> with @{term "x \<in> Close1 Bs B"} and @{term "x \<in> C"},
 all items obtained by the operations \emph{Predict} or \emph{Complete} on \<open>x\<close> also end up in \<open>C\<close>.
This proof boils down to the observation that if \<open>x\<close> ends up in \<open>C\<close>, there must exist a step in which it is picked from \<open>B\<close> and moved to \<open>C\<close>.
In this step, all items added to @{const Close1} by \<open>x\<close> are also added to \<open>B\<close> in the @{const Close2} step and therefore end up in \<open>C\<close> eventually.

For termination, we define a well-founded potential function that decreases for every step.
It is a lexicographic ordering primarily on the number of well-formed items not in the workset or accumulator,
 and secondarily on the size of the workset. The number of items not in the workset or accumulator decreases whenever an item is added through \emph{Predict} or \emph{Complete}.
 If no new items are added, the workset's size decreases by 1, since one item is always moved to the accumulator.

After proving that the step relation always decreases this potential, we can prove termination of the algorithm and finish the equivalence proof of @{const close2} and @{const Close1}.

\<close>

(*text \<open>
\begin{quote}
  @{fun step_fun}
\end{quote}

- create a closure under Complete and Predict
- scan transitions between sets after full closure
- a natural way to implement this is as a WorkList algorithm
\<close>*)

text (in Earley_Gw) \<open>
\section{Epsilon Treatment} \label{sec:epsilon}
In this section, we discuss different ways of handling grammars that contain epsilon productions.

As a first solution, we can leverage the fact that there exist algorithms that transform any CFG \<open>C\<close> into another CFG \<open>C'\<close> with @{prop "LangS(C') = LangS(C) - {[]}"}.
This has already been formalized in the theory Epsilon\_Elimination\footnote{\href{https://www.isa-afp.org/thys/Context_Free_Grammar/Epsilon_Elimination.html}{https://www.isa-afp.org/thys/Context\_Free\_Grammar/Epsilon\_Elimination.html}} by Martin Stimpfle, where $\isaconst{eps\_elim}$ transforms a grammar into one without epsilon productions and the predicate $\isaconst{Nullable}$, which checks if a non-terminal can derive the empty word.
We can write a wrapper to the Earley recognizer, which runs the recognizer on \<open>C'\<close> if @{prop "w \<noteq> []"}, and checks if \mbox{@{prop "[] \<in> LangS C"}} otherwise.
 While this is a simple solution, it has the drawback that the resulting epsilon-free grammar may be much larger than the original.

Another approach that does not require rewriting the grammar would be to modify the closure algorithm and enable it to handle epsilon productions.
 For this, we suggest changing the \emph{Predict} operation and consequently the \emph{Init} set, as is described in \cite{Aycock2002}.
If there are epsilon productions in a grammar, multiple Nts may derive the empty word @{term "P \<turnstile> [Nt B] \<Rightarrow>* []"} even over multiple steps.

Whenever an item \<open>(A \<rightarrow> \<alpha>B\<Zspot>\<beta>, k)\<close> is added by the \emph{Complete} operation on an item with a from-value equal to the current bin index, the item \<open>(A \<rightarrow> \<alpha>\<Zspot>B\<beta>, k)\<close> must also be in the current bin.
In this case, we can add this item to the set of items added by the \emph{Predict} operation:
\begin{quote}
  @{term "Predict' it i = Predict it i \<union> (if (P \<turnstile> [the (next_symbol it)] \<Rightarrow>* []) then {(mv_dot it)} else {})"}
\end{quote}
This will solve our problem, since the new prediction operation depends only on the set of productions.
This could be made executable using the $\isaconst{Nullable}$ predicate, but
to make it efficient, it would be better to compute the set of Nts that can derive the empty word once using $\isaconst{Nullable}$ and then do a lookup as the if condition.

 

%\begin{itemize}
%  \item do epsilon treatment outside of this Algorithm (is there an isabelle implementation of epsilon removal (constructing L - {$\epsilon$}))
%  \item check which Nts could produce epsilon and change \emph{Predict} to also do epsilon completion for these Nts (would require changing underlying algorithm and doing a lot of proving)
%  \item TODO check literature for different stratagies
%\end{itemize}

\<close>

text\<open>
%\begin{itemize}
  %\item inductive definition lends itself well to first correctness proof
  %\item towards executability we do iterative computation of sets, as earley suggested
  %\item example
  %\item WorkList algorithm for the closure of one set under \emph{Predict} and \emph{Complete}
%\end{itemize}

%\begin{itemize}
%  \item Earley-items
%  \item Inductive Definition
%  \item Soundness
%  \item Completeness
%  \item section about empty word treatment possibilities (modifying Predict)
%\end{itemize}
\<close>
(*<*)
context Earley_Gw
begin

notation diff_list (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation union_list (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation insert_list (\<open>{_} \<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub> _\<close> 65)
notation Close2_L (\<open>\<^latex>\<open>\isaconst{\<close>Close2\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation step_fun_L (\<open>\<^latex>\<open>\isaconst{\<close>step'_fun\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation Init_L (\<open>\<^latex>\<open>\isaconst{\<close>Init\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Predict_L (\<open>\<^latex>\<open>\isaconst{\<close>Predict\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Complete_L (\<open>\<^latex>\<open>\isaconst{\<close>Complete\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Scan_L (\<open>\<^latex>\<open>\isaconst{\<close>Scan\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation ItemList ("\<^latex>\<open>\\isaconst{\<close>IL\<^latex>\<open>}\<close>")

notation set_ItemList (\<open>\<^latex>\<open>\isaconst{\<close>set\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation empty_IL (\<open>\<^latex>\<open>\isaconst{\<close>empty\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation insert  (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation isin (\<open>\<^latex>\<open>\isaconst{\<close>isin\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation union_LIL (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation minus_LIL ("\<^latex>\<open>\\isaconst{\<close>diff\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>LIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation minus_IL (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)

notation inv_IL ("\<^latex>\<open>\\isaconst{\<close>inv\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation wf1_IL ("\<^latex>\<open>\\isaconst{\<close>wf1\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation step_fun (\<open>\<^latex>\<open>\isaconst{\<close>step'_fun\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation steps (\<open>\<^latex>\<open>\isaconst{\<close>steps\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation close2_L (\<open>\<^latex>\<open>\isaconst{\<close>close2\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation bins_L (\<open>\<^latex>\<open>\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
end
(*>*)

text (in Earley_Gw_eps)\<open>
\chapter{Executable List-based Version} \label{chap:List_version}
We can now implement a list-based version. For this, we write list-based implementations of the Earley operations 
and implement the repetition of the closure algorithm using a functional while loop. This version will not be enough to prove the cubic running time guarantees put forth by Earley.
 To that end, we introduce a data structure to efficiently look up items in \autoref{sec:IL_Datastructure}.
We first start by implementing the four Earley operations for lists using the map and filter functions:
\begin{quote}
  @{def Init_L}\\[2.5mm]
  @{const_typ Predict_L}\\[\funheadersep]
  @{thm Predict_L_def[of it]}\\[2.5mm]
  @{const_typ Complete_L}\\[\funheadersep]
  @{thm Complete_L_def[of Bs it]}\\[2.5mm]
  @{const_typ Scan_L}\\[\funheadersep]
  @{thm Scan_L_def[of B k]}
\end{quote}
We then prove equivalence with the set-based versions defined earlier.
\begin{lemma}\,\\[\funheadersep]
  @{thm Init_L_eq_Init}\\[1ex]
  @{thm set_Predict_L[of it]}\\[1ex]
  @{thm set_Complete_L[of it]}\\[1ex]
  @{thm Scan_L_eq_Scan[of k B]}
\end{lemma}
Using the \emph{Predict} and \emph{Complete} operations in conjunction with the set operations on lists, we implement @{const step_fun_L}, which computes one step of the closure and should thus fulfill @{const Close2}.
 For brevity, we introduce the @{const Close2_L} relation, which is a wrapper for the @{const Close2} relation that converts lists to sets.
\begin{quote}
  {\setlength{\parskip}{0pt}@{fun step_fun_L}}\pagebreak\\
  {\setlength{\parskip}{0pt}@{fun Close2_L}}
\end{quote}
The @{const step_fun_L} implementation emulates the @{const Close2} relation, because the list-based Earley operations are equivalent to the set-based operations, and the next state of the worklist algorithm is computed the same way as in @{const Close2}.
\begin{lemma}\,\\[\funheadersep]
  @{thm step_fun_L_sound}
\end{lemma}
\<close>


text (in Earley_Gw) \<open>
We implement the closure using @{const "while_option"} for a functional while loop in conjunction with @{const step_fun_L}.
The @{const "while_option"} construction takes a condition \<open>c\<close>, a body function \<open>b\<close>, and a starting value \<open>s\<close>,
and returns the first value that is a result of repeatedly applying \<open>b\<close> to \<open>s\<close> and violates \<open>c\<close>, if such a result exists.
It can be proven that this is equivalent to the following executable version.
\begin{quote}
  @{thm while_option_unfold[of c b s]}
\end{quote}
Proving predicates about the result of @{const while_option}, assuming that a result exists, requires the predicate to be preserved across applications of the body's function and be valid for the starting value.
Then a simple proof by induction shows that the predicate must hold for the result as well.
\begin{lemma}\,\\[\funheadersep]
  \<open>(\<close>@{thm (prem 1) while_option_rule[of _ c b s]}\<open>)\<close> \<open>\<and>\<close> @{thm (prem 2) while_option_rule[of _ c b s]} 
  \<open>\<and>\<close> @{thm (prem 3) while_option_rule[of _ c b s]} \<open>\<Longrightarrow>\<close> @{thm (concl) while_option_rule[of _ c b s]}
\end{lemma}
\<close>

(*<*)
context Earley_Gw
begin
notation set_ItemList (\<open>\<^latex>\<open>\isaconst{\<close>set\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation steps_L (\<open>\<^latex>\<open>\isaconst{\<close>steps\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation close2_L_Th (\<open>\<^latex>\<open>\isaconst{\<close>close2\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation bins_L_Th (\<open>\<^latex>\<open>\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

fun Close2_IL where
  "Close2_IL Bs (B, C) (B', C') = Close2 (map set Bs) (set_ItemList B, set_ItemList C) (set_ItemList B', set_ItemList C')"
end
(*>*)

text (in Earley_Gw_eps)\<open>
The implementation of the closure then boils down to repeatedly applying @{const step_fun_L} until the worklist is empty, using @{const while_option}.
\begin{quote}
  {\setlength{\parskip}{0pt}@{fun steps_L}}
\end{quote}
To prove equality to the workset-based closure @{const close2}, we prove that the result of the @{const while_option} loop is part of the transitive closure of @{const Close2}
 and that the while loop terminates.

We already proved that the @{const step_fun_L} emulates the @{const Close2} relation.
Proving that the loop result is in the transitive closure uses the proof technique described above. 
We simplify the lemma and the following proof, by ignoring well-formedness requirements. 
\begin{lemma}\,\\[\funheadersep]
  @{thm (prem 3) steps_L_Th_sound1} \<open>\<Longrightarrow>\<close> @{thm (concl) steps_L_Th_sound1}
\end{lemma}
\begin{proof} 
  We start by constructing the predicate we want to prove, that the result of the loop @{term "(B', C')"}
 is in the transitive closure starting from the initial lists @{term "(B, C)"}:\\

  @{term "\<lambda> (B', C'). (Close2_L Bs)^** (B, C) (B', C')"}\\

  Now we have to prove two things: first, that the predicate holds for the starting value, and second, that it holds after the loop body, @{const step_fun}, is applied.\\

  1) @{prop "(Close2_L Bs)^** (B, C) (B, C)"} holds, as this is the reflexive case of the transitive closure.\\
  
  2) We can assume that the proposition holds for \mbox{@{term "(B', C')"}} and have to show that it also holds for \mbox{@{term "step_fun_L Bs (B', C')"}}.
  From the fact that @{const step_fun_L} emulates the relation, we get \mbox{@{term "Close2_L  Bs (B', C') (step_fun_L Bs (B', C'))"}}.\\
  Then \mbox{@{prop "(Close2_L Bs)^** (B, C) (step_fun_L Bs (B', C'))"}} also holds, following from the transitive property of the transitive closure.
\end{proof}
Since the fact that @{const step_fun_L} emulates @{const Close2_L} requires assumptions about
 well-formedness, those also have to be preserved throughout the loop body, making the predicate we construct in the non-simplified proof more complicated, but the underlying argumentation is the same.
Using this and the fact that the worklist of the result must be empty by the loop condition, we can show that the accumulator at the end of @{const steps_L} is part of the transitive closure of @{const Close2_L}.
\begin{lemma}\,\\[\funheadersep]
  @{thm steps_L_Th_sound}
\end{lemma}
Termination is proven the same way as in the set version of the algorithm, using the same lexicographical ordering, adapted to work with lists.

From this, the equivalence of @{const close2_L_Th} and @{const close2} follows.
\begin{lemma}\,\\[\funheadersep]
  @{thm[break,margin=70] close2_L_Th_eq_close2}
\end{lemma}

As a last step, we prove the equivalence of the @{const bins_L_Th} and original @{const bins} functions.
For this, we need to ensure that the bins we compute are well-formed, which requires that the closure result be well-formed.
The closure is well-formed, as all items added come from the Earley operations, which we proved to be well-formed. 

\begin{lemma}\,\\[\funheadersep]
  @{thm bins_L_Th_eq_bins}
\end{lemma}

At this point, we have an executable version of the recognizer, but it does not have the time bounds we want.
 That is because the list-based difference has a quadratic running time and is called on the full bins for every closure step.
 Earley introduces a data structure to speed up the difference operation, which we will present after a short space analysis that lays the foundation for the 
 data structure and the running time analysis.
\<close>

(*should probably be made a section in another chapter*)
text (in Earley_Gw) \<open>
\section{Space Analysis} \label{sec:space}
We do a space analysis based on the length of the word, so we assume the number of productions $\isaconst{L}$ and the maximum length of a production $\isaconst{K}$ are constant.
 To guarantee that the number of productions is equal to the length of the productions list, \isavar{ps}, we require the list to be duplicate-free, using @{term "distinct ps"}.

For the well-formed predicate, we introduced a parameter $\isavar{k}$ that bounds the maximum from-value in a bin. Additionally, we require the items production to be in the set of productions, bounding the number of different options by $\isaconst{L}$.
 The dot has to be a valid index into the rhs of the production, bounding it by $\isaconst{K}$.
 Thus, the size of a well-formed set, and by extension its space, is bounded by the multiplication of all upper bounds.
\begin{lemma}\,\\[\funheadersep]
  @{thm card_wf1[of xs k]}
\end{lemma}
This gives us a simple way to bound the size of any set and bin computed by our algorithm, since we have already proven that well-formedness is preserved throughout the algorithm.
 The size of a list is bounded by the same number, as long as it is distinct, a property guaranteed by list-based set operations and one that must be guaranteed by the implementation of our new data structure.

Since every Earley bin bounds the from-values that can appear in it by its index, the size of each bin grows linearly with its index.
Thus, the overall size is bounded by the sum over all Earley bins, yielding a quadratic total space cost.
\begin{theorem}\,\\[\funheadersep]
  @{thm card_Si}\\[2.5mm]
  @{thm card_Earley}
\end{theorem}
Here, the @{const Earley} set is the one from the formalization that is the union of all Earley bins.
We can also observe that in a well-formed bin, the number of well-formed items for a specific from-value is bounded by a constant (@{term "L * (K+1)"}),
 a fact that will become relevant for the data structure we build in the next section to prove better running time guarantees for the difference operation.
\<close>

text (in Earley_Gw_eps) \<open>
\section{Efficient Itemlist Data Structure for Running Time Guarantees} \label{sec:IL_Datastructure}
We aim to prove the running time analysis given by Earley \cite{Earley1970}. % talk about theory first.
We know from space analysis in \autoref{sec:space} that the size of every Earley bin is linearly proportional to its index.
Earley proposes a way to construct a bin in a time quadratic to its index.
This is not possible using standard list-based set operations, as the difference operation has a quadratic running time and is called a linear number of times for each step of the closure.

The solution described by Earley uses a data structure to achieve item lookup in constant time, enabling a linear-time difference operation.
This data structure stores the entire bin as a partition, with one part for every from-value. As we argued in the space analysis, every part will have a size bounded by a constant.
So if we can access the parts in constant time, we can fully search any one of them in constant time as well. This makes the constant lookup time possible. 
As every Earley bin bounds the from-values of items by its index, we can use an array constructed once at the start of each bin closure to store the parts.
In our implementation, we only use a list to store the parts. We could further refine the data structure by using an array with a functional interface, but this was beyond the scope of this thesis.
Instead, we perform a parameterized running time analysis based on the partition access time, allowing us to prove the running time of the same data structure for different partition access times.

This data structure has type @{type efficientItemList} and will be called @{const ItemList} for short. We use it like a normal list to represent the bins.
In practice, we implement the @{const ItemList} as a normal list and a partition, stored as a list of parts and mirroring the items stored in the list.
\begin{quote}
  @{datatype efficientItemList}
\end{quote}
This type has two projection functions, @{const list} and @{const froms}, to access the list and the list of parts.
 The list provides simple constant-time access to an element in the bin, while the partition is used to access and look up specific elements.
 Since the list and the partition should store the same items, the set represented is simply the set the list represents.
\begin{quote}
  @{fun set_ItemList}
\end{quote}
For the data structure we need an invariant to ensure that the items stored in the list and the partitions are the same,
 so that the lookup operation using the partition is equivalent to the membership test of the set, represented by the @{const ItemList}.
\begin{definition}
  @{fun inv_IL}
\end{definition}
To ensure the validity of the lookup in the partitions, we require that all items can be stored in the reserved partitions, and that
 an item is in the list if and only if it is present in the partition corresponding to its from-value.
We additionally require that both the list and all parts are distinct. This allows us to use the findings from the space analysis to bound their maximum lengths.


We now define the basic operations for this data structure in accordance with the invariant.
 These are the @{const isin}, @{const insert}, and @{const empty_IL}, which correspond to the membership test, insertion, and the empty set constructor.
These are then used to implement the @{const union_LIL} and @{const minus_IL} operations, which are equivalent to their set counterparts, and to convert from type  @{type list} to @{type efficientItemList} using @{const IL_of_List}. 
\begin{quote}
  @{fun isin}\pagebreak\\
  {\setlength{\parskip}{0pt}@{fun insert}}\\[5mm]
  @{const_typ empty_froms}\\[\funheadersep]
  @{thm empty_froms.simps(1)}\\
  @{thm empty_froms.simps(2)}\\[3mm]
  @{def empty_IL}\\[5mm]
  {\setlength{\parskip}{0pt}@{const_typ[break,margin=70] union_LIL}}\\[\funheadersep]
  @{thm union_LIL.simps(1)}\\
  @{thm union_LIL.simps(2)}\\[5mm]
  {\setlength{\parskip}{0pt}@{const_typ[break,margin=80] minus_LIL}}\\[\funheadersep]
  @{thm minus_LIL.simps(1)}\\
  @{thm minus_LIL.simps(2)}\\[3mm]
  {\setlength{\parskip}{0pt}@{const_typ[break] minus_IL}}\\[\funheadersep]
  @{thm minus_IL_def[of il1 il2]}\\[5mm]
  @{def IL_of_List}
\end{quote}
The important details are that the lookup uses the partition to take constant time in an array implementation, that
 there is a check for inclusion before inserting an item, to guarantee distinctness,
 and that we implement the difference operation by inserting into an empty list, making use of the constant-time lookup to check if the item is present in the other @{const ItemList}.
The natural number given as a parameter to @{const empty_IL} and @{const IL_of_List} affects the number of parts in the partition of the 
resulting item list and thus bounds the highest from-value items in this list can have.
We constructed it so that a bin @{term xs} with @{term "wf_bin xs k"} can be stored in an @{term "empty_IL k"}.

All item list functions maintain the invariant and correspond to set functions, provided the items inserted have a from-value that fits within the partition.
 Otherwise, the \emph{nth} and \emph{update} functions are undefined.
In general, we prove given set operation \<open>\<Zspot>\<close> and the corresponding item list operation \<open>\<Zspot>\<close>$_{\isaconst{IL}}$:
\begin{quote}
  $\isaconst{IL\_inv}$ $\isavar{il1}$ \<open>\<Longrightarrow>\<close> $\isaconst{prop}$ $\isavar{x}$ \<open>\<Longrightarrow>\<close> $\isaconst{IL\_inv}$ ($\isavar{il1}$ \<open>\<Zspot>\<close>$_{\isaconst{IL}}$ $\isavar{x}$)\\
  $\isaconst{IL\_inv}$ $\isavar{il1}$ \<open>\<Longrightarrow>\<close> $\isaconst{prop}$ $\isavar{x}$ \<open>\<Longrightarrow>\<close> $\isaconst{set\_IL}$ ($\isavar{il1}$ \<open>\<Zspot>\<close>$_{\isaconst{IL}}$ $\isavar{x}$) $=$ $\isaconst{set\_IL}$ $\isavar{il1}$ \<open>\<Zspot>\<close> $\isavar{x}$
\end{quote}
Depending on whether $\isavar{x}$ is a single item or a set of items, the proposition of $\isavar{x}$ ensures that the from-value of $\isavar{x}$ itself or every item in $\isavar{x}$ is lower than the number of partitions in the item list.

We then proceed to replace the lists in the worklist algorithm with these item lists. The functions do not change much, but to differentiate them from the functions that work with pure lists, they have the subscript $\isaconst{IL}$.
 The proof of correctness then works the same way, with newly added assumptions that must be valid at every step of the algorithm.
These are that the invariant of the item list holds for both the worklist and accumulator, and a predicate about the number of parts reserved in each item list.
This last assumption then requires us to also prove that all operations do not change the number of parts.
\begin{quote}
  \<open>|\<close>\isaconst{froms} \<open>(\<close>$\isavar{il1}$ \<open>\<Zspot>\<close>$_{\isaconst{IL}}$ $\isavar{x}$\<open>)| = |\<close>\isaconst{froms} \<open>(\<close>$\isavar{il1}$\<open>)|\<close>
\end{quote}
We proved, as in the list version, that @{const bins_L} computes the same bins as the set-based @{const bins} function.
And used this equivalence to show that this implementation only recognizes a word if and only if it is in the language.
\begin{theorem}\,\\[\funheadersep]
  @{thm bins_L_eq_bins}\\[2.5mm]
  @{thm[mode=iffSpace] correctness_earley_Th}\\
  where @{const earley_recognized_Th} \text{\upshape checks whether there is a final item in the last bin of} @{term "bins_L (length w)"}.
\end{theorem}

%We can now talk about the $IL\_INVARIANTS$ that we abbreviated in the previous chapter. 
%These are that for every item list the invarriance function described above is fulfilled,
% and that the number of partitions is enough to hold the items generated in the closure steps.

%  quickly touch on invariants

%TODO give a quick example using interpretation and value

%\begin{itemize}
%  \item WorkList Datatype + why requirement for cubic runtime
%  \item WorkList insert intracasies (set bahavior using upsize for ease of theoretical analysis, but isnt used in actual algorithm)
%  \item List-based functions
%  \item correctness by equivalence to inductive set-based WorkListAlgorithm
%  \item WorkList Algorithm with help of while\_option
%\end{itemize}
\<close>
(*\begin{quote}
  @{thm (prem 1) step_fun_sound_il[of B]} \<open>\<Longrightarrow>\<close> @{thm (prem 2) step_fun_sound_il[of B]} \<open>\<Longrightarrow>\<close> @{thm (prem 3) step_fun_sound_il} \<open>\<Longrightarrow>\<close> IL\_INVARIANTS\\
  \mbox{ \<open>\<Longrightarrow>\<close> @{thm (prem 8) step_fun_sound_il[of B Bs C B' C']}}\\
  \mbox{ \<open>\<Longrightarrow>\<close> @{thm (concl) step_fun_sound_il[of B Bs C B' C']}}\\[3mm]
  @{thm (prem 1) steps_sound_il[of B Bs]} \<open>\<Longrightarrow>\<close> @{thm (prem 2) steps_sound_il[of B Bs]} \<open>\<Longrightarrow>\<close> IL\_INVARIANTS\\
  \mbox{ \<open>\<Longrightarrow>\<close> @{thm (prem 7) steps_sound_il[of B Bs C B' C']}}\\
  \mbox{ \<open>\<Longrightarrow>\<close> @{thm (concl) steps_sound_il[of B Bs C B' C']}}\\[3mm]
  @{thm (prem 1) close2_L_eq_close2[of Bs B]} \<open>\<Longrightarrow>\<close> @{thm (prem 2) close2_L_eq_close2[of Bs B]} \<open>\<Longrightarrow>\<close> IL\_INVARIANTS\\
  \mbox{ \<open>\<Longrightarrow>\<close> @{thm (concl) close2_L_eq_close2[of Bs B]}}
\end{quote*)

(*<*)
context Earley_Gw_eps_T
begin
notation T_nth_IL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>nth\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_list_update (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>list'_update\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_nth (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>nth\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_step_fun (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>step'_fun\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_steps (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>steps\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_close2_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>close2\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_bins_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_earley_recognized1 (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>earley'_recognized\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_Init_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>Init\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_Predict_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>Predict\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_Complete_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>Complete\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_Scan_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>Scan\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation T_empty_IL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>empty\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_isin (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>isin\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_insert (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_union_LIL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_minus_IL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
(*notation T_Parse_step_fun
notation T_Parse_steps
notation T_Parse_close2_L
notation T_Parse_bins_L
notation T_get_parse_tree
notation T_get_parse_tree_w

notation T_empty_PIL
notation T_PIL_list
notation T_parseIL_isin
notation T_parseIL_insert
notation T_PIL_first
notation T_union_LPIL
notation T_minus_LPIL
notation T_minus_PIL
notation T_PIL_of_List

notation T_Parse_Predict_L
notation T_Parse_Complete_L
notation T_Parse_Scan_L*)
end
(*>*)

text (in Earley_Gw_eps_T) \<open>
\chapter{Running Time Analysis} \label{chap:Runingtime_1}
We now begin a formal running time analysis based on the length of the word, so we assume, as in the space analysis, that the number of productions $\isaconst{L}$ and the maximum length of a production $\isaconst{K}$ are constant.
 Our goal is to verify the guarantees put forth by Earley. 
He claims an overall running time of $O(n^3)$. As we mentioned before, we will perform a parameterized running time analysis based on the random-access time of the parts stored in the partition of the item lists.
We specifically assume that both the \emph{nth} and \emph{update} operations for the parts list are bounded by the same running time function @{term "T_nth_IL"}, which is monotone increasing.
As both the \emph{nth} and \emph{update} operations boil down to a random lookup, we bound them by the same function, while monotonicity is needed to aggregate different calls.
And both of these assumptions are satisfied by our current list-based partition implementation, which has linear running time for the operations, and by the optimal array implementation, which would guarantee constant running time for both operations.
\begin{quote}
  @{thm T_list_update_general}\\[3mm]
  @{thm (concl) T_nth}
\end{quote}
For the analysis, we use the built-in \<open>time_fun\<close> command in Isabelle, which automatically generates a timing function for a given function.
The timing functions generated this way count non-primitive function calls. Other operations, like arithmetic computation, variable access, or datatype construction, are assumed to take no time. 
This approach provides time bounds in the correct $O$-class, while simplifying the reasoning as much as possible and allowing inductive proofs. A more detailed explanation of the implementation of the automatic timing functions can be found in \cite{2025}.
The only exception where automation fails is the @{const steps} function, which is currently not supported by \<open>time_fun\<close> due to the @{const while_option} loop, for which there is no automatic termination proof.

We give one example of how the generated timing functions look using @{const union_LIL} as an example.
\begin{quote}
  @{const_typ T_union_LIL}\\[\funheadersep]
  @{thm T_union_LIL.simps(1)}\\
  @{thm T_union_LIL.simps(2)}
\end{quote}
The base case simply returns the given item list resulting in a time of 1 for the application of the function itself.
The recursion case is defined as the time taken for the recursive function call plus the insert plus one for the function call itself again.
\\

For brevity, we will only show the time bounds without any assumptions, as they are the same as in the correctness proofs.
When discussing time bounds in the text, we assume a constant running time for @{term "T_nth_IL"} and elaborate on implementations with other access time assumptions only for the final time bounds of the complete algorithm.

\section{Efficient Itemlist}
We start by proving running time bounds for the operations of @{type efficientItemList}.
The basic operations of lookup (@{const isin}) and insertion @{const insert} are the only places where the assumed time bounds for \emph{nth} and \emph{update} are needed directly.
 All other functions use @{const isin} and @{const insert}.
\begin{quote}
  @{thm (concl) T_isin_wf}\\[3.5mm]
  @{thm (concl) T_insert_less}
\end{quote}
We see that these functions have a constant running time, since they only need to perform a lookup and then search the corresponding partition.
Then the running times of the union and difference operations are linear in the length of the list, since they perform either a single lookup or both a lookup and an insert per list element.
\begin{quote}
\begin{tabularx}{\textwidth}{l c X}
@{thm (lhs) T_union_LIL_wf} & @{text "\<le>"} & @{thm (rhs) T_union_LIL_wf}\\[3mm]
@{thm (lhs) T_minus_IL_wf_Th[of il1 il2]}&@{text "\<le>"}&@{thm (rhs) T_minus_IL_wf_Th[of il1 il2]}
\end{tabularx}
\end{quote}
The difference operation has an additional linear addend in the number of parts in its partition, stemming from the @{const empty_IL} time bound, which is linear in the number of parts it has to construct for the empty partition.
 In the full algorithm analysis, the list size equals the bin size, and the number of parts equals the index of the bin currently under construction.
 As the bin size grows linearly with its index, both addends will also grow linearly with the bin index.
 Lastly, we have the conversion from lists to item lists, @{const IL_of_List}, which is a simple combination of the @{const empty_IL} and @{const union_LIL} operations and will therefore also be linear.

\section{Earley Algorithm}
For the four Earley operations, both the \emph{Init} and \emph{Predict} operations depend only on the number of productions and therefore take constant time.
The \emph{Complete} and \emph{Scan} operations depend on the size of the bin they have to filter, resulting in a time bound that is linear in the bin's size.
Since every Earley bin is well-formed it has a size linear to its index, and the \emph{Complete} and \emph{Scan} operations are also linear in the index of the bin for which the closure is being computed. 
\begin{quote}
  @{thm T_Init_L_bound}\\[3.5mm]
  @{thm (concl) T_Predict_L_bound}\\[3.5mm]
  @{thm (concl) T_Complete_L_bound}\\[3.5mm]
  @{thm (concl) T_Scan_L_bound[of k B]}
\end{quote}

Putting these time bounds together with those for the efficient item list, we find that the @{const step_fun} time bound is also linear in the index of the current bin. 
This mostly follows directly from the time bounds given and the assumption that the item lists are well-formed and satisfy the invariant @{const inv_IL}, which requires that the lists be distinct.
 Distinctness allows us to get length bounds on these lists equal to the sizes of well-formed bins, which are linear in their indices.

We now come to the while loop implementation of the closure for which we had to write a custom timing function.
 Our timing function performs the normal computation and maintains a timing accumulator throughout.
The accumulator of the result then gives the total running time of the while loop, if it exists.\vspace{3.5mm}
\begin{quote}
  {\setlength{\parskip}{0pt}@{const_typ[break,margin=100] steps_time}\\[\funheadersep]
  @{thm[break,margin=100] steps_time.simps}\\[3.5mm]
  @{fun T_steps}}
\end{quote}\vspace{3.5mm}

The size of the list accumulator increases by one every iteration, as one item is moved from the worklist to the accumulator,
 and so we can bound the entire closure algorithm by the size of the accumulator times the time bound for a single step.
This time bound is the predicate we use in our proof about the while loop's result.\vspace{2.5mm}
\begin{quote}
  @{term "(\<lambda>((il1,il2),k). k \<le> length (list il2) * T_step_fun_bound_Th_def)"}
\end{quote}\vspace{2.5mm}

Here, @{term "T_step_fun_bound_Th_def"} is simply an abbreviation for the full numeric time bound.
Again, we have to augment this predicate with the other assumptions about well-formedness and invariants, but the core of the proof is about showing that this inequality holds.
We can again bound the length of the accumulator to be linear by well-formedness and distinctness, so we get a quadratic running time for @{const T_steps}.
The time bound for the full closure, @{const close2_L}, adds only a linear term for creating an empty item list and is therefore also quadratic.\vspace{2.5mm}
\begin{quote}
\begin{tabularx}{\textwidth}{lcX}
  @{thm[break] (lhs) T_close2_L_bound_Th_nice} & @{text "\<le>"} & @{thm[break] (rhs) T_close2_L_bound_Th_nice}
\end{tabularx}
\end{quote}\vspace{2.5mm}

Lastly, we bound the running time of the @{const bins_L} function and the top-level predicate, @{const earley_recognized}.
Since @{const bins_L} computes a linear number of bins, each with a quadratic time bound, the overall time bound is cubic.
We show a simplified time bound, but there exists another with tighter constants.\pagebreak
\begin{theorem}\,\\[\funheadersep]
  @{thm (concl) nice_T_bins_L_bound}\\[2.5mm]
  @{const T_earley_recognized1} \<open>\<le>\<close> @{thm (rhs) T_earley_recognized_nice}\\[2.5mm]
  @{thm C1_def} \hspace{5mm} @{thm C1'_def}\\
  @{thm C2_def}
\end{theorem}

From the total parameterized running time, we see that if we set the random-access time to be constant, we do indeed obtain a cubic running time, as we argued in the text.
If we instead take our current list-based implementation, we get a running time of $O(n^4)$ instead.
 This concludes the asymptotic analysis of the recognizer, where we have verified the time bound given by Earley, assuming a constant access time for the parts stored in the item list data structure.

%\begin{itemize}
%  \item analysis with WorkList T\_nth parameter (assumed to be constatnt for array)
%  \item WorkList insert requires WorkList map\_length bound, which has to be carried through proofs
%  \item runtime of list functions
%  \item parametized runingtime (cubic if T\_nth is constant)
%\end{itemize}
\<close>

(*<*)
context Earley_Gw
begin

definition parseItem_for_Typedef :: "('n,'t) parseItem" 
  where "parseItem_for_Typedef = ((Earley.Item (hd (ps)) 0 0),([] :: ('n,'t) tree list))"

notation Parse_Init (\<open>\<^latex>\<open>\isaconst{\<close>Init\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_Predict (\<open>\<^latex>\<open>\isaconst{\<close>Predict\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_Complete (\<open>\<^latex>\<open>\isaconst{\<close>Complete\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_Scan (\<open>\<^latex>\<open>\isaconst{\<close>Scan\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation Parse_Close (\<open>\<^latex>\<open>\isaconst{\<close>Close\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_bins (\<open>\<^latex>\<open>\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
end


(*>*)

text (in Earley_Gw_eps) \<open>
\chapter{Expansion to Parse Trees} \label{chap:Parse_trees}
We now turn this recognizer into a parser. For each item, we save parse trees that make up the derivation that is represented by the item.
The way we do this is by creating a pair of an Earley item and a list of parse trees, with access functions @{const item} and @{const trees}.
\begin{quote}
  @{type parseItem} @{text "::"} @{typeof parseItem_for_Typedef}
\end{quote}\<close>

(*<*)
context Earley_Gw
begin
translations (type) "('n, 'a) parseItem" <= (type) "('n, 'a) Earley.item \<times> ('b, 'c) tree list"
translations (type) "('n, 'a) parseIL" <= (type) "('n, 'a) efficientItemList \<times> ('b, 'c) tree list list"
end
(*>*)
text (in Earley_Gw_eps)\<open>
The intention is that the item represents the derivation of a substring of $\isaconst{w}$ from the symbols left of the dot, and that the list of trees stores this derivation by having one parse tree for every symbol up to the dot, holding part of the derivation.
Thus, if the item is complete with the dot at the end of the production, we can create a complete parse tree for this item
 by creating a new @{const Rule} node from the lhs of the production and all saved trees as its children.

The following invariant models the internal consistency between the item and the tree list. It makes sure that every parse tree is constructed correctly, 
 that the leaves of the parse trees form the slice of $\isaconst{w}$ which can be derived from the production up to its dot, 
 and that the roots of the parse trees are the symbols present in the production's rhs up to its dot. 
In a complete item, the roots of the trees must make up the production's rhs, as otherwise we would be constructing a parse tree, where the new @{const Rule} node does not represent a valid production.
 The parse trees in the list are stored in reverse order, since this makes insertions of new trees more convenient during the algorithm.
\begin{definition}
  @{const_typ wf_parseItem1}\\[\funheadersep]
  @{thm[break] (eta_expand t) wf_parseItem1.simps[unfolded \<alpha>_def]}
\end{definition}

Similarly to the recognizer, we have created both a set-based and a list-based parser. We begin by introducing the set-based parser.

The overall structure is again similar to the recognizer. We compute parse bins @{term "parseBin i"} using a @{const bins} function in conjunction with an inductive closure.
So we need to augment the Earley operations to also construct the tree lists for every parse item.
\begin{quote}
{\sc Init$_P$}: $\inferrule{@{thm (prem 1) PInit_Th} \\
  @{thm (prem 2) PInit_Th}}{@{thm (concl) PInit_Th}}$\\[3mm]
{\sc Predict$_P$}: $\inferrule{@{thm (prem 1) PPredict_Th} \\
  @{thm (prem 2) PPredict_Th}\\
  @{thm (prem 3) PPredict_Th}}{@{thm (concl) PPredict_Th}}$\\[3mm]
{\sc Complete$_P$}: $\inferrule{@{thm (prem 1) PComplete_Th} \\
  @{thm (prem 2) PComplete_Th}\\ @{thm (prem 3) PComplete_Th}\\\\
  @{thm (prem 4) PComplete_Th}\\ @{thm (prem 5) PComplete_Th}\\
  @{thm (prem 6) PComplete_Th}}{@{thm (concl) PComplete_Th}}$\\[3mm]
{\sc Scan$_P$}: $\inferrule{@{thm (prem 1) PScan_Th} \\
  @{thm (prem 2) PScan_Th}\\
  @{thm (prem 3) PScan_Th}}{@{thm (concl) PScan_Th}}$
\end{quote}
In the \emph{Init} and \emph{Predict} operations, we start parsing a new substring, so we do not need to store any parse trees.
The \emph{Scan} operation directly parses a terminal symbol, which itself makes a complete parse tree, so we add it to the list of parse trees.
In the \emph{Complete} operation, we have completed parsing a substring, so we construct a complete parse tree for this substring by creating a @{const Rule} node from the production's lhs and all of the child parse trees.
This new tree is then added to all parse items, in which we advance the item's dot and thereby extend the derivation represented by the item. 

We implement functions returning sets by applying these operations to a single parse item. They are similar to the ones in the recognizer, but with more complicated parse item constructions.
We show the Scan function as an example.\vspace{1mm}
\begin{quote}
  {\setlength{\parskip}{0pt}@{def Parse_Scan}}
\end{quote}
All of the operations fulfill the well-formed predicate, by how we defined them.
 With the implementations of the operations, we define an inductive set closure, @{const Parse_Close}, similar to @{const Close1} in the recognizer case, and then use that to construct all parse bins again as we did prior.
\begin{quote}
  @{const_typ Parse_bins}\\[\funheadersep]
  @{thm Parse_bins.simps(1)}\\
  @{thm Parse_bins.simps(2)[rename_abs Bs]}
\end{quote}
Lastly, we have to retrieve the full parse tree from a \emph{final} item in the last bin.
\begin{definition}
  @{def get_parse_tree_set}
\end{definition}
This top-level function returns a tree if a final item exists, and then constructs the complete parse tree from a completed parse item, just as the \emph{Complete} operation.
We need to use the Hilbert choice operator because multiple parse trees may exist for an item when the productions are ambiguous.

We now go on to prove correctness in two steps. First, we prove that any tree returned by our algorithm represents a valid derivation of $\isaconst{w}$ from $\isavar{S}$ under the given productions.
Second, we prove that our algorithm returns a parse tree if and only if $\isaconst{w}$ can be derived.

For the first claim, we have to prove that the parse bins we compute are well-formed, which then implies that every returned parse tree is valid.
 The only parse items added during the closure come from the Earley operations, which only return well-formed items, so all items in the closure and thus the bins will also be well-formed.
\begin{lemma}\,\\[\funheadersep]
  @{thm parse_bins_wf1}\\[2.5mm]
  @{thm get_parse_tree_set_valid} 
\end{lemma}
To tackle the second claim, we use the fact that the parser operations are only an augmentation of the recognizer operations. We do not change the items generated for each bin; we only add trees to them.
 Thus, we can prove that projecting the parse items in a bin to only their item parts yields the same bins as those computed by the recognizer algorithm.
\begin{lemma}\,\\[\funheadersep]
  @{thm item_Pbins_eq_bins}
\end{lemma}
Using this and the correctness of the recognizer we can prove correctness of the parser as follows:
\begin{theorem}\,\\[\funheadersep]
  @{thm[mode=iffSpace] get_parse_tree_set_iff}
\end{theorem}
\begin{proof}\,\\
  @{term "\<exists> t. get_parse_tree_set = Some t"} \<open>\<longleftrightarrow>\<close>\\
  @{term "\<exists>it ts. (it,ts) \<in> (last (Parse_bins (length w))) \<and> is_final it"} \<open>\<longleftrightarrow>\<close>\\
  @{term "\<exists>it. it \<in> last (bins (length w)) \<and> is_final it"} \<open>\<longleftrightarrow>\<close>\\
  @{term "P \<turnstile> [Nt S] \<Rightarrow>* w"}
\end{proof}
\<close>

(*<*)
(*To tackle the second claim, we use the fact that we have already proven that we recognize an item if and only if a derivation exists, which is equivalent to the existence of a final item in the last bin.
 Since the parser operations are only an augmentation of the recognizer operations, we do not change the items generated for each bin; we only add trees to them.
 Thus, we can prove that projecting the parse items in a bin to only their item parts yields the same bins as those computed by the recognizer algorithm.
 By extension, a final item is only present in the last parse bin if a derivation exists, and we only return a tree if this is the case, so our claim is true.
\begin{theorem}\,\\[\funheadersep]
  @{thm item_Pbins_eq_bins}\\[3mm]
  @{thm[mode=iffSpace] get_parse_tree_set_iff}
\end{theorem}*)

(*@{def Parse_Init}\\[3mm]
  @{def Parse_Predict}\\[3mm]
  @{def Parse_Complete}\\[3mm]
  @{def Parse_Scan}*)

context Earley_Gw
begin
no_translations (type) "('n, 'a) parseItem" <= (type) "('n, 'a) Earley.item \<times> ('b, 'c) tree list"
no_translations (type) "('n, 'a) parseIL" <= (type) "('n, 'a) efficientItemList \<times> ('b, 'c) tree list list"

definition paresIL_for_Typedef :: "('n, 't) efficientItemList \<times> ('n, 't) tree list list"
  where "paresIL_for_Typedef = (empty_IL 0, [[]])"

fun unzip :: "('n, 't) parseItem list \<Rightarrow> ('n, 't) item list \<times> ('n,'t) tree list list"
  where "unzip xs = undefined"
end
(*>*)

text (in Earley_Gw) \<open>
\section{List-based Parser}
We now proceed to construct an executable list-based parser.
We mentioned that for ambiguous grammars, an item may have multiple valid parse trees representing its derivation. 
The number of these and thus the number of parse items is not nicely linearly bounded by the bin's index. So if we computed all parse items we could not give very good time bounds.
 That is why we only save one derivation per Earley item and thus we save only one parse item per Earley item.
 This is different from the set version, where we did not specify such a constraint.

So we will be working with parse item lists, where each Earley item appears only once, which will give us the same length bounds for bins as in the recognizer case.
 To store such lists we do not write a new efficient item list for parse items, but instead we "unzip" the
 @{typ "('n,'t) parseItem list"} into a @{typ "('n,'t) item list"} and a \mbox{@{typ "('n,'t) tree list list"}}, where entries at the same index in both lists form a parse item in the original list.
 Then we can store the item list as an efficient item list, and the tree list list as is.
 The augmented parse item list ($\isaconst{PIL}$) then looks like this.
\begin{quote}
  @{type parseIL} @{text "::"} @{typeof paresIL_for_Typedef}
\end{quote}
\<close>

(*<*)
context Earley_Gw
begin
translations (type) "('n, 'a) parseItem" <= (type) "('n, 'a) Earley.item \<times> ('b, 'c) tree list"
translations (type) "('n, 'a) parseIL" <= (type) "('n, 'a) efficientItemList \<times> ('b, 'c) tree list list"

notation inv_PIL (\<open>\<^latex>\<open>\isaconst{\<close>inv\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation set_PIL (\<open>\<^latex>\<open>\isaconst{\<close>set\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation wf_PIL (\<open>\<^latex>\<open>\isaconst{\<close>wf\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation isin_PIL (\<open>\<^latex>\<open>\isaconst{\<close>isin\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation insert_PIL  (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation hd_PIL (\<open>\<^latex>\<open>\isaconst{\<close>hd\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation Parse_bins_L (\<open>\<^latex>\<open>\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

notation Parse_Predict_L (\<open>\<^latex>\<open>\isaconst{\<close>Predict\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P,L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
end
(*>*)
text (in Earley_Gw_eps) \<open>
The parse item set represented by this data structure is obtained by zipping both lists.
\begin{quote}
  @{fun set_PIL}
\end{quote}

The semantic requirements for a valid parse item list are that the projection onto items is distinct,
 that the item list and tree list list have equal length, and that items and tree lists stored at the same index form a valid parse item.
 To capture the first two semantic requirements for the parse item list, we define a new invariant
 that reuses the efficient item list's invariant and ensures that the efficient item list and the tree list list are the same length for the zipping operation.
 The item list invariant already contains that the projected parse item list is distinct.
 The third semantic requirement is satisfied if the zipped set representation is well-formed.
\begin{definition}
  @{fun inv_PIL}\\[3mm]
  @{fun wf_PIL}
\end{definition}

The interesting operations on the parse item list are @{const isin_PIL} and @{const insert_PIL}. 
For the membership test, we only consider the Earley item part, while insertion boils down to insertion into the item list and the tree list.
We also introduce the new function @{const hd_PIL}, which returns the parse item at the head of the list, which is no longer easily achievable through pattern matching.
\begin{quote}
  @{fun isin_PIL}\\[3mm]
  @{fun[break, margin=100] insert_PIL}\\[3mm]
  @{fun hd_PIL}
\end{quote}
The other operations for the parse list are defined the same way as the item list's, using the adapted @{const isin_PIL} and @{const insert_PIL} operations.

We adapt the set-based \emph{Init}, \emph{Predict}, \emph{Complete}, and \emph{Scan} operations to work with lists.
Then we again define a step function and closure as before, and finally use that to compute all parse bins.
As a last step, we have to return the parse tree of a final item in the last bin, if such an item exists. This will then be a parse tree for the complete word.
\begin{definition}
  @{const_typ get_parse_tree}\\[\funheadersep]
  @{thm get_parse_tree.simps(1)}\\
  @{thm[break] get_parse_tree.simps(2)}\\[3mm]
  @{const parse_tree_w} \<open>\<equiv>\<close> @{thm (rhs) parse_tree_w_abbrev}
\end{definition}

Since we have introduced the constraint that we only save one parse item per Earley item, we cannot prove the equivalence to the set-based parser.
 Instead we can prove that the efficient item list in the parse item list is the same as the item list computed in the recognizer algorithm.
 In conjunction with proving that the list implementations of the Earley operations projected onto items are also the same, we can prove that the projection of parse bins onto the items is the same as the bins computed for the recognizer.
As examples, we show equality of the \emph{Predict} operation and the \emph{bins} function:
\begin{lemma}\,\\[\funheadersep]
  @{thm PPredict_L_eq_Predict_L}\\[2.5mm]
  @{thm Parse_bins_L_eq_bins_L}
\end{lemma}
Additionally, we show that the computed parse bins are well-formed, as we have done before. 
Using the equivalence to the recognizer, we can then show, similarly to the set-based parser algorithm, that our algorithm returns a parse tree only if the word is in the language,
 and that any parse tree it returns is valid under the productions.
Thus, our algorithm returns only valid parse trees and only if the word is in the language.
\begin{theorem}\,\\[\funheadersep]
  @{thm[mode=iffSpace] find_parse_tree_iff_w_in_L_Th}\\[2.5mm]
  @{thm generated_parse_tree_is_valid_Th}
\end{theorem}

As a simple corollary, we get that if the grammar is unambiguous, we return the singular correct tree, and that the set-based and list-based parsers are equal.
\begin{corollary}\,\\[\funheadersep]
  @{thm[break,margin=90,mode=iffSpace] unambiguous_impl_the_parse_tree_Th}\\[2.5mm]
  @{thm[break,margin=70] unambiguous_impl_P_set_eq_P_L_Th}
\end{corollary}

%\begin{itemize}
%  \item set version which does not require only one tree per Earley item
%  \item parse items and well-formedness characterisation
%  \item list version for executability
%  \item in many ways similar proof to first version
%\end{itemize}
\<close>

(*<*)
context Earley_Gw_eps_T
begin
notation T_Parse_Complete_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>Complete\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>P,L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_insert_PIL (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_Parse_bins_L (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>bins\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>PIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation T_get_parse_tree_w (\<open>\<^latex>\<open>\isaconst{\<close>T\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>parse'_tree'_w\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
end
(*>*)

text (in Earley_Gw_eps_T) \<open>
\section{Runing Time Analysis of Parsing Algorithm} \label{sec:Runingtime_2}

The running time analysis works very similarly to the one for the recognizer. 
One big difference is that in the recognizer, we could make assumptions about the size of all well-formed bins, whereas the @{const wf_parse_bin} predicate does not allow for the same bounds.
 We only have the same size bounds if the bin was computed using a $\isaconst{PIL}$ that fulfills its invariant, as that guarantees that the projection onto the items is distinct.
So if we only know that a bin is well-formed we have to introduce an assumption about the size of that bin being bounded by some variable.

In the end, this bound is resolved in the analysis of the @{const Parse_bins_L} method, where we can finally show that all bins are computed using a $\isaconst{PIL}$ and have the same bound as in the recognizer.
For example, for the time bound of the \emph{Complete} operation, we introduce the assumption that the bin size is bounded by $\isavar{C}$ \mbox{(@{thm (prem 4) T_Parse_Complete_L_bound})} and obtain this time bound. We do not show other assumptions about well-formedness and invariants for readability.
\begin{quote}
  @{thm (prem 4) T_Parse_Complete_L_bound} \<open>\<Longrightarrow>\<close>\\ @{thm (concl) T_Parse_Complete_L_bound}
\end{quote}

Overall, the time bounds are very similar to those of the recognizer, since the parsing functions follow the same scheme and we reuse item list operations in the definition of the parse item list operations.
 One difference appears in the insert operation of the parse item list, since both the parse item list and the item list perform inclusion checks during insertion.
 One of these could be removed for optimization, but was left in, as it does not change the overall time bound. 
If we compare the bounds of both operations, we see that they differ by @{term "T_nth_IL (from x) + L * (K + 1) + 1"}, which is the bound for @{const isin}.\\
\\
\begin{tabularx}{\textwidth}{l c X}
  @{thm (lhs) T_insert_less} & \<open>\<le>\<close> & @{thm (rhs) T_insert_less}\\
  @{thm (lhs) PIL_T_insert_bound} & \<open>\<le>\<close> & @{thm (rhs) PIL_T_insert_bound}
\end{tabularx}\\
\\
This difference then affects all other parse list running times as well, as they all use @{const insert_PIL}.
 Another difference is that the @{const Parse_Complete_L} operation takes more time than the recognizer operation,
 since it has to reverse the tree list attached to the item to build a valid parse tree for the completed item.
 The running time of the inefficient list reversal is @{term "mbox (2 * K * K + 2 * K + 5)"} and may be incurred for every item in the bin.
Again, we could use a more efficient list reversal using an accumulator, but it does not change the overall asymptotic running time, as both are constant in the size of the word.

The end result is that while the asymptotic running time stays the same as in the recognizer case, the prefactors change.
\begin{lemma}\,\\[\funheadersep]
\begin{tabularx}{\textwidth}{lcX}
  @{thm (lhs) T_Parse_bins_bound_nice_Th} & \<open>\<le>\<close> & @{thm[break] (rhs) T_Parse_bins_bound_nice_Th}
\end{tabularx}\\[1ex]
  @{thm C3_def}\\
  @{thm C4_def}\\
  @{thm C5_def}\\
  @{thm C6_def}\\
  @{thm C7_def}
\end{lemma}
Combining this with the running time for the extraction of the final tree gives us:
\begin{theorem}\,\\[\funheadersep]
\begin{tabularx}{\textwidth}{lcX}
  @{const T_get_parse_tree_w} & \<open>\<le>\<close> & @{thm[break] (rhs) T_ovrall_time_bound_Th}
\end{tabularx}\\[1ex]
  @{thm C8_def}
\end{theorem}

%\begin{itemize}
% \item same O runingtime as version without (different prefactors)
%\end{itemize}
\<close>

text \<open>
\chapter{Related Work}\label{chap:related}

Lasser formalizes two parsers based on the LL(1) and All(*) algorithm approaches using the Coq proof assistant \cite{lasser2022formal}.
 They prove soundness and completeness of both parsers, as well as termination, as long as the grammars are LL(1) or non-left-recursive, respectively.
 Instead of proving a formal running time bound they measure the parsers' practical performance through empirical tests.
 Finally, they augment their All(*) parser to handle grammars with semantic predicates, which are checked during parsing to ensure the input is semantically well-formed.\\

Another work tackling the LL(1) parser is by Edelmann et. al. \cite{Edelmann2020}. Their approach uses derivatives of formal languages. They use a zipper-inspired data structure to achieve a linear running time algorithm.
 Their work encompasses formal verification in Coq, including termination and correctness proofs, as well as an implementation in Scala.\\

Firsov and Uustalu verify a parser based on the CYK algorithm in Agda \cite{Firsov2014}.
 Their work encompasses correctness and termination proofs, assuming the grammar is in Chomsky-Normal Form.\\

Koprowski and Binsztok verify a parser for parsing expression grammars (PEGs) in Coq \cite{Koprowski2011}.
 They prove correctness and termination by first inspecting the grammar and rejecting those that would not lead to termination.
 On running time, they mention that their algorithm may take exponential time on grammars that are not LL(k).
 A solution to this problem that trades a linear running time for higher space requirements is the packrat parsing approach using memoization.
 A formal verification of such a PEG parser has been performed by Blaudeau and Shankar \cite{Blaudeau2020} in PVS.\\

Another approach is used by Jordan et al., who write a validator for LR(1) parsers in Coq \cite{Jourdan2012}.
 The validator takes a CFG and an otherwise generated parser and validates that the parser works correctly for the given grammar.
 One aspect that is not verified is that the given parser terminates for invalid input. 
 This validation approach has the benefit of verifying the output of optimized, already existing parser generators and could thus be incorporated into those, guaranteeing correctness.
 Thus, this approach can be used with a variety of parser generators, without having to prove correctness of each one individually.

\<close>

text \<open>
\chapter{Conclusion and Future Work}
In this thesis, we refined the prior work done by Nipkow and Rau on the Earley algorithm into an executable list-based recognizer.
 The recognizer was proven correct for all epsilon-free grammars and could be adapted to work on those as well, as outlined in \autoref{sec:epsilon}.
 We also prove termination in all cases. For running time guarantees, we implemented the \mbox{@{typ "('n,'t) efficientItemList"}} data structure proposed by Earley.
 Using a parameter for the random-access time of the partition in this data structure, we conducted an asymptotic running time analysis, verifying a cubic running time under constant access time.
 Our list-based implementation achieves only an $O(n^4)$ running time instead.\\

We then verified both a set-based and a list-based parser using this algorithm. 
 Both algorithms are correct and always terminate for epsilon-free grammars, and were proven to be equivalent if the grammar is unambiguous.
 In the case of an ambiguous grammar, our algorithm returns only one random parse tree. 
 The running time analysis resulted in the same asymptotic time bounds as the recognizer.\\

For future work, we see a possibility in replacing the list used in the partition in the \mbox{@{typ "('n,'t) efficientItemList"}} datatype by an actual array implementation, as this would guarantee the best running time bounds for this algorithm.
 Another avenue is to formalize the treatment of grammars containing epsilon productions using one of the approaches outlined in \autoref{sec:epsilon}.\\

Earley also presents sets of languages for which the algorithm has a better running time bound, which could be of interest.
 Unambiguous reduced grammars could have quadratic running time because the set-difference operation can be omitted.
 There are also grammars for which the size of each Earley bin is bounded by a constant, leading to linear running time.
 Earley mentions that most LR(k) grammars fall under this, but does not give a characterization of exactly which.
 Fully characterizing this set of grammars and verifying their linear running time is also an interesting direction.\\

Lastly, CFGs can be extended to give certain productions higher priority when multiple apply, resolving ambiguity.
 This feature is used in many programming languages as well, so an extension to these would be great, but would require a full extension of the derivation infrastructure for CFGs.

%\begin{itemize}
%  \item make it truly cubic runtime by repacing list with array
%  \item formalize algorithm for turning Productions epsilon free to cover that edge case
%  \item addapt to priority grammars in a step to make programm language parsing more achievable
%\end{itemize}
\<close>

(*------------------------------------------------------------------------------------------------*)

(*<*)
end
(*>*)