section \<open>Earley's Recognizer\<close>

theory Earley_Recognizer
imports
  "Earley"
  "HOL-Library.While_Combinator" 
begin

(* TODO: IL verification relates back to inductive Close2 but should use recursive close2L *)

subsection \<open>IL definiton and functions\<close>

datatype ('n,'t) item_list = 
  IL ("list": "('n,'t) item list") ("froms" : "('n,'t) item list list")

fun inv_IL :: "('n, 't) item_list \<Rightarrow> bool" where
"inv_IL (IL as fs) = ((\<forall>x \<in> set as. from x < length fs) 
                            \<and> (\<forall>i < length fs. set (fs ! i) = {x \<in> set as. from x = i}) 
                            \<and> (\<forall>i < length fs. distinct (fs ! i)) 
                            \<and> distinct as)"

type_synonym ('n,'t) item_list2 = "('n,'t) item_list * ('n,'t) item_list"

context Earley_Gw
begin

(* Could pull out the definitions and lemmas about \<open>item_list\<close>.
   But they would be polymorphic and not with fixed 'n and 't as currently.
   Such polymorphic lemmas break some existing proofs because type variables need to be instantiated.
   One would need to specialize the type variables manually.
*)


fun set_IL :: "('n, 't) item_list \<Rightarrow> ('n, 't) item set" where
"set_IL il = set (list il)"

fun isin_IL :: "('n, 't) item_list \<Rightarrow> ('n, 't) item \<Rightarrow> bool" where
"isin_IL (IL as fs) x = isin_list (fs ! from x) x"

fun empty_froms :: "nat \<Rightarrow> ('n, 't) item list list" where
"empty_froms 0 = [[]]"|
"empty_froms (Suc k) = []#empty_froms k"

definition empty_IL :: "nat \<Rightarrow> ('n, 't) item_list" where
"empty_IL k = (IL [] (empty_froms k))"

fun insert_IL :: "('n, 't) item \<Rightarrow> ('n, 't) item_list \<Rightarrow> ('n, 't) item_list" where
"insert_IL x (IL as fs) = (if isin_IL (IL as fs) x then IL as fs else
                                IL (x#as) (fs[from x := x#(fs ! from x)]))"

fun union_LIL :: "('n, 't) item list \<Rightarrow> ('n, 't) item_list \<Rightarrow> ('n, 't) item_list" where
"union_LIL [] il = il" |
"union_LIL (a#as) il = insert_IL a (union_LIL as il)"

definition IL_list :: "nat \<Rightarrow> ('n, 't) item list \<Rightarrow> ('n, 't) item_list" where
"IL_list k as = union_LIL as (empty_IL k)"

fun minus_LIL :: "nat \<Rightarrow> ('n, 't) item list \<Rightarrow> ('n, 't) item_list \<Rightarrow> ('n, 't) item_list" where
"minus_LIL k [] il = empty_IL k" |
"minus_LIL k (a#as) il = (if \<not>(isin_IL il a) then insert_IL a (minus_LIL k as il) else minus_LIL k as il)"

definition minus_IL :: "('n, 't) item_list \<Rightarrow> ('n, 't) item_list \<Rightarrow> ('n, 't) item_list" where
"minus_IL il1 il2 = minus_LIL (length (froms il1) - 1) (list il1) il2"

abbreviation wf_IL :: "nat \<Rightarrow> ('n, 't) item_list \<Rightarrow> bool" where
"wf_IL k il \<equiv> wf_bin k (set_IL il)"

abbreviation wf1_IL :: "nat \<Rightarrow> ('n, 't) item_list \<Rightarrow> bool" where
"wf1_IL k il \<equiv> wf_bin1 k (set_IL il)"

abbreviation (input) "wf1_IL' Bs \<equiv> wf1_IL (length Bs)"

lemma il_decomp: "\<exists>as m. il = IL as m"
  by (meson item_list.exhaust_sel)

subsection \<open>IL invariant lemmas and Set function equivalences\<close>

lemma set_empty_IL: "set_IL (empty_IL k) = {}" by (simp add: empty_IL_def)

lemma length_empty_froms: "length (empty_froms k) = Suc k"
  by (induction k) auto

lemma nth_empty_froms: "i < Suc k \<Longrightarrow> empty_froms k ! i = []"
proof (induction k arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case by (cases i) (auto simp flip: nth_Cons_Suc)
qed 

lemma empty_inv: "inv_IL (empty_IL k)"
  by (induction k) (auto simp add: empty_IL_def nth_empty_froms length_empty_froms 
                         simp del: empty_froms.simps)

lemma length_empty_IL[simp]: "length (froms (empty_IL k)) = Suc k"
  by (induction k) (auto simp add: empty_IL_def)

lemma inv_IL1: "inv_IL il \<Longrightarrow> distinct (list il) 
  \<and> (\<forall>x \<in> set (list il). from x < length (froms il)) 
  \<and> (\<forall>i < length (froms il). set ((froms il) ! i) = {x \<in> set (list il). from x = i}) 
  \<and> (\<forall>i < length (froms il). distinct ((froms il) ! i))"
  using inv_IL.simps[of "list il" "froms il"] by auto
    
lemma isin_IL_IL: "inv_IL (IL as m) \<Longrightarrow> from x < length m \<Longrightarrow> isin_IL (IL as m) x = (x \<in> set_IL (IL as m))" 
  by (auto)

lemma isin_IL_IL1: "inv_IL il \<Longrightarrow> from x < length (froms il) \<Longrightarrow> isin_IL il x = (x \<in> set_IL il)"
  by (metis item_list.exhaust_sel isin_IL_IL)

lemma set_insert_IL: "inv_IL (IL as m) \<Longrightarrow> from x < length m \<Longrightarrow> set_IL (insert_IL x (IL as m)) = set_IL ((IL as m)) \<union> {x}"
  by (auto simp add: Let_def isin_IL_IL simp del: isin_IL.simps)

lemma set_insert_IL1: "inv_IL il \<Longrightarrow> from x < length (froms il) \<Longrightarrow> set_IL (insert_IL x il) = set_IL il \<union> {x}"
  using set_insert_IL by (metis item_list.collapse)

lemma list_map_inv:
  assumes "x \<notin> set as" "from x < length m" "inv_IL (IL as m)" 
  shows "inv_IL (IL (x#as) (m[from x := x#(m!from x)]))"
proof -
  have 1: "i < length m \<Longrightarrow> set (m[from x := x#(m!from x)] ! i) = {y \<in> set (x#as). from y = i}" for i
    using assms by (cases "i = from x") auto
  have "i < length m \<Longrightarrow> distinct (m[from x := x#(m!from x)] ! i)" for i
      using assms by (cases "i = from x") auto 
  then show ?thesis using assms 1 by auto
qed

lemma inv_insert_IL: 
  assumes "inv_IL (IL as m)" "from x < length m" shows "inv_IL (insert_IL x (IL as m))"
  using assms list_map_inv by (auto simp add: isin_IL_IL simp del: inv_IL.simps isin_IL.simps)

lemma inv_insert_IL1: "inv_IL il \<Longrightarrow> from x < length (froms il) \<Longrightarrow> inv_IL (insert_IL x il)"
  using inv_insert_IL
  by (metis item_list.sel(2) il_decomp)

lemma length_froms_insert_IL[simp]: 
 "length (froms (insert_IL x il)) = length(froms il)" by (cases il) auto

lemma length_LIL_union[simp]: "length (froms (union_LIL as il)) = length (froms il)"
  by (induction as arbitrary: il) (auto)

lemma LIL_union_inv: "inv_IL il \<Longrightarrow> \<forall>a \<in> set as. from a < length (froms il) \<Longrightarrow> inv_IL (union_LIL as il)"
  using inv_insert_IL1 by (induction as) (auto simp add: wf_item_def)

lemma LIL_union: "inv_IL il \<Longrightarrow> \<forall>a \<in> set as. from a < length (froms il) \<Longrightarrow> set_IL (union_LIL as il) = set as \<union> set_IL il"
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have "set_IL (union_LIL (a # as) il) = set_IL (insert_IL a (union_LIL as il))" by simp
  also have "... = set_IL (union_LIL as il) \<union> {a}" using Cons set_insert_IL1 LIL_union_inv by simp
  also have "... = set as \<union> set_IL il \<union> {a}" using Cons set_insert_IL1 LIL_union_inv by simp
  finally show ?case by auto
qed

lemma set_IL_list: "\<forall>a \<in> set as. from a < Suc k \<Longrightarrow> set_IL (IL_list k as) = set as"
  using LIL_union[of "empty_IL k" as] empty_inv set_empty_IL
  by (auto simp add: IL_list_def)

lemma IL_list_inv: "\<forall>a \<in> set as. from a < Suc k \<Longrightarrow> inv_IL (IL_list k as)"
  using LIL_union_inv[of "empty_IL k"] empty_inv by (auto simp add: IL_list_def)

lemma length_IL_list[simp]: "length (froms (IL_list k as)) = Suc k"
  using IL_list_def length_LIL_union by auto

lemma length_minus_LIL[simp]: "length (froms (minus_LIL k as il)) = Suc k"
  by (induction as) auto

lemma LIL_minus_inv: "\<forall>a \<in> set as. from a < Suc k \<Longrightarrow> inv_IL (minus_LIL k as il)"
  using inv_insert_IL1 empty_inv by (induction as) (auto simp add: wf_item_def length_minus_LIL)

lemma LIL_minus: "inv_IL il \<Longrightarrow> \<forall>a \<in> set as. from a < Suc k \<Longrightarrow> length (froms il) \<ge> Suc k \<Longrightarrow> set_IL (minus_LIL k as il) = set as - set_IL il"
proof (induction as)
  case Nil
  then show ?case by (simp add: empty_IL_def)
next
  case (Cons a as)
  then show ?case
  proof (cases "isin_IL il a")
    case True
    then show ?thesis using Cons isin_IL_IL1 by auto
  next
    case False
    then have "set_IL (minus_LIL k (a # as) il) = set_IL (insert_IL a (minus_LIL k as il))" by simp
    also have "... = set_IL (minus_LIL k as il) \<union> {a}" using set_insert_IL1 Cons LIL_minus_inv by simp
    then show ?thesis using Cons isin_IL_IL1 by auto
  qed
qed

lemma IL_minus_inv: "inv_IL il1 \<Longrightarrow> length (froms il2) \<ge> length (froms il1) \<Longrightarrow> length (froms il1) > 0 \<Longrightarrow> inv_IL (minus_IL il1 il2)"
  using LIL_minus_inv by (cases il1) (auto simp add: minus_IL_def)

lemma IL_minus: "inv_IL il2 \<Longrightarrow> inv_IL il1 \<Longrightarrow> length (froms il2) \<ge> length (froms il1) \<Longrightarrow> length (froms il1) > 0
  \<Longrightarrow> set_IL (minus_IL il1 il2) = set_IL il1 - set_IL il2"
  using LIL_minus by (cases il1) (auto simp add: minus_IL_def)

lemma length_IL_minus1: "length (froms il1) > 0 \<Longrightarrow> length (froms (minus_IL il1 il2)) = length (froms il1)" 
  by (auto simp add: minus_IL_def)


subsection \<open>Earley IL algorithm\<close>

definition Init_L :: "('n,'t) item list" where
  "Init_L =  map (\<lambda> p. Item p 0 0) (filter (\<lambda> p. lhs p = (S)) ps)"

definition Scan_L :: "nat \<Rightarrow> ('n,'t) item list \<Rightarrow> ('n,'t) item list" where
  "Scan_L k Bs = (let s = w!k in map mv_dot (filter (\<lambda> b. next_sym b s) Bs))"

fun step2_IL :: "('n, 't) item list list \<Rightarrow>  ('n, 't) item_list2 \<Rightarrow> ('n, 't) item_list2" where
  "step2_IL Bs ((IL (x#xs) fs), C) = (let nexts = PreCo_L Bs x in
    (minus_IL (union_LIL nexts (IL (x#xs) fs)) (insert_IL x C), insert_IL x C) )"

fun test2_IL :: "('n, 't) item_list2 \<Rightarrow> bool" where
"test2_IL (ilB,ilC) = (list ilB \<noteq> [])"

definition steps2_IL :: "('n, 't) item list list \<Rightarrow> ('n, 't) item_list2 \<Rightarrow> ('n, 't) item_list2 option" where
  "steps2_IL Bs BC = while_option test2_IL (step2_IL Bs) BC"

definition close2_IL :: "('n, 't) item list list \<Rightarrow> ('n, 't) item_list \<Rightarrow> ('n, 't) item list" where
  "close2_IL Bs B = list (snd (the (steps2_IL Bs (B, empty_IL (length Bs)))))"

fun bins_IL :: "nat \<Rightarrow> ('n,'t) item list list" where
  "bins_IL 0 = [close2_IL [] (IL_list 0 Init_L)]" |
  "bins_IL (Suc k) = (let Bs = bins_IL k in Bs @ [close2_IL Bs (IL_list (length Bs) (Scan_L k (last Bs)))])"

fun recognized_L :: "('n, 't) item list \<Rightarrow> bool" where
"recognized_L [] = False" |
"recognized_L (a#as) = (is_final a \<or> recognized_L as)"

(*defined as a function for time_fun (could maybe be solved differently)*)
abbreviation earley_recognized where
"earley_recognized \<equiv> recognized_L (last (bins_IL (length w)))"

subsection \<open>Correctness of IL algorithm\<close>

lemma Init_L_eq_Init: "set Init_L = Init"
  by (auto simp add: Init_L_def Init_def)

lemma Scan_L_eq_Scan: "k < length w \<Longrightarrow> set (Scan_L k Bs) = Scan k (set Bs)"
  by (auto simp add: Scan_L_def Scan_def w_def)

lemma Complete_eq: "from st < length Bs \<Longrightarrow> set (Complete_L Bs st) = Complete (map set Bs) st"
  by (auto simp add: Complete_L_def Complete_def nths_map)

end

(*TODO: this is a bit of a hack. Can we do better? Same in Parser *)
context Earley_G
begin
fun earley_recognized1 :: "'t list \<Rightarrow> bool" where
"earley_recognized1 w = Earley_Gw.earley_recognized ps S w"
end

context Earley_Gw_eps
begin

lemma wf1_Predict_L: "wf_item1 k st \<Longrightarrow> wf_bin1 k (set (Predict_L k st))"
  using wf1_Predict set_Predict_L by (auto simp add: wf_bin1_def)

lemma wf1_Complete_L: 
  assumes "wf_bins1 (map set Bs)" "wf_item1 (length Bs) st" "is_complete st" 
    shows "wf_bin1' Bs (set (Complete_L Bs st))"
proof-
  have 1: "\<forall>x \<in>  (set (filter (\<lambda> b. next_sym b (Nt(lhs(prod st)))) (Bs ! from st))). wf_item (from st) x"
    using assms by (simp add: wf_bin1_def wf_bins1_def wf_item1_def)
  then have 2: "\<forall>x \<in> (set  (filter (\<lambda> b. next_sym b (Nt(lhs(prod st)))) (Bs ! from st))). wf_item (from st) (mv_dot x)"
    using assms 1 unfolding wf_item_def is_complete_def next_sym_def mv_dot_def
    by (auto split: if_splits)
  have "from st < length Bs"
    using assms(2,3) wf_item1_def by auto
  then show ?thesis
     using assms 2 Complete_L_def in_set_conv_nth wf1_Complete wf_bin1_def wf_bins1_def by fastforce  
 qed

lemma forall_from_Suc: "wf_bin1 k as \<Longrightarrow> \<forall>a \<in> as. from a < (Suc k)"
  by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)

lemma step2_IL_set:
  assumes inv: "inv_IL (IL (a#as) m1)" "inv_IL (IL bs m2)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and wf: "wf_bins1 (map set Bs)" "wf_item1 (length Bs) a"
  and sf: "step2_IL Bs ((IL (a#as) m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"
  shows  "set as' = (set as \<union> set (PreCo_L Bs a)) - (set bs \<union> {a})"
proof-
  let ?step = "PreCo_L Bs a"
  have wf_step: "wf_bin1' Bs (set ?step)" using wf wf1_Predict_L wf1_Complete_L by auto
  then have 1: "inv_IL (union_LIL ?step (IL (a#as) m1))" using LIL_union_inv[of "(IL (a#as) m1)" ?step] inv(1) leng(1)
    forall_from_Suc[of "length Bs" "set ?step"] by auto
  have 2: "inv_IL (insert_IL a (IL bs m2))" using inv_insert_IL[of bs m2 a] inv(2) wf(2)
    by (fastforce simp add: wf_item1_def wf_item_def leng(2))
  have "set as' = set_IL (minus_IL (union_LIL ?step (IL (a#as) m1)) (insert_IL a (IL bs m2)))"
    using sf by auto
  also have "... = set_IL (union_LIL ?step (IL (a#as) m1)) - set_IL (insert_IL a (IL bs m2))"
    using IL_minus leng 1 2
    by (metis diff_is_0_eq diff_self_eq_0 item_list.sel(2) length_froms_insert_IL length_LIL_union zero_less_Suc)
  also have "... = (set (a#as) \<union> set ?step) - set_IL (insert_IL a (IL bs m2))" 
    using LIL_union[of "IL (a#as) m1" ?step] wf_step forall_from_Suc[of "length Bs" "set ?step"] inv(1)
    by (metis Un_commute item_list.sel(1,2) leng(1) set_IL.simps)
  also have "... = (set (a#as) \<union> set ?step) - (set bs \<union> {a})" using set_insert_IL1[of "IL bs m2" a] 
     inv by (auto simp add: leng)

  finally show ?thesis by auto
qed

lemma Close2_if_step2_IL: 
  assumes cons: "as \<noteq> []" 
  and wf: "wf1_IL' Bs (IL as m1)" "wf_bins1 (map set Bs)"
  and inv: "inv_IL (IL as m1)" "inv_IL (IL bs m2)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and sf: "step2_IL Bs ((IL as m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"
shows "Close2 (map set Bs) (set as,set bs) (set as', set bs')"
proof-
  have comp: "\<forall>a \<in> set as. is_complete a \<longrightarrow> from a < length Bs" using wf by (auto simp add: wf_bin1_def wf_item1_def)
  from cons obtain a ass where P :"as = a # ass"
    using list.exhaust by auto 

  let ?xs = "if is_complete a then Complete (map set Bs) a else Predict (length Bs) a"
  let ?xsL = "PreCo_L Bs a"

  have "a \<in> set as"
    by (auto simp add: P next_sym_def)
  then have 1: "(map set Bs) \<turnstile> (set as, set bs) \<rightarrow> ((set as \<union> ?xs) - (set bs \<union> {a}), (set bs \<union> {a}))"
    using Close2.Complete Close2.Predict
    by (smt (verit, best) Un_insert_right boolean_algebra.disj_zero_right length_map)

  have "wf_item1 (length Bs) a" using wf by (auto simp add: wf_bin1_def P)
  then have 2: "set as' = (set ass \<union> set ?xsL) - (set bs \<union> {a})"
    using P inv sf step2_IL_set[of a ass m1 bs m2 Bs as' m3 bs' m4] wf leng by blast
  have "set bs' = (set bs \<union> {a})" using inv sf P set_insert_IL1[of "(IL bs m2)" a] leng by auto 

  then show ?thesis using 1 2
    using Complete_eq P set_Predict_L comp by fastforce
qed
  
lemma step2_IL_inv1: 
  assumes ne: "as \<noteq> []"
  and inv: "inv_IL (IL as m1)"
  and wf: "wf_bins1 (map set Bs)" "wf_bin1' Bs (set as)"
  and sf: "step2_IL Bs ((IL as m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
shows "inv_IL (IL as' m3)"
proof-
  from ne obtain a ass where P: "as = a#ass"
    by (meson neq_Nil_conv)
  let ?step = "PreCo_L Bs a"
  have "wf_item1 (length Bs) a" using P wf by (auto simp add: wf_bin1_def)
  then have wf_step: "wf_bin1' Bs (set ?step)" using wf wf1_Predict_L wf1_Complete_L by auto
  then have "\<forall>x \<in> set ?step. from x < Suc (length Bs)" by (auto simp add: forall_from_Suc)
  then show ?thesis
    using P IL_minus_inv[of "(union_LIL ?step (IL (a#ass) m1))" "(insert_IL a (IL bs m2))"] sf leng
      LIL_union_inv inv
      length_LIL_union[of ?step "IL (a#ass) m1"] length_froms_insert_IL[of a "IL bs m2"] by auto
qed

lemma step2_IL_inv2: 
  assumes ne: "as \<noteq> []"
  and wf: "wf_bin1' Bs (set as)"
  and leng: "length m2 = Suc (length Bs)"
  and inv: "inv_IL (IL bs m2)"
  and sf: "step2_IL Bs ((IL as m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"
shows "inv_IL (IL bs' m4)"
proof-
  from ne obtain a ass where P: "as = a#ass"
    by (meson neq_Nil_conv)
  then show ?thesis using inv_insert_IL1[of "(IL bs m2)" a] sf inv wf leng 
    by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
qed
  
lemma step2_IL_wf: 
  assumes ne: "as \<noteq> []"
  and wf: "wf_bins1 (map set Bs)" "wf1_IL' Bs (IL as m1)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and inv: "inv_IL (IL as m1)" "inv_IL (IL bs m2)"
  and sf: "step2_IL Bs ((IL as m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"  
  shows "wf1_IL' Bs (IL as' m3)"
proof -  
  from assms obtain a ass where P: "as = a # ass"
    by (meson neq_Nil_conv)
  let ?step = "PreCo_L Bs a"
  have "wf_item1 (length Bs) a" using P assms by (auto simp add: wf_bin1_def)
  then have "wf_bin1' Bs (set ?step)" using assms wf1_Predict_L wf1_Complete_L by auto
  then have 1: "wf_bin1' Bs ((set as \<union> set ?step) - (set bs \<union> {a}))" 
    using wf_bin1_def wf by auto
  from wf P have "wf_item1 (length Bs) a" by (auto simp add: wf_bin1_def)
  then have "set as' = (set ass \<union> set ?step) - (set bs \<union> {a})"
    using P inv sf leng wf step2_IL_set[of a ass m1 bs m2 Bs as'] by blast
  then show ?thesis using P 1 by auto
qed

lemma step2_IL_wf2: 
  assumes ne: "as \<noteq> []"
  and wf: "wf1_IL' Bs (IL as m1)" "wf1_IL' Bs (IL bs m2)"
  and leng: "length m2 = Suc (length Bs)"
  and inv: "inv_IL (IL bs m2)"
  and sf: "step2_IL Bs ((IL as m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"
  shows "wf1_IL' Bs (IL bs' m4)"
proof-
  from \<open>as \<noteq> []\<close> obtain a ass where P: "as = a#ass" by (meson neq_Nil_conv)
  then have "from a < Suc (length Bs)" using wf by (auto simp add: wf_bin1_def wf_item1_def wf_item_def) 
  then have "set bs' = set bs \<union> {a}" using inv sf P set_insert_IL1[of "(IL bs m2)" a] leng 
      by auto
  then show ?thesis using assms P by (auto simp add: wf_bin1_def)
qed

lemma length_step2_IL1:
  assumes ne: "as \<noteq> []"
  and sf: "step2_IL Bs ((IL as m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"
  and leng: "length m1 = Suc (length Bs)"
shows "length m3 = Suc (length Bs)"
proof-
  obtain a ass where P: "as = a#ass"
    by (meson ne recognized_L.cases)
  from P have "minus_IL (union_LIL (PreCo_L Bs a) (IL (a # ass) m1)) (IL bs' m4) = IL as' m3"
    using assms by auto
  then show ?thesis 
    by (metis item_list.sel(2) leng length_IL_minus1 length_LIL_union zero_less_Suc)
qed

lemma length_step2_IL2:
  assumes ne: "as \<noteq> []"
  and sf: "step2_IL Bs ((IL as m1),(IL bs m2)) = ((IL as' m3), (IL bs' m4))"
  and leng: "length m2 = Suc (length Bs)"
shows "length m4 = Suc (length Bs)"
proof-
  obtain a ass where P: "as = a#ass"
    by (meson ne recognized_L.cases)
  then show ?thesis using assms length_froms_insert_IL[of a "IL bs m2"] by (auto simp del: insert_IL.simps)
qed

lemma test2_IL_def: "test2_IL = (\<lambda>(ilB,ilC). list ilB \<noteq> [])"
using test2_IL.simps by blast

lemma steps2_IL_sound:
  assumes wf: "wf1_IL' Bs (IL as m1)"  "wf_bins1 (map set Bs)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and inv: "inv_IL (IL as m1)" "inv_IL (IL bs m2)"
  and step: "steps2_IL Bs ((IL as m1),(IL bs m2)) = Some ((IL as' m3), (IL bs' m4))"
shows "((Close2 (map set Bs))^**) (set as, set bs) ({},set bs')"
proof -
  let ?P = "\<lambda>(il1,il2). inv_IL il1 \<and> inv_IL il2 \<and> wf1_IL' Bs il1 \<and> wf_bins1 (map set Bs) 
              \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs) 
              \<and> (Close2 (map set Bs))^** (set as, set bs) (set (list il1),set (list il2))"
  let ?b = "test2_IL"
  let ?c = "step2_IL Bs"

  have 1: "(?P (il1,il2) \<Longrightarrow> ?b (il1,il2) \<Longrightarrow> ?P (?c (il1,il2)))" for il1 il2
  proof-
    assume assm: "?P (il1,il2)" and ne: "?b (il1,il2)"
    obtain xs n1 ys n2 where P: "il1 = (IL xs n1) \<and> il2 = (IL ys n2)"
      by (meson inv_IL.cases)
    obtain xs' n1' ys' n2' where c: "?c (il1, il2) = ((IL xs' n1'), (IL ys' n2'))"
      by (metis inv_IL.cases surj_pair)
    obtain x xss where P_xs: "xs = x#xss" using ne P
      using list.exhaust by auto
    then have 11: "length n1' = Suc (length Bs) \<and> length n2' = Suc (length Bs)"
      using assm length_step2_IL1[of xs Bs n1 ys n2 xs' n1' ys' n2'] 
            length_step2_IL2[of xs Bs n1 ys n2 xs' n1' ys' n2'] P c by auto
    moreover have 12: "inv_IL (IL xs' n1') \<and> inv_IL (IL ys' n2')" 
      using step2_IL_inv1[of xs n1 Bs ys n2 xs' n1' ys' n2'] 
            step2_IL_inv2[of xs Bs n2 ys n1 xs' n1' ys' n2'] assm P c P_xs by fastforce
    moreover have 13: "wf1_IL' Bs (IL xs' n1') \<and> wf_bins1 (map set Bs)" 
      using step2_IL_wf[of xs Bs n1 n2 ys] assm P c P_xs by force
    moreover have "(Close2 (map set Bs))^** (set as, set bs) (set xs', set ys')"
      using Close2_if_step2_IL[of xs Bs n1 ys n2] assm P c P_xs by auto
    ultimately show ?thesis using c by auto
  qed

  have stop: "as' = []" using step while_option_stop[of ?b ?c "((IL as m1),(IL bs m2))"] by (auto simp add: steps2_IL_def)

  have "?P ((IL as m1),(IL bs m2))" using wf inv leng by auto
  then have "?P ((IL as' m3), (IL bs' m4))" using step
      while_option_rule[of ?P ?b ?c "((IL as m1),(IL bs m2))" "((IL as' m3), (IL bs' m4))"] 1
    unfolding steps2_IL_def test2_IL_def by force
  then show ?thesis using stop by auto     
qed

lemma steps2_IL_sound1: 
  assumes wf: "wf1_IL' Bs (IL as m1)"  "wf_bins1 (map set Bs)"
  and leng: "length m1 = Suc (length Bs)"
  and inv: "inv_IL (IL as m1)"
  and step: "steps2_IL Bs ((IL as m1),empty_IL (length Bs)) = Some (B',C)" 
shows "(Close2 (map set Bs))^** (set as,{}) ({},set (list C))"
proof-
  have "inv_IL (empty_IL (length Bs))"
    by (simp add: empty_inv)
  moreover have "wf1_IL' Bs (empty_IL (length Bs))" by (simp add: empty_IL_def wf_bin1_def)
  moreover have "length (froms (empty_IL (length Bs))) = Suc (length Bs)" by simp
  ultimately show ?thesis using steps2_IL_sound assms
    by (metis Earley_Gw.set_IL.simps item_list.collapse set_empty_IL)
qed

lemma step2_IL_inv1_il: 
  assumes ne: "list il1 \<noteq> []"
  and inv: "inv_IL il1"
  and wf: "wf_bins1 (map set Bs)" "wf1_IL' Bs il1"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and sf: "step2_IL Bs (il1,il2) = (il1', il2')"
shows "inv_IL il1'"
  using step2_IL_inv1 il_decomp sf inv leng wf ne
  by (metis item_list.collapse set_IL.elims)

lemma step2_IL_inv2_il: 
  assumes ne: "(list il1) \<noteq> []"
  and wf: "wf1_IL' Bs il1"
  and leng: "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il2"
  and sf: "step2_IL Bs (il1,il2) = (il1', il2')"
shows "inv_IL il2'"
 using step2_IL_inv2 il_decomp ne wf leng inv sf
  by (metis item_list.collapse set_IL.elims)
  
lemma step2_IL_wf_il: 
  assumes ne: "(list il1) \<noteq> []"
  and wf: "wf_bins1 (map set Bs)" "wf1_IL' Bs il1"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il1" "inv_IL il2"
  and sf: "step2_IL Bs (il1,il2) = (il1', il2')"  
shows "wf1_IL' Bs il1'"
  using step2_IL_wf il_decomp ne wf inv sf leng
  by (metis item_list.collapse)

lemma step2_IL_wf2_il: 
   assumes ne: "list il1 \<noteq> []"
  and wf: "wf1_IL' Bs il1" "wf1_IL' Bs il2"
  and leng: "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il2"
  and sf: "step2_IL Bs (il1,il2) = (il1', il2')"
shows "wf1_IL' Bs il2'"
  using step2_IL_wf2 il_decomp ne wf inv sf leng
  by (metis item_list.collapse)

lemma length_step2_IL1_il: 
  assumes "list il1 \<noteq> []"  
          "step2_IL Bs (il1, il2) = (il1', il2')" "length (froms il1) = Suc (length Bs)" 
  shows "length (froms il1') = Suc (length Bs)"
  using length_step2_IL1 il_decomp assms by (metis item_list.collapse)

lemma length_step2_IL2_il: 
  assumes "list il1 \<noteq> []" "step2_IL Bs (il1, il2) = (il1', il2')" 
          "length (froms il2) = Suc (length Bs)"
  shows "length (froms il2') = Suc (length Bs)"
  using length_step2_IL2 il_decomp assms by (metis item_list.collapse)
  
lemma steps2_IL_inv2: 
  assumes inv: "inv_IL il2" "inv_IL il1"
  and wf: "wf1_IL' Bs il1" "wf_bins1 (map set Bs)"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and step: "steps2_IL Bs (il1,il2) = Some (il1', il2')"
shows "inv_IL il2'"
  using while_option_rule[where P= "\<lambda>(il1,il2). inv_IL il2 \<and> inv_IL il1 \<and> wf1_IL' Bs il1 \<and> wf_bins1 (map set Bs) \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs)"] 
    step2_IL_inv2_il step2_IL_inv1_il length_step2_IL1_il length_step2_IL2_il step2_IL_wf_il step inv wf leng unfolding steps2_IL_def test2_IL_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps2_IL_wf2: 
  assumes wf: "wf_bins1 (map set Bs)" "wf1_IL' Bs il1" "wf1_IL' Bs il2"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il1" "inv_IL il2"
  and sf: "steps2_IL Bs (il1,il2) = Some (il1', il2')"  
shows "wf1_IL' Bs il2'"
  using while_option_rule[where P= "\<lambda>(il1,il2). wf1_IL' Bs il2 \<and> wf1_IL' Bs il1 \<and> inv_IL il1 \<and> inv_IL il2 \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs) \<and> wf_bins1 (map set Bs)"] 
    step2_IL_wf_il step2_IL_wf2_il step2_IL_inv1_il step2_IL_inv2_il length_step2_IL1_il length_step2_IL2_il wf sf inv leng unfolding steps2_IL_def test2_IL_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)


text \<open>This is the wellfounded relation for the termination proof:\<close>

definition step2_IL_less :: "nat \<Rightarrow> ((('n, 't) item_list2) \<times> (('n, 't) item_list2)) set" where
"step2_IL_less k = (\<lambda>(B,C). card({x. wf_item k x} - (set_IL B \<union> set_IL C))) <*mlex*> inv_image finite_psubset (set_IL o fst)"

lemma step2_IL_less_eq: "((A, B), (C,D)) \<in> step2_IL_less k \<longleftrightarrow> ((set_IL A, set_IL B), (set_IL C, set_IL D)) \<in> Close2_less k"
  by (simp add: step2_IL_less_def Close2_less_def mlex_prod_def)

lemma wf_step2_IL_less: "wf (step2_IL_less k)"
  by (simp add: step2_IL_less_def wf_mlex)

text \<open>This is a key property of \<open>step2_IL\<close>: it goes down in the \<open>step2_IL_less\<close> relation.\<close>
lemma step2_IL_less_step: 
  assumes ne: "list il1 \<noteq>[]" 
  and wf: "wf_bins1 (map set Bs)" "wf1_IL' Bs il1" "wf1_IL' Bs il2"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il1" "inv_IL il2"
shows "(step2_IL Bs (il1,il2), (il1,il2)) \<in> (step2_IL_less (length Bs))"
proof-
  let ?B' = "fst (step2_IL Bs (il1,il2))"
  let ?C' = "snd (step2_IL Bs (il1,il2))"
  have 1: "(?B', ?C') = step2_IL Bs (il1,il2) " by simp

  obtain as m1 bs m2 where P1: "il1 = (IL as m1) \<and> il2 = (IL bs m2)"
    by (meson inv_IL.cases)
  obtain as' m1' bs' m2' where P2: "?B' = (IL as' m1') \<and> ?C' = (IL bs' m2')"
    by (meson inv_IL.cases)

  have "Close2 (map set Bs) (set_IL il1, set_IL il2) (set_IL ?B', set_IL ?C')"
    using Close2_if_step2_IL assms P1 P2
    by (metis "1" item_list.sel(1,2) set_IL.elims) 
  then show ?thesis using assms Close2_less_step step2_IL_less_eq 1
    by (metis length_map)
qed

lemma step2_IL_wf_items: 
  assumes wf: "wf_bins1 (map set Bs)" "wf1_IL' Bs il1" "wf1_IL' Bs il2"
    and inv: "inv_IL il1" "inv_IL il2" 
    and ne:"(list il1) \<noteq> []"
    and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  shows "\<exists>B' C'. step2_IL Bs (il1,il2) = (B',C') \<and> inv_IL B' \<and> inv_IL C' \<and> wf1_IL' Bs B' \<and> wf1_IL' Bs C' 
    \<and> length (froms B') = Suc (length Bs) \<and> length (froms C') = Suc (length Bs)"
proof-
  obtain as m1 bs m2 where P1: "il1 = (IL as m1) \<and> il2 = (IL bs m2)"
    by (meson inv_IL.cases)
  obtain as' m1' bs' m2' where P: "step2_IL Bs (il1,il2) = ((IL as' m1'),(IL bs' m2'))"
    by (metis item_list.exhaust surj_pair)
  then have 1: "wf1_IL' Bs (IL as' m1') \<and> wf1_IL' Bs (IL bs' m2')"
    using step2_IL_wf step2_IL_wf2 assms P1
    by (metis item_list.sel(1,2))
  moreover have "inv_IL (IL as' m1') \<and> inv_IL (IL bs' m2')" using P P1
    using assms step2_IL_inv1 step2_IL_inv2
    by (metis item_list.sel(1,2) set_IL.elims)
  moreover have "length m1' = Suc (length Bs) \<and> length m2' = Suc (length Bs)"
    using leng P P1 length_step2_IL1 length_step2_IL2 ne by simp
  ultimately show ?thesis using P by auto
qed

theorem Close2_L_NF: "\<lbrakk>wf_bins1 (map set Bs); wf1_IL' Bs il1; wf1_IL' Bs il2; 
    inv_IL il1; inv_IL il2; length (froms il1) = Suc (length Bs); length (froms il2) = Suc (length Bs)\<rbrakk>
  \<Longrightarrow> \<exists>il1' il2'. steps2_IL Bs (il1,il2) = Some (il1',il2')"
unfolding steps2_IL_def
using wf_step2_IL_less[of "length Bs"]
proof (induction "(il1,il2)" arbitrary: il1 il2 rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume ne: "list il1 = []"
    thus ?thesis by(simp add: while_option_unfold[of _ _ "(il1,il2)"])
  next
    let ?steps = "while_option (\<lambda>(B, C). list B \<noteq> []) (step2_IL Bs)"
    assume cons: "list il1 \<noteq> []"
    then obtain il1' il2'
      where "(il1',il2') = step2_IL Bs (il1,il2)" and wf': "wf1_IL' Bs il1'" "wf1_IL' Bs il2'" 
        and inv': "inv_IL il1'" "inv_IL il2'"
        and leng': "length (froms il1') = Suc (length Bs)" "length (froms il2') = Suc (length Bs)"
      using step2_IL_wf_items[OF less.prems(1,2,3,4,5) cons less.prems(6,7)] by fastforce
    then have "((il1',il2'), (il1, il2)) \<in> step2_IL_less (length Bs)"
      using cons less.prems step2_IL_less_step by presburger
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf' inv' leng']
    show ?thesis
      by (simp add: \<open>(il1',il2') = step2_IL Bs (il1,il2)\<close> while_option_unfold)
  qed
qed

lemma close2_IL_eq_Close1: 
  assumes "wf_bins1 (map set Bs)" "wf1_IL' Bs il" "inv_IL il" "length (froms il) = Suc (length Bs)"
  shows "set (close2_IL Bs il) = Close1 (map set Bs) (set (list il))"
proof-
  have "wf1_IL' Bs (empty_IL (length Bs)) \<and> inv_IL (empty_IL (length Bs)) 
      \<and> length (froms (empty_IL (length Bs))) = Suc (length Bs)"
    by (metis empty_iff empty_inv set_empty_IL wf_bin1_def length_empty_IL)
  then obtain il1 il2 where D1: "steps2_IL Bs (il,(empty_IL (length Bs))) = Some (il1,il2)" using assms Close2_L_NF
    by blast
  then have "(map set Bs) \<turnstile> (set (list il), {}) \<rightarrow>* ({}, set (list il2))" using steps2_IL_sound
    by (metis assms(1,2,3,4) item_list.collapse steps2_IL_sound1)
  then have DC1: "set (list il2) = Close1 (map set Bs) (set (list il))"
    by (simp add: Close1_subset_Close2 Close2_steps_subset_Close1' subset_antisym)
  have "set (list il2) = set (close2_IL Bs il)" using D1 by (auto simp add: close2_IL_def)
  then show ?thesis using DC1 by auto
qed

lemma close2_IL_eq_Close: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_IL' Bs il \<Longrightarrow> length (froms il) = Suc (length Bs) 
  \<Longrightarrow> inv_IL il \<Longrightarrow> set (close2_IL Bs il) = Close (map set Bs) (set_IL il)"
  by (auto simp add: close2_IL_eq_Close1 Close1_eq_Close)

lemma length_bins_IL: "length (bins_IL k) = Suc k"
  by (induction k) (auto simp add: Let_def)

theorem bins_IL_eq_bins: "k \<le> length w \<Longrightarrow> map set (bins_IL k) = bins k"
proof (induction k)
  case 0
  have "wf_bins1 (map set []) \<and> wf_bin1 0 (set Init_L)"
    by (simp add: Init_L_eq_Init wf_bin1_Init wf_bins1_def)
  then have "wf_bins1 (map set []) \<and> wf1_IL 0 (IL_list 0 Init_L) \<and> inv_IL (IL_list 0 Init_L)
    \<and> length (froms (IL_list 0 Init_L)) = Suc 0"
    using IL_list_inv forall_from_Suc set_IL_list length_IL_list by presburger
  then have "set (close2_IL [] (IL_list 0 Init_L)) = Close [] Init"
    using close2_IL_eq_Close[of "[]" "IL_list 0 Init_L"]
    using Init_L_eq_Init forall_from_Suc list.map_disc_iff set_IL_list set_IL.elims wf_bin1_Init by force
  then show ?case by simp
next
  case (Suc k)
  let ?Bs = "bins_IL k"
  have kl: "k < length w" using Suc by auto
  then have 1: "set (Scan_L k (last ?Bs)) = Scan k (last (map set ?Bs))" using Suc
    by (metis Scan_L_eq_Scan Suc_leD bins_nonempty map_is_Nil_conv last_map)
  have "wf_bin1 k (set (last ?Bs))"
    by (metis Earley_Gw.bins_nonempty Suc.IH Suc.prems Suc_leD last_map list.map_disc_iff wf_bin1_last)
  then have 2: "wf1_IL' ?Bs (IL_list (Suc k) (Scan_L k (last ?Bs)))"
    by (metis Scan_L_eq_Scan wf_bin1_Scan forall_from_Suc kl set_IL_list length_bins_IL)
  have 3: "wf_bins1 (map set (bins_IL k))"
    by (simp add: Suc.IH Suc.prems Suc_leD wf_bins1_bins)
  have 4: "length (froms (IL_list  (Suc k) (Scan_L k (last ?Bs)))) = Suc (length ?Bs)"
    by (simp add: length_bins_IL)

  then have "set (close2_IL ?Bs (IL_list  (Suc k) (Scan_L k (last ?Bs)))) = Close (map set ?Bs) (Scan k (last (map set ?Bs)))"
    using close2_IL_eq_Close[OF 3 2 4] IL_list_inv
        1 2 3 forall_from_Suc
    using Suc.IH Suc.prems Suc_leD kl set_IL_list wf_bin1_Scan wf_bin1_last by presburger
  then show ?case using Suc by (auto simp add: Let_def length_bins_IL)
qed 

corollary bins_IL_eq_\<E>: "i \<le> k \<Longrightarrow> k \<le> length w \<Longrightarrow> set (bins_IL k ! i) = \<E> i"
  using bins_eq_\<E> bins_IL_eq_bins length_bins_IL
  by (metis bins_IL_eq_bins bins_eq_\<E>_gen le_imp_less_Suc length_bins_IL nth_map)

lemma recognized_set: "recognized_L as = (\<exists>x \<in> set as. is_final x)"
  by (induction as) auto

lemma earley_recognized_eq_recognized_Earley: "earley_recognized \<longleftrightarrow> recognized Earley"
proof
  assume "earley_recognized"
  then have "\<exists>x \<in> set (last (bins_IL (length w))). is_final x" using recognized_set 
    by metis
  then obtain x where P: "is_final x \<and> x \<in> set (last (bins_IL (length w)))" by blast
  then have "x \<in> \<E> (length w)" using bins_IL_eq_\<E> length_bins_IL last_conv_nth
    by (metis bins_IL_eq_bins bins_nonempty diff_Suc_1 map_is_Nil_conv nat_le_linear)
  then show "recognized Earley" using P
    using accepted_def accpted_sound correctness_Earley by auto
next
  assume "recognized Earley"
  then obtain x where P: "is_final x \<and> (length w, x) \<in> Earley"
    using recognized_def by blast
  then have "x \<in> \<E> (length w)"
    using Earley_eq_\<E> by auto
  then have "x \<in> set (last (bins_IL (length w)))" using bins_IL_eq_\<E> length_bins_IL last_conv_nth
    by (metis bins_IL_eq_bins bins_nonempty diff_Suc_1 map_is_Nil_conv nat_le_linear)
  then have "\<exists>x \<in> set (last (bins_IL (length w))). is_final x" using P by blast
  then show "earley_recognized" using recognized_set by metis
qed

theorem correctness_earley:
  shows "earley_recognized \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using correctness_Earley earley_recognized_eq_recognized_Earley by metis 

end

context Earley_Gw
begin
(*code declarations for recognizer*)
  declare Earley_Gw.Predict_L_def[code]
  declare Earley_Gw.Complete_L_def[code]
  declare Earley_Gw.Scan_L_def[code]
  declare Earley_Gw.Init_L_def[code]
  declare Earley_Gw.test2_IL.simps[code]
  declare Earley_Gw.step2_IL.simps[code]
  declare Earley_Gw.steps2_IL_def[code]
  declare Earley_Gw.close2_IL_def[code]
  declare Earley_Gw.bins_IL.simps[code]
  declare Earley_Gw.w_def[code]
  declare Earley_Gw.is_final_def[code]
  declare Earley_Gw.recognized_def[code]
  declare Earley_Gw.recognized_L.simps[code]
  
  declare Earley_Gw.empty_IL_def[code]
  declare Earley_Gw.empty_froms.simps[code]
  declare Earley_Gw.IL_list_def[code]
  declare Earley_Gw.isin_IL.simps[code]
  declare Earley_Gw.union_LIL.simps[code]
  declare Earley_Gw.minus_IL_def[code]
  declare Earley_Gw.insert_IL.simps[code]
  declare Earley_Gw.minus_LIL.simps[code]

end

(*unused_thms*)

subsection \<open>Example\<close>

(* TODO: define Earley_G that can be instantiated independently of w *)

interpretation Test:Earley_Gw_eps
  where ps = "[((0::nat), [Tm (1::int)]), (0, [Nt (0::nat), Nt 0])]" and S = 0
  and w0 = "[1, 1, (1 :: int)]"
proof (standard, goal_cases)
  case 1 show ?case by (auto simp add: Eps_free_def)
qed

value "Test.bins_IL 0"
value "Test.bins_IL 1"
value "Test.bins_IL 2"
value "Test.bins_IL 3"

value "Test.earley_recognized"

end