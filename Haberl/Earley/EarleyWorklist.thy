theory EarleyWorklist

imports
  "Earley"
  "HOL-Library.While_Combinator" 
  "HOL-Library.Time_Functions"  
  "Context_Free_Grammar.Parse_Tree"

begin

(* TODO mv *)
lemma T_fst_0[simp]: "T_fst x = 0"
  by (metis T_fst.elims)

lemma T_snd_0[simp]: "T_snd x = 0"
  by (metis T_snd.elims)

time_fun the

declare T_append[simp]

time_fun list_update
time_fun last

time_fun replicate

lemma T_last[simp]: "as \<noteq> [] \<Longrightarrow> T_last as = length as"
  by (induction as) auto

lemma T_replicate[simp]: "T_replicate k x = Suc k"
  by (induction k) auto

(* [simp] ? *)
lemma T_filter_eq_T_map: "T_filter T_f xs = T_map T_f xs"
by (simp add: T_filter T_map)

lemma sum_list_bound: "\<forall>n \<in> set ns. n \<le> k \<Longrightarrow> sum_list ns \<le> k * length ns"
by (induction ns) auto

lemma T_map_bound:
  "\<forall>x \<in> set xs. T_P x \<le> k \<Longrightarrow> T_map T_P xs \<le> k * length xs + length xs + 1"
using sum_list_bound[of "map T_P xs"] by(simp add: T_map)

lemma T_filter_bound:
  "\<forall>x \<in> set xs. T_P x \<le> k \<Longrightarrow> T_filter T_P xs \<le> k * length xs + length xs + 1"
by (metis T_filter_eq_T_map T_map_bound)

time_fun hd
time_fun zip

lemma T_zip: "length xs = length ys \<Longrightarrow> T_zip xs ys = length ys + 1"
  by (induction xs ys rule: list_induct2) auto

lemma T_rev_bound: "T_rev xs \<le> 2*length xs * length xs + 1"
  by (induction xs) auto


section \<open>ItemList definiton and functions\<close>

datatype ('n,'a) efficientItemList = 
  ItemList ("list": "('n,'a) item list") ("froms" : "('n,'a) item list list")

fun inv_IL :: "('n, 'a) efficientItemList \<Rightarrow> bool" where
"inv_IL (ItemList as fs) = (length fs > 0 
                            \<and> (\<forall>x \<in> set as. from x < length fs) 
                            \<and> (\<forall>i < length fs. set (fs ! i) = {x \<in> set as. from x = i}) 
                            \<and> (\<forall>i < length fs. distinct (fs ! i)) 
                            \<and> distinct as)"

fun isin :: "('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) item \<Rightarrow> bool" where
"isin (ItemList as fs) x = isin_list (fs ! from x) x"

definition empty_IL :: "nat \<Rightarrow> ('n, 'a) efficientItemList" where
"empty_IL k = (ItemList [] (replicate (Suc k) []))"

context Earley_Gw
begin

(* Could pull out more defs and lemmas but they would be polymorphic now
   and not with fixed 'n and 'a as currently. Such polymorphic lemmas
   break some existing proofs because type variables need to be instantiated.
   Worth the effort?
*)

fun set_ItemList :: "('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) item set" where
"set_ItemList il = set (list il)"

fun insert :: "('n, 'a) item \<Rightarrow> ('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) efficientItemList" where
"insert x (ItemList as fs) = (if isin (ItemList as fs) x then ItemList as fs else
                                ItemList (x#as) (fs[from x := x#(fs ! from x)]))"

fun union_LIL :: "('n, 'a) item list \<Rightarrow> ('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) efficientItemList" where
"union_LIL [] il = il" |
"union_LIL (a#as) il = insert a (union_LIL as il)"

definition IL_of_List :: "nat \<Rightarrow> ('n, 'a) item list \<Rightarrow> ('n, 'a) efficientItemList" where
"IL_of_List k as = union_LIL as (empty_IL k)"

fun minus_LIL :: "nat \<Rightarrow> ('n, 'a) item list \<Rightarrow> ('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) efficientItemList" where
"minus_LIL k [] il = empty_IL k" |
"minus_LIL k (a#as) il = (if \<not>(isin il a) then insert a (minus_LIL k as il) else minus_LIL k as il)"

definition minus_IL :: "('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) efficientItemList" where
"minus_IL il1 il2 = minus_LIL (length (froms il1) - 1) (list il1) il2"

abbreviation wf_IL :: "('n, 'a) efficientItemList \<Rightarrow> nat \<Rightarrow> bool" where
"wf_IL il k \<equiv> wf_bin (set_ItemList il) k"

abbreviation wf1_IL :: "('n, 'a) efficientItemList \<Rightarrow> nat \<Rightarrow> bool" where
"wf1_IL il k \<equiv> wf_bin1 (set_ItemList il) k"

lemma il_decomp: "\<exists>as m. il = ItemList as m"
  by (meson efficientItemList.exhaust_sel)

subsection \<open>ItemList invariant lemmas and Set function equivalences\<close>

lemma set_empty_IL: "set_ItemList (empty_IL k) = {}" by (simp add: empty_IL_def)

lemma empty_inv: "inv_IL (empty_IL k)"
  by (induction k) (auto simp add: empty_IL_def simp del: replicate.simps)

lemma length_empty_IL[simp]: "length (froms (empty_IL k)) = Suc k"
  by (induction k) (auto simp add: empty_IL_def)

lemma inv_IL1: "inv_IL il \<Longrightarrow> distinct (list il) 
  \<and> (\<forall>x \<in> set (list il). from x < length (froms il)) 
  \<and> (\<forall>i < length (froms il). set ((froms il) ! i) = {x \<in> set (list il). from x = i}) 
  \<and> (\<forall>i < length (froms il). distinct ((froms il) ! i))"
  using inv_IL.simps[of "list il" "froms il"] by auto
    
lemma isin_IL: "inv_IL (ItemList as m) \<Longrightarrow> from x < length m \<Longrightarrow> (isin (ItemList as m) x) = (x \<in> set_ItemList (ItemList as m))" 
  by (auto)

lemma isin_IL1: "inv_IL il \<Longrightarrow> from x < length (froms il) \<Longrightarrow> (isin il x) = (x \<in> set_ItemList il)"
  by (metis efficientItemList.exhaust_sel isin_IL)

lemma IL_insert: "inv_IL (ItemList as m) \<Longrightarrow> from x < length m \<Longrightarrow> set_ItemList (insert x (ItemList as m)) = set_ItemList ((ItemList as m)) \<union> {x}"
  by (auto simp add: Let_def isin_IL simp del: isin.simps)

lemma IL_insert1: "inv_IL il \<Longrightarrow> from x < length (froms il) \<Longrightarrow> set_ItemList (insert x il) = set_ItemList il \<union> {x}"
  using IL_insert by (metis efficientItemList.collapse)

lemma list_map_inv: 
  assumes "x \<notin> set as" "from x < length m" "inv_IL (ItemList as m)" 
  shows "inv_IL (ItemList (x#as) (m[from x := x#(m!from x)]))"
proof -
  have 1: "i < length m \<Longrightarrow> set (m[from x := x#(m!from x)] ! i) = {y \<in> set (x#as). from y = i}" for i
    using assms by (cases "i = from x") auto
  have "i < length m \<Longrightarrow> distinct (m[from x := x#(m!from x)] ! i)" for i
      using assms by (cases "i = from x") auto 
  then show ?thesis using assms 1 by auto
qed

lemma insert_inv_IL: 
  assumes "inv_IL (ItemList as m)" "from x < length m" shows "inv_IL (insert x (ItemList as m))"
  using assms list_map_inv by (auto simp add: isin_IL simp del: inv_IL.simps isin.simps)

lemma insert_inv_IL1: "inv_IL il \<Longrightarrow> from x < length (froms il) \<Longrightarrow> inv_IL (insert x il)"
  using insert_inv_IL
  by (metis efficientItemList.sel(2) il_decomp)

lemma length_IL_insert[simp]: 
 "length (froms (insert x il)) = length(froms il)" by (cases il) auto

lemma length_LIL_union[simp]: "length (froms (union_LIL as il)) = length (froms il)"
  by (induction as arbitrary: il) (auto)

lemma LIL_union_inv: "inv_IL il \<Longrightarrow> \<forall>a \<in> set as. from a < length (froms il) \<Longrightarrow> inv_IL (union_LIL as il)"
  using insert_inv_IL1 by (induction as) (auto simp add: wf_item_def)

lemma LIL_union: "inv_IL il \<Longrightarrow> \<forall>a \<in> set as. from a < length (froms il) \<Longrightarrow> set_ItemList (union_LIL as il) = set as \<union> set_ItemList il"
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have "set_ItemList (union_LIL (a # as) il) = set_ItemList (insert a (union_LIL as il))" by simp
  also have "... = set_ItemList (union_LIL as il) \<union> {a}" using Cons IL_insert1 LIL_union_inv by simp
  also have "... = set as \<union> set_ItemList il \<union> {a}" using Cons IL_insert1 LIL_union_inv by simp
  finally show ?case by auto
qed

lemma set_IL_of_List: "\<forall>a \<in> set as. from a < Suc k \<Longrightarrow> set_ItemList (IL_of_List k as) = set as"
  using LIL_union[of "empty_IL k" as] empty_inv set_empty_IL
  by (auto simp add: IL_of_List_def)

lemma IL_of_List_inv: "\<forall>a \<in> set as. from a < Suc k \<Longrightarrow> inv_IL (IL_of_List k as)"
  using LIL_union_inv[of "empty_IL k"] empty_inv by (auto simp add: IL_of_List_def)

lemma length_IL_of_List[simp]: "length (froms (IL_of_List k as)) = Suc k"
  using IL_of_List_def length_LIL_union by auto

lemma length_minus_LIL[simp]: "length (froms (minus_LIL k as il)) = Suc k"
  using length_IL_insert by (induction as) auto

lemma LIL_minus_inv: "\<forall>a \<in> set as. from a < Suc k \<Longrightarrow> inv_IL (minus_LIL k as il)"
  using insert_inv_IL1 empty_inv by (induction as) (auto simp add: wf_item_def length_minus_LIL)

lemma LIL_minus: "inv_IL il \<Longrightarrow> \<forall>a \<in> set as. from a < Suc k \<Longrightarrow> length (froms il) \<ge> Suc k \<Longrightarrow> set_ItemList (minus_LIL k as il) = set as - set_ItemList il"
proof (induction as)
  case Nil
  then show ?case by (simp add: empty_IL_def)
next
  case (Cons a as)
  then show ?case
  proof (cases "isin il a")
    case True
    then show ?thesis using Cons isin_IL1 by auto
  next
    case False
    then have "set_ItemList (minus_LIL k (a # as) il) = set_ItemList (insert a (minus_LIL k as il))" by simp
    also have "... = set_ItemList (minus_LIL k as il) \<union> {a}" using IL_insert1 Cons LIL_minus_inv by simp
    then show ?thesis using Cons isin_IL1 by auto
  qed
qed

lemma IL_minus_inv: "inv_IL il1 \<Longrightarrow> length (froms il2) \<ge> length (froms il1) \<Longrightarrow> inv_IL (minus_IL il1 il2)"
  using LIL_minus_inv by (cases il1) (auto simp add: minus_IL_def)

lemma IL_minus: "inv_IL il2 \<Longrightarrow> inv_IL il1 \<Longrightarrow> length (froms il2) \<ge> length (froms il1) 
  \<Longrightarrow> set_ItemList (minus_IL il1 il2) = set_ItemList il1 - set_ItemList il2"
  using LIL_minus by (cases il1) (auto simp add: minus_IL_def)

lemma length_IL_minus: 
  assumes inv: "inv_IL il1" shows "length (froms (minus_IL il1 il2)) = length (froms il1)"
proof-
  obtain as m where "il1 = ItemList as m"
    using il_decomp by blast
  then show ?thesis using inv length_minus_LIL by (auto simp add: minus_IL_def)
qed

lemma length_IL_minus1: "length (froms il1) > 0 \<Longrightarrow> length (froms (minus_IL il1 il2)) = length (froms il1)" 
  by (auto simp add: minus_IL_def)


section \<open>Earley ItemList algorithm\<close>


definition step_rel :: "('n, 'a) item set list \<Rightarrow> ('n, 'a) item set \<times> ('n, 'a) item set \<Rightarrow> ('n, 'a) item set \<times> ('n, 'a) item set \<Rightarrow> bool" where
  "step_rel  \<equiv> Close2"

definition Init_L :: "('n,'a) item list" where
  "Init_L =  map (\<lambda> p. Item p 0 0) (filter (\<lambda> p. lhs p = (S)) ps)"

definition Scan_L :: "('n,'a) item list \<Rightarrow> nat \<Rightarrow> ('n,'a) item list" where
  "Scan_L Bs k = (let x = Some(w ! k) in map mv_dot (filter (\<lambda> b. next_symbol b = x) Bs))"

fun step_fun :: "('n, 'a) item list list \<Rightarrow>  ('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList" where
  "step_fun Bs ((ItemList (x#xs) fs), C) = (let nexts = (if is_complete x then Complete_L Bs x else Predict_L x (length Bs)) in
    ( minus_IL (union_LIL nexts (ItemList (x#xs) fs)) (insert x C), insert x C) )"

definition steps :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList \<Rightarrow> (('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList) option" where
  "steps Bs BC = while_option (\<lambda>(ilB,ilC). list ilB \<noteq> []) (step_fun Bs) BC"

definition close2_L :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) efficientItemList \<Rightarrow> ('n, 'a) item list" where
  "close2_L Bs B = list (snd (the (steps Bs (B, empty_IL (length Bs)))))"

fun bins_L :: "nat \<Rightarrow> ('n,'a) item list list" where
  "bins_L 0 = [close2_L [] (IL_of_List 0 Init_L)]" |
  "bins_L (Suc k) = (let Bs = bins_L k in Bs @ [close2_L Bs (IL_of_List (length Bs) (Scan_L (last Bs) k))])"

fun recognized_L :: "('n, 'a) item list \<Rightarrow> bool" where
"recognized_L [] = False" |
"recognized_L (a#as) = (is_final a \<or> recognized_L as)"

(*defined as a function for time_fun (could maybe be solved differently)*)
definition earley_recognized where
"earley_recognized _ = recognized_L (last (bins_L (length w)))"

subsection \<open>Correctness of ItemList algorithm\<close>

lemma Init_L_eq_Init: "set Init_L = Init"
  by (auto simp add: Init_L_def Init_def)

lemma Scan_L_eq_Scan: "k < length w \<Longrightarrow> set (Scan_L Bs k) = Scan (set Bs) k"
  by (auto simp add: Scan_L_def Scan_def w_def)

(* now already in Earley as set_Predict_L
lemma Predict_eq: "set (Predict_L st k) = Predict st k"
  by (auto simp add: Predict_L_def Predict_def)
*)

lemma Complete_eq: "from st < length Bs \<Longrightarrow> set (Complete_L Bs st) = Complete (map set Bs) st"
  by (auto simp add: Complete_L_def Complete_def nths_map)
end

context Earley_Gw_eps
begin

lemma wf1_Predict_L: "wf_item1 st k \<Longrightarrow> wf_bin1 (set (Predict_L st k)) k"
  using wf1_Predict set_Predict_L by (auto simp add: wf_bin1_def)

lemma wf1_Complete_L: 
  assumes "wf_bins1 (map set Bs)" "wf_item1 st (length Bs)" "is_complete st" 
    shows "wf_bin1 (set (Complete_L Bs st)) (length Bs)"
proof-
  have 1: "\<forall>x \<in>  (set (filter (\<lambda> b. next_sym_Nt b (lhs(prod st))) (Bs ! from st))). wf_item x (from st)"
    using assms by (simp add: wf_bin1_def wf_bins1_def wf_item1_def)
  then have 2: "\<forall>x \<in> (set  (filter (\<lambda> b. next_sym_Nt b (lhs(prod st))) (Bs ! from st))). wf_item (mv_dot x) (from st)"
    using assms 1 unfolding wf_item_def is_complete_def next_symbol_def mv_dot_def
    by (auto split: if_splits)
  have "from st < length Bs"
    using assms(2,3) wf_item1_def by auto
  then show ?thesis
     using assms 2 Complete_L_def in_set_conv_nth wf1_Complete wf_bin1_def wf_bins1_def by fastforce  
 qed

lemma forall_from_Suc: "wf_bin1 as k \<Longrightarrow> \<forall>a \<in> as. from a < (Suc k)"
  by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)

lemma test:
  assumes inv: "inv_IL (ItemList (a#as) m1)" "inv_IL (ItemList bs m2)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and wf: "wf_bins1 (map set Bs)" "wf_item1 a (length Bs)"
  and sf: "step_fun Bs ((ItemList (a#as) m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"
  shows  "set as' = (set as \<union> set ((if is_complete a then Complete_L Bs a else Predict_L a (length Bs)))) - (set bs \<union> {a})"
proof-
  let ?step = "(if is_complete a then Complete_L Bs a else Predict_L a (length Bs))"
  have wf_step: "wf_bin1 (set ?step) (length Bs)" using wf wf1_Predict_L wf1_Complete_L by auto
  then have 1: "inv_IL (union_LIL ?step (ItemList (a#as) m1))" using LIL_union_inv[of "(ItemList (a#as) m1)" ?step] inv(1) leng(1)
    forall_from_Suc[of "set ?step" "length Bs"] by auto
  have 2: "inv_IL (insert a (ItemList bs m2))" using insert_inv_IL[of bs m2 a] inv(2) wf(2)
    by (fastforce simp add: wf_item1_def wf_item_def leng(2))
  have "set as' = set_ItemList (minus_IL (union_LIL ?step (ItemList (a#as) m1)) (insert a (ItemList bs m2)))"
    using sf by auto
  also have "... = set_ItemList (union_LIL ?step (ItemList (a#as) m1)) - set_ItemList (insert a (ItemList bs m2))"
    using IL_minus leng 1 2 by auto
  also have "... = (set (a#as) \<union> set ?step) - set_ItemList (insert a (ItemList bs m2))" 
    using LIL_union[of "ItemList (a#as) m1" ?step] wf_step forall_from_Suc[of "set ?step" "length Bs"] inv(1)
    by (metis Un_commute efficientItemList.sel(1,2) leng(1) set_ItemList.simps)
  also have "... = (set (a#as) \<union> set ?step) - (set bs \<union> {a})" using IL_insert1[of "ItemList bs m2" a] 
     inv by (auto simp add: leng)

  finally show ?thesis by auto
qed

lemma step_fun_sound: 
  assumes cons: "as \<noteq> []" 
  and wf: "wf1_IL (ItemList as m1) (length Bs)" "wf_bins1 (map set Bs)"
  and inv: "inv_IL (ItemList as m1)" "inv_IL (ItemList bs m2)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and sf: "step_fun Bs ((ItemList as m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"
shows "step_rel (map set Bs) (set as,set bs) (set as', set bs')"
proof-
  have comp: "\<forall>a \<in> set as. is_complete a \<longrightarrow> from a < length Bs" using wf by (auto simp add: wf_bin1_def wf_item1_def)
  from cons obtain a ass where P :"as = a # ass"
    using list.exhaust by auto 

  let ?xs = "if is_complete a then Complete (map set Bs) a else Predict a (length Bs)"
  let ?xsL = "if is_complete a then Complete_L Bs a else Predict_L a (length Bs)"

  have "a \<in> set as"
    by (auto simp add: P next_symbol_def)
  then have 1: "(map set Bs) \<turnstile> (set as, set bs) \<rightarrow> ((set as \<union> ?xs) - (set bs \<union> {a}), (set bs \<union> {a}))"
    using Close2.Complete Close2.Predict
    by (smt (verit, best) Un_insert_right boolean_algebra.disj_zero_right length_map)

  have "wf_item1 a (length Bs)" using wf by (auto simp add: wf_bin1_def P)
  then have 2: "set as' = (set ass \<union> set ?xsL) - (set bs \<union> {a})"
    using P inv sf test[of a ass m1 bs m2 Bs as' m3 bs' m4] wf leng by blast
  have "set bs' = (set bs \<union> {a})" using inv sf P IL_insert1[of "(ItemList bs m2)" a] leng by auto 

  then show ?thesis using 1 2
    using Complete_eq P set_Predict_L comp step_rel_def by fastforce
qed
  
lemma step_fun_inv1: 
  assumes ne: "as \<noteq> []"
  and inv: "inv_IL (ItemList as m1)"
  and wf: "wf_bins1 (map set Bs)" "wf_bin1 (set as) (length Bs)"
  and sf: "step_fun Bs ((ItemList as m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
shows "inv_IL (ItemList as' m3)"
proof-
  from ne obtain a ass where P: "as = a#ass"
    by (meson neq_Nil_conv)
  let ?step = "(if is_complete a then Complete_L Bs a else Predict_L a (length Bs))"
  have "wf_item1 a (length Bs)" using P wf by (auto simp add: wf_bin1_def)
  then have wf_step: "wf_bin1 (set ?step) (length Bs)" using wf wf1_Predict_L wf1_Complete_L by auto
  then have "\<forall>x \<in> set ?step. from x < Suc (length Bs)" by (auto simp add: forall_from_Suc)
  then show ?thesis using P IL_minus_inv[of "(union_LIL ?step (ItemList (a#ass) m1))" "(insert a (ItemList bs m2))"] sf leng
      LIL_union_inv inv
      length_LIL_union[of ?step "ItemList (a#ass) m1"] length_IL_insert[of a "ItemList bs m2"] by auto
qed

lemma step_fun_inv2: 
  assumes ne: "as \<noteq> []"
  and wf: "wf_bin1 (set as) (length Bs)"
  and leng: "length m2 = Suc (length Bs)"
  and inv: "inv_IL (ItemList bs m2)"
  and sf: "step_fun Bs ((ItemList as m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"
shows "inv_IL (ItemList bs' m4)"
proof-
  from ne obtain a ass where P: "as = a#ass"
    by (meson neq_Nil_conv)
  then show ?thesis using insert_inv_IL1[of "(ItemList bs m2)" a] sf inv wf leng 
    by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
qed
  
lemma step_fun_wf: 
  assumes ne: "as \<noteq> []"
  and wf: "wf_bins1 (map set Bs)" "wf1_IL (ItemList as m1) (length Bs)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and inv: "inv_IL (ItemList as m1)" "inv_IL (ItemList bs m2)"
  and sf: "step_fun Bs ((ItemList as m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"  
  shows "wf1_IL (ItemList as' m3) (length Bs)"
proof -  
  from assms obtain a ass where P: "as = a # ass"
    by (meson neq_Nil_conv)
  let ?step = "(if is_complete a then Complete_L Bs a else Predict_L a (length Bs))"
  have "wf_item1 a (length Bs)" using P assms by (auto simp add: wf_bin1_def)
  then have "wf_bin1 (set ?step) (length Bs)" using assms wf1_Predict_L wf1_Complete_L by auto
  then have 1: "wf_bin1 ((set as \<union> set ?step) - (set bs \<union> {a})) (length Bs)" 
    using wf_bin1_def wf by auto
  from wf P have "wf_item1 a (length Bs)" by (auto simp add: wf_bin1_def)
  then have "set as' = (set ass \<union> set ?step) - (set bs \<union> {a})"
    using P inv sf leng wf test[of a ass m1 bs m2 Bs as'] by blast
  then show ?thesis using P 1 by auto
qed

lemma step_fun_wf2: 
  assumes ne: "as \<noteq> []"
  and wf: "wf1_IL (ItemList as m1) (length Bs)" "wf1_IL (ItemList bs m2) (length Bs)"
  and leng: "length m2 = Suc (length Bs)"
  and inv: "inv_IL (ItemList bs m2)"
  and sf: "step_fun Bs ((ItemList as m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"
  shows "wf1_IL (ItemList bs' m4) (length Bs)"
proof-
  from \<open>as \<noteq> []\<close> obtain a ass where P: "as = a#ass" by (meson neq_Nil_conv)
  then have "from a < Suc (length Bs)" using wf by (auto simp add: wf_bin1_def wf_item1_def wf_item_def) 
  then have "set bs' = set bs \<union> {a}" using inv sf P IL_insert1[of "(ItemList bs m2)" a] leng 
      by auto
  then show ?thesis using assms P by (auto simp add: wf_bin1_def)
qed

lemma length_step_fun1:
  assumes ne: "as \<noteq> []"
  and sf: "step_fun Bs ((ItemList as m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"
  and leng: "length m1 = Suc (length Bs)"
shows "length m3 = Suc (length Bs)"
proof-
  obtain a ass where P: "as = a#ass"
    by (meson ne recognized_L.cases)
  let ?step = "if is_complete a then Complete_L Bs a else Predict_L a (length Bs)"
  from P have "minus_IL (union_LIL ?step (ItemList (a # ass) m1)) (ItemList bs' m4) = ItemList as' m3"
    using assms by auto
  then show ?thesis 
    by (metis efficientItemList.sel(2) leng length_IL_minus1 length_LIL_union zero_less_Suc)
qed

lemma length_step_fun2:
  assumes ne: "as \<noteq> []"
  and sf: "step_fun Bs ((ItemList as m1),(ItemList bs m2)) = ((ItemList as' m3), (ItemList bs' m4))"
  and leng: "length m2 = Suc (length Bs)"
shows "length m4 = Suc (length Bs)"
proof-
  obtain a ass where P: "as = a#ass"
    by (meson ne recognized_L.cases)
  then show ?thesis using assms length_IL_insert[of a "ItemList bs m2"] by (auto simp del: insert.simps)
qed

lemma steps_sound:
  assumes wf: "wf1_IL (ItemList as m1) (length Bs)"  "wf_bins1 (map set Bs)"
  and leng: "length m1 = Suc (length Bs)" "length m2 = Suc (length Bs)"
  and inv: "inv_IL (ItemList as m1)" "inv_IL (ItemList bs m2)"
  and step: "steps Bs ((ItemList as m1),(ItemList bs m2)) = Some ((ItemList as' m3), (ItemList bs' m4))"
shows "((step_rel (map set Bs))^**) (set as, set bs) ({},set bs')"
proof -
  let ?P = "\<lambda>(il1,il2). inv_IL il1 \<and> inv_IL il2 \<and> wf1_IL il1 (length Bs) \<and> wf_bins1 (map set Bs) 
              \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs) 
              \<and> (step_rel (map set Bs))^** (set as, set bs) (set (list il1),set (list il2))"
  let ?b = "\<lambda>(il1, il2). (list il1) \<noteq> []"
  let ?c = "\<lambda>(il1, il2). step_fun Bs (il1,il2)"

  have 1: "(?P (il1,il2) \<Longrightarrow> ?b (il1,il2) \<Longrightarrow> ?P (?c (il1,il2)))" for il1 il2
  proof-
    assume assm: "?P (il1,il2)" and ne: "?b (il1,il2)"
    obtain xs n1 ys n2 where P: "il1 = (ItemList xs n1) \<and> il2 = (ItemList ys n2)"
      by (meson inv_IL.cases)
    obtain xs' n1' ys' n2' where c: "?c (il1, il2) = ((ItemList xs' n1'), (ItemList ys' n2'))"
      by (metis inv_IL.cases surj_pair)
    obtain x xss where P_xs: "xs = x#xss" using ne P
      using list.exhaust by auto
    then have 11: "length n1' = Suc (length Bs) \<and> length n2' = Suc (length Bs)"
      using assm length_step_fun1[of xs Bs n1 ys n2 xs' n1' ys' n2'] 
            length_step_fun2[of xs Bs n1 ys n2 xs' n1' ys' n2'] P c by auto
    moreover have 12: "inv_IL (ItemList xs' n1') \<and> inv_IL (ItemList ys' n2')" 
      using step_fun_inv1[of xs n1 Bs ys n2 xs' n1' ys' n2'] 
            step_fun_inv2[of xs Bs n2 ys n1 xs' n1' ys' n2'] assm P c P_xs by fastforce
    moreover have 13: "wf1_IL (ItemList xs' n1') (length Bs) \<and> wf_bins1 (map set Bs)" 
      using step_fun_wf[of xs Bs n1 n2 ys] assm P c P_xs by force
    moreover have "(step_rel (map set Bs))^** (set as, set bs) (set xs', set ys')"
      using step_fun_sound[of xs n1 Bs ys n2] assm P c P_xs by auto
    ultimately show ?thesis using c by auto
  qed

  have stop: "as' = []" using step while_option_stop[of ?b ?c "((ItemList as m1),(ItemList bs m2))"] by (auto simp add: steps_def)

  have "?P ((ItemList as m1),(ItemList bs m2))" using wf inv leng by auto
  then have "?P ((ItemList as' m3), (ItemList bs' m4))"using 
      while_option_rule[of ?P _ _ "((ItemList as m1),(ItemList bs m2))" "((ItemList as' m3), (ItemList bs' m4))"] 1
    by (smt (verit) case_prodE case_prod_conv local.step steps_def)
  then show ?thesis using stop by auto     
qed

lemma steps_sound1: 
  assumes wf: "wf1_IL (ItemList as m1) (length Bs)"  "wf_bins1 (map set Bs)"
  and leng: "length m1 = Suc (length Bs)"
  and inv: "inv_IL (ItemList as m1)"
  and step: "steps Bs ((ItemList as m1),empty_IL (length Bs)) = Some (B',C)" 
shows "((step_rel (map set Bs))^**) (set as,{}) ({},set (list C))"
proof-
  have "inv_IL (empty_IL (length Bs))"
    by (simp add: empty_inv)
  moreover have "wf1_IL (empty_IL (length Bs)) (length Bs)" by (simp add: empty_IL_def wf_bin1_def)
  moreover have "length (froms (empty_IL (length Bs))) = Suc (length Bs)" by simp
  ultimately show ?thesis using steps_sound assms
    by (metis Earley_Gw.set_ItemList.simps efficientItemList.collapse set_empty_IL)
qed


 

lemma step_fun_inv1_il: 
  assumes ne: "(list il1) \<noteq> []"
  and inv: "inv_IL il1"
  and wf: "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and sf: "step_fun Bs (il1,il2) = (il1', il2')"
shows "inv_IL il1'"
  using step_fun_inv1 il_decomp sf inv leng wf ne
  by (metis efficientItemList.collapse set_ItemList.elims)
 

lemma step_fun_inv2_il: 
  assumes ne: "(list il1) \<noteq> []"
  and wf: "wf1_IL il1 (length Bs)"
  and leng: "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il2"
  and sf: "step_fun Bs (il1,il2) = (il1', il2')"
shows "inv_IL il2'"
 using step_fun_inv2 il_decomp ne wf leng inv sf
  by (metis efficientItemList.collapse set_ItemList.elims)
  
lemma step_fun_wf_il: 
  assumes ne: "(list il1) \<noteq> []"
  and wf: "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il1" "inv_IL il2"
  and sf: "step_fun Bs (il1,il2) = (il1', il2')"  
shows "wf1_IL il1' (length Bs)"
  using step_fun_wf il_decomp ne wf inv sf leng
  by (metis efficientItemList.collapse)

lemma step_fun_wf2_il: 
   assumes ne: "(list il1) \<noteq> []"
  and wf: "wf1_IL il1 (length Bs)" "wf1_IL il2 (length Bs)"
  and leng: "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il2"
  and sf: "step_fun Bs (il1,il2) = (il1', il2')"
shows "wf1_IL il2' (length Bs)"
  using step_fun_wf2 il_decomp ne wf inv sf leng
  by (metis efficientItemList.collapse)

lemma length_step_fun1_il: 
  assumes "list il1 \<noteq> []"  
          "step_fun Bs (il1, il2) = (il1', il2')" "length (froms il1) = Suc (length Bs)" 
  shows "length (froms il1') = Suc (length Bs)"
  using length_step_fun1 il_decomp assms by (metis efficientItemList.collapse)

lemma length_step_fun2_il: 
  assumes "list il1 \<noteq> []" "step_fun Bs (il1, il2) = (il1', il2')" 
          "length (froms il2) = Suc (length Bs)"
  shows "length (froms il2') = Suc (length Bs)"
  using length_step_fun2 il_decomp assms by (metis efficientItemList.collapse)
  

lemma steps_inv1: 
  assumes inv: "inv_IL il1" "inv_IL il2"
  and wf: "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and step: "steps Bs (il1,il2) = Some (il1', il2')"
shows "inv_IL il1'"
  using while_option_rule[where P= "\<lambda>(il1,il2). inv_IL il1 \<and> inv_IL il2 \<and> wf1_IL il1 (length Bs) \<and> wf_bins1 (map set Bs) \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs)"] 
    step_fun_inv1_il step_fun_inv2_il
    length_step_fun1_il length_step_fun2_il step_fun_wf_il step inv wf leng unfolding steps_def
 by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)


lemma steps_inv2: 
  assumes inv: "inv_IL il2" "inv_IL il1"
  and wf: "wf1_IL il1 (length Bs)" "wf_bins1 (map set Bs)"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and step: "steps Bs (il1,il2) = Some (il1', il2')"
shows "inv_IL il2'"
  using while_option_rule[where P= "\<lambda>(il1,il2). inv_IL il2 \<and> inv_IL il1 \<and> wf1_IL il1 (length Bs) \<and> wf_bins1 (map set Bs) \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs)"] 
    step_fun_inv2_il step_fun_inv1_il length_step_fun1_il length_step_fun2_il step_fun_wf_il step inv wf leng unfolding steps_def 
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)
(*
lemma steps_wf1: 
  assumes wf: "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)"
  and inv: "inv_IL il1" "inv_IL il2"
  and sf: "steps Bs (il1,il2) = Some (il1', il2')"  
shows "wf1_IL il1' (length Bs)"
  using while_option_rule[where P= "\<lambda>(il1,il2). wf1_IL il1 (length Bs) \<and> inv_IL il1 \<and> inv_IL il2 \<and> wf_bins1 (map set Bs)"] 
    step_fun_wf_il step_fun_inv1_il step_fun_inv2_il wf sf inv unfolding steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)*)



lemma steps_wf2: 
  assumes wf: "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)" "wf1_IL il2 (length Bs)"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il1" "inv_IL il2"
  and sf: "steps Bs (il1,il2) = Some (il1', il2')"  
shows "wf1_IL il2' (length Bs)"
  using while_option_rule[where P= "\<lambda>(il1,il2). wf1_IL il2 (length Bs) \<and> wf1_IL il1 (length Bs) \<and> inv_IL il1 \<and> inv_IL il2 \<and> length (froms il1) = Suc (length Bs) \<and> length (froms il2) = Suc (length Bs) \<and> wf_bins1 (map set Bs)"] 
    step_fun_wf_il step_fun_wf2_il step_fun_inv1_il step_fun_inv2_il length_step_fun1_il length_step_fun2_il wf sf inv leng unfolding steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)


(*
lemma step_fun_sound_il: "list il1 \<noteq> [] \<Longrightarrow> wf1_IL il1 (length Bs) \<Longrightarrow> inv_IL il1 \<Longrightarrow> inv_IL il2
 \<Longrightarrow> step_fun Bs (il1,il2) = (il1', il2')
 \<Longrightarrow> step_rel (map set Bs) (set_ItemList il1,set_ItemList il2) (set_ItemList il1', set_ItemList il2')"
  using il_decomp step_fun_sound
  by (metis efficientItemList.sel(1) set_ItemList.elims)*)



end (*Earley_Gw_eps*)


context Earley_Gw
begin


(* This is the wellfounded relation for the termination proof.
It should really be called step_fun_less but I have kept the original name.
I adapted it to work on lists rather that sets.
To simplify matters, I dropped the parameter k *)
definition step_fun_less :: "nat \<Rightarrow> ((('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList) \<times> (('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList)) set" where
"step_fun_less k = (\<lambda>(B,C). card({x. wf_item x k} - (set_ItemList B \<union> set_ItemList C))) <*mlex*> inv_image finite_psubset (set_ItemList o fst)"

lemma step_fun_less_eq: "((A, B), (C,D)) \<in> step_fun_less k \<longleftrightarrow> ((set_ItemList A, set_ItemList B), (set_ItemList C, set_ItemList D)) \<in> Close2_less k"
  by (simp add: step_fun_less_def Close2_less_def mlex_prod_def)

lemma wf_step_fun_less: "wf (step_fun_less k)"
  by (simp add: step_fun_less_def wf_mlex)
end

context Earley_Gw_eps
begin

(* This is the important property of step_fun: it goes down in the Close2_less relation.
   The wf_items premises may not be 100% right *)
lemma step_fun_less_step: 
  assumes ne: "(list il1) \<noteq>[]" 
  and wf: "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)" "wf1_IL il2 (length Bs)"
  and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  and inv: "inv_IL il1" "inv_IL il2"
shows "(step_fun Bs (il1,il2), (il1,il2)) \<in> (step_fun_less (length Bs))"
proof-
  let ?B' = "fst (step_fun Bs (il1,il2))"
  let ?C' = "snd (step_fun Bs (il1,il2))"
  have 1: "(?B', ?C') = step_fun Bs (il1,il2) " by simp

  obtain as m1 bs m2 where P1: "il1 = (ItemList as m1) \<and> il2 = (ItemList bs m2)"
    by (meson inv_IL.cases)
  obtain as' m1' bs' m2' where P2: "?B' = (ItemList as' m1') \<and> ?C' = (ItemList bs' m2')"
    by (meson inv_IL.cases)

  have "Close2 (map set Bs) (set_ItemList il1, set_ItemList il2) (set_ItemList ?B', set_ItemList ?C')"
    using step_fun_sound step_rel_def assms P1 P2
    by (metis "1" efficientItemList.sel(1,2) set_ItemList.elims) 
  then show ?thesis using assms Close2_less_step step_fun_less_eq 1
    by (metis length_map)
qed

end (*Earley_Gw*)

context Earley_Gw_eps
begin


lemma step_fun_wf_items: 
  assumes wf: "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)" "wf1_IL il2 (length Bs)"
    and inv: "inv_IL il1" "inv_IL il2" 
    and ne:"(list il1) \<noteq> []"
    and leng: "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  shows "\<exists>B' C'. step_fun Bs (il1,il2) = (B',C') \<and> inv_IL B' \<and> inv_IL C' \<and> wf1_IL B' (length Bs) \<and> wf1_IL C' (length Bs) 
    \<and> length (froms B') = Suc (length Bs) \<and> length (froms C') = Suc (length Bs)"
proof-
  obtain as m1 bs m2 where P1: "il1 = (ItemList as m1) \<and> il2 = (ItemList bs m2)"
    by (meson inv_IL.cases)
  obtain as' m1' bs' m2' where P: "step_fun Bs (il1,il2) = ((ItemList as' m1'),(ItemList bs' m2'))"
    by (metis efficientItemList.exhaust surj_pair)
  then have 1: "wf1_IL (ItemList as' m1') (length Bs) \<and> wf1_IL (ItemList bs' m2') (length Bs)"
    using step_fun_wf step_fun_wf2 assms P1
    by (metis efficientItemList.sel(1,2))
  moreover have "inv_IL (ItemList as' m1') \<and> inv_IL (ItemList bs' m2')" using P P1
    using assms step_fun_inv1 step_fun_inv2
    by (metis efficientItemList.sel(1,2) set_ItemList.elims)
  moreover have "length m1' = Suc (length Bs) \<and> length m2' = Suc (length Bs)"
    using leng P P1 length_step_fun1 length_step_fun2 ne by simp
  ultimately show ?thesis using P by auto
qed


theorem Close2_L_NF: "\<lbrakk>wf_bins1 (map set Bs); wf1_IL il1 (length Bs); wf1_IL il2 (length Bs); 
    inv_IL il1; inv_IL il2; length (froms il1) = Suc (length Bs); length (froms il2) = Suc (length Bs)\<rbrakk>
  \<Longrightarrow> \<exists>il1' il2'. steps Bs (il1,il2) = Some (il1',il2')"
unfolding steps_def
using wf_step_fun_less[of "length Bs"]
proof (induction "(il1,il2)" arbitrary: il1 il2 rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume ne: "list il1 = []"
    thus ?thesis by(simp add: while_option_unfold[of _ _ "(il1,il2)"])
  next
    let ?steps = "while_option (\<lambda>(B, C). list B \<noteq> []) (step_fun Bs)"
    assume cons: "list il1 \<noteq> []"
    then obtain il1' il2'
      where "(il1',il2') = step_fun Bs (il1,il2)" and wf': "wf1_IL il1' (length Bs)" "wf1_IL il2' (length Bs)" 
        and inv': "inv_IL il1'" "inv_IL il2'"
        and leng': "length (froms il1') = Suc (length Bs)" "length (froms il2') = Suc (length Bs)"
      using step_fun_wf_items[OF less.prems(1,2,3,4,5) cons less.prems(6,7)] by fastforce
    then have "((il1',il2'), (il1, il2)) \<in> step_fun_less (length Bs)"
      using cons less.prems step_fun_less_step by presburger
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf' inv' leng']
    show ?thesis
      by (simp add: \<open>(il1',il2') = step_fun Bs (il1,il2)\<close> while_option_unfold)
  qed
qed

lemma close2_L_eq_Close1: 
  assumes "wf_bins1 (map set Bs)" "wf1_IL il (length Bs)" "inv_IL il" "length (froms il) = Suc (length Bs)"
  shows "set (close2_L Bs il) = Close1 (map set Bs) (set (list il))"
proof-
  have "wf1_IL (empty_IL (length Bs)) (length Bs) \<and> inv_IL (empty_IL (length Bs)) 
      \<and> length (froms (empty_IL (length Bs))) = Suc (length Bs)"
    by (metis empty_iff empty_inv set_empty_IL wf_bin1_def length_empty_IL)
  then obtain il1 il2 where D1: "steps Bs (il,(empty_IL (length Bs))) = Some (il1,il2)" using assms Close2_L_NF
    by blast
  then have "(map set Bs) \<turnstile> (set (list il), {}) \<rightarrow>* ({}, set (list il2))" using steps_sound
    by (metis assms(1,2,3,4) efficientItemList.collapse step_rel_def steps_sound1)
  then have DC1: "set (list il2) = Close1 (map set Bs) (set (list il))"
    by (simp add: Close1_subset_Close2 Close2_steps_subset_Close1' subset_antisym)
  have "set (list il2) = set (close2_L Bs il)" using D1 by (auto simp add: close2_L_def)
  then show ?thesis using DC1 by auto
qed

lemma close2_L_eq_close2: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_IL il (length Bs) \<Longrightarrow> length (froms il) = Suc (length Bs) 
  \<Longrightarrow> inv_IL il \<Longrightarrow> set (close2_L Bs il) = close2 (map set Bs) (set_ItemList il)"
  by (auto simp add: close2_L_eq_Close1 close2_eq_Close1)

lemma close2_L_eq_Close: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_IL il (length Bs) \<Longrightarrow> length (froms il) = Suc (length Bs) 
  \<Longrightarrow> inv_IL il \<Longrightarrow> set (close2_L Bs il) = Close (map set Bs) (set_ItemList il)"
  by (auto simp add: close2_L_eq_Close1 Close1_eq_Close)

lemma length_bins_L: "length (bins_L k) = Suc k"
  by (induction k) (auto simp add: Let_def)

theorem bins_L_eq_bins: "k \<le> length w \<Longrightarrow> map set (bins_L k) = bins k"
proof (induction k)
  case 0
  have "wf_bins1 (map set []) \<and> wf_bin1 (set Init_L) 0"
    by (simp add: Init_L_eq_Init wf_bin1_Init wf_bins1_def)
  then have "wf_bins1 (map set []) \<and> wf1_IL (IL_of_List 0 Init_L) 0 \<and> inv_IL (IL_of_List 0 Init_L)
    \<and> length (froms (IL_of_List 0 Init_L)) = Suc 0"
    using IL_of_List_inv forall_from_Suc set_IL_of_List length_IL_of_List by presburger
  then have "set (close2_L [] (IL_of_List 0 Init_L)) = Close [] Init"
    using close2_L_eq_Close[of "[]" "IL_of_List 0 Init_L"]
    using Init_L_eq_Init forall_from_Suc list.map_disc_iff set_IL_of_List set_ItemList.elims wf_bin1_Init by force
  then show ?case by simp
next
  case (Suc k)
  let ?Bs = "bins_L k"
  have kl: "k < length w" using Suc by auto
  then have 1: "set (Scan_L (last ?Bs) k) = (Scan (last (map set ?Bs)) k)" using Suc
    by (metis Scan_L_eq_Scan Suc_leD bins_nonempty map_is_Nil_conv last_map)
  have "wf_bin1 (set (last ?Bs)) k"
    by (metis Earley_Gw.bins_nonempty Suc.IH Suc.prems Suc_leD last_map list.map_disc_iff wf_bin1_last)
  then have 2: "wf1_IL (IL_of_List (Suc k) (Scan_L (last ?Bs) k)) (length ?Bs)"
    by (metis Scan_L_eq_Scan wf_bin1_Scan forall_from_Suc kl set_IL_of_List length_bins_L)
  have 3: "wf_bins1 (map set (bins_L k))"
    by (simp add: Suc.IH Suc.prems Suc_leD wf_bins1_bins)
  have 4: "length (froms (IL_of_List  (Suc k) (Scan_L (last ?Bs) k))) = Suc (length ?Bs)"
    by (simp add: length_bins_L)

  then have "set (close2_L ?Bs (IL_of_List  (Suc k) (Scan_L (last ?Bs) k))) = Close (map set ?Bs) (Scan (last (map set ?Bs)) k)"
    using close2_L_eq_Close[OF 3 2 4] IL_of_List_inv
        1 2 3 forall_from_Suc
    using Suc.IH Suc.prems Suc_leD kl set_IL_of_List wf_bin1_Scan wf_bin1_last by presburger
  then show ?case using Suc by (auto simp add: Let_def length_bins_L)
qed 

corollary bins_L_eq_\<S>: "i \<le> k \<Longrightarrow> k \<le> length w \<Longrightarrow> set (bins_L k ! i) = \<S> i"
  using bins_eq_\<S> bins_L_eq_bins length_bins_L
  by (metis bins_L_eq_bins bins_eq_\<S>_gen le_imp_less_Suc length_bins_L nth_map)

lemma recognized_set: "recognized_L as = (\<exists>x \<in> set as. is_final x)"
  by (induction as) auto

lemma earley_recognized_eq_recognized_Earley: "earley_recognized y \<longleftrightarrow> recognized Earley"
proof
  assume "earley_recognized y"
  then have "\<exists>x \<in> set (last (bins_L (length w))). is_final x" using recognized_set earley_recognized_def
    by metis
  then obtain x where P: "is_final x \<and> x \<in> set (last (bins_L (length w)))" by blast
  then have "x \<in> \<S> (length w)" using bins_L_eq_\<S> length_bins_L last_conv_nth
    by (metis bins_L_eq_bins bins_nonempty diff_Suc_1 map_is_Nil_conv nat_le_linear)
  then show "recognized Earley" using P
    using accepted_def accpted_sound correctness_Earley by auto
next
  assume "recognized Earley"
  then obtain x where P: "is_final x \<and> (x, length w) \<in> Earley"
    using recognized_def by blast
  then have "x \<in> \<S> (length w)"
    using Earley_eq_\<S> by auto
  then have "x \<in> set (last (bins_L (length w)))" using bins_L_eq_\<S> length_bins_L last_conv_nth
    by (metis bins_L_eq_bins bins_nonempty diff_Suc_1 map_is_Nil_conv nat_le_linear)
  then have "\<exists>x \<in> set (last (bins_L (length w))). is_final x" using P by blast
  then show "earley_recognized y" using recognized_set earley_recognized_def by metis
qed

theorem correctness_earley:
  shows "earley_recognized y \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using correctness_Earley earley_recognized_eq_recognized_Earley by metis 

end

section \<open>Space analysis\<close>

(*Section space analysis*)
context Earley_Gw
begin

definition "K = Max { length (rhs r) | r. r \<in> set ps }"
definition "N = length w"
definition "L = length ps"

lemma card_wf: 
  assumes "\<forall>p \<in> set ps. length (rhs p) \<le> k" "\<forall>x \<in> bs. wf_item x i" 
  shows "card bs \<le> (length ps) * (Suc k) * (Suc i)"
proof -
  let ?f = "\<lambda> (p, m, k). Item p m k"
  define Top where "Top = (P \<times> {0..k} \<times> {0..i})"
  hence top_card: "card Top = card (set ps) * Suc k * (Suc i)"
    using Groups_Big.card_cartesian_product by (auto simp add: add_mult_distrib add_mult_distrib2)
  have fin: "finite Top" using finite_cartesian_product finite Top_def by blast
  have inj: "inj_on ?f Top"
    unfolding Top_def inj_on_def by simp
  have 1: "bs \<subseteq> ?f ` Top"
  proof
    fix x
    assume "x \<in> bs"
    then have "\<exists>p m k. x = Item p m k \<and> p \<in> P \<and> m \<le> length (rhs p) \<and> k \<le> i \<and> i \<le> length w"
      by (metis Earley_Gw.wf_item_def item.exhaust_sel assms(2))
    then obtain p m j where x: "x = Item p m j" and wf: "p \<in> P \<and> m \<le> length (rhs p) \<and> j \<le> i \<and> i \<le> length w" by blast
    then have 1: "(p, m, j) \<in> Top" using assms by (auto simp add: Top_def)
    have "?f (p, m, j) = x" using x by simp
    then show "x \<in> (\<lambda>(p, m, k). Item p m k) ` Top" using 1 by blast
  qed

  then have "card  bs \<le> card Top" using fin
    by (simp add: surj_card_le)
  then show ?thesis using top_card card_length
    by (metis (no_types, lifting) dual_order.trans mult_le_mono1)
qed

lemma prod_length_bound: 
  assumes "p \<in> set ps" shows "length (rhs p) \<le> K"
proof-
  have "K = Max (length ` (rhs ` (set ps)))" using K_def
    by (metis Setcompr_eq_image image_image)
  then show ?thesis using assms K_def by auto
qed

lemma card_wf1: "\<forall>x \<in> bs. wf_item x i \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
  using card_wf L_def prod_length_bound by simp

lemma card_wf_bin1: "wf_bin1 bs i \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
  using card_wf1 by (simp add: wf_bin1_def wf_item1_def)

lemma card_Si: "card (\<S> i) \<le> L * (Suc K) * (Suc i)"
  using card_wf1 wf_EarleyS by simp

lemma Si_empty: "i > length w \<Longrightarrow> \<S> i = {}"
  using wf_Earley by (fastforce simp add: \<S>_def wf_item_def)

theorem "card Earley \<le> L * (Suc K) * (Suc (length w))^2"
proof-
  let ?X = "{x. (\<exists>i \<le> length w. x = {(y, z). wf_item y z \<and> z = i})}"

  have "Earley \<subseteq> {(x, k). wf_item x k \<and> k \<le> length w}"
    using wf_Earley by (fastforce simp add: wf_item_def)
  also have "... = \<Union> {x. (\<exists>i \<le> length w. x = {(y, z). wf_item y z \<and> z = i})}" by (auto simp add: wf_item_def)
  finally have 1: "Earley \<subseteq> \<Union> {x. (\<exists>i \<le> length w. x = {(y, z). wf_item y z \<and> z = i})}".

  have 2: "x \<in> ?X \<longrightarrow> card x \<le> L * (Suc K) * (Suc (length w))" for x 
  proof
    fix x
    assume assm: "x \<in> ?X"
    then have "\<exists>i \<le> length w. \<forall>(y, z) \<in> x. wf_item y i \<and> z = i" by auto
    then obtain i where P: "\<forall>(y, z) \<in> x. wf_item y i \<and> z = i" and l: "i \<le> length w" by blast
    then have 3: "x \<subseteq> {y. wf_item y i} \<times> {i}" by fastforce

    have "finite ({y. wf_item y i} \<times> {i})"
      by (simp add: finite_ex_wf_item)
    then have "card x \<le> card {y. wf_item y i}" 
      using Groups_Big.card_cartesian_product[of "{y. wf_item y i}" "{i}"] 
            Finite_Set.card_mono[of "{y. wf_item y i} \<times> {i}"] 3 by auto
    also have "... \<le> L * (Suc K) * (Suc i)" using card_wf1 by auto
    also have "... \<le> L * (Suc K) * (Suc (length w))" using l by auto
    finally show "card x \<le> L * (Suc K) * (Suc (length w))".
  qed

  let ?f = "\<lambda>k. {(x, z). wf_item x z \<and> z = k}"
  let ?Y = "{i. i \<le> (length w)}"

  have fin: "?X = ?f ` ?Y" and "finite ?Y" by auto
  then have "card ?X  \<le> card ?Y"
    using card_image_le by force
  then have 3: "card ?X \<le> Suc (length w)" by auto

  have "\<forall> x \<in> ?X. \<exists>i. x \<subseteq> {y. wf_item y i} \<times> {i}" by fastforce
  then have "\<forall>x \<in> ?X. finite x" using finite_wf_item
    by (metis (no_types, lifting) ext finite.emptyI finite_SigmaI finite_ex_wf_item finite_insert rev_finite_subset)
  then have "finite (\<Union> ?X)"
    by (simp add: fin)
  then have "card Earley \<le> card (\<Union> ?X)" using 1
    by (meson card_mono)
  also have "... \<le> sum card ?X" using Groups_Big.card_Union_le_sum_card by simp
  also have "... \<le> L * (Suc K) * (Suc (length w)) * (Suc (length w))" 
    using 2 3 Groups_Big.sum_bounded_above[of ?X card "L * (Suc K) * (Suc (length w))"]
    by (smt (verit, best) le_trans mult_le_mono2 mult_of_nat_commute of_nat_id)
  finally show ?thesis
    by (metis mult.assoc power2_eq_square)
qed

unused_thms

end (*Context Earley_Gw*)
section \<open>Running time analysis earley recognizer\<close>

subsection \<open>Timing functions and simple bounds\<close>

time_fun rhs

time_fun_0 Earley_Gw.w




context Earley_Gw
begin

time_fun prod
time_fun dot
time_fun "from"

time_fun isin_list
time_fun isin

time_fun efficientItemList.list
time_fun efficientItemList.froms

(*time_fun empty_IL*)
(*normal time_fun definition fails, as there are extra type variables on the rhs (in the list type)*)
fun T_empty_IL :: "nat \<Rightarrow> nat" where
"T_empty_IL k = T_replicate (Suc k) ([] :: nat list)"

time_fun insert

time_fun union_LIL
time_fun IL_of_List
time_fun minus_LIL
time_fun minus_IL

time_fun mv_dot
time_fun is_complete
time_fun next_symbol  

time_fun Scan_L
time_fun Predict_L
time_fun Complete_L

(*Copied from time_fun*)
definition T_Init_L where
"T_Init_L = T_filter T_fst ps + T_map (\<lambda>p. 0) (filter (\<lambda>p. lhs p = S) ps)"

time_fun step_fun


(*assumes that the stop condition check takes 0 time*)
fun steps_time :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList \<Rightarrow> nat \<Rightarrow> ((('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList) \<times> nat) option" where
"steps_time Bs ils y = while_option (\<lambda>((il1,il2),k). (list il1) \<noteq> []) (\<lambda>((il1,il2),k). (step_fun Bs (il1,il2), k + T_step_fun Bs (il1,il2))) (ils, y)"

fun T_steps :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) efficientItemList \<times> ('n, 'a) efficientItemList \<Rightarrow> nat" where
"T_steps Bs ils = snd (the (steps_time Bs ils 0))"

time_fun close2_L
time_fun bins_L

time_fun is_final
time_fun recognized_L
time_fun earley_recognized

end (*Context Earley_Gw*)

locale Earley_Gw_eps_T = Earley_Gw_eps +
  fixes T_nth_IL:: "nat \<Rightarrow> nat"
  assumes T_nth_Bound: "(T_nth :: ('a, 'b) item list list \<Rightarrow> nat \<Rightarrow> nat) as k \<le> T_nth_IL k"
  and T_update_Bound: "(T_list_update :: ('a, 'b) item list list \<Rightarrow> nat \<Rightarrow> ('a, 'b) item list \<Rightarrow> nat) as k a \<le> T_nth_IL k"
  and mono_nth: "mono T_nth_IL" (*mono f*)
begin

(* general List and prod time bounds *)

lemma T_prod_0[simp]: "T_prod x = 0"
  using T_prod.elims by blast

lemma T_dot_0[simp]: "T_dot x = 0"
  using T_dot.elims by blast

lemma T_from_0[simp]: "T_from x = 0"
  using T_from.elims by blast

lemma T_mv_dot_0[simp]: "T_mv_dot s = 0"
  by simp

lemma [simp]: "T_list il = 0"
  using Earley_Gw.T_list.elims by blast

lemma [simp]: "T_froms il = 0"
  using Earley_Gw.T_froms.elims by blast

lemma T_is_complete_bound: "T_is_complete s = Suc (length (rhs (prod s)))"
  by (auto simp add: T_length)

lemma T_next_symbol_bound: 
  assumes "prod s \<in> set ps" shows "T_next_symbol s \<le> 2*(Suc K)"
proof-
  have "length (rhs (prod s)) \<le> K" using prod_length_bound assms by auto
  then show ?thesis 
    using assms T_nth[of "dot s" "rhs (item.prod s)"] by (auto simp add: T_length is_complete_def)
qed

subsection \<open>ItemList time bounds\<close>

lemma T_isin_list_bound: "T_isin_list xs x \<le> length xs + 1"
  by (induction xs) auto

lemma T_isin_general: "inv_IL il \<Longrightarrow> T_isin il x \<le> T_nth_IL (from x) + length ((froms il) ! from x) + 1"
proof-
  obtain as m where "il = ItemList as m"
    using inv_IL.cases by blast
  then show ?thesis 
    using T_isin_list_bound[of "m ! from x" x] T_nth_Bound[of m "from x"] by auto
qed

lemma T_empty_IL_bound[simp]: "T_empty_IL k = k + 2"
  by simp

lemma T_isin_wf: 
  assumes dist: "distinct ps" and inv: "inv_IL il" and wf: "wf1_IL il k" "from x < length (froms il)"
  shows "T_isin il x \<le> T_nth_IL (from x) + L * (Suc K) + 1"
proof-
  obtain as m where IL: "il = ItemList as m"
    using inv_IL.cases by blast
  let ?f = "\<lambda> (p, m). Item p m (from x)"
    
  have 1: "from x < length (froms il) \<Longrightarrow> set ((froms il) ! from x) = {y \<in> set as. from y = from x}" using inv IL by auto
  have 2: "from x < length (froms il) \<Longrightarrow> distinct ((froms il) ! from x)" using inv IL by auto
  
  have fin: "finite (P \<times> {0..K})" using finite_cartesian_product finite by blast
  have inj: "inj_on ?f (P \<times> {0..K})"
    unfolding inj_on_def by simp
  have card_PK: "card (P \<times> {0..K}) = card P * (Suc K)"
    using Groups_Big.card_cartesian_product by (auto simp add: add_mult_distrib add_mult_distrib2)
  have "{y \<in> set as. from y = from x} \<subseteq> ?f ` (P \<times> {0..K})"
  proof
    fix xa
    assume "xa \<in> {y \<in> set as. from y = from x}"
    then obtain p d where XA: "xa = Item p d (from x) \<and> xa \<in> set as"
      by (metis (mono_tags, lifting) T_prod.cases mem_Collect_eq item.sel(3))
    then have "p \<in> P \<and> d \<le> K" using prod_length_bound[of p] wf IL by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
    then show "xa \<in> ?f ` (P \<times> {0..K})" using XA by auto
  qed
    
  then have "card {y \<in> set as. from y = from x} \<le> (card P) * (Suc K)" using fin
    using surj_card_le[of "(P \<times> {0..K})"] by (auto simp add: card_PK)
  then have "from x < length (froms il) \<Longrightarrow> length ((froms il) ! from x) \<le> (card P) * Suc K" using 1 2
    using distinct_card by (fastforce)
  then have "from x < length (froms il) \<Longrightarrow> length ((froms il) ! from x) \<le> L * Suc K"
    using distinct_card dist by (fastforce simp add: L_def)
  then show ?thesis using wf(2) inv T_isin_general[of il x] by auto
qed


lemma T_insert_less: 
  assumes "distinct ps" "inv_IL il" "wf1_IL il k" and le: "from x < length (froms il)" 
  shows "T_insert x il \<le> 3 * T_nth_IL (from x) + L * (Suc K) + 1"
proof-
  obtain as m where "il = ItemList as m"
    using inv_IL.cases by blast
  then have "T_insert x il \<le> T_isin il x + T_nth m (from x) + T_list_update m (from x) (x # m ! from x)" using le by auto
  also have "... \<le> T_nth_IL (from x) + L * (Suc K) + 1 + T_nth_IL (from x) + T_nth_IL (from x)" 
    using assms T_isin_wf[of il k x] T_nth_Bound[of m "from x"] T_update_Bound[of m "from x" "x # m ! from x"] by auto
  finally show ?thesis by auto
qed

lemma wf1_IL_insert: "inv_IL il \<Longrightarrow> wf1_IL il k \<Longrightarrow> from x < length (froms il) \<Longrightarrow> wf_item1 x k \<Longrightarrow> wf1_IL (insert x il) k"
  using IL_insert1 wf_bin1_def by auto

            
lemma wf1_IL_union_LIL: "inv_IL il \<Longrightarrow> wf1_IL il k \<Longrightarrow> \<forall>a\<in>set as. from a < length (froms il) \<Longrightarrow> wf_bin1 (set as) k \<Longrightarrow> wf1_IL (union_LIL as il) k"
  using LIL_union wf_bin1_def by fastforce

lemma T_union_LIL_wf: "distinct ps \<Longrightarrow> inv_IL il \<Longrightarrow> wf1_IL il (length (froms il) - 1) \<Longrightarrow> wf_bin1 (set as) (length (froms il) - 1) 
  \<Longrightarrow> \<forall>a\<in>set as. from a < length (froms il) \<Longrightarrow> T_union_LIL as il \<le> (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1"
proof (induction as arbitrary: il)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then have 1: "inv_IL (union_LIL as il) \<and> wf1_IL (union_LIL as il) (length (froms il) - 1)" using LIL_union_inv wf1_IL_union_LIL
    by (metis list.set_intros(2) wf_bin1_def)
  have wf_from: "\<forall>x \<in> set (a#as). from x < (length (froms il))" using Cons by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have 2: "from a < Suc (length (froms (union_LIL as il)))" using Cons length_LIL_union by auto
  have 3: "from a \<le> (length (froms il) - 1)" using wf_from by auto
  have "T_union_LIL (a#as) il = T_union_LIL as il + T_insert a (union_LIL as il) + 1" by simp
  also have "... \<le> (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1 + 3 * T_nth_IL (from a) + L * (Suc K) + 1 + 1" 
    using Cons T_insert_less[of "union_LIL as il" "(length (froms il)) - 1" a] 1 2 by (fastforce simp add: wf_bin1_def)
  also have "... \<le> (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1 + 3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 1 + 1"
    using mono_nth 3 by (auto simp add: monoD)
  finally show ?case by auto
qed

lemma [simp]: "T_empty_IL k = k + 2"
  by (induction k) auto

lemma wf1_empty_IL: "wf1_IL (empty_IL k) l"
  using set_empty_IL by (auto simp add: wf_bin1_def)

lemma wf1_IL_minus_LIL: "inv_IL il \<Longrightarrow> \<forall>a\<in>set as. from a < Suc n \<Longrightarrow> Suc n \<le> length (froms il) 
  \<Longrightarrow> wf_bin1 (set as) k \<Longrightarrow> wf1_IL (minus_LIL n as il) k"
  using LIL_minus by (auto simp add: wf_bin1_def)

lemma T_minus_LIL_wf: "distinct ps \<Longrightarrow> wf1_IL il k \<Longrightarrow>  inv_IL il \<Longrightarrow> wf_bin1 (set as) k \<Longrightarrow> Suc k \<le> length (froms il)
  \<Longrightarrow> T_minus_LIL k as il \<le> (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) + k + 3 + length as"
proof (induction as)
  case Nil
  then show ?case by (auto simp del: T_empty_IL.simps)
next
  case (Cons a as)
  then have 1: "wf_bin1 (set as) k" by (auto simp add: wf_bin1_def)
  have 2: "inv_IL (minus_LIL k as il) \<and> wf1_IL (minus_LIL k as il) k" using Cons wf1_IL_minus_LIL
    using "1" LIL_minus_inv forall_from_Suc by blast
  have 4: "\<forall>x \<in> set (a#as). from x < Suc k" using Cons by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have 3: "from a < length (froms (minus_LIL k as il))" by simp
  have "T_minus_LIL k (a#as) il \<le> T_isin il a + T_minus_LIL k as il + T_insert a (minus_LIL k as il) + 1" by auto
  also have "... \<le> T_nth_IL (from a) + L * (Suc K) + 1 + T_minus_LIL k as il + T_insert a (minus_LIL k as il) + 1" 
    using Cons T_isin_wf 4 by auto
  also have "... \<le> T_nth_IL (from a) + L * (Suc K) + 1 + (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4)
       + k + 3 + length as + T_insert a (minus_LIL k as il) + 1"
    using Cons 1 by auto
  also have "... \<le> T_nth_IL (from a) + L * (Suc K) + 1 + (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) 
       + k + 3 + length as + 3 * T_nth_IL (from a) + L * (Suc K) + 1 + 1"
    using T_insert_less[of "minus_LIL k as il" k a] Cons 2 3 by linarith
  also have "... \<le> T_nth_IL k + L * (Suc K) + 1 + (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) 
       + k + 2 + length as + 3 * T_nth_IL k + L * (Suc K) + 2 + 1"
    using mono_nth 4 by (auto simp add: monoD)
  also have "... \<le> (length (a#as)) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) + k + 2 + (length (a#as))" by simp
  finally show ?case by simp
qed

lemma T_minus_IL_wf: "distinct ps \<Longrightarrow> wf1_IL il1 (length (froms il1) - 1) \<Longrightarrow> inv_IL il1 \<Longrightarrow> inv_IL il2 \<Longrightarrow> wf1_IL il2 (length (froms il1) - 1)
  \<Longrightarrow> length (froms il2) \<ge> length (froms il1)
  \<Longrightarrow> T_minus_IL il1 il2 \<le> (length (list il1)) * (4 * T_nth_IL (length (froms il1) - 1) + 2*L * (Suc K) + 4) + (length (froms il1) - 1) + 4 + length (list il1) + length (froms il1)"
  using T_minus_LIL_wf[of il2 "length (froms il1) - 1" "list il1"] by (cases il1) (auto simp add: T_length)

subsection \<open>Earley recognizer time bounds\<close>

lemma T_Init_L_bound: "T_Init_L \<le> 2 * (L + 1)"
proof-
  have 1: "\<forall>x \<in> set ps. T_fst x \<le> 0" by auto
  have "T_map (\<lambda>p. 0) (filter (\<lambda>p. lhs p = S) ps) \<le> length (filter (\<lambda>p. lhs p = S) ps) + 1"
    using T_map_bound[of "(filter (\<lambda>p. lhs p = S) ps)" "(\<lambda>p. 0)" 0] by auto
  also have "... \<le> length ps + 1" by auto
  finally show ?thesis using T_filter_bound[of ps T_fst 0] 1 by (auto simp add: T_Init_L_def L_def)
qed

lemma T_Scan_L_bound:
  assumes "k < length w" and wf: "wf_bin1 (set Bs) l" 
  shows "T_Scan_L Bs k \<le> k + 2*(K + 2) * length Bs + 3"
proof-
  have 1: "T_nth w k \<le> k+1" using assms by (auto simp add: T_nth)

  have 2: "T_filter T_next_symbol Bs \<le> 2*(Suc K) * length Bs + length Bs + 1" 
    using T_next_symbol_bound wf T_filter_bound[of Bs T_next_symbol "2*(Suc K)"] 
    by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)

  have "T_map T_mv_dot (filter (\<lambda>b. next_symbol b = Some (w ! k)) Bs) 
            \<le> length (filter (\<lambda>b. next_symbol b = Some (w ! k)) Bs) + 1"
    using T_map_bound[of _ T_mv_dot 0] by auto
  also have "... \<le> length Bs + 1" by auto

  finally show ?thesis using 1 2 assms(1) w_def by (auto simp add: Let_def T_nth)
qed

lemma T_Predict_L_bound: 
  assumes "prod x \<in> set ps" shows "T_Predict_L x k \<le> 2*(K + 2)* length ps + 2"
proof-
  have "\<forall>p \<in> set ps. (\<lambda>p. T_next_symbol x + T_fst p) p \<le> 2*(Suc K)"
    using assms T_next_symbol_bound[of x] by auto
  then have 1: "T_filter (\<lambda>p. T_next_symbol x + T_fst p) ps \<le> 2*(Suc K) * length ps + length ps + 1"
    using T_filter_bound[of ps _ "2*(Suc K)"] by auto

  have "T_map (\<lambda>p. 0) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps) \<le> length (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps) + 1"
    using T_map_bound[of _ "(\<lambda>p. 0)" 0] by auto
  also have "... \<le> length ps + 1" by auto
  finally show ?thesis using 1 by auto
qed


lemma T_Complete_L_bound: 
  assumes "from y < length Bs" "wf_bins1 (map set Bs)" 
  shows "T_Complete_L Bs y \<le> T_nth_IL (from y) + 2*(K + 2) * length (Bs ! from y) + 2"
proof -
  have 1: "T_nth Bs (from y) \<le> T_nth_IL (from y)" using T_nth_Bound by simp
  have "\<forall>x \<in> set (Bs ! from y). (\<lambda>b. T_next_symbol b + (T_prod y + T_fst (item.prod y))) x \<le> 2*(Suc K)"
    using assms T_next_symbol_bound 
    by (auto simp add: wf_bins1_def wf_bin1_def wf_item1_def wf_item_def)
  then have 2: "T_filter (\<lambda>b. T_next_symbol b + (T_prod y + T_fst (item.prod y))) (Bs ! from y)
            \<le> 2*(Suc K) * length (Bs ! from y) + length (Bs ! from y) + 1"
    using T_filter_bound[of "(Bs ! from y)" _ "2*(Suc K)"] by auto

  have "T_map T_mv_dot (filter (\<lambda>b. next_sym_Nt b (lhs (item.prod y))) (Bs ! from y))
          \<le> length (filter (\<lambda>b. next_sym_Nt b (lhs (item.prod y))) (Bs ! from y)) + 1"
    using T_map_bound[of _ T_mv_dot 0] by auto
  also have "... \<le> length (Bs ! from y) + 1" by auto
  finally show ?thesis using 1 2 by auto
qed

lemma distinct_Init: 
  assumes "distinct ps" shows "distinct Init_L"
proof -                                           
  have "inj_on (\<lambda> p. Item p 0 0) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. Item p 0 0) ps)" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Init_L_def distinct_map_filter)
qed

lemma distinct_Predict_L: 
  assumes "distinct ps" shows "distinct (Predict_L x k)"
proof -                                           
  have "inj_on (\<lambda>p. Item p 0 k) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. Item p 0 k) ps)" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Predict_L_def distinct_map_filter)
qed

lemma distinct_Complete_L: 
  assumes "distinct (Bs ! from y)" shows "distinct (Complete_L Bs y)"
proof -                                           
  have "inj_on mv_dot (set (Bs ! from y))"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel item.expand item.inject)
  then have "distinct (map mv_dot (Bs ! from y))" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Complete_L_def distinct_map_filter)
qed

lemma distinct_Scan_L: 
  assumes "distinct B" shows "distinct (Scan_L B k)"
proof -                                           
  have "inj_on mv_dot (set B)"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel item.expand item.inject)
  then have "distinct (map mv_dot B)" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Scan_L_def distinct_map_filter)
qed

lemma wfbin1_impl_wfbin: "wf_bin1 xs k \<Longrightarrow> wf_bin xs k"
  by (auto simp add: wf_bin1_def wf_item1_def)

lemma mult_mono_mix: "i \<le> (j :: nat) \<Longrightarrow> k * i * l \<le> k * j * l"
  by simp

lemma T_step_fun_bound: assumes "(list il1) \<noteq> []" "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf1_IL il1 (length Bs)" "inv_IL il1" "length (froms il1) = Suc (length Bs)"
  "wf1_IL il2 (length Bs)" "inv_IL il2" "length (froms il2) = Suc (length Bs)"
shows "T_step_fun Bs (il1, il2) 
    \<le> L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + 7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 8 + Suc K"
proof-
  obtain bs m where IL1: "il1 = ItemList bs m"
    using inv_IL.cases by blast
  obtain b bss where bbs: "bs = b#bss" using assms IL1
    using efficientItemList.sel(1) T_last.cases by blast

  have from_b: "from b \<le> length Bs"
    using assms by (simp add: IL1 bbs wf_bin1_def wf_item1_def wf_item_def)

  let ?step = "if is_complete b then Complete_L Bs b else Predict_L b (length Bs)"
  let ?t_step = "(if is_complete b then T_Complete_L Bs b else T_length Bs + T_Predict_L b (length Bs))"
  have t_step: "?t_step \<le> T_nth_IL (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2 + Suc (length Bs)"
  proof (cases)
    assume complete: "is_complete b"
    then have 1: "from b < length Bs" using assms
      using assms by (simp add: bbs IL1 wf_bin1_def wf_item1_def)
    then have 2: "distinct (Bs ! from b)" using assms
      by simp
    have "wf_bin1 (set (Bs ! from b)) (from b)" using assms 1
      by (simp add: wf_bins1_def)
    then have "length (Bs ! from b) \<le> L * (Suc K) * (Suc (from b))" 
      using card_wf1 2
      by (metis card_wf_bin1 distinct_card)
    then have 4: "length (Bs ! from b) \<le> L * (Suc K) * (Suc (length Bs))" using 1
      by (meson Suc_le_mono le_trans mult_le_mono2 nat_less_le)

    have "T_Complete_L Bs b \<le> T_nth_IL (from b) + 2 * (K + 2) * length (Bs ! from b) + 2"
      using assms T_Complete_L_bound 1 by (auto simp add: IL1 bbs simp del: T_Complete_L.simps)
    also have "... \<le> T_nth_IL (from b) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2" 
      using mult_le_mono2[OF 4]
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) add_le_mono1 nat_add_left_cancel_le)
    also have "... \<le> T_nth_IL (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2"
      using mono_nth 1 by (auto simp add: monoD)
    finally have "T_Complete_L Bs b \<le> T_nth_IL (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2".
    then show ?thesis using complete by simp
  next
    assume incomplete: "\<not>is_complete b"
    have t_pred: "T_Predict_L b (length Bs) \<le> 2 * (K + 2) * L + 2" 
      using T_Predict_L_bound assms by (simp add: L_def IL1 bbs wf_bin1_def wf_item1_def wf_item_def)

    show ?thesis using t_pred incomplete by (auto simp add: T_length)
  qed

  have "T_length (rhs (item.prod b)) = Suc (length (rhs (prod b)))"
    by (simp add: T_length)
  then have 6: "T_length (rhs (item.prod b)) \<le> Suc K" 
    using prod_length_bound[of "prod b"] assms by (auto simp add: IL1 bbs wf_bin1_def wf_item1_def wf_item_def)

  have wfStep: "wf_bin1 (set ?step) (length Bs)"
    using assms wf1_Complete_L[of Bs b] wf1_Predict_L[of b "length Bs"] IL1 bbs wfbin1_impl_wfbin by (auto simp add: wf_bin1_def)
  have "is_complete b \<Longrightarrow> distinct (Bs ! from b)" using assms
      by (simp add: wf_bin1_def wf_item1_def IL1 bbs)
  then have lengthStep: "length (?step) \<le> L * (Suc K) * (Suc (length Bs))" 
    using card_wf1[of "set (?step)" "length Bs"] assms distinct_Complete_L distinct_Predict_L wfStep
    by (simp add: distinct_card wfbin1_impl_wfbin)
  then have "T_union_LIL (?step) il1 \<le> length (?step) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1"
    using T_union_LIL_wf[of il1 ?step] assms wfStep forall_from_Suc[OF wfStep] by (auto simp add: IL1)
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1"
    using mult_le_mono1[OF lengthStep]
    using add_le_mono1 by blast
  finally have 7: "T_union_LIL ?step il1 \<le> L * (Suc K) * (Suc (length Bs)) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1".

  have "T_insert b il2 \<le> 3 * T_nth_IL (from b) + L * Suc K + 1"
    using T_insert_less[of il2 _ b] from_b assms by auto
  also have "... \<le> 3 * T_nth_IL (length Bs) + L * Suc K + 1"
    using mono_nth from_b by (auto simp add: monoD)
  finally have 8: "T_insert b il2 \<le> 3 * T_nth_IL (length Bs) + L * Suc K + 1".

  have wf_Comp_union: "wf1_IL (union_LIL ?step il1) (length Bs)"
    using assms wfStep wf1_IL_union_LIL forall_from_Suc by auto
  have inv_Comp_union: "inv_IL (union_LIL ?step il1)"
    using LIL_union_inv assms wfStep forall_from_Suc by auto
  obtain bs' m' where decomp: "(union_LIL ?step il1) = ItemList bs' m'"
    using inv_IL.cases by blast
  then have length_Comp_union: "length bs' \<le> L * (Suc K) * (Suc (length Bs))"
    using card_wf_bin1[of "set bs'" "length Bs"] wf_Comp_union inv_Comp_union by (auto simp add: distinct_card)
  have "\<forall>x\<in>set ?step. from x < Suc (length Bs)" 
    using wfStep by (cases "is_complete b") (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  have wf_ins_b: "wf1_IL (insert b il2) (length Bs)" 
    using assms wf1_IL_insert
    by (metis IL1 bbs efficientItemList.sel(1) from_b less_Suc_eq_le list.set_intros(1) set_ItemList.elims wf_bin1_def)
  have inv_ins_b: "inv_IL (insert b il2)"
    using insert_inv_IL1 assms(9)
    by (simp add: assms(10) from_b le_imp_less_Suc)

  let ?minus = "T_minus_IL (union_LIL ?step il1) (insert b il2)"
  have "?minus \<le> length bs' * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 4) + length Bs + 4 + length bs' + length (froms il1)"
    using T_minus_IL_wf[of "union_LIL ?step il1" "insert b il2"] decomp inv_Comp_union wf_Comp_union wf_ins_b inv_ins_b
    by (metis assms(10,2,7) diff_Suc_1 efficientItemList.sel(1) eq_imp_le length_IL_insert length_LIL_union) 
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 4) + length Bs + 4 + L * (Suc K) * (Suc (length Bs)) + Suc (length Bs)"
    using length_Comp_union mult_le_mono1
    using add_le_mono add_le_mono1 assms(7) by presburger
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 5) + 2*length Bs + 5"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"]
    by auto
  finally have 9: "?minus \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 5) + 2*length Bs + 5".

  have "T_step_fun Bs (il1, il2) \<le> T_length (rhs (prod b)) + ?t_step +
  T_union_LIL ?step il1 +
   T_insert b il2 + T_minus_IL (union_LIL ?step il1) (insert b il2) +
   T_insert b il2" by (auto simp add: Let_def IL1 bbs simp del: T_Complete_L.simps T_Predict_L.simps T_minus_IL.simps)

  also have "... \<le> Suc K + T_nth_IL (length Bs) + 2 * (K + 2) * L * (Suc K) * Suc (length Bs) + 2 + Suc (length Bs)
    + L * Suc K * (Suc (length Bs)) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1
    + 3 * T_nth_IL (length Bs) + L * Suc K + 1 + L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 5) + 2*length Bs + 5 +
   3 * T_nth_IL (length Bs) + L * Suc K + 1" using t_step 6 7 8 9 by linarith

  also have "... \<le> Suc K + 2 * (K + 2) * L * (Suc K) * Suc (length Bs)
    + L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7)
    + 7 * T_nth_IL (length Bs) + 2* L * Suc K + 3 * Suc (length Bs) + 8"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  also have "... = Suc K + L * (Suc K) * Suc (length Bs) * 2 * (K + 2)
    + L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7)
    + 7 * T_nth_IL (length Bs) + 2* L * Suc K + 3 * Suc (length Bs) + 8"
    by (smt (verit) mult.assoc mult.commute)
  also have "... = L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + 7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 8 + Suc K"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  finally show ?thesis.
qed




lemma step_fun_dist: 
  assumes "list il1 \<noteq> []" "inv_IL il1" "inv_IL il2" "step_fun Bs (il1, il2) = (il1', il2')" "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)"
    "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  shows "set_ItemList il1' \<inter> set_ItemList il2' = {}"
proof-
  obtain a as m bs n where IL: "il1 = ItemList (a#as) m \<and> il2 = ItemList bs n"
    using il_decomp assms
    by (metis efficientItemList.sel(1) neq_Nil_conv)
  let ?step = "if is_complete a then Complete_L Bs a else Predict_L a (length Bs)"
  have wf_a: "wf_item1 a (length Bs)" using assms(6) IL by (auto simp add: wf_bin1_def)
  then have wf_step: "wf_bin1 (set ?step) (length Bs)"
    using assms(5,6) IL wf1_Complete_L wf1_Predict_L by auto
  have from_a: "from a < length (froms il2)" using wf_a assms(8) by (auto simp add: wf_item1_def wf_item_def)
  have "il1' = minus_IL (union_LIL ?step il1) (insert a il2)" using assms IL by auto
  then have "set_ItemList il1' \<inter> set_ItemList (insert a il2) = {}" 
    using assms IL_minus[of "insert a il2" "union_LIL ?step il1"] insert_inv_IL1 from_a LIL_union_inv wf_step forall_from_Suc by auto
  then show ?thesis using assms IL by auto
qed

lemma length_step_fun_inc: 
  assumes "list il1 \<noteq> []" "inv_IL il2" "wf1_IL il1 (length (froms il2) - 1)" "step_fun Bs (il1, il2) = (il1', il2')" 
          "set_ItemList il1 \<inter> set_ItemList il2 = {}" 
  shows "length (list il2') = Suc (length (list il2))"
proof-
  obtain a as m where IL1: "il1 = ItemList (a#as) m"
    using assms by (metis efficientItemList.sel(1) T_last.cases il_decomp) 
  obtain bs n where IL2: "il2 = ItemList bs n"
    using il_decomp by blast
  have "from a \<le> length (froms il2) - 1" using assms(3) IL1 by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  moreover have "length (froms il2) > 0" using assms(2) IL2 by auto
  ultimately have from_a: "from a < length (froms il2)"
    by linarith
  have "il2' = insert a il2" using assms IL1 by auto
  then have "list il2' = a#bs" using assms isin_IL1 from_a by (auto simp add: IL1 IL2 Let_def simp del: isin.simps)

  then show ?thesis by (simp add: IL2)
qed

lemma steps_time_time: assumes 
    dist_ps: "distinct ps" 
and wf_Bs:  "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" 
and il1_assms:  "wf1_IL il1 (length Bs)" "inv_IL il1" "length (froms il1) = Suc (length Bs)"
and il2_assms:  "wf1_IL il2 (length Bs)" "inv_IL il2" "length (froms il2) = Suc (length Bs)"
and dist_ils: "set_ItemList il1 \<inter> set_ItemList il2 = {}"
and step:  "steps_time Bs (il1,il2) k = Some ((il1',il2'), k')" "k \<le> (length (list il2)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 8 + Suc K)"
  shows "k' \<le> (length (list il2')) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 8 + Suc K)" 
proof -
  let ?C = "L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 8 + Suc K"
  let ?P3 = "\<lambda>((il1',il2'),k). wf1_IL il1' (length Bs) \<and> wf1_IL il2' (length Bs) \<and> wf_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((il1',il2'),k). wf1_IL il1' (length Bs) \<and> wf1_IL il2' (length Bs) \<and> wf_bins1 (map set Bs) \<and> inv_IL il1' \<and> inv_IL il2' 
        \<and> length(froms il1') = Suc (length Bs) \<and> length (froms  il2') = Suc (length Bs) \<and> set_ItemList il1' \<inter> set_ItemList il2' = {} \<and> (\<forall>i < length Bs. distinct (Bs ! i)) \<and> distinct ps"
  let ?P2 = "\<lambda>((il1',il2'),k). k \<le> (length (list il2')) * (?C)"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((il1,il2),k). (list il1) \<noteq> [])"
  let ?c = "\<lambda>((il1,il2),k). (step_fun Bs (il1,il2), k + T_step_fun Bs (il1,il2))"


  have init: "?P ((il1,il2), k)" using assms by auto

  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y
    using step_fun_inv1_il[of a Bs b] step_fun_inv2_il[of a Bs b] step_fun_wf2_il[of a Bs b] 
      step_fun_wf_il[of a Bs b] length_step_fun1_il[of a Bs b] length_step_fun2_il[of a Bs b] step_fun_dist[of a b Bs]
    by (smt (verit) case_prodI2' case_prod_conv wf_Bs(1)) 
  
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_step_fun Bs (a, b) \<le> ?C" using T_step_fun_bound by auto
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "step_fun Bs (a,b) = (a', b')" by auto
    then have "length (list b') = Suc (length (list b))" using length_step_fun_inc[of a b Bs a' b'] assms by auto
    then have 2: "length (list b') * ?C = length (list b) * ?C + ?C"
      by (metis add.commute mult_Suc)
    have "y' \<le> y + ?C" using P1 1 by auto
    also have "... \<le> length (list b) * ?C + ?C" 
      using assms by (auto simp add: add_mult_distrib2)
    also have "... = length (list b') * ?C" using 2 by auto
    finally have "y' \<le> length (list b') * ?C".
    then show "?P2 (?c ((a,b), y))" using P1
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
  qed

  then have t: "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P (?c ((a,b), y)))" for a b y using P1 by auto
  then show "k' \<le> (length (list il2')) * ?C"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((il1,il2),k)", where t="((il1',il2'), k')"] assms init by auto
  (*show "wf_bin1 (set C') (length Bs)"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto
  show "distinct C'"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto*)
qed

theorem steps_time_NF: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_IL il1 (length Bs) \<Longrightarrow> wf1_IL il2 (length Bs) \<Longrightarrow> inv_IL il1 \<Longrightarrow> inv_IL il2 
  \<Longrightarrow> length (froms il1) = Suc (length Bs) \<Longrightarrow> length (froms il2) = Suc (length Bs)
  \<Longrightarrow> \<exists>il1' il2' k'. steps_time Bs (il1,il2) k = Some ((il1',il2'),k') \<and> steps Bs (il1, il2) = Some (il1', il2')"
using wf_step_fun_less[of "length Bs"]
proof (induction "(il1,il2)" arbitrary: il1 il2 k rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "list il1 = []"
    thus ?thesis by(simp add: while_option_unfold steps_def)
  next
    let ?steps = "while_option (\<lambda>(as,bs). list as \<noteq> []) (step_fun Bs)"
    assume cons: "list il1 \<noteq> []"
    then obtain il1' il2'
      where "(il1',il2') = step_fun Bs (il1,il2)" and wf': "wf1_IL il1' (length Bs)" "wf1_IL il2' (length Bs)" 
        and inv': "inv_IL il1'" "inv_IL il2'" and leng': "length (froms il1') = Suc (length Bs)" "length (froms il2') = Suc (length Bs)"
      using step_fun_wf_items[OF less.prems(1,2,3,4,5) cons less.prems(6,7)] by auto
    then have "((il1',il2'), (il1, il2)) \<in> step_fun_less (length Bs)" using less.prems
      by (simp add: step_fun_less_step \<open>list il1 \<noteq> []\<close>)
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf' inv' leng']
    show ?thesis
      by (simp add: \<open>(il1', il2') = step_fun Bs (il1, il2)\<close> while_option_unfold steps_def)
  qed
qed

lemma T_steps_bound: assumes
  "distinct ps" "wf_bins1 (map set Bs)" "wf1_IL il1 (length Bs)" "wf1_IL il2 (length Bs)" "inv_IL il1" "inv_IL il2"
  "\<forall>i < length Bs. distinct (Bs ! i)"  "set_ItemList il1 \<inter> set_ItemList il2 = {}" 
  "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
shows "T_steps Bs (il1, il2) \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 8 + Suc K)"
proof-
  obtain il1' il2' k' where P: "steps_time Bs (il1,il2) 0 = Some ((il1',il2'),k') \<and> steps Bs (il1, il2) = Some (il1', il2')"
    using steps_time_NF assms by blast
  have "wf1_IL il2' (length Bs) \<and> inv_IL il2'"
    using P assms(2,3,4,5,6,9,10) steps_wf2 steps_inv2 by blast
  then have 1: "length (list il2') \<le> L * Suc K * Suc (length Bs)"
    using card_wf_bin1 distinct_card[of "list il2'"] inv_IL1
    by fastforce
  have "k' \<le> (length (list il2')) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 8 + Suc K)"
    using steps_time_time[of Bs il1 il2 0] assms P by simp
  also have "... \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 8 + Suc K)"
    using P mult_le_mono1[OF 1] by auto
  finally show ?thesis using P by simp
qed

lemma T_close2_L_bound: 
assumes "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)"  "wf1_IL il (length Bs)" "inv_IL il" "length (froms il) = Suc (length Bs)"
shows "T_close2_L Bs il \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 8 + Suc K) + Suc (length Bs) + Suc (Suc (length Bs))"
proof-
  obtain il1' il2' where "steps Bs (il, empty_IL (length Bs)) = Some (il1', il2')"
    using Close2_L_NF empty_inv assms(2,4,5,6) wf1_empty_IL length_empty_IL by blast
  then show ?thesis using T_steps_bound[of Bs il "empty_IL (length Bs)"] empty_inv[of "length Bs"] set_empty_IL 
        wf1_empty_IL length_empty_IL assms T_length[of Bs] by (auto simp del: T_empty_IL.simps)
qed

lemma wf1_Init_L: "wf_bin1 (set Init_L) 0"
  by (simp add: Init_L_eq_Init wf_bin1_Init)

lemma wf1_Scan_L: "k < length w \<Longrightarrow> wf_bin1 (set as) k \<Longrightarrow> wf_bin1 (set (Scan_L as k)) (Suc k)"
  using wf_bin1_Scan
  by (simp add: Scan_L_eq_Scan)

lemma wf_Scan_L: "k < length w \<Longrightarrow> wf_bin (set as) k \<Longrightarrow> wf_bin (set (Scan_L as k)) k"
  by (auto simp add: Scan_L_def mv_dot_def next_symbol_def wf_item_def is_complete_def)

lemma length_Init_L: "length Init_L \<le> L"
  by (auto simp add: Init_L_def L_def)

lemma length_Scan_L: "length (Scan_L as k) \<le> length as"
  by (auto simp add: Scan_L_def)
                                                
lemma wf1_IL_of_List: "wf_bin1 (set as) k \<Longrightarrow> wf1_IL (IL_of_List k as) k"
  using set_IL_of_List forall_from_Suc by auto

lemma distinct_close2: 
  assumes "wf_bins1 (map set Bs)" "wf1_IL il (length Bs)" "inv_IL il" "length (froms il) = Suc (length Bs)"
  shows "distinct (close2_L Bs il)"
proof-
  obtain il1 il2 where "steps Bs (il, empty_IL (length Bs)) = Some (il1, il2)"
    using empty_inv wf1_empty_IL length_empty_IL Close2_L_NF assms by blast
  then show ?thesis using steps_inv2[of " empty_IL (length Bs)"] assms length_empty_IL
      inv_IL1[of "il2"] close2_L_def by (auto simp add: close2_L_def empty_inv)
qed

lemma distinct_bins_L: "k \<le> length w \<Longrightarrow> distinct ps \<Longrightarrow> i < Suc k \<Longrightarrow> distinct ((bins_L k) ! i)"
proof(induction k arbitrary: i)
  case 0
  then show ?case using distinct_Init distinct_close2[of "[]" "IL_of_List 0 Init_L"] length_IL_of_List
    using IL_of_List_inv[OF forall_from_Suc] set_IL_of_List wf1_Init_L wf_bins1_def wf1_IL_of_List by auto
next
  case (Suc k)
  then have 1: "i < Suc k \<longrightarrow> distinct (bins_L (Suc k) ! i)" using length_bins_L by (auto simp add: Let_def nth_append_left)

  have 2: "wf_bins1 (map set (bins_L k))" using "Suc.prems"(1)
    by (simp add: bins_L_eq_bins wf_bins1_bins)
  have "wf_bin1 (set (last (bins_L k))) k" using "Suc.prems"(1)
    by (metis Suc_leD Zero_not_Suc bins_L_eq_bins last_map length_bins_L list.size(3) wf_bin1_last)
  then have 3: "wf_bin1 (set (Scan_L (last (bins_L k)) k)) (Suc k)"
    using Scan_L_eq_Scan Suc.prems(1) wf_bin1_Scan by auto
  have 5: "distinct (close2_L (bins_L k) (IL_of_List (Suc k) (Scan_L (last (bins_L k)) k)))" using 2 3 Suc distinct_close2
    using IL_of_List_inv[OF forall_from_Suc] length_bins_L wf1_IL_of_List by auto

  have "\<not> i < Suc k \<longrightarrow> i = Suc k" using Suc by auto
  then show ?case using 1 5 using nth_append_length[of "bins_L k"] length_bins_L by (auto simp add: Let_def)
qed

(*(k+2)^3 * ((?a) + (?b))
    + 7*k + 18 
    + (k+2)^2 * ?a
    + Suc (Suc k) * ?b*)

lemma bound_help: 
  assumes "a > 0" "b > 0" 
  shows "(x+2)^3 * (a+b) + 7*(x::nat) + (x+2)^2 * a + (x+2) * b + 18 \<le> (x+3)^3 * (a+b)"
proof-
  have "(x+2)^3 * (a+b) + 7*x + (x+2)^2 * a + (x+2) * b + 18
         = (x+2) * (x+2) *(x+2) * (a+b) + 7* x+ (x+2) * (x+2) * a + (x+2) * b + 18"
    by (auto simp add: numeral_eq_Suc)
  then have 1: "(x+2)^3 * (a+b) + 7*x + (x+2)^2 * a + (x+2) * b + 18 
    = (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x + (x*x + 4*x + 4) * a + (x+2) * b + 18"
    by (auto simp add: add_mult_distrib)
  also have "... \<le> (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x + (x*x + 4*x + 4) * (a +b) + (x+2) * (a+b) + 18"
    by (auto simp add: add_mult_distrib add_mult_distrib2)
  also have "... \<le> (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x * (a+b) + (x*x + 4*x + 4) * (a +b) + (x+2) * (a+b) + 18"
    using assms by auto
  also have "... \<le> (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x * (a+b) + (x*x + 4*x + 4) * (a +b) + (x+2) * (a+b) + 9*(a+b)"
    using assms by auto
  also have "... = (x*x*x + 7*x*x + 24*x + 23) * (a + b)" by (auto simp add: add_mult_distrib add_mult_distrib2)
  finally have 1: "(x+2)^3 * (a+b) + 7*x + (x+2)^2 * a + (x+2) * b + 18 \<le> (x*x*x + 7*x*x + 24*x + 23) * (a + b)".
  have "(x+3)^3 *(a+b) = Suc(Suc(Suc x)) * Suc(Suc(Suc x)) * Suc(Suc(Suc x)) * (a+b)"
    by (auto simp add: numeral_eq_Suc)
  then have 2: "(x+3)^3 * (a+b) = (x*x*x + 9*x*x + 27*x + 27) * (a+b)"
    by (auto simp add: add_mult_distrib)
  show ?thesis using 1 2 by (auto simp add: add_mult_distrib add_mult_distrib2)
qed
(*8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (1) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (1) + 3* L * Suc K + 9 + Suc K)))*)

lemma T_bins_L_bound: "distinct ps \<Longrightarrow> k \<le> length w \<Longrightarrow> T_bins_L k 
  \<le> (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K)))"
proof (induction k)
  case 0
  have "\<forall>x \<in> set (Init_L). from x = 0" using wf1_Init_L by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have 1: "T_union_LIL Init_L (empty_IL 0) \<le> length Init_L * (3 * T_nth_IL (0) + L * Suc K + 2) + 1" 
    using T_union_LIL_wf[of "empty_IL 0"] 0 empty_inv wf1_empty_IL wf1_Init_L by (auto simp add:)
  have "length (froms (IL_of_List 0 Init_L)) = 1" 
    using length_IL_of_List by simp
  then have "T_close2_L [] (IL_of_List 0 Init_L) \<le> (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 8 + Suc K) + 3"
    using 0 T_close2_L_bound[of "[]" "(IL_of_List 0 Init_L)"] wf1_Init_L wf1_IL_of_List
        IL_of_List_inv[OF forall_from_Suc] by (auto simp add: wf_bins1_def simp del: T_close2_L.simps)
  then have "T_bins_L 0 \<le> length Init_L * (3 * T_nth_IL (0) + L * Suc K + 2) + 1 + (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 8 + Suc K) + 3+3" 
    unfolding T_bins_L.simps T_IL_of_List.simps T_empty_IL.simps 
    using 1 by (auto)
  also have "... =  length Init_L * (3 * T_nth_IL (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 8 + Suc K) + 7" by auto
  also have "... \<le> L * (3 * T_nth_IL (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 8 + Suc K) + 7"
    using length_Init_L
    using add_le_mono1 mult_le_cancel2 by presburger
  also have "... \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 10 + Suc K)))"
    by (auto simp add: add_mult_distrib add_mult_distrib2)
  finally have 2: "T_bins_L 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 10 + Suc K)))".

  have "7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2)
      \<le> 7 * T_nth_IL (1) + 3* L * Suc K + 10 + 2 * (K + 2)" using mono_nth by (auto simp add: monoD)
  then have 3: "Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2))
    \<le> Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (1) + 3* L * Suc K + 10 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 10 + Suc K \<le> 2 * (K + 2) + 10 * T_nth_IL (1) + 3* L * Suc K + 10 + Suc K"
    using mono_nth by (auto simp add: monoD)
  then have 4: "(Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 10 + Suc K)) \<le> (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (1) + 3* L * Suc K + 10 + Suc K))"
    using mult_le_mono2 by blast

  have "T_bins_L 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (1) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (1) + 3* L * Suc K + 10 + Suc K)))"
    using 2 3 4 by auto

  then show ?case by (auto simp add: numeral_eq_Suc)
next
  case (Suc k)
  have 1: "T_length (bins_L k) = k + 2"
    by (auto simp add: length_bins_L T_length)

  have 2: "T_last (bins_L k) = Suc k"
    by (metis T_last Zero_not_Suc length_bins_L list.size(3))

  have wf_last: "wf_bin1 (set (last (bins_L k))) k" using Suc wf_bin1_last
    by (metis Suc_leD Zero_not_Suc bins_L_eq_bins length_bins_L list.size(3) last_map)
  then have length_last: "length (last (bins_L k)) \<le> L * Suc K * Suc k"
    using distinct_bins_L card_wf_bin1 last_conv_nth length_bins_L
    by (metis Suc.prems(1,2) Suc_leD diff_Suc_1 distinct_card length_greater_0_conv lessI zero_less_Suc)
  have "T_Scan_L (last (bins_L k)) k \<le> k + 2 * (K + 2) * length (last (bins_L k)) + 3"
    using T_Scan_L_bound Suc w_def wf_last by auto
  also have "... \<le> k + 2 * (K + 2) * L * Suc K * Suc k + 3"
    using length_last
    by (metis (no_types, lifting) add_le_mono1 mult.assoc mult_le_mono2 nat_add_left_cancel_le)
  also have "... = k + L * Suc K * Suc k * 2 * (K + 2) + 3"
    by (metis (no_types, lifting) mult.commute mult.left_commute)
  finally have 3: "T_Scan_L (last (bins_L k)) k \<le> k + L * Suc K * Suc k * 2 * (K + 2) + 3".

  have wf_Scan: "wf_bin1 (set (Scan_L (last (bins_L k)) k)) (Suc k)"
    using wf_last wf_Scan_L Suc wfbin1_impl_wfbin
    by (meson Suc_le_eq wf1_Scan_L)
  then have from_Scan: "\<forall>a \<in> set (Scan_L (last (bins_L k)) k). from a < Suc (Suc k)"
    using forall_from_Suc by blast
  have length_Scan: "length (Scan_L (last (bins_L k)) k) \<le> L * Suc K * Suc k"
    using length_Scan_L length_last dual_order.trans by blast
  have "T_IL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k) \<le> k+3 + length (Scan_L (last (bins_L k)) k) * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + 1"
    using T_union_LIL_wf[of "(empty_IL (Suc k))" "Scan_L (last (bins_L k)) k"] empty_inv[of "Suc k"] wf1_empty_IL wf_Scan Suc wfbin1_impl_wfbin
    length_IL_of_List from_Scan by (auto simp add: length_bins_L algebra_simps)
  also have "... \<le> k+3 + L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + 1" using length_Scan mult_le_mono1[OF length_Scan]
    using add_le_mono1 nat_add_left_cancel_le by presburger
  finally have 4: "T_IL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k) \<le> L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + k + 4" by linarith

  have wf_bins_L: "wf_bins1 (map set (bins_L k))" using wf_bins1_bins bins_L_eq_bins Suc by auto
  have wf_IL_of_List: "wf1_IL (IL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k))  (Suc k)"
    using set_IL_of_List[OF forall_from_Suc, of "Scan_L (last (bins_L k)) k" "Suc k"] 
    using Suc.prems(2) wf1_Scan_L[of "k" "last (bins_L k)"] wf_last length_bins_L by auto
  have leng_IL_of_List: "length (froms (IL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k))) = k+2"
    by (auto simp add: length_bins_L)
  have 5: "T_close2_L (bins_L k) (IL_of_List  (length (bins_L k)) (Scan_L (last (bins_L k)) k))  
            \<le> (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 8 + Suc K) + Suc (Suc k) + Suc (Suc (Suc k))"
    using T_close2_L_bound[of "bins_L k" "IL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k)"] 
      wf_bins_L wf_Scan Suc distinct_bins_L wf_IL_of_List IL_of_List_inv[OF forall_from_Suc] leng_IL_of_List 
    by (auto simp add: length_bins_L simp del: T_close2_L.simps)

  have 6: "T_append (bins_L k) [close2_L (bins_L k) (IL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k))] = k+2"
    by (auto simp add: length_bins_L)

  have "L * Suc K * Suc (Suc k) * 2 * Suc (Suc k) \<le>  L * Suc K * L * Suc K * Suc (Suc k) * 2* Suc (Suc k)" using le_square[of "L * Suc K"]
    by (metis (no_types, lifting) mult.assoc mult_le_mono1)
  then have test': "L * Suc K * Suc (Suc k) * 3 * Suc (Suc k) \<le> L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * 3"
    by (auto simp add: algebra_simps)
  have test'': "L \<le> Suc L" by simp

  have "T_bins_L (Suc k) \<le> T_bins_L k + k + 2 + Suc k + k + L * Suc K * Suc k * 2 * (K + 2) + 3
        + L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + k + 4
        + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 8 + Suc K) + Suc (Suc k) + Suc (Suc (Suc k))
      + k + 2 + 1" unfolding T_bins_L.simps Let_def using 1 2 3 4 5 6 by linarith

  
  
  also have "... = T_bins_L k + 7*k + 18 + L * Suc K * Suc k * 2 * (K + 2)
            + L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 8 + Suc K)"
    by auto

  also have "... = T_bins_L k + 7*k + 18
            + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 8 + Suc K)"
    using add_mult_distrib2 by auto

  also have "... = T_bins_L k + 7*k + 18 + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 8 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))" "L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))"
                                "7 * T_nth_IL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K"]
    by (smt (verit, del_insts) Suc_1 ab_semigroup_add_class.add_ac(1) ab_semigroup_mult_class.mult_ac(1) add_2_eq_Suc' add_Suc_shift add_mult_distrib2 group_cancel.add2
        mult.commute mult.left_commute)

  also have "... = T_bins_L k + 7*k + 18 + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * 3 * Suc (Suc k)
    + L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 2* L * Suc K + 8 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] by auto

  also have "... \<le>  T_bins_L k + 7*k + 18 + L * Suc K * (Suc (Suc k)) * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * 3
    + L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 2* L * Suc K + 8 + Suc K)"
    using mult_mono_mix[of "Suc k" "(Suc (Suc k))" "L * Suc K" "2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2"] test' by presburger

  also have "... \<le> T_bins_L k + 7*k + 18 
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] 
          add_mult_distrib2[of "L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k)"] by auto

  also have "... = T_bins_L k + 7*k + 18 
    + L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K))"
    by (metis (no_types, opaque_lifting) mult.assoc)

  also have "... \<le> T_bins_L k + 7*k + 18 
    + Suc L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + Suc L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K))" 
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_L k + 7*k + 18 
    + L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K)"
    by (metis (no_types, lifting) dual_order.refl mult.commute mult.left_commute mult.assoc)
  also have "... \<le> T_bins_L k + 7*k + 18 
    + Suc L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K)"
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_L k + 7*k + 18 
    + Suc (Suc k) * Suc (Suc k) * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K))"
    by (smt (verit, ccfv_threshold) mult.commute mult.left_commute verit_comp_simplify1(2))
  also have "... \<le> T_bins_L k + 7*k + 18 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K))"
    by (metis add_2_eq_Suc' le_refl power2_eq_square)
  finally have short: "T_bins_L (Suc k) \<le> T_bins_L k + 7*k + 18 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K))".

  let ?a = "Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))"
  let ?b = "Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K)"

  have ff: "T_nth_IL (Suc k) \<le> T_nth_IL (Suc (Suc k))" using mono_nth
    by (simp add: monoD)
  then have "(7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)) \<le> (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))"
    by auto
  then have a1: "?a \<le> Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K \<le> 2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + Suc K"
    using ff by auto
  then have b1: "?b \<le> Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + Suc K)"
    using mult_le_mono2 by blast

  have "T_bins_L (Suc k) \<le> (k+2)^3 * ((?a) + (?b))
    + 7*k + 18 
    + (k+2)^2 * ?a
    + Suc (Suc k) * ?b" using short Suc by simp

  also have "... \<le> (k+3)^3 * ((?a) + (?b))"
    using bound_help[of ?a ?b k] by simp

  also have "... \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + Suc K)))"
    using a1 b1 by simp
  finally have "T_bins_L (Suc k)
  \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + Suc K)))".

  then show ?case
    by (metis add_Suc_shift eval_nat_numeral(3))
qed

subsection \<open>Final nice time bounds\<close>

definition C1 where "C1 = 30 * (L+1)^3 * (K+1)^3"
definition C2 where "C2 = 17 * (L+1)^2 * (K+1)^2"

corollary nice_T_bins_L_bound: 
  assumes "distinct ps" "k \<le> length w" 
  shows "T_bins_L k \<le> C1 *(k+2)^3 + C2 * (k+2)^3 * T_nth_IL (k+1)"
proof-
  have "T_bins_L k \<le> (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + Suc K)))"
    using T_bins_L_bound assms by auto
  also have "... = (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * 7 * T_nth_IL (k+1) + Suc L * Suc K * 10 * T_nth_IL (k+1)) 
    + (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 3* L * Suc K + 10 + Suc K)))"
    by (auto simp add: algebra_simps)
  also have "... \<le> (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * 17 * T_nth_IL (k+1))
                  + (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * (6* L * Suc K + 20 + 5 * (K + 2)))"
    by (auto simp add: algebra_simps)
  also have "... \<le> 17 * (L+1) * (L+1) * (K+1) * (K+1) * (k+2)^3 * T_nth_IL (k+1)
                  + 30 * (L+1) * (L+1) * (L+1) * (K+1) * (K+1) * (K+1) * (k+2)^3"
    by (auto simp add: algebra_simps)
  also have "... = 17 * (L+1)^2 * (K+1)^2 * (k+2)^3 * T_nth_IL (k+1)
                  + 30 * (L+1)^3 * (K+1)^3 * (k+2)^3"
    by (auto simp add: monoid_mult_class.power2_eq_square monoid_mult_class.power3_eq_cube algebra_simps)
  finally show ?thesis by (auto simp add: C1_def C2_def)
qed


lemma T_final_bound: "prod x \<in> set ps \<Longrightarrow> T_is_final x \<le> Suc K"
  by (auto simp add: T_length prod_length_bound)

lemma T_recognized_bound: "wf_bin (set as) k \<Longrightarrow> T_recognized_L as \<le> Suc (length as) * (K+2)"
proof (induction as)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then show ?case using T_final_bound[of a] by (auto simp del: T_is_final.simps simp add: wf_item_def)
qed

definition C1' where "C1' = 32 * (L+1)^3 * (K+1)^3"

lemma 
  assumes dist: "distinct ps" 
  shows "T_earley_recognized y \<le> C1' *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1)"
proof-
  have wf_last: "wf_bin1 (set (last (bins_L (length w)))) (length w)" using wf_bin1_last
    by (metis bins_L_eq_bins length_bins_L lessI less_Suc_eq_le list.size(3) not_less_zero last_map)
  then have length_last: "length (last (bins_L (length w))) \<le> L * Suc K * Suc (length w)"
    using distinct_bins_L card_wf_bin1 last_conv_nth length_bins_L distinct_card
    by (metis diff_Suc_1 dist interval_class.less_imp_less_eq_dec lessI list.size(3) nat.distinct(1))
  have "T_recognized_L (last (bins_L (length w))) \<le> Suc (length (last (bins_L (length w)))) * (K+2)"
    using wf_last wfbin1_impl_wfbin T_recognized_bound by metis
  also have "... \<le> Suc (L * Suc K * Suc (length w)) * (K+2)" using length_last
    using Suc_le_mono mult_le_mono1 by presburger
  finally have 1: "T_recognized_L (last (bins_L (length w))) \<le> Suc (L * Suc K * Suc (length w)) * (K+2)".

  from dist have 2: "T_bins_L (length w) \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1)"
    using nice_T_bins_L_bound by auto

  have 3: "T_last (bins_L (length w)) = Suc (length w)"
    using T_last length_bins_L
    by (metis Zero_not_Suc list.size(3))

  have 4: "T_length w = Suc (length w)"
    using T_length by auto

  have "T_earley_recognized y \<le> T_bins_L (length w) + T_last (bins_L (length w)) + T_recognized_L(last (bins_L (length w))) + T_length w"
    by auto
  also have "... \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1) + Suc (length w) + Suc (length w) + Suc (L * Suc K * Suc (length w)) * (K+2)" 
    using 1 2 3 4 by linarith
  also have "... \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1) + 2 * (L+1) * (L+1) * (L+1) * (K+1) * (K+1) * (K+1) * ((length w)+2) * ((length w)+2) * ((length w)+2)"
    by (auto simp add: algebra_simps)
  also have "... = C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1) + 2 * (L+1)^3 * (K+1)^3 * ((length w)+2)^3"
    by (auto simp add: monoid_mult_class.power3_eq_cube algebra_simps)
  also have "... = C1' *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1)"
    using C1_def C1'_def by auto
  finally show ?thesis.
qed
end

section \<open>Set based earley parser\<close>
subsection \<open>parse_item definitions and set based version\<close>
context Earley_Gw
begin
type_synonym ('c, 'd) item_Pt = "('c, 'd) item \<times> ('c, 'd) tree list"

abbreviation item :: "('n,'a) item_Pt \<Rightarrow> ('n, 'a) item" where
  "item \<equiv> fst"

abbreviation tree :: "('n,'a) item_Pt \<Rightarrow> ('n, 'a) tree list" where
  "tree \<equiv> snd"

fun wf_item_Pt :: "('n, 'a) item_Pt \<Rightarrow> nat \<Rightarrow> bool" where
"wf_item_Pt x k = (wf_item (item x) k \<and> (\<forall>t \<in> (set (tree x)). parse_tree P t) \<and> fringes (rev (tree x)) = slice (from (item x)) k w \<and> (map root (rev (tree x)) = \<alpha> (item x)))"

fun wf_item_Pt1 :: "('n, 'a) item_Pt \<Rightarrow> nat \<Rightarrow> bool" where
"wf_item_Pt1 x k = (wf_item1 (item x) k \<and> (\<forall>t \<in> (set (tree x)). parse_tree P t) \<and> fringes (rev (tree x)) = slice (from (item x)) k w \<and> (map root (rev (tree x)) = \<alpha> (item x)))"
  
fun wf_parse_bin :: "('n, 'a) item_Pt set \<Rightarrow> nat \<Rightarrow> bool" where
"wf_parse_bin xs k = (\<forall>x \<in> xs. wf_item_Pt x k)"

fun wf_parse_bin1 :: "('n, 'a) item_Pt set \<Rightarrow> nat \<Rightarrow> bool" where
"wf_parse_bin1 xs k = (\<forall>x \<in> xs. wf_item_Pt1 x k)"

definition wf_parse_bins1 :: "('n, 'a) item_Pt set list \<Rightarrow> bool" where
"wf_parse_bins1 Bs = (\<forall>k < length Bs. wf_parse_bin1 (Bs!k) k)"

definition Parse_Predict :: "('n,'a) item \<Rightarrow> nat \<Rightarrow> ('n,'a) item_Pt set" where 
  "Parse_Predict x k = { (Item r 0 k, []) | r. r \<in> P \<and> next_sym_Nt x (lhs r) }"

definition Parse_Complete :: "('n, 'a) item_Pt set list \<Rightarrow> ('n, 'a) item_Pt \<Rightarrow> ('n, 'a) item_Pt set" where
  "Parse_Complete Bs y = (\<lambda> (p, t). (mv_dot p, (Rule (lhs(prod (item y))) (rev (tree y)))#t)) ` {x. x \<in> Bs ! from (item y) \<and> next_sym_Nt (fst x) (lhs(prod (item y)))}"

definition Parse_Init :: "('n,'a) item_Pt set" where
  "Parse_Init = { (Item r 0 0, []) | r. r \<in> P \<and> lhs r = (S) }"

definition Parse_Scan :: "('n,'a) item_Pt set \<Rightarrow> nat \<Rightarrow> ('n,'a) item_Pt set" where
  "Parse_Scan B k = { (mv_dot (item x), (Sym (w!k))#(tree x)) | x. x \<in> B \<and> next_symbol (item x) = Some (w!k) }"

inductive_set Parse_Close :: "('n,'a) item_Pt set list \<Rightarrow> ('n,'a) item_Pt set \<Rightarrow> ('n,'a) item_Pt set" for Bs B where
    Init: "x \<in> B \<Longrightarrow> x \<in> Parse_Close Bs B"
  | Predict: "\<lbrakk> x \<in> Parse_Close Bs B; x' \<in> Parse_Predict (item x) (length Bs) \<rbrakk> \<Longrightarrow> x' \<in> Parse_Close Bs B"
  | Complete: "\<lbrakk> y \<in> Parse_Close Bs B; is_complete (item y); x \<in> Parse_Complete Bs y\<rbrakk> \<Longrightarrow> x \<in> Parse_Close Bs B"

fun Parse_bins :: "nat \<Rightarrow> ('n, 'a) item_Pt set list" where
  "Parse_bins 0 = [(Parse_Close [] Parse_Init)]" |
  "Parse_bins (Suc k) = (let bs = Parse_bins k in bs @ [Parse_Close bs (Parse_Scan (last bs) k)])"


lemma Parse_Predict_item: "Parse_Predict x k = Predict x k \<times> {[]}"
  by (auto simp add: Parse_Predict_def Predict_def)

lemma Parse_Complete_item: "from (item y) < length Bs \<Longrightarrow> item ` (Parse_Complete Bs y) = (Complete (map (\<lambda> x. item ` x) Bs) (item y))"
proof (auto simp add: Parse_Complete_def Complete_def)
  fix p t
  assume "from (item y) < length Bs" "(p, t) \<in> Bs ! from (item y)" "next_sym_Nt p (lhs (item.prod (item y)))" 
  then show "mv_dot p \<in> mv_dot ` {x \<in> item ` Bs ! from (item y). next_sym_Nt x (lhs (item.prod (item y)))}"
    by (metis (mono_tags, lifting) fst_conv imageI mem_Collect_eq)
next
  fix s t
  assume "from (item y) < length Bs" "(s, t) \<in> Bs ! from (item y)" "next_sym_Nt s (lhs (item.prod (item y)))"
  then show "mv_dot s
           \<in> item `
              (\<lambda>x. case x of (p, t) \<Rightarrow> (mv_dot p, Rule (lhs (item.prod (item y))) (rev (tree y)) # t)) `
              {x \<in> Bs ! from (item y). next_sym_Nt (item x) (lhs (item.prod (item y)))}"
    by (metis (mono_tags, lifting) fst_conv imageI mem_Collect_eq pair_imageI)
qed

lemma Parse_Init_item: "Parse_Init = Init \<times> {[]}"
  by (auto simp add: Parse_Init_def Init_def)

lemma Parse_Scan_item: "item ` Parse_Scan B k = Scan (item ` B) k"
proof (auto simp add: Parse_Scan_def Scan_def)
  fix s t 
  assume "next_symbol s = Some (w ! k)" "(s, t) \<in> B"
  then show "\<exists>x. mv_dot s = mv_dot x \<and> x \<in> item ` B \<and> next_symbol x = Some (w ! k)"
    by (metis fst_conv image_eqI)
next
  fix s t
  assume "next_symbol s = Some (w ! k)" "(s, t) \<in> B"
  then show "mv_dot s \<in> item ` {(mv_dot a, Sym (w ! k) # b) |a b. (a, b) \<in> B \<and> next_symbol a = Some (w ! k)}"
    by force
qed

lemma wf_parse_init: "wf_parse_bin (Parse_Init) 0"
  by (auto simp add: Parse_Init_def slice_drop_take wf_item_def \<alpha>_def)

lemma wf_parse_predict: "wf_item_Pt x k \<Longrightarrow> wf_parse_bin (Parse_Predict (item x) k) k"
  by (auto simp add: Parse_Predict_def wf_item_def slice_drop_take \<alpha>_def)

lemma "wf_parse_bin1 xs k \<Longrightarrow> wf_bin1 (item ` xs) k"
  by (auto simp add: wf_bin1_def)

lemma wf_parse_bins1_impl_bins1: "wf_parse_bins1 xs \<Longrightarrow> wf_bins1 (map ((`) item) xs)"
  by (auto simp add: wf_bins1_def wf_parse_bins1_def wf_bin1_def)

lemma \<alpha>_mv_dot: "next_sym_Nt x A \<Longrightarrow> \<alpha> (mv_dot x) = \<alpha> x @ [Nt A]"
  by (auto simp add: \<alpha>_def mv_dot_def next_symbol_def is_complete_def take_Suc_conv_app_nth split: if_splits)

lemma wf_item_Pt1_impl_wf: "wf_item_Pt1 x k \<Longrightarrow> wf_item_Pt x k"
  by (simp add: wf_item1_def)

lemma wf_parse_complete: 
  assumes "wf_parse_bins1 Bs" "wf_item_Pt1 st (length Bs)" "is_complete (item st)" 
  shows "wf_parse_bin1 (Parse_Complete Bs st) (length Bs)"
  unfolding wf_parse_bin1.simps proof
  fix x
  assume "x \<in> Parse_Complete Bs st"
  then obtain a b where P: "x = (mv_dot a, Rule (lhs (item.prod (item st))) (rev (tree st)) # b) 
    \<and> (a, b) \<in> Bs ! from (item st) \<and> next_sym_Nt a (lhs (prod (item st))) \<and> from (item st) < length Bs"
    using assms by (auto simp add: Parse_Complete_def wf_item1_def wf_parse_bins1_def)
  then have wf_ab: "wf_item_Pt1 (a,b) (from (item st))" using assms by (auto simp add: wf_parse_bins1_def simp del: wf_item_Pt1.simps)
  then have 1: "wf_item1 (item x) (length Bs) \<and> (\<forall>t \<in> set (tree x). parse_tree P t)"
    using assms P by (auto simp add: wf_parse_bins1_def mv_dot_def wf_item1_def is_complete_def wf_item_def rhs_def \<alpha>_def next_symbol_def split: if_splits)
  have "fringes (rev (tree x)) = slice (from (item x)) (length Bs) w"
    using wf_ab assms(2) P
    by (auto simp add: wf_item1_def wf_item_def mv_dot_def slice_concat)
  then show "wf_item_Pt1 x (length Bs)" using assms P wf_ab 1 by (auto simp add: \<alpha>_mv_dot)
qed

lemma wf_parse_scan: 
  assumes "k < length w" "wf_parse_bin1 as k" shows "wf_parse_bin1 (Parse_Scan as k) (Suc k)"
  unfolding wf_parse_bin1.simps proof 
  fix x
  assume "x \<in> Parse_Scan as k"
  then obtain a b where P: "x = (mv_dot a, Sym (w ! k) # b) \<and> (a, b) \<in> as \<and> next_symbol a = Some (w ! k)"
    by (auto simp add: Parse_Scan_def)
  then have Broots: "map root (rev b) = \<alpha> a" and Bfringes: "fringes (rev b) = slice (from a) k w" and Btree: "\<forall>x \<in> set b. parse_tree P x"
    using assms(2) by auto
  from P have 1: "wf_item1 (mv_dot a) (Suc k)" using assms(1,2) 
    by (auto simp add: wf_item1_def next_symbol_def mv_dot_def is_complete_def wf_item_def split: if_splits)
  have "from a \<le> k" using P assms(2) by (auto simp add: wf_item1_def wf_item_def)
  then have 2: "fringes (rev b @ [Sym (w ! k)]) = slice (from (mv_dot a)) (Suc k) w"
    using Bfringes assms(1) by (auto simp add: slice_drop_take take_Suc_conv_app_nth mv_dot_def)
  have 3: "map root (rev b @ [Sym (w ! k)]) = \<alpha> (mv_dot a)"
    using Broots P by (auto simp add: \<alpha>_def mv_dot_def next_symbol_def is_complete_def take_Suc_conv_app_nth split: if_splits)
  then show "wf_item_Pt1 x (Suc k)" using P 1 2 3 Btree by auto
qed

end

subsection \<open>correctness of set based earley parser\<close>

context Earley_Gw_eps
begin

lemma wf_parse_predict1: "wf_item_Pt1 x k \<Longrightarrow> wf_parse_bin1 (Parse_Predict (item x) k) k"
  using \<epsilon>_free by (auto simp add: Parse_Predict_def wf_item1_def wf_item_def is_complete_def slice_drop_take \<alpha>_def)

lemma wf_parse_init1: "wf_parse_bin1 (Parse_Init) 0"
  using \<epsilon>_free by (auto simp add: Parse_Init_def slice_drop_take wf_item1_def wf_item_def is_complete_def \<alpha>_def)

lemma wf_parse_bin_close: 
  assumes "wf_parse_bins1 Bs" "wf_parse_bin1 B (length Bs)" 
  shows "wf_parse_bin1 (Parse_Close Bs B) (length Bs)"
  unfolding wf_parse_bin1.simps proof
  fix x
  assume "x \<in> Parse_Close Bs B"
  then show "wf_item_Pt1 x (length Bs)" using assms
  proof (induction x rule: Parse_Close.induct)
    case (Init x)
    then show ?case by simp
  next
    case (Predict x x')
    then show ?case using wf_parse_predict1[of x] by auto
  next
    case (Complete y x)
    then show ?case using wf_parse_complete[of Bs y] by auto
  qed
qed

lemma PClose_incl_Close: "x \<in> Parse_Close Bs B \<Longrightarrow> wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 B (length Bs) \<Longrightarrow>  item x \<in> Close (map ((`) item) Bs) (item ` B)"
proof (induction x rule: Parse_Close.induct) 
  case (Init x)
  then show ?case by (auto simp add: Close.Init)
next
  case (Predict x x')
  then show ?case by (auto simp add: Close.Predict Parse_Predict_item)
next
  case (Complete y x)
  then have l_from: "from (item y) < length Bs" using wf_parse_bin_close[of Bs B] by (auto simp add: wf_item1_def)
  then obtain a b where P: "(a, b) \<in> Bs ! from (item y) \<and> next_sym_Nt a (lhs (item.prod (item y)))
    \<and> x = (mv_dot a, Rule (lhs (item.prod (item y))) (rev (tree y)) # b)" using Complete by (auto simp add: Parse_Complete_def)
  then have a_in: "a \<in> (map ((`) item) Bs) ! from (item y)" using l_from
    by (metis fst_conv imageI nth_map)
  then have 1: "mv_dot a \<in> Complete (map ((`) item) Bs) (item y)" using P by (auto simp add: Complete_def)
  have "(item y) \<in> Close (map ((`) item) Bs) (item ` B)" using Complete wf_parse_bin_close by blast
  then have "mv_dot a \<in> Close (map ((`) item) Bs) (item ` B)" using 1 Close.Complete Complete l_from P a_in
         by auto
  then show ?case using P 1 by (auto simp add: Close.Complete)
qed

lemma Close_incl_PClose: "x \<in> Close (map ((`) item) Bs) (item ` B) \<Longrightarrow> wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 B (length Bs) \<Longrightarrow> \<exists>b. (x, b) \<in> Parse_Close Bs B"
proof(induction x rule: Close.induct)
  case (Init x)
  then show ?case
    using Parse_Close.Init by fastforce
next
  case (Predict x x')
  then show ?case using Parse_Close.Predict Parse_Predict_item by fastforce
next
  case (Complete y x)
  then have l_from: "from y < length (map ((`) item) Bs)" using wf_parse_bin_close[of Bs B] by (auto simp add: wf_item1_def)
  then have 1: "mv_dot x \<in> Close (map ((`) item) Bs) (item ` B) \<and> (\<exists> xb. (x,xb) \<in> Bs ! (from y))" using Close.Complete Complete by auto
  then obtain xb where P_xb: "(x,xb) \<in> Bs ! (from y)" by blast
  obtain yb where P_yb: "(y, yb) \<in> Parse_Close Bs B" using Complete by auto
  then obtain xbb where "(mv_dot x,xbb) \<in> Parse_Complete Bs (y,yb)" using Complete 1 l_from P_xb by (fastforce simp add: Parse_Complete_def)
  then show ?case using Complete Parse_Close.Complete[of "(y, yb)" Bs B "(mv_dot x,xbb)"] P_yb by auto
qed

lemma PClose_eq_Close: "wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 B (length Bs) \<Longrightarrow> item ` (Parse_Close Bs B) = Close (map ((`) item) Bs) (item ` B)"
  using PClose_incl_Close Close_incl_PClose image_iff by fastforce

lemma length_parse_bins: "length (Parse_bins k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma parse_bins_wf1_nth: "k \<le> length w \<Longrightarrow> i \<le> k \<Longrightarrow> wf_parse_bin1 (Parse_bins k ! i) i"
proof (induction k arbitrary: i)
  case 0
  then show ?case using wf_parse_init1 wf_parse_bin_close[of "[]" Parse_Init] by (auto simp add: wf_parse_bins1_def)
next
  case (Suc k)
  then have wf_bins: "wf_parse_bins1 (Parse_bins k)" unfolding wf_parse_bins1_def by (simp add: length_parse_bins less_Suc_eq_le)
  from Suc have 1: "\<not> i \<le> k \<longrightarrow> i = Suc k" by auto
  from Suc have "wf_parse_bin1 (last (Parse_bins k)) k" 
    using length_parse_bins[of k] last_conv_nth[of "Parse_bins k"] by fastforce
  then show ?case 
    using Suc wf_parse_scan[of k "last (Parse_bins k)"] wf_bins wf_parse_bin_close[of "Parse_bins k" "Parse_Scan (last (Parse_bins k)) k"] 
      length_parse_bins[of k] 1 by (cases "i \<le> k") (auto simp add: Let_def nth_append_left nth_append_right)
qed

lemma parse_bins_wf1: "k \<le> length w \<Longrightarrow> wf_parse_bins1 (Parse_bins k)"
  using parse_bins_wf1_nth by (auto simp add: wf_parse_bins1_def length_parse_bins less_Suc_eq_le)

lemma all_f_nth_impl_map: "length xs = length ys \<Longrightarrow> \<forall>i < length xs. T_nth_IL (xs ! i) = ys ! i \<Longrightarrow>  map T_nth_IL xs = ys"
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then have "(\<forall>i<length xs. T_nth_IL (xs ! i) = ys ! i) \<and> T_nth_IL x = y" by auto
  then show ?case using Cons by auto
qed

lemma item_Pbins_eq_bins_nth: "k \<le> length w \<Longrightarrow> i \<le> k \<Longrightarrow> item ` (Parse_bins k ! i) = bins k ! i"
proof (induction k arbitrary: i)
  case 0
  then show ?case using Parse_Init_item wf_parse_init1 PClose_eq_Close[of "[]" Parse_Init] 
    by (auto simp add: wf_parse_bins1_def)
next
  case (Suc k)
  then have map_bins: "map ((`) item) (Parse_bins k) = bins k" using all_f_nth_impl_map[of _ _ "(`) item"] by (auto simp add: length_parse_bins)
  from Suc have wf_last: "wf_parse_bin1 (last (Parse_bins k)) k" using parse_bins_wf1[of k] wf_parse_bins1_def length_parse_bins last_conv_nth
    by (metis One_nat_def Suc_leD Zero_not_Suc diff_Suc_1' eq_imp_le list.size(3) parse_bins_wf1_nth)
  then have wf_scan: "wf_parse_bin1 (Parse_Scan (last (Parse_bins k)) k) (Suc k)" using Suc wf_parse_scan by (auto simp del: wf_parse_bin1.simps)
  have item_last: "item ` last (Parse_bins k) = last (bins k)"
    by (metis Earley_Gw.bins_nonempty last_map list.map_disc_iff map_bins)
  from Suc have 1: "\<not> i \<le> k \<longrightarrow> i = Suc k" by auto
  then show ?case using Suc Parse_Scan_item PClose_eq_Close[of "Parse_bins k" "Parse_Scan (last (Parse_bins k)) k"] 
      parse_bins_wf1[of k] wf_scan map_bins item_last
    by (cases "i \<le> k") (auto simp add: Let_def length_parse_bins nth_append_left nth_append_right simp del: wf_parse_bin1.simps)
qed

lemma item_Pbins_eq_bins: "k \<le> length w \<Longrightarrow> map ((`) item) (Parse_bins k) = bins k"
  using item_Pbins_eq_bins_nth all_f_nth_impl_map[of _ _ "(`) item"] 
  by (auto simp add: length_parse_bins)

lemma "k \<le> length w \<Longrightarrow> i \<le> k \<Longrightarrow> item ` (Parse_bins k ! i) = \<S> i"
  using item_Pbins_eq_bins_nth by (simp add: bins_eq_\<S>_gen)

definition valid_parse_tree :: "('n, 'a) Prods \<Rightarrow> ('n, 'a) sym list \<Rightarrow> 'n \<Rightarrow> ('n,'a) tree \<Rightarrow> bool" where
"valid_parse_tree p ws A t \<equiv> parse_tree p t \<and> root t = Nt A \<and> fringe t = ws"

lemma valid_parse_tree_iff_derived: "(\<exists> t. valid_parse_tree p ws A t) \<longleftrightarrow> p \<turnstile> [Nt A] \<Rightarrow>* ws"
proof
  assume "\<exists>t. valid_parse_tree p ws A t"
  then obtain t where "valid_parse_tree p ws A t" by blast
  then show "p \<turnstile> [Nt A] \<Rightarrow>* ws" using fringe_steps_if_parse_tree[of p t] 
    by (auto simp add: valid_parse_tree_def)
next
  assume "p \<turnstile> [Nt A] \<Rightarrow>* ws"
  then show "\<exists>t. valid_parse_tree p ws A t" using parse_tree_if_derives[of p A ws] 
    by (auto simp add: valid_parse_tree_def)
qed


definition unambiguous :: "('n, 'a) Cfg \<Rightarrow> bool" where
"unambiguous g \<equiv> \<forall>w \<in> LangS g. \<forall> t1 t2. (valid_parse_tree (Prods g) (map Tm w) (Start g) t1 \<and> valid_parse_tree (Prods g) (map Tm w) (Start g) t2) \<longrightarrow> t1 = t2"

lemma wf_complete_imp_valid_tree: "wf_item_Pt x k \<Longrightarrow> is_complete (item x) \<Longrightarrow> valid_parse_tree P (slice (from (item x)) k w) (lhs (prod (item x))) (Rule (lhs (prod (item x))) (rev (tree x)))"
  by (auto simp add: valid_parse_tree_def wf_item1_def wf_item_def is_complete_def \<alpha>_def rhs_def)

lemma accepted_impl_valid_tree: 
  assumes "accepted" 
  shows "\<exists> s t. (s, t) \<in> Parse_bins (length w) ! (length w) \<and> valid_parse_tree P w S (Rule (lhs (prod s)) (rev t))"
proof-
  obtain x where "x \<in> \<S> (length w) \<and> is_final x" using accepted_def assms by blast
  then have P_x: "x \<in> bins (length w) ! (length w) \<and> lhs(prod x) = S \<and> from x = 0 \<and> is_complete x"
    by (auto simp add: is_final_def bins_eq_\<S>_gen)
  then have "x \<in> item  ` (Parse_bins (length w) ! (length w))" using item_Pbins_eq_bins_nth by auto
  then obtain t where bins_nth: "(x, t) \<in> Parse_bins (length w) ! (length w)" by auto
  then have "wf_item_Pt1 (x,t) (length w)" using parse_bins_wf1_nth[of "length w" "length w"] by auto
  then have "wf_item_Pt (x,t) (length w)" by (auto simp add: wf_item1_def)
  then show ?thesis using P_x bins_nth wf_complete_imp_valid_tree[of "(x,t)" "length w"] by auto
qed

(*would need other direction as well 
(\<exists> s t. (s, t) \<in> Parse_bins (length w) ! (length w) \<and> valid_parse_tree P w S (Rule (lhs (prod s)) (rev t))) \<Longrightarrow> accepted*)

lemma accepted_wf_cover_impl_tree: 
  assumes "accepted" "wf_parse_bin1 X (length w)" "\<forall>s \<in> \<S> (length w). \<exists>i \<in> X. fst i = s" 
  shows "\<exists>s t. (s,t) \<in> X \<and> is_final s \<and> valid_parse_tree P w S (Rule S (rev t))"
proof-
  obtain s where P_s: "s \<in> \<S> (length w) \<and> is_final s" using accepted_def assms by blast
  then obtain t where P_t: "(s, t) \<in> X \<and> lhs (prod s) = S" using assms(3)
    by (fastforce simp add: is_final_def)
  then have "valid_parse_tree P w S (Rule S (rev t))" using assms(2) P_s 
    by (auto simp add: slice_drop_take is_final_def valid_parse_tree_def wf_item1_def wf_item_def \<alpha>_def is_complete_def rhs_def)
  then show ?thesis using P_s P_t by auto
qed
end

section \<open>List based earley parser\<close>

context Earley_Gw
begin

subsection \<open>ParseItemList definition\<close>

type_synonym ('c, 'd) parseIL = "('c,'d) efficientItemList \<times> ('c,'d) tree list list"

fun inv_PIL :: "('n, 'a) parseIL \<Rightarrow> bool" where
"inv_PIL (il, ts) = (inv_IL il \<and> length (list il) = length ts)"

definition empty_PIL :: "nat \<Rightarrow> ('n, 'a) parseIL" where
"empty_PIL k = (empty_IL k, [] )"

fun PIL_list :: "('n, 'a) parseIL \<Rightarrow> ('n, 'a) item_Pt list" where
"PIL_list (il, ts) = (zip (list il) ts)"

fun parseIL_isin :: "('n, 'a) parseIL \<Rightarrow> ('n, 'a) item_Pt \<Rightarrow> bool" where
"parseIL_isin (il, ts) (s, t) = isin il s"

fun set_parseIL :: "('n, 'a) parseIL \<Rightarrow> ('n, 'a) item_Pt set" where
"set_parseIL (il, ts) = set (zip (list il) ts)"

fun parseIL_insert :: "('n, 'a) item_Pt \<Rightarrow> ('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL" where
"parseIL_insert (s, t) (il, ts) = (if isin il s then (il, ts) else (insert s il, t#ts))"

fun union_LPIL :: "('n, 'a) item_Pt list \<Rightarrow> ('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL" where
"union_LPIL [] pil = pil" |
"union_LPIL (a#as) pil = parseIL_insert a (union_LPIL as pil)"

definition union_PIL :: "('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL" where
"union_PIL pil1 pil2 = union_LPIL (PIL_list pil1) pil2"

definition PIL_of_List :: "nat \<Rightarrow> ('n, 'a) item_Pt list \<Rightarrow> ('n, 'a) parseIL" where
"PIL_of_List k as = union_LPIL as (empty_PIL k)"

fun minus_LPIL :: "nat \<Rightarrow> ('n, 'a) item_Pt list \<Rightarrow> ('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL" where
"minus_LPIL k [] pil = empty_PIL k" |
"minus_LPIL k (a#as) pil = (if \<not>(parseIL_isin pil a) then parseIL_insert a (minus_LPIL k as pil) else minus_LPIL k as pil)"

definition minus_PIL :: "('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL" where
"minus_PIL pil1 pil2 = minus_LPIL (length (froms (fst pil1)) - 1) (PIL_list pil1) pil2"

fun PIL_first :: "('n,'a) parseIL \<Rightarrow> ('n,'a) item_Pt" where
"PIL_first (il, t#ts) = (hd (list il), t)"

fun wf_PIL :: "('n,'a) parseIL \<Rightarrow> nat \<Rightarrow> bool" where
"wf_PIL pil k = wf_parse_bin1 (set_parseIL pil) k"

definition PIL_map_item :: "('n, 'a) parseIL \<Rightarrow> ('n,'a) item list" where
"PIL_map_item pil = list (fst pil)"

subsection \<open>ParseItemList lemmas\<close>

lemma [simp]: "list (empty_IL k) = []"
  by (simp add: empty_IL_def)

lemma [simp]: "isin il x \<Longrightarrow> list (insert x il) = list il"
  by (cases il) auto

lemma [simp]: "\<not> isin il x \<Longrightarrow> list (insert x il) = x # (list il)"
  by (cases il) (auto simp add: Let_def)

lemma PIL_first_in_set_PIL: 
  assumes "pil = (il, ts)" "ts \<noteq> []" "inv_PIL pil" shows "PIL_first pil \<in> set_parseIL pil"
proof-
  obtain a as t tss where "list il = a#as \<and> ts = t#tss"
    using assms by (metis inv_PIL.simps T_last.cases length_0_conv)
  then show ?thesis using assms by auto
qed

lemma PIL_inv_empty: "inv_PIL (empty_PIL k)"
  by (auto simp add: empty_PIL_def empty_inv)

lemma wf_empty_PIL: "wf_PIL (empty_PIL k) n"
  by (auto simp add: empty_PIL_def)

lemma length_empty_PIL[simp]: "length (froms (fst (empty_PIL k))) = Suc k" by (simp add: empty_PIL_def)

lemma PIL_inv_insert: "inv_PIL pil \<Longrightarrow> from (item x) < length (froms (fst pil)) \<Longrightarrow> inv_PIL (parseIL_insert x pil)"
  by (cases pil, cases x) (auto simp add: insert_inv_IL1)

lemma wf_PIL_insert: "wf_PIL pil k \<Longrightarrow> wf_item_Pt1 x k \<Longrightarrow> wf_PIL (parseIL_insert x pil) k"
  by(cases pil, cases x) auto

lemma length_insert_parse[simp]: "length (froms (fst (parseIL_insert x pil))) = length (froms (fst pil))" 
  by (cases pil, cases x) auto

lemma length_union_LPIL[simp]: "length (froms (fst (union_LPIL xs pil))) = length (froms (fst pil))"
  by (induction xs) auto

lemma PIL_inv_union_LPIL: "inv_PIL pil \<Longrightarrow> \<forall>x \<in> set xs. from (item x) < length (froms (fst pil)) 
  \<Longrightarrow> inv_PIL (union_LPIL xs pil)"
  by (cases pil, induction xs) (auto simp add: PIL_inv_insert)

lemma wf_union_LPIL: "wf_PIL pil k \<Longrightarrow> wf_parse_bin1 (set xs) k \<Longrightarrow> wf_PIL (union_LPIL xs pil) k"
  by (induction xs) (auto simp add: wf_PIL_insert simp del: wf_PIL.simps)

lemma PIL_inv_union_PIL: "inv_PIL pil1 \<Longrightarrow> inv_PIL pil2 \<Longrightarrow> length (froms (fst pil2)) \<ge> length (froms (fst pil1)) 
  \<Longrightarrow> inv_PIL (union_PIL pil1 pil2)"
proof-
  assume assms: "inv_PIL pil1" "inv_PIL pil2" "length (froms (fst pil2)) \<ge> length (froms (fst pil1))"
  then obtain xs fs ts where PIL: "pil1 = (ItemList xs fs, ts)"
    by (metis il_decomp set_parseIL.cases)
  then have "\<forall>x \<in> set xs. from x < length (froms (fst pil2))" using assms(1,3) by auto
  then have "\<forall>x \<in> set (zip xs ts). from (item x) < length (froms (fst pil2))" by (auto simp add: set_zip_leftD)
  then show ?thesis using PIL_inv_union_LPIL[of pil2 "zip xs ts"] assms(2) by (auto simp add: union_PIL_def PIL)
qed

lemma wf_union_PIL: "wf_PIL pil1 k \<Longrightarrow> wf_PIL pil2 k \<Longrightarrow> wf_PIL (union_PIL pil1 pil2) k"
  by (metis Earley_Gw.wf_PIL.elims(1) Earley_Gw.wf_union_LPIL PIL_list.simps set_parseIL.cases set_parseIL.simps union_PIL_def)

lemma PIL_inv_PIL_of_List: "\<forall>x \<in> set xs. from (item x) < Suc k \<Longrightarrow> inv_PIL (PIL_of_List k xs)"
  using PIL_inv_empty PIL_inv_union_LPIL PIL_of_List_def by simp

lemma wf_PIL_of_List: "wf_parse_bin1 (set xs) n \<Longrightarrow> wf_PIL (PIL_of_List k xs) n"
  using PIL_of_List_def wf_empty_PIL wf_union_LPIL by presburger

lemma length_PIL_of_List[simp]: "length (froms (fst (PIL_of_List k xs))) = Suc k"
  by (auto simp add: PIL_of_List_def)

lemma length_minus_LPIL[simp]: "length (froms (fst (minus_LPIL k xs pil))) = Suc k" 
  by (induction xs) auto

lemma length_minus_PIL[simp]: "inv_PIL pil1 \<Longrightarrow> length (froms (fst (minus_PIL pil1 pil2))) = length(froms (fst pil1))" 
  by (cases pil1, cases "fst pil1") (auto simp add: minus_PIL_def)

lemma PIL_inv_minus_LPIL: "\<forall>x \<in> set xs. from (item x) < Suc k \<Longrightarrow> inv_PIL (minus_LPIL k xs pil)"
  by (induction xs) (auto simp add: PIL_inv_empty PIL_inv_insert)

lemma wf_minus_LPIL: "wf_parse_bin1 (set xs) n \<Longrightarrow> wf_PIL (minus_LPIL k xs pil) n"
  by (induction xs) (auto simp add: wf_empty_PIL wf_PIL_insert simp del: wf_PIL.simps)

lemma PIL_inv_minus_PIL: "inv_PIL pil1 \<Longrightarrow> inv_PIL (minus_PIL pil1 pil2)"
proof-
  assume assms: "inv_PIL pil1"
  obtain xs fs ts where PIL: "pil1 = (ItemList xs fs, ts)"
    by (metis il_decomp set_parseIL.cases)
  then have "\<forall>x \<in> set xs. from x < length (froms (fst pil1))" using assms by auto
  then have "\<forall>x \<in> set (zip xs ts). from (item x) < length (froms (fst pil1))" by (auto simp add: set_zip_leftD)
  moreover have "length fs > 0" using assms by (auto simp add: PIL)
  ultimately show ?thesis using PIL_inv_minus_LPIL by (auto simp add: minus_PIL_def PIL)
qed

lemma wf_minus_PIL: "wf_PIL pil1 k \<Longrightarrow> wf_PIL (minus_PIL pil1 pil2) k"
  by (metis PIL_list.simps minus_PIL_def set_parseIL.elims wf_PIL.elims(2) wf_minus_LPIL)

lemma PIL_map_item_Cons2: "inv_PIL pil \<Longrightarrow> PIL_map_item pil = a#as \<Longrightarrow> \<exists>x xs. snd pil = x#xs"
  using PIL_map_item_def
  by (metis inv_PIL.simps length_Suc_conv prod.collapse)

lemma PIL_map_item_Cons1: "inv_PIL pil \<Longrightarrow> PIL_map_item pil = a#as \<Longrightarrow> \<exists>x xs m. fst pil = ItemList (x#xs) m"
  using PIL_map_item_Cons2
  by (metis efficientItemList.exhaust efficientItemList.sel(1) PIL_map_item_def)

(*parseIL operations are ItemList operations*)
lemma [simp]: "fst (empty_PIL k) = empty_IL k"
  by (simp add: empty_PIL_def)
lemma [simp]: "fst (parseIL_insert x pil) = insert (item x) (fst pil)"
  by (cases pil, cases x, cases "fst pil") auto
lemma [simp]: "fst (union_LPIL xs pil) = union_LIL (map item xs) (fst pil)"
  by (cases pil,  induction xs) auto
lemma [simp]: "fst (minus_LPIL k xs pil) = minus_LIL k (map item xs) (fst pil)"
  by (cases pil, induction xs) (auto)
lemma [simp]: "inv_PIL pil1 \<Longrightarrow> fst (minus_PIL pil1 pil2) = minus_IL (fst pil1) (fst pil2)"
  by (cases pil1) (auto simp add: minus_PIL_def minus_IL_def)


lemma set_zip_eq_length_rule: "length xs = length ys \<Longrightarrow> \<forall>x \<in> set (zip xs ys). Q (fst x) \<Longrightarrow> \<forall>x \<in> set xs. Q x"
  by (induction xs ys rule: list_induct2) auto

lemma wf_PIL_impl_wf1_IL: 
  assumes "inv_PIL pil" "wf_PIL pil k" shows "wf1_IL (fst pil) k"
proof-
  obtain as m ts where "pil = (ItemList as m, ts)"
    by (metis set_parseIL.cases il_decomp)
  then show ?thesis using set_zip_eq_length_rule[of as ts "\<lambda>x. wf_item1 x k"] assms 
    by (auto simp add: wf_bin1_def)
qed

lemma length_fst_PIL: assumes "inv_PIL pil" "wf_PIL pil k"
  shows "length (list (fst pil)) \<le> L * Suc K * Suc k"
proof-
  from assms have "wf_bin1 (set_ItemList (fst pil)) k" using wf_PIL_impl_wf1_IL by auto
  moreover have "distinct (list (fst pil))" using assms by (cases pil, cases "fst pil") auto
  ultimately show ?thesis using card_wf_bin1 distinct_card
    by fastforce
qed

lemma length_snd_PIL: assumes "inv_PIL pil" "wf_PIL pil k"
  shows "length (snd pil) \<le> L * Suc K * Suc k"
proof-
  from assms have "length (list (fst pil)) \<le> L * Suc K * Suc k" using length_fst_PIL by simp
  then show ?thesis using assms by (cases pil) auto
qed


subsection \<open>Parsing algorithm\<close>

definition Parse_Predict_L :: "('n,'a) item \<Rightarrow> nat \<Rightarrow> ('n,'a) item_Pt list" where 
"Parse_Predict_L x k = map (\<lambda>p. (Item p 0 k, [])) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps)"


definition Parse_Complete_L :: "('n, 'a) item_Pt list list \<Rightarrow> ('n, 'a) item_Pt \<Rightarrow> ('n, 'a) item_Pt list" where
  "Parse_Complete_L Bs y = map (\<lambda> x. let (p,t) = x in (mv_dot p, (Rule (lhs(prod (item y))) (rev (tree y)))#t)) (filter (\<lambda> x. let (p,t) = x in next_sym_Nt p (lhs(prod (item y)))) (Bs ! from (item y)))"

(*definition Parse_Complete_L :: "('n, 'a) item_Pt list list \<Rightarrow> ('n, 'a) item_Pt \<Rightarrow> ('n, 'a) item_Pt list" where
  "Parse_Complete_L Bs y = map (\<lambda> (p, t). (mv_dot p, (Rule (lhs(prod (item y))) (rev (tree y)))#t)) (filter (\<lambda> (p, t). next_sym_Nt p (lhs(prod (item y)))) (Bs ! from (item y)))"*)

definition Parse_Init_L :: "('n,'a) item_Pt list" where
  "Parse_Init_L = map (\<lambda>p. (Item p 0 0, [])) (filter (\<lambda> p. lhs p = (S)) ps)"


definition Parse_Scan_L :: "('n,'a) item_Pt list \<Rightarrow> nat \<Rightarrow> ('n,'a) item_Pt list" where
  "Parse_Scan_L Bs k = (let x = Some (w ! k) in map (\<lambda> y. let (p,t) = y in (mv_dot p, (Sym (the x))#t)) (filter (\<lambda> y. let (p,t) = y in next_symbol p = x) Bs))"

fun Parse_step_fun :: "('n, 'a) item_Pt list list \<Rightarrow>  ('n, 'a) parseIL \<times> ('n, 'a) parseIL \<Rightarrow> ('n, 'a) parseIL \<times> ('n, 'a) parseIL" where
  "Parse_step_fun Bs ((il1, []), pil2) = undefined" |
  "Parse_step_fun Bs ((il1, ts1), pil2) = (let b = PIL_first (il1, ts1) in 
    (let step = (if is_complete (item b) then Parse_Complete_L Bs b else Parse_Predict_L (item b) (length Bs)) in
    ( minus_PIL (union_LPIL step (il1, ts1)) (parseIL_insert b pil2), parseIL_insert b pil2) ))"

definition Parse_steps :: "('n, 'a) item_Pt list list \<Rightarrow> ('n, 'a) parseIL \<times> ('n, 'a) parseIL \<Rightarrow> (('n, 'a) parseIL \<times> ('n, 'a) parseIL) option" where
  "Parse_steps Bs BC = while_option (\<lambda>(B,C). PIL_map_item B \<noteq> []) (Parse_step_fun Bs) BC"

definition Parse_close2_L :: "('n, 'a) item_Pt list list \<Rightarrow> ('n, 'a) parseIL \<Rightarrow> ('n, 'a) item_Pt list" where
"Parse_close2_L Bs B = PIL_list (snd (the (Parse_steps Bs (B, empty_PIL (length Bs)))))"

fun Parse_bins_L :: "nat \<Rightarrow> ('n,'a) item_Pt list list" where
"Parse_bins_L 0 = [Parse_close2_L [] (PIL_of_List 0 Parse_Init_L)]" |
"Parse_bins_L (Suc k) = (let Bs = Parse_bins_L k in Bs @ [Parse_close2_L Bs (PIL_of_List (length Bs) (Parse_Scan_L (last Bs) k))])"

fun get_parse_tree :: "('n,'a) item_Pt list \<Rightarrow> ('n,'a) tree option" where
"get_parse_tree [] = None" |
"get_parse_tree (x#xs) = (if is_final (fst x) then Some (Rule S (rev (snd x))) else get_parse_tree xs)"

lemma get_parse_tree_NF: "is_final (fst x) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>s t. (s,t) \<in> set xs \<and> is_final s \<and> get_parse_tree xs = Some (Rule S (rev t))"
  by (induction xs) auto

fun parse_tree_w where
"parse_tree_w _ = the (get_parse_tree (last (Parse_bins_L (length w))))"
(*TODO make a definition and move outside of Context*)

end

subsection \<open>Correctness of list based earley parser\<close>

context Earley_Gw
begin

lemma PPredict_L_eq_Predict_L: "map item (Parse_Predict_L s k) = Predict_L s k"
  by (auto simp add: Parse_Predict_L_def Predict_L_def)

lemma PComplete_L_eq_Complete_L: 
  assumes "from (item b) < length Bs" 
  shows "map item (Parse_Complete_L Bs b) = Complete_L (map (map item) Bs) (item b)"
proof-
  have "map item (Parse_Complete_L Bs b)
    = map mv_dot (map item (filter (\<lambda>(p, t). next_sym_Nt p (lhs (item.prod (item b)))) (Bs ! from (item b))))" by (auto simp add: Parse_Complete_L_def)
  also have "... = map mv_dot (map item (filter (\<lambda>x. next_sym_Nt (item x) (lhs (item.prod (item b)))) (Bs ! from (item b))))"
    by (simp add: case_prod_beta')
  also have "... = map mv_dot (filter (\<lambda>x. next_sym_Nt x (lhs (item.prod (item b)))) (map item (Bs ! from (item b))))"
    using filter_map
    by (metis (no_types, lifting) ext comp_def)
  finally show ?thesis
    using assms by (auto simp add: Complete_L_def)
qed

lemma Parse_Init_L_eq_Init_L: "map item Parse_Init_L = Init_L"
  by (auto simp add: Parse_Init_L_def Init_L_def)

lemma Parse_Scan_L_eq_Scan_L: "map item (Parse_Scan_L Bs k) = Scan_L (map item Bs) k"
proof-
  have "map item (Parse_Scan_L Bs k) = map mv_dot (map item (filter (\<lambda>(p, t).  next_symbol p = Some (w ! k)) Bs))"
    by (auto simp add: Parse_Scan_L_def)
  also have "... = map mv_dot (map item (filter (\<lambda>x. next_symbol (item x) = Some (w ! k)) Bs))"
    by (simp add: case_prod_beta')
  also have "... = map mv_dot (filter (\<lambda>x. next_symbol  x = Some (w ! k)) (map item Bs))"
    using filter_map
    by (metis (no_types, lifting) ext comp_def)
  finally show ?thesis
    by (auto simp add: Scan_L_def)
qed

lemma PCompleteL_sub_PComplete: "from (item st) < length Bs \<Longrightarrow> set (Parse_Complete_L Bs st) \<subseteq> Parse_Complete (map set Bs) st"
  by (auto simp add: Parse_Complete_L_def Parse_Complete_def)
  
lemma wf1_Parse_Complete_L: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_item_Pt1 st (length Bs)" "is_complete (item st)" 
  shows "wf_parse_bin1 (set (Parse_Complete_L Bs st)) (length Bs)"
proof-
  have "set (Parse_Complete_L Bs st) \<subseteq> Parse_Complete (map set Bs) st"
    using assms PCompleteL_sub_PComplete by (auto simp add: wf_item1_def)
  then show ?thesis using assms wf_parse_complete[of "map set Bs" st] by auto
qed

lemma PScanL_sub_PScan: "k < length w \<Longrightarrow> set (Parse_Scan_L xs k) \<subseteq> Parse_Scan (set xs) k"
  by (auto simp add: Parse_Scan_L_def Parse_Scan_def w_def)

lemma wf1_Parse_Scan_L: "k < length w \<Longrightarrow> wf_parse_bin1 (set xs) k \<Longrightarrow> wf_parse_bin1 (set (Parse_Scan_L xs k)) (Suc k)"
  using PScanL_sub_PScan wf_parse_scan
  by (meson subset_code(1) wf_parse_bin1.elims(2,3))

end

context Earley_Gw_eps
begin

lemma wf1_Parse_Predict_L: "wf_item_Pt1 s k \<Longrightarrow> wf_parse_bin1 (set (Parse_Predict_L (item s) k)) k"
  using \<epsilon>_free by (auto simp add: Parse_Predict_L_def wf_item1_def wf_item_def slice_drop_take \<alpha>_def is_complete_def)

lemma wf1_Parse_Init_L: "wf_parse_bin1 (set (Parse_Init_L)) 0"
  using \<epsilon>_free by (auto simp add: Parse_Init_L_def wf_item1_def wf_item_def slice_drop_take \<alpha>_def is_complete_def) 

lemma forall_from_Suc_parse: "wf_parse_bin1 xs k \<Longrightarrow> \<forall>x \<in> xs. from (item x) < Suc k"
  by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)

lemma PIL_inv_parse_step1: "pil1 = (il1, t#ts) \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL pil1 (length Bs) 
  \<Longrightarrow> length (froms (fst pil1)) = Suc (length Bs) \<Longrightarrow> wf_parse_bins1 (map set Bs) \<Longrightarrow> Parse_step_fun Bs (pil1, pil2) = (pil3, pil4) \<Longrightarrow> inv_PIL pil3"
proof-
  assume assms: "pil1 = (il1, t#ts)" "inv_PIL pil1" "wf_PIL pil1 (length Bs)" "length (froms (fst pil1)) = Suc (length Bs)"
    "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)" "wf_parse_bins1 (map set Bs)"
  let ?b = "PIL_first pil1"
  let ?step = "if is_complete (fst ?b) then Parse_Complete_L Bs ?b else Parse_Predict_L (item ?b) (length Bs)"
  have "wf_item_Pt1 ?b (length Bs)" using assms PIL_first_in_set_PIL
    by (meson list.discI wf_PIL.simps wf_parse_bin1.elims(2))
  then have "wf_parse_bin1 (set ?step) (length Bs)" using wf1_Parse_Predict_L wf1_Parse_Complete_L assms
    by (smt (verit, del_insts))
  then have "inv_PIL (union_LPIL ?step pil1)" 
    using PIL_inv_union_LPIL assms(2,4) forall_from_Suc_parse by auto
  then show "inv_PIL pil3"
    using PIL_inv_minus_PIL[of "union_LPIL ?step pil1" "(parseIL_insert (hd (list il1), t) pil2)"] 
      assms(1,5) by (auto simp add: Let_def)
qed

lemma PIL_inv_parse_step1': "PIL_map_item pil1 \<noteq> [] \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL pil1 (length Bs) 
  \<Longrightarrow> length (froms (fst pil1)) = Suc (length Bs) \<Longrightarrow> wf_parse_bins1 (map set Bs) 
  \<Longrightarrow> Parse_step_fun Bs (pil1, pil2) = (pil3, pil4) \<Longrightarrow> inv_PIL pil3"
  using PIL_inv_parse_step1 PIL_map_item_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma PIL_inv_parse_step2: 
  assumes "pil1 = (il1, t#ts)" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)"
  "inv_PIL pil2" "inv_PIL pil1" "length (froms (fst pil2)) = length (froms (fst pil1))"
shows "inv_PIL pil4"
proof-
  have "\<forall> x \<in> set (list il1). from x < length (froms (fst pil2))" using assms by (cases il1) auto
  then have "\<forall> x \<in> set (zip (list il1) (t#ts)). from (item x) < length (froms (fst pil2))" 
    by (auto simp add: set_zip_leftD)
  moreover have "(hd (list il1), t) \<in> set (zip (list il1) (t#ts))"
    by (metis PIL_first.simps PIL_first_in_set_PIL assms(1,4) list.distinct(1) set_parseIL.simps)
  ultimately show ?thesis
    using PIL_inv_insert assms by (fastforce simp add: Let_def)
qed

lemma PIL_inv_parse_step2': 
  assumes "PIL_map_item pil1 \<noteq> []"  "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)"
  "inv_PIL pil2" "inv_PIL pil1" "length (froms (fst pil2)) = length (froms (fst pil1))"
shows "inv_PIL pil4"
  using PIL_inv_parse_step2 PIL_map_item_Cons2 assms
  by (metis recognized_L.cases surjective_pairing)

lemma Pstep_fun_eq_step_fun:
  assumes step: "list il1 \<noteq> []" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)" "step_fun (map (map item) Bs) (il1, il2) = (il3, il4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_parse_bin1 (set_parseIL pil1) (length Bs)" "wf_parse_bins1 (map set Bs)"
  and eq_start: "fst pil1 = il1" "fst pil2 = il2"
  shows "fst pil3 = il3 \<and> fst pil4 = il4"
proof- 
  from step obtain a as m where P_il1: "il1 = ItemList (a#as) m"
    by (metis efficientItemList.sel(1) recognized_L.cases il_decomp)
  then obtain t ts where P_ts: "pil1 = (il1, t#ts)" using eq_start invs(1)
    by (metis efficientItemList.sel(1) inv_PIL.simps Suc_length_conv fst_conv set_parseIL.cases)
  let ?step = "if is_complete a then Parse_Complete_L Bs (a, t) else Parse_Predict_L a (length Bs)"
  have wf_at: "wf_item_Pt1 (a,t) (length Bs)" using wf P_il1 P_ts by auto
  then have "wf_parse_bin1 (set ?step) (length Bs)"
    using wf1_Parse_Predict_L wf1_Parse_Complete_L wf
    by (smt (verit, ccfv_threshold) fst_conv)
  then have "inv_PIL (union_LPIL (?step) pil1)" 
    using PIL_inv_union_LPIL invs forall_from_Suc_parse leng by auto
  then show ?thesis 
    using step eq_start invs P_ts P_il1 PPredict_L_eq_Predict_L PComplete_L_eq_Complete_L wf PIL_first_in_set_PIL 
    by (auto simp add: Let_def wf_item1_def)
qed

lemma Pstep_fun_eq_step_fun1:
  assumes step: "PIL_map_item pil1 \<noteq> []" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_parse_bin1 (set_parseIL pil1) (length Bs)" "wf_parse_bins1 (map set Bs)"
shows "(let x = step_fun (map (map item) Bs) (fst pil1, fst pil2) in fst pil3 = (fst x) \<and> fst pil4 = (snd x))"
  using Pstep_fun_eq_step_fun
  by (metis PIL_map_item_def invs leng local.step(1,2) local.wf surjective_pairing)

lemma wf_parse_step1: 
  assumes "pil1 = (il1, t#ts)" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)" 
  and wf_parse: "wf_parse_bins1 (map set Bs)" "wf_PIL pil1 (length Bs)" "inv_PIL pil1" 
shows "wf_PIL pil3 (length Bs)"
proof-
  let ?b = "PIL_first (il1, t#ts)"
  let ?step = "(if is_complete (item ?b) then Parse_Complete_L Bs ?b else Parse_Predict_L (item ?b) (length Bs))"
  from assms have 3: "pil3 = minus_PIL (union_LPIL ?step (il1, t#ts)) (parseIL_insert ?b pil2)" 
    by (auto simp add: Let_def)
  have "wf_item_Pt1 ?b (length Bs)" using wf_parse PIL_first_in_set_PIL assms by (auto simp del: wf_item_Pt1.simps PIL_first.simps)
  then have "wf_parse_bin1 (set ?step) (length Bs)" using wf1_Parse_Complete_L wf1_Parse_Predict_L wf_parse
    by presburger
  then show ?thesis 
  using wf_minus_PIL wf_union_LPIL 3 wf_parse assms(1) by blast
qed

lemma wf_parse_step1': "PIL_map_item pil1 \<noteq> [] \<Longrightarrow> Parse_step_fun Bs (pil1, pil2) = (pil3, pil4) 
  \<Longrightarrow> wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PIL pil1 (length Bs) \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL pil3 (length Bs)"
  using wf_parse_step1 PIL_map_item_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma wf_parse_step2: 
  assumes "pil1 = (il1, t#ts)" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)" 
  and wf_parse: "wf_PIL pil1 (length Bs)" "inv_PIL pil1" "wf_PIL pil2 (length Bs)" 
  shows "wf_PIL pil4 (length Bs)"
proof-
  let ?b = "PIL_first (il1, t#ts)"
  from assms have 4: "pil4 = parseIL_insert ?b pil2" by (auto simp add: Let_def)
  have "wf_item_Pt1 ?b (length Bs)" using wf_parse(1,2) PIL_first_in_set_PIL assms(1) 
    by (auto simp del: wf_item_Pt1.simps PIL_first.simps)
  then show ?thesis using wf_PIL_insert wf_parse(1) assms 4 by blast
qed

lemma wf_parse_step2': "PIL_map_item pil1 \<noteq> [] \<Longrightarrow> Parse_step_fun Bs (pil1, pil2) = (pil3, pil4) 
  \<Longrightarrow> wf_PIL pil1 (length Bs) \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL pil2 (length Bs) \<Longrightarrow> wf_PIL pil4 (length Bs)"
  using wf_parse_step2 PIL_map_item_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma length_parse_step1: 
  assumes step: "pil1 = (il1, t#ts)" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_PIL pil1 (length Bs)" "wf_parse_bins1 (map set Bs)"
  shows "length (froms (fst pil3)) = length (froms (fst pil1))"
proof- 
  have "list il1 \<noteq> []" using invs step
    by force
  then obtain a as m where P_il1: "il1 = ItemList (a#as) m"
    by (metis efficientItemList.sel(1) il_decomp recognized_L.cases)
  let ?step = "if is_complete a then Parse_Complete_L Bs (a, t) else Parse_Predict_L a (length Bs)"
  have wf_at: "wf_item_Pt1 (a,t) (length Bs)" using wf P_il1 step(1) by auto
  then have "wf_parse_bin1 (set ?step) (length Bs)"
    using wf1_Parse_Predict_L wf1_Parse_Complete_L wf
    by (smt (verit, ccfv_threshold) fst_conv)
  then have "inv_PIL (union_LPIL (?step) pil1)" 
    using PIL_inv_union_LPIL invs forall_from_Suc_parse leng by auto
  then show ?thesis using length_union_LPIL length_minus_PIL[of "union_LPIL (?step) pil1"] step P_il1 
    by (auto simp add: Let_def)
qed

lemma length_parse_step1': 
  assumes "PIL_map_item pil1 \<noteq> []" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_PIL pil1 (length Bs)" "wf_parse_bins1 (map set Bs)"
  shows "length (froms (fst pil3)) = length (froms (fst pil1))"
using length_parse_step1 PIL_map_item_Cons2 assms invs leng wf
  by (metis eq_snd_iff neq_Nil_conv)

lemma length_parse_step2: 
  assumes step: "pil1 = (il1, t#ts)" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)"
shows "length (froms (fst pil4)) = length (froms (fst pil2))" 
  using step by (auto simp add: Let_def)

lemma length_parse_step2': 
  assumes "PIL_map_item pil1 \<noteq> []" "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)" "inv_PIL pil1"
  shows "length (froms (fst pil4)) = length (froms (fst pil2))" 
using length_parse_step2 PIL_map_item_Cons2 assms
  by (metis eq_snd_iff neq_Nil_conv)

lemma Parse_steps_inv1: 
  assumes inv: "inv_PIL pil1" and wf: "wf_PIL pil1 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and step: "Parse_steps Bs (pil1,pil2) = Some (pil1', pil2')"
shows "inv_PIL pil1'"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). inv_PIL pil1 \<and> wf_PIL pil1 (length Bs) \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil1)) = Suc (length Bs)"] 
    PIL_inv_parse_step1' wf_parse_step1' length_parse_step1' step inv leng wf unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma Parse_steps_inv2: 
  assumes inv: "inv_PIL pil2" "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)"
  and wf: "wf_PIL pil1 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and step: "Parse_steps Bs (pil1,pil2) = Some (pil1', pil2')"
shows "inv_PIL pil2'"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). inv_PIL pil2 \<and> inv_PIL pil1 
      \<and> length (froms (fst pil1)) = Suc (length Bs) \<and> length (froms (fst pil2)) = Suc (length Bs)
      \<and> wf_PIL pil1 (length Bs) \<and> wf_parse_bins1 (map set Bs)"] 
    PIL_inv_parse_step2' PIL_inv_parse_step1' length_parse_step1' length_parse_step2' wf_parse_step1' 
    step inv leng wf unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)


lemma Parse_steps_wf1: 
  assumes wf: "wf_parse_bins1 (map set Bs)" "wf_PIL pil1 (length Bs)"
  and inv: "inv_PIL pil1" 
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and sf: "Parse_steps Bs (pil1,pil2) = Some (pil1', pil2')"  
shows "wf_PIL pil1' (length Bs)"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). wf_PIL pil1 (length Bs) \<and> inv_PIL pil1 
      \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil1)) = Suc (length Bs)"] 
    wf_parse_step1' step_fun_inv1_il PIL_inv_parse_step1' length_parse_step1' wf sf inv leng unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma Parse_steps_wf2: 
  assumes wf: "wf_parse_bins1 (map set Bs)" "wf_PIL pil1 (length Bs)" "wf_PIL pil2 (length Bs)"
  and inv: "inv_PIL pil1" 
  and leng: "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)"
  and sf: "Parse_steps Bs (pil1,pil2) = Some (pil1', pil2')"  
shows "wf_PIL pil2' (length Bs)"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). wf_PIL pil2 (length Bs) \<and> wf_PIL pil1 (length Bs) 
      \<and> inv_PIL pil1 \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil1)) = Suc (length Bs)
      \<and> length (froms (fst pil2)) = Suc (length Bs)"] 
    wf_parse_step1' wf_parse_step2' step_fun_inv1_il PIL_inv_parse_step1' length_parse_step1'
    length_parse_step2' wf sf inv leng unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_one_step: "list a \<noteq> [] \<Longrightarrow> steps Bs (a,b) = Some (a',b') \<Longrightarrow> step_fun Bs (a,b) = (c,d) \<Longrightarrow> steps Bs (c,d) = Some (a',b')"
  unfolding steps_def
  by (simp add: while_option_unfold)

lemma Parse_steps_steps:
  assumes step: "list il1 \<noteq> []" "Parse_steps Bs (pil1, pil2) = Some (pil3, pil4)" "steps (map (map item) Bs) (il1, il2) = Some (il3, il4)"
  and eq_start: "fst pil1 = il1" "fst pil2 = il2"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and invs: "inv_PIL pil1"
  and wf: "wf_parse_bin1 (set_parseIL pil1) (length Bs)" "wf_parse_bins1 (map set Bs)"
shows "steps (map (map item) Bs) (fst pil3, fst pil4) = Some (il3, il4)"
proof-
  let ?P = "\<lambda>(pil3,pil4). steps (map (map item) Bs) (fst pil3, fst pil4) = Some (il3, il4) \<and> inv_PIL pil3 
      \<and> wf_PIL pil3 (length Bs) \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil3)) = Suc (length Bs)"
  let ?b = "(\<lambda>(B,C). PIL_map_item B \<noteq> [])" 
  let ?c = "(Parse_step_fun Bs)"
  have "?P s \<Longrightarrow> ?b s \<Longrightarrow> ?P (?c s)" for s
  proof-
    assume P: "?P s" and b: "?b s"
    then obtain il1' ts1 il2' ts2 il3' ts3 il4' ts4 where P_s: "s = ((il1', ts1), (il2', ts2)) \<and> Parse_step_fun Bs s = ((il3', ts3), (il4', ts4))"
      by (metis (no_types, opaque_lifting) T_fst.cases)
    obtain il5 il6 where step_f: "step_fun (map (map item) Bs) (il1', il2') = (il5, il6)"
      using PIL_map_item_def by fastforce
    then have eq: "il5 = il3' \<and> il6  = il4'" using b P P_s 
        Pstep_fun_eq_step_fun[of _ _ "(il1', ts1)" "(il2', ts2)" "(il3', ts3)" "(il4', ts4)" il2' il5 il6]
      by (auto simp add: PIL_map_item_def)
    have 1: "inv_PIL (il3', ts3) \<and> wf_parse_bin1 (set_parseIL (il3', ts3)) (length Bs) 
        \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (il3')) = Suc (length Bs) "
      using P b P_s PIL_inv_parse_step1'[of "(il1', ts1)"] wf_parse_step1' length_parse_step1'
      by (auto simp del: wf_parse_bin1.simps )
    have "list il1' \<noteq> []" using b P_s by (auto simp add: PIL_map_item_def)
    then show "?P (?c s)" using P 1 P_s eq step_f steps_one_step[of il1' "(map (map item) Bs)" il2' il3 il4] 
       by (auto simp add:  simp del: wf_parse_bin1.simps)
  qed
  then show ?thesis
  using while_option_rule[where P= ?P, where b= ?b, where c= ?c] using eq_start invs wf step leng unfolding Parse_steps_def
  by (smt (verit) Parse_steps_def case_prod_conv wf_PIL.elims(1))
qed

theorem Parse_steps_NF: "wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PIL pil1 (length Bs) 
  \<Longrightarrow> wf_PIL pil2 (length Bs) \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> inv_PIL pil2 
  \<Longrightarrow> length (froms (fst pil1)) = Suc (length Bs) \<Longrightarrow> length (froms (fst pil2)) = Suc (length Bs)
  \<Longrightarrow> \<exists>pil1' pil2'. Parse_steps Bs (pil1,pil2) = Some (pil1',pil2') "
using wf_step_fun_less[of "length Bs"]
proof (induction "(fst pil1,fst pil2)" arbitrary: pil1 pil2 rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "list (fst pil1) = []"
    thus ?thesis by (simp add: while_option_unfold Parse_steps_def PIL_map_item_def)
  next
    let ?steps = "while_option (\<lambda>(as,bs). PIL_map_item as \<noteq> []) (Parse_step_fun Bs)"
    assume cons: "list (fst pil1) \<noteq> []"
    then obtain il1 t ts where P_pil1: "pil1 = (il1, t#ts)" using less.prems(4)
      by (metis PIL_map_item_Cons2 PIL_map_item_def list.exhaust surjective_pairing)
    then obtain pil1' pil2'
      where P_step: "(pil1',pil2') = Parse_step_fun Bs (pil1,pil2)"
      by (metis T_fst.cases)
    then have wf_inv: "wf_PIL pil1' (length Bs)" "wf_PIL pil2' (length Bs)" "inv_PIL pil1'" "inv_PIL pil2'"
      "length (froms (fst pil1')) = Suc (length Bs)" "length (froms (fst pil2')) = Suc (length Bs)"
      using wf_parse_step1 wf_parse_step2 PIL_inv_parse_step1 PIL_inv_parse_step2 
        length_parse_step1 length_parse_step2 less.prems P_pil1
      by (metis, metis, metis, metis, metis, metis)
      
    from P_step have step_f: "(fst pil1',fst pil2') = step_fun (map (map item) Bs) (fst pil1, fst pil2)"
      using less.prems Pstep_fun_eq_step_fun1[of pil1 Bs pil2 pil1' pil2'] cons unfolding PIL_map_item_def by (auto simp add: Let_def)
    have "wf1_IL (fst pil1) (length Bs) \<and> wf1_IL (fst pil2) (length Bs)"
      using less.prems wf_PIL_impl_wf1_IL by (cases pil1, cases pil2) (auto simp del: wf_PIL.simps inv_PIL.simps)
    then have "((fst pil1',fst pil2'), (fst pil1, fst pil2)) \<in> step_fun_less (length Bs)" 
      using less.prems step_fun_less_step[of "fst pil1" "(map (map item) Bs)" "fst pil2"] \<open>list (fst pil1) \<noteq> []\<close> step_f 
      by (cases pil1, cases pil2) (auto simp add: wf_parse_bins1_def wf_bins1_def wf_bin1_def)
    from less.hyps[OF this \<open>wf_parse_bins1 (map set Bs)\<close> wf_inv]
    show ?thesis
      by (simp add: P_step while_option_unfold Parse_steps_def)
  qed
qed

lemma Pclose2_L_eq_close2_L: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_PIL pil1 (length Bs)" "inv_PIL pil1" 
    "length (froms (fst pil1)) = Suc (length Bs)"
  shows "map item (Parse_close2_L Bs pil1) = close2_L (map (map item) Bs) (fst pil1)"
proof-
  obtain pil3 pil4 where P_steps: "Parse_steps Bs (pil1, empty_PIL (length Bs)) = Some (pil3, pil4)"
    using assms Parse_steps_NF PIL_inv_empty wf_empty_PIL length_empty_PIL by blast
  then have P_pil3: "wf_PIL pil3 (length Bs) \<and> inv_PIL pil3 \<and> list (fst pil3) = []"
    using Parse_steps_wf1 Parse_steps_inv1 while_option_stop assms unfolding Parse_steps_def PIL_map_item_def
    by (metis (mono_tags, lifting) case_prodI)
  from P_steps have inv_pil4: "inv_PIL pil4" 
    using PIL_inv_empty wf_empty_PIL length_empty_PIL Parse_steps_inv2 assms by blast
  from assms have "wf_bins1 (map set (map (map item) Bs))" using wf_parse_bins1_impl_bins1[of "map set Bs"] 
    by (auto simp add: wf_bins1_def)
  then obtain il3 il4 where steps: "steps (map (map item) Bs) (fst pil1, empty_IL (length Bs)) = Some (il3, il4)"
    using assms Close2_L_NF[of "(map (map item) Bs)" "fst pil1" "empty_IL (length Bs)"] wf_PIL_impl_wf1_IL[of "pil1" "length Bs"] set_empty_IL
    by (cases pil1) (auto simp add: wf_bin1_def empty_inv)
  have "fst pil3 = il3 \<and> fst pil4 = il4"
  proof (cases "list (fst pil1) = []")
    case True
    then show ?thesis using P_steps steps unfolding Parse_steps_def steps_def PIL_map_item_def
      by (auto simp add: while_option_unfold)
  next
    case False
    then have "steps (map (map item) Bs) (fst pil3, fst pil4) = Some (il3, il4)"
      using Parse_steps_steps assms P_steps steps P_pil3 by auto
    then show ?thesis using P_pil3 unfolding steps_def by (auto simp add: while_option_unfold)
  qed
  then show ?thesis using P_steps steps inv_pil4 unfolding Parse_close2_L_def close2_L_def 
    by (cases pil4) auto
qed

lemma set_PIL_list_eq_set_PIL[simp]: "set (PIL_list pil) = set_parseIL pil"
  by (cases pil) auto

lemma wf_Parse_close2_L: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_PIL pil (length Bs)" "inv_PIL pil" 
      "length (froms (fst pil)) = Suc (length Bs)"
  shows "wf_parse_bin1 (set (Parse_close2_L Bs pil)) (length Bs)"
proof-
  obtain pil3 pil4 where P: "Parse_steps Bs (pil, empty_PIL (length Bs)) = Some (pil3, pil4)"
    using assms Parse_steps_NF wf_empty_PIL PIL_inv_empty length_empty_PIL by blast
  then have "wf_PIL pil4 (length Bs)" using Parse_steps_wf2 assms
    using wf_empty_PIL length_empty_PIL by blast
  then show ?thesis unfolding Parse_close2_L_def P by (auto simp del: wf_parse_bin1.simps)
qed

lemma length_Parse_bins[simp]: "length (Parse_bins_L k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma wf_parse_bins_L: "k \<le> length w \<Longrightarrow> wf_parse_bins1 (map set (Parse_bins_L k))"
proof (induction k)
  case 0
  then show ?case using wf_PIL_of_List wf_Parse_close2_L[of "[]"] 
      wf1_Parse_Init_L PIL_inv_PIL_of_List[OF forall_from_Suc_parse] 
    by (auto simp add: wf_parse_bins1_def simp del: wf_parse_bin1.simps)
next
  case (Suc k)
  have "Parse_bins_L k \<noteq> []" using length_Parse_bins
    by (metis length_0_conv nat.distinct(1))
  then have "wf_parse_bin1 (set (last (Parse_bins_L k))) k" using Suc length_Parse_bins wf_parse_bins1_def 
    by (auto simp add: last_conv_nth simp del: wf_parse_bin1.simps)
  then have 1: "wf_parse_bin1 (set (Parse_close2_L (Parse_bins_L k) (PIL_of_List (Suc k) (Parse_Scan_L (last (Parse_bins_L k)) k)))) (Suc k)"
    using Suc wf_PIL_of_List wf_Parse_close2_L[of "Parse_bins_L k"] wf1_Parse_Scan_L 
        PIL_inv_PIL_of_List[OF forall_from_Suc_parse]
    by (auto simp del: wf_parse_bin1.simps)

  show ?case unfolding wf_parse_bins1_def
  proof
    fix n
    show "n < length (map set (Parse_bins_L (Suc k))) \<longrightarrow> wf_parse_bin1 (map set (Parse_bins_L (Suc k)) ! n) n"
    proof
      assume assm: "n < length (map set (Parse_bins_L (Suc k)))"
      show "wf_parse_bin1 (map set (Parse_bins_L (Suc k)) ! n) n"
      proof (cases "n < Suc k")
        case True
        then show ?thesis using Suc by (auto simp add: nth_append wf_parse_bins1_def Let_def simp del: wf_parse_bin1.simps)
      next
        case False
        then have "n = Suc k" using assm by (auto simp add: Let_def)
        then show ?thesis using 1 by (auto simp add: nth_append Let_def simp del: wf_parse_bin1.simps)
      qed
    qed
  qed
qed

lemma Parse_bins_L_eq_bins_L: "k \<le> length w \<Longrightarrow> map (map item) (Parse_bins_L k) = bins_L k"
proof (induction k)
  case 0
  have "fst (PIL_of_List 0 Parse_Init_L) = IL_of_List 0 Init_L"
    using Parse_Init_L_eq_Init_L by (auto simp add: PIL_of_List_def IL_of_List_def)
  then show ?case using Pclose2_L_eq_close2_L[of "[]" "PIL_of_List 0 Parse_Init_L"] 
      PIL_inv_PIL_of_List[OF forall_from_Suc_parse] wf_PIL_of_List wf1_Parse_Init_L
    by (auto simp add: wf_parse_bins1_def simp del: wf_parse_bin1.simps)
next
  case (Suc k)
  have cons: "Parse_bins_L k \<noteq> []" using length_Parse_bins
    by (metis length_0_conv nat.distinct(1))
  then have last_eq: "map item (last (Parse_bins_L k)) = last (bins_L k)" using Suc
    by (metis Suc_leD last_map)
  have 1: "wf_parse_bins1 (map set (Parse_bins_L k))" using wf_parse_bins_L Suc by auto
  then have "wf_parse_bin1 (set (last (Parse_bins_L k))) k" using Suc cons by (auto simp add: last_conv_nth wf_parse_bins1_def)
  then have wf_Scan: "wf_parse_bin1 (set (Parse_Scan_L (last (Parse_bins_L k)) k)) (Suc k)"
    using wf1_Parse_Scan_L Suc by (auto simp del: wf_parse_bin1.simps)
  let ?pil = "PIL_of_List (Suc k) (Parse_Scan_L (last (Parse_bins_L k)) k)"
  let ?il = "IL_of_List (Suc k) (Scan_L (last (bins_L k)) k)"
  have "fst ?pil = ?il"
    using Parse_Scan_L_eq_Scan_L last_eq by (auto simp add: PIL_of_List_def IL_of_List_def)
  then have "map item (Parse_close2_L (Parse_bins_L k) ?pil) = close2_L (bins_L k) ?il"
    using Suc Pclose2_L_eq_close2_L PIL_inv_PIL_of_List[OF forall_from_Suc_parse] wf_PIL_of_List wf_Scan
    using "1" Suc_leD length_Parse_bins length_PIL_of_List by metis
  then show ?case using Suc 1 by (auto simp add: Let_def length_bins_L)
qed

end

context Earley_Gw_eps
begin

lemma accepted_implies_Some_tree: 
  assumes "accepted" shows "\<exists> t. get_parse_tree (last (Parse_bins_L (length w))) = Some t"
proof-
  obtain s where P_s: "s \<in> (\<S> (length w)) \<and> is_final s" using assms by (auto simp add: accepted_def)
  have cons: "Parse_bins_L (length w) \<noteq> []" using length_Parse_bins
    by (metis length_0_conv nat.distinct(1))
  have "last (map (map item) (Parse_bins_L (length w))) = last (bins_L (length w))"
    using Parse_bins_L_eq_bins_L by auto
  then have "set (map item (last (Parse_bins_L (length w)))) = set (last (bins_L (length w)))"
    using cons by (auto simp add: last_map)
  then have "set (map item (last (Parse_bins_L (length w)))) = \<S> (length w)" 
    using bins_L_eq_\<S> length_bins_L last_conv_nth
    by (metis bins_L_eq_bins bins_nonempty diff_Suc_1 list.simps(8) nat_le_linear)
  then obtain t where "(s,t) \<in> set (last (Parse_bins_L (length w)))" using P_s by fastforce
  then obtain s1 t1 where P_s1t1: "(s1, t1) \<in> set (last (Parse_bins_L (length w)))
    \<and> is_final s1 
    \<and> get_parse_tree (last (Parse_bins_L (length w))) = Some (Rule S (rev t1))"
    using get_parse_tree_NF[of "(s,t)" "last (Parse_bins_L (length w))"] P_s by auto
  then show ?thesis by auto
qed

lemma get_parse_tree_Some_t_decomp: "get_parse_tree xs = Some t \<Longrightarrow> \<exists>s ts. (s,ts) \<in> set xs \<and> is_final s \<and> t = (Rule S (rev ts))"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
    by (metis get_parse_tree.simps(2) list.set_intros(1,2) option.inject surjective_pairing)
qed

theorem generated_parse_tree_is_valid: "get_parse_tree (last (Parse_bins_L (length w))) = Some t \<longrightarrow> valid_parse_tree P w S t"
proof
  assume "get_parse_tree (last (Parse_bins_L (length w))) = Some t"
  then obtain s ts where P_t: "(s,ts) \<in> set (last (Parse_bins_L (length w))) \<and> is_final s \<and> t = (Rule S (rev ts))" 
    using get_parse_tree_Some_t_decomp by blast
  moreover have "Parse_bins_L (length w) \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_Parse_bins)
  ultimately have "wf_item_Pt1 (s, ts) (length w)" using wf_parse_bins_L 
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_item_Pt1.simps)
  then show "valid_parse_tree P w S t" using P_t 
    by (auto simp add: valid_parse_tree_def is_final_def wf_item1_def wf_item_def \<alpha>_def rhs_def is_complete_def)
qed

theorem find_parse_tree_iff_w_in_L: "(\<exists>t. get_parse_tree (last (Parse_bins_L (length w))) = Some t) \<longleftrightarrow> w0 \<in> Lang P S"
proof
  assume "\<exists>t. get_parse_tree (last (Parse_bins_L (length w))) = Some t"
  then obtain t where "get_parse_tree (last (Parse_bins_L (length w))) = Some t" by blast
  then have "valid_parse_tree P w S t" using generated_parse_tree_is_valid by blast
  then have "P \<turnstile> [Nt S] \<Rightarrow>* w" using fringe_steps_if_parse_tree[of P t] by (auto simp add: valid_parse_tree_def)
  then show "w0 \<in> lang ps S" by (auto simp add: w_def Lang_def)
next
  assume "w0 \<in> lang ps S"
  then have "recognized Earley" using correctness_Earley by (auto simp add: Lang_def w_def)
  then obtain x where "is_final x \<and> (x, length w) \<in> Earley" using recognized_def by blast
  then have "x \<in> \<S> (length w) \<and> is_final x"
    by (simp add: Earley_eq_\<S>) 
  then have "accepted"
    using accepted_def by blast
  then show "\<exists>t. get_parse_tree (last (Parse_bins_L (length w))) = Some t"
    using accepted_implies_Some_tree by auto
qed


corollary unambiguous_impl_the_parse_tree: 
  assumes "unambiguous (Cfg P S)" shows "valid_parse_tree P w S t \<longrightarrow> get_parse_tree (last (Parse_bins_L (length w))) = Some t"
proof
  assume valid: "valid_parse_tree P w S t"
  then have "P \<turnstile> [Nt S] \<Rightarrow>* w"
    using valid_parse_tree_iff_derived by auto
  then have w0_in_L: "w0 \<in> Lang P S" by (auto simp add: Lang_def w_def)
  then obtain t1 where P_t1: "get_parse_tree (last (Parse_bins_L (length w))) = Some t1"
    using find_parse_tree_iff_w_in_L by blast
  then have "valid_parse_tree P w S t1"
    by (simp add: generated_parse_tree_is_valid)
  then have "t1 = t" using assms valid w0_in_L by (auto simp add: unambiguous_def w_def)
  then show "get_parse_tree (last (Parse_bins_L (length w))) = Some t" using P_t1 by auto
qed

end

section \<open>Running time analysis of list based earley parser\<close>

subsection \<open>Time_fun defs and simple bounds\<close>



context Earley_Gw_eps_T
begin
time_fun empty_PIL
time_fun parseIL_insert
time_fun union_LPIL
time_fun parseIL_isin
time_fun minus_LPIL
time_fun PIL_list
time_fun minus_PIL
time_fun PIL_of_List
time_fun PIL_first

time_fun Parse_Complete_L
time_fun Parse_Scan_L
time_fun Parse_Predict_L
time_fun Parse_step_fun

lemma T_rev_tree: 
  assumes "wf_item_Pt item_Pt k" shows "T_rev (tree item_Pt) \<le> 2 * K * K + 1" 
proof-
  obtain lh rh d T_nth_IL t where P: "item_Pt = (Item (lh, rh) d T_nth_IL, t)"
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

lemma [simp]: "inv_PIL pil \<Longrightarrow> T_PIL_list pil = (length (snd pil)) + 1"
  using T_zip by (cases pil) auto

lemma [simp]: 
  assumes "snd pil \<noteq> []" "inv_PIL pil" shows "T_PIL_first pil = 0"
proof-
  obtain as m b bs where P1: "pil = (ItemList as m, (b#bs))"
    using assms by (metis T_last.cases set_parseIL.cases snd_conv il_decomp)
  then have "as \<noteq> []" using assms by auto
  then obtain a ass where "as = a#ass"
    by (meson recognized_L.cases)
  then show ?thesis using P1 by auto
qed

(*assumes that the stop condition check takes 0 time*)
fun parse_steps_time :: "('a, 'b) item_Pt list list \<Rightarrow> ('a, 'b) parseIL \<times> ('a, 'b) parseIL \<Rightarrow> nat \<Rightarrow> ((('a, 'b) parseIL \<times> ('a, 'b) parseIL) \<times> nat) option" where
"parse_steps_time Bs ils y = while_option (\<lambda>((B,C),k). PIL_map_item B \<noteq> []) (\<lambda>((B,C),k). (Parse_step_fun Bs (B,C), k + T_Parse_step_fun Bs (B,C))) (ils, y)"

fun T_Parse_steps :: "('a, 'b) item_Pt list list \<Rightarrow> ('a, 'b) parseIL \<times> ('a, 'b) parseIL \<Rightarrow> nat" where
"T_Parse_steps Bs ils = snd (the (parse_steps_time Bs ils 0))"


time_fun Parse_close2_L
time_fun Parse_bins_L

subsection \<open>ParseItemList time bounds\<close>

lemma PIL_T_insert_simp: "T_parseIL_insert x pil \<le> T_isin (fst pil) (fst x) + T_insert (fst x) (fst pil)"
  by (cases pil, cases x) simp

corollary PIL_T_insert_bound: "distinct ps \<Longrightarrow> inv_IL (fst pil) \<Longrightarrow> wf1_IL (fst pil) k \<Longrightarrow> from (fst x) <  length (froms (fst pil)) 
  \<Longrightarrow> T_parseIL_insert x pil \<le> 4 * T_nth_IL (from (fst x)) + 2* L * Suc K + 2"
  using T_isin_wf[of "fst pil" k "fst x"] T_insert_less[of "fst pil" k  "fst x"] PIL_T_insert_simp[of x pil]
  by auto

lemma T_union_LPIL_bound: "distinct ps \<Longrightarrow> inv_PIL pil \<Longrightarrow> wf_parse_bin1 (set xs) (length (froms (fst pil)) - 1) \<Longrightarrow> wf_PIL pil (length (froms (fst pil)) - 1)
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
    using forall_from_Suc_parse[OF Cons(4)] by (cases "fst pil") (auto simp del: wf_parse_bin1.simps)
  then have 2: "inv_IL (union_LIL (map item xs) (fst pil))"
    using LIL_union_inv Cons(3) by (cases pil) auto

  have a_le_leng: "from (fst a) < length (froms (fst pil))" 
    using forall_from_Suc_parse[OF Cons(4)] 1 by (cases "fst pil") (auto simp del: wf_parse_bin1.simps)
  then have 4: "from (fst a) \<le> length (froms (fst pil)) - 1" by auto
  
  have "wf1_IL (fst pil) (length (froms (fst pil)) - 1)" using Cons wf_PIL_impl_wf1_IL[of pil "length (froms (fst pil)) - 1"] by auto
  then have 3: "wf_bin1 (set (list (union_LIL (map item xs) (fst pil)))) (length (froms (fst pil)) - 1)" 
    using 1 Cons from_xs wf1_IL_union_LIL[of "fst pil" "length (froms (fst pil)) - 1" "map item xs"] 
    by (auto simp add: wf_bin1_def)
  from 2 3 have "T_parseIL_insert a (union_LPIL xs pil) \<le> 4 * T_nth_IL (from (fst a)) + 2* L * Suc K + 2"
    using "Cons.prems"(1) PIL_T_insert_bound[of "(union_LPIL xs pil)" "length (froms (fst pil)) - 1" a]
    a_le_leng by (auto simp add: wf_item1_def wf_item_def)
  then have "T_parseIL_insert a (union_LPIL xs pil) \<le> 4 * T_nth_IL (length (froms (fst pil)) - 1) + 2* L * Suc K + 2"
    using mono_nth 4 monoD[of T_nth_IL "from (fst a)" "length (froms (fst pil)) - 1"] by (auto simp add: algebra_simps)
  then show ?case using ih by (auto simp add: algebra_simps)
qed

lemma T_minus_LPIL_bound: "distinct ps \<Longrightarrow> inv_PIL pil \<Longrightarrow> wf_parse_bin1 (set xs) k \<Longrightarrow> wf_PIL pil k
  \<Longrightarrow> length (froms (fst pil)) \<ge> Suc k
 \<Longrightarrow> T_minus_LPIL k xs pil \<le> length xs * (5 * T_nth_IL k + 3 * L * Suc K + 3) + length xs + k + 3"
proof(induction k xs pil rule: T_minus_LPIL.induct)
  case (1 k pil)
  then show ?case by simp
next
  case (2 k a as pil)
  then have ih: "T_minus_LPIL k as pil \<le> length as * (5 * T_nth_IL k + 3 * L * Suc K + 3) + length as + k + 3"
    by auto

  from 2 have 3: "inv_IL (fst pil)" by (cases pil) auto
  have 4: "inv_IL (minus_LIL k (map item as) (fst pil))"
    using LIL_minus_inv forall_from_Suc_parse "2"(5) by auto

  have a_le_k: "from (fst a) \<le> k" using 2 by (auto simp add: wf_item1_def wf_item_def)
  have from_l: "\<forall>a\<in>set (map item as). from a < Suc k" using forall_from_Suc_parse "2"(5) by auto
  
  have "wf1_IL (fst pil) k" using 2 wf_PIL_impl_wf1_IL[of pil k] by auto
  then have 5: "wf_bin1 (set (list (minus_LIL k (map item as) (fst pil)))) k" 
    using 2 3 from_l wf1_IL_minus_LIL[of "fst pil" "map item as" k k] by (auto simp add: wf_bin1_def)
  have 6: "from (item a) < (length (froms (minus_LIL k (map item as) (fst pil))))" 
    using 2 le_imp_less_Suc 
    by (auto simp add: wf_item1_def wf_item_def)

  from 4 5 6 have "T_parseIL_insert a (minus_LPIL k as pil) \<le> 4 * T_nth_IL (from (fst a)) + 2* L * Suc K + 2"
    using "2.prems"(1) PIL_T_insert_bound[of "(minus_LPIL k as pil)" k a] 
    by (auto simp add: wf_item1_def wf_item_def)
  then have 7: "T_parseIL_insert a (minus_LPIL k as pil) \<le> 4 * T_nth_IL k + 2* L * Suc K + 2"
    using mono_nth a_le_k monoD[of T_nth_IL "from (fst a)" k] by (auto simp add: algebra_simps)

  have "T_isin (fst pil) (fst a) \<le> T_nth_IL (from (fst a)) + L * Suc K + 1"
    using T_isin_wf
    using "2.prems"(1,5) "3" \<open>wf1_IL (fst pil) k\<close> a_le_k by auto
  then have "T_parseIL_isin pil a \<le> T_nth_IL (from (fst a)) + L * Suc K + 1" by (cases pil, cases a) auto
  then have "T_parseIL_isin pil a \<le> T_nth_IL k + L * Suc K + 1" 
    using mono_nth a_le_k monoD[of T_nth_IL "from (fst a)" k] by (auto simp add: algebra_simps)


  then show ?case using ih 7 by (auto simp add: algebra_simps)
qed

lemma T_minus_PIL_bound: 
  assumes "distinct ps" "inv_PIL pil1" "inv_PIL pil2" "wf_PIL pil1 (length (froms (fst pil1)) - 1)" 
    "wf_PIL pil2 (length (froms (fst pil1)) - 1)" "length (froms (fst pil1)) \<le> length (froms (fst pil2))"
  shows "T_minus_PIL pil1 pil2 \<le> length (snd pil1) * (5 * T_nth_IL (length (froms (fst pil1)) - 1) + 3 * L * Suc K + 3) + 2 * length (snd pil1) + 2 * (length (froms (fst pil1))) + 4"
proof-
  have 1: "length (froms (fst pil1)) > 0" using assms(2) by (cases pil1, cases "fst pil1") auto

  have "T_PIL_list pil1 = length (snd pil1) + 1" using assms by auto

  moreover have "T_minus_LPIL (length (froms (fst pil1)) - 1) (PIL_list pil1) pil2 
    \<le> length (PIL_list pil1) * (5 * T_nth_IL (length (froms (fst pil1)) - 1) + 3 * L * Suc K + 3) + length (PIL_list pil1) + (length (froms (fst pil1)) - 1) + 3" 
    using assms 1 T_minus_LPIL_bound[of pil2 "PIL_list pil1" "length (froms (fst pil1)) - 1"] wf_PIL_impl_wf1_IL by auto
  moreover have "length (PIL_list pil1) = length (snd pil1)" using assms by (cases pil1) auto
  ultimately show ?thesis using 1 by (auto simp add: algebra_simps T_length)
qed

lemma T_PIL_of_List_bound: 
  assumes "distinct ps" "wf_parse_bin1 (set xs) k"
  shows "T_PIL_of_List k xs \<le> length xs * (4 * T_nth_IL k + 2* L * Suc K + 2) + length xs + k + 3"
proof-
  have "inv_PIL (empty_PIL k)" and "wf_PIL (empty_PIL k) k"
    using wf_empty_PIL by (auto simp add: PIL_inv_empty)
  then have "T_union_LPIL xs (empty_PIL k) \<le> length xs * (4 * T_nth_IL k + 2* L * Suc K + 2) + length xs + 1"
    using T_union_LPIL_bound[of "empty_PIL k"] assms by auto
  then show ?thesis by auto
qed

subsection \<open>Earley parser time bounds\<close>

lemma T_Parse_Complete_L_bound: 
  assumes "wf_parse_bins1 (map set Bs)" "from (item item_Pt) < length Bs" "wf_item_Pt item_Pt (length Bs)" "length (Bs ! from (item item_Pt)) \<le> C"
  shows "T_Parse_Complete_L Bs item_Pt \<le> length Bs +  (2 * K * K + 2 * K + 5) * C + 2"
proof-
  let ?from_list = "Bs ! from (item item_Pt)"
  let ?T_filt = "\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> T_next_symbol p + (T_fst item_Pt + T_prod (item item_Pt) + T_fst (item.prod (item item_Pt)))"
  let ?filtered = "filter (\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> next_sym_Nt p (lhs (item.prod (item item_Pt)))) (Bs ! from (item item_Pt))"
  let ?T_Pred = "\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> T_mv_dot p + (T_fst item_Pt + T_prod (item item_Pt) + T_fst (item.prod (item item_Pt)) + (T_snd item_Pt + T_rev (tree item_Pt)))"
  have "\<forall>x \<in> set (Bs ! from (item item_Pt)). ?T_filt x \<le> 2 * Suc K" 
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

  have "T_nth Bs (from (item item_Pt)) \<le> length Bs" 
    using assms T_nth[of "from (item item_Pt)" Bs] by auto

  then show ?thesis using 1 2 by (auto simp add: algebra_simps)
qed

lemma T_Parse_Scan_L_bound: 
  assumes "k < length w" "wf_parse_bin (set Bs) k" 
  shows "T_Parse_Scan_L Bs k \<le> k + (2*K + 4) * (length Bs) + 3"
proof-
  have 1: "T_nth w k = k + 1" using assms by (auto simp add: T_nth)

  let ?T_filt = "\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_next_symbol p"
  have "\<forall>x \<in> set Bs. ?T_filt x \<le> 2 * Suc K" 
    using assms T_next_symbol_bound by (fastforce simp add: wf_item_def)
  then have 2: "T_filter ?T_filt Bs \<le> 2 * Suc K * (length Bs) + length Bs + 1"
    using T_filter_bound[of Bs ?T_filt "2 * Suc K"] by simp

  let ?filtered = "filter (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> next_symbol p = Some (w ! k)) Bs"
  let ?T_map = "\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p + T_the (Some (w ! k))"
  have "T_map (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p + T_the (Some (w ! k))) ?filtered
  = T_map (\<lambda>y. 0) ?filtered" by auto
  also have "... \<le> length ?filtered + 1" using T_map_bound by fastforce
  also have "... \<le> length Bs + 1" by auto
  finally have "T_map (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p + T_the (Some (w ! k))) ?filtered \<le> length Bs + 1".

  then show ?thesis using 1 2 by (auto simp add: algebra_simps)
qed

lemma T_Parse_Predict_L_bound: 
  assumes "prod x \<in> P" shows "T_Parse_Predict_L x k \<le> 2 * Suc K * L + 2*L + 2"
proof-
  have "T_filter (\<lambda>p. T_next_symbol x + T_fst p) ps \<le> 2 * Suc K * L + L + 1"
    using assms T_next_symbol_bound T_filter_bound[of ps "\<lambda>p. T_next_symbol x + T_fst p" "2 * Suc K"] 
    by (auto simp add: L_def)
  moreover have "T_map (\<lambda>p. 0) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps) \<le> L + 1"
    using T_map_bound[of "filter (\<lambda>p. next_sym_Nt x (lhs p)) ps" "\<lambda>p. 0" 0]
    by (metis (no_types, lifting) L_def add_le_mono dual_order.trans lambda_zero le_refl length_filter_le plus_nat.add_0)
  ultimately show ?thesis by (auto simp add: algebra_simps)
qed


lemma [simp]: 
  assumes "inv_PIL (il, t#ts)" shows "T_PIL_first (il, t#ts) = 0"
proof-
  from assms have "list il \<noteq> []" by auto
  then obtain x xs m where "il = ItemList (x#xs) m"
    by (metis efficientItemList.sel(1) il_decomp recognized_L.cases)    
  then show ?thesis by auto
qed

lemma parse_complete_length: "length (Parse_Complete_L Bs item_Pt) \<le> length (Bs ! from (item item_Pt))"
  by (auto simp add: Parse_Complete_L_def)

lemma parse_predict_length: "length (Parse_Predict_L s n) \<le> L"
  by (auto simp add: Parse_Predict_L_def L_def)

lemma T_parse_step_fun_bound: 
  assumes cons: "PIL_map_item pil1 \<noteq> []"
  and dist: "distinct ps"
  and invs: "inv_PIL pil1" "inv_PIL pil2"
  and lengs: "length (froms (fst pil1)) =  Suc (length Bs)" "length (froms (fst pil2)) =  Suc (length Bs)"
  and wf1: "wf_parse_bin1 (set_parseIL pil1) (length Bs)" "wf_parse_bin1 (set_parseIL pil2) (length Bs)" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
shows "T_Parse_step_fun Bs (pil1,pil2) 
    \<le> (2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12"
proof-
  from cons invs obtain x xs m t ts where P_pil1: "pil1 = (ItemList (x#xs) m, (t#ts))"
    by (metis PIL_map_item_Cons1 PIL_map_item_Cons2 prod.collapse recognized_L.cases)
  obtain il2 ts2 where P_pil2: "pil2 = (il2, ts2)"
    using set_parseIL.cases by blast
  let ?b = "PIL_first (ItemList (x#xs) m, (t#ts))"
  have b_simp: "?b = (x,t)" by simp

  have wf1_b: "wf_item_Pt1 ?b (length Bs)" using wf1 PIL_first_in_set_PIL P_pil1 by auto
  then have 1: "T_is_complete (item ?b) \<le> K + 1" using T_is_complete_bound prod_length_bound P_pil1 
    by (auto simp add: wf_item1_def wf_item_def)

  have 2: "is_complete (item ?b) \<longrightarrow> T_Parse_Complete_L Bs ?b \<le> length Bs +  (2 * K * K + 2 * K + 5) * C + 2"
    using wf1 wf1_b max_bin_size T_Parse_Complete_L_bound[of Bs ?b C] by (auto simp add: wf_item1_def)

  moreover have "T_Parse_Predict_L (item ?b) (length Bs) \<le> 2 * Suc K * L + 2 * L + 2" 
    using wf1_b T_Parse_Predict_L_bound by (simp add: wf_item1_def wf_item_def)
  ultimately have 3: "(if is_complete (item ?b) then T_Parse_Complete_L Bs ?b 
    else T_fst ?b + (T_length Bs + T_Parse_Predict_L (item ?b) (length Bs)))
    \<le> length Bs + (2 * K * K + 2 * K + 5) * C + 2 * Suc K * L + 2 * L + 3"  
    by (auto simp add: T_length algebra_simps)

  let ?step = "if is_complete (item ?b) then Parse_Complete_L Bs ?b else Parse_Predict_L (item ?b) (length Bs)"
  have length_step: "length ?step \<le> max C L" 
    using parse_complete_length[of Bs "(x,t)"] parse_predict_length[of x "length Bs"] max_bin_size wf1_b 
    by (auto simp add: wf_item1_def)
  have wf_step: "wf_parse_bin1 (set ?step) (length Bs)"
    using wf1(3) wf1_Parse_Complete_L wf1_Parse_Predict_L wf1_b by presburger  
  then have "T_union_LPIL ?step pil1 \<le> length ?step * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + length ?step + 1"
    using T_union_LPIL_bound[of pil1 ?step] dist invs wf1 by (auto simp add: lengs simp del: wf_parse_bin1.simps)
  also have "... \<le> (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1"
    using length_step using mult_le_mono1[of "length ?step" "max C L"]
    by (meson add_le_mono le_numeral_extra(4))
  finally have 4: "T_union_LPIL ?step pil1 \<le> (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1".

  have from_b: "from (item ?b) < (length (froms il2))" using lengs wf1_b P_pil2 by (auto simp add: wf_item1_def wf_item_def)
  then have "T_parseIL_insert ?b pil2 \<le> 4 * T_nth_IL (from (item ?b)) + 2 * L * Suc K + 2"
    using PIL_T_insert_bound[of pil2 "length Bs" ?b] dist invs wf1 P_pil2 wf_PIL_impl_wf1_IL by auto
  also have "... \<le> 4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2" using mono_nth wf1_b 
    by (auto simp add: monoD wf_item1_def wf_item_def)
  finally have 5: "T_parseIL_insert ?b pil2 \<le> 4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2".
  
  have wf_PIL_union: "wf_PIL (union_LPIL ?step pil1) (length Bs)" 
    using wf1(1) wf_step wf_union_LPIL[of pil1 "length Bs" ?step] by simp
  moreover have inv_union: "inv_PIL (union_LPIL ?step pil1)" using PIL_inv_union_LPIL invs(1) 
    using forall_from_Suc_parse lengs(1) wf_step by auto 
  ultimately have length_snd_union: "length (snd(union_LPIL ?step pil1)) \<le> L * Suc K * Suc (length Bs)" 
    using length_snd_PIL[of "union_LPIL ?step pil1" "length Bs"] by simp

  have wf_PIL_insert: "wf_PIL (parseIL_insert ?b pil2) (length Bs)" 
    using wf_PIL_insert[of pil2 "length Bs" ?b] wf1(2) wf1_b by fastforce
  have inv_insert: "inv_PIL (parseIL_insert ?b pil2)" 
    using PIL_inv_insert[of pil2 ?b] invs(2) from_b P_pil2 by auto
  let ?length_list = "length (snd (union_LPIL ?step pil1))"
  let ?leng_il = "length (froms (fst (union_LPIL ?step pil1))) - 1"
  have "T_minus_PIL (union_LPIL ?step pil1) (parseIL_insert ?b pil2)
    \<le>?length_list * (5 * T_nth_IL (?leng_il) + 3 * L * Suc K + 3) + 2 * ?length_list + 2*?leng_il + 6" 
    using T_minus_PIL_bound[of "union_LPIL ?step pil1" "parseIL_insert ?b pil2"]
      wf_PIL_union inv_union wf_PIL_insert inv_insert dist length_union_LPIL[of ?step pil1] length_insert_parse[of ?b pil1] lengs
    wf_step by auto
  also have "... \<le> L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + 2*length Bs + 6"
    using mult_le_mono1[of ?length_list "L * Suc K * Suc (length Bs)" "(5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3)"] 
      mult_le_mono2[of ?length_list "L * Suc K * Suc (length Bs)" 2] 
      wf_step length_union_LPIL[of ?step pil1] add_mult_distrib lengs(1) length_snd_union by auto
  finally have 6: "T_minus_PIL (union_LPIL ?step pil1) (parseIL_insert ?b pil2) \<le>
    L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + 2*length Bs + 6".

  have "T_Parse_step_fun Bs (pil1,pil2) \<le> 
    T_is_complete (item ?b)
    + (if is_complete (item ?b) then T_Parse_Complete_L Bs ?b else T_fst ?b + (T_length Bs + T_Parse_Predict_L (item ?b) (length Bs)))
    + T_union_LPIL ?step pil1
    + 2 * T_parseIL_insert ?b pil2
    + T_minus_PIL (union_LPIL ?step pil1) (parseIL_insert ?b pil2)"
    using P_pil1 by (auto simp add: Let_def)
  also have "... \<le> K + 1 + length Bs + (2 * K * K + 2 * K + 5) * C + 2 * Suc K * L + 2 * L + 3 
    + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1
    + 2 * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 2)
    + L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + 2*length Bs + 6"
    using 1 3 4 5 6 by (auto simp only: algebra_simps)
  also have "... = 3 * length Bs + K + 15 + 6 * Suc K * L + 2 * L + (2 * K * K + 2 * K + 5) * C 
    + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3) + 8 * T_nth_IL (length Bs)
    + L * Suc K * Suc (length Bs) * (5 * T_nth_IL (length Bs) + 3 * L * Suc K + 5)"
    by (auto simp add: algebra_simps)
  also have "... \<le>  (2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12"
    by (auto simp add: algebra_simps)
  finally show ?thesis.
qed

lemma Parse_step_fun_set_inc:
  assumes "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4)" "PIL_map_item pil1 \<noteq> []" "inv_PIL pil1" "inv_PIL pil2"
          "set (PIL_map_item pil1) \<inter> set (PIL_map_item pil2) = {}" "length (froms (fst pil2)) \<ge> length (froms (fst pil1))"
  shows "length (PIL_map_item pil4) = Suc (length (PIL_map_item pil2))"
proof-
  from assms(2,3) obtain x xs m t ts  ys m2 ts2 where "pil1 = (ItemList (x#xs) m, t#ts)" 
      and "pil2 = (ItemList ys m2, ts2)"
    using PIL_map_item_def PIL_map_item_Cons2
    by (metis efficientItemList.sel(1) T_size_list.cases surjective_pairing il_decomp)
  then show ?thesis using assms by (auto simp add: Let_def PIL_map_item_def isin_list)
qed

lemma Parse_step_fun_dist_sets:
  assumes "Parse_step_fun Bs (pil1, pil2) = (pil3, pil4 )" "PIL_map_item pil1 \<noteq> []" "inv_PIL pil1" "inv_PIL pil2"
    "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)" "wf_parse_bins1 (map set Bs)"
    "wf_PIL pil1 (length Bs)"
  shows "set (PIL_map_item pil3) \<inter> set (PIL_map_item pil4) = {}"
proof-
  
  from assms(2,3) obtain x xs m t ts  il2 ts2 where P_il1: "pil1 = (ItemList (x#xs) m, t#ts)" 
      and P_il2: "pil2 = (il2, ts2)"
    using PIL_map_item_def PIL_map_item_Cons2
    by (metis efficientItemList.sel(1) T_size_list.cases surjective_pairing il_decomp)
  let ?step = "if is_complete x then Parse_Complete_L Bs (x,t) else Parse_Predict_L x (length Bs)"
  let ?step1 = "if is_complete x then Complete_L (map (map item) Bs) x else Predict_L x (length Bs)"

  have 3: "from x \<le> length Bs" using assms(8) P_il1 by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  have "wf_item_Pt1 (x,t) (length Bs)" using assms(8) P_il1 by auto
  then have wf: "wf_parse_bin1 (set ?step) (length Bs)" 
    using assms wf1_Parse_Complete_L wf1_Parse_Predict_L
    by (smt (verit) fst_conv)
  have steps_eq: "?step1 = map item ?step" 
    using PPredict_L_eq_Predict_L PComplete_L_eq_Complete_L assms(8) P_il1 
    by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have wf1: "wf_bin1 (set ?step1) (length Bs)" using wf by (auto simp add: wf_bin1_def)

  have 2: "\<forall>x\<in>set ?step. from (item x) < length (froms (fst pil1))" 
    using wf forall_from_Suc_parse assms(5) by auto
  have 4: "\<forall>x \<in> set ?step1. from x < length (froms (fst pil1))" 
    using wf1 forall_from_Suc assms(5) by auto
  
  have 1: "inv_PIL (union_LPIL ?step pil1)"
    using PIL_inv_union_LPIL 2 assms(3) by blast

  have "set (PIL_map_item pil3) = set (list (minus_IL (union_LIL (map item ?step) (fst pil1)) (insert x (fst pil2))))"
    using assms 1 P_il1 by (auto simp add: Let_def PIL_map_item_def)
  also have "... = set (list (minus_IL (union_LIL ?step1 (fst pil1)) (insert x (fst pil2))))"
    using steps_eq by auto
  finally have "set (PIL_map_item pil3) = set (list (minus_IL (union_LIL ?step1 (fst pil1)) (insert x (fst pil2))))".
  moreover have "set (PIL_map_item pil4) = set (list (insert x (fst pil2)))"
    using assms P_il1 3 by (auto simp add: Let_def PIL_map_item_def)
  ultimately show "set (PIL_map_item pil3) \<inter> set (PIL_map_item pil4) = {}"
    using IL_minus[of "insert x (fst pil2)" "union_LIL ?step1 (fst pil1)"] assms 
        LIL_union_inv[OF _ 4] insert_inv_IL1 3 P_il1 P_il2 by auto
qed

lemma parse_steps_time_bound:
  assumes k_bound:"k \<le> length (PIL_map_item pil2) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)" 
  and res: "parse_steps_time Bs (pil1, pil2) k = Some ((pil3, pil4), k1)"
  and dist: "distinct ps"
  and invs: "inv_PIL pil1" "inv_PIL pil2"
  and lengs: "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)"
  and wf1: "wf_PIL pil1 (length Bs)" "wf_PIL pil2 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and distinct: "set (PIL_map_item pil1) \<inter> set (PIL_map_item pil2) = {}" 
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
  shows "k1 \<le> length (PIL_map_item pil4) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)"
proof-
  let ?C = "(2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12"
  let ?P3 = "\<lambda>((pil1',pil2'),k). wf_PIL pil1' (length Bs) \<and> wf_PIL pil2' (length Bs) \<and> wf_parse_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((pil1',pil2'),k). wf_PIL pil1' (length Bs) \<and> wf_PIL pil2' (length Bs) \<and> wf_parse_bins1 (map set Bs) \<and> inv_PIL pil1' \<and> inv_PIL pil2' 
        \<and> length (froms (fst pil1')) = Suc (length Bs) \<and> length (froms (fst pil2')) = Suc (length Bs) \<and> (\<forall>i < length Bs. length (Bs ! i) \<le> C) \<and> distinct ps 
        \<and> set (PIL_map_item pil1') \<inter> set (PIL_map_item pil2') = {}" 
  let ?P2 = "\<lambda>((pil1',pil2'),k). k \<le> length (PIL_map_item pil2') * (?C)"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((pil1,pil2),k). PIL_map_item pil1 \<noteq> [])"
  let ?c = "\<lambda>((pil1,pil2),k). (Parse_step_fun Bs (pil1,pil2), k + T_Parse_step_fun Bs (pil1,pil2))"


  have init: "?P ((pil1,pil2), k)" using assms by auto

  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y
    using PIL_inv_parse_step1' PIL_inv_parse_step2' wf_parse_step2' wf_parse_step1' length_parse_step1' 
      length_parse_step2' Parse_step_fun_dist_sets
    by (smt (verit) case_prodI2' case_prod_conv)
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_Parse_step_fun Bs (a, b) \<le> ?C" using T_parse_step_fun_bound[of a b Bs C] by auto
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "Parse_step_fun Bs (a,b) = (a', b')" by auto
    then have "length (PIL_map_item b') = Suc (length (PIL_map_item b))" 
      using Parse_step_fun_set_inc  assms by auto
    then have 2: "length (PIL_map_item b') * ?C = length (PIL_map_item b) * ?C + ?C"
      by (metis add.commute mult_Suc)
    have "y' \<le> y + ?C" using P1 1 by auto
    also have "... \<le> length (PIL_map_item b) * ?C + ?C" 
      using assms by (auto simp add: add_mult_distrib2)
    also have "... = length (PIL_map_item b') * ?C" using 2 by auto
    finally have "y' \<le> length (PIL_map_item b') * ?C".
    then show "?P2 (?c ((a,b), y))" using P1
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
  qed

  then have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P (?c ((a,b), y)))" for a b y using P1 by auto
  then have "?P ((pil3,pil4), k1)"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((pil1,pil2),k)", where t="((pil3,pil4), k1)"] res init unfolding parse_steps_time.simps
    by (auto simp only:)
  then show "k1 \<le> (length (PIL_map_item pil4)) * ?C"
    by auto
qed

theorem Parse_steps_time_NF: "wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PIL pil1 (length Bs) \<Longrightarrow> wf_PIL pil2 (length Bs) 
  \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> inv_PIL pil2 \<Longrightarrow> length (froms (fst pil1)) = Suc (length Bs) \<Longrightarrow> length (froms (fst pil2)) = Suc (length Bs)
  \<Longrightarrow> \<exists>pil1' pil2' k'. parse_steps_time Bs (pil1, pil2) k = Some ((pil1', pil2'), k') \<and> Parse_steps Bs (pil1, pil2) = Some (pil1', pil2')" 
using wf_step_fun_less[of "length Bs"]
proof (induction "(fst pil1,fst pil2)" arbitrary: pil1 pil2 k rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "list (fst pil1) = []"
    thus ?thesis by (simp add: while_option_unfold Parse_steps_def PIL_map_item_def)
  next
    let ?steps = "while_option (\<lambda>(as,bs). PIL_map_item as \<noteq> []) (Parse_step_fun Bs)"
    assume cons: "list (fst pil1) \<noteq> []"
    then obtain il1 t ts where P_pil1: "pil1 = (il1, t#ts)" using less.prems(4)
      by (metis PIL_map_item_Cons2 PIL_map_item_def list.exhaust surjective_pairing)
    then obtain pil1' pil2'
      where P_step: "(pil1',pil2') = Parse_step_fun Bs (pil1,pil2)"
      by (metis T_fst.cases)
    then have wf_inv: "wf_PIL pil1' (length Bs)" "wf_PIL pil2' (length Bs)" "inv_PIL pil1'" 
      "inv_PIL pil2'" "length (froms (fst pil1')) = Suc (length Bs)" "length (froms (fst pil2')) = Suc (length Bs)"
      using wf_parse_step1 wf_parse_step2 PIL_inv_parse_step1 PIL_inv_parse_step2 length_parse_step1 length_parse_step2 less.prems P_pil1
      by (metis, metis, metis, metis, metis, metis)
      
    from P_step have step_f: "(fst pil1',fst pil2') = step_fun (map (map item) Bs) (fst pil1, fst pil2)"
      using less.prems Pstep_fun_eq_step_fun1[of pil1 Bs pil2 pil1' pil2'] cons unfolding PIL_map_item_def by (auto simp add: Let_def)
    have "wf1_IL (fst pil1) (length Bs) \<and> wf1_IL (fst pil2) (length Bs)"
      using less.prems wf_PIL_impl_wf1_IL by (cases pil1, cases pil2) (auto simp del: wf_PIL.simps inv_PIL.simps)
    then have "((fst pil1',fst pil2'), (fst pil1, fst pil2)) \<in> step_fun_less (length Bs)" 
      using less.prems step_fun_less_step[of "fst pil1" "(map (map item) Bs)" "fst pil2"] \<open>list (fst pil1) \<noteq> []\<close> step_f 
      by (cases pil1, cases pil2) (auto simp add: wf_parse_bins1_def wf_bins1_def wf_bin1_def)
    from less.hyps[OF this \<open>wf_parse_bins1 (map set Bs)\<close> wf_inv]
    show ?thesis
      by (simp add: P_step while_option_unfold Parse_steps_def)
  qed
qed

lemma T_Parse_steps_bound: 
  assumes dist: "distinct ps"
  and length_pil2: "length (PIL_map_item pil2) = 0"
  and invs: "inv_PIL pil1" "inv_PIL pil2"
  and lengs: "length(froms  (fst pil1)) = Suc (length Bs)" "length(froms  (fst pil2)) = Suc (length Bs)"
  and wf1: "wf_PIL pil1 (length Bs)" "wf_PIL pil2 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
  shows "T_Parse_steps Bs (pil1, pil2) \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)"
proof-
  obtain pil3 pil4 k where Psteps_time: "parse_steps_time Bs (pil1, pil2) 0 = Some ((pil3, pil4), k)" 
    and Psteps: "Parse_steps Bs (pil1, pil2) = Some (pil3, pil4)"
    using assms Parse_steps_time_NF
    by blast
  have "wf_PIL pil4 (length Bs)" using Psteps Parse_steps_wf2 wf1 invs lengs by blast
  then have length_bound: "length (PIL_map_item pil4) \<le> L * Suc K * Suc (length Bs)" 
    using length_fst_PIL Parse_steps_inv2 invs Psteps lengs
    by (metis PIL_map_item_def wf1(1,3))
  have "T_Parse_steps Bs (pil1, pil2) \<le> length (PIL_map_item pil4) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)"
    using assms Psteps_time parse_steps_time_bound[of 0] by auto
  also have "... \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)" using length_bound by simp
  finally show ?thesis.
qed

lemma T_Parse_close2_L_bound: 
  assumes dist: "distinct ps"
  and invs: "inv_PIL pil1"
  and lengs: "length (froms (fst pil1)) = Suc (length Bs)" 
  and wf1: "wf_PIL pil1 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
shows "T_Parse_close2_L Bs pil1 \<le> length Bs + 2 + Suc (length Bs) + L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12) +  Suc (L * Suc K * Suc (length Bs))"
proof-
  have 2: "T_empty_PIL (length Bs) = length Bs + 2" by simp
  have 3: "T_length Bs = Suc (length Bs)" by (simp add: T_length)

  have empty_inv: "inv_PIL (empty_PIL (length Bs))" and "length (froms (fst (empty_PIL (length Bs)))) = Suc (length Bs)"
    and empty_wf: "wf_PIL (empty_PIL (length Bs)) (length Bs)"
    and "length (PIL_map_item (empty_PIL (length Bs))) = 0"
    using PIL_inv_empty wf_empty_PIL by (auto simp add: PIL_map_item_def)
  then have 1: "T_Parse_steps Bs (pil1, empty_PIL (length Bs)) \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_IL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)" using T_Parse_steps_bound assms by simp

  obtain a where Some_Psteps: "Parse_steps Bs (pil1, empty_PIL (length Bs)) = Some a"
    using Parse_steps_NF empty_inv empty_wf length_empty_PIL lengs invs wf1(1,2) by blast

  let ?result_PIL = "(snd (the (Parse_steps Bs (pil1, empty_PIL (length Bs)))))"
  have "wf_PIL ?result_PIL (length Bs)"
    using wf_Parse_close2_L assms by (auto simp add: Parse_close2_L_def simp del: wf_parse_bin1.simps)
  moreover have res_inv: "inv_PIL ?result_PIL" using  Parse_steps_inv2 invs empty_inv empty_wf length_empty_PIL
    by (metis Parse_steps_NF eq_snd_iff option.sel wf1(1,2) lengs)
  ultimately have "length (list (fst ?result_PIL)) \<le> L * Suc K * Suc (length Bs)" using length_fst_PIL by auto
  then have "T_PIL_list ?result_PIL \<le> Suc (L * Suc K * Suc (length Bs))" using res_inv T_zip 
    by (cases ?result_PIL) fastforce
  moreover have "T_the (Parse_steps Bs (pil1, empty_PIL (length Bs))) = 0" using Some_Psteps by auto
  moreover have "T_snd (the (Parse_steps Bs (pil1, empty_PIL (length Bs)))) = 0" by simp
  ultimately show ?thesis using 1 2 3 unfolding T_Parse_close2_L.simps by presburger
qed

lemma length_Parse_close2_L: 
  assumes "inv_PIL pil" "wf_PIL pil (length Bs)" "wf_parse_bins1 (map set Bs)" "length (froms (fst pil)) = Suc (length Bs)"
  shows "length (Parse_close2_L Bs pil) \<le> L * Suc K * Suc (length Bs)"
proof-
  have empty_inv: "inv_PIL (empty_PIL (length Bs))" and empty_wf: "wf_PIL (empty_PIL (length Bs)) (length Bs)"
    and empty_leng: "length (froms (fst (empty_PIL (length Bs)))) = Suc (length Bs)"
    using PIL_inv_empty wf_empty_PIL by auto

  let ?result_PIL = "(snd (the (Parse_steps Bs (pil, empty_PIL (length Bs)))))"
  have "wf_PIL ?result_PIL (length Bs)"
    using wf_Parse_close2_L assms by (auto simp add: Parse_close2_L_def simp del: wf_parse_bin1.simps)
  moreover have res_inv: "inv_PIL ?result_PIL" using  Parse_steps_inv2 empty_inv empty_wf empty_leng assms
    by (metis Parse_steps_NF eq_snd_iff option.sel)
  ultimately show "length (Parse_close2_L Bs pil) \<le> L * Suc K * Suc (length Bs)" 
    using length_snd_PIL by (cases ?result_PIL) (auto simp add: Parse_close2_L_def)
qed

lemma Parse_bins_L_lengths: "k \<le> length w \<Longrightarrow> \<forall> i < Suc k. length ((Parse_bins_L k) ! i) \<le> L * Suc K * Suc k"
proof(induction k)
  case 0
  have "length (Parse_close2_L [] (PIL_of_List 0 Parse_Init_L)) \<le> L + L * K" 
    using length_Parse_close2_L[of "PIL_of_List 0 Parse_Init_L" "[]"] PIL_inv_PIL_of_List[OF forall_from_Suc_parse]
      wf_PIL_of_List[of Parse_Init_L 0 0] wf1_Parse_Init_L ex_map_conv in_set_conv_nth 
      less_nat_zero_code list.distinct(1) wf_parse_bins1_def by fastforce 
  then show ?case 
       by auto
next
  case (Suc k)
  then have ih: "\<forall> i < Suc k. length (Parse_bins_L (Suc k) ! i) \<le> L * Suc K * Suc (Suc k)" 
    by (auto simp add: Let_def nth_append_left)
  let ?scan_pil = "PIL_of_List (Suc k) (Parse_Scan_L (last (Parse_bins_L k)) k)"
  have "Parse_bins k \<noteq> []"
    by (metis length_parse_bins list.size(3) nat.distinct(1))
  then have "last (Parse_bins_L k) = Parse_bins_L k ! k" using Suc length_parse_bins last_conv_nth
    by (metis One_nat_def Zero_not_Suc diff_Suc_Suc length_Parse_bins list.size(3) minus_nat.diff_0)
  then have "wf_parse_bin1 (set (last (Parse_bins_L k))) k" 
    using Suc wf_parse_bins_L unfolding wf_parse_bins1_def by (auto simp del: wf_parse_bin1.simps)
  then have 1: "wf_PIL ?scan_pil (length (Parse_bins_L k))" using wf1_Parse_Scan_L Suc wf_PIL_of_List
    using length_Parse_bins less_eq_Suc_le by presburger
  moreover have "inv_PIL ?scan_pil" using 1 PIL_inv_PIL_of_List[OF forall_from_Suc_parse]
    by (meson Suc.prems \<open>wf_parse_bin1 (set (last (Parse_bins_L k))) k\<close> less_eq_Suc_le wf1_Parse_Scan_L)
  moreover have "wf_parse_bins1 (map set (Parse_bins_L k))" using Suc wf_parse_bins_L by simp
  ultimately have 1: "length (Parse_close2_L (Parse_bins_L k) ?scan_pil) \<le> L * Suc K * Suc (Suc k)" 
    using length_Parse_close2_L[of ?scan_pil "Parse_bins_L k"] by auto
  then have "length (Parse_bins_L (Suc k) ! (Suc k)) \<le> L * Suc K * Suc (Suc k)" by (simp add: Let_def nth_append_right)
  then show ?case using ih not_less_less_Suc_eq by blast
qed



lemma T_Parse_bins_L_bound:
  assumes "distinct ps" "k \<le> length w"
  shows "T_Parse_bins_L k 
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 9 + k"
using assms proof(induction k)
  case 0
  have 1: "length Parse_Init_L \<le> L" by (auto simp add: Parse_Init_L_def L_def)
  have "T_PIL_of_List 0 Parse_Init_L \<le> (length Parse_Init_L) * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + length Parse_Init_L + 3"
    using T_PIL_of_List_bound by (metis Nat.add_0_right  assms(1) wf1_Parse_Init_L)
  also have "... \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + L + 3"
    using 1 mult_le_mono1[OF 1, of "(4 * T_nth_IL (0) + 2 * L * Suc K + 2)"] by auto
  finally have 2: "T_PIL_of_List 0 Parse_Init_L \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + L + 3".

  have "wf_parse_bins1 (map set [])" by (auto simp add: wf_parse_bins1_def)
  moreover have "\<forall>i<length []. length ([] ! i) \<le> 0" by auto
  moreover have "wf_PIL (PIL_of_List 0 Parse_Init_L) 0" using wf_PIL_of_List wf1_Parse_Init_L by blast
  moreover have "length (froms (fst (PIL_of_List 0 Parse_Init_L))) = 1" 
    using length_PIL_of_List wf1_Parse_Init_L by (auto simp add: wf_item1_def )
  ultimately have "T_Parse_close2_L [] (PIL_of_List 0 Parse_Init_L) \<le> 2 + 1 + L * Suc K  
    * (L * (4 * T_nth_IL (0) + 2 * L * Suc K + 3)
    + Suc L * Suc K  * (13 * T_nth_IL (0) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12) +  Suc (L * Suc K)" 
    using T_Parse_close2_L_bound[of "PIL_of_List 0 Parse_Init_L" "[]" 0] assms 
      PIL_inv_PIL_of_List[OF forall_from_Suc_parse] wf1_Parse_Init_L
    by (auto simp del: T_Parse_close2_L.simps)
  also have "... \<le> L * Suc K  * (Suc L * Suc K  * (17 * T_nth_IL (0) + 5 * L * Suc K + 19) + 13) + 4" 
    by (auto simp add: algebra_simps)
  finally have "T_Parse_close2_L [] (PIL_of_List 0 Parse_Init_L) 
    \<le> L * Suc K  * (Suc L * Suc K  * (17 * T_nth_IL (0) + 5 * L * Suc K + 19) + 13) + 4".

  then have "T_Parse_bins_L 0 \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2) + L + 3
    + L * Suc K  * (Suc L * Suc K  * (17 * T_nth_IL (0) + 5 * L * Suc K + 19) + 13) + 4 + 1"
    using 2 by auto
  also have "... \<le> L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
    + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 9" 
    by (auto simp add: algebra_simps)
  finally show ?case by auto
next  
  case (Suc k)
  let ?Bs = "Parse_bins_L k"
  have cons: "?Bs \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_Parse_bins)
  then have length_last: "length (last ?Bs) \<le> L * Suc K * Suc k" 
    using Parse_bins_L_lengths last_conv_nth Suc
    by (metis One_nat_def diff_Suc_1' length_Parse_bins less_eq_Suc_le order_le_less)
  have wf1_last: "wf_parse_bin1 (set (last ?Bs)) k" 
    using length_Parse_bins wf_parse_bins_L[of k] cons Suc
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_item_Pt1.simps)
  then have wf_last: "wf_parse_bin (set (last ?Bs)) k" using Suc by (auto simp add: wf_item1_def)

  have 1: "T_length ?Bs = k + 2" by (auto simp add: T_length)
  have 2: "T_last ?Bs = k + 1" using T_last cons by auto
  have "T_Parse_Scan_L (last ?Bs) k \<le> k + (2 * K + 4) * (length (last (Parse_bins_L k))) + 3"
    using wf_last Suc T_Parse_Scan_L_bound
    by (auto simp add: w_def simp del: T_Parse_Scan_L.simps)
  also have "... \<le> k + (2 * K + 4) * (L * Suc K * Suc k) + 3" using length_last by auto
  finally have 3: "T_Parse_Scan_L (last ?Bs) k \<le> k + (2 * K + 4) * (L * Suc K * Suc k) + 3".

  let ?parse = "Parse_Scan_L (last ?Bs) k"
  have "length ?parse \<le> length (last ?Bs)" 
    unfolding Parse_Scan_L_def Let_def by simp
  then have length_parse: "length ?parse \<le> L * Suc K * Suc k" using length_last by auto
  have "T_PIL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k) 
    \<le> length ?parse * (4 * T_nth_IL (length ?Bs) + 2 * L * Suc K + 2) + length ?parse + length ?Bs + 3" 
    using T_PIL_of_List_bound[of ?parse "length ?Bs"] wf1_Parse_Scan_L wf1_last Suc 
    by (auto simp del: T_PIL_of_List.simps wf_parse_bin1.simps)
  also have "... \<le> L * Suc K * Suc k * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 3" 
    using length_parse mult_le_mono1[OF length_parse, of "(4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2)"]
    by (auto simp add: algebra_simps)
  finally have 4: "T_PIL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k)
    \<le> L * Suc K * Suc k * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 3".

  have 5: "T_append ?Bs [Parse_close2_L ?Bs (PIL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k))] 
    = k+2" by simp

  let ?parse_pil = "PIL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k)"
  have wf1_parse: "wf_parse_bin1 (set ?parse) (Suc k)" using wf1_Parse_Scan_L wf1_last Suc 
    by (auto simp del: wf_parse_bin1.simps)
  have "inv_PIL ?parse_pil" using PIL_inv_PIL_of_List[OF forall_from_Suc_parse]
    using length_Parse_bins wf1_parse by presburger
  moreover have "wf_PIL ?parse_pil (Suc k)" using wf_PIL_of_List wf1_Parse_Scan_L wf1_last Suc 
    by (auto simp del: wf_parse_bin1.simps)
  moreover have "length (froms (fst ?parse_pil)) - 1 = Suc k" 
    using wf1_parse by (auto simp add: wf_item1_def)
  ultimately have 6: "T_Parse_close2_L ?Bs (PIL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k))
    \<le> Suc k + 2 + Suc (Suc k) + L * Suc K * Suc (Suc k)
    * ((2 * K * K + 2 * K + 5) * (L * Suc K * Suc k) + (L * Suc K * Suc k) * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (Suc k) * (13 * T_nth_IL (Suc k) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12) +  Suc (L * Suc K * Suc (Suc k))"
    using T_Parse_close2_L_bound[of ?parse_pil ?Bs "L * Suc K * Suc k"] Parse_bins_L_lengths wf_parse_bins_L Suc 
    by (auto simp del: T_Parse_close2_L.simps wf_parse_bin1.simps)
  also have "... = L * Suc K * Suc (Suc k)
    * ((L * Suc K * Suc k) * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K * K + 2 * K + 8)
    + Suc L * Suc K * Suc (Suc k) * (13 * T_nth_IL (Suc k) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 13) + 2 * k + 6" by (auto simp add: algebra_simps)
  also have "... \<le> L * Suc K * Suc (Suc k)
    * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 13) 
    + 2 * k + 6" by (auto simp add: algebra_simps)
  finally have 7:  "T_Parse_close2_L ?Bs (PIL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k))
    \<le> L * Suc K * Suc (Suc k)
      * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 13) 
      + 2 * k + 6".

  have "T_Parse_bins_L k \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 9 + k"
    using Suc by simp
  also have "... \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 9 + k"
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
  finally have "T_Parse_bins_L k \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 9 + k".

  then have "T_Parse_bins_L (Suc k)
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 9 + k
      +
      k + 3 + k + 1 + k + (2 * K + 4) * (L * Suc K * Suc k) + 3
      + L * Suc K * Suc k * (4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 3
      + L * Suc K * Suc (Suc k)
      * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 13) 
      + 2 * k + 5 + k + 2 + 1" unfolding T_Parse_bins_L.simps Let_def using 1 2 3 4 5 7 by presburger
  
  also have "... \<le> Suc k *
       (L * Suc K * Suc (Suc (Suc k)) *
        (Suc L * Suc K * Suc (Suc (Suc k)) * (17 * T_nth_IL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 4 * T_nth_IL (Suc k) + 2 * L * Suc K + 2 * K + 20) +
        7 * Suc k +
        16) +
       L * (4 * T_nth_IL 0 + 2 * L * Suc K + 2) +
       L * Suc K * (Suc L * Suc K * (21 * T_nth_IL 0 + 5 * L * Suc K + 19) + 2 * L + 15) +
       L +
       9 +
       Suc k" by (auto simp add: algebra_simps)
  finally show ?case.
qed

subsection \<open>Nice time bounds\<close>

definition C3 where "C3 = (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))"
definition C4 where "C4 = (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)"
definition C6 where "C6 = L * Suc K * Suc L * Suc K * 17"
definition C7 where "C7 = L * Suc K * 4"
definition C5 where "C5 = L * Suc K  * (Suc L * Suc K  * (25 * T_nth_IL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 7"


theorem T_Parse_bins_bound_nice:
  assumes "distinct ps" "k \<le> length w"
  shows "T_Parse_bins_L k 
      \<le> (k+2)^3 * C3 + (k+2)^2 * C4 + (k+2) * 3 + C5 
        + (k+2)^3 * T_nth_IL (k) * C6 + (k+2)^2 * T_nth_IL (k) * C7"
proof-
  have "T_Parse_bins_L k 
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_IL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_IL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 9 + k"
    using T_Parse_bins_L_bound assms by simp
  also have "... \<le> (k+2) * (L * Suc K * (k+2)
          * (Suc L * Suc K * (k+2) * (17 * T_nth_IL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_IL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * (k + 2) + 2)
        + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_IL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 9 + k"
    by (auto simp add: algebra_simps)
  also have "... = (k+2) * (k+2) * (k+2) * (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))
    + (k+2) * (k+2) * (k+2) * (L * Suc K * Suc L * Suc K * 17 * T_nth_IL (k))
    + (k+2) * (k+2) * (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)
    + (k+2) * (k+2) * (L * Suc K * 4 * T_nth_IL (k))
    + (k+2) * 3
    + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_IL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 7"
    by (auto simp add: algebra_simps)
  also have "... = (k+2)^3 * (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))
    + (k+2)^3 * (L * Suc K * Suc L * Suc K * 17 * T_nth_IL (k))
    + (k+2)^2 * (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)
    + (k+2)^2 * (L * Suc K * 4 * T_nth_IL (k))
    + (k+2) * 3 
    + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_IL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 7" 
    by (simp only: monoid_mult_class.power3_eq_cube monoid_mult_class.power2_eq_square)
  finally show ?thesis by (auto simp add: C3_def C4_def C5_def C6_def C7_def algebra_simps)
qed

end

section \<open>Example\<close>

definition ps where "ps = [((0::nat), [Tm (1::int)]), (0, [Nt (0::nat), Nt 0])]"
definition S :: nat where "S = 0"
definition w1 where "w1 = [1, 1, (1 :: int)]"

interpretation Earley_Gw_eps
  where ps = ps and S = S and w0 = w1 
proof
  show "eps_free ps" by (auto simp add: Eps_free_def ps_def)
qed

declare Earley_Gw.Predict_L_def[code]
declare Earley_Gw.mv_dot_def[code]
declare Earley_Gw.Complete_L_def[code]
declare Earley_Gw.Scan_L_def[code]
declare Earley_Gw.Init_L_def[code]
declare Earley_Gw.step_fun.simps[code]
declare Earley_Gw.steps_def[code]
declare Earley_Gw.close2_L_def[code]
declare Earley_Gw.bins_L.simps[code]
declare Earley_Gw.w_def[code]

declare Earley_Gw.IL_of_List_def[code]
declare Earley_Gw.union_LIL.simps[code]
declare Earley_Gw.minus_IL_def[code]
declare empty_IL_def[code]
declare Earley_Gw.insert.simps[code]
declare Earley_Gw.minus_LIL.simps[code]
declare isin.simps[code]

value "bins_L 0"
value "bins_L 1"
value "bins_L 2"
value "bins_L 3"

(*unused_thms*)
end