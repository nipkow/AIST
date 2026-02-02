theory EarleyWorklist

imports "Earley" "HOL-Library.While_Combinator" "HOL-Data_Structures.Define_Time_Function" "HOL-Data_Structures.Set_Specs" "Context_Free_Grammar.Parse_Tree"

begin

context Earley_Gw
begin

(* must not be empty, otherwise by def step_rel is always false *)
definition step_rel :: "('n, 'a) state set list \<Rightarrow> ('n, 'a) state set \<times> ('n, 'a) state set \<Rightarrow> ('n, 'a) state set \<times> ('n, 'a) state set \<Rightarrow> bool" where
"step_rel  \<equiv> Close2"


definition Predict_L :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> ('n,'a) state list" where
  "Predict_L x k = map (\<lambda>p. State p 0 k) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps)"


definition Complete_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) state list" where
  "Complete_L Bs y = map mv_dot (filter (\<lambda> b. next_sym_Nt b (lhs(prod y))) (Bs ! from y))"

definition Init_L :: "('n,'a) state list" where
  "Init_L =  map (\<lambda> p. State p 0 0) (filter (\<lambda> p. lhs p = (S)) ps)"

lemma Init_L_eq_Init: "set Init_L = Init"
  by (auto simp add: Init_L_def Init_def)

definition Scan_L :: "('n,'a) state list \<Rightarrow> nat \<Rightarrow> ('n,'a) state list" where
  "Scan_L Bs k = (let x = Some (Tm (w0 ! k)) in map mv_dot (filter (\<lambda> b. next_symbol b = x) Bs))"
                                           
lemma Scan_L_eq_Scan: "k < length w \<Longrightarrow> set (Scan_L Bs k) = Scan (set Bs) k"
  by (auto simp add: Scan_L_def Scan_def w_def)

definition minus_L :: "'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" (infix "-l" 50) where
  "minus_L As Bs = foldr (removeAll) Bs As"

lemma minus_L_set[simp]: "set (As -l Bs) = set As - set Bs"
  by (induction Bs) (auto simp add: minus_L_def)

fun member :: "'c list \<Rightarrow> 'c \<Rightarrow> bool" where
"member [] a = False"
| "member (x#xs) a = (if x = a then True else member xs a)"

lemma member_elem: "member xs a = (a \<in> (set xs))"
  by (induction xs) auto


datatype ('c,'d) WorkList = 
  WorkList ("list": "('c,'d) state list") ("leng" : nat) ("list_map" : "('c,'d) state list list")

fun WL_inv :: "('n, 'a) WorkList \<Rightarrow> bool" where
"WL_inv (WorkList as l m) = (Suc l = length m \<and> (\<forall>x \<in> set as. from x < Suc l) \<and> (\<forall>i < Suc l. set (m ! i) = {x \<in> set as. from x = i}) \<and> (\<forall>i < Suc l. distinct (m ! i)) \<and> distinct as)"

(*TODO use replicate instead*)
fun empty_list_map :: "nat \<Rightarrow> ('n, 'a) state list list" where
"empty_list_map 0 = [[]]"|
"empty_list_map (Suc k) = []#empty_list_map k"

definition WL_empty :: "nat \<Rightarrow> ('n, 'a) WorkList" where
"WL_empty k = (WorkList [] k (empty_list_map k))"

fun isin :: "('n, 'a) WorkList \<Rightarrow> ('n, 'a) state \<Rightarrow> bool" where
"isin (WorkList as l m) x = (if from x < Suc l then member (m ! from x) x else False)"

fun set_WorkList :: "('n, 'a) WorkList \<Rightarrow> ('n, 'a) state set" where
"set_WorkList wl = set (list wl)"

fun upsize :: "('n, 'a) WorkList \<Rightarrow> nat \<Rightarrow> ('n, 'a) WorkList" where
"upsize wl 0 = wl" |
"upsize wl (Suc k) = WorkList (list wl) (leng wl + (Suc k)) ((list_map wl) @ empty_list_map k)"

fun insert :: "('n, 'a) WorkList \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) WorkList" where
"insert (WorkList as l m) x = (if isin (WorkList as l m) x then WorkList as l m else
                                (if from x < Suc l then WorkList (x#as) l (m[from x := x#(m ! from x)]) else
                               (let wl = (upsize (WorkList as l m) (Suc (from x) - l)) 
                                in WorkList (x # (list wl)) (leng wl) ((list_map wl)[from x := x#(list_map wl ! from x)]) )))"

(*fun remove_first :: "('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList" where
"remove_first (WorkList [] l m) = WorkList [] l m" |
"remove_first (WorkList (a#as) l m) = WorkList as l (m[l - from a - 1 := list_remove (m ! (l - from a - 1)) a])"*)

fun union_LWL :: "('n, 'a) state list \<Rightarrow> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList" where
"union_LWL [] wl = wl" |
"union_LWL (a#as) wl = insert (union_LWL as wl) a"

definition union_WL :: "('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList" where
"union_WL wl1 wl2 = union_LWL (list wl1) wl2"

definition WL_of_List :: "nat \<Rightarrow> ('n, 'a) state list \<Rightarrow> ('n, 'a) WorkList" where
"WL_of_List k as = union_LWL as (WL_empty k)"

fun minus_LWL :: "nat \<Rightarrow> ('n, 'a) state list \<Rightarrow> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList" where
"minus_LWL k [] wl = WL_empty k" |
"minus_LWL k (a#as) wl = (if \<not>(isin wl a) then insert (minus_LWL k as wl) a else minus_LWL k as wl)"

definition minus_WL :: "('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList" where
"minus_WL wl1 wl2 = minus_LWL (leng wl1) (list wl1) wl2"

lemma wl_decomp: "\<exists>as l m. wl = WorkList as l m"
  by (meson Earley_Gw.WorkList.exhaust_sel)

lemma set_WL_empty: "set_WorkList (WL_empty k) = {}" by (simp add: WL_empty_def)

lemma leng_empty_list_map: "length (empty_list_map k) = Suc k"
  by(induction k) auto

lemma nth_empty_list_map: "i < Suc k \<Longrightarrow> (empty_list_map k) ! i = []"
proof (induction k arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case by (cases "i") (auto simp flip: nth_Cons_Suc)
qed

lemma empty_inv: "WL_inv (WL_empty k)"
proof (induction k)
  case 0
  then show ?case by (simp add: WL_empty_def)
next
  case (Suc k)
  have "Suc (length (empty_list_map k)) = length (empty_list_map (length (empty_list_map k)))"
    by (auto simp add: leng_empty_list_map)
  then show ?case using Suc by (auto simp add: WL_empty_def nth_empty_list_map)
qed



lemma WL_inv1: "WL_inv wl \<Longrightarrow> distinct (list wl) \<and> Suc (leng wl) = length (list_map wl) 
  \<and> (\<forall>x \<in> set (list wl). from x < Suc (leng wl)) 
  \<and> (\<forall>i < Suc (leng wl). set ((list_map wl) ! i) = {x \<in> set (list wl). from x = i}) 
  \<and> (\<forall>i < Suc (leng wl). distinct ((list_map wl) ! i))"
  using WL_inv.simps[of "list wl" "leng wl" "list_map wl"] by auto
    
lemma isin_WL: "WL_inv (WorkList as l m) \<Longrightarrow> (isin (WorkList as l m) x) = (x \<in> set_WorkList (WorkList as l m))" 
  by (auto simp add: member_elem)

lemma isin_WL1: "WL_inv wl \<Longrightarrow> (isin wl x) = (x \<in> set_WorkList wl)"
  by (metis WL_inv.cases isin_WL)

lemma WL_inv_upsize: 
  assumes "WL_inv (WorkList as l m)" shows "WL_inv (upsize (WorkList as l m) k)"
proof -
  show ?thesis 
  proof (cases k)
    case 0
    then show ?thesis using assms by auto
  next
    case (Suc n)
    have 1: "i < Suc l + k \<Longrightarrow> set ((m @ empty_list_map n) ! i) = {x \<in> set as. from x = i}" for i
      using assms Suc by (cases "i < length m") (auto simp add: nth_append_left nth_append_right nth_empty_list_map)
    have "i < Suc l + k \<Longrightarrow> distinct ((m @ empty_list_map n) ! i)" for i
      using assms Suc by (cases "i < length m") (auto simp add: nth_append_left nth_append_right nth_empty_list_map)
    then show ?thesis using assms Suc 1 by (auto simp add: leng_empty_list_map)
  qed
qed

lemma upsize_length: "upsize (WorkList as l m) k = WorkList as' l' m' \<Longrightarrow> l' = k + l"
  by (metis Earley_Gw.WorkList.sel(2) Earley_Gw.upsize.elims add.commute add_cancel_left_left)

lemma upsize_list: "list (upsize (WorkList as l m) k) = as"
  by (cases k) auto

lemma upsize_list1[simp]: "list (upsize wl k) = list wl"
  using upsize_list by (metis WL_inv.cases WorkList.sel(1))

lemma set_upsize: "set_WorkList (upsize (WorkList as l m) k) = set_WorkList (WorkList as l m)"
  by (cases k) auto

lemma set_upsize1: "set_WorkList (upsize wl k) = set_WorkList wl"
  using set_upsize by (metis WL_inv.cases)

lemma WL_insert: "WL_inv (WorkList as l m) \<Longrightarrow> set_WorkList (insert (WorkList as l m) x) = set_WorkList ((WorkList as l m)) \<union> {x}"
  using set_upsize[of _ _ _ "(Suc (from x) - l)"] by (auto simp add: Let_def isin_WL simp del: isin.simps)

lemma WL_insert1: "WL_inv wl \<Longrightarrow> set_WorkList (insert wl x) = set_WorkList wl \<union> {x}"
  using WL_insert by (metis WL_inv.cases)

lemma list_map_inv: 
  assumes "x \<notin> set as" "from x < Suc l" "WL_inv (WorkList as l m)" 
  shows "WL_inv (WorkList (x#as) l (m[from x := x#(m!from x)]))"
proof -
  have 1: "i < Suc l \<Longrightarrow> set (m[from x := x#(m!from x)] ! i) = {y \<in> set (x#as). from y = i}" for i
    using assms by (cases "i = from x") auto
  have "i < Suc l \<Longrightarrow> distinct (m[from x := x#(m!from x)] ! i)" for i
      using assms by (cases "i = from x") auto 
  then show ?thesis using assms 1 by auto
qed

lemma insert_WL_inv: 
  assumes "WL_inv (WorkList as l m)" shows "WL_inv (insert (WorkList as l m) x)"
proof -
  let ?wl = "(upsize (WorkList as l m) (Suc (from x) - l))"
  have "WL_inv ?wl" using assms by (auto simp add: WL_inv_upsize)
  then obtain k n where P: "?wl = WorkList as k n \<and> WL_inv (WorkList as k n)"
    by (metis Earley_Gw.WL_inv.cases upsize_list upsize_list1)
  have 1: "from x < k" using P upsize_length
    by (metis less_diff_conv less_not_refl not_less_eq)

  then show ?thesis using assms P list_map_inv 
    by (auto simp add: isin_WL simp del: WL_inv.simps isin.simps)
qed

lemma insert_WL_inv1: "WL_inv wl \<Longrightarrow> WL_inv (insert wl x)"
  using insert_WL_inv by (metis WL_inv.cases)

lemma LWL_union_inv: "WL_inv wl \<Longrightarrow> WL_inv (union_LWL as wl)"
  using insert_WL_inv1 by (induction as) auto

lemma LWL_union: "WL_inv wl \<Longrightarrow> set_WorkList (union_LWL as wl) = set as \<union> set_WorkList wl"
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have "set_WorkList (union_LWL (a # as) wl) = set_WorkList (insert (union_LWL as wl) a)" by simp
  also have "... = set_WorkList (union_LWL as wl) \<union> {a}" using Cons WL_insert1 LWL_union_inv by blast
  also have "... = set as \<union> set_WorkList wl \<union> {a}" using Cons WL_insert1 LWL_union_inv by blast
  finally show ?case by auto
qed

lemma WL_union: "WL_inv wl2 \<Longrightarrow> set_WorkList (union_WL wl1 wl2) = set_WorkList wl1 \<union> set_WorkList wl2"
  using LWL_union by (auto simp add: union_WL_def)

lemma WL_union_inv: "WL_inv wl2 \<Longrightarrow> WL_inv (union_WL wl1 wl2)"
  using LWL_union_inv by (auto simp add: union_WL_def)

lemma set_WL_of_List: "set_WorkList (WL_of_List k as) = set as"
  using LWL_union empty_inv
  by (metis WL_of_List_def set_WL_empty sup_bot_right)

lemma WL_of_List_inv: "WL_inv (WL_of_List k as)"
  using LWL_union_inv empty_inv by (auto simp add: WL_of_List_def)

lemma LWL_minus_inv: "WL_inv (minus_LWL k as wl)"
  using insert_WL_inv1 empty_inv by (induction as) (auto simp add:)

lemma LWL_minus: "WL_inv wl \<Longrightarrow> set_WorkList (minus_LWL k as wl) = set as - set_WorkList wl"
proof (induction as)
  case Nil
  then show ?case by (simp add: WL_empty_def)
next
  case (Cons a as)
  then show ?case
  proof (cases "isin wl a")
    case True
    then show ?thesis using Cons isin_WL1 by auto
  next
    case False
    then have "set_WorkList (minus_LWL k (a # as) wl) = set_WorkList (insert (minus_LWL k as wl) a)" by simp
    also have "... = set_WorkList (minus_LWL k as wl) \<union> {a}" using WL_insert1 Cons LWL_minus_inv by blast
    then show ?thesis using Cons isin_WL1 by auto
  qed
qed

lemma WL_minus_inv: "WL_inv (minus_WL wl1 wl2)"
  using LWL_minus_inv by (auto simp add: minus_WL_def)

lemma WL_minus: "WL_inv wl2 \<Longrightarrow> set_WorkList (minus_WL wl1 wl2) = set_WorkList wl1 - set_WorkList wl2"
  using LWL_minus by (auto simp add: minus_WL_def)

lemma leng_WL_insert: 
  assumes "from a < Suc (leng wl)" shows "leng (insert wl a) = leng wl"
proof-
  obtain as l m where "wl = WorkList as l m"
    using WL_inv.cases by blast
  then show ?thesis using assms by auto
qed

lemma leng_LWL_union: "\<forall>x \<in> set as. from x < Suc (leng wl) \<Longrightarrow> leng (union_LWL as wl) = leng wl"
  by (induction as arbitrary: wl) (auto simp add: leng_WL_insert)

abbreviation wf1_WL :: "('n, 'a) WorkList \<Rightarrow> nat \<Rightarrow> bool" where
"wf1_WL wl k \<equiv> wf_bin1 (set_WorkList wl) k"


fun step_fun :: "('n, 'a) state list list \<Rightarrow>  ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList" where
  "step_fun Bs ((WorkList [] l m), C) = undefined" |
  "step_fun Bs ((WorkList (b#bs) l m), C) = (let step = (if is_complete b then Complete_L Bs b else Predict_L b (length Bs)) in
    ( minus_WL (union_LWL step (WorkList (b#bs) l m)) (insert C b), insert C b) )"
(* (bs \<union> step) - (C \<union> {b}) *)

definition steps :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> (('n, 'a) WorkList \<times> ('n, 'a) WorkList) option" where
  "steps Bs BC = while_option (\<lambda>(B,C). list B \<noteq> []) (step_fun Bs) BC"

definition close2_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) state list" where
"close2_L Bs B = list (snd (the (steps Bs (B, WL_empty (length Bs)))))"

fun bins_L :: "nat \<Rightarrow> ('n,'a) state list list" where
"bins_L 0 = [close2_L [] (WL_of_List 0 Init_L)]" |
"bins_L (Suc k) = (let Bs = bins_L k in Bs @ [close2_L Bs (WL_of_List (length Bs) (Scan_L (last Bs) k))])"

(*definition "wf_binL B k = (list_all (\<lambda> x. wf_state1 x k) B)"

fun wf_binsL_help where
  "wf_binsL_help [] k = True"
| "wf_binsL_help (B#Bs) k = (wf_binL B k \<and> wf_binsL_help Bs (Suc k))"
definition "wf_binsL Bs = wf_binsL_help Bs 0"

lemma wf_binL_eq: "wf_binL B k = wf_bin1 (set B) k"
   by (induction B) (auto simp add: wf_bin1_def wf_binL_def)

lemma wf_binsL_help_eq: "wf_binsL_help Bs n = (\<forall>k < length Bs. wf_binL (Bs!k) (k + n))"
  by (induction Bs arbitrary: n) (auto simp add: less_Suc_eq_0_disj)

lemma wf_binsL_eq: "wf_binsL Bs = wf_bins1 (map set Bs)" 
  by (auto simp add: wf_binsL_def wf_bins1_def wf_binL_eq wf_binsL_help_eq)*)

lemma Predict_eq: "set (Predict_L st k) = Predict st k"
  by (auto simp add: Predict_L_def Predict_def)


lemma Complete_eq: "from st < length Bs \<Longrightarrow> set (Complete_L Bs st) = Complete (map set Bs) st"
  by (auto simp add: Complete_L_def Complete_def nths_map)

lemma test:
  assumes inv: "WL_inv (WorkList (a#as) l1 m1)" "WL_inv (WorkList bs l2 m2)"
  and sf: "step_fun Bs ((WorkList (a#as) l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
  shows  "set as' = (set as \<union> set ((if is_complete a then Complete_L Bs a else Predict_L a (length Bs)))) - (set bs \<union> {a})"
proof-
  let ?step = "(if is_complete a then Complete_L Bs a else Predict_L a (length Bs))"
  have "set as' = set_WorkList (minus_WL (union_LWL ?step (WorkList (a#as) l1 m1)) (insert (WorkList bs l2 m2) a))"
    using sf by auto
  also have "... = (set (a#as) \<union> set ?step) - (set bs \<union> {a})" using inv
    by (smt (verit) Earley_Gw.WorkList.sel(1) Earley_Gw.set_WorkList.simps LWL_union Un_commute WL_insert1 WL_minus insert_WL_inv1)
  finally show ?thesis by auto
qed

lemma step_fun_sound: 
  assumes cons: "as \<noteq> []" 
  and wf: "wf1_WL (WorkList as l1 m1) (length Bs)"
  and inv: "WL_inv (WorkList as l1 m1)" "WL_inv (WorkList bs l2 m2)"
  and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
shows "step_rel (map set Bs) (set as,set bs) (set as', set bs')"
proof-
  have comp: "\<forall>a \<in> set as. is_complete a \<longrightarrow> from a < length Bs" using wf by (auto simp add: wf_bin1_def wf_state1_def)
  from cons obtain a ass where P :"as = a # ass"
    using list.exhaust by auto 

  let ?xs = "if is_complete a then Complete (map set Bs) a else Predict a (length Bs)"
  let ?xsL = "if is_complete a then Complete_L Bs a else Predict_L a (length Bs)"

  have "a \<in> set as \<and> (if is_complete a then next_symbol a = None else next_symbol a \<noteq> None)"
    by (auto simp add: P next_symbol_def)
  then have 1: "(map set Bs) \<turnstile> (set as, set bs) \<rightarrow> ((set as \<union> ?xs) - (set bs \<union> {a}), (set bs \<union> {a}))"
    using Close2.Complete Close2.Predict
    by (smt (verit, best) Un_insert_right boolean_algebra.disj_zero_right length_map)

  have 2: "set as' = (set ass \<union> set ?xsL) - (set bs \<union> {a})"
    using P inv sf test[of a ass l1 m1 bs l2 m2 Bs as'] by blast
  have "set bs' = (set bs \<union> {a})" using inv sf P WL_insert1[of "(WorkList bs l2 m2)" a] by auto 

  then show ?thesis using 1 2
    using Complete_eq P Predict_eq comp step_rel_def by fastforce
qed
  
end (*Earley_Gw*)

context Earley_Gw_eps
begin

lemma wf1_Predict_L: "wf_state1 st k \<Longrightarrow> wf_bin1 (set (Predict_L st k)) k"
  using wf1_Predict Predict_eq by (auto simp add: wf_bin1_def)

lemma wf1_Complete_L: 
  assumes "wf_bins1 (map set Bs)" "wf_state1 st (length Bs)" "is_complete st" 
    shows "wf_bin1 (set (Complete_L Bs st)) (length Bs)"
proof-
  have 1: "\<forall>x \<in>  (set (filter (\<lambda> b. next_sym_Nt b (lhs(prod st))) (Bs ! from st))). wf_state x (from st)"
    using assms by (simp add: wf_bin1_def wf_bins1_def wf_state1_def)
  then have 2: "\<forall>x \<in> (set  (filter (\<lambda> b. next_sym_Nt b (lhs(prod st))) (Bs ! from st))). wf_state (mv_dot x) (from st)"
    using assms 1 unfolding wf_state_def is_complete_def next_symbol_def mv_dot_def
    by (auto split: if_splits)
  have "from st < length Bs"
    using assms(2,3) wf_state1_def by auto
  then show ?thesis
     using assms 2 Complete_L_def in_set_conv_nth wf1_Complete wf_bin1_def wf_bins1_def by fastforce  
 qed

lemma step_fun_inv1: 
  assumes ne: "as \<noteq> []"
  and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
shows "WL_inv (WorkList as' l3 m3)"
proof-
  from ne obtain a ass where P: "as = a#ass"
    by (meson neq_Nil_conv)
  let ?step = "(if is_complete a then Complete_L Bs a else Predict_L a (length Bs))"
  from P show ?thesis using WL_minus_inv[of "(union_LWL ?step (WorkList (a#ass) l1 m1))" "(insert (WorkList bs l2 m2) a)"] sf by auto
qed

lemma step_fun_inv2: 
  assumes ne: "as \<noteq> []"
  and inv: "WL_inv (WorkList bs l2 m2)"
  and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
shows "WL_inv (WorkList bs' l4 m4)"
proof-
  from ne obtain a ass where P: "as = a#ass"
    by (meson neq_Nil_conv)
  then show ?thesis using insert_WL_inv1[of "(WorkList bs l2 m2)" a] sf inv by auto
qed
  
lemma step_fun_wf: 
  assumes ne: "as \<noteq> []"
  and wf: "wf_bins1 (map set Bs)" "wf1_WL (WorkList as l1 m1) (length Bs)"
  and inv: "WL_inv (WorkList as l1 m1)" "WL_inv (WorkList bs l2 m2)"
  and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"  
  shows "wf1_WL (WorkList as' l3 m3) (length Bs)"
proof -  
  from assms obtain a ass where P: "as = a # ass"
    by (meson neq_Nil_conv)
  let ?step = "(if is_complete a then Complete_L Bs a else Predict_L a (length Bs))"
  have "wf_state1 a (length Bs)" using P assms by (auto simp add: wf_bin1_def)
  then have "wf_bin1 (set ?step) (length Bs)" using assms wf1_Predict_L wf1_Complete_L by auto
  then have 1: "wf_bin1 ((set as \<union> set ?step) - (set bs \<union> {a})) (length Bs)" 
    using wf_bin1_def wf by auto
  have "set as' = (set ass \<union> set ?step) - (set bs \<union> {a})"
    using P inv sf test[of a ass l1 m1 bs l2 m2 Bs as'] by blast
  then show ?thesis using P 1 by auto
qed

lemma step_fun_wf2: 
  assumes ne: "as \<noteq> []"
  and wf: "wf1_WL (WorkList as l1 m1) (length Bs)" "wf1_WL (WorkList bs l2 m2) (length Bs)"
  and inv: "WL_inv (WorkList bs l2 m2)"
  and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
  shows "wf1_WL (WorkList bs' l4 m4) (length Bs)"
proof-
  from \<open>as \<noteq> []\<close> obtain a ass where P: "as = a#ass" by (meson neq_Nil_conv)
  then have "set bs' = set bs \<union> {a}" using inv sf P WL_insert1[of "(WorkList bs l2 m2)" a] by auto
  then show ?thesis using assms P by (auto simp add: wf_bin1_def)
qed

(*"wf_WL (WorkList bs l2 m2) (length Bs)"*)
lemma steps_sound:
  assumes wf: "wf1_WL (WorkList as l1 m1) (length Bs)"  "wf_bins1 (map set Bs)"
  and inv: "WL_inv (WorkList as l1 m1)" "WL_inv (WorkList bs l2 m2)"
  and step: "steps Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = Some ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
shows "((step_rel (map set Bs))^**) (set as, set bs) ({},set bs')"
proof -
  let ?P1 = "\<lambda>(wl1,wl2). WL_inv wl1 \<and> WL_inv wl2"
  let ?P2 = "\<lambda>(wl1,wl2). ((step_rel (map set Bs))^**) (set as, set bs) (set (list wl1),set (list wl2)) \<and> wf1_WL wl1 (length Bs) \<and> wf_bins1 (map set Bs)"
  let ?P = "\<lambda>(wl1,wl2). ?P1 (wl1, wl2) \<and> ?P2 (wl1, wl2)"
  let ?b = "\<lambda>(wl1, wl2). (list wl1) \<noteq> []"
  let ?c = "\<lambda>(wl1, wl2). step_fun Bs (wl1,wl2)"

  have 1: "(?P1 (wl1,wl2) \<Longrightarrow> ?b (wl1,wl2) \<Longrightarrow> ?P1 (?c (wl1,wl2)))" for wl1 wl2
  proof-
    assume assm: "?P1 (wl1,wl2)" and ne: "?b (wl1,wl2)"
    obtain xs k1 n1 ys k2 n2 where P: "wl1 = (WorkList xs k1 n1) \<and> wl2 = (WorkList ys k2 n2)"
      by (meson Earley_Gw.WL_inv.cases)
    obtain xs' k1' n1' ys' k2' n2' where c: "?c (wl1, wl2) = ((WorkList xs' k1' n1'), (WorkList ys' k2' n2'))"
      by (metis Earley_Gw.WL_inv.cases surj_pair)
    obtain x xss where "xs = x#xss" using ne P
      using list.exhaust by auto
    then show ?thesis using step_fun_inv1 step_fun_inv2 P c assm
      by (metis case_prod_conv list.distinct(1))
  qed

  have 2: "(?P (wl1,wl2) \<Longrightarrow> ?b (wl1,wl2) \<Longrightarrow> ?P2 (?c (wl1,wl2)))" for wl1 wl2
  proof-
    assume assm: "?P (wl1,wl2)" and ne: "?b (wl1,wl2)"
    obtain xs k1 n1 ys k2 n2 where P: "wl1 = (WorkList xs k1 n1) \<and> wl2 = (WorkList ys k2 n2)"
      by (meson Earley_Gw.WL_inv.cases)
    obtain xs' k1' n1' ys' k2' n2' where c: "?c (wl1, wl2) = ((WorkList xs' k1' n1'), (WorkList ys' k2' n2'))"
      by (metis Earley_Gw.WL_inv.cases surj_pair)
    obtain x xss where "xs = x#xss" using ne P
      using list.exhaust by auto
    then show ?thesis using step_fun_wf P c assm step_fun_sound
      by (smt (verit) Earley_Gw.WorkList.sel(1) case_prod_conv list.distinct(1) rtranclp.simps)
  qed

  have "(?P (wl1,wl2) \<Longrightarrow> ?b (wl1,wl2) \<Longrightarrow> ?P1 (?c (wl1,wl2)))" for wl1 wl2
    using 1 by auto
  then have 3: "(?P (wl1,wl2) \<Longrightarrow> ?b (wl1,wl2) \<Longrightarrow> ?P (?c (wl1,wl2)))" for wl1 wl2
    using 2
    by (metis (no_types, lifting) case_prodI2)

  have stop: "as' = []" using step while_option_stop[of ?b ?c "((WorkList as l1 m1),(WorkList bs l2 m2))"] by (auto simp add: steps_def)

  have "?P ((WorkList as l1 m1),(WorkList bs l2 m2))" using wf inv by auto
  then have "?P ((WorkList as' l3 m3), (WorkList bs' l4 m4))"using 
      while_option_rule[of ?P _ _ "((WorkList as l1 m1),(WorkList bs l2 m2))" "((WorkList as' l3 m3), (WorkList bs' l4 m4))"] 3
    by (smt (verit) case_prodE case_prod_conv local.step steps_def)
  then show ?thesis using stop by auto     
qed

lemma steps_sound1: 
  assumes wf: "wf1_WL (WorkList as l1 m1) (length Bs)"  "wf_bins1 (map set Bs)"
  and inv: "WL_inv (WorkList as l1 m1)"
  and step: "steps Bs ((WorkList as l1 m1),WL_empty (length Bs)) = Some (B',C)" 
shows "((step_rel (map set Bs))^**) (set as,{}) ({},set (list C))"
proof-
  have 1: "WL_inv (WL_empty (length Bs))"
    by (simp add: empty_inv)
  have 2: "wf1_WL (WL_empty (length Bs)) (length Bs)" by (simp add: WL_empty_def wf_bin1_def)
  show ?thesis using steps_sound 1 2 assms
    by (metis (no_types, lifting) WorkList.exhaust set_WorkList.elims set_WL_empty upsize_list upsize_list1)
qed
 

lemma step_fun_inv1_wl: 
  assumes ne: "(list wl1) \<noteq> []"
  and sf: "step_fun Bs (wl1,wl2) = (wl1', wl2')"
shows "WL_inv wl1'"
  using step_fun_inv1 wl_decomp
  by (metis Earley_Gw.WorkList.sel(1) ne sf)

lemma step_fun_inv2_wl: 
  assumes ne: "(list wl1) \<noteq> []"
  and inv: "WL_inv wl2"
  and sf: "step_fun Bs (wl1,wl2) = (wl1', wl2')"
shows "WL_inv wl2'"
 using step_fun_inv2 wl_decomp
  by (metis inv ne sf upsize_list upsize_list1)
  
lemma step_fun_wf_wl: 
  assumes ne: "(list wl1) \<noteq> []"
  and wf: "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)"
  and inv: "WL_inv wl1" "WL_inv wl2"
  and sf: "step_fun Bs (wl1,wl2) = (wl1', wl2')"  
shows "wf1_WL wl1' (length Bs)"
  using step_fun_wf wl_decomp ne wf inv sf
  by (metis upsize_list upsize_list1)

lemma step_fun_wf2_wl: 
   assumes ne: "(list wl1) \<noteq> []"
  and wf: "wf1_WL wl1 (length Bs)" "wf1_WL wl2 (length Bs)"
  and inv: "WL_inv wl2"
  and sf: "step_fun Bs (wl1,wl2) = (wl1', wl2')"
shows "wf1_WL wl2' (length Bs)"
  using wl_decomp ne wf inv sf
  by (metis step_fun_wf2 upsize_list upsize_list1)
  

lemma steps_inv1: 
  assumes inv: "WL_inv wl1"
  and step: "steps Bs (wl1,wl2) = Some (wl1', wl2')"
shows "WL_inv wl1'"
  using while_option_rule[where P= "\<lambda>(wl1,wl2). WL_inv wl1"] step_fun_inv1_wl step inv unfolding steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_inv2: 
  assumes inv: "WL_inv wl2"
  and step: "steps Bs (wl1,wl2) = Some (wl1', wl2')"
shows "WL_inv wl2'"
  using while_option_rule[where P= "\<lambda>(wl1,wl2). WL_inv wl2"] step_fun_inv2_wl step inv unfolding steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_wf1: 
  assumes wf: "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)"
  and inv: "WL_inv wl1" "WL_inv wl2"
  and sf: "steps Bs (wl1,wl2) = Some (wl1', wl2')"  
shows "wf1_WL wl1' (length Bs)"
  using while_option_rule[where P= "\<lambda>(wl1,wl2). wf1_WL wl1 (length Bs) \<and> WL_inv wl1 \<and> WL_inv wl2 \<and> wf_bins1 (map set Bs)"] 
    step_fun_wf_wl step_fun_inv1_wl step_fun_inv2_wl wf sf inv unfolding steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_wf2: 
  assumes wf: "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)" "wf1_WL wl2 (length Bs)"
  and inv: "WL_inv wl1" "WL_inv wl2"
  and sf: "steps Bs (wl1,wl2) = Some (wl1', wl2')"  
shows "wf1_WL wl2' (length Bs)"
  using while_option_rule[where P= "\<lambda>(wl1,wl2). wf1_WL wl2 (length Bs) \<and> wf1_WL wl1 (length Bs) \<and> WL_inv wl1 \<and> WL_inv wl2 \<and> wf_bins1 (map set Bs)"] 
    step_fun_wf_wl step_fun_wf2_wl step_fun_inv1_wl step_fun_inv2_wl wf sf inv unfolding steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma step_fun_sound_wl: "list wl1 \<noteq> [] \<Longrightarrow> wf1_WL wl1 (length Bs) \<Longrightarrow> WL_inv wl1 \<Longrightarrow> WL_inv wl2
 \<Longrightarrow> step_fun Bs (wl1,wl2) = (wl1', wl2')
 \<Longrightarrow> step_rel (map set Bs) (set_WorkList wl1,set_WorkList wl2) (set_WorkList wl1', set_WorkList wl2')"
  using wl_decomp step_fun_sound
  by (metis Earley_Gw.WorkList.sel(1) set_WorkList.elims)

(*lemma test3: assumes wf: "wf1_WL wl1 (length Bs)"  "wf_bins1 (map set Bs)"
  and inv: "WL_inv wl1" "WL_inv wl2"
  and sf: "steps Bs (wl1,wl2) = Some (wl1', wl2')"
shows "((step_rel (map set Bs))^** ) (set_WorkList wl1, set_WorkList wl2) ({}, set_WorkList wl2')"
  using while_option_rule[where P= "\<lambda>(wl1,wl2). ((step_rel (map set Bs))^** ) (set_WorkList wl1, set_WorkList wl2) ({}, set_WorkList wl2') \<and> wf1_WL wl1 (length Bs) \<and> WL_inv wl1 \<and> WL_inv wl2 \<and> wf_bins1 (map set Bs)"] 
    step_fun_wf_wl step_fun_wf2_wl step_fun_inv1_wl step_fun_inv2_wl step_fun_sound_wl wf sf inv unfolding steps_def
  sorry*)


(*proof -
  let ?P = "\<lambda>(B',C'). ((step_rel (map set Bs))^** ) (set B,{}) (set B',set C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)" 
  show ?thesis using while_option_rule[where P="?P"] assms[unfolded steps_def] step_fun step_fun_wf 
    by (smt (verit, ccfv_SIG) case_prodE case_prodI2 empty_set old.prod.case rtranclp.simps step_fun
        while_option_stop)
qed*)

(*lemma steps_Some[no_atp]: assumes "wf_bin1 (set as) (length Bs)" "wf_bins1 (map set Bs)"
  shows "\<exists>cs. steps Bs (as,bs) = Some([],cs)"
sorry

lemma close2_sound: assumes "wf_bin1 (set B) (length Bs)" "wf_bins1 (map set Bs)" shows "((step_rel (map set Bs))^** ) (set B, {}) ({}, set (close2_L Bs B))"
using steps_sound steps_Some unfolding close2_L_def
  by (metis assms(1,2) option.sel snd_conv)*)

end (*Earley_Gw_eps*)


context Earley_Gw
begin

(*definition wf_state where
"wf_state = undefined"

abbreviation "wf_states B \<equiv> (\<forall>x\<in>B. wf_state x)"*)

(*unused*)
lemma finite_ex_wf_state1: "finite ({x. wf_state1 x k})"
proof -
  have "{x. wf_state1 x k} \<subseteq> {x. wf_state x k}" by (auto simp add: wf_state1_def)
  then show ?thesis using finite_ex_wf_state rev_finite_subset by auto
qed


(* This is the wellfounded relation for the termination proof.
It should really be called step_fun_less but I have kept the original name.
I adapted it to work on lists rather that sets.
To simplify matters, I dropped the parameter k *)
definition step_fun_less :: "nat \<Rightarrow> ((('n, 'a) WorkList \<times> ('n, 'a) WorkList) \<times> (('n, 'a) WorkList \<times> ('n, 'a) WorkList)) set" where
"step_fun_less k = (\<lambda>(B,C). card({x. wf_state x k} - (set_WorkList B \<union> set_WorkList C))) <*mlex*> inv_image finite_psubset (set_WorkList o fst)"

lemma step_fun_less_eq: "((A, B), (C,D)) \<in> step_fun_less k \<longleftrightarrow> ((set_WorkList A, set_WorkList B), (set_WorkList C, set_WorkList D)) \<in> Close2_less k"
  by (simp add: step_fun_less_def Close2_less_def mlex_prod_def)

lemma wf_step_fun_less: "wf (step_fun_less k)"
  by (simp add: step_fun_less_def wf_mlex)

(* This is the important property of step_fun: it goes down in the Close2_less relation.
   The wf_states premises may not be 100% right *)
lemma step_fun_less_step: 
  assumes ne: "(list wl1) \<noteq>[]" 
  and wf: "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)" "wf1_WL wl2 (length Bs)"
  and inv: "WL_inv wl1" "WL_inv wl2"
shows "(step_fun Bs (wl1,wl2), (wl1,wl2)) \<in> (step_fun_less (length Bs))"
proof-
  let ?B' = "fst (step_fun Bs (wl1,wl2))"
  let ?C' = "snd (step_fun Bs (wl1,wl2))"
  have 1: "(?B', ?C') = step_fun Bs (wl1,wl2) " by simp

  obtain as l1 m1 bs l2 m2 where P1: "wl1 = (WorkList as l1 m1) \<and> wl2 = (WorkList bs l2 m2)"
    by (meson Earley_Gw.WL_inv.cases)
  obtain as' l1' m1' bs' l2' m2' where P2: "?B' = (WorkList as' l1' m1') \<and> ?C' = (WorkList bs' l2' m2')"
    by (meson Earley_Gw.WL_inv.cases)

  have "Close2 (map set Bs) (set_WorkList wl1, set_WorkList wl2) (set_WorkList ?B', set_WorkList ?C')"
    using step_fun_sound step_rel_def assms P1 P2
    by (metis "1" Earley_Gw.WorkList.sel(1) Earley_Gw.set_WorkList.simps)
  then show ?thesis using assms Close2_less_step step_fun_less_eq 1
    by (metis length_map)
qed

end (*Earley_Gw*)

context Earley_Gw_eps
begin


lemma step_fun_wf_states: 
  assumes "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)" "wf1_WL wl2 (length Bs)" "WL_inv wl1" "WL_inv wl2" "(list wl1) \<noteq> []"
  shows "\<exists>B' C'. step_fun Bs (wl1,wl2) = (B',C') \<and> WL_inv B' \<and> WL_inv C' \<and> wf1_WL B' (length Bs) \<and> wf1_WL C' (length Bs)"
proof-
  obtain as l1 m1 bs l2 m2 where P1: "wl1 = (WorkList as l1 m1) \<and> wl2 = (WorkList bs l2 m2)"
    by (meson Earley_Gw.WL_inv.cases)
  obtain as' l1' m1' bs' l2' m2' where P: "step_fun Bs (wl1,wl2) = ((WorkList as' l1' m1'),(WorkList bs' l2' m2'))"
    by (metis Earley_Gw.WorkList.exhaust surj_pair)
  then have 1: "wf1_WL (WorkList as' l1' m1') (length Bs) \<and> wf1_WL (WorkList bs' l2' m2') (length Bs)"
    using step_fun_wf step_fun_wf2 assms P1
    by (metis Earley_Gw.WorkList.sel(1))
  have "WL_inv (WorkList as' l1' m1') \<and> WL_inv (WorkList bs' l2' m2')" using P P1
    using assms(5,6) step_fun_inv1 step_fun_inv2
    by (metis Earley_Gw.WorkList.sel(1))
  then show ?thesis using P 1 by auto
qed


theorem Close2_L_NF: "\<lbrakk>wf_bins1 (map set Bs); wf1_WL wl1 (length Bs); wf1_WL wl2 (length Bs); WL_inv wl1; WL_inv wl2\<rbrakk>
  \<Longrightarrow> \<exists>wl1' wl2'. steps Bs (wl1,wl2) = Some (wl1',wl2')"
unfolding steps_def
using wf_step_fun_less[of "length Bs"]
proof (induction "(wl1,wl2)" arbitrary: wl1 wl2 rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume ne: "list wl1 = []"
    thus ?thesis by(simp add: while_option_unfold[of _ _ "(wl1,wl2)"])
  next
    let ?steps = "while_option (\<lambda>(B, C). list B \<noteq> []) (step_fun Bs)"
    assume cons: "list wl1 \<noteq> []"
    then obtain wl1' wl2'
      where "(wl1',wl2') = step_fun Bs (wl1,wl2)" and wf': "wf1_WL wl1' (length Bs)" "wf1_WL wl2' (length Bs)" and inv': "WL_inv wl1'" "WL_inv wl2'"
      using step_fun_wf_states[OF less.prems] by fastforce
    then have "((wl1',wl2'), (wl1, wl2)) \<in> step_fun_less (length Bs)"
      using cons less.prems(1,2,3,4,5) step_fun_less_step by presburger
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf' inv']
    show ?thesis
      by (simp add: \<open>(wl1',wl2') = step_fun Bs (wl1,wl2)\<close> while_option_unfold)
  qed
qed

lemma close2_L_eq_Close1: 
  assumes "wf_bins1 (map set Bs)" "wf1_WL wl (length Bs)" "WL_inv wl" 
  shows "set (close2_L Bs wl) = Close1 (map set Bs) (set (list wl))"
proof-
  have "wf1_WL (WL_empty (length Bs)) (length Bs) \<and> WL_inv (WL_empty (length Bs))"
    by (metis empty_iff empty_inv set_WL_empty wf_bin1_def)
  then obtain wl1 wl2 where D1: "steps Bs (wl,(WL_empty (length Bs))) = Some (wl1,wl2)" using assms Close2_L_NF
    by blast
  then have "(map set Bs) \<turnstile> (set (list wl), {}) \<rightarrow>* ({}, set (list wl2))" using steps_sound
    by (metis Earley_Gw.WorkList.exhaust assms(1,2,3) step_rel_def steps_sound1 upsize_list upsize_list1)
  then have DC1: "set (list wl2) = Close1 (map set Bs) (set (list wl))"
    by (simp add: Close1_subset_Close2 Close2_steps_subset_Close1' subset_antisym)
  have "set (list wl2) = set (close2_L Bs wl)" using D1 by (auto simp add: close2_L_def)
  then show ?thesis using DC1 by auto
qed

lemma close2_L_eq_close2: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_WL wl (length Bs) \<Longrightarrow> WL_inv wl \<Longrightarrow> set (close2_L Bs wl) = close2 (map set Bs) (set (list wl))"
  by (auto simp add: close2_L_eq_Close1 close2_eq_Close1)

lemma close2_L_eq_Close: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_WL wl (length Bs) \<Longrightarrow> WL_inv wl \<Longrightarrow> set (close2_L Bs wl) = Close (map set Bs) (set (list wl))"
  by (auto simp add: close2_L_eq_Close1 Close1_eq_Close)

lemma set_last: "As \<noteq> [] \<Longrightarrow> set (last As) = last (map set As)"
  by (induction As) auto

lemma length_bins_L: "length (bins_L k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma bins_L_eq_bins: "k \<le> length w \<Longrightarrow> map set (bins_L k) = bins k"
proof (induction k)
  case 0
  have "wf_bins1 (map set []) \<and> wf_bin1 (set Init_L) 0"
    by (simp add: Init_L_eq_Init wf_bin1_Init wf_bins1_def)
  then have "wf_bins1 (map set []) \<and> wf1_WL (WL_of_List 0 Init_L) 0 \<and> WL_inv (WL_of_List 0 Init_L)"
    by (metis WL_of_List_inv set_WL_of_List)
  then have "set (close2_L [] (WL_of_List 0 Init_L)) = Close [] Init"
    by (auto simp add: close2_L_eq_Close Earley_Gw.Init_L_eq_Init set_WL_of_List simp flip: set_WorkList.simps)
  then show ?case by simp
next
  case (Suc k)
  let ?Bs = "bins_L k"
  have kl: "k < length w" using Suc by auto
  then have 1: "set (Scan_L (last ?Bs) k) = (Scan (last (map set ?Bs)) k)" using Suc
    by (metis Scan_L_eq_Scan Suc_leD bins_nonempty map_is_Nil_conv set_last)
  have "wf_bin1 (set (last ?Bs)) k"
    by (metis Earley_Gw.bins_nonempty Suc.IH Suc.prems Suc_leD last_map list.map_disc_iff wf_bin1_last)
  then have 2: "wf1_WL (WL_of_List (Suc k) (Scan_L (last ?Bs) k)) (Suc k)"
    by (metis Scan_L_eq_Scan wf_bin1_Scan kl set_WL_of_List)
  have "wf_bins1 (map set (bins_L k))"
    by (simp add: Suc.IH Suc.prems Suc_leD wf_bins1_bins)
  
  then have "set (close2_L ?Bs (WL_of_List  (Suc k) (Scan_L (last ?Bs) k))) = Close (map set ?Bs) (Scan (last (map set ?Bs)) k)"
    by (metis "1" "2" Earley_Gw.set_WorkList.simps WL_of_List_inv close2_L_eq_Close length_bins_L set_WL_of_List)
  then show ?case using Suc by (auto simp add: Let_def length_bins_L)
qed 

lemma bins_L_eq_\<S>: "i \<le> k \<Longrightarrow> k \<le> length w \<Longrightarrow> set (bins_L k ! i) = \<S> i"
  using bins_eq_\<S> bins_L_eq_bins length_bins_L
  by (metis bins_L_eq_bins bins_eq_\<S>_gen le_imp_less_Suc length_bins_L nth_map)
(*lemma bins0_close2_L: "bins 0 = map set [close2_L [] Init_L]"
  by(simp flip: Close1_eq_Close add: close2_L_eq_Close1 wf_bins1_def wf_bin1_Init Init_L_eq_Init)

lemma binsSuc_close2_L:
  "k < length w \<Longrightarrow> bins (Suc k) = map set (let Bs = bins_L k in Bs @ [close2_L Bs (Scan_L (last Bs) k)])"
by(simp flip: Close1_eq_Close add: close2_eq_Close1 wf_bins1_bins wf_bin1_Scan wf_bin1_last Let_def)*) 

end


(*TODO space analyse und Zeit analyse mit eigen gesetzten laufzeiten für listenoperationen*)

(*Section space analysis*)
context Earley_Gw
begin

definition "K = Max { length (rhs r) | r. r \<in> set ps }"
definition "N = length w0"
definition "L = length ps"

lemma card_wf: 
  assumes "\<forall>p \<in> set ps. length (rhs p) \<le> k" "\<forall>x \<in> bs. wf_state x i" 
  shows "card bs \<le> (length ps) * (Suc k) * (Suc i)"
proof -
  let ?f = "\<lambda> (p, m, k). State p m k"
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
    then have "\<exists>p m k. x = State p m k \<and> p \<in> P \<and> m \<le> length (rhs p) \<and> k \<le> i \<and> i \<le> length w"
      by (metis Earley_Gw.wf_state_def state.exhaust_sel assms(2))
    then obtain p m j where x: "x = State p m j" and wf: "p \<in> P \<and> m \<le> length (rhs p) \<and> j \<le> i \<and> i \<le> length w" by blast
    then have 1: "(p, m, j) \<in> Top" using assms by (auto simp add: Top_def)
    have "?f (p, m, j) = x" using x by simp
    then show "x \<in> (\<lambda>(p, m, k). State p m k) ` Top" using 1 by blast
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

lemma card_wf1: "\<forall>x \<in> bs. wf_state x i \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
  using card_wf L_def prod_length_bound by simp

lemma card_wf_bin1: "wf_bin1 bs i \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
  using card_wf1 by (simp add: wf_bin1_def wf_state1_def)

lemma card_Si: "card (\<S> i) \<le> L * (Suc K) * (Suc i)"
  using card_wf1 wf_EarleyS by simp

lemma Si_empty: "i > length w \<Longrightarrow> \<S> i = {}"
  using wf_Earley by (fastforce simp add: \<S>_def wf_state_def)

lemma "card Earley \<le> L * (Suc K) * (Suc (length w))^2"
proof-
  let ?X = "{x. (\<exists>i \<le> length w. x = {(y, z). wf_state y z \<and> z = i})}"

  have "Earley \<subseteq> {(x, k). wf_state x k \<and> k \<le> length w}"
    using wf_Earley by (fastforce simp add: wf_state_def)
  also have "... = \<Union> {x. (\<exists>i \<le> length w. x = {(y, z). wf_state y z \<and> z = i})}" by (auto simp add: wf_state_def)
  finally have 1: "Earley \<subseteq> \<Union> {x. (\<exists>i \<le> length w. x = {(y, z). wf_state y z \<and> z = i})}".

  have 2: "x \<in> ?X \<longrightarrow> card x \<le> L * (Suc K) * (Suc (length w))" for x 
  proof
    fix x
    assume assm: "x \<in> ?X"
    then have "\<exists>i \<le> length w. \<forall>(y, z) \<in> x. wf_state y i \<and> z = i" by auto
    then obtain i where P: "\<forall>(y, z) \<in> x. wf_state y i \<and> z = i" and l: "i \<le> length w" by blast
    then have 3: "x \<subseteq> {y. wf_state y i} \<times> {i}" by fastforce

    have "finite ({y. wf_state y i} \<times> {i})"
      by (simp add: finite_ex_wf_state)
    then have "card x \<le> card {y. wf_state y i}" 
      using Groups_Big.card_cartesian_product[of "{y. wf_state y i}" "{i}"] 
            Finite_Set.card_mono[of "{y. wf_state y i} \<times> {i}"] 3 by auto
    also have "... \<le> L * (Suc K) * (Suc i)" using card_wf1 by auto
    also have "... \<le> L * (Suc K) * (Suc (length w))" using l by auto
    finally show "card x \<le> L * (Suc K) * (Suc (length w))".
  qed

  let ?f = "\<lambda>k. {(x, z). wf_state x z \<and> z = k}"
  let ?Y = "{i. i \<le> (length w)}"

  have fin: "?X = ?f ` ?Y" and "finite ?Y" by auto
  then have "card ?X  \<le> card ?Y"
    using card_image_le by force
  then have 3: "card ?X \<le> Suc (length w)" by auto

  have "\<forall> x \<in> ?X. \<exists>i. x \<subseteq> {y. wf_state y i} \<times> {i}" by fastforce
  then have "\<forall>x \<in> ?X. finite x" using finite_wf_state
    by (metis (no_types, lifting) ext finite.emptyI finite_SigmaI finite_ex_wf_state finite_insert rev_finite_subset)
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

section "Timing functions"

time_fun map
time_fun filter
time_fun nth
time_fun list_update
time_fun append
time_fun last

lemma T_filter_simps [simp,code]:
  "T_filter T_P [] = 1"
  "T_filter T_P (x # xs) = T_P x + T_filter T_P xs + 1"
  by (simp_all add: T_filter_def)

lemma T_map_simps [simp,code]:
  "T_map T_f [] = 1"
  "T_map T_f (x21 # x22) = T_f x21 + T_map T_f x22 + 1"
  by (simp_all add: T_map_def)

(*should be replaced by *)
lemma T_nth_general: "k < length as \<Longrightarrow> T_nth as k \<le> Suc k"
proof (induction k arbitrary: as)
  case 0
  then obtain a as' where "as = a # as'"
    using T_last.cases by auto
  then show ?case by auto
next
  case (Suc k)
  then obtain a as' where "as = a # as'"
    by (metis T_last.cases list.size(3) not_less_zero)
  then show ?case using Suc by auto
qed

lemma T_append_bound[simp]: "T_append as bs = Suc (length as)"
  by (induction as) auto

lemma T_last_bound[simp]: "as \<noteq> [] \<Longrightarrow> T_last as = length as"
  by (induction as) auto

time_fun snd
time_fun fst
time_fun the

fun T_rhs where
"T_rhs x = T_snd x"

lemma T_fst_0[simp]: "T_fst x = 0"
  by (metis T_fst.elims)

lemma T_snd_0[simp]: "T_snd x = 0"
  by (metis T_snd.elims)

time_fun length
(* Copy of the length time function but with options*)
fun T_size :: "'a list \<Rightarrow> nat option" where
"T_size [] = Some 1" |
"T_size (x21 # x22) = Some (the (T_size x22) + 1)"

lemma T_length_bound: "the (T_size as) = Suc (length as)"
  by (induction as) auto

time_fun_0 Earley_Gw.w

context Earley_Gw
begin

time_fun prod
time_fun dot
time_fun "from"

time_fun WorkList.list
time_fun WorkList.leng
time_fun WorkList.list_map

time_fun member
time_fun isin
time_fun empty_list_map
time_fun WL_empty
time_fun upsize
time_fun insert

time_fun union_LWL
time_fun union_WL
time_fun WL_of_List
time_fun minus_LWL
time_fun minus_WL

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
fun steps_time :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> nat \<Rightarrow> ((('n, 'a) WorkList \<times> ('n, 'a) WorkList) \<times> nat) option" where
"steps_time Bs wls y = while_option (\<lambda>((wl1,wl2),k). (list wl1) \<noteq> []) (\<lambda>((wl1,wl2),k). (step_fun Bs (wl1,wl2), k + T_step_fun Bs (wl1,wl2))) (wls, y)"

fun T_steps :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> nat" where
"T_steps Bs wls = snd (the (steps_time Bs wls 0))"

time_fun close2_L
time_fun bins_L

end (*Context Earley_Gw*)

locale Earley_Gw_eps_T = Earley_Gw_eps +
  fixes T_nth_WL:: "nat \<Rightarrow> nat"
  assumes T_nth_Bound: "(T_nth :: ('a, 'b) state list list \<Rightarrow> nat \<Rightarrow> nat) as k \<le> T_nth_WL k"
  and T_update_Bound: "(T_list_update :: ('a, 'b) state list list \<Rightarrow> nat \<Rightarrow> ('a, 'b) state list \<Rightarrow> nat) as k a \<le> T_nth_WL k"
  and mono_nth: "mono T_nth_WL" (*mono f*)
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

lemma T_the_0[simp]: "T_the (Some x) = 0"
  by simp

lemma [simp]: "T_list wl = 0"
  using Earley_Gw.T_list.elims by blast

lemma [simp]: "T_leng wl = 0"
  using Earley_Gw.T_leng.elims by blast 

lemma [simp]: "T_list_map wl = 0"
  using Earley_Gw.T_list_map.elims by blast

lemma T_is_complete_bound: "T_is_complete s = Suc (length (rhs (prod s)))"
  by (auto simp add: T_length_bound)

lemma T_next_symbol_bound: 
  assumes "prod s \<in> set ps" shows "T_next_symbol s \<le> 2*(Suc K)"
proof-
  have "length (rhs (prod s)) \<le> K" using prod_length_bound assms by auto
  then show ?thesis 
    using assms T_nth_general[of "dot s" "rhs (state.prod s)"] by (auto simp add: T_length_bound is_complete_def)
qed

lemma T_filter_bound: "\<forall>x \<in> set xs. T_P x \<le> k \<Longrightarrow> T_filter T_P xs \<le> k * length xs + length xs + 1"
proof (induction xs)
  case Nil
  then have "T_filter T_P [] = 1" by simp
  then show ?case by auto
next
  case (Cons a xs)
  then have "T_P a + T_filter T_P xs \<le> Suc (k + k * length xs + length xs)"
    by (metis Suc_eq_plus1 add.commute add.left_commute add_le_mono list.set_intros(1,2))
  then show ?case by simp
qed

lemma T_map_bound: "\<forall>x \<in> set xs. T_P x \<le> k \<Longrightarrow> T_map T_P xs \<le> k * length xs + length xs + 1"
proof (induction xs)
  case Nil
  then have "T_filter T_P [] = 1" by simp
  then show ?case by auto
next
  case (Cons a xs)
  then have "T_P a + T_map T_P xs \<le> Suc (k + k * length xs + length xs)"
    by (metis Suc_eq_plus1 add.commute add.left_commute add_le_mono list.set_intros(1,2))
  then show ?case by simp
qed

lemma T_Init_L_bound: "T_Init_L \<le> 2 * (L + 1)"
proof-
  have 1: "\<forall>x \<in> set ps. T_fst x \<le> 0" by auto
  have "T_map (\<lambda>p. 0) (filter (\<lambda>p. lhs p = S) ps) \<le> length (filter (\<lambda>p. lhs p = S) ps) + 1"
    using T_map_bound[of "(filter (\<lambda>p. lhs p = S) ps)" "(\<lambda>p. 0)" 0] by auto
  also have "... \<le> length ps + 1" by auto
  finally show ?thesis using T_filter_bound[of ps T_fst 0] 1 by (auto simp add: T_Init_L_def L_def)
qed

lemma T_Scan_L_bound: 
  assumes "k < length w0" and wf: "wf_bin1 (set Bs) l" 
  shows "T_Scan_L Bs k \<le> k + 2*(K + 2) * length Bs + 3"
proof-
  have 1: "T_nth w0 k \<le> k+1" using assms by (auto simp add: T_nth_general)

  have 2: "T_filter T_next_symbol Bs \<le> 2*(Suc K) * length Bs + length Bs + 1" 
    using T_next_symbol_bound wf T_filter_bound[of Bs T_next_symbol "2*(Suc K)"] 
    by (auto simp add: wf_bin1_def wf_state1_def wf_state_def)

  have "T_map T_mv_dot (filter (\<lambda>b. next_symbol b = Some (Tm (w0 ! k))) Bs) 
            \<le> length (filter (\<lambda>b. next_symbol b = Some (Tm (w0 ! k))) Bs) + 1"
    using T_map_bound[of _ T_mv_dot 0] by auto
  also have "... \<le> length Bs + 1" by auto

  finally show ?thesis using 1 2 by (auto simp add: Let_def)
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
  shows "T_Complete_L Bs y \<le> T_nth_WL (from y) + 2*(K + 2) * length (Bs ! from y) + 2"
proof -
  have 1: "T_nth Bs (from y) \<le> T_nth_WL (from y)" using T_nth_Bound by simp
  have "\<forall>x \<in> set (Bs ! from y). (\<lambda>b. T_next_symbol b + (T_prod y + T_fst (state.prod y))) x \<le> 2*(Suc K)"
    using assms T_next_symbol_bound 
    by (auto simp add: wf_bins1_def wf_bin1_def wf_state1_def wf_state_def)
  then have 2: "T_filter (\<lambda>b. T_next_symbol b + (T_prod y + T_fst (state.prod y))) (Bs ! from y)
            \<le> 2*(Suc K) * length (Bs ! from y) + length (Bs ! from y) + 1"
    using T_filter_bound[of "(Bs ! from y)" _ "2*(Suc K)"] by auto

  have "T_map T_mv_dot (filter (\<lambda>b. next_sym_Nt b (lhs (state.prod y))) (Bs ! from y))
          \<le> length (filter (\<lambda>b. next_sym_Nt b (lhs (state.prod y))) (Bs ! from y)) + 1"
    using T_map_bound[of _ T_mv_dot 0] by auto
  also have "... \<le> length (Bs ! from y) + 1" by auto
  finally show ?thesis using 1 2 by auto
qed

(* WorkList time bounds*)

lemma T_member_bound: "T_member xs x \<le> length xs + 1"
  by (induction xs) auto

lemma T_isin_general: "WL_inv wl \<Longrightarrow> T_isin wl x \<le> T_nth_WL (from x) + length ((list_map wl) ! from x) + 1"
proof-
  obtain as l m where "wl = WorkList as l m"
    using WL_inv.cases by blast
  then show ?thesis 
    using T_member_bound[of "m ! from x" x] T_nth_Bound[of m "from x"] by auto
qed

lemma [simp]: "T_empty_list_map k = Suc k"
  by (induction k) auto

lemma T_WL_empty_bound[simp]: "T_WL_empty k = Suc k"
  by simp

lemma T_isin_wf: 
  assumes dist: "distinct ps" and inv: "WL_inv wl" and wf: "wf1_WL wl k" 
  shows "T_isin wl x \<le> T_nth_WL (from x) + L * (Suc K) + 1"
proof-
  obtain as l m where WL: "wl = WorkList as l m"
    using WL_inv.cases by blast
  show ?thesis
  proof (cases "from x < Suc (leng wl)")
    case True
    let ?f = "\<lambda> (p, m). State p m (from x)"
    
    have 1: "from x < Suc (leng wl) \<Longrightarrow> set ((list_map wl) ! from x) = {y \<in> set as. from y = from x}" using inv WL by auto
    have 2: "from x < Suc (leng wl) \<Longrightarrow> distinct ((list_map wl) ! from x)" using inv WL by auto
  
    have fin: "finite (P \<times> {0..K})" using finite_cartesian_product finite by blast
    have inj: "inj_on ?f (P \<times> {0..K})"
      unfolding inj_on_def by simp
    have card_PK: "card (P \<times> {0..K}) = card P * (Suc K)"
      using Groups_Big.card_cartesian_product by (auto simp add: add_mult_distrib add_mult_distrib2)
    have "{y \<in> set as. from y = from x} \<subseteq> ?f ` (P \<times> {0..K})"
    proof
      fix xa
      assume "xa \<in> {y \<in> set as. from y = from x}"
      then obtain p d where XA: "xa = State p d (from x) \<and> xa \<in> set as"
        by (metis (mono_tags, lifting) T_prod.cases mem_Collect_eq state.sel(3))
      then have "p \<in> P \<and> d \<le> K" using prod_length_bound[of p] wf WL by (auto simp add: wf_bin1_def wf_state1_def wf_state_def)
      then show "xa \<in> ?f ` (P \<times> {0..K})" using XA by auto
    qed
    
    then have "card {y \<in> set as. from y = from x} \<le> (card P) * (Suc K)" using fin
      using surj_card_le[of "(P \<times> {0..K})"] by (auto simp add: card_PK)
    then have "from x < Suc (leng wl) \<Longrightarrow> length ((list_map wl) ! from x) \<le> (card P) * Suc K" using 1 2
      using distinct_card by (fastforce)
    then have "from x < Suc (leng wl) \<Longrightarrow> length ((list_map wl) ! from x) \<le> L * Suc K"
      using distinct_card dist by (fastforce simp add: L_def)
    then show ?thesis using True inv T_isin_general[of wl x] by auto
  next
    case False
    then show ?thesis using WL by auto
  qed
qed


lemma T_insert_less: 
  assumes "distinct ps" "WL_inv wl" "wf1_WL wl k" and le: "from x < Suc (leng wl)" 
  shows "T_insert wl x \<le> 3 * T_nth_WL (from x) + L * (Suc K) + 1"
proof-
  obtain as l m where "wl = WorkList as l m"
    using WL_inv.cases by blast
  then have "T_insert wl x \<le> T_isin wl x + T_nth m (from x) + T_list_update m (from x) (x # m ! from x)" using le by auto
  also have "... \<le> T_nth_WL (from x) + L * (Suc K) + 1 + T_nth_WL (from x) + T_nth_WL (from x)" 
    using assms T_isin_wf[of wl k x] T_nth_Bound[of m "from x"] T_update_Bound[of m "from x" "x # m ! from x"] by auto
  finally show ?thesis by auto
qed

lemma wf1_WL_insert: "WL_inv wl \<Longrightarrow> wf1_WL wl k \<Longrightarrow> wf_state1 x k \<Longrightarrow> wf1_WL (insert wl x) k"
  using WL_insert1 wf_bin1_def by auto

            
lemma wf1_WL_union_LWL: "WL_inv wl \<Longrightarrow> wf1_WL wl k \<Longrightarrow> wf_bin1 (set xs) k \<Longrightarrow> wf1_WL (union_LWL xs wl) k"
  using LWL_union wf_bin1_def by fastforce

lemma T_union_LWL_wf: "distinct ps \<Longrightarrow> WL_inv wl \<Longrightarrow> wf1_WL wl (leng wl) \<Longrightarrow> wf_bin1 (set as) (leng wl) 
  \<Longrightarrow> T_union_LWL as wl \<le> (length as) * (3 * T_nth_WL (leng wl) + L * (Suc K) + 2) + 1"
proof (induction as arbitrary: wl)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then have 1: "WL_inv (union_LWL as wl) \<and> wf1_WL (union_LWL as wl) (leng wl)" using LWL_union_inv wf1_WL_union_LWL
    by (metis list.set_intros(2) wf_bin1_def)
  have wf_from: "\<forall>x \<in> set (a#as). from x < Suc (leng wl)" using Cons by (auto simp add: wf_bin1_def wf_state1_def wf_state_def)
  then have 2: "from a < Suc (leng (union_LWL as wl))" using Cons leng_LWL_union by auto
  have 3: "from a \<le> leng wl" using wf_from by simp
  have "T_union_LWL (a#as) wl = T_union_LWL as wl + T_insert (union_LWL as wl) a + 1" by simp
  also have "... \<le> (length as) * (3 * T_nth_WL (leng wl) + L * (Suc K) + 2) + 1 + 3 * T_nth_WL (from a) + L * (Suc K) + 1 + 1" 
    using Cons T_insert_less[of "union_LWL as wl" "leng wl" a] 1 2 by (fastforce simp add: wf_bin1_def)
  also have "... \<le> (length as) * (3 * T_nth_WL (leng wl) + L * (Suc K) + 2) + 1 + 3 * T_nth_WL (leng wl) + L * (Suc K) + 1 + 1"
    using mono_nth 3 by (auto simp add: incseqD)
  finally show ?case by auto
qed

lemma [simp]: "T_WL_empty k = k + 1"
  by (induction k) auto

lemma [simp]: "leng (WL_empty k) = k"
  by (induction k) (auto simp add: WL_empty_def)

lemma wf1_WL_empty: "wf1_WL (WL_empty k) l"
  using set_WL_empty by (auto simp add: wf_bin1_def)

lemma wf1_WL_minus_LWL: "WL_inv wl \<Longrightarrow> wf_bin1 (set xs) k \<Longrightarrow> wf1_WL (minus_LWL n xs wl) k"
  using LWL_minus by (auto simp add: wf_bin1_def)

lemma leng_minus_LWL: "\<forall>x \<in> set xs. from x < Suc k \<Longrightarrow> leng (minus_LWL k xs wl) = k"
  using leng_WL_insert by (induction xs) auto

lemma T_minus_LWL_wf: "distinct ps \<Longrightarrow> wf1_WL wl k \<Longrightarrow>  WL_inv wl \<Longrightarrow> wf_bin1 (set as) k
  \<Longrightarrow> T_minus_LWL k as wl \<le> (length as) * (4 * T_nth_WL k + 2*L * (Suc K) + 4) + k + 2 + length as"
proof (induction as)
  case Nil
  then show ?case by (auto simp del: T_WL_empty.simps)
next
  case (Cons a as)
  then have 1: "wf_bin1 (set as) k" by (auto simp add: wf_bin1_def)
  have 2: "WL_inv (minus_LWL k as wl) \<and> wf1_WL (minus_LWL k as wl) k" using Cons wf1_WL_minus_LWL
    using "1" LWL_minus_inv by blast
  have 4: "\<forall>x \<in> set (a#as). from x < Suc k" using Cons by (auto simp add: wf_bin1_def wf_state1_def wf_state_def)
  then have 3: "from a < Suc (leng (minus_LWL k as wl))" by (auto simp add: leng_minus_LWL)
  have "T_minus_LWL k (a#as) wl \<le> T_isin wl a + T_minus_LWL k as wl + T_insert (minus_LWL k as wl) a + 1" by auto
  also have "... \<le> T_nth_WL (from a) + L * (Suc K) + 1 + T_minus_LWL k as wl + T_insert (minus_LWL k as wl) a + 1" 
    using Cons T_isin_wf by auto
  also have "... \<le> T_nth_WL (from a) + L * (Suc K) + 1 + (length as) * (4 * T_nth_WL k + 2*L * (Suc K) + 4) + k + 2 + length as + T_insert (minus_LWL k as wl) a + 1"
    using Cons 1 by auto
  also have "... \<le> T_nth_WL (from a) + L * (Suc K) + 1 + (length as) * (4 * T_nth_WL k + 2*L * (Suc K) + 4) + k + 2 + length as + 3 * T_nth_WL (from a) + L * (Suc K) + 1 + 1"
    using T_insert_less[of "minus_LWL k as wl" k a] Cons 2 3 by linarith
  also have "... \<le> T_nth_WL k + L * (Suc K) + 1 + (length as) * (4 * T_nth_WL k + 2*L * (Suc K) + 4) + k + 1 + length as + 3 * T_nth_WL k + L * (Suc K) + 2 + 1"
    using mono_nth 4 by (auto simp add: incseqD)
  also have "... \<le> (length (a#as)) * (4 * T_nth_WL k + 2*L * (Suc K) + 4) + k + 2 + (length (a#as))" by simp
  finally show ?case by simp
qed

lemma T_minus_WL_wf: "distinct ps \<Longrightarrow> wf1_WL wl1 (leng wl1) \<Longrightarrow> WL_inv wl1 \<Longrightarrow> WL_inv wl2 \<Longrightarrow> wf1_WL wl2 (leng wl1)
  \<Longrightarrow> T_minus_WL wl1 wl2 \<le> (length (list wl1)) * (4 * T_nth_WL (leng wl1) + 2*L * (Suc K) + 4) + (leng wl1) + 2 + length (list wl1)"
  using T_minus_LWL_wf[of wl2 "leng wl1" "list wl1"] by auto

(*List procedures are distinct*)

lemma distinct_Init: 
  assumes "distinct ps" shows "distinct Init_L"
proof -                                           
  have "inj_on (\<lambda> p. State p 0 0) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. State p 0 0) ps)" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Init_L_def distinct_map_filter)
qed

lemma distinct_Predict_L: 
  assumes "distinct ps" shows "distinct (Predict_L x k)"
proof -                                           
  have "inj_on (\<lambda>p. State p 0 k) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. State p 0 k) ps)" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Predict_L_def distinct_map_filter)
qed

lemma distinct_Complete_L: 
  assumes "distinct (Bs ! from y)" shows "distinct (Complete_L Bs y)"
proof -                                           
  have "inj_on mv_dot (set (Bs ! from y))"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel state.expand state.inject)
  then have "distinct (map mv_dot (Bs ! from y))" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Complete_L_def distinct_map_filter)
qed

lemma distinct_Scan_L: 
  assumes "distinct B" shows "distinct (Scan_L B k)"
proof -                                           
  have "inj_on mv_dot (set B)"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel state.expand state.inject)
  then have "distinct (map mv_dot B)" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Scan_L_def distinct_map_filter)
qed

lemma wfbin1_impl_wfbin: "wf_bin1 xs k \<Longrightarrow> wf_bin xs k"
  by (auto simp add: wf_bin1_def wf_state1_def)

lemma mult_mono_mix: "i \<le> (j :: nat) \<Longrightarrow> k * i * l \<le> k * j * l"
  by simp

(* actual time bounds*)

lemma T_step_fun_bound: assumes "(list wl1) \<noteq> []" "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf1_WL wl1 (length Bs)" "WL_inv wl1" "leng wl1 = length Bs"
  "wf1_WL wl2 (length Bs)" "WL_inv wl2" "leng wl2 = length Bs"
shows "T_step_fun Bs (wl1, wl2) 
    \<le> L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
proof-
  obtain bs l m where WL1: "wl1 = WorkList bs l m"
    using WL_inv.cases by blast
  obtain b bss where bbs: "bs = b#bss" using assms WL1
    using Earley_Gw.WorkList.sel(1) T_last.cases by blast

  have from_b: "from b \<le> length Bs"
    using assms by (simp add: WL1 bbs wf_bin1_def wf_state1_def wf_state_def)

  let ?step = "if is_complete b then Complete_L Bs b else Predict_L b (length Bs)"
  let ?t_step = "(if is_complete b then T_Complete_L Bs b else the (T_size Bs) + T_Predict_L b (length Bs))"
  have t_step: "?t_step \<le> T_nth_WL (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2 + Suc (length Bs)"
  proof (cases)
    assume complete: "is_complete b"
    then have 1: "from b < length Bs" using assms
      using assms by (simp add: bbs WL1 wf_bin1_def wf_state1_def)
    then have 2: "distinct (Bs ! from b)" using assms
      by simp
    have "wf_bin1 (set (Bs ! from b)) (from b)" using assms 1
      by (simp add: wf_bins1_def)
    then have "length (Bs ! from b) \<le> L * (Suc K) * (Suc (from b))" 
      using card_wf1 2
      by (metis card_wf_bin1 distinct_card)
    then have 4: "length (Bs ! from b) \<le> L * (Suc K) * (Suc (length Bs))" using 1
      by (meson Suc_le_mono le_trans mult_le_mono2 nat_less_le)

    have "T_Complete_L Bs b \<le> T_nth_WL (from b) + 2 * (K + 2) * length (Bs ! from b) + 2"
      using assms T_Complete_L_bound 1 by (auto simp add: WL1 bbs simp del: T_Complete_L.simps)
    also have "... \<le> T_nth_WL (from b) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2" 
      using mult_le_mono2[OF 4]
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) add_le_mono1 nat_add_left_cancel_le)
    also have "... \<le> T_nth_WL (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2"
      using mono_nth 1 by (auto simp add: incseqD)
    finally have "T_Complete_L Bs b \<le> T_nth_WL (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2".
    then show ?thesis using complete by simp
  next
    assume incomplete: "\<not>is_complete b"
    have t_pred: "T_Predict_L b (length Bs) \<le> 2 * (K + 2) * L + 2" 
      using T_Predict_L_bound assms by (simp add: L_def WL1 bbs wf_bin1_def wf_state1_def wf_state_def)
    have t_size: "the (T_size Bs) = Suc (length Bs)" by (simp add: T_length_bound)

    show ?thesis using t_pred t_size incomplete by auto
  qed

  have "the (T_size (rhs (state.prod b))) = Suc (length (rhs (prod b)))"
    by (simp add: T_length_bound)
  then have 6: "the (T_size (rhs (state.prod b))) \<le> Suc K" 
    using prod_length_bound[of "prod b"] assms by (auto simp add: WL1 bbs wf_bin1_def wf_state1_def wf_state_def)

  have wfStep: "wf_bin1 (set ?step) (length Bs)"
    using assms wf1_Complete_L[of Bs b] wf1_Predict_L[of b "length Bs"] WL1 bbs wfbin1_impl_wfbin by (auto simp add: wf_bin1_def)
  have "is_complete b \<Longrightarrow> distinct (Bs ! from b)" using assms
      by (simp add: wf_bin1_def wf_state1_def WL1 bbs)
  then have lengthStep: "length (?step) \<le> L * (Suc K) * (Suc (length Bs))" 
    using card_wf1[of "set (?step)" "length Bs"] assms distinct_Complete_L distinct_Predict_L wfStep
    by (simp add: distinct_card wfbin1_impl_wfbin)
  then have "T_union_LWL (?step) wl1 \<le> length (?step) * (3 * T_nth_WL (length Bs) + L * Suc K + 2) + 1"
    using T_union_LWL_wf[of wl1 ?step] assms wfStep  by (auto simp add: WL1)
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (3 * T_nth_WL (length Bs) + L * Suc K + 2) + 1"
    using mult_le_mono1[OF lengthStep]
    using add_le_mono1 by blast
  finally have 7: "T_union_LWL ?step wl1 \<le> L * (Suc K) * (Suc (length Bs)) * (3 * T_nth_WL (length Bs) + L * Suc K + 2) + 1".

  have "T_insert wl2 b \<le> 3 * T_nth_WL (from b) + L * Suc K + 1"
    using T_insert_less[of wl2 _ b] from_b assms by auto
  also have "... \<le> 3 * T_nth_WL (length Bs) + L * Suc K + 1"
    using mono_nth from_b by (auto simp add: incseqD)
  finally have 8: "T_insert wl2 b \<le> 3 * T_nth_WL (length Bs) + L * Suc K + 1".

  have wf_Comp_union: "wf1_WL (union_LWL ?step wl1) (length Bs)"
    using assms wfStep wf1_WL_union_LWL by presburger
  have inv_Comp_union: "WL_inv (union_LWL ?step wl1)"
    using LWL_union_inv assms by auto
  obtain bs' l' m' where decomp: "(union_LWL ?step wl1) = WorkList bs' l' m'"
    using WL_inv.cases by blast
  then have length_Comp_union: "length bs' \<le> L * (Suc K) * (Suc (length Bs))"
    using card_wf_bin1[of "set bs'" "length Bs"] wf_Comp_union inv_Comp_union by (auto simp add: distinct_card)
  have "\<forall>x\<in>set ?step. from x < Suc (length Bs)" 
    using wfStep by (cases "is_complete b") (auto simp add: wf_bin1_def wf_state1_def wf_state_def)
  then have l': "l' = length Bs"
    using leng_LWL_union assms(7) decomp
    by (metis Earley_Gw.WorkList.sel(2))
  have wf_ins_b: "wf1_WL (insert wl2 b) (length Bs)" 
    using assms wf1_WL_insert
    by (metis Earley_Gw.WorkList.sel(1) WL1 bbs list.set_intros(1) set_WorkList.simps wf1_WL_insert wf_bin1_def)
  have inv_ins_b: "WL_inv (insert wl2 b)"
    by (simp add: assms(9) insert_WL_inv1)

  let ?minus = "T_minus_WL (union_LWL ?step wl1) (local.insert wl2 b)"
  have "?minus \<le> length bs' * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 4) + length Bs + 2 + length bs'"
    using T_minus_WL_wf decomp inv_Comp_union wf_Comp_union l' wf_ins_b inv_ins_b
    by (metis Earley_Gw.WorkList.sel(1,2) assms(2))
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 4) + length Bs + 2 + L * (Suc K) * (Suc (length Bs))"
    using length_Comp_union mult_le_mono1
    using add_le_mono add_le_mono1 by presburger
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 5) + length Bs + 2"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"]
    by auto
  finally have 9: "?minus \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 5) + length Bs + 2".

  have "T_step_fun Bs (wl1, wl2) \<le> the (T_size (rhs (state.prod b))) + ?t_step +
  T_union_LWL ?step wl1 +
   T_insert wl2 b + T_minus_WL (union_LWL ?step wl1) (local.insert wl2 b) +
   T_insert wl2 b" by (auto simp add: Let_def WL1 bbs simp del: T_Complete_L.simps T_Predict_L.simps T_minus_WL.simps)

  also have "... \<le> Suc K + T_nth_WL (length Bs) + 2 * (K + 2) * L * (Suc K) * Suc (length Bs) + 2 + Suc (length Bs)
    + L * Suc K * Suc (length Bs) * (3 * T_nth_WL (length Bs) + L * Suc K + 2) + 1
    + 3 * T_nth_WL (length Bs) + L * Suc K + 1 + L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 5) + length Bs + 2 +
   3 * T_nth_WL (length Bs) + L * Suc K + 1" using t_step 6 7 8 9 by linarith

  also have "... \<le> Suc K + 2 * (K + 2) * L * (Suc K) * Suc (length Bs)
    + L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7)
    + 7 * T_nth_WL (length Bs) + 2* L * Suc K + 2 * Suc (length Bs) + 7"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  also have "... = Suc K + L * (Suc K) * Suc (length Bs) * 2 * (K + 2)
    + L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7)
    + 7 * T_nth_WL (length Bs) + 2* L * Suc K + 2 * Suc (length Bs) + 7"
    by (smt (verit) mult.assoc mult.commute)
  also have "... = L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  finally show ?thesis.
qed

lemma leng_WL_minus: 
  assumes inv: "WL_inv wl1" shows "leng (minus_WL wl1 wl2) = leng wl1"
proof-
  obtain as l m where "wl1 = WorkList as l m"
    using wl_decomp by blast
  then show ?thesis using inv leng_minus_LWL by (auto simp add: minus_WL_def)
qed

lemma leng_step_fun1: 
  assumes "list wl1 \<noteq> []" "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)" "WL_inv wl1" 
          "step_fun Bs (wl1, wl2) = (wl1', wl2')" "leng wl1 = length Bs" 
  shows "leng wl1' = length Bs"
proof-
  obtain as l m where WL1: "wl1 = WorkList as l m"
    using wl_decomp by blast
  then obtain a ass where aas: "list wl1 = a#ass"
    using assms T_last.cases by auto
  let ?step = "if is_complete a then Complete_L Bs a else Predict_L a (length Bs)"
  have "wf_bin1 (set ?step) (length Bs)" using wf1_Predict_L wf1_Complete_L assms aas
    by (smt (verit, ccfv_threshold) list.set_intros(1) set_WorkList.elims wf_bin1_def)
  then have 1: "\<forall> x \<in> set ?step. from x < Suc (leng wl1)" 
    using assms by (cases "is_complete a") (auto simp add: wf_bin1_def wf_state1_def wf_state_def)
  have "wl1' = minus_WL (union_LWL ?step wl1) (insert wl2 a)" using assms aas by (auto simp add: WL1)
  then show ?thesis using assms 1 leng_LWL_union leng_WL_minus LWL_union_inv by auto
qed

lemma leng_step_fun2: 
  assumes "list wl1 \<noteq> []" "WL_inv wl1" "step_fun Bs (wl1, wl2) = (wl1', wl2')" 
          "leng wl1 = length Bs" "leng wl2 = length Bs" 
  shows "leng wl2' = length Bs"
    using leng_WL_insert assms by (cases wl1, cases "list wl1") auto

lemma step_fun_dist: 
  assumes "list wl1 \<noteq> []" "WL_inv wl2" "step_fun Bs (wl1, wl2) = (wl1', wl2')" 
  shows "set_WorkList wl1' \<inter> set_WorkList wl2' = {}"
proof-
  obtain a as l m bs k n where WL: "wl1 = WorkList (a#as) l m \<and> wl2 = WorkList bs k n"
    using wl_decomp assms
    by (metis Earley_Gw.WorkList.sel(1) neq_Nil_conv)
  let ?step = "if is_complete a then Complete_L Bs a else Predict_L a (length Bs)"
  have "wl1' = minus_WL (union_LWL ?step wl1) (insert wl2 a)" using assms WL by auto
  then have "set_WorkList wl1' \<inter> set_WorkList (insert wl2 a) = {}" 
    using assms WL_minus insert_WL_inv1 by auto
  then show ?thesis using assms WL by auto
qed

lemma length_step_fun2: 
  assumes "list wl1 \<noteq> []" "WL_inv wl2" "step_fun Bs (wl1, wl2) = (wl1', wl2')" 
          "set_WorkList wl1 \<inter> set_WorkList wl2 = {}" 
  shows "length (list wl2') = Suc (length (list wl2))"
proof-
  obtain a as l m where WL1: "wl1 = WorkList (a#as) l m"
    using assms by (metis Earley_Gw.WorkList.sel(1) T_last.cases wl_decomp)
  obtain bs k n where WL2: "wl2 = WorkList bs k n"
    using wl_decomp by blast
  have "wl2' = insert wl2 a" using assms WL1 by auto
  then have "list wl2' = a#bs" using assms isin_WL1 by (auto simp add: WL1 WL2 Let_def simp del: isin.simps)

  then show ?thesis by (simp add: WL2)
qed

lemma steps_time_time: assumes 
    dist_ps: "distinct ps" 
and wf_Bs:  "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" 
and wl1_assms:  "wf1_WL wl1 (length Bs)" "WL_inv wl1" "leng wl1 = length Bs"
and wl2_assms:  "wf1_WL wl2 (length Bs)" "WL_inv wl2" "leng wl2 = length Bs"
and dist_wls: "set_WorkList wl1 \<inter> set_WorkList wl2 = {}"
and step:  "steps_time Bs (wl1,wl2) k = Some ((wl1',wl2'), k')" "k \<le> (length (list wl2)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
  shows "k' \<le> (length (list wl2')) * (L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)" (*and "wf1_WL wl2' (length Bs)" and "WL_inv wl2'"*)
proof -
  let ?C = "L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
  let ?P3 = "\<lambda>((wl1',wl2'),k). wf1_WL wl1' (length Bs) \<and> wf1_WL wl2' (length Bs) \<and> wf_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((wl1',wl2'),k). wf1_WL wl1' (length Bs) \<and> wf1_WL wl2' (length Bs) \<and> wf_bins1 (map set Bs) \<and> WL_inv wl1' \<and> WL_inv wl2' 
        \<and> leng wl1' = length Bs \<and> leng wl2' = length Bs \<and> set_WorkList wl1' \<inter> set_WorkList wl2' = {} \<and> (\<forall>i < length Bs. distinct (Bs ! i)) \<and> distinct ps"
  let ?P2 = "\<lambda>((wl1',wl2'),k). k \<le> (length (list wl2')) * (?C)"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((wl1,wl2),k). (list wl1) \<noteq> [])"
  let ?c = "\<lambda>((wl1,wl2),k). (step_fun Bs (wl1,wl2), k + T_step_fun Bs (wl1,wl2))"


  have init: "?P ((wl1,wl2), k)" using assms by auto

  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y
    by (smt (verit) case_prodI2' case_prod_conv step_fun_inv1_wl step_fun_inv2_wl step_fun_wf2_wl step_fun_wf_wl leng_step_fun1 leng_step_fun2 step_fun_dist)
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_step_fun Bs (a, b) \<le> ?C" using T_step_fun_bound by auto
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "step_fun Bs (a,b) = (a', b')" by auto
    then have "length (list b') = Suc (length (list b))" using length_step_fun2 assms by auto
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
  then show "k' \<le> (length (list wl2')) * ?C"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((wl1,wl2),k)", where t="((wl1',wl2'), k')"] assms init by auto
  (*show "wf_bin1 (set C') (length Bs)"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto
  show "distinct C'"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto*)
qed

theorem steps_time_NF: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_WL wl1 (length Bs) \<Longrightarrow> wf1_WL wl2 (length Bs) \<Longrightarrow> WL_inv wl1 \<Longrightarrow> WL_inv wl2 
  \<Longrightarrow> \<exists>wl1' wl2' k'. steps_time Bs (wl1,wl2) k = Some ((wl1',wl2'),k') \<and> steps Bs (wl1, wl2) = Some (wl1', wl2')"
using wf_step_fun_less[of "length Bs"]
proof (induction "(wl1,wl2)" arbitrary: wl1 wl2 k rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "list wl1 = []"
    thus ?thesis by(simp add: while_option_unfold steps_def)
  next
    let ?steps = "while_option (\<lambda>(as,bs). list as \<noteq> []) (step_fun Bs)"
    assume cons: "list wl1 \<noteq> []"
    then obtain wl1' wl2'
      where "(wl1',wl2') = step_fun Bs (wl1,wl2)" and wf': "wf1_WL wl1' (length Bs)" "wf1_WL wl2' (length Bs)" and inv': "WL_inv wl1'" "WL_inv wl2'"
      using step_fun_wf_states[OF less.prems] by auto
    then have "((wl1',wl2'), (wl1, wl2)) \<in> step_fun_less (length Bs)" using less.prems
      by (simp add: step_fun_less_step \<open>list wl1 \<noteq> []\<close>)
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf' inv']
    show ?thesis
      by (simp add: \<open>(wl1', wl2') = step_fun Bs (wl1, wl2)\<close> while_option_unfold steps_def)
  qed
qed

lemma T_steps_bound: assumes
  "distinct ps" "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)" "wf1_WL wl2 (length Bs)" "WL_inv wl1" "WL_inv wl2"
  "\<forall>i < length Bs. distinct (Bs ! i)"  "set_WorkList wl1 \<inter> set_WorkList wl2 = {}" "leng wl1 = length Bs" "leng wl2 = length Bs"
shows "T_steps Bs (wl1, wl2) \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
proof-
  obtain wl1' wl2' k' where P: "steps_time Bs (wl1,wl2) 0 = Some ((wl1',wl2'),k') \<and> steps Bs (wl1, wl2) = Some (wl1', wl2')"
    using steps_time_NF assms by blast
  have "wf1_WL wl2' (length Bs) \<and> WL_inv wl2'"
    using P assms(2,3,4,5,6) steps_wf2 steps_inv2 by blast
  then have 1: "length (list wl2') \<le> L * Suc K * Suc (length Bs)"
    using card_wf_bin1 distinct_card[of "list wl2'"] WL_inv1
    by fastforce
  have "k' \<le> (length (list wl2')) * (L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
    using steps_time_time[of Bs wl1 wl2 0] assms P by simp
  also have "... \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
    using P mult_le_mono1[OF 1] by auto
  finally show ?thesis using P by simp
qed

lemma T_close2_L_bound: 
assumes "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)"  "wf1_WL wl (length Bs)" "WL_inv wl" "leng wl = length Bs"
shows "T_close2_L Bs wl \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_WL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K) + 2* Suc (length Bs)"
proof-
  obtain wl1' wl2' where "steps Bs (wl, WL_empty (length Bs)) = Some (wl1', wl2')"
    using Close2_L_NF Earley_Gw.empty_inv assms(2,4,5) wf1_WL_empty by blast
  then show ?thesis using T_steps_bound[of Bs wl "WL_empty (length Bs)"] empty_inv set_WL_empty 
        wf1_WL_empty assms T_length_bound[of Bs] by (auto simp del: T_WL_empty.simps)
qed

lemma wf1_Init_L: "wf_bin1 (set Init_L) 0"
  by (simp add: Init_L_eq_Init wf_bin1_Init)

lemma wf1_Scan_L: "k < length w \<Longrightarrow> wf_bin1 (set as) k \<Longrightarrow> wf_bin1 (set (Scan_L as k)) (Suc k)"
  using wf_bin1_Scan
  by (simp add: Scan_L_eq_Scan)

lemma "k < length w \<Longrightarrow> wf_bin (set as) k \<Longrightarrow> wf_bin1 (set (Scan_L as k)) (Suc k)"
  by (auto simp add: wf_state_def wf_bin1_def Scan_L_def wf_state1_def mv_dot_def next_symbol_def is_complete_def)

lemma "i < k \<and> k \<le> length w \<Longrightarrow> wf_bin (set ((bins_L k) ! i)) i"
  by (simp add: bins_L_eq_\<S> wf_EarleyS)

lemma wf_Scan_L: "k < length w \<Longrightarrow> wf_bin (set as) k \<Longrightarrow> wf_bin (set (Scan_L as k)) k"
  by (auto simp add: Scan_L_def mv_dot_def next_symbol_def wf_state_def is_complete_def)

lemma length_Init_L: "length Init_L \<le> L"
  by (auto simp add: Init_L_def L_def)

lemma length_Scan_L: "length (Scan_L as k) \<le> length as"
  by (auto simp add: Scan_L_def)

lemma leng_WL_of_List: "\<forall>x \<in> set as. from x < Suc k \<Longrightarrow> leng (WL_of_List k as) = k"
  using WL_of_List_def leng_LWL_union by auto

lemma wf1_WL_of_List: "wf_bin1 (set as) k \<Longrightarrow> wf1_WL (WL_of_List l as) k"
  using set_WL_of_List by auto

lemma distinct_close2: 
  assumes "wf_bins1 (map set Bs)" "wf1_WL wl (length Bs)" "WL_inv wl" 
  shows "distinct (close2_L Bs wl)"
proof-
  obtain wl1 wl2 where "steps Bs (wl, WL_empty (length Bs)) = Some (wl1, wl2)"
    using empty_inv wf1_WL_empty Close2_L_NF assms by blast
  then show ?thesis using steps_inv2[of " WL_empty (length Bs)"] 
      WL_inv1[of "wl2"] close2_L_def empty_inv by (auto simp add: close2_L_def)
qed

lemma distinct_bins_L: "k \<le> length w \<Longrightarrow> distinct ps \<Longrightarrow> i < Suc k \<Longrightarrow> distinct ((bins_L k) ! i)"
proof(induction k arbitrary: i)
  case 0
  then show ?case using distinct_Init distinct_close2
    using WL_of_List_inv set_WL_of_List wf1_Init_L wf_bins1_def by auto
next
  case (Suc k)
  then have 1: "i < Suc k \<longrightarrow> distinct (bins_L (Suc k) ! i)" using length_bins_L by (auto simp add: Let_def nth_append_left)

  have 2: "wf_bins1 (map set (bins_L k))" using "Suc.prems"(1)
    by (simp add: bins_L_eq_bins wf_bins1_bins)
  have "wf_bin1 (set (last (bins_L k))) k" using "Suc.prems"(1)
    by (metis Suc_leD Zero_not_Suc bins_L_eq_bins last_map length_bins_L list.size(3) wf_bin1_last)
  then have 3: "wf_bin1 (set (Scan_L (last (bins_L k)) k)) (Suc k)"
    using Scan_L_eq_Scan Suc.prems(1) wf_bin1_Scan by auto
  have 5: "distinct (close2_L (bins_L k) (WL_of_List (Suc k) (Scan_L (last (bins_L k)) k)))" using 2 3 Suc distinct_close2
    using WL_of_List_inv length_bins_L wf1_WL_of_List by presburger

  have "\<not> i < Suc k \<longrightarrow> i = Suc k" using Suc by auto
  then show ?case using 1 5 using nth_append_length[of "bins_L k"] length_bins_L by (auto simp add: Let_def)
qed

lemma bound_help: 
  assumes "a > 0" "b > 0" 
  shows "(x+2)^3 * (a+b) + 7*(x::nat) + (x+2)^2 * a + (x+2) * b + 16 \<le> (x+3)^3 * (a+b)"
proof-
  have "(x+2)^3 * (a+b) + 7*x + (x+2)^2 * a + (x+2) * b + 16
         = (x+2) * (x+2) *(x+2) * (a+b) + 7* x+ (x+2) * (x+2) * a + (x+2) * b + 16"
    by (auto simp add: numeral_eq_Suc)
  then have 1: "(x+2)^3 * (a+b) + 7*x + (x+2)^2 * a + (x+2) * b + 16 
    = (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x + (x*x + 4*x + 4) * a + (x+2) * b + 16"
    by (auto simp add: add_mult_distrib)
  also have "... \<le> (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x + (x*x + 4*x + 4) * (a +b) + (x+2) * (a+b) + 16"
    by (auto simp add: add_mult_distrib add_mult_distrib2)
  also have "... \<le> (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x * (a+b) + (x*x + 4*x + 4) * (a +b) + (x+2) * (a+b) + 16"
    using assms by auto
  also have "... \<le> (x*x*x + 6*x*x + 12*x + 8) * (a + b) + 7*x * (a+b) + (x*x + 4*x + 4) * (a +b) + (x+2) * (a+b) + 8*(a+b)"
    using assms by auto
  also have "... = (x*x*x + 7*x*x + 24*x + 22) * (a + b)" by (auto simp add: add_mult_distrib add_mult_distrib2)
  finally have 1: "(x+2)^3 * (a+b) + 7*x + (x+2)^2 * a + (x+2) * b + 16 \<le> (x*x*x + 7*x*x + 24*x + 22) * (a + b)".
  have "(x+3)^3 *(a+b) = Suc(Suc(Suc x)) * Suc(Suc(Suc x)) * Suc(Suc(Suc x)) * (a+b)"
    by (auto simp add: numeral_eq_Suc)
  then have 2: "(x+3)^3 * (a+b) = (x*x*x + 9*x*x + 27*x + 27) * (a+b)"
    by (auto simp add: add_mult_distrib)
  show ?thesis using 1 2 by (auto simp add: add_mult_distrib add_mult_distrib2)
qed


lemma T_bins_L_bound: "distinct ps \<Longrightarrow> k \<le> length w \<Longrightarrow> T_bins_L k 
  \<le> (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K)))"
proof (induction k)
  case 0
  then have 1: "T_union_LWL Init_L (WL_empty 0) \<le> length Init_L * (3 * T_nth_WL (0) + L * Suc K + 2) + 1" 
    using T_union_LWL_wf[of "(WL_empty 0)" Init_L] empty_inv wf1_WL_empty wf1_Init_L wfbin1_impl_wfbin[of "set Init_L"] wf1_Init_L by auto
  have "leng (WL_of_List 0 Init_L) = 0" 
    using leng_WL_of_List wf1_Init_L by (auto simp add: wf_bin1_def wf_state1_def wf_state_def)
  then have "T_close2_L [] (WL_of_List 0 Init_L) \<le> (L * Suc K) * (L * Suc K * (7 * T_nth_WL (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (0) + 2* L * Suc K + 9 + Suc K) + 2"
    using 0 T_close2_L_bound[of "[]" "(WL_of_List 0 Init_L)"] wf1_Init_L wf1_WL_of_List
        WL_of_List_inv by (auto simp add: wf_bins1_def simp del: T_close2_L.simps)
  then have "T_bins_L 0 \<le> length Init_L * (3 * T_nth_WL (0) + L * Suc K + 2) + 1 + (L * Suc K) * (L * Suc K * (7 * T_nth_WL (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (0) + 2* L * Suc K + 9 + Suc K) + 2+2" 
    unfolding T_bins_L.simps T_WL_of_List.simps T_WL_empty.simps T_empty_list_map.simps 
    using 1 by (linarith)
  also have "... =  length Init_L * (3 * T_nth_WL (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * T_nth_WL (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (0) + 2* L * Suc K + 9 + Suc K) + 5" using length_Init_L by auto
  also have "... \<le> L * (3 * T_nth_WL (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * T_nth_WL (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (0) + 2* L * Suc K + 9 + Suc K) + 5"
    using length_Init_L
    using add_le_mono1 mult_le_cancel2 by presburger
  also have "... \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (0) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (0) + 3* L * Suc K + 9 + Suc K)))"
    by (auto simp add: add_mult_distrib add_mult_distrib2)
  finally have 2: "T_bins_L 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (0) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (0) + 3* L * Suc K + 9 + Suc K)))".

  have "7 * T_nth_WL (0) + 3* L * Suc K + 9 + 2 * (K + 2)
      \<le> 7 * T_nth_WL (1) + 3* L * Suc K + 9 + 2 * (K + 2)" using mono_nth by (auto simp add: incseq_SucD)
  then have 3: "Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (0) + 3* L * Suc K + 9 + 2 * (K + 2))
    \<le> Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (1) + 3* L * Suc K + 9 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * T_nth_WL (0) + 3* L * Suc K + 9 + Suc K \<le> 2 * (K + 2) + 10 * T_nth_WL (1) + 3* L * Suc K + 9 + Suc K"
    using mono_nth by (auto simp add: incseq_SucD)
  then have 4: "(Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (0) + 3* L * Suc K + 9 + Suc K)) \<le> (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (1) + 3* L * Suc K + 9 + Suc K))"
    using mult_le_mono2 by blast

  have "T_bins_L 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (1) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (1) + 3* L * Suc K + 9 + Suc K)))"
    using 2 3 4 by auto

  then show ?case by (auto simp add: numeral_eq_Suc)
next
  case (Suc k)
  have 1: "the (T_size (bins_L k)) = k + 2"
    by (auto simp add: length_bins_L T_length_bound)

  have 2: "T_last (bins_L k) = Suc k"
    by (metis T_last_bound Zero_not_Suc length_bins_L list.size(3))

  have wf_last: "wf_bin1 (set (last (bins_L k))) k" using Suc wf_bin1_last
    by (metis Suc_leD Zero_not_Suc bins_L_eq_bins length_bins_L list.size(3) set_last)
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
  have length_Scan: "length (Scan_L (last (bins_L k)) k) \<le> L * Suc K * Suc k"
    using length_Scan_L length_last dual_order.trans by blast
  have "T_WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k) \<le> k+2 + length (Scan_L (last (bins_L k)) k) * (3 * T_nth_WL (Suc k) + L * Suc K + 2) + 1"
    using T_union_LWL_wf[of "(WL_empty (Suc k))"] empty_inv wf1_WL_empty wf_Scan Suc wfbin1_impl_wfbin
    by (auto simp add: length_bins_L)
  also have "... \<le> k+2 + L * Suc K * Suc k * (3 * T_nth_WL (Suc k) + L * Suc K + 2) + 1" using length_Scan mult_le_mono1[OF length_Scan]
    using add_le_mono1 nat_add_left_cancel_le by presburger
  finally have 4: "T_WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k) \<le> L * Suc K * Suc k * (3 * T_nth_WL (Suc k) + L * Suc K + 2) + k + 3" by linarith

  have wf_bins_L: "wf_bins1 (map set (bins_L k))" using wf_bins1_bins bins_L_eq_bins Suc by auto
  have wf_WL_of_List: "wf1_WL (WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k))  (Suc k)"
    using set_WL_of_List wf_Scan wfbin1_impl_wfbin
    using Suc.prems(2) wf1_Scan_L wf_last by auto
  have leng_WL_of_List: "leng (WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k)) = (Suc k)"
    using wf_Scan leng_WL_of_List wf_bin1_def wf_state1_def wf_state_def length_bins_L
    by (metis le_imp_less_Suc)
  have 5: "T_close2_L (bins_L k) (WL_of_List  (length (bins_L k)) (Scan_L (last (bins_L k)) k))  
            \<le> (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) + 2* Suc (Suc k)"
    using T_close2_L_bound[of "bins_L k" "WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k)"] wf_bins_L Suc distinct_bins_L wf_WL_of_List WL_of_List_inv leng_WL_of_List 
    by (auto simp add: length_bins_L simp del: T_close2_L.simps)

  have 6: "T_append (bins_L k) [close2_L (bins_L k) (WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k))] = k+2"
    by (auto simp add: length_bins_L)

  have "L * Suc K * Suc (Suc k) * 2 * Suc (Suc k) \<le>  L * Suc K * L * Suc K * Suc (Suc k) * 2* Suc (Suc k)" using le_square[of "L * Suc K"]
    by (metis (no_types, lifting) mult.assoc mult_le_mono1)
  then have test': "L * Suc K * Suc (Suc k) * 2 * Suc (Suc k) \<le> L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * 2"
    by (metis (no_types, lifting) mult.commute mult.left_commute)
  have test'': "L \<le> Suc L" by simp

  have "T_bins_L (Suc k) \<le> T_bins_L k + k + 2 + Suc k + k + L * Suc K * Suc k * 2 * (K + 2) + 3
        + L * Suc K * Suc k * (3 * T_nth_WL (Suc k) + L * Suc K + 2) + k + 3
        + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) + 2* Suc (Suc k)
      + k + 2 + 1" unfolding T_bins_L.simps Let_def using 1 2 3 4 5 6 by linarith

  
  
  also have "... = T_bins_L k + 7*k + 16 + L * Suc K * Suc k * 2 * (K + 2)
            + L * Suc K * Suc k * (3 * T_nth_WL (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    by auto

  also have "... = T_bins_L k + 7*k + 16
            + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_WL (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2 by auto

  also have "... = T_bins_L k + 7*k + 16 + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_WL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))" "L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))"
                                "7 * T_nth_WL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K"]
    by (smt (verit, del_insts) Suc_1 ab_semigroup_add_class.add_ac(1) ab_semigroup_mult_class.mult_ac(1) add_2_eq_Suc' add_Suc_shift add_mult_distrib2 group_cancel.add2
        mult.commute mult.left_commute)

  also have "... = T_bins_L k + 7*k + 16 + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_WL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * 2 * Suc (Suc k)
    + L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] by auto

  also have "... \<le>  T_bins_L k + 7*k + 16 + L * Suc K * (Suc (Suc k)) * (2 * (K + 2) + 3 * T_nth_WL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * 2
    + L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using mult_mono_mix[of "Suc k" "(Suc (Suc k))" "L * Suc K" "2 * (K + 2) + 3 * T_nth_WL (Suc k) + L * Suc K + 2"] test' by presburger

  also have "... \<le> T_bins_L k + 7*k + 16 
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] 
          add_mult_distrib2[of "L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k)"] by auto

  also have "... = T_bins_L k + 7*k + 16 
    + L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (metis (no_types, opaque_lifting) mult.assoc)

  also have "... \<le> T_bins_L k + 7*k + 16 
    + Suc L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + Suc L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K))" 
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_L k + 7*k + 16 
    + L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K)"
    by (metis (no_types, lifting) dual_order.refl mult.commute mult.left_commute mult.assoc)
  also have "... \<le> T_bins_L k + 7*k + 16 
    + Suc L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K)"
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_L k + 7*k + 16 
    + Suc (Suc k) * Suc (Suc k) * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (smt (verit, ccfv_threshold) mult.commute mult.left_commute verit_comp_simplify1(2))
  also have "... \<le> T_bins_L k + 7*k + 16 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (metis add_2_eq_Suc' le_refl power2_eq_square)
  finally have short: "T_bins_L (Suc k) \<le> T_bins_L k + 7*k + 16 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K))".

  let ?a = "Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))"
  let ?b = "Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K)"

  have ff: "T_nth_WL (Suc k) \<le> T_nth_WL (Suc (Suc k))" using mono_nth
    by (simp add: incseq_SucD)
  then have "(7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)) \<le> (7 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))"
    by auto
  then have a1: "?a \<le> Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K \<le> 2 * (K + 2) + 10 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K"
    using ff by auto
  then have b1: "?b \<le> Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)"
    using mult_le_mono2 by blast

  have "T_bins_L (Suc k) \<le> (k+2)^3 * ((?a) + (?b))
    + 7*k + 16 
    + (k+2)^2 * ?a
    + Suc (Suc k) * ?b" using short Suc by simp

  also have "... \<le> (k+3)^3 * ((?a) + (?b))"
    using bound_help[of ?a ?b k] by simp

  also have "... \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)))"
    using a1 b1 by simp
  finally have "T_bins_L (Suc k)
  \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)))".

  (*  (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_WL (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) *)

  then show ?case
    by (metis add_Suc_shift eval_nat_numeral(3))
qed
(*algebra_simps*)

definition C1 where "C1 = 28 * (L+1)^3 * (K+1)^3"
definition C2 where "C2 = 17 * (L+1)^2 * (K+1)^2"

corollary nice_T_bins_L_bound: 
  assumes "distinct ps" "k \<le> length w" 
  shows "T_bins_L k \<le> C1 *(k+2)^3 + C2 * (k+2)^3 * T_nth_WL (k+1)"
proof-
  have "T_bins_L k \<le> (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_WL (Suc k) + 3* L * Suc K + 9 + Suc K)))"
    using T_bins_L_bound assms by auto
  also have "... = (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * 7 * T_nth_WL (k+1) + Suc L * Suc K * 10 * T_nth_WL (k+1)) 
    + (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 3* L * Suc K + 9 + Suc K)))"
    by (auto simp add: algebra_simps)
  also have "... \<le> (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * 17 * T_nth_WL (k+1))
                  + (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * (6* L * Suc K + 18 + 5 * (K + 2)))"
    by (auto simp add: algebra_simps)
  also have "... \<le> 17 * (L+1) * (L+1) * (K+1) * (K+1) * (k+2)^3 * T_nth_WL (k+1)
                  + 28 * (L+1) * (L+1) * (L+1) * (K+1) * (K+1) * (K+1) * (k+2)^3"
    by (auto simp add: algebra_simps)
  also have "... = 17 * (L+1)^2 * (K+1)^2 * (k+2)^3 * T_nth_WL (k+1)
                  + 28 * (L+1)^3 * (K+1)^3 * (k+2)^3"
    by (auto simp add: monoid_mult_class.power2_eq_square monoid_mult_class.power3_eq_cube algebra_simps)
  finally show ?thesis by (auto simp add: C1_def C2_def)
qed

end

context Earley_Gw
begin

fun recognized_L :: "('n, 'a) state list \<Rightarrow> bool" where
"recognized_L [] = False" |
"recognized_L (a#as) = (is_final a \<or> recognized_L as)"

definition earley where
"earley _ = recognized_L (last (bins_L (length w)))"

lemma recognized_set: "recognized_L as = (\<exists>x \<in> set as. is_final x)"
  by (induction as) auto

time_fun is_final
time_fun recognized_L
time_fun earley

(*parse Bäume für eindeutige Grammatiken*)
(*parse-tree in AFP*)

end

context Earley_Gw_eps
begin

lemma earley_eq_recognized_Earley: "earley y \<longleftrightarrow> recognized Earley"
proof
  assume "earley y"
  then have "\<exists>x \<in> set (last (bins_L (length w))). is_final x" using recognized_set earley_def
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
  then show "earley y" using recognized_set earley_def by metis
qed

theorem correctness_earley:
  shows "earley y \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using correctness_Earley earley_eq_recognized_Earley by metis 
end

context Earley_Gw_eps_T
begin

lemma T_final_bound: "prod x \<in> set ps \<Longrightarrow> T_is_final x \<le> Suc K"
  by (auto simp add: T_length_bound prod_length_bound)

lemma T_recognized_bound: "wf_bin (set as) k \<Longrightarrow> T_recognized_L as \<le> Suc (length as) * (K+2)"
proof (induction as)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then show ?case using T_final_bound[of a] by (auto simp del: T_is_final.simps simp add: wf_state_def)
qed

definition C1' where "C1' = 30 * (L+1)^3 * (K+1)^3"

lemma 
  assumes dist: "distinct ps" 
  shows "T_earley y \<le> C1' *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_WL ((length w)+1)"
proof-
  have wf_last: "wf_bin1 (set (last (bins_L (length w)))) (length w)" using wf_bin1_last
    by (metis bins_L_eq_bins length_bins_L lessI less_Suc_eq_le list.size(3) not_less_zero set_last)
  then have length_last: "length (last (bins_L (length w))) \<le> L * Suc K * Suc (length w)"
    using distinct_bins_L card_wf_bin1 last_conv_nth length_bins_L distinct_card
    by (metis diff_Suc_1 dist interval_class.less_imp_less_eq_dec lessI list.size(3) nat.distinct(1))
  have "T_recognized_L (last (bins_L (length w))) \<le> Suc (length (last (bins_L (length w)))) * (K+2)"
    using wf_last wfbin1_impl_wfbin T_recognized_bound by metis
  also have "... \<le> Suc (L * Suc K * Suc (length w)) * (K+2)" using length_last
    using Suc_le_mono mult_le_mono1 by presburger
  finally have 1: "T_recognized_L (last (bins_L (length w))) \<le> Suc (L * Suc K * Suc (length w)) * (K+2)".

  from dist have 2: "T_bins_L (length w) \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_WL ((length w)+1)"
    using nice_T_bins_L_bound by auto

  have 3: "T_last (bins_L (length w)) = Suc (length w)"
    using T_last_bound length_bins_L
    by (metis Zero_not_Suc list.size(3))

  have 4: "the (T_size w) = Suc (length w)"
    using T_length_bound by auto

  have "T_earley y \<le> T_bins_L (length w) + T_last (bins_L (length w)) + T_recognized_L(last (bins_L (length w))) + the (T_size w)"
    by auto
  also have "... \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_WL ((length w)+1) + Suc (length w) + Suc (length w) + Suc (L * Suc K * Suc (length w)) * (K+2)" 
    using 1 2 3 4 by linarith
  also have "... \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_WL ((length w)+1) + 2 * (L+1) * (L+1) * (L+1) * (K+1) * (K+1) * (K+1) * ((length w)+2) * ((length w)+2) * ((length w)+2)"
    by (auto simp add: algebra_simps)
  also have "... = C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_WL ((length w)+1) + 2 * (L+1)^3 * (K+1)^3 * ((length w)+2)^3"
    by (auto simp add: monoid_mult_class.power3_eq_cube algebra_simps)
  also have "... = C1' *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_WL ((length w)+1)"
    using C1_def C1'_def by auto
  finally show ?thesis.
qed
end

context Earley_Gw
begin
type_synonym ('c, 'd) item = "('c, 'd) state \<times> ('c, 'd) tree list"

abbreviation state :: "('n,'a) item \<Rightarrow> ('n, 'a) state" where
  "state \<equiv> fst"

abbreviation tree :: "('n,'a) item \<Rightarrow> ('n, 'a) tree list" where
  "tree \<equiv> snd"

definition Parse_Predict :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> ('n,'a) item set" where 
"Parse_Predict x k = { (State r 0 k, []) | r. r \<in> P \<and> next_sym_Nt x (lhs r) }"

lemma Parse_Predict_state: "Parse_Predict x k = Predict x k \<times> {[]}"
  by (auto simp add: Parse_Predict_def Predict_def)

definition Parse_Complete :: "('n, 'a) item set list \<Rightarrow> ('n, 'a) item \<Rightarrow> ('n, 'a) item set" where
  "Parse_Complete Bs y = (\<lambda> (p, t). (mv_dot p, (Rule (lhs(prod (state y))) (rev (tree y)))#t)) ` {x. x \<in> Bs ! from (state y) \<and> next_sym_Nt (fst x) (lhs(prod (state y)))}"



lemma Parse_Complete_state: "from (state y) < length Bs \<Longrightarrow> state ` (Parse_Complete Bs y) = (Complete (map (\<lambda> x. state ` x) Bs) (state y))"
proof (auto simp add: Parse_Complete_def Complete_def)
  fix p t
  assume "from (state y) < length Bs" "(p, t) \<in> Bs ! from (state y)" "next_sym_Nt p (lhs (state.prod (state y)))" 
  then show "mv_dot p \<in> mv_dot ` {x \<in> state ` Bs ! from (state y). next_sym_Nt x (lhs (state.prod (state y)))}"
    by (metis (mono_tags, lifting) fst_conv imageI mem_Collect_eq)
next
  fix s t
  assume "from (state y) < length Bs" "(s, t) \<in> Bs ! from (state y)" "next_sym_Nt s (lhs (state.prod (state y)))"
  then show "mv_dot s
           \<in> state `
              (\<lambda>x. case x of (p, t) \<Rightarrow> (mv_dot p, Rule (lhs (state.prod (state y))) (rev (tree y)) # t)) `
              {x \<in> Bs ! from (state y). next_sym_Nt (state x) (lhs (state.prod (state y)))}"
    by (metis (mono_tags, lifting) fst_conv imageI mem_Collect_eq pair_imageI)
qed

definition Parse_Init :: "('n,'a) item set" where
  "Parse_Init = { (State r 0 0, []) | r. r \<in> P \<and> lhs r = (S) }"

lemma Parse_Init_state: "Parse_Init = Init \<times> {[]}"
  by (auto simp add: Parse_Init_def Init_def)

definition Parse_Scan :: "('n,'a) item set \<Rightarrow> nat \<Rightarrow> ('n,'a) item set" where
  "Parse_Scan B k = { (mv_dot (state x), (Sym (w!k))#(tree x)) | x. x \<in> B \<and> next_symbol (state x) = Some (w!k) }"


lemma Parse_Scan_state: "state ` Parse_Scan B k = Scan (state ` B) k"
proof (auto simp add: Parse_Scan_def Scan_def)
  fix s t 
  assume "next_symbol s = Some (w ! k)" "(s, t) \<in> B"
  then show "\<exists>x. mv_dot s = mv_dot x \<and> x \<in> state ` B \<and> next_symbol x = Some (w ! k)"
    by (metis fst_conv image_eqI)
next
  fix s t
  assume "next_symbol s = Some (w ! k)" "(s, t) \<in> B"
  then show "mv_dot s \<in> state ` {(mv_dot a, Sym (w ! k) # b) |a b. (a, b) \<in> B \<and> next_symbol a = Some (w ! k)}"
    by force
qed

fun wf_item :: "('n, 'a) item \<Rightarrow> nat \<Rightarrow> bool" where
"wf_item x k = (wf_state (state x) k \<and> (\<forall>t \<in> (set (tree x)). parse_tree P t) \<and> fringes (rev (tree x)) = slice (from (state x)) k w \<and> (map root (rev (tree x)) = \<alpha> (state x)))"

fun wf_item1 :: "('n, 'a) item \<Rightarrow> nat \<Rightarrow> bool" where
"wf_item1 x k = (wf_state1 (state x) k \<and> (\<forall>t \<in> (set (tree x)). parse_tree P t) \<and> fringes (rev (tree x)) = slice (from (state x)) k w \<and> (map root (rev (tree x)) = \<alpha> (state x)))"
  
fun wf_parse_bin :: "('n, 'a) item set \<Rightarrow> nat \<Rightarrow> bool" where
"wf_parse_bin xs k = (\<forall>x \<in> xs. wf_item x k)"

fun wf_parse_bin1 :: "('n, 'a) item set \<Rightarrow> nat \<Rightarrow> bool" where
"wf_parse_bin1 xs k = (\<forall>x \<in> xs. wf_item1 x k)"

definition wf_parse_bins1 :: "('n, 'a) item set list \<Rightarrow> bool" where
"wf_parse_bins1 Bs = (\<forall>k < length Bs. wf_parse_bin1 (Bs!k) k)"

lemma wf_parse_init: "wf_parse_bin (Parse_Init) 0"
  by (auto simp add: Parse_Init_def slice_drop_take wf_state_def \<alpha>_def)

lemma wf_parse_predict: "wf_item x k \<Longrightarrow> wf_parse_bin (Parse_Predict (state x) k) k"
  by (auto simp add: Parse_Predict_def wf_state_def slice_drop_take \<alpha>_def)

lemma "wf_parse_bin1 xs k \<Longrightarrow> wf_bin1 (state ` xs) k"
  by (auto simp add: wf_bin1_def)

lemma wf_parse_bins1_impl_bins1: "wf_parse_bins1 xs \<Longrightarrow> wf_bins1 (map ((`) state) xs)"
  by (auto simp add: wf_bins1_def wf_parse_bins1_def wf_bin1_def)

lemma \<alpha>_mv_dot: "next_sym_Nt x A \<Longrightarrow> \<alpha> (mv_dot x) = \<alpha> x @ [Nt A]"
  by (auto simp add: \<alpha>_def mv_dot_def next_symbol_def is_complete_def take_Suc_conv_app_nth split: if_splits)

lemma wf_item1_impl_wf: "wf_item1 x k \<Longrightarrow> wf_item x k"
  by (simp add: wf_state1_def)

lemma wf_parse_complete: 
  assumes "wf_parse_bins1 Bs" "wf_item1 st (length Bs)" "is_complete (state st)" 
  shows "wf_parse_bin1 (Parse_Complete Bs st) (length Bs)"
  unfolding wf_parse_bin1.simps proof
  fix x
  assume "x \<in> Parse_Complete Bs st"
  then obtain a b where P: "x = (mv_dot a, Rule (lhs (state.prod (state st))) (rev (tree st)) # b) 
    \<and> (a, b) \<in> Bs ! from (state st) \<and> next_sym_Nt a (lhs (prod (state st))) \<and> from (state st) < length Bs"
    using assms by (auto simp add: Parse_Complete_def wf_state1_def wf_parse_bins1_def)
  then have wf_ab: "wf_item1 (a,b) (from (state st))" using assms by (auto simp add: wf_parse_bins1_def simp del: wf_item1.simps)
  then have 1: "wf_state1 (state x) (length Bs) \<and> (\<forall>t \<in> set (tree x). parse_tree P t)"
    using assms P by (auto simp add: wf_parse_bins1_def mv_dot_def wf_state1_def is_complete_def wf_state_def rhs_def \<alpha>_def next_symbol_def split: if_splits)
  have "fringes (rev (tree x)) = slice (from (state x)) (length Bs) w"
    using wf_ab assms(2) P
    by (auto simp add: wf_state1_def wf_state_def mv_dot_def slice_concat)
  then show "wf_item1 x (length Bs)" using assms P wf_ab 1 by (auto simp add: \<alpha>_mv_dot)
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
  from P have 1: "wf_state1 (mv_dot a) (Suc k)" using assms(1,2) 
    by (auto simp add: wf_state1_def next_symbol_def mv_dot_def is_complete_def wf_state_def split: if_splits)
  have "from a \<le> k" using P assms(2) by (auto simp add: wf_state1_def wf_state_def)
  then have 2: "fringes (rev b @ [Sym (w ! k)]) = slice (from (mv_dot a)) (Suc k) w"
    using Bfringes assms(1) by (auto simp add: slice_drop_take take_Suc_conv_app_nth mv_dot_def)
  have 3: "map root (rev b @ [Sym (w ! k)]) = \<alpha> (mv_dot a)"
    using Broots P by (auto simp add: \<alpha>_def mv_dot_def next_symbol_def is_complete_def take_Suc_conv_app_nth split: if_splits)
  then show "wf_item1 x (Suc k)" using P 1 2 3 Btree by auto
qed

inductive_set Parse_Close :: "('n,'a) item set list \<Rightarrow> ('n,'a) item set \<Rightarrow> ('n,'a) item set" for Bs B where
    Init: "x \<in> B \<Longrightarrow> x \<in> Parse_Close Bs B"
  | Predict: "\<lbrakk> x \<in> Parse_Close Bs B; x' \<in> Parse_Predict (state x) (length Bs) \<rbrakk> \<Longrightarrow> x' \<in> Parse_Close Bs B"
  | Complete: "\<lbrakk> y \<in> Parse_Close Bs B; is_complete (state y); x \<in> Parse_Complete Bs y\<rbrakk> \<Longrightarrow> x \<in> Parse_Close Bs B"

end

context Earley_Gw_eps
begin

lemma wf_parse_predict1: "wf_item1 x k \<Longrightarrow> wf_parse_bin1 (Parse_Predict (state x) k) k"
  using \<epsilon> by (auto simp add: Parse_Predict_def wf_state1_def wf_state_def is_complete_def \<epsilon>_free_def slice_drop_take \<alpha>_def )

lemma wf_parse_init1: "wf_parse_bin1 (Parse_Init) 0"
  using \<epsilon> by (auto simp add: Parse_Init_def slice_drop_take wf_state1_def wf_state_def is_complete_def \<alpha>_def \<epsilon>_free_def)

lemma wf_parse_bin_close: 
  assumes "wf_parse_bins1 Bs" "wf_parse_bin1 B (length Bs)" 
  shows "wf_parse_bin1 (Parse_Close Bs B) (length Bs)"
  unfolding wf_parse_bin1.simps proof
  fix x
  assume "x \<in> Parse_Close Bs B"
  then show "wf_item1 x (length Bs)" using assms
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

lemma PClose_incl_Close: "x \<in> Parse_Close Bs B \<Longrightarrow> wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 B (length Bs) \<Longrightarrow>  state x \<in> Close (map ((`) state) Bs) (state ` B)"
proof (induction x rule: Parse_Close.induct) 
  case (Init x)
  then show ?case by (auto simp add: Close.Init)
next
  case (Predict x x')
  then show ?case by (auto simp add: Close.Predict Parse_Predict_state)
next
  case (Complete y x)
  then have l_from: "from (state y) < length Bs" using wf_parse_bin_close[of Bs B] by (auto simp add: wf_state1_def)
  then obtain a b where P: "(a, b) \<in> Bs ! from (state y) \<and> next_sym_Nt a (lhs (state.prod (state y)))
    \<and> x = (mv_dot a, Rule (lhs (state.prod (state y))) (rev (tree y)) # b)" using Complete by (auto simp add: Parse_Complete_def)
  then have a_in: "a \<in> (map ((`) state) Bs) ! from (state y)" using l_from
    by (metis fst_conv imageI nth_map)
  then have 1: "mv_dot a \<in> Complete (map ((`) state) Bs) (state y)" using P by (auto simp add: Complete_def)
  have "(state y) \<in> Close (map ((`) state) Bs) (state ` B)" using Complete wf_parse_bin_close by blast
  then have "mv_dot a \<in> Close (map ((`) state) Bs) (state ` B)" using 1 Close.Complete Complete l_from P a_in
         by auto
  then show ?case using P 1 by (auto simp add: Close.Complete)
qed

lemma Close_incl_PClose: "x \<in> Close (map ((`) state) Bs) (state ` B) \<Longrightarrow> wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 B (length Bs) \<Longrightarrow> \<exists>b. (x, b) \<in> Parse_Close Bs B"
proof(induction x rule: Close.induct)
  case (Init x)
  then show ?case
    using Parse_Close.Init by fastforce
next
  case (Predict x x')
  then show ?case using Parse_Close.Predict Parse_Predict_state by fastforce
next
  case (Complete y x)
  then have l_from: "from y < length (map ((`) state) Bs)" using wf_parse_bin_close[of Bs B] by (auto simp add: wf_state1_def)
  then have 1: "mv_dot x \<in> Close (map ((`) state) Bs) (state ` B) \<and> (\<exists> xb. (x,xb) \<in> Bs ! (from y))" using Close.Complete Complete by auto
  then obtain xb where P_xb: "(x,xb) \<in> Bs ! (from y)" by blast
  obtain yb where P_yb: "(y, yb) \<in> Parse_Close Bs B" using Complete by auto
  then obtain xbb where "(mv_dot x,xbb) \<in> Parse_Complete Bs (y,yb)" using Complete 1 l_from P_xb by (fastforce simp add: Parse_Complete_def)
  then show ?case using Complete Parse_Close.Complete[of "(y, yb)" Bs B "(mv_dot x,xbb)"] P_yb by auto
qed

lemma PClose_eq_Close: "wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 B (length Bs) \<Longrightarrow> state ` (Parse_Close Bs B) = Close (map ((`) state) Bs) (state ` B)"
  using PClose_incl_Close Close_incl_PClose image_iff by fastforce

fun Parse_bins :: "nat \<Rightarrow> ('a, 'b) item set list" where
"Parse_bins 0 = [(Parse_Close [] Parse_Init)]" |
"Parse_bins (Suc k) = (let bs = Parse_bins k in bs @ [Parse_Close bs (Parse_Scan (last bs) k)])"

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

lemma all_f_nth_impl_map: "length xs = length ys \<Longrightarrow> \<forall>i < length xs. T_nth_WL (xs ! i) = ys ! i \<Longrightarrow>  map T_nth_WL xs = ys"
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  then have "(\<forall>i<length xs. T_nth_WL (xs ! i) = ys ! i) \<and> T_nth_WL x = y" by auto
  then show ?case using Cons by auto
qed

lemma state_Pbins_eq_bins_nth: "k \<le> length w \<Longrightarrow> i \<le> k \<Longrightarrow> state ` (Parse_bins k ! i) = bins k ! i"
proof (induction k arbitrary: i)
  case 0
  then show ?case using Parse_Init_state wf_parse_init1 PClose_eq_Close[of "[]" Parse_Init] 
    by (auto simp add: wf_parse_bins1_def)
next
  case (Suc k)
  then have map_bins: "map ((`) state) (Parse_bins k) = bins k" using all_f_nth_impl_map[of _ _ "(`) state"] by (auto simp add: length_parse_bins)
  from Suc have wf_last: "wf_parse_bin1 (last (Parse_bins k)) k" using parse_bins_wf1[of k] wf_parse_bins1_def length_parse_bins last_conv_nth
    by (metis One_nat_def Suc_leD Zero_not_Suc diff_Suc_1' eq_imp_le list.size(3) parse_bins_wf1_nth)
  then have wf_scan: "wf_parse_bin1 (Parse_Scan (last (Parse_bins k)) k) (Suc k)" using Suc wf_parse_scan by (auto simp del: wf_parse_bin1.simps)
  have state_last: "state ` last (Parse_bins k) = last (bins k)"
    by (metis Earley_Gw.bins_nonempty last_map list.map_disc_iff map_bins)
  from Suc have 1: "\<not> i \<le> k \<longrightarrow> i = Suc k" by auto
  then show ?case using Suc Parse_Scan_state PClose_eq_Close[of "Parse_bins k" "Parse_Scan (last (Parse_bins k)) k"] 
      parse_bins_wf1[of k] wf_scan map_bins state_last
    by (cases "i \<le> k") (auto simp add: Let_def length_parse_bins nth_append_left nth_append_right simp del: wf_parse_bin1.simps)
qed

lemma state_Pbins_eq_bins: "k \<le> length w \<Longrightarrow> map ((`) state) (Parse_bins k) = bins k"
  using state_Pbins_eq_bins_nth all_f_nth_impl_map[of _ _ "(`) state"] 
  by (auto simp add: length_parse_bins)

lemma "k \<le> length w \<Longrightarrow> i \<le> k \<Longrightarrow> state ` (Parse_bins k ! i) = \<S> i"
  using state_Pbins_eq_bins_nth by (simp add: bins_eq_\<S>_gen)



definition valid_parse_tree :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) sym list \<Rightarrow> 'a \<Rightarrow> ('a,'b) tree \<Rightarrow> bool" where
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


definition unambiguous :: "('a, 'b) Cfg \<Rightarrow> bool" where
"unambiguous g \<equiv> \<forall>w \<in> LangS g. \<forall> t1 t2. (valid_parse_tree (Prods g) (map Tm w) (Start g) t1 \<and> valid_parse_tree (Prods g) (map Tm w) (Start g) t2) \<longrightarrow> t1 = t2"

lemma wf_complete_imp_valid_tree: "wf_item x k \<Longrightarrow> is_complete (state x) \<Longrightarrow> valid_parse_tree P (slice (from (state x)) k w) (lhs (prod (state x))) (Rule (lhs (prod (state x))) (rev (tree x)))"
  by (auto simp add: valid_parse_tree_def wf_state1_def wf_state_def is_complete_def \<alpha>_def rhs_def)

lemma accepted_impl_valid_tree: 
  assumes "accepted" 
  shows "\<exists> s t. (s, t) \<in> Parse_bins (length w) ! (length w) \<and> valid_parse_tree P w S (Rule (lhs (prod s)) (rev t))"
proof-
  obtain x where "x \<in> \<S> (length w) \<and> is_final x" using accepted_def assms by blast
  then have P_x: "x \<in> bins (length w) ! (length w) \<and> lhs(prod x) = S \<and> from x = 0 \<and> is_complete x"
    by (auto simp add: is_final_def bins_eq_\<S>_gen)
  then have "x \<in> state  ` (Parse_bins (length w) ! (length w))" using state_Pbins_eq_bins_nth by auto
  then obtain t where bins_nth: "(x, t) \<in> Parse_bins (length w) ! (length w)" by auto
  then have "wf_item1 (x,t) (length w)" using parse_bins_wf1_nth[of "length w" "length w"] by auto
  then have "wf_item (x,t) (length w)" by (auto simp add: wf_state1_def)
  then show ?thesis using P_x bins_nth wf_complete_imp_valid_tree[of "(x,t)" "length w"] by auto
qed
  

lemma accepted_wf_cover_impl_tree: 
  assumes "accepted" "wf_parse_bin1 X (length w)" "\<forall>s \<in> \<S> (length w). \<exists>i \<in> X. fst i = s" 
  shows "\<exists>s t. (s,t) \<in> X \<and> is_final s \<and> valid_parse_tree P w S (Rule S (rev t))"
proof-
  obtain s where P_s: "s \<in> \<S> (length w) \<and> is_final s" using accepted_def assms by blast
  then obtain t where P_t: "(s, t) \<in> X \<and> lhs (prod s) = S" using assms(3)
    by (fastforce simp add: is_final_def)
  then have "valid_parse_tree P w S (Rule S (rev t))" using assms(2) P_s 
    by (auto simp add: slice_drop_take is_final_def valid_parse_tree_def wf_state1_def wf_state_def \<alpha>_def is_complete_def rhs_def)
  then show ?thesis using P_s P_t by auto
qed
end

context Earley_Gw
begin 

definition Parse_Predict_L :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> ('n,'a) item list" where 
"Parse_Predict_L x k = map (\<lambda>p. (State p 0 k, [])) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps)"


definition Parse_Complete_L :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) item \<Rightarrow> ('n, 'a) item list" where
  "Parse_Complete_L Bs y = map (\<lambda> x. let (p,t) = x in (mv_dot p, (Rule (lhs(prod (state y))) (rev (tree y)))#t)) (filter (\<lambda> x. let (p,t) = x in next_sym_Nt p (lhs(prod (state y)))) (Bs ! from (state y)))"

(*definition Parse_Complete_L :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) item \<Rightarrow> ('n, 'a) item list" where
  "Parse_Complete_L Bs y = map (\<lambda> (p, t). (mv_dot p, (Rule (lhs(prod (state y))) (rev (tree y)))#t)) (filter (\<lambda> (p, t). next_sym_Nt p (lhs(prod (state y)))) (Bs ! from (state y)))"*)

definition Parse_Init_L :: "('n,'a) item list" where
  "Parse_Init_L = map (\<lambda>p. (State p 0 0, [])) (filter (\<lambda> p. lhs p = (S)) ps)"


definition Parse_Scan_L :: "('n,'a) item list \<Rightarrow> nat \<Rightarrow> ('n,'a) item list" where
  "Parse_Scan_L Bs k = (let x = Some (Tm (w0 ! k)) in map (\<lambda> y. let (p,t) = y in (mv_dot p, (Sym (the x))#t)) (filter (\<lambda> y. let (p,t) = y in next_symbol p = x) Bs))"

(*fun Parse_step_fun :: "('n, 'a) item list list \<Rightarrow>  ('n, 'a) item list \<times> ('n, 'a) item list \<Rightarrow> ('n, 'a) item list \<times> ('n, 'a) item list" where
  "Parse_step_fun Bs ([], cs) = undefined" |
  "Parse_step_fun Bs (a#as , cs) = (let step = (if is_complete (state a) then Parse_Complete_L Bs a else Parse_Predict_L (state a) (length Bs)) in
    ( minus_L (List.union step (a#as)) (List.insert a cs), List.insert a cs))"*)


lemma PPredict_L_eq_Predict_L: "map state (Parse_Predict_L s k) = Predict_L s k"
  by (auto simp add: Parse_Predict_L_def Predict_L_def)

lemma PComplete_L_eq_Complete_L: 
  assumes "from (state b) < length Bs" 
  shows "map state (Parse_Complete_L Bs b) = Complete_L (map (map state) Bs) (state b)"
proof-
  have "map state (Parse_Complete_L Bs b)
    = map mv_dot (map state (filter (\<lambda>(p, t). next_sym_Nt p (lhs (state.prod (state b)))) (Bs ! from (state b))))" by (auto simp add: Parse_Complete_L_def)
  also have "... = map mv_dot (map state (filter (\<lambda>x. next_sym_Nt (state x) (lhs (state.prod (state b)))) (Bs ! from (state b))))"
    by (simp add: case_prod_beta')
  also have "... = map mv_dot (filter (\<lambda>x. next_sym_Nt x (lhs (state.prod (state b)))) (map state (Bs ! from (state b))))"
    using filter_map
    by (metis (no_types, lifting) ext comp_def)
  finally show ?thesis
    using assms by (auto simp add: Complete_L_def)
qed

lemma Parse_Init_L_eq_Init_L: "map state Parse_Init_L = Init_L"
  by (auto simp add: Parse_Init_L_def Init_L_def)

lemma Parse_Scan_L_eq_Scan_L: "map state (Parse_Scan_L Bs k) = Scan_L (map state Bs) k"
proof-
  have "map state (Parse_Scan_L Bs k) = map mv_dot (map state (filter (\<lambda>(p, t).  next_symbol p = Some (Tm (w0 ! k))) Bs))"
    by (auto simp add: Parse_Scan_L_def)
  also have "... = map mv_dot (map state (filter (\<lambda>x. next_symbol (state x) = Some (Tm (w0 ! k))) Bs))"
    by (simp add: case_prod_beta')
  also have "... = map mv_dot (filter (\<lambda>x. next_symbol  x = Some (Tm (w0 ! k))) (map state Bs))"
    using filter_map
    by (metis (no_types, lifting) ext comp_def)
  finally show ?thesis
    by (auto simp add: Scan_L_def)
qed

lemma PCompleteL_sub_PComplete: "from (state st) < length Bs \<Longrightarrow> set (Parse_Complete_L Bs st) \<subseteq> Parse_Complete (map set Bs) st"
  by (auto simp add: Parse_Complete_L_def Parse_Complete_def)
  
lemma wf1_Parse_Complete_L: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_item1 st (length Bs)" "is_complete (state st)" 
  shows "wf_parse_bin1 (set (Parse_Complete_L Bs st)) (length Bs)"
proof-
  have "set (Parse_Complete_L Bs st) \<subseteq> Parse_Complete (map set Bs) st"
    using assms PCompleteL_sub_PComplete by (auto simp add: wf_state1_def)
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

lemma wf1_Parse_Predict_L: "wf_item1 s k \<Longrightarrow> wf_parse_bin1 (set (Parse_Predict_L (state s) k)) k"
  using \<epsilon> by (auto simp add: Parse_Predict_L_def wf_state1_def wf_state_def slice_drop_take \<alpha>_def is_complete_def \<epsilon>_free_def)

lemma wf1_Parse_Init_L: "wf_parse_bin1 (set (Parse_Init_L)) 0"
  using \<epsilon> by (auto simp add: Parse_Init_L_def wf_state1_def wf_state_def slice_drop_take \<alpha>_def is_complete_def \<epsilon>_free_def) 
end

context Earley_Gw
begin

type_synonym ('c, 'd) ParseWL = "('c,'d) WorkList \<times> ('c,'d) tree list list"

fun ParseWL_inv :: "('n, 'a) ParseWL \<Rightarrow> bool" where
"ParseWL_inv (wl, ts) = (WL_inv wl \<and> length (list wl) = length ts)"

definition PWL_empty :: "nat \<Rightarrow> ('n, 'a) ParseWL" where
"PWL_empty k = (WL_empty k, [] )"

fun PWL_list :: "('n, 'a) ParseWL \<Rightarrow> ('n, 'a) item list" where
"PWL_list (wl, ts) = (zip (list wl) ts)"

fun ParseWL_isin :: "('n, 'a) ParseWL \<Rightarrow> ('n, 'a) item \<Rightarrow> bool" where
"ParseWL_isin (wl, ts) (s, t) = isin wl s"

fun set_ParseWL :: "('n, 'a) ParseWL \<Rightarrow> ('n, 'a) item set" where
"set_ParseWL (wl, ts) = set (zip (list wl) ts)"

fun ParseWL_insert :: "('n, 'a) ParseWL \<Rightarrow> ('n, 'a) item \<Rightarrow> ('n, 'a) ParseWL" where
"ParseWL_insert (wl, ts) (s, t) = (if isin wl s then (wl, ts) else (insert wl s, t#ts))"

fun union_LPWL :: "('n, 'a) item list \<Rightarrow> ('n, 'a) ParseWL \<Rightarrow> ('n, 'a) ParseWL" where
"union_LPWL [] pwl = pwl" |
"union_LPWL (a#as) pwl = ParseWL_insert (union_LPWL as pwl) a"

definition union_PWL :: "('n, 'a) ParseWL \<Rightarrow> ('n, 'a) ParseWL \<Rightarrow> ('n, 'a) ParseWL" where
"union_PWL pwl1 pwl2 = union_LPWL (PWL_list pwl1) pwl2"

definition PWL_of_List :: "nat \<Rightarrow> ('n, 'a) item list \<Rightarrow> ('n, 'a) ParseWL" where
"PWL_of_List k as = union_LPWL as (PWL_empty k)"

fun minus_LPWL :: "nat \<Rightarrow> ('n, 'a) item list \<Rightarrow> ('n, 'a) ParseWL \<Rightarrow> ('n, 'a) ParseWL" where
"minus_LPWL k [] pwl = PWL_empty k" |
"minus_LPWL k (a#as) pwl = (if \<not>(ParseWL_isin pwl a) then ParseWL_insert (minus_LPWL k as pwl) a else minus_LPWL k as pwl)"

definition minus_PWL :: "('n, 'a) ParseWL \<Rightarrow> ('n, 'a) ParseWL \<Rightarrow> ('n, 'a) ParseWL" where
"minus_PWL pwl1 pwl2 = minus_LPWL (leng (fst pwl1)) (PWL_list pwl1) pwl2"

fun PWL_first :: "('n,'a) ParseWL \<Rightarrow> ('n,'a) item" where
"PWL_first (wl, t#ts) = (hd (list wl), t)"

fun wf_PWL :: "('n,'a) ParseWL \<Rightarrow> nat \<Rightarrow> bool" where
"wf_PWL pwl k = wf_parse_bin1 (set_ParseWL pwl) k"

definition PWL_map_state :: "('n, 'a) ParseWL \<Rightarrow> ('n,'a) state list" where
"PWL_map_state pwl = list (fst pwl)"

lemma [simp]: "list (WL_empty k) = []"
  by (simp add: WL_empty_def)

lemma [simp]: "isin wl x \<Longrightarrow> list (insert wl x) = list wl"
  by (cases wl) auto

lemma [simp]: "\<not> isin wl x \<Longrightarrow> list (insert wl x) = x # (list wl)"
  by (cases wl) (auto simp add: Let_def)

lemma PWL_first_in_set_PWL: 
  assumes "pwl = (wl, ts)" "ts \<noteq> []" "ParseWL_inv pwl" shows "PWL_first pwl \<in> set_ParseWL pwl"
proof-
  obtain a as t tss where "list wl = a#as \<and> ts = t#tss"
    using assms by (metis ParseWL_inv.simps T_last.cases length_0_conv)
  then show ?thesis using assms by auto
qed

lemma PWL_inv_empty: "ParseWL_inv (PWL_empty k)"
  by (auto simp add: PWL_empty_def empty_inv)

lemma wf_PWL_empty: "wf_PWL (PWL_empty k) n"
  by (auto simp add: PWL_empty_def)

lemma PWL_inv_insert: "ParseWL_inv pwl \<Longrightarrow> ParseWL_inv (ParseWL_insert pwl x)"
  by (cases pwl, cases x) (auto simp add: insert_WL_inv1)

lemma wf_PWL_insert: "wf_PWL pwl k \<Longrightarrow> wf_item1 x k \<Longrightarrow> wf_PWL (ParseWL_insert pwl x) k"
  by(cases pwl, cases x) auto

lemma PWL_inv_union_LPWL: "ParseWL_inv pwl \<Longrightarrow> ParseWL_inv (union_LPWL xs pwl)"
  by (cases pwl, induction xs) (auto simp add: PWL_inv_insert)

lemma wf_union_LPWL: "wf_PWL pwl k \<Longrightarrow> wf_parse_bin1 (set xs) k \<Longrightarrow> wf_PWL (union_LPWL xs pwl) k"
  by (induction xs) (auto simp add: wf_PWL_insert simp del: wf_PWL.simps)

lemma PWL_inv_union_PWL: "ParseWL_inv pwl1 \<Longrightarrow> ParseWL_inv pwl2 \<Longrightarrow> ParseWL_inv (union_PWL pwl1 pwl2)"
  by (auto simp add: PWL_inv_union_LPWL union_PWL_def)

lemma wf_union_PWL: "wf_PWL pwl1 k \<Longrightarrow> wf_PWL pwl2 k \<Longrightarrow> wf_PWL (union_PWL pwl1 pwl2) k"
  by (metis Earley_Gw.wf_PWL.elims(1) Earley_Gw.wf_union_LPWL PWL_list.simps set_ParseWL.cases set_ParseWL.simps union_PWL_def)

lemma PWL_inv_PWL_of_List: "ParseWL_inv (PWL_of_List k xs)"
  by (simp add: PWL_inv_empty PWL_inv_union_LPWL PWL_of_List_def)

lemma wf_PWL_of_List: "wf_parse_bin1 (set xs) n \<Longrightarrow> wf_PWL (PWL_of_List k xs) n"
  using PWL_of_List_def wf_PWL_empty wf_union_LPWL by presburger

lemma PWL_inv_minus_LPWL: "ParseWL_inv (minus_LPWL k xs pwl)"
  by (induction xs) (auto simp add: PWL_inv_empty PWL_inv_insert)

lemma wf_minus_LPWL: "wf_parse_bin1 (set xs) n \<Longrightarrow> wf_PWL (minus_LPWL k xs pwl) n"
  by (induction xs) (auto simp add: wf_PWL_empty wf_PWL_insert simp del: wf_PWL.simps)

lemma PWL_inv_minus_PWL: "ParseWL_inv (minus_PWL pwl1 pwl2)"
  by (simp add: PWL_inv_minus_LPWL minus_PWL_def)

lemma wf_minus_PWL: "wf_PWL pwl1 k \<Longrightarrow> wf_PWL (minus_PWL pwl1 pwl2) k"
  by (metis PWL_list.simps minus_PWL_def set_ParseWL.elims wf_PWL.elims(2) wf_minus_LPWL)

lemma PWL_map_state_Cons2: "ParseWL_inv pwl \<Longrightarrow> PWL_map_state pwl = a#as \<Longrightarrow> \<exists>x xs. snd pwl = x#xs"
  using PWL_map_state_def
  by (metis ParseWL_inv.simps length_Suc_conv prod.collapse)

lemma PWL_map_state_Cons1: "ParseWL_inv pwl \<Longrightarrow> PWL_map_state pwl = a#as \<Longrightarrow> \<exists>x xs l m. fst pwl = WorkList (x#xs) l m"
  using PWL_map_state_Cons2
  by (metis Earley_Gw.WorkList.exhaust Earley_Gw.WorkList.sel(1) PWL_map_state_def)

(*ParseWL operations are WorkList operations*)
lemma [simp]: "fst (PWL_empty k) = WL_empty k"
  by (simp add: PWL_empty_def)
lemma [simp]: "fst (ParseWL_insert pwl x) = insert (fst pwl) (state x)"
  by (cases pwl, cases x, cases "fst pwl") auto
lemma [simp]: "fst (union_LPWL xs pwl) = union_LWL (map state xs) (fst pwl)"
  by (cases pwl,  induction xs) auto
lemma [simp]: "fst (minus_LPWL k xs pwl) = minus_LWL k (map state xs) (fst pwl)"
  by (cases pwl, induction xs) (auto)
lemma [simp]: "ParseWL_inv pwl1 \<Longrightarrow> fst (minus_PWL pwl1 pwl2) = minus_WL (fst pwl1) (fst pwl2)"
  by (cases pwl1) (auto simp add: minus_PWL_def minus_WL_def)

lemma leng_PWL_insert: assumes "wf_item x (leng (fst pwl))" shows "leng (fst (ParseWL_insert pwl x)) = leng (fst pwl)"
  using leng_WL_insert assms by (auto simp add: wf_state_def)

lemma leng_LPWL_union: "wf_parse_bin1 (set xs) (leng (fst pwl)) \<Longrightarrow> leng (fst (union_LPWL xs pwl)) = leng (fst pwl)"
  using leng_PWL_insert by (induction xs pwl rule: union_LPWL.induct) (auto simp add: wf_state1_def)


lemma set_zip_eq_length_rule: "length xs = length ys \<Longrightarrow> \<forall>x \<in> set (zip xs ys). Q (fst x) \<Longrightarrow> \<forall>x \<in> set xs. Q x"
  by (induction xs ys rule: list_induct2) auto

lemma wf_PWL_impl_wf1_WL: 
  assumes "ParseWL_inv pwl" "wf_PWL pwl k" shows "wf1_WL (fst pwl) k"
proof-
  obtain as l m ts where "pwl = (WorkList as l m, ts)"
    by (metis set_ParseWL.cases wl_decomp)
  then show ?thesis using set_zip_eq_length_rule[of as ts "\<lambda>x. wf_state1 x k"] assms 
    by (auto simp add: wf_bin1_def)
qed

lemma length_fst_PWL: assumes "ParseWL_inv pwl" "wf_PWL pwl k"
  shows "length (list (fst pwl)) \<le> L * Suc K * Suc k"
proof-
  from assms have "wf_bin1 (set_WorkList (fst pwl)) k" using wf_PWL_impl_wf1_WL by auto
  moreover have "distinct (list (fst pwl))" using assms by (cases pwl, cases "fst pwl") auto
  ultimately show ?thesis using card_wf_bin1 distinct_card
    by fastforce
qed

lemma length_snd_PWL: assumes "ParseWL_inv pwl" "wf_PWL pwl k"
  shows "length (snd pwl) \<le> L * Suc K * Suc k"
proof-
  from assms have "length (list (fst pwl)) \<le> L * Suc K * Suc k" using length_fst_PWL by simp
  then show ?thesis using assms by (cases pwl) auto
qed

fun Parse_step_fun :: "('n, 'a) item list list \<Rightarrow>  ('n, 'a) ParseWL \<times> ('n, 'a) ParseWL \<Rightarrow> ('n, 'a) ParseWL \<times> ('n, 'a) ParseWL" where
  "Parse_step_fun Bs ((wl1, []), pwl2) = undefined" |
  "Parse_step_fun Bs ((wl1, ts1), pwl2) = (let b = PWL_first (wl1, ts1) in 
    (let step = (if is_complete (state b) then Parse_Complete_L Bs b else Parse_Predict_L (state b) (length Bs)) in
    ( minus_PWL (union_LPWL step (wl1, ts1)) (ParseWL_insert pwl2 b), ParseWL_insert pwl2 b) ))"

lemma PWL_inv_parse_step1: "pwl1 = (wl1, t#ts) \<Longrightarrow> Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4) \<Longrightarrow> ParseWL_inv pwl3"
  using PWL_inv_minus_PWL by (fastforce simp add: Let_def)

lemma PWL_inv_parse_step1': "PWL_map_state pwl1 \<noteq> [] \<Longrightarrow> Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4) \<Longrightarrow> ParseWL_inv pwl1 \<Longrightarrow> ParseWL_inv pwl3"
  using PWL_inv_parse_step1 PWL_map_state_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma PWL_inv_parse_step2: "pwl1 = (wl1, t#ts) \<Longrightarrow> Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4) \<Longrightarrow> ParseWL_inv pwl2 \<Longrightarrow> ParseWL_inv pwl4"
  using PWL_inv_insert by (fastforce simp add: Let_def)

lemma PWL_inv_parse_step2': "PWL_map_state pwl1 \<noteq> [] \<Longrightarrow> Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4) \<Longrightarrow> ParseWL_inv pwl2 \<Longrightarrow> ParseWL_inv pwl1 \<Longrightarrow> ParseWL_inv pwl4"
  using PWL_inv_parse_step2 PWL_map_state_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma Pstep_fun_eq_step_fun:
  assumes step: "list wl1 \<noteq> []" "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4)" "step_fun (map (map state) Bs) (wl1, wl2) = (wl3, wl4)"
  and invs: "ParseWL_inv pwl1"
  and wf: "wf_parse_bin1 (set_ParseWL pwl1) (length Bs)"
  and eq_start: "fst pwl1 = wl1" "fst pwl2 = wl2"
  shows "fst pwl3 = wl3 \<and> fst pwl4 = wl4"
proof- 
  from step obtain a as l m where P_wl1: "wl1 = WorkList (a#as) l m"
    by (metis Earley_Gw.WorkList.sel(1) recognized_L.cases wl_decomp)
  then obtain t ts where P_ts: "pwl1 = (wl1, t#ts)" using eq_start invs(1)
    by (metis Earley_Gw.WorkList.sel(1) ParseWL_inv.simps Suc_length_conv fst_conv set_ParseWL.cases)
  have "ParseWL_inv (union_LPWL (Parse_Predict_L a (length Bs)) pwl1)" using PWL_inv_union_LPWL invs by auto
  moreover have "ParseWL_inv (union_LPWL (Parse_Complete_L Bs (a, t)) pwl1)" using PWL_inv_union_LPWL invs by auto
  ultimately show ?thesis 
    using step eq_start invs P_ts P_wl1 PPredict_L_eq_Predict_L PComplete_L_eq_Complete_L wf PWL_first_in_set_PWL 
    by (auto simp add: Let_def wf_state1_def)
qed

lemma Pstep_fun_eq_step_fun1:
  assumes step: "PWL_map_state pwl1 \<noteq> []" "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4)"
  and invs: "ParseWL_inv pwl1"
  and wf: "wf_parse_bin1 (set_ParseWL pwl1) (length Bs)"
shows "(let x = step_fun (map (map state) Bs) (fst pwl1, fst pwl2) in fst pwl3 = (fst x) \<and> fst pwl4 = (snd x))"
  using Pstep_fun_eq_step_fun
  by (metis PWL_map_state_def invs local.step(1,2) local.wf surjective_pairing)

definition Parse_steps :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) ParseWL \<times> ('n, 'a) ParseWL \<Rightarrow> (('n, 'a) ParseWL \<times> ('n, 'a) ParseWL) option" where
  "Parse_steps Bs BC = while_option (\<lambda>(B,C). PWL_map_state B \<noteq> []) (Parse_step_fun Bs) BC"


lemma Parse_steps_inv1: 
  assumes inv: "ParseWL_inv pwl1"
  and step: "Parse_steps Bs (pwl1,pwl2) = Some (pwl1', pwl2')"
shows "ParseWL_inv pwl1'"
  using while_option_rule[where P= "\<lambda>(pwl1,pwl2). ParseWL_inv pwl1"] PWL_inv_parse_step1' step inv unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma Parse_steps_inv2: 
  assumes inv: "ParseWL_inv pwl2" "ParseWL_inv pwl1"
  and step: "Parse_steps Bs (pwl1,pwl2) = Some (pwl1', pwl2')"
shows "ParseWL_inv pwl2'"
  using while_option_rule[where P= "\<lambda>(pwl1,pwl2). ParseWL_inv pwl2 \<and> ParseWL_inv pwl1"] PWL_inv_parse_step2' PWL_inv_parse_step1' step inv unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)


definition Parse_close2_L :: "('n, 'a) item list list \<Rightarrow> ('n, 'a) ParseWL \<Rightarrow> ('n, 'a) item list" where
"Parse_close2_L Bs B = PWL_list (snd (the (Parse_steps Bs (B, PWL_empty (length Bs)))))"

fun Parse_bins_L :: "nat \<Rightarrow> ('n,'a) item list list" where
"Parse_bins_L 0 = [Parse_close2_L [] (PWL_of_List 0 Parse_Init_L)]" |
"Parse_bins_L (Suc k) = (let Bs = Parse_bins_L k in Bs @ [Parse_close2_L Bs (PWL_of_List (length Bs) (Parse_Scan_L (last Bs) k))])"

end


context Earley_Gw_eps
begin

lemma wf_parse_step1: 
  assumes "pwl1 = (wl1, t#ts)" "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4)" 
  and wf_parse: "wf_parse_bins1 (map set Bs)" "wf_PWL pwl1 (length Bs)" "ParseWL_inv pwl1" 
shows "wf_PWL pwl3 (length Bs)"
proof-
  let ?b = "PWL_first (wl1, t#ts)"
  let ?step = "(if is_complete (state ?b) then Parse_Complete_L Bs ?b else Parse_Predict_L (state ?b) (length Bs))"
  from assms have 3: "pwl3 = minus_PWL (union_LPWL ?step (wl1, t#ts)) (ParseWL_insert pwl2 ?b)" 
    by (auto simp add: Let_def)
  have "wf_item1 ?b (length Bs)" using wf_parse PWL_first_in_set_PWL assms by (auto simp del: wf_item1.simps PWL_first.simps)
  then have "wf_parse_bin1 (set ?step) (length Bs)" using wf1_Parse_Complete_L wf1_Parse_Predict_L wf_parse
    by presburger
  then show ?thesis 
  using wf_minus_PWL wf_union_LPWL 3 wf_parse assms(1) by blast
qed

lemma wf_parse_step1': "PWL_map_state pwl1 \<noteq> [] \<Longrightarrow> Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4) 
  \<Longrightarrow> wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PWL pwl1 (length Bs) \<Longrightarrow> ParseWL_inv pwl1 \<Longrightarrow> wf_PWL pwl3 (length Bs)"
  using wf_parse_step1 PWL_map_state_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma wf_parse_step2: 
  assumes "pwl1 = (wl1, t#ts)" "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4)" 
  and wf_parse: "wf_PWL pwl1 (length Bs)" "ParseWL_inv pwl1" "wf_PWL pwl2 (length Bs)" 
  shows "wf_PWL pwl4 (length Bs)"
proof-
  let ?b = "PWL_first (wl1, t#ts)"
  from assms have 4: "pwl4 = ParseWL_insert pwl2 ?b" by (auto simp add: Let_def)
  have "wf_item1 ?b (length Bs)" using wf_parse(1,2) PWL_first_in_set_PWL assms(1) 
    by (auto simp del: wf_item1.simps PWL_first.simps)
  then show ?thesis using wf_PWL_insert wf_parse(1) assms 4 by blast
qed

lemma wf_parse_step2': "PWL_map_state pwl1 \<noteq> [] \<Longrightarrow> Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4) 
  \<Longrightarrow> wf_PWL pwl1 (length Bs) \<Longrightarrow> ParseWL_inv pwl1 \<Longrightarrow> wf_PWL pwl2 (length Bs) \<Longrightarrow> wf_PWL pwl4 (length Bs)"
  using wf_parse_step2 PWL_map_state_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma Parse_steps_wf1: 
  assumes wf: "wf_parse_bins1 (map set Bs)" "wf_PWL pwl1 (length Bs)"
  and inv: "ParseWL_inv pwl1" 
  and sf: "Parse_steps Bs (pwl1,pwl2) = Some (pwl1', pwl2')"  
shows "wf_PWL pwl1' (length Bs)"
  using while_option_rule[where P= "\<lambda>(pwl1,pwl2). wf_PWL pwl1 (length Bs) \<and> ParseWL_inv pwl1 \<and> wf_parse_bins1 (map set Bs)"] 
    wf_parse_step1' step_fun_inv1_wl PWL_inv_parse_step1' wf sf inv unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma Parse_steps_wf2: 
  assumes wf: "wf_parse_bins1 (map set Bs)" "wf_PWL pwl1 (length Bs)" "wf_PWL pwl2 (length Bs)"
  and inv: "ParseWL_inv pwl1" 
  and sf: "Parse_steps Bs (pwl1,pwl2) = Some (pwl1', pwl2')"  
shows "wf_PWL pwl2' (length Bs)"
  using while_option_rule[where P= "\<lambda>(pwl1,pwl2). wf_PWL pwl2 (length Bs) \<and> wf_PWL pwl1 (length Bs) \<and> ParseWL_inv pwl1 \<and> wf_parse_bins1 (map set Bs)"] 
    wf_parse_step1' wf_parse_step2' step_fun_inv1_wl PWL_inv_parse_step1' wf sf inv unfolding Parse_steps_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_one_step: "list a \<noteq> [] \<Longrightarrow> steps Bs (a,b) = Some (a',b') \<Longrightarrow> step_fun Bs (a,b) = (c,d) \<Longrightarrow> steps Bs (c,d) = Some (a',b')"
  unfolding steps_def
  by (simp add: while_option_unfold)

lemma Parse_steps_steps:
  assumes step: "list wl1 \<noteq> []" "Parse_steps Bs (pwl1, pwl2) = Some (pwl3, pwl4)" "steps (map (map state) Bs) (wl1, wl2) = Some (wl3, wl4)"
  and eq_start: "fst pwl1 = wl1" "fst pwl2 = wl2"
  and invs: "ParseWL_inv pwl1"
  and wf: "wf_parse_bin1 (set_ParseWL pwl1) (length Bs)" "wf_parse_bins1 (map set Bs)"
shows "steps (map (map state) Bs) (fst pwl3, fst pwl4) = Some (wl3, wl4)"
proof-
  let ?P = "\<lambda>(pwl3,pwl4). steps (map (map state) Bs) (fst pwl3, fst pwl4) = Some (wl3, wl4) \<and> ParseWL_inv pwl3 \<and> wf_parse_bin1 (set_ParseWL pwl3) (length Bs) \<and> wf_parse_bins1 (map set Bs)"
  let ?b = "(\<lambda>(B,C). PWL_map_state B \<noteq> [])" 
  let ?c = "(Parse_step_fun Bs)"
  have "?P s \<Longrightarrow> ?b s \<Longrightarrow> ?P (?c s)" for s
  proof-
    assume P: "?P s" and b: "?b s"
    then obtain wl1' ts1 wl2' ts2 wl3' ts3 wl4' ts4 where P_s: "s = ((wl1', ts1), (wl2', ts2)) \<and> Parse_step_fun Bs s = ((wl3', ts3), (wl4', ts4))"
      by (metis (no_types, opaque_lifting) T_fst.cases)
    obtain wl5 wl6 where step_f: "step_fun (map (map state) Bs) (wl1', wl2') = (wl5, wl6)" using PWL_map_state_def
      using T_union_WL.cases by blast
    then have eq: "wl5 = wl3' \<and> wl6  = wl4'" using b P P_s 
        Pstep_fun_eq_step_fun[of _ _ "(wl1', ts1)" "(wl2', ts2)" "(wl3', ts3)" "(wl4', ts4)" wl2' wl5 wl6]
      by (auto simp add: PWL_map_state_def)
    have 1: "ParseWL_inv (wl3', ts3) \<and> wf_parse_bin1 (set_ParseWL (wl3', ts3)) (length Bs) \<and> wf_parse_bins1 (map set Bs)"
      using P b P_s PWL_inv_parse_step1' wf_parse_step1' by (auto simp del: wf_parse_bin1.simps)
    have "list wl1' \<noteq> []" using b P_s by (auto simp add: PWL_map_state_def)
    then show "?P (?c s)" using P 1 P_s eq step_f steps_one_step[of wl1' "(map (map state) Bs)" wl2' wl3 wl4] 
      by (auto simp add:  simp del: wf_parse_bin1.simps)
  qed
  then show ?thesis
  using while_option_rule[where P= ?P] using eq_start invs wf step unfolding Parse_steps_def
  by blast
qed

theorem Parse_steps_NF: "wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PWL pwl1 (length Bs) \<Longrightarrow> wf_PWL pwl2 (length Bs) \<Longrightarrow> ParseWL_inv pwl1 \<Longrightarrow> ParseWL_inv pwl2 
  \<Longrightarrow> \<exists>pwl1' pwl2'. Parse_steps Bs (pwl1,pwl2) = Some (pwl1',pwl2') "
using wf_step_fun_less[of "length Bs"]
proof (induction "(fst pwl1,fst pwl2)" arbitrary: pwl1 pwl2 rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "list (fst pwl1) = []"
    thus ?thesis by (simp add: while_option_unfold Parse_steps_def PWL_map_state_def)
  next
    let ?steps = "while_option (\<lambda>(as,bs). PWL_map_state as \<noteq> []) (Parse_step_fun Bs)"
    assume cons: "list (fst pwl1) \<noteq> []"
    then obtain wl1 t ts where P_pwl1: "pwl1 = (wl1, t#ts)" using less.prems(4)
      by (metis PWL_map_state_Cons2 PWL_map_state_def list.exhaust surjective_pairing)
    then obtain pwl1' pwl2'
      where P_step: "(pwl1',pwl2') = Parse_step_fun Bs (pwl1,pwl2)"
      by (metis T_fst.cases)
    then have wf_inv: "wf_PWL pwl1' (length Bs)" "wf_PWL pwl2' (length Bs)" "ParseWL_inv pwl1'" "ParseWL_inv pwl2'"
      using wf_parse_step1 wf_parse_step2 PWL_inv_parse_step1 PWL_inv_parse_step2 less.prems P_pwl1
      by (metis, metis, metis, metis)
      
    from P_step have step_f: "(fst pwl1',fst pwl2') = step_fun (map (map state) Bs) (fst pwl1, fst pwl2)"
      using less.prems Pstep_fun_eq_step_fun1[of pwl1 Bs pwl2 pwl1' pwl2'] cons unfolding PWL_map_state_def by (auto simp add: Let_def)
    have "wf1_WL (fst pwl1) (length Bs) \<and> wf1_WL (fst pwl2) (length Bs)"
      using less.prems wf_PWL_impl_wf1_WL by (cases pwl1, cases pwl2) (auto simp del: wf_PWL.simps ParseWL_inv.simps)
    then have "((fst pwl1',fst pwl2'), (fst pwl1, fst pwl2)) \<in> step_fun_less (length Bs)" 
      using less.prems step_fun_less_step[of "fst pwl1" "(map (map state) Bs)" "fst pwl2"] \<open>list (fst pwl1) \<noteq> []\<close> step_f 
      by (cases pwl1, cases pwl2) (auto simp add: wf_parse_bins1_def wf_bins1_def wf_bin1_def)
    from less.hyps[OF this \<open>wf_parse_bins1 (map set Bs)\<close> wf_inv]
    show ?thesis
      by (simp add: P_step while_option_unfold Parse_steps_def)
  qed
qed

lemma Pclose2_L_eq_close2_L: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_PWL pwl1 (length Bs)" "ParseWL_inv pwl1"
  shows "map state (Parse_close2_L Bs pwl1) = close2_L (map (map state) Bs) (fst pwl1)"
proof-
  obtain pwl3 pwl4 where P_steps: "Parse_steps Bs (pwl1, PWL_empty (length Bs)) = Some (pwl3, pwl4)"
    using assms Parse_steps_NF PWL_inv_empty wf_PWL_empty by blast
  then have P_pwl3: "wf_PWL pwl3 (length Bs) \<and> ParseWL_inv pwl3 \<and> list (fst pwl3) = []"
    using Parse_steps_wf1 Parse_steps_inv1 while_option_stop assms unfolding Parse_steps_def PWL_map_state_def
    by (metis (mono_tags, lifting) case_prodI)
  from P_steps have inv_pwl4: "ParseWL_inv pwl4" using PWL_inv_empty Parse_steps_inv2 assms by blast
  from assms have "wf_bins1 (map set (map (map state) Bs))" using wf_parse_bins1_impl_bins1[of "map set Bs"] 
    by (auto simp add: wf_bins1_def)
  then obtain wl3 wl4 where steps: "steps (map (map state) Bs) (fst pwl1, WL_empty (length Bs)) = Some (wl3, wl4)"
    using assms Close2_L_NF[of "(map (map state) Bs)" "fst pwl1" "WL_empty (length Bs)"] empty_inv wf_PWL_impl_wf1_WL[of "pwl1" "length Bs"] set_WL_empty
    by (cases pwl1) (auto simp add: wf_bin1_def)
  have "fst pwl3 = wl3 \<and> fst pwl4 = wl4"
  proof (cases "list (fst pwl1) = []")
    case True
    then show ?thesis using P_steps steps unfolding Parse_steps_def steps_def PWL_map_state_def
      by (auto simp add: while_option_unfold)
  next
    case False
    then have "steps (map (map state) Bs) (fst pwl3, fst pwl4) = Some (wl3, wl4)"
      using Parse_steps_steps assms P_steps steps P_pwl3 by auto
    then show ?thesis using P_pwl3 unfolding steps_def by (auto simp add: while_option_unfold)
  qed
  then show ?thesis using P_steps steps inv_pwl4 unfolding Parse_close2_L_def close2_L_def 
    by (cases pwl4) auto
qed

lemma set_PWL_list_eq_set_PWL[simp]: "set (PWL_list pwl) = set_ParseWL pwl"
  by (cases pwl) auto

lemma wf_Parse_close2_L: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_PWL pwl (length Bs)" "ParseWL_inv pwl" 
  shows "wf_parse_bin1 (set (Parse_close2_L Bs pwl)) (length Bs)"
proof-
  obtain pwl3 pwl4 where P: "Parse_steps Bs (pwl, PWL_empty (length Bs)) = Some (pwl3, pwl4)"
    using assms Parse_steps_NF wf_PWL_empty PWL_inv_empty by blast
  then have "wf_PWL pwl4 (length Bs)" using Parse_steps_wf2 assms
    using wf_PWL_empty by blast
  then show ?thesis unfolding Parse_close2_L_def P by (auto simp del: wf_parse_bin1.simps)
qed

lemma "fst (PWL_of_List k xs) = WL_of_List k (map state xs)"
  by (induction xs) (auto simp add: PWL_of_List_def WL_of_List_def)

lemma length_Parse_bins[simp]: "length (Parse_bins_L k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma wf_parse_bins_L: "k \<le> length w \<Longrightarrow> wf_parse_bins1 (map set (Parse_bins_L k))"
proof (induction k)
  case 0
  then show ?case using wf_PWL_of_List wf_Parse_close2_L[of "[]"] wf1_Parse_Init_L PWL_inv_PWL_of_List
    by (auto simp add: wf_parse_bins1_def simp del: wf_parse_bin1.simps)
next
  case (Suc k)
  have "Parse_bins_L k \<noteq> []" using length_Parse_bins
    by (metis length_0_conv nat.distinct(1))
  then have "wf_parse_bin1 (set (last (Parse_bins_L k))) k" using Suc length_Parse_bins wf_parse_bins1_def 
    by (auto simp add: last_conv_nth simp del: wf_parse_bin1.simps)
  then have 1: "wf_parse_bin1 (set (Parse_close2_L (Parse_bins_L k) (PWL_of_List (Suc k) (Parse_Scan_L (last (Parse_bins_L k)) k)))) (Suc k)"
    using Suc wf_PWL_of_List wf_Parse_close2_L[of "Parse_bins_L k"] wf1_Parse_Scan_L PWL_inv_PWL_of_List
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

lemma Parse_bins_L_eq_bins_L: "k \<le> length w \<Longrightarrow> map (map state) (Parse_bins_L k) = bins_L k"
proof (induction k)
  case 0
  have "fst (PWL_of_List 0 Parse_Init_L) = WL_of_List 0 Init_L"
    using Parse_Init_L_eq_Init_L by (auto simp add: PWL_of_List_def WL_of_List_def)
  then show ?case using Pclose2_L_eq_close2_L[of "[]" "PWL_of_List 0 Parse_Init_L"] PWL_inv_PWL_of_List wf_PWL_of_List wf1_Parse_Init_L
    by (auto simp add: wf_parse_bins1_def simp del: wf_parse_bin1.simps)
next
  case (Suc k)
  have cons: "Parse_bins_L k \<noteq> []" using length_Parse_bins
    by (metis length_0_conv nat.distinct(1))
  then have last_eq: "map state (last (Parse_bins_L k)) = last (bins_L k)" using Suc
    by (metis Suc_leD last_map)
  have 1: "wf_parse_bins1 (map set (Parse_bins_L k))" using wf_parse_bins_L Suc by auto
  then have "wf_parse_bin1 (set (last (Parse_bins_L k))) k" using Suc cons by (auto simp add: last_conv_nth wf_parse_bins1_def)
  then have wf_Scan: "wf_parse_bin1 (set (Parse_Scan_L (last (Parse_bins_L k)) k)) (Suc k)"
    using wf1_Parse_Scan_L Suc by (auto simp del: wf_parse_bin1.simps)
  let ?pwl = "PWL_of_List (Suc k) (Parse_Scan_L (last (Parse_bins_L k)) k)"
  let ?wl = "WL_of_List (Suc k) (Scan_L (last (bins_L k)) k)"
  have "fst ?pwl = ?wl"
    using Parse_Scan_L_eq_Scan_L last_eq by (auto simp add: PWL_of_List_def WL_of_List_def)
  then have "map state (Parse_close2_L (Parse_bins_L k) ?pwl) = close2_L (bins_L k) ?wl"
    using Suc Pclose2_L_eq_close2_L PWL_inv_PWL_of_List wf_PWL_of_List wf_Scan
    using "1" Suc_leD length_Parse_bins by presburger
  then show ?case using Suc 1 by (auto simp add: Let_def length_bins_L)
qed

end

context Earley_Gw
begin
fun get_parse_tree :: "('n,'a) item list \<Rightarrow> ('n,'a) tree option" where
"get_parse_tree [] = None" |
"get_parse_tree (x#xs) = (if is_final (fst x) then Some (Rule S (rev (snd x))) else get_parse_tree xs)"

lemma get_parse_tree_NF: "is_final (fst x) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>s t. (s,t) \<in> set xs \<and> is_final s \<and> get_parse_tree xs = Some (Rule S (rev t))"
  by (induction xs) auto

fun parse_tree_w where
"parse_tree_w _ = the (get_parse_tree (last (Parse_bins_L (length w))))"
(*TODO make a definition and move outside of Context*)

end

context Earley_Gw_eps
begin

lemma accepted_implies_Some_tree: 
  assumes "accepted" shows "\<exists> t. get_parse_tree (last (Parse_bins_L (length w))) = Some t"
proof-
  obtain s where P_s: "s \<in> (\<S> (length w)) \<and> is_final s" using assms by (auto simp add: accepted_def)
  have cons: "Parse_bins_L (length w) \<noteq> []" using length_Parse_bins
    by (metis length_0_conv nat.distinct(1))
  have "last (map (map state) (Parse_bins_L (length w))) = last (bins_L (length w))"
    using Parse_bins_L_eq_bins_L by auto
  then have "set (map state (last (Parse_bins_L (length w)))) = set (last (bins_L (length w)))"
    using cons by (auto simp add: last_map)
  then have "set (map state (last (Parse_bins_L (length w)))) = \<S> (length w)" 
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

lemma generated_parse_tree_is_valid: "get_parse_tree (last (Parse_bins_L (length w))) = Some t \<longrightarrow> valid_parse_tree P w S t"
proof
  assume "get_parse_tree (last (Parse_bins_L (length w))) = Some t"
  then obtain s ts where P_t: "(s,ts) \<in> set (last (Parse_bins_L (length w))) \<and> is_final s \<and> t = (Rule S (rev ts))" 
    using get_parse_tree_Some_t_decomp by blast
  moreover have "Parse_bins_L (length w) \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_Parse_bins)
  ultimately have "wf_item1 (s, ts) (length w)" using wf_parse_bins_L 
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_item1.simps)
  then show "valid_parse_tree P w S t" using P_t 
    by (auto simp add: valid_parse_tree_def is_final_def wf_state1_def wf_state_def \<alpha>_def rhs_def is_complete_def)
qed

lemma find_parse_tree_iff_w_in_L: "(\<exists>t. get_parse_tree (last (Parse_bins_L (length w))) = Some t) \<longleftrightarrow> w0 \<in> Lang P S"
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

time_fun hd
time_fun zip
time_fun rev

lemma T_zip_eq_len: "length xs = length ys \<Longrightarrow> T_zip xs ys = length ys + 1"
  by (induction xs ys rule: list_induct2) auto

lemma T_rev_bound: "T_rev xs \<le> 2*length xs * length xs + 1"
  by (induction xs) auto



context Earley_Gw_eps_T
begin
time_fun PWL_empty
time_fun ParseWL_insert
time_fun union_LPWL
time_fun ParseWL_isin
time_fun minus_LPWL
time_fun PWL_list
time_fun minus_PWL
time_fun PWL_of_List
time_fun PWL_first

time_fun Parse_Complete_L
time_fun Parse_Scan_L
time_fun Parse_Predict_L
time_fun Parse_step_fun

lemma T_rev_tree: 
  assumes "wf_item item k" shows "T_rev (tree item) \<le> 2 * K * K + 1" 
proof-
  obtain lh rh d T_nth_WL t where P: "item = (State (lh, rh) d T_nth_WL, t)"
    by (metis state.exhaust surj_pair)
  have "map root (rev t) = take d rh" using assms P by (auto simp add: \<alpha>_def rhs_def)
  then have "length t = length (take d rh)"
    by (metis length_map length_rev)
  moreover have "length rh \<le> K" using assms P prod_length_bound by (auto simp add: wf_state_def rhs_def)

  ultimately have 1: "length t \<le> K" by auto
  have "T_rev t \<le> Suc (length t * (length t * 2))" using T_rev_bound[of t] by auto
  also have "... \<le> Suc (K * (K * 2))" using 1 by (simp add: mult_le_mono)
  finally show ?thesis using P by simp
qed

lemma [simp]: "ParseWL_inv pwl \<Longrightarrow> T_PWL_list pwl = (length (snd pwl)) + 1"
  using T_zip_eq_len by (cases pwl) auto

lemma [simp]: 
  assumes "snd pwl \<noteq> []" "ParseWL_inv pwl" shows "T_PWL_first pwl = 0"
proof-
  obtain as l m b bs where P1: "pwl = (WorkList as l m, (b#bs))"
    using assms by (metis T_last.cases set_ParseWL.cases snd_conv wl_decomp)
  then have "as \<noteq> []" using assms by auto
  then obtain a ass where "as = a#ass"
    by (meson recognized_L.cases)
  then show ?thesis using P1 by auto
qed

(*assumes that the stop condition check takes 0 time*)
fun parse_steps_time :: "('a, 'b) item list list \<Rightarrow> ('a, 'b) ParseWL \<times> ('a, 'b) ParseWL \<Rightarrow> nat \<Rightarrow> ((('a, 'b) ParseWL \<times> ('a, 'b) ParseWL) \<times> nat) option" where
"parse_steps_time Bs wls y = while_option (\<lambda>((B,C),k). PWL_map_state B \<noteq> []) (\<lambda>((B,C),k). (Parse_step_fun Bs (B,C), k + T_Parse_step_fun Bs (B,C))) (wls, y)"

fun T_Parse_steps :: "('a, 'b) item list list \<Rightarrow> ('a, 'b) ParseWL \<times> ('a, 'b) ParseWL \<Rightarrow> nat" where
"T_Parse_steps Bs wls = snd (the (parse_steps_time Bs wls 0))"


time_fun Parse_close2_L
time_fun Parse_bins_L

lemma PWL_T_insert_simp: "T_ParseWL_insert pwl x \<le> T_isin (fst pwl) (fst x) + T_insert (fst pwl) (fst x)"
  by (cases pwl, cases x) simp
corollary PWL_T_insert_bound: "distinct ps \<Longrightarrow> WL_inv (fst pwl) \<Longrightarrow> wf1_WL (fst pwl) k \<Longrightarrow> from (fst x) < Suc (leng (fst pwl)) 
  \<Longrightarrow> T_ParseWL_insert pwl x \<le> 4 * T_nth_WL (from (fst x)) + 2* L * Suc K + 2"
  using T_isin_wf[of "fst pwl" k "fst x"] T_insert_less[of "fst pwl" k  "fst x"] PWL_T_insert_simp[of pwl x] 
  by auto

lemma T_union_LPWL_bound: "distinct ps \<Longrightarrow> ParseWL_inv pwl \<Longrightarrow> wf_parse_bin1 (set xs) (leng (fst pwl)) \<Longrightarrow> wf_PWL pwl (leng (fst pwl))
  \<Longrightarrow> T_union_LPWL xs pwl \<le> length xs * (4 * T_nth_WL (leng (fst pwl)) + 2* L * Suc K + 2) + length xs + 1"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have ih: "T_union_LPWL xs pwl \<le> length xs * (4 * T_nth_WL (leng (fst pwl)) + 2 * L * Suc K + 2) + length xs + 1"
    by simp

  from Cons have 1: "WL_inv (fst pwl)" by (cases pwl) auto
  then have 2: "WL_inv (union_LWL (map state xs) (fst pwl))"
    by (simp add: LWL_union_inv)

  have a_le_leng: "from (fst a) \<le> leng (fst pwl)" using Cons by (auto simp add: wf_state1_def wf_state_def)
  
  have "wf1_WL (fst pwl) (leng (fst pwl))" using Cons wf_PWL_impl_wf1_WL[of pwl "leng (fst pwl)"] by auto
  then have 3: "wf_bin1 (set (list (union_LWL (map state xs) (fst pwl)))) (leng (fst pwl))" 
    using 1 Cons wf1_WL_union_LWL[of "fst pwl" "leng (fst pwl)" "map state xs"] by (auto simp add: wf_bin1_def)
  have 4: "from (state a) < Suc (leng (union_LWL (map state xs) (fst pwl)))" using Cons leng_LWL_union[of "map state xs" "fst pwl"] le_imp_less_Suc 
    by (auto simp add: wf_state1_def wf_state_def)
  from 2 3 4 have "T_ParseWL_insert (union_LPWL xs pwl) a \<le> 4 * T_nth_WL (from (fst a)) + 2* L * Suc K + 2"
    using "Cons.prems"(1) PWL_T_insert_bound[of "(union_LPWL xs pwl)" "leng (fst pwl)" a] 
    by (auto simp add: wf_state1_def wf_state_def)
  then have "T_ParseWL_insert (union_LPWL xs pwl) a \<le> 4 * T_nth_WL (leng (fst pwl)) + 2* L * Suc K + 2"
    using mono_nth a_le_leng incseqD[of T_nth_WL "from (fst a)" "leng (fst pwl)"] by (auto simp add: algebra_simps)
  then show ?case using ih by (auto simp add: algebra_simps)
qed

lemma T_minus_LPWL_bound: "distinct ps \<Longrightarrow> ParseWL_inv pwl \<Longrightarrow> wf_parse_bin1 (set xs) k \<Longrightarrow> wf_PWL pwl k
 \<Longrightarrow> T_minus_LPWL k xs pwl \<le> length xs * (5 * T_nth_WL k + 3 * L * Suc K + 3) + length xs + k + 2"
proof(induction k xs pwl rule: T_minus_LPWL.induct)
  case (1 k pwl)
  then show ?case by simp
next
  case (2 k a as pwl)
  then have ih: "T_minus_LPWL k as pwl \<le> length as * (5 * T_nth_WL k + 3 * L * Suc K + 3) + length as + k + 2"
    by auto

  from 2 have 3: "WL_inv (fst pwl)" by (cases pwl) auto
  have 4: "WL_inv (minus_LWL k (map state as) (fst pwl))"
    by (simp add: LWL_minus_inv)

  have a_le_k: "from (fst a) \<le> k" using 2 by (auto simp add: wf_state1_def wf_state_def)
  
  have "wf1_WL (fst pwl) k" using 2 wf_PWL_impl_wf1_WL[of pwl k] by auto
  then have 5: "wf_bin1 (set (list (minus_LWL k (map state as) (fst pwl)))) k" 
    using 2 3 wf1_WL_minus_LWL[of "fst pwl" "map state as" k k] by (auto simp add: wf_bin1_def)
  have 6: "from (state a) < Suc (leng (minus_LWL k (map state as) (fst pwl)))" using 2 leng_minus_LWL[of "map state as" k] le_imp_less_Suc 
    by (auto simp add: wf_state1_def wf_state_def)

  from 4 5 6 have "T_ParseWL_insert (minus_LPWL k as pwl) a \<le> 4 * T_nth_WL (from (fst a)) + 2* L * Suc K + 2"
    using "2.prems"(1) PWL_T_insert_bound[of "(minus_LPWL k as pwl)" k a] 
    by (auto simp add: wf_state1_def wf_state_def)
  then have 7: "T_ParseWL_insert (minus_LPWL k as pwl) a \<le> 4 * T_nth_WL k + 2* L * Suc K + 2"
    using mono_nth a_le_k incseqD[of T_nth_WL "from (fst a)" k] by (auto simp add: algebra_simps)

  have "T_isin (fst pwl) (fst a) \<le> T_nth_WL (from (fst a)) + L * Suc K + 1"
    using T_isin_wf
    using "2.prems"(1) "3" \<open>wf1_WL (fst pwl) k\<close> by blast
  then have "T_ParseWL_isin pwl a \<le> T_nth_WL (from (fst a)) + L * Suc K + 1" by (cases pwl, cases a) auto
  then have "T_ParseWL_isin pwl a \<le> T_nth_WL k + L * Suc K + 1" 
    using mono_nth a_le_k incseqD[of T_nth_WL "from (fst a)" k] by (auto simp add: algebra_simps)


  then show ?case using ih 7 by (auto simp add: algebra_simps)
qed

lemma T_minus_PWL_bound: 
  assumes "distinct ps" "ParseWL_inv pwl1" "ParseWL_inv pwl2" "wf_PWL pwl1 (leng (fst pwl1))" "wf_PWL pwl2 (leng (fst pwl1))"
  shows "T_minus_PWL pwl1 pwl2 \<le> length (snd pwl1) * (5 * T_nth_WL (leng (fst pwl1)) + 3 * L * Suc K + 3) + 2 * length (snd pwl1) + (leng (fst pwl1)) + 3"
proof-
  have "T_PWL_list pwl1 = length (snd pwl1) + 1" using assms by auto

  moreover have "T_minus_LPWL (leng (fst pwl1)) (PWL_list pwl1) pwl2 
    \<le> length (PWL_list pwl1) * (5 * T_nth_WL (leng (fst pwl1)) + 3 * L * Suc K + 3) + length (PWL_list pwl1) + (leng (fst pwl1)) + 2" 
    using assms T_minus_LPWL_bound[of pwl2 "PWL_list pwl1" "leng (fst pwl1)"] wf_PWL_impl_wf1_WL by auto
  moreover have "length (PWL_list pwl1) = length (snd pwl1)" using assms by (cases pwl1) auto
  ultimately show ?thesis by (auto simp add: algebra_simps)
qed

lemma T_PWL_of_List_bound: 
  assumes "distinct ps" "wf_parse_bin1 (set xs) k"
  shows "T_PWL_of_List k xs \<le> length xs * (4 * T_nth_WL k + 2* L * Suc K + 2) + length xs + k + 2"
proof-
  have "ParseWL_inv (PWL_empty k)" and "wf_PWL (PWL_empty k) k"
    using wf_PWL_empty by (auto simp add: PWL_inv_empty)
  then have "T_union_LPWL xs (PWL_empty k) \<le> length xs * (4 * T_nth_WL k + 2* L * Suc K + 2) + length xs + 1"
    using T_union_LPWL_bound[of "PWL_empty k"] assms by auto
  then show ?thesis by auto
qed

lemma T_Parse_Complete_L_bound: 
  assumes "wf_parse_bins1 (map set Bs)" "from (state item) < length Bs" "wf_item item (length Bs)" "length (Bs ! from (state item)) \<le> C"
  shows "T_Parse_Complete_L Bs item \<le> length Bs +  (2 * K * K + 2 * K + 5) * C + 2"
proof-
  let ?from_list = "Bs ! from (state item)"
  let ?T_filt = "\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> T_next_symbol p + (T_fst item + T_prod (state item) + T_fst (state.prod (state item)))"
  let ?filtered = "filter (\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> next_sym_Nt p (lhs (state.prod (state item)))) (Bs ! from (state item))"
  let ?T_Pred = "\<lambda>x. let a = x in case a of (p, t) \<Rightarrow> T_mv_dot p + (T_fst item + T_prod (state item) + T_fst (state.prod (state item)) + (T_snd item + T_rev (tree item)))"
  have "\<forall>x \<in> set (Bs ! from (state item)). ?T_filt x \<le> 2 * Suc K" 
    using assms T_next_symbol_bound by (fastforce simp add: wf_parse_bins1_def wf_state1_def wf_state_def)
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

  have "T_nth Bs (from (state item)) \<le> length Bs" 
    using assms T_nth_general[of "from (state item)" Bs] by auto

  then show ?thesis using 1 2 by (auto simp add: algebra_simps)
qed

lemma T_Parse_Scan_L_bound: 
  assumes "k < length w0" "wf_parse_bin (set Bs) k" 
  shows "T_Parse_Scan_L Bs k \<le> k + (2*K + 4) * (length Bs) + 3"
proof-
  have 1: "T_nth w0 k \<le> k + 1" using assms T_nth_general by auto

  let ?T_filt = "\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_next_symbol p"
  have "\<forall>x \<in> set Bs. ?T_filt x \<le> 2 * Suc K" 
    using assms T_next_symbol_bound by (fastforce simp add: wf_state_def)
  then have 2: "T_filter ?T_filt Bs \<le> 2 * Suc K * (length Bs) + length Bs + 1"
    using T_filter_bound[of Bs ?T_filt "2 * Suc K"] by simp

  let ?filtered = "filter (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> next_symbol p = Some (Tm (w0 ! k))) Bs"
  let ?T_map = "\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p + T_the (Some (Tm (w0 ! k)))"
  have "T_map (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p + T_the (Some (Tm (w0 ! k)))) ?filtered
  = T_map (\<lambda>y. 0) ?filtered" by auto
  also have "... \<le> length ?filtered + 1" using T_map_bound by fastforce
  also have "... \<le> length Bs + 1" by auto
  finally have "T_map (\<lambda>y. let a = y in case a of (p, t) \<Rightarrow> T_mv_dot p + T_the (Some (Tm (w0 ! k)))) ?filtered \<le> length Bs + 1".

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
  assumes "ParseWL_inv (wl, t#ts)" shows "T_PWL_first (wl, t#ts) = 0"
proof-
  obtain x xs l m where "wl = WorkList (x#xs) l m" using assms
    by (metis ParseWL_inv.simps length_0_conv neq_Nil_conv upsize_list upsize_list1 wl_decomp)
  then show ?thesis by auto
qed

lemma parse_complete_length: "length (Parse_Complete_L Bs item) \<le> length (Bs ! from (state item))"
  by (auto simp add: Parse_Complete_L_def)

lemma parse_predict_length: "length (Parse_Predict_L s n) \<le> L"
  by (auto simp add: Parse_Predict_L_def L_def)

lemma T_parse_step_fun_bound: 
  assumes cons: "PWL_map_state pwl1 \<noteq> []"
  and dist: "distinct ps"
  and invs: "ParseWL_inv pwl1" "ParseWL_inv pwl2"
  and lengs: "leng (fst pwl1) = length Bs" "leng (fst pwl2) = length Bs"
  and wf1: "wf_parse_bin1 (set_ParseWL pwl1) (length Bs)" "wf_parse_bin1 (set_ParseWL pwl2) (length Bs)" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
shows "T_Parse_step_fun Bs (pwl1,pwl2) 
    \<le> (2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12"
proof-
  from cons invs obtain x xs l m t ts where P_pwl1: "pwl1 = (WorkList (x#xs) l m, (t#ts))"
    by (metis PWL_map_state_Cons1 PWL_map_state_Cons2 prod.collapse recognized_L.cases)
  obtain wl2 ts2 where P_pwl2: "pwl2 = (wl2, ts2)"
    using set_ParseWL.cases by blast
  let ?b = "PWL_first (WorkList (x#xs) l m, (t#ts))"
  have b_simp: "?b = (x,t)" by simp

  have wf1_b: "wf_item1 ?b (length Bs)" using wf1 PWL_first_in_set_PWL P_pwl1 by auto
  then have 1: "T_is_complete (state ?b) \<le> K + 1" using T_is_complete_bound prod_length_bound P_pwl1 
    by (auto simp add: wf_state1_def wf_state_def)

  have 2: "is_complete (state ?b) \<longrightarrow> T_Parse_Complete_L Bs ?b \<le> length Bs +  (2 * K * K + 2 * K + 5) * C + 2"
    using wf1 wf1_b max_bin_size T_Parse_Complete_L_bound[of Bs ?b C] by (auto simp add: wf_state1_def)

  moreover have "T_Parse_Predict_L (state ?b) (length Bs) \<le> 2 * Suc K * L + 2 * L + 2" 
    using wf1_b T_Parse_Predict_L_bound by (simp add: wf_state1_def wf_state_def)
  ultimately have 3: "(if is_complete (state ?b) then T_Parse_Complete_L Bs ?b 
    else T_fst ?b + (the (T_size Bs) + T_Parse_Predict_L (state ?b) (length Bs)))
    \<le> length Bs + (2 * K * K + 2 * K + 5) * C + 2 * Suc K * L + 2 * L + 3"  
    by (auto simp add: T_length_bound algebra_simps)

  let ?step = "if is_complete (state ?b) then Parse_Complete_L Bs ?b else Parse_Predict_L (state ?b) (length Bs)"
  have length_step: "length ?step \<le> max C L" 
    using parse_complete_length[of Bs "(x,t)"] parse_predict_length[of x "length Bs"] max_bin_size wf1_b 
    by (auto simp add: wf_state1_def)
  have wf_step: "wf_parse_bin1 (set ?step) (length Bs)"
    using wf1(3) wf1_Parse_Complete_L wf1_Parse_Predict_L wf1_b by presburger  
  then have "T_union_LPWL ?step pwl1 \<le> length ?step * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 2) + length ?step + 1"
    using T_union_LPWL_bound[of pwl1 ?step] dist invs wf1 by (auto simp add: lengs simp del: wf_parse_bin1.simps)
  also have "... \<le> (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1"
    using length_step using mult_le_mono1[of "length ?step" "max C L"]
    by (meson add_le_mono le_numeral_extra(4))
  finally have 4: "T_union_LPWL ?step pwl1 \<le> (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1".

  have "from (state ?b) < Suc (leng wl2)" using lengs wf1_b P_pwl2 by (auto simp add: wf_state1_def wf_state_def)
  then have "T_ParseWL_insert pwl2 ?b \<le> 4 * T_nth_WL (from (state ?b)) + 2 * L * Suc K + 2"
    using PWL_T_insert_bound[of pwl2 "length Bs" ?b] dist invs wf1 P_pwl2 wf_PWL_impl_wf1_WL by auto
  also have "... \<le> 4 * T_nth_WL (length Bs) + 2 * L * Suc K + 2" using mono_nth wf1_b 
    by (auto simp add: incseqD wf_state1_def wf_state_def)
  finally have 5: "T_ParseWL_insert pwl2 ?b \<le> 4 * T_nth_WL (length Bs) + 2 * L * Suc K + 2".
  
  have wf_PWL_union: "wf_PWL (union_LPWL ?step pwl1) (length Bs)" 
    using wf1(1) wf_step wf_union_LPWL[of pwl1 "length Bs" ?step] by simp
  moreover have inv_union: "ParseWL_inv (union_LPWL ?step pwl1)" using PWL_inv_union_LPWL invs(1) 
    by auto
  ultimately have length_snd_union: "length (snd(union_LPWL ?step pwl1)) \<le> L * Suc K * Suc (length Bs)" 
    using length_snd_PWL[of "union_LPWL ?step pwl1" "length Bs"] by simp

  have wf_PWL_insert: "wf_PWL (ParseWL_insert pwl2 ?b) (length Bs)" 
    using wf_PWL_insert[of pwl2 "length Bs" ?b] wf1(2) wf1_b by fastforce
  have inv_insert: "ParseWL_inv (ParseWL_insert pwl2 ?b)" 
    using PWL_inv_insert[of pwl2 ?b] invs(2) by auto
  let ?length_list = "length (snd (union_LPWL ?step pwl1))"
  let ?leng_wl = "leng (fst (union_LPWL ?step pwl1))"
  have "T_minus_PWL (union_LPWL ?step pwl1) (ParseWL_insert pwl2 ?b)
    \<le>?length_list * (5 * T_nth_WL (?leng_wl) + 3 * L * Suc K + 3) + 2 * ?length_list + ?leng_wl + 3" 
    using T_minus_PWL_bound[of "union_LPWL ?step pwl1" "ParseWL_insert pwl2 ?b"]
      wf_PWL_union inv_union wf_PWL_insert inv_insert dist leng_PWL_insert[of ?b pwl1] leng_LPWL_union[of ?step pwl1] lengs
    by (metis wf_step)
  also have "... \<le> L * Suc K * Suc (length Bs) * (5 * T_nth_WL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + length Bs + 3"
    using mult_le_mono1[of ?length_list "L * Suc K * Suc (length Bs)" "(5 * T_nth_WL (length Bs) + 3 * L * Suc K + 3)"] 
      mult_le_mono2[of ?length_list "L * Suc K * Suc (length Bs)" 2] 
      wf_step leng_LPWL_union[of ?step pwl1] add_mult_distrib lengs(1) length_snd_union by auto
  finally have 6: "T_minus_PWL (union_LPWL ?step pwl1) (ParseWL_insert pwl2 ?b) \<le>
    L * Suc K * Suc (length Bs) * (5 * T_nth_WL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + length Bs + 3".

  have "T_Parse_step_fun Bs (pwl1,pwl2) \<le> 
    T_is_complete (state ?b)
    + (if is_complete (state ?b) then T_Parse_Complete_L Bs ?b else T_fst ?b + (the (T_size Bs) + T_Parse_Predict_L (state ?b) (length Bs)))
    + T_union_LPWL ?step pwl1
    + 2 * T_ParseWL_insert pwl2 ?b
    + T_minus_PWL (union_LPWL ?step pwl1) (ParseWL_insert pwl2 ?b)"
    using P_pwl1 by (auto simp add: Let_def)
  also have "... \<le> K + 1 + length Bs + (2 * K * K + 2 * K + 5) * C + 2 * Suc K * L + 2 * L + 3 
    + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 2) + (max C L) + 1
    + 2 * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 2)
    + L * Suc K * Suc (length Bs) * (5 * T_nth_WL (length Bs) + 3 * L * Suc K + 3) + 2 * L * Suc K * Suc (length Bs) + length Bs + 3"
    using 1 3 4 5 6 by (auto simp only: algebra_simps)
  also have "... = 2 * length Bs + K + 12 + 6 * Suc K * L + 2 * L + (2 * K * K + 2 * K + 5) * C 
    + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3) + 8 * T_nth_WL (length Bs)
    + L * Suc K * Suc (length Bs) * (5 * T_nth_WL (length Bs) + 3 * L * Suc K + 5)"
    by (auto simp add: algebra_simps)
  also have "... \<le>  (2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12"
    by (auto simp add: algebra_simps)
  finally show ?thesis.
qed

lemma leng_minus_PWL: "ParseWL_inv pwl1 \<Longrightarrow> leng (fst (minus_PWL pwl1 pwl2)) = leng (fst pwl1)"
  using leng_minus_LWL by (cases pwl1, cases "fst pwl1") (auto simp add: minus_PWL_def)

lemma Parse_step_fun_leng1: assumes 
  "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4)" "PWL_map_state pwl1 \<noteq> []" "ParseWL_inv pwl1"
  "wf_PWL pwl1 (length Bs)" "wf_PWL pwl2 (length Bs)" "wf_parse_bins1 (map set Bs)"
  "leng (fst pwl1) = length Bs"
shows  "leng (fst pwl3) = length Bs"
proof- 
  from assms(2,3) obtain x xs l m t ts where "pwl1 = (WorkList (x#xs) l m, t#ts)"
    using PWL_map_state_def PWL_map_state_Cons2
    by (metis Earley_Gw.WorkList.sel(1) T_size_list.cases surjective_pairing wl_decomp)
  then show ?thesis using assms leng_minus_PWL PWL_inv_union_LPWL leng_LPWL_union wf1_Parse_Complete_L
        wf1_Parse_Predict_L
    by (smt (verit) PWL_first_in_set_PWL Parse_step_fun.simps(2) Pstep_fun_eq_step_fun1 list.distinct(1) wf_PWL.elims(2) wf_parse_bin1.elims(2))
qed

lemma Parse_step_fun_leng2: assumes 
  "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4)" "PWL_map_state pwl1 \<noteq> []" "ParseWL_inv pwl1"
  "wf_PWL pwl1 (length Bs)" 
  "leng (fst pwl2) = length Bs"
shows  "leng (fst pwl4) = length Bs"
proof-
  from assms(2,3) obtain x xs l m t ts where "pwl1 = (WorkList (x#xs) l m, t#ts)"
    using PWL_map_state_def PWL_map_state_Cons2
    by (metis Earley_Gw.WorkList.sel(1) T_size_list.cases surjective_pairing wl_decomp)
  then show ?thesis using leng_PWL_insert assms by (auto simp add: Let_def wf_state1_def)
qed

lemma Parse_step_fun_set_inc:
  assumes "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4)" "PWL_map_state pwl1 \<noteq> []" "ParseWL_inv pwl1" "ParseWL_inv pwl2"
          "set (PWL_map_state pwl1) \<inter> set (PWL_map_state pwl2) = {}"
  shows "length (PWL_map_state pwl4) = Suc (length (PWL_map_state pwl2))"
proof-
  from assms(2,3) obtain x xs l m t ts  ys l2 m2 ts2 where "pwl1 = (WorkList (x#xs) l m, t#ts)" 
      and "pwl2 = (WorkList ys l2 m2, ts2)"
    using PWL_map_state_def PWL_map_state_Cons2
    by (metis Earley_Gw.WorkList.sel(1) T_size_list.cases surjective_pairing wl_decomp)
  then show ?thesis using assms by (auto simp add: Let_def PWL_map_state_def member_elem)
qed

lemma Parse_step_fun_dist_sets:
  assumes "Parse_step_fun Bs (pwl1, pwl2) = (pwl3, pwl4 )" "PWL_map_state pwl1 \<noteq> []" "ParseWL_inv pwl1" "ParseWL_inv pwl2"
  shows "set (PWL_map_state pwl3) \<inter> set (PWL_map_state pwl4) = {}"
proof-
  from assms(2,3) obtain x xs l m t ts  wl2 ts2 where "pwl1 = (WorkList (x#xs) l m, t#ts)" 
      and "pwl2 = (wl2, ts2)"
    using PWL_map_state_def PWL_map_state_Cons2
    by (metis Earley_Gw.WorkList.sel(1) T_size_list.cases surjective_pairing wl_decomp)
  then show ?thesis using assms PWL_inv_union_LPWL insert_WL_inv1 WL_minus 
    by (auto simp add: Let_def PWL_map_state_def WL_minus split: if_splits)
qed

lemma parse_steps_time_bound:
  assumes k_bound:"k \<le> length (PWL_map_state pwl2) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)" 
  and res: "parse_steps_time Bs (pwl1, pwl2) k = Some ((pwl3, pwl4), k1)"
  and dist: "distinct ps"
  and invs: "ParseWL_inv pwl1" "ParseWL_inv pwl2"
  and lengs: "leng (fst pwl1) = length Bs" "leng (fst pwl2) = length Bs"
  and wf1: "wf_PWL pwl1 (length Bs)" "wf_PWL pwl2 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and distinct: "set (PWL_map_state pwl1) \<inter> set (PWL_map_state pwl2) = {}" 
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
  shows "k1 \<le> length (PWL_map_state pwl4) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)"
proof-
  let ?C = "(2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12"
  let ?P3 = "\<lambda>((pwl1',pwl2'),k). wf_PWL pwl1' (length Bs) \<and> wf_PWL pwl2' (length Bs) \<and> wf_parse_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((pwl1',pwl2'),k). wf_PWL pwl1' (length Bs) \<and> wf_PWL pwl2' (length Bs) \<and> wf_parse_bins1 (map set Bs) \<and> ParseWL_inv pwl1' \<and> ParseWL_inv pwl2' 
        \<and> leng (fst pwl1') = length Bs \<and> leng (fst pwl2') = length Bs \<and> (\<forall>i < length Bs. length (Bs ! i) \<le> C) \<and> distinct ps 
        \<and> set (PWL_map_state pwl1') \<inter> set (PWL_map_state pwl2') = {}" 
  let ?P2 = "\<lambda>((pwl1',pwl2'),k). k \<le> length (PWL_map_state pwl2') * (?C)"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((pwl1,pwl2),k). PWL_map_state pwl1 \<noteq> [])"
  let ?c = "\<lambda>((pwl1,pwl2),k). (Parse_step_fun Bs (pwl1,pwl2), k + T_Parse_step_fun Bs (pwl1,pwl2))"


  have init: "?P ((pwl1,pwl2), k)" using assms by auto

  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y
    using PWL_inv_parse_step1' PWL_inv_parse_step2' wf_parse_step2' wf_parse_step1' Parse_step_fun_leng1 Parse_step_fun_leng2 Parse_step_fun_dist_sets
    by (smt (verit) case_prodI2' case_prod_conv)
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_Parse_step_fun Bs (a, b) \<le> ?C" using T_parse_step_fun_bound[of a b Bs C] by auto
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "Parse_step_fun Bs (a,b) = (a', b')" by auto
    then have "length (PWL_map_state b') = Suc (length (PWL_map_state b))" 
      using Parse_step_fun_set_inc  assms by auto
    then have 2: "length (PWL_map_state b') * ?C = length (PWL_map_state b) * ?C + ?C"
      by (metis add.commute mult_Suc)
    have "y' \<le> y + ?C" using P1 1 by auto
    also have "... \<le> length (PWL_map_state b) * ?C + ?C" 
      using assms by (auto simp add: add_mult_distrib2)
    also have "... = length (PWL_map_state b') * ?C" using 2 by auto
    finally have "y' \<le> length (PWL_map_state b') * ?C".
    then show "?P2 (?c ((a,b), y))" using P1
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
  qed

  then have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P (?c ((a,b), y)))" for a b y using P1 by auto
  then have "?P ((pwl3,pwl4), k1)"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((pwl1,pwl2),k)", where t="((pwl3,pwl4), k1)"] res init unfolding parse_steps_time.simps
    by (auto simp only:)
  then show "k1 \<le> (length (PWL_map_state pwl4)) * ?C"
    by auto
qed

theorem Parse_steps_time_NF: "wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PWL pwl1 (length Bs) \<Longrightarrow> wf_PWL pwl2 (length Bs) \<Longrightarrow> ParseWL_inv pwl1 \<Longrightarrow> ParseWL_inv pwl2 
  \<Longrightarrow> \<exists>pwl1' pwl2' k'. parse_steps_time Bs (pwl1, pwl2) k = Some ((pwl1', pwl2'), k') \<and> Parse_steps Bs (pwl1, pwl2) = Some (pwl1', pwl2')" 
using wf_step_fun_less[of "length Bs"]
proof (induction "(fst pwl1,fst pwl2)" arbitrary: pwl1 pwl2 k rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "list (fst pwl1) = []"
    thus ?thesis by (simp add: while_option_unfold Parse_steps_def PWL_map_state_def)
  next
    let ?steps = "while_option (\<lambda>(as,bs). PWL_map_state as \<noteq> []) (Parse_step_fun Bs)"
    assume cons: "list (fst pwl1) \<noteq> []"
    then obtain wl1 t ts where P_pwl1: "pwl1 = (wl1, t#ts)" using less.prems(4)
      by (metis PWL_map_state_Cons2 PWL_map_state_def list.exhaust surjective_pairing)
    then obtain pwl1' pwl2'
      where P_step: "(pwl1',pwl2') = Parse_step_fun Bs (pwl1,pwl2)"
      by (metis T_fst.cases)
    then have wf_inv: "wf_PWL pwl1' (length Bs)" "wf_PWL pwl2' (length Bs)" "ParseWL_inv pwl1'" "ParseWL_inv pwl2'"
      using wf_parse_step1 wf_parse_step2 PWL_inv_parse_step1 PWL_inv_parse_step2 less.prems P_pwl1
      by (metis, metis, metis, metis)
      
    from P_step have step_f: "(fst pwl1',fst pwl2') = step_fun (map (map state) Bs) (fst pwl1, fst pwl2)"
      using less.prems Pstep_fun_eq_step_fun1[of pwl1 Bs pwl2 pwl1' pwl2'] cons unfolding PWL_map_state_def by (auto simp add: Let_def)
    have "wf1_WL (fst pwl1) (length Bs) \<and> wf1_WL (fst pwl2) (length Bs)"
      using less.prems wf_PWL_impl_wf1_WL by (cases pwl1, cases pwl2) (auto simp del: wf_PWL.simps ParseWL_inv.simps)
    then have "((fst pwl1',fst pwl2'), (fst pwl1, fst pwl2)) \<in> step_fun_less (length Bs)" 
      using less.prems step_fun_less_step[of "fst pwl1" "(map (map state) Bs)" "fst pwl2"] \<open>list (fst pwl1) \<noteq> []\<close> step_f 
      by (cases pwl1, cases pwl2) (auto simp add: wf_parse_bins1_def wf_bins1_def wf_bin1_def)
    from less.hyps[OF this \<open>wf_parse_bins1 (map set Bs)\<close> wf_inv]
    show ?thesis
      by (simp add: P_step while_option_unfold Parse_steps_def)
  qed
qed

lemma T_Parse_steps_bound: 
  assumes dist: "distinct ps"
  and length_pwl2: "length (PWL_map_state pwl2) = 0"
  and invs: "ParseWL_inv pwl1" "ParseWL_inv pwl2"
  and lengs: "leng (fst pwl1) = length Bs" "leng (fst pwl2) = length Bs"
  and wf1: "wf_PWL pwl1 (length Bs)" "wf_PWL pwl2 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
  shows "T_Parse_steps Bs (pwl1, pwl2) \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)"
proof-
  obtain pwl3 pwl4 k where Psteps_time: "parse_steps_time Bs (pwl1, pwl2) 0 = Some ((pwl3, pwl4), k)" 
    and Psteps: "Parse_steps Bs (pwl1, pwl2) = Some (pwl3, pwl4)"
    using assms Parse_steps_time_NF
    by blast
  have "wf_PWL pwl4 (length Bs)" using Psteps Parse_steps_wf2 wf1 invs by blast
  then have length_bound: "length (PWL_map_state pwl4) \<le> L * Suc K * Suc (length Bs)" 
    using length_fst_PWL Parse_steps_inv2 invs Psteps
    by (metis PWL_map_state_def)
  have "T_Parse_steps Bs (pwl1, pwl2) \<le> length (PWL_map_state pwl4) 
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)"
    using assms Psteps_time parse_steps_time_bound[of 0] by auto
  also have "... \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)" using length_bound by simp
  finally show ?thesis.
qed

lemma T_Parse_close2_L_bound: 
  assumes dist: "distinct ps"
  and invs: "ParseWL_inv pwl1"
  and lengs: "leng (fst pwl1) = length Bs" 
  and wf1: "wf_PWL pwl1 (length Bs)" "wf_parse_bins1 (map set Bs)"
  and max_bin_size: "\<forall>i < length Bs. length (Bs ! i) \<le> C"
shows "T_Parse_close2_L Bs pwl1 \<le> Suc (length Bs) + Suc (length Bs) + L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12) +  Suc (L * Suc K * Suc (length Bs))"
proof-
  have 2: "T_PWL_empty (length Bs) = Suc (length Bs)" by simp
  have 3: "the (T_size Bs) = Suc (length Bs)" by (simp add: T_length_bound)

  have empty_inv: "ParseWL_inv (PWL_empty (length Bs))" and "leng (fst (PWL_empty (length Bs))) = length Bs"
    and empty_wf: "wf_PWL (PWL_empty (length Bs)) (length Bs)"
    and "length (PWL_map_state (PWL_empty (length Bs))) = 0"
    using PWL_inv_empty wf_PWL_empty by (auto simp add: PWL_map_state_def)
  then have 1: "T_Parse_steps Bs (pwl1, PWL_empty (length Bs)) \<le> L * Suc K * Suc (length Bs)
    * ((2 * K * K + 2 * K + 5) * C + (max C L) * (4 * T_nth_WL (length Bs) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (length Bs) * (13 * T_nth_WL (length Bs) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12)" using T_Parse_steps_bound assms by simp

  obtain a where Some_Psteps: "Parse_steps Bs (pwl1, PWL_empty (length Bs)) = Some a"
    using Parse_steps_NF empty_inv empty_wf invs wf1(1,2) by blast

  let ?result_PWL = "(snd (the (Parse_steps Bs (pwl1, PWL_empty (length Bs)))))"
  have "wf_PWL ?result_PWL (length Bs)"
    using wf_Parse_close2_L assms by (auto simp add: Parse_close2_L_def simp del: wf_parse_bin1.simps)
  moreover have res_inv: "ParseWL_inv ?result_PWL" using  Parse_steps_inv2 invs empty_inv empty_wf
    by (metis Parse_steps_NF eq_snd_iff option.sel wf1(1,2))
  ultimately have "length (list (fst ?result_PWL)) \<le> L * Suc K * Suc (length Bs)" using length_fst_PWL by auto
  then have "T_PWL_list ?result_PWL \<le> Suc (L * Suc K * Suc (length Bs))" using res_inv T_zip_eq_len 
    by (cases ?result_PWL) fastforce
  moreover have "T_the (Parse_steps Bs (pwl1, PWL_empty (length Bs))) = 0" using Some_Psteps by auto
  moreover have "T_snd (the (Parse_steps Bs (pwl1, PWL_empty (length Bs)))) = 0" by simp
  ultimately show ?thesis using 1 2 3 unfolding T_Parse_close2_L.simps by presburger
qed

lemma length_Parse_close2_L: 
  assumes "ParseWL_inv pwl" "wf_PWL pwl (length Bs)" "wf_parse_bins1 (map set Bs)"
  shows "length (Parse_close2_L Bs pwl) \<le> L * Suc K * Suc (length Bs)"
proof-
  have empty_inv: "ParseWL_inv (PWL_empty (length Bs))" and empty_wf: "wf_PWL (PWL_empty (length Bs)) (length Bs)" 
    using PWL_inv_empty wf_PWL_empty by auto

  let ?result_PWL = "(snd (the (Parse_steps Bs (pwl, PWL_empty (length Bs)))))"
  have "wf_PWL ?result_PWL (length Bs)"
    using wf_Parse_close2_L assms by (auto simp add: Parse_close2_L_def simp del: wf_parse_bin1.simps)
  moreover have res_inv: "ParseWL_inv ?result_PWL" using  Parse_steps_inv2 empty_inv empty_wf assms
    by (metis Parse_steps_NF eq_snd_iff option.sel)
  ultimately show "length (Parse_close2_L Bs pwl) \<le> L * Suc K * Suc (length Bs)" 
    using length_snd_PWL by (cases ?result_PWL) (auto simp add: Parse_close2_L_def)
qed

lemma Parse_bins_L_lengths: "k \<le> length w \<Longrightarrow> \<forall> i < Suc k. length ((Parse_bins_L k) ! i) \<le> L * Suc K * Suc k"
proof(induction k)
  case 0
  have "length (Parse_close2_L [] (PWL_of_List 0 Parse_Init_L)) \<le> L + L * K" 
    using length_Parse_close2_L[of "PWL_of_List 0 Parse_Init_L" "[]"] PWL_inv_PWL_of_List 
      wf_PWL_of_List[of Parse_Init_L 0 0] wf1_Parse_Init_L ex_map_conv in_set_conv_nth 
      less_nat_zero_code list.distinct(1) wf_parse_bins1_def by fastforce 
  then show ?case 
       by auto
next
  case (Suc k)
  then have ih: "\<forall> i < Suc k. length (Parse_bins_L (Suc k) ! i) \<le> L * Suc K * Suc (Suc k)" 
    by (auto simp add: Let_def nth_append_left)
  let ?scan_pwl = "PWL_of_List (Suc k) (Parse_Scan_L (last (Parse_bins_L k)) k)"
  have "Parse_bins k \<noteq> []"
    by (metis length_parse_bins list.size(3) nat.distinct(1))
  then have "last (Parse_bins_L k) = Parse_bins_L k ! k" using Suc length_parse_bins last_conv_nth
    by (metis One_nat_def Zero_not_Suc diff_Suc_Suc length_Parse_bins list.size(3) minus_nat.diff_0)
  then have "wf_parse_bin1 (set (last (Parse_bins_L k))) k" 
    using Suc wf_parse_bins_L unfolding wf_parse_bins1_def by (auto simp del: wf_parse_bin1.simps)
  then have "wf_PWL ?scan_pwl (length (Parse_bins_L k))" using wf1_Parse_Scan_L Suc wf_PWL_of_List
    using length_Parse_bins less_eq_Suc_le by presburger
  moreover have "ParseWL_inv ?scan_pwl" by (simp add: PWL_inv_PWL_of_List)
  moreover have "wf_parse_bins1 (map set (Parse_bins_L k))" using Suc wf_parse_bins_L by simp
  ultimately have 1: "length (Parse_close2_L (Parse_bins_L k) ?scan_pwl) \<le> L * Suc K * Suc (Suc k)" 
    using length_Parse_close2_L[of ?scan_pwl "Parse_bins_L k"] by auto
  then have "length (Parse_bins_L (Suc k) ! (Suc k)) \<le> L * Suc K * Suc (Suc k)" by (simp add: Let_def nth_append_right)
  then show ?case using ih not_less_less_Suc_eq by blast
qed

lemma leng_PWL_of_List: assumes "wf_parse_bin (set xs) k" 
  shows "leng (fst (PWL_of_List k xs)) = k"
proof-
  have "\<forall>x\<in>set xs. from (state x) < Suc k" using assms by (auto simp add: wf_bin1_def wf_state1_def wf_state_def) 
  then show ?thesis 
    using leng_LWL_union[of "(map state xs)" "WL_empty k"] assms 
    by (auto simp add: PWL_of_List_def)
qed

lemma T_Parse_bins_L_bound:
  assumes "distinct ps" "k \<le> length w"
  shows "T_Parse_bins_L k 
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_WL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 6 + k"
using assms proof(induction k)
  case 0
  have 1: "length Parse_Init_L \<le> L" by (auto simp add: Parse_Init_L_def L_def)
  have "T_PWL_of_List 0 Parse_Init_L \<le> (length Parse_Init_L) * (4 * T_nth_WL (0) + 2 * L * Suc K + 2) + length Parse_Init_L + 2"
    by (metis Nat.add_0_right T_PWL_of_List_bound assms(1) wf1_Parse_Init_L)
  also have "... \<le> L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2) + L + 2"
    using 1 mult_le_mono1[OF 1, of "(4 * T_nth_WL (0) + 2 * L * Suc K + 2)"] by auto
  finally have 2: "T_PWL_of_List 0 Parse_Init_L \<le> L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2) + L + 2".

  have "wf_parse_bins1 (map set [])" by (auto simp add: wf_parse_bins1_def)
  moreover have "\<forall>i<length []. length ([] ! i) \<le> 0" by auto
  moreover have "wf_PWL (PWL_of_List 0 Parse_Init_L) 0" using wf_PWL_of_List wf1_Parse_Init_L by blast
  moreover have "leng (fst (PWL_of_List 0 Parse_Init_L)) = 0" 
    using leng_PWL_of_List wf1_Parse_Init_L by (auto simp add: wf_state1_def )
  ultimately have "T_Parse_close2_L [] (PWL_of_List 0 Parse_Init_L) \<le> 1 + 1 + L * Suc K  
    * (L * (4 * T_nth_WL (0) + 2 * L * Suc K + 3)
    + Suc L * Suc K  * (13 * T_nth_WL (0) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12) +  Suc (L * Suc K)" 
    using T_Parse_close2_L_bound[of "PWL_of_List 0 Parse_Init_L" "[]" 0] assms PWL_inv_PWL_of_List 
    by (auto simp del: T_Parse_close2_L.simps)
  also have "... \<le> L * Suc K  * (Suc L * Suc K  * (17 * T_nth_WL (0) + 5 * L * Suc K + 19) + 13) + 3" 
    by (auto simp add: algebra_simps)
  finally have "T_Parse_close2_L [] (PWL_of_List 0 Parse_Init_L) 
    \<le> L * Suc K  * (Suc L * Suc K  * (17 * T_nth_WL (0) + 5 * L * Suc K + 19) + 13) + 3".

  then have "T_Parse_bins_L 0 \<le> L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2) + L + 2
    + L * Suc K  * (Suc L * Suc K  * (17 * T_nth_WL (0) + 5 * L * Suc K + 19) + 13) + 3 + 1"
    using 2 by auto
  also have "... \<le> L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2)
    + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_WL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 6" 
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
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_item1.simps)
  then have wf_last: "wf_parse_bin (set (last ?Bs)) k" using Suc by (auto simp add: wf_state1_def)

  have 1: "the (T_size ?Bs) = k + 2" by (auto simp add: T_length_bound)
  have 2: "T_last ?Bs = k + 1" using T_last_bound cons by auto
  have "T_Parse_Scan_L (last ?Bs) k \<le> k + (2 * K + 4) * (length (last (Parse_bins_L k))) + 3"
    using wf_last Suc T_Parse_Scan_L_bound
    by (auto simp add: w_def simp del: T_Parse_Scan_L.simps)
  also have "... \<le> k + (2 * K + 4) * (L * Suc K * Suc k) + 3" using length_last by auto
  finally have 3: "T_Parse_Scan_L (last ?Bs) k \<le> k + (2 * K + 4) * (L * Suc K * Suc k) + 3".

  let ?parse = "Parse_Scan_L (last ?Bs) k"
  have "length ?parse \<le> length (last ?Bs)" 
    unfolding Parse_Scan_L_def Let_def by simp
  then have length_parse: "length ?parse \<le> L * Suc K * Suc k" using length_last by auto
  have "T_PWL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k) 
    \<le> length ?parse * (4 * T_nth_WL (length ?Bs) + 2 * L * Suc K + 2) + length ?parse + length ?Bs + 2" 
    using T_PWL_of_List_bound[of ?parse "length ?Bs"] wf1_Parse_Scan_L wf1_last Suc 
    by (auto simp del: T_PWL_of_List.simps wf_parse_bin1.simps)
  also have "... \<le> L * Suc K * Suc k * (4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 2" 
    using length_parse mult_le_mono1[OF length_parse, of "(4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2)"]
    by auto
  finally have 4: "T_PWL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k)
    \<le> L * Suc K * Suc k * (4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 2".

  have 5: "T_append ?Bs [Parse_close2_L ?Bs (PWL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k))] 
    = k+2" by simp

  let ?parse_pwl = "PWL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k)"
  have wf1_parse: "wf_parse_bin1 (set ?parse) (Suc k)" using wf1_Parse_Scan_L wf1_last Suc 
    by (auto simp del: wf_parse_bin1.simps)
  have "ParseWL_inv ?parse_pwl" using PWL_inv_PWL_of_List by simp
  moreover have "wf_PWL ?parse_pwl (Suc k)" using wf_PWL_of_List wf1_Parse_Scan_L wf1_last Suc 
    by (auto simp del: wf_parse_bin1.simps)
  moreover have "leng (fst ?parse_pwl) = Suc k" 
    using leng_PWL_of_List[of ?parse "Suc k"] wf1_parse by (auto simp add: wf_state1_def)
  ultimately have 6: "T_Parse_close2_L ?Bs (PWL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k))
    \<le> Suc (Suc k) + Suc (Suc k) + L * Suc K * Suc (Suc k)
    * ((2 * K * K + 2 * K + 5) * (L * Suc K * Suc k) + (L * Suc K * Suc k) * (4 * T_nth_WL (Suc k) + 2 * L * Suc K + 3)
    + Suc L * Suc K * Suc (Suc k) * (13 * T_nth_WL (Suc k) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 12) +  Suc (L * Suc K * Suc (Suc k))"
    using T_Parse_close2_L_bound[of ?parse_pwl ?Bs "L * Suc K * Suc k"] Parse_bins_L_lengths wf_parse_bins_L Suc 
    by (auto simp del: T_Parse_close2_L.simps wf_parse_bin1.simps)
  also have "... = L * Suc K * Suc (Suc k)
    * ((L * Suc K * Suc k) * (4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2 * K * K + 2 * K + 8)
    + Suc L * Suc K * Suc (Suc k) * (13 * T_nth_WL (Suc k) + 3 * L * Suc K + 7)
    + 9 * Suc K * L + 13) + 2 * k + 5" by (auto simp add: algebra_simps)
  also have "... \<le> L * Suc K * Suc (Suc k)
    * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 13) 
    + 2 * k + 5" by (auto simp add: algebra_simps)
  finally have 7:  "T_Parse_close2_L ?Bs (PWL_of_List (length ?Bs) (Parse_Scan_L (last ?Bs) k))
    \<le> L * Suc K * Suc (Suc k)
      * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 13) 
      + 2 * k + 5".

  have "T_Parse_bins_L k \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_WL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 6 + k"
    using Suc by simp
  also have "... \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_WL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 6 + k"
  proof-
    have "T_nth_WL k \<le> T_nth_WL (Suc k)" using mono_nth incseqD[of T_nth_WL k "Suc k"] by simp
    then have 1: "4 * T_nth_WL (k) + 2 * L * Suc K + 2 * K + 20 \<le> 4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2 * K + 20"
      by auto
    then have "17 * T_nth_WL (k) + 5 * L * Suc K + 4 * K * K + 24 
        \<le> 17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24" by auto
    then have "Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (k) + 5 * L * Suc K + 4 * K * K + 24)
        \<le> Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)"
      using mult_le_mono2 by blast
    then have "(Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (k) + 2 * L * Suc K + 2 * K + 20)
        \<le> (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2 * K + 20)" using 1 add_le_mono[OF _ 1] by (simp only:)
    then show ?thesis by auto
  qed
  finally have "T_Parse_bins_L k \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_WL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 6 + k".

  then have "T_Parse_bins_L (Suc k)
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_WL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 6 + k
      +
      k + 2 + k + 1 + k + (2 * K + 4) * (L * Suc K * Suc k) + 3
      + L * Suc K * Suc k * (4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2) + L * Suc K * Suc k + Suc k + 2
      + L * Suc K * Suc (Suc k)
      * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 13) 
      + 2 * k + 5 + k + 2 + 1" unfolding T_Parse_bins_L.simps Let_def using 1 2 3 4 5 7 by presburger
  
  also have "... \<le> Suc k *
       (L * Suc K * Suc (Suc (Suc k)) *
        (Suc L * Suc K * Suc (Suc (Suc k)) * (17 * T_nth_WL (Suc k) + 5 * L * Suc K + 4 * K * K + 24) + 4 * T_nth_WL (Suc k) + 2 * L * Suc K + 2 * K + 20) +
        7 * Suc k +
        16) +
       L * (4 * T_nth_WL 0 + 2 * L * Suc K + 2) +
       L * Suc K * (Suc L * Suc K * (21 * T_nth_WL 0 + 5 * L * Suc K + 19) + 2 * L + 15) +
       L +
       6 +
       Suc k" by (auto simp add: algebra_simps)
  finally show ?case.
qed

definition C3 where "C3 = (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))"
definition C4 where "C4 = (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)"
definition C6 where "C6 = L * Suc K * Suc L * Suc K * 17"
definition C7 where "C7 = L * Suc K * 4"
definition C5 where "C5 = L * Suc K  * (Suc L * Suc K  * (25 * T_nth_WL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 4"


theorem T_Parse_bins_bound_nice:
  assumes "distinct ps" "k \<le> length w"
  shows "T_Parse_bins_L k 
      \<le> (k+2)^3 * C3 + (k+2)^2 * C4 + (k+2) * 3 + C5 
        + (k+2)^3 * T_nth_WL (k) * C6 + (k+2)^2 * T_nth_WL (k) * C7"
proof-
  have "T_Parse_bins_L k 
      \<le> k * (L * Suc K * Suc (Suc k)
          * (Suc L * Suc K * Suc (Suc k) * (17 * T_nth_WL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * k + 16)
        + L * (4 * T_nth_WL (0) + 2 * L * Suc K + 2)
        + L * Suc K  * (Suc L * Suc K  * (21 * T_nth_WL (0) + 5 * L * Suc K + 19) + 2 * L + 15) + L + 6 + k"
    using T_Parse_bins_L_bound assms by simp
  also have "... \<le> (k+2) * (L * Suc K * (k+2)
          * (Suc L * Suc K * (k+2) * (17 * T_nth_WL (k) + 5 * L * Suc K + 4 * K * K + 24)
            + 4 * T_nth_WL (k) + 2 * L * Suc K + 2 * K + 20)
          + 7 * (k + 2) + 2)
        + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_WL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 6 + k"
    by (auto simp add: algebra_simps)
  also have "... = (k+2) * (k+2) * (k+2) * (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))
    + (k+2) * (k+2) * (k+2) * (L * Suc K * Suc L * Suc K * 17 * T_nth_WL (k))
    + (k+2) * (k+2) * (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)
    + (k+2) * (k+2) * (L * Suc K * 4 * T_nth_WL (k))
    + (k+2) * 3
    + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_WL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 4"
    by (auto simp add: algebra_simps)
  also have "... = (k+2)^3 * (L * Suc K * Suc L * Suc K * (5 * L * Suc K + 4 * K * K + 24))
    + (k+2)^3 * (L * Suc K * Suc L * Suc K * 17 * T_nth_WL (k))
    + (k+2)^2 * (L * Suc K * (2 * L * Suc K + 2 * K + 20) + 7)
    + (k+2)^2 * (L * Suc K * 4 * T_nth_WL (k))
    + (k+2) * 3 
    + L * Suc K  * (Suc L * Suc K  * (25 * T_nth_WL (0) + 5 * L * Suc K + 20) + 2 * L + 17) + L + 4" 
    by (simp only: monoid_mult_class.power3_eq_cube monoid_mult_class.power2_eq_square)
  finally show ?thesis by (auto simp add: C3_def C4_def C5_def C6_def C7_def algebra_simps)
qed

end


(*korrektheit ohne Eindeutigkeits beweis aus Early.thy*)

(*literature for linear runtime grammars*)

definition ps where "ps = [((0::nat), [Tm (1::int)]), (0, [Nt (0::nat), Nt 0])]"
definition S :: nat where "S = 0"
definition w1 where "w1 = [1, 1, (1 :: int)]"

interpretation Earley_Gw_eps
  where ps = ps and S = S and w0 = w1 
proof
  show "Earley_Gw.\<epsilon>_free ps" by (auto simp add: Earley_Gw.\<epsilon>_free_def ps_def rhs_def)
qed

declare Earley_Gw.Predict_L_def[code]
declare Earley_Gw.mv_dot_def[code]
declare Earley_Gw.Complete_L_def[code]
declare Earley_Gw.Scan_L_def[code]
declare Earley_Gw.minus_L_def[code]
declare Earley_Gw.Init_L_def[code]
declare Earley_Gw.step_fun.simps[code]
declare Earley_Gw.steps_def[code]
declare Earley_Gw.close2_L_def[code]
declare Earley_Gw.bins_L.simps[code]
declare Earley_Gw.w_def[code]

declare Earley_Gw.WL_of_List_def[code]
declare Earley_Gw.union_LWL.simps[code]
declare Earley_Gw.minus_WL_def[code]
declare Earley_Gw.WL_empty_def[code]
declare Earley_Gw.insert.simps[code]
declare Earley_Gw.empty_list_map.simps[code]
declare Earley_Gw.minus_LWL.simps[code]
declare Earley_Gw.upsize.simps[code]
declare Earley_Gw.isin.simps[code]

value "bins_L 0"
value "bins_L 1"
value "bins_L 2"
value "bins_L 3"

unused_thms
end