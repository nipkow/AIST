theory EarleyWorklist

imports "Earley" "HOL-Library.While_Combinator" "HOL-Data_Structures.Define_Time_Function" "HOL-Data_Structures.Set_Specs"

begin

context Earley_Gw
begin

(* must not be empty, otherwise by def step_rel is always false *)
definition step_rel :: "('n, 'a) state set list \<Rightarrow> ('n, 'a) state set \<times> ('n, 'a) state set \<Rightarrow> ('n, 'a) state set \<times> ('n, 'a) state set \<Rightarrow> bool" where
"step_rel  \<equiv> Close2"

(*fun Predict_L_help :: "('n, 'a) prods \<Rightarrow> ('n, 'a) state \<Rightarrow> nat \<Rightarrow> ('n, 'a) state list" where
  "Predict_L_help [] x k = []"
| "Predict_L_help (p#Ps) x k = (let ps' = (Predict_L_help Ps x k) in (if next_sym_Nt x (lhs p) then (State p 0 k) # ps' else ps' ))"*)

(*fun Predict_L_eps_complete where
  "Predict_L_eps_complete = undefined"*)

(*definition Predict_L :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> ('n,'a) state list" where
  "Predict_L x k = Predict_L_help ps x k"*)

definition Predict_L :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> ('n,'a) state list" where
  "Predict_L x k = map (\<lambda>p. State p 0 k) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps)"

(*fun Complete_L_help :: "('n, 'a) state list \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) state list" where
  "Complete_L_help [] y = []"
| "Complete_L_help (b#bs) y = (let acc = Complete_L_help bs y in (if next_sym_Nt b (lhs(prod y)) then (mv_dot b) # acc else acc))"*)

definition Complete_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) state list" where
  "Complete_L Bs y = map mv_dot (filter (\<lambda> b. next_sym_Nt b (lhs(prod y))) (Bs ! from y))"
 (*= Complete_L_help (Bs ! from y) y"*)

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

(*fun list_remove :: "'c list \<Rightarrow> 'c \<Rightarrow> 'c list" where
"list_remove [] x = []" |
"list_remove (a#as) x = (if a = x then list_remove as x else a # (list_remove as x))"*)

datatype ('c,'d) WorkList = 
  WorkList ("list": "('c,'d) state list") ("leng" : nat) ("list_map" : "('c,'d) state list list")

fun WL_inv :: "('n, 'a) WorkList \<Rightarrow> bool" where
"WL_inv (WorkList as l m) = (Suc l = length m \<and> (\<forall>x \<in> set as. from x < Suc l) \<and> (\<forall>i < Suc l. set (m ! i) = {x \<in> set as. from x = i}) \<and> (\<forall>i < Suc l. distinct (m ! i)) \<and> distinct as)"

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

lemma WL_inv_upsize: "WL_inv (WorkList as l m) \<Longrightarrow> WL_inv (upsize (WorkList as l m) k)"
proof -
  assume assm: "WL_inv (WorkList as l m)"
  then show ?thesis 
  proof (cases k)
    case 0
    then show ?thesis using assm by auto
  next
    case (Suc n)
    have 1: "i < Suc l + k \<Longrightarrow> set ((m @ empty_list_map n) ! i) = {x \<in> set as. from x = i}" for i
      using assm Suc by (cases "i < length m") (auto simp add: nth_append_left nth_append_right nth_empty_list_map)
    have "i < Suc l + k \<Longrightarrow> distinct ((m @ empty_list_map n) ! i)" for i
      using assm Suc by (cases "i < length m") (auto simp add: nth_append_left nth_append_right nth_empty_list_map)
    then show ?thesis using assm Suc 1 by (auto simp add: leng_empty_list_map)
  qed
qed

lemma upsize_length: "upsize (WorkList as l m) k = WorkList as' l' m' \<Longrightarrow> l' = k + l"
  by (metis Earley_Gw.WorkList.sel(2) Earley_Gw.upsize.elims add.commute add_cancel_left_left)

lemma upsize_list: "list (upsize (WorkList as l m) k) = as"
  by (cases k) auto

lemma upsize_list1: "list (upsize wl k) = list wl"
  using upsize_list by (metis WL_inv.cases WorkList.sel(1))

lemma set_upsize: "set_WorkList (upsize (WorkList as l m) k) = set_WorkList (WorkList as l m)"
  by (cases k) auto

lemma set_upsize1: "set_WorkList (upsize wl k) = set_WorkList wl"
  using set_upsize by (metis WL_inv.cases)

lemma WL_insert: "WL_inv (WorkList as l m) \<Longrightarrow> set_WorkList (insert (WorkList as l m) x) = set_WorkList ((WorkList as l m)) \<union> {x}"
  using set_upsize[of _ _ _ "(Suc (from x) - l)"] by (auto simp add: Let_def isin_WL simp del: isin.simps)

lemma WL_insert1: "WL_inv wl \<Longrightarrow> set_WorkList (insert wl x) = set_WorkList wl \<union> {x}"
  using WL_insert by (metis WL_inv.cases)

lemma list_map_inv: "x \<notin> set as \<Longrightarrow> from x < Suc l \<Longrightarrow> WL_inv (WorkList as l m) \<Longrightarrow> WL_inv (WorkList (x#as) l (m[from x := x#(m!from x)]))"
proof -
  assume assm: "x \<notin> set as" "from x < Suc l" "WL_inv (WorkList as l m)"
  have 1: "i < Suc l \<Longrightarrow> set (m[from x := x#(m!from x)] ! i) = {y \<in> set (x#as). from y = i}" for i
    using assm by (cases "i = from x") auto
  have "i < Suc l \<Longrightarrow> distinct (m[from x := x#(m!from x)] ! i)" for i
      using assm by (cases "i = from x") auto 
  then show ?thesis using assm 1 by auto
qed

lemma insert_WL_inv: "WL_inv (WorkList as l m) \<Longrightarrow> WL_inv (insert (WorkList as l m) x)"
proof -
  let ?wl = "(upsize (WorkList as l m) (Suc (from x) - l))"
  assume assm: "WL_inv (WorkList as l m)"
  then have "WL_inv ?wl" by (auto simp add: WL_inv_upsize)
  then obtain k n where P: "?wl = WorkList as k n \<and> WL_inv (WorkList as k n)"
    by (metis Earley_Gw.WL_inv.cases upsize_list upsize_list1)
  have 1: "from x < k" using P upsize_length
    by (metis less_diff_conv less_not_refl not_less_eq)

  then show ?thesis using assm P list_map_inv by (auto simp add: isin_WL simp del: WL_inv.simps isin.simps)
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

lemma step_fun_sound: "as \<noteq> [] \<Longrightarrow> wf1_WL (WorkList as l1 m1) (length Bs) \<Longrightarrow> WL_inv (WorkList as l1 m1) \<Longrightarrow> WL_inv (WorkList bs l2 m2)
 \<Longrightarrow> step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))
 \<Longrightarrow> step_rel (map set Bs) (set as,set bs) (set as', set bs')"
proof-
  assume assms: "as \<noteq> []" 
    and wf: "wf1_WL (WorkList as l1 m1) (length Bs)"
    and inv: "WL_inv (WorkList as l1 m1)" "WL_inv (WorkList bs l2 m2)"
    and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
  have comp: "\<forall>a \<in> set as. is_complete a \<longrightarrow> from a < length Bs" using wf by (auto simp add: wf_bin1_def wf_state1_def)
  from assms obtain a ass where P :"as = a # ass"
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

lemma wf1_Complete_L: "wf_bins1 (map set Bs) \<Longrightarrow> wf_state1 st (length Bs) \<Longrightarrow> is_complete st \<Longrightarrow> wf_bin1 (set (Complete_L Bs st)) (length Bs)"
proof-
  assume assms: "wf_bins1 (map set Bs)" "wf_state1 st (length Bs)" "is_complete st"
  then have 1: "\<forall>x \<in>  (set (filter (\<lambda> b. next_sym_Nt b (lhs(prod st))) (Bs ! from st))). wf_state x (from st)"
    by (simp add: wf_bin1_def wf_bins1_def wf_state1_def)
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


lemma step_fun_wf_states: "\<lbrakk>wf_bins1 (map set Bs); wf1_WL wl1 (length Bs); wf1_WL wl2 (length Bs); WL_inv wl1; WL_inv wl2; (list wl1) \<noteq> [] \<rbrakk>
 \<Longrightarrow> \<exists>B' C'. step_fun Bs (wl1,wl2) = (B',C') \<and> WL_inv B' \<and> WL_inv C' \<and> wf1_WL B' (length Bs) \<and> wf1_WL C' (length Bs)"
proof-
  assume assms: "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)" "wf1_WL wl2 (length Bs)" "WL_inv wl1" "WL_inv wl2" "(list wl1) \<noteq> []"
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

lemma close2_L_eq_Close1: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_WL wl (length Bs) \<Longrightarrow> WL_inv wl \<Longrightarrow> set (close2_L Bs wl) = Close1 (map set Bs) (set (list wl))"
proof-
  assume assms: "wf_bins1 (map set Bs)" "wf1_WL wl (length Bs)" "WL_inv wl"

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

lemma card_wf: "\<forall>p \<in> set ps. length (rhs p) \<le> k \<Longrightarrow> \<forall>x \<in> bs. wf_state x i \<Longrightarrow> card bs \<le> (length ps) * (Suc k) * (Suc i)"
proof -
  assume assm: "\<forall>p \<in> set ps. length (rhs p) \<le> k" "\<forall>x \<in> bs. wf_state x i"
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
      by (metis Earley_Gw.wf_state_def state.exhaust_sel assm(2))
    then obtain p m j where x: "x = State p m j" and wf: "p \<in> P \<and> m \<le> length (rhs p) \<and> j \<le> i \<and> i \<le> length w" by blast
    then have 1: "(p, m, j) \<in> Top" using assm by (auto simp add: Top_def)
    have "?f (p, m, j) = x" using x by simp
    then show "x \<in> (\<lambda>(p, m, k). State p m k) ` Top" using 1 by blast
  qed

  then have "card  bs \<le> card Top" using fin
    by (simp add: surj_card_le)
  then show ?thesis using top_card card_length
    by (metis (no_types, lifting) dual_order.trans mult_le_mono1)
qed

lemma prod_length_bound: "p \<in> set ps \<Longrightarrow> length (rhs p) \<le> K"
proof-
  assume assm: "p \<in> set ps"
  have "K = Max (length ` (rhs ` (set ps)))" using K_def
    by (metis Setcompr_eq_image image_image)
  then show ?thesis using assm K_def by auto
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
  fixes f:: "nat \<Rightarrow> nat"
  assumes T_nth_Bound: "(T_nth :: ('a, 'b) state list list \<Rightarrow> nat \<Rightarrow> nat) as k \<le> f k"
  and T_update_Bound: "(T_list_update :: ('a, 'b) state list list \<Rightarrow> nat \<Rightarrow> ('a, 'b) state list \<Rightarrow> nat) as k a \<le> f k"
  and mono_f: "monotone (\<le>) (\<le>) f"
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

lemma T_next_symbol_bound: "prod s \<in> set ps \<Longrightarrow> T_next_symbol s \<le> 2*(Suc K)"
proof-
  assume assm: "prod s \<in> set ps"
  then have "length (rhs (prod s)) \<le> K" using prod_length_bound by auto
  then show ?thesis 
    using assm T_nth_general[of "dot s" "rhs (state.prod s)"] by (auto simp add: T_length_bound is_complete_def)
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

lemma T_Scan_L_bound: "k < length w0 \<Longrightarrow> wf_bin1 (set Bs) l \<Longrightarrow> T_Scan_L Bs k \<le> k + 2*(K + 2) * length Bs + 3"
proof-
  assume "k < length w0" and wf: "wf_bin1 (set Bs) l"
  then have 1: "T_nth w0 k \<le> k+1" by (auto simp add: T_nth_general)

  have 2: "T_filter T_next_symbol Bs \<le> 2*(Suc K) * length Bs + length Bs + 1" 
    using T_next_symbol_bound wf T_filter_bound[of Bs T_next_symbol "2*(Suc K)"] 
    by (auto simp add: wf_bin1_def wf_state1_def wf_state_def)

  have "T_map T_mv_dot (filter (\<lambda>b. next_symbol b = Some (Tm (w0 ! k))) Bs) 
            \<le> length (filter (\<lambda>b. next_symbol b = Some (Tm (w0 ! k))) Bs) + 1"
    using T_map_bound[of _ T_mv_dot 0] by auto
  also have "... \<le> length Bs + 1" by auto

  finally show ?thesis using 1 2 by (auto simp add: Let_def)
qed

lemma T_Predict_L_bound: "prod x \<in> set ps \<Longrightarrow> T_Predict_L x k \<le> 2*(K + 2)* length ps + 2"
proof-
  assume "prod x \<in> set ps"
  then have "\<forall>p \<in> set ps. (\<lambda>p. T_next_symbol x + T_fst p) p \<le> 2*(Suc K)"
    using T_next_symbol_bound[of x] by auto
  then have 1: "T_filter (\<lambda>p. T_next_symbol x + T_fst p) ps \<le> 2*(Suc K) * length ps + length ps + 1"
    using T_filter_bound[of ps _ "2*(Suc K)"] by auto

  have "T_map (\<lambda>p. 0) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps) \<le> length (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps) + 1"
    using T_map_bound[of _ "(\<lambda>p. 0)" 0] by auto
  also have "... \<le> length ps + 1" by auto
  finally show ?thesis using 1 by auto
qed


lemma T_Complete_L_bound: "from y < length Bs \<Longrightarrow> wf_bins1 (map set Bs) 
  \<Longrightarrow> T_Complete_L Bs y \<le> f (from y) + 2*(K + 2) * length (Bs ! from y) + 2"
proof -
  assume assms: "from y < length Bs" "wf_bins1 (map set Bs)"
  have 1: "T_nth Bs (from y) \<le> f (from y)" using T_nth_Bound by simp
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

lemma T_isin_general: "WL_inv wl \<Longrightarrow> T_isin wl x \<le> f (from x) + length ((list_map wl) ! from x) + 1"
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

lemma T_isin_wf: "distinct ps \<Longrightarrow> WL_inv wl \<Longrightarrow> wf1_WL wl k \<Longrightarrow> T_isin wl x \<le> f (from x) + L * (Suc K) + 1"
proof-
  assume inv: "WL_inv wl" and wf: "wf1_WL wl k" and dist: "distinct ps"
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


lemma T_insert_less: "distinct ps \<Longrightarrow> WL_inv wl \<Longrightarrow> wf1_WL wl k \<Longrightarrow> from x < Suc (leng wl) \<Longrightarrow> T_insert wl x \<le> 3 * f (from x) + L * (Suc K) + 1"
proof-
  assume le: "from x < Suc (leng wl)" and other: "WL_inv wl" "wf1_WL wl k" "distinct ps"
  obtain as l m where "wl = WorkList as l m"
    using WL_inv.cases by blast
  then have "T_insert wl x \<le> T_isin wl x + T_nth m (from x) + T_list_update m (from x) (x # m ! from x)" using le by auto
  also have "... \<le> f (from x) + L * (Suc K) + 1 + f (from x) + f (from x)" 
    using other T_isin_wf[of wl k x] T_nth_Bound[of m "from x"] T_update_Bound[of m "from x" "x # m ! from x"] by auto
  finally show ?thesis by auto
qed

lemma wf1_WL_insert: "WL_inv wl \<Longrightarrow> wf1_WL wl k \<Longrightarrow> wf_state1 x k \<Longrightarrow> wf1_WL (insert wl x) k"
  using WL_insert1 wf_bin1_def by auto

            
lemma wf1_WL_union_LWL: "WL_inv wl \<Longrightarrow> wf1_WL wl k \<Longrightarrow> wf_bin1 (set xs) k \<Longrightarrow> wf1_WL (union_LWL xs wl) k"
  using LWL_union wf_bin1_def by fastforce

lemma leng_WL_insert: "from a < Suc (leng wl) \<Longrightarrow> leng (insert wl a) = leng wl"
proof-
  assume assm: "from a < Suc (leng wl)"
  obtain as l m where "wl = WorkList as l m"
    using WL_inv.cases by blast
  then show ?thesis using assm by auto
qed

lemma leng_LWL_union: "\<forall>x \<in> set as. from x < Suc (leng wl) \<Longrightarrow> leng (union_LWL as wl) = leng wl"
  by (induction as arbitrary: wl) (auto simp add: leng_WL_insert)

lemma T_union_LWL_wf: "distinct ps \<Longrightarrow> WL_inv wl \<Longrightarrow> wf1_WL wl (leng wl) \<Longrightarrow> wf_bin1 (set as) (leng wl) 
  \<Longrightarrow> T_union_LWL as wl \<le> (length as) * (3 * f (leng wl) + L * (Suc K) + 2) + 1"
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
  also have "... \<le> (length as) * (3 * f (leng wl) + L * (Suc K) + 2) + 1 + 3 * f (from a) + L * (Suc K) + 1 + 1" 
    using Cons T_insert_less[of "union_LWL as wl" "leng wl" a] 1 2 by (fastforce simp add: wf_bin1_def)
  also have "... \<le> (length as) * (3 * f (leng wl) + L * (Suc K) + 2) + 1 + 3 * f (leng wl) + L * (Suc K) + 1 + 1"
    using mono_f 3 by (auto simp add: incseqD)
  finally show ?case by auto
qed

lemma [simp]: "T_WL_empty k = k + 1"
  by (induction k) auto

lemma [simp]: "leng (WL_empty k) = k"
  by (induction k) (auto simp add: WL_empty_def)

lemma wf1_WL_empty: "wf1_WL (WL_empty k) l"
  using set_WL_empty by (auto simp add: wf_bin1_def)

lemma wf1_WL_minus_LWL: "WL_inv wl \<Longrightarrow> wf_bin1 (set xs) k \<Longrightarrow> wf1_WL (minus_LWL k xs wl) k"
  using LWL_minus by (auto simp add: wf_bin1_def)

lemma leng_minus_LWL: "\<forall>x \<in> set xs. from x < Suc k \<Longrightarrow> leng (minus_LWL k xs wl) = k"
  using leng_WL_insert by (induction xs) auto

lemma T_minus_LWL_wf: "distinct ps \<Longrightarrow> wf1_WL wl k \<Longrightarrow>  WL_inv wl \<Longrightarrow> wf_bin1 (set as) k
  \<Longrightarrow> T_minus_LWL k as wl \<le> (length as) * (4 * f k + 2*L * (Suc K) + 4) + k + 2 + length as"
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
  also have "... \<le> f (from a) + L * (Suc K) + 1 + T_minus_LWL k as wl + T_insert (minus_LWL k as wl) a + 1" 
    using Cons T_isin_wf by auto
  also have "... \<le> f (from a) + L * (Suc K) + 1 + (length as) * (4 * f k + 2*L * (Suc K) + 4) + k + 2 + length as + T_insert (minus_LWL k as wl) a + 1"
    using Cons 1 by auto
  also have "... \<le> f (from a) + L * (Suc K) + 1 + (length as) * (4 * f k + 2*L * (Suc K) + 4) + k + 2 + length as + 3 * f (from a) + L * (Suc K) + 1 + 1"
    using T_insert_less[of "minus_LWL k as wl" k a] Cons 2 3 by linarith
  also have "... \<le> f k + L * (Suc K) + 1 + (length as) * (4 * f k + 2*L * (Suc K) + 4) + k + 1 + length as + 3 * f k + L * (Suc K) + 2 + 1"
    using mono_f 4 by (auto simp add: incseqD)
  also have "... \<le> (length (a#as)) * (4 * f k + 2*L * (Suc K) + 4) + k + 2 + (length (a#as))" by simp
  finally show ?case by simp
qed

lemma T_minus_WL_wf: "distinct ps \<Longrightarrow> wf1_WL wl1 (leng wl1) \<Longrightarrow> WL_inv wl1 \<Longrightarrow> WL_inv wl2 \<Longrightarrow> wf1_WL wl2 (leng wl1)
  \<Longrightarrow> T_minus_WL wl1 wl2 \<le> (length (list wl1)) * (4 * f (leng wl1) + 2*L * (Suc K) + 4) + (leng wl1) + 2 + length (list wl1)"
  using T_minus_LWL_wf[of wl2 "leng wl1" "list wl1"] by auto

(*List procedures are distinct*)

lemma distinct_Init: "distinct ps \<Longrightarrow> distinct Init_L"
proof -                                           
  assume assm: "distinct ps"
  have "inj_on (\<lambda> p. State p 0 0) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. State p 0 0) ps)" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Init_L_def distinct_map_filter)
qed

lemma distinct_Predict_L: "distinct ps \<Longrightarrow> distinct (Predict_L x k)"
proof -                                           
  assume assm: "distinct ps"
  have "inj_on (\<lambda>p. State p 0 k) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. State p 0 k) ps)" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Predict_L_def distinct_map_filter)
qed

lemma distinct_Complete_L: "distinct (Bs ! from y) \<Longrightarrow> distinct (Complete_L Bs y)"
proof -                                           
  assume assm: "distinct (Bs ! from y)"
  have "inj_on mv_dot (set (Bs ! from y))"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel state.expand state.inject)
  then have "distinct (map mv_dot (Bs ! from y))" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Complete_L_def distinct_map_filter)
qed

lemma distinct_Scan_L: "distinct B \<Longrightarrow> distinct (Scan_L B k)"
proof -                                           
  assume assm: "distinct B"
  have "inj_on mv_dot (set B)"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel state.expand state.inject)
  then have "distinct (map mv_dot B)" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Scan_L_def distinct_map_filter)
qed

lemma wfbin1_impl_wfbin: "wf_bin1 xs k \<Longrightarrow> wf_bin xs k"
  by (auto simp add: wf_bin1_def wf_state1_def)

lemma mult_mono_mix: "i \<le> (j :: nat) \<Longrightarrow> k * i * l \<le> k * j * l"
  by simp

(* actual time bounds*)

lemma T_step_fun_bound: assumes "(list wl1) \<noteq> []" "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf1_WL wl1 (length Bs)" "WL_inv wl1" "leng wl1 = length Bs"
  "wf1_WL wl2 (length Bs)" "WL_inv wl2" "leng wl2 = length Bs"
shows "T_step_fun Bs (wl1, wl2) 
    \<le> L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
proof-
  obtain bs l m where WL1: "wl1 = WorkList bs l m"
    using WL_inv.cases by blast
  obtain b bss where bbs: "bs = b#bss" using assms WL1
    using Earley_Gw.WorkList.sel(1) T_last.cases by blast

  have from_b: "from b \<le> length Bs"
    using assms by (simp add: WL1 bbs wf_bin1_def wf_state1_def wf_state_def)

  let ?step = "if is_complete b then Complete_L Bs b else Predict_L b (length Bs)"
  let ?t_step = "(if is_complete b then T_Complete_L Bs b else the (T_size Bs) + T_Predict_L b (length Bs))"
  have t_step: "?t_step \<le> f (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2 + Suc (length Bs)"
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

    have "T_Complete_L Bs b \<le> f (from b) + 2 * (K + 2) * length (Bs ! from b) + 2"
      using assms T_Complete_L_bound 1 by (auto simp add: WL1 bbs simp del: T_Complete_L.simps)
    also have "... \<le> f (from b) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2" 
      using mult_le_mono2[OF 4]
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) add_le_mono1 nat_add_left_cancel_le)
    also have "... \<le> f (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2"
      using mono_f 1 by (auto simp add: incseqD)
    finally have "T_Complete_L Bs b \<le> f (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2".
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
  then have "T_union_LWL (?step) wl1 \<le> length (?step) * (3 * f (length Bs) + L * Suc K + 2) + 1"
    using T_union_LWL_wf[of wl1 ?step] assms wfStep  by (auto simp add: WL1)
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (3 * f (length Bs) + L * Suc K + 2) + 1"
    using mult_le_mono1[OF lengthStep]
    using add_le_mono1 by blast
  finally have 7: "T_union_LWL ?step wl1 \<le> L * (Suc K) * (Suc (length Bs)) * (3 * f (length Bs) + L * Suc K + 2) + 1".

  have "T_insert wl2 b \<le> 3 * f (from b) + L * Suc K + 1"
    using T_insert_less[of wl2 _ b] from_b assms by auto
  also have "... \<le> 3 * f (length Bs) + L * Suc K + 1"
    using mono_f from_b by (auto simp add: incseqD)
  finally have 8: "T_insert wl2 b \<le> 3 * f (length Bs) + L * Suc K + 1".

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
  have "?minus \<le> length bs' * (4 * f (length Bs) + 2 * L * Suc K + 4) + length Bs + 2 + length bs'"
    using T_minus_WL_wf decomp inv_Comp_union wf_Comp_union l' wf_ins_b inv_ins_b
    by (metis Earley_Gw.WorkList.sel(1,2) assms(2))
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * f (length Bs) + 2 * L * Suc K + 4) + length Bs + 2 + L * (Suc K) * (Suc (length Bs))"
    using length_Comp_union mult_le_mono1
    using add_le_mono add_le_mono1 by presburger
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * f (length Bs) + 2 * L * Suc K + 5) + length Bs + 2"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"]
    by auto
  finally have 9: "?minus \<le> L * (Suc K) * (Suc (length Bs)) * (4 * f (length Bs) + 2 * L * Suc K + 5) + length Bs + 2".

  have "T_step_fun Bs (wl1, wl2) \<le> the (T_size (rhs (state.prod b))) + ?t_step +
  T_union_LWL ?step wl1 +
   T_insert wl2 b + T_minus_WL (union_LWL ?step wl1) (local.insert wl2 b) +
   T_insert wl2 b" by (auto simp add: Let_def WL1 bbs simp del: T_Complete_L.simps T_Predict_L.simps T_minus_WL.simps)

  also have "... \<le> Suc K + f (length Bs) + 2 * (K + 2) * L * (Suc K) * Suc (length Bs) + 2 + Suc (length Bs)
    + L * Suc K * Suc (length Bs) * (3 * f (length Bs) + L * Suc K + 2) + 1
    + 3 * f (length Bs) + L * Suc K + 1 + L * (Suc K) * (Suc (length Bs)) * (4 * f (length Bs) + 2 * L * Suc K + 5) + length Bs + 2 +
   3 * f (length Bs) + L * Suc K + 1" using t_step 6 7 8 9 by linarith

  also have "... \<le> Suc K + 2 * (K + 2) * L * (Suc K) * Suc (length Bs)
    + L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7)
    + 7 * f (length Bs) + 2* L * Suc K + 2 * Suc (length Bs) + 7"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  also have "... = Suc K + L * (Suc K) * Suc (length Bs) * 2 * (K + 2)
    + L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7)
    + 7 * f (length Bs) + 2* L * Suc K + 2 * Suc (length Bs) + 7"
    by (smt (verit) mult.assoc mult.commute)
  also have "... = L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  finally show ?thesis.
qed

lemma leng_WL_minus: "WL_inv wl1 \<Longrightarrow> leng (minus_WL wl1 wl2) = leng wl1"
proof-
  assume inv: "WL_inv wl1"
  obtain as l m where "wl1 = WorkList as l m"
    using wl_decomp by blast
  then show ?thesis using inv leng_minus_LWL by (auto simp add: minus_WL_def)
qed

lemma leng_step_fun1: "list wl1 \<noteq> [] \<Longrightarrow> wf_bins1 (map set Bs) \<Longrightarrow> wf1_WL wl1 (length Bs) \<Longrightarrow> WL_inv wl1 \<Longrightarrow> step_fun Bs (wl1, wl2) = (wl1', wl2') \<Longrightarrow> leng wl1 = length Bs \<Longrightarrow> leng wl1' = length Bs"
proof-
  assume assms: "list wl1 \<noteq> []" "step_fun Bs (wl1, wl2) = (wl1', wl2')" "leng wl1 = length Bs" "wf_bins1 (map set Bs)" "wf1_WL wl1 (length Bs)" " WL_inv wl1"
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

lemma leng_step_fun2: "list wl1 \<noteq> [] \<Longrightarrow> WL_inv wl1 \<Longrightarrow> step_fun Bs (wl1, wl2) = (wl1', wl2') \<Longrightarrow> leng wl1 = length Bs \<Longrightarrow> leng wl2 = length Bs \<Longrightarrow> leng wl2' = length Bs"
proof-
  assume assms: "list wl1 \<noteq> []" "WL_inv wl1" "step_fun Bs (wl1, wl2) = (wl1', wl2')" "leng wl1 = length Bs" "leng wl2 = length Bs"
  then obtain a as l m where "wl1 = WorkList (a#as) l m"
    by (metis Earley_Gw.WorkList.sel(1) T_last.cases wl_decomp)
  then show ?thesis using leng_WL_insert assms by auto
qed

lemma step_fun_dist: "list wl1 \<noteq> [] \<Longrightarrow> WL_inv wl2 \<Longrightarrow> step_fun Bs (wl1, wl2) = (wl1', wl2') \<Longrightarrow> set_WorkList wl1' \<inter> set_WorkList wl2' = {}"
proof-
  assume assms: "list wl1 \<noteq> []" "step_fun Bs (wl1, wl2) = (wl1', wl2')" "WL_inv wl2"
  then obtain a as l m bs k n where WL: "wl1 = WorkList (a#as) l m \<and> wl2 = WorkList bs k n"
    using wl_decomp
    by (metis Earley_Gw.WorkList.sel(1) neq_Nil_conv)
  let ?step = "if is_complete a then Complete_L Bs a else Predict_L a (length Bs)"
  have "wl1' = minus_WL (union_LWL ?step wl1) (insert wl2 a)" using assms WL by auto
  then have "set_WorkList wl1' \<inter> set_WorkList (insert wl2 a) = {}" 
    using assms WL_minus insert_WL_inv1 by auto
  then show ?thesis using assms WL by auto
qed

lemma length_step_fun2: "list wl1 \<noteq> [] \<Longrightarrow> WL_inv wl2 \<Longrightarrow> step_fun Bs (wl1, wl2) = (wl1', wl2') \<Longrightarrow> set_WorkList wl1 \<inter> set_WorkList wl2 = {} \<Longrightarrow> length (list wl2') = Suc (length (list wl2))"
proof-
  assume assms: "list wl1 \<noteq> []" "WL_inv wl2" "step_fun Bs (wl1, wl2) = (wl1', wl2')" "set_WorkList wl1 \<inter> set_WorkList wl2 = {}"
  then obtain a as l m where WL1: "wl1 = WorkList (a#as) l m"
    by (metis Earley_Gw.WorkList.sel(1) T_last.cases wl_decomp)
  obtain bs k n where WL2: "wl2 = WorkList bs k n"
    using wl_decomp by blast
  have "wl2' = insert wl2 a" using assms WL1 by auto
  then have "list wl2' = a#bs" using assms isin_WL1 by (auto simp add: upsize_list1 WL1 WL2 Let_def simp del: isin.simps)

  then show ?thesis by (simp add: WL2)
qed

lemma steps_time_time: assumes 
    dist_ps: "distinct ps" 
and wf_Bs:  "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" 
and wl1_assms:  "wf1_WL wl1 (length Bs)" "WL_inv wl1" "leng wl1 = length Bs"
and wl2_assms:  "wf1_WL wl2 (length Bs)" "WL_inv wl2" "leng wl2 = length Bs"
and dist_wls: "set_WorkList wl1 \<inter> set_WorkList wl2 = {}"
and step:  "steps_time Bs (wl1,wl2) k = Some ((wl1',wl2'), k')" "k \<le> (length (list wl2)) * (L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
  shows "k' \<le> (length (list wl2')) * (L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)" (*and "wf1_WL wl2' (length Bs)" and "WL_inv wl2'"*)
proof -
  let ?C = "L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
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
shows "T_steps Bs (wl1, wl2) \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
proof-
  obtain wl1' wl2' k' where P: "steps_time Bs (wl1,wl2) 0 = Some ((wl1',wl2'),k') \<and> steps Bs (wl1, wl2) = Some (wl1', wl2')"
    using steps_time_NF assms by blast
  have "wf1_WL wl2' (length Bs) \<and> WL_inv wl2'"
    using P assms(2,3,4,5,6) steps_wf2 steps_inv2 by blast
  then have 1: "length (list wl2') \<le> L * Suc K * Suc (length Bs)"
    using card_wf_bin1 distinct_card[of "list wl2'"] WL_inv1
    by fastforce
  have "k' \<le> (length (list wl2')) * (L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
    using steps_time_time[of Bs wl1 wl2 0] assms P by simp
  also have "... \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)"
    using P mult_le_mono1[OF 1] by auto
  finally show ?thesis using P by simp
qed

lemma T_close2_L_bound: 
assumes "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)"  "wf1_WL wl (length Bs)" "WL_inv wl" "leng wl = length Bs"
shows "T_close2_L Bs wl \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * f (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (length Bs) + 2 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K) + 2* Suc (length Bs)"
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

lemma distinct_close2: "wf_bins1 (map set Bs) \<Longrightarrow> wf1_WL wl (length Bs) \<Longrightarrow> WL_inv wl \<Longrightarrow> distinct (close2_L Bs wl)"
proof-
  assume "wf_bins1 (map set Bs)" "wf1_WL wl (length Bs)" "WL_inv wl"
  then obtain wl1 wl2 where "steps Bs (wl, WL_empty (length Bs)) = Some (wl1, wl2)"
    using empty_inv wf1_WL_empty Close2_L_NF by blast
  then show ?thesis using steps_inv2[of " WL_empty (length Bs)"] WL_inv1[of "wl2"] close2_L_def empty_inv by (auto simp add: close2_L_def)
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

lemma bound_help: "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> (x+2)^3 * (a+b) + 7*(x::nat) + (x+2)^2 * a + (x+2) * b + 16 \<le> (x+3)^3 * (a+b)"
proof-
  assume assms: "a > 0" " b > 0"
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
  \<le> (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K)))"
proof (induction k)
  case 0
  then have 1: "T_union_LWL Init_L (WL_empty 0) \<le> length Init_L * (3 * f (0) + L * Suc K + 2) + 1" 
    using T_union_LWL_wf[of "(WL_empty 0)" Init_L] empty_inv wf1_WL_empty wf1_Init_L wfbin1_impl_wfbin[of "set Init_L"] wf1_Init_L by auto
  have "leng (WL_of_List 0 Init_L) = 0" 
    using leng_WL_of_List wf1_Init_L by (auto simp add: wf_bin1_def wf_state1_def wf_state_def)
  then have "T_close2_L [] (WL_of_List 0 Init_L) \<le> (L * Suc K) * (L * Suc K * (7 * f (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (0) + 2* L * Suc K + 9 + Suc K) + 2"
    using 0 T_close2_L_bound[of "[]" "(WL_of_List 0 Init_L)"] wf1_Init_L wf1_WL_of_List
        WL_of_List_inv by (auto simp add: wf_bins1_def simp del: T_close2_L.simps)
  then have "T_bins_L 0 \<le> length Init_L * (3 * f (0) + L * Suc K + 2) + 1 + (L * Suc K) * (L * Suc K * (7 * f (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (0) + 2* L * Suc K + 9 + Suc K) + 2+2" 
    unfolding T_bins_L.simps T_WL_of_List.simps T_WL_empty.simps T_empty_list_map.simps 
    using 1 by (linarith)
  also have "... =  length Init_L * (3 * f (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * f (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (0) + 2* L * Suc K + 9 + Suc K) + 5" using length_Init_L by auto
  also have "... \<le> L * (3 * f (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * f (0) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (0) + 2* L * Suc K + 9 + Suc K) + 5"
    using length_Init_L
    using add_le_mono1 mult_le_cancel2 by presburger
  also have "... \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * f (0) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * f (0) + 3* L * Suc K + 9 + Suc K)))"
    by (auto simp add: add_mult_distrib add_mult_distrib2)
  finally have 2: "T_bins_L 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * f (0) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * f (0) + 3* L * Suc K + 9 + Suc K)))".

  have "7 * f (0) + 3* L * Suc K + 9 + 2 * (K + 2)
      \<le> 7 * f (1) + 3* L * Suc K + 9 + 2 * (K + 2)" using mono_f by (auto simp add: incseq_SucD)
  then have 3: "Suc L * Suc K * Suc L * Suc K * (7 * f (0) + 3* L * Suc K + 9 + 2 * (K + 2))
    \<le> Suc L * Suc K * Suc L * Suc K * (7 * f (1) + 3* L * Suc K + 9 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * f (0) + 3* L * Suc K + 9 + Suc K \<le> 2 * (K + 2) + 10 * f (1) + 3* L * Suc K + 9 + Suc K"
    using mono_f by (auto simp add: incseq_SucD)
  then have 4: "(Suc L * Suc K * (2 * (K + 2) + 10 * f (0) + 3* L * Suc K + 9 + Suc K)) \<le> (Suc L * Suc K * (2 * (K + 2) + 10 * f (1) + 3* L * Suc K + 9 + Suc K))"
    using mult_le_mono2 by blast

  have "T_bins_L 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * f (1) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * f (1) + 3* L * Suc K + 9 + Suc K)))"
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
  have "T_WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k) \<le> k+2 + length (Scan_L (last (bins_L k)) k) * (3 * f (Suc k) + L * Suc K + 2) + 1"
    using T_union_LWL_wf[of "(WL_empty (Suc k))"] empty_inv wf1_WL_empty wf_Scan Suc wfbin1_impl_wfbin
    by (auto simp add: length_bins_L)
  also have "... \<le> k+2 + L * Suc K * Suc k * (3 * f (Suc k) + L * Suc K + 2) + 1" using length_Scan mult_le_mono1[OF length_Scan]
    using add_le_mono1 nat_add_left_cancel_le by presburger
  finally have 4: "T_WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k) \<le> L * Suc K * Suc k * (3 * f (Suc k) + L * Suc K + 2) + k + 3" by linarith

  have wf_bins_L: "wf_bins1 (map set (bins_L k))" using wf_bins1_bins bins_L_eq_bins Suc by auto
  have wf_WL_of_List: "wf1_WL (WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k))  (Suc k)"
    using set_WL_of_List wf_Scan wfbin1_impl_wfbin
    using Suc.prems(2) wf1_Scan_L wf_last by auto
  have leng_WL_of_List: "leng (WL_of_List (length (bins_L k)) (Scan_L (last (bins_L k)) k)) = (Suc k)"
    using wf_Scan leng_WL_of_List wf_bin1_def wf_state1_def wf_state_def length_bins_L
    by (metis le_imp_less_Suc)
  have 5: "T_close2_L (bins_L k) (WL_of_List  (length (bins_L k)) (Scan_L (last (bins_L k)) k))  
            \<le> (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) + 2* Suc (Suc k)"
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
        + L * Suc K * Suc k * (3 * f (Suc k) + L * Suc K + 2) + k + 3
        + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) + 2* Suc (Suc k)
      + k + 2 + 1" unfolding T_bins_L.simps Let_def using 1 2 3 4 5 6 by linarith

  
  
  also have "... = T_bins_L k + 7*k + 16 + L * Suc K * Suc k * 2 * (K + 2)
            + L * Suc K * Suc k * (3 * f (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    by auto

  also have "... = T_bins_L k + 7*k + 16
            + L * Suc K * Suc k * (2 * (K + 2) + 3 * f (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2 by auto

  also have "... = T_bins_L k + 7*k + 16 + L * Suc K * Suc k * (2 * (K + 2) + 3 * f (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))" "L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))"
                                "7 * f (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K"]
    by (smt (verit, del_insts) Suc_1 ab_semigroup_add_class.add_ac(1) ab_semigroup_mult_class.mult_ac(1) add_2_eq_Suc' add_Suc_shift add_mult_distrib2 group_cancel.add2
        mult.commute mult.left_commute)

  also have "... = T_bins_L k + 7*k + 16 + L * Suc K * Suc k * (2 * (K + 2) + 3 * f (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * 2 * Suc (Suc k)
    + L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] by auto

  also have "... \<le>  T_bins_L k + 7*k + 16 + L * Suc K * (Suc (Suc k)) * (2 * (K + 2) + 3 * f (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * 2
    + L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using mult_mono_mix[of "Suc k" "(Suc (Suc k))" "L * Suc K" "2 * (K + 2) + 3 * f (Suc k) + L * Suc K + 2"] test' by presburger

  also have "... \<le> T_bins_L k + 7*k + 16 
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] 
          add_mult_distrib2[of "L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k)"] by auto

  also have "... = T_bins_L k + 7*k + 16 
    + L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (metis (no_types, opaque_lifting) mult.assoc)

  also have "... \<le> T_bins_L k + 7*k + 16 
    + Suc L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + Suc L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K))" 
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_L k + 7*k + 16 
    + L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K)"
    by (metis (no_types, lifting) dual_order.refl mult.commute mult.left_commute mult.assoc)
  also have "... \<le> T_bins_L k + 7*k + 16 
    + Suc L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K)"
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_L k + 7*k + 16 
    + Suc (Suc k) * Suc (Suc k) * (Suc L * Suc K * Suc L * Suc K * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (smt (verit, ccfv_threshold) mult.commute mult.left_commute verit_comp_simplify1(2))
  also have "... \<le> T_bins_L k + 7*k + 16 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (metis add_2_eq_Suc' le_refl power2_eq_square)
  finally have short: "T_bins_L (Suc k) \<le> T_bins_L k + 7*k + 16 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K))".

  let ?a = "Suc L * Suc K * Suc L * Suc K * (7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2))"
  let ?b = "Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K)"

  have ff: "f(Suc k) \<le> f (Suc (Suc k))" using mono_f
    by (simp add: incseq_SucD)
  then have "(7 * f (Suc k) + 3* L * Suc K + 9 + 2 * (K + 2)) \<le> (7 * f (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))"
    by auto
  then have a1: "?a \<le> Suc L * Suc K * Suc L * Suc K * (7 * f (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * f (Suc k) + 3* L * Suc K + 9 + Suc K \<le> 2 * (K + 2) + 10 * f (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K"
    using ff by auto
  then have b1: "?b \<le> Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)"
    using mult_le_mono2 by blast

  have "T_bins_L (Suc k) \<le> (k+2)^3 * ((?a) + (?b))
    + 7*k + 16 
    + (k+2)^2 * ?a
    + Suc (Suc k) * ?b" using short Suc by simp

  also have "... \<le> (k+3)^3 * ((?a) + (?b))"
    using bound_help[of ?a ?b k] by simp

  also have "... \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * f (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)))"
    using a1 b1 by simp
  finally have "T_bins_L (Suc k)
  \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * f (Suc (Suc k)) + 3* L * Suc K + 9 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * f (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)))".

  (*  (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * f (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * f (Suc k) + 2 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) *)

  then show ?case
    by (metis add_Suc_shift eval_nat_numeral(3))
qed


end

context Earley_Gw
begin

fun recognized_L :: "('n, 'a) state list \<Rightarrow> bool" where
"recognized_L [] = False" |
"recognized_L (a#as) = (is_final a \<or> recognized_L as)"

definition earley where
"earley = recognized_L (last (bins_L (length w)))"

lemma recognized_set: "recognized_L as = (\<exists>x \<in> set as. is_final x)"
  by (induction as) auto

end

context Earley_Gw_eps
begin

lemma earley_eq_recognized_Earley: "earley \<longleftrightarrow> recognized Earley"
proof
  assume "earley"
  then have "\<exists>x \<in> set (last (bins_L (length w))). is_final x" using recognized_set earley_def by blast
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
  then show "earley" using recognized_set earley_def by blast
qed

theorem correctness_earley:
  shows "earley \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using correctness_Earley earley_eq_recognized_Earley by blast 
end


context Earley_Gw_eps
begin


lemma distinct_steps: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct ps" "distinct (B@C)" "steps Bs (B,C) = Some (B',C')" "distinct C" shows "distinct (B'@C')"
proof -
  let ?P = "\<lambda>(B',C'). distinct (B'@C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs) \<and> (\<forall>i < length Bs. distinct (Bs ! i)) \<and> distinct ps" 
  show ?thesis using while_option_rule[where P="?P"] assms[unfolded steps_def] step_fun_sound step_fun_wf distinct_step_fun
    by (smt (verit, ccfv_SIG) case_prodE case_prodI2 empty_set old.prod.case rtranclp.simps
        while_option_stop)
qed


lemma distinct_close2: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct ps" "distinct B" shows "distinct (close2_L Bs B)"
proof-
  have "wf_bin1 (set []) (length Bs)" by (simp add: wf_bin1_def)
  then obtain C' where c': "steps Bs (B, []) = Some ([], C')" using Close2_L_NF assms by blast
  have "distinct []" by simp
  then have "distinct C'" using distinct_steps assms c'
    by (metis Int_empty_right distinct_append empty_set)
  then show ?thesis using close2_L_def c' by auto
qed

lemma distinct_bins_L: "k \<le> length w \<Longrightarrow> distinct ps \<Longrightarrow> i < length (bins_L k) \<Longrightarrow> distinct (bins_L k ! i)"
proof(induction k arbitrary: i)
  case 0
  then have "i = 0"
    by simp
  then show ?case using distinct_Init distinct_close2
    by (simp add: "0.prems"(1,2) Init_L_eq_Init wf_bin1_Init wf_bins1_def)
next
  case (Suc k)
  then have 1: "i < Suc k \<longrightarrow> distinct (bins_L (Suc k) ! i)" using length_bins_L by (auto simp add: Let_def nth_append_left)

  have 2: "wf_bins1 (map set (bins_L k))" using "Suc.prems"(1)
    by (simp add: bins_L_eq_bins wf_bins1_bins)
  have "wf_bin1 (set (last (bins_L k))) k" using "Suc.prems"(1)
    by (metis Suc_leD Zero_not_Suc bins_L_eq_bins last_map length_bins_L list.size(3) wf_bin1_last)
  then have 3: "wf_bin1 (set (Scan_L (last (bins_L k)) k)) (Suc k)"
    using Scan_L_eq_Scan Suc.prems(1) wf_bin1_Scan by auto
  have "bins_L k \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_bins_L)
  then have "distinct (last (bins_L k))" using last_conv_nth length_bins_L Suc by (auto simp add: last_conv_nth)
  then have 4: "distinct (Scan_L (last (bins_L k)) k)" using distinct_Scan_L by simp
  have 5: "distinct (close2_L (bins_L k) (Scan_L (last (bins_L k)) k))" using 2 3 4 Suc distinct_close2
    by (simp add: length_bins_L)

  have "\<not> i < Suc k \<longrightarrow> i = Suc k" using Suc
    by (metis le_Suc_eq length_bins_L less_Suc_eq_le)
  then show ?case using 1 5 using nth_append_length[of "bins_L k"] length_bins_L by (auto simp add: Let_def)
qed




lemma T_close2_L_bound: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "distinct ps" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct B"
  shows "T_close2_L Bs B \<le> 3*(L * L * (Suc K) * (Suc K) * (Suc (length Bs)) * (Suc (length Bs)))"
proof-
  have "\<exists>C' k'. steps_time Bs (B,[]) 0 = Some (([],C'),k')" using assms
    using steps_time_NF wf_bin1_def by auto
  then obtain C' k' where steps: "steps_time Bs (B,[]) 0 = Some (([],C'),k')" by blast
  then have wfC': "wf_bin1 (set C') (length Bs)" and k'le: "k' \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))" and C'_d: "distinct C'"
    using steps_time_time[of Bs B "[]" 0 "[]" C' k'] assms
    by (simp_all add: wf_bin1_def)
  then have "length C' \<le> L * (Suc K) * (Suc (length Bs))" 
    by (metis card_wf_bin1 distinct_card)
  then have "k' \<le> (L * (Suc K) * (Suc (length Bs))) * (3*(L * (Suc K) * (Suc (length Bs))))"
    by (meson k'le le_trans mult_le_mono1) 
  then have "k' \<le> 3*(L * L * (Suc K) * (Suc K) * (Suc (length Bs)) * (Suc (length Bs)))"
    by (metis (no_types, opaque_lifting) mult.commute mult.left_commute)
  then show ?thesis using steps by (simp add: T_close2_L_def)
qed


lemma T_bins_L_bound: "k \<le> length w \<Longrightarrow> distinct ps \<Longrightarrow> T_bins_L k \<le> 3*L * L * (Suc K) * (Suc K) * (Suc k) * (Suc k) * (Suc k) + L"
proof(induction k)
  case 0
  then have "wf_bin1 (set Init_L) 0"
    using Init_L_eq_Init wf_bin1_Init by auto
  then have "T_bins_L 0 \<le> 3*(L * L * (Suc K) * (Suc K)) + L" 
    using "0" T_close2_L_bound[of "[]" "Init_L"] T_Init_L_def distinct_Init 
    by (auto simp add: wf_bins1_def wf_bin1_def L_def)
  then show ?case
    by linarith
next
  case (Suc k)
  then have 0: "T_bins_L k \<le> 3*L * L * (Suc K) * (Suc K) * (Suc k) * (Suc k) * (Suc k) + L" by simp
  have "(Suc k) * (Suc k) * (Suc k) = (k * k * k + 3* k*k + 3*k+1)" by (auto simp add: add_mult_distrib)
  then have 1: "T_bins_L k \<le> 3*L * L * (Suc K) * (Suc K) * (k * k * k + 3* k*k + 3*k+1) + L" using 0
    by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1))

  have P1: "\<forall>i < length (bins_L k). distinct ((bins_L k) ! i)" using distinct_bins_L Suc
    using Suc_leD by blast
  have P2: "wf_bin1 (set (Scan_L (last (bins_L k)) k)) (length (bins_L k))"
    by (metis Scan_L_eq_Scan Suc.prems(1) Zero_not_Suc bins_L_eq_bins le_Suc_eq length_bins_L list.size(3) nat_less_le not_less_eq_eq set_last wf_bin1_Scan
        wf_bin1_last)
  have P3: "distinct (Scan_L (last (bins_L k)) k)"
    by (metis P1 all_nth_imp_all_set bot_nat_0.extremum_strict distinct_Scan_L last_in_set length_bins_L lessI list.size(3))
  have 2: "T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) \<le> 3*(L * L * (Suc K) * (Suc K) * (Suc (Suc k)) * (Suc (Suc k)))"
    using T_close2_L_bound[of "(bins_L k)" "(Scan_L (last (bins_L k)) k)"] P1 P2 P3
    using Suc.prems(1,2) bins_L_eq_bins length_bins_L wf_bins1_bins by fastforce
  have "(Suc (Suc k)) * (Suc (Suc k)) = (k*k + 4 *k + 4)" by (auto simp add: add_mult_distrib)
  then have 3: "T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) \<le> 3*L * L * (Suc K) * (Suc K) * (k*k + 4 *k + 4)" using 2
    by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1))

  have Q1: "wf_bin1 (set (last (bins_L k))) k"
    by (metis Suc.prems(1) Suc_leD Zero_not_Suc bins_L_eq_bins length_bins_L list.size(3) set_last wf_bin1_last)
  have "distinct (last (bins_L k))"
    by (metis P1 all_nth_imp_all_set bot_nat_0.extremum_strict last_in_set length_bins_L list.size(3) not_less_eq)
  then have "length (last (bins_L k)) \<le> L * (Suc K) * (Suc k)" using Q1
    by (metis card_wf_bin1 distinct_card)
  then have 4: "length (last (bins_L k)) \<le> 3* L *L * (Suc K) * (Suc K) * (Suc k)" 
  proof - (*TODO make easier*)
    have "\<forall>n na. (n::nat) \<le> na \<or> \<not> n * n \<le> na"
      using dual_order.trans le_square by blast
    then have "L \<le> 3 * L * L * Suc K" 
      by (metis (no_types) Suc_mult_le_cancel1 mult_le_mono mult_le_mono1 mult_numeral_1 mult_numeral_1_right numeral_le_iff semiring_norm(68))
    then show ?thesis
      by (meson \<open>length (last (bins_L k)) \<le> L * Suc K * Suc k\<close> dual_order.trans mult_le_mono1)
  qed

  have "T_bins_L k + (T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) + length (last (bins_L k))) 
        \<le> 3*L * L * (Suc K) * (Suc K) * (k*k*k + 4*k*k + 8*k+6) + L" 
    using 1 3 4 Rings.semiring_class.distrib_left[of "3*L * L * (Suc K) * (Suc K)"] by auto
  also have "... \<le> 3*L * L * (Suc K) * (Suc K) * (k * k * k + 6* k*k + 12*k+8) + L" by auto
  finally have 5: "T_bins_L k + (T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) + length (last (bins_L k))) 
        \<le> 3*L * L * (Suc K) * (Suc K) * (k * k * k + 6* k*k + 12*k+8) + L".

  have "(Suc (Suc k)) * (Suc (Suc k)) * (Suc (Suc k)) = (k * k * k + 6* k*k + 12*k+8)" by (auto simp add: add_mult_distrib)
  then have "3*L * L * (Suc K) * (Suc K) * (Suc (Suc k) * (Suc (Suc k)) * (Suc (Suc k))) 
    = 3*L * L * (Suc K) * (Suc K) * (k * k * k + 6* k*k + 12*k+8)"
    by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1))
  then show ?case using 5
    by (smt (z3) T_Scan_L.simps T_bins_L.simps(2) mult.commute mult.left_commute)
qed


(* time bounds mit generierten funktionen und mit locale für n-th laufzeit*)

(*korrektheit ohne Eindeutigkeits beweis aus Early.thy*)

(*literature for linear runtime grammars*)
end

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


value "bins_L 0"
value "bins_L 1"
value "bins_L 2"
value "bins_L 3"

unused_thms
end

(*unused*)
context Earley_Gw_eps
begin
lemma "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> set (close2_L Bs B) \<subseteq> close2 (map set Bs)  (set B)"
proof -
  assume wf: "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)"
  have 1: "wf_bin1 (set []) k" for k by (auto simp add: wf_bin1_def)
  from wf 1 obtain C' where C': "steps Bs (B,[]) = Some ([],C')" using Close2_L_NF by blast
  then have "(step_rel (map set Bs))^** (set B, {}) ({}, set (close2_L Bs B))" 
    using wf Close2_NF steps_sound1 by (auto simp add: close2_L_def)
  then show ?thesis
    by (simp add: Close2_steps_subset_Close1' close2_eq_Close1 local.wf(1,2) step_rel_def)
qed


lemma Close2_step_subset_Close1_2: "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> B' \<union> C' \<subseteq> C \<union> Close1 Bs B"
proof(induction rule: Close2_induct)
  case (Predict x B C)
  then show ?case using Close1_incr Close1.Predict by blast
next
  case (Complete x B C)
  have *: "B \<subseteq> Close1 Bs B" using Close1_incr by blast
  have 1: "x \<in> Close1 Bs B" using Complete Close1_incr by blast
  then have "Complete Bs x \<subseteq> Close1 Bs B"
    using Complete Close1.Complete * unfolding Complete_def next_symbol_def by (auto split: if_splits)
  then show ?case using * 1 by fastforce
qed


lemma Close2_step_snd_subset: "Bs \<turnstile> (B,C) \<rightarrow> (D,E) \<Longrightarrow> C \<subseteq> E"
by (induction rule: Close2_induct) auto


lemma Close2_steps_snd_subset: "Bs \<turnstile> (B,C) \<rightarrow>* (D,E) \<Longrightarrow> C \<subseteq> E"
proof(induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step B' C' B'' C'')
  then show ?case using Close2_step_snd_subset by fastforce
qed

lemma Close2_disj: "Bs \<turnstile> (B, C) \<rightarrow> (D, E) \<Longrightarrow> D \<inter> E = {}"
  by (induction rule: Close2_induct) auto

lemma Close2_steps_subset_Close1'_2: "Bs \<turnstile> (B,C) \<rightarrow>* (D,E) \<Longrightarrow> B \<inter> C = {} \<Longrightarrow> D \<union> E \<subseteq> C \<union> Close1 Bs B"
proof(induction rule: rtranclp_induct2)
  case refl
  thus ?case
    using Close1_incr by blast
next
  case (step B' C' B'' C'')
  have 1: "B' \<subseteq> B'' \<union> C''" using step Close2_step_incr by auto
  have "B'' \<union> C'' \<subseteq> C' \<union> Close1 Bs B'"
    using Close2_step_subset_Close1_2[OF step.hyps(2)] by simp
  then have *: "B'' \<union> C'' \<subseteq> B' \<union> C' \<union> Close1 Bs B'" using 1 by auto
  have 2: "C \<subseteq> C'" using Close2_steps_snd_subset step by auto
  have 3: "B' \<inter> C' = {}" using step
    by (simp add: Close2_steps_disj)
  then have "B' \<subseteq> Close1 Bs B" using step 2 by fastforce
  then have "Close1 Bs B' \<subseteq> Close1 Bs B"
    using Close1_idemp1 Close1_mono1 by blast
  then show ?case
    using * step by fastforce
qed

lemma 1: "Bs \<turnstile> (B, C) \<rightarrow> (D, E) \<Longrightarrow> Bs \<turnstile> (B, C \<union> F) \<rightarrow> (D - F, E \<union> F)"
proof-
  assume assm: "Bs \<turnstile> (B, C) \<rightarrow> (D, E)"
  then show ?thesis
  proof (cases rule: Close2.cases)
    case (Predict x)
    have "B \<union> Predict x (length Bs) - ((C \<union> F) \<union> {x}) = B \<union> Predict x (length Bs) - (C \<union> {x}) - F" by auto
    then show ?thesis using Predict Close2.Predict[of x B Bs "C \<union> F"]
      by simp
  next
    case (Complete x)
    have "B \<union> Complete Bs x - ((C \<union> F) \<union> {x}) = B \<union> Complete Bs x - (C \<union> {x}) - F" by auto
    then show ?thesis using Complete Close2.Complete[of x B Bs "C \<union> F"] by simp
  qed
qed



lemma Close1_elem_union: "x \<in> Close1 Bs (B \<union> C) \<Longrightarrow> x \<in> Close1 Bs B \<union> Close1 Bs C"
proof (induction rule: Close1.induct)
  case (Init x)
  then show ?case
    using Close1.Init by blast 
next
  case (Predict x x')
  then show ?case
    using Close1.Predict by blast 
next
  case (Complete y x)
  then show ?case
    using Close1.Complete by blast 
qed

lemma Close_of_empty: "Close1 Bs {} = {}"
proof-
  have "Bs \<turnstile> ({},{}) \<rightarrow>* ({},{})" by simp
  then have "Close1 Bs {} \<subseteq> {}" using Close1_subset_Close2 by auto
  then show "Close1 Bs {} = {}" by auto
qed

lemma Close2_steps_from_empty: "Bs \<turnstile> ({},C) \<rightarrow>* ({},C') \<Longrightarrow> C = C'"
proof-
  assume assm: "Bs \<turnstile> ({},C) \<rightarrow>* ({},C')"
  then have " C' \<subseteq> C \<union> Close1 Bs {}" using Close2_steps_subset_Close1'_2 by auto
  then have 1: "C' \<subseteq> C" using Close_of_empty by simp
  have 2: "C \<subseteq> C'" using assm
    using Close2_steps_snd_subset by auto
  then show ?thesis using 1 by auto
qed

(*lemma "((step_rel (map set Bs))^** ) (set B, set C) ({},set C') \<Longrightarrow> wf_bins1 (map set Bs) 
  \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> wf_bin1 (set C) (length Bs) \<Longrightarrow> (steps Bs (B, C)) = Some ([], D) 
  \<Longrightarrow> set D = set C'"
unfolding steps_def
using wf_step_fun_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C D rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "B = []"
    thus ?thesis using less Close2_steps_from_empty
      by (simp add: while_option_unfold[of _ _ "([],C)"] step_rel_def)
   next
    let ?steps = "while_option (\<lambda>(as,bs). as \<noteq> []) (step_fun Bs)"
    assume cons: "B \<noteq> []"
    then obtain B' C''
      where step: "(B',C'') = step_fun Bs (B,C)" and wf': "wf_bin1 (set B') (length Bs)" "wf_bin1 (set C'') (length Bs)"
      using step_fun_wf_states[OF less.prems(2,3,4)] by auto
    then have "((B',C''), (B, C)) \<in> step_fun_less (length Bs)"
      by (simp add: Earley_Gw.step_fun_less_step \<open>B \<noteq> []\<close> less.prems(2,3,4))
    have "steps Bs (B', C'') = Some ([], D)" using less cons while_option_unfold
      by (metis (mono_tags, lifting) Earley_Gw_eps.steps_def Earley_Gw_eps_axioms case_prodI local.step)
      (*using Close2_NF less.prems(2) wf'(1,2) by blast*)
    then have "((step_rel (map set Bs))^** ) (set B', set C'') ({},set C')"
      using less.prems(1) step steps_sound cons wf'
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf']
    show ?thesis
      by (simp add: \<open>(B', C'') = step_fun Bs (B, C)\<close> while_option_unfold)
  qed
qed*)
end (*Gw_eps*)



end