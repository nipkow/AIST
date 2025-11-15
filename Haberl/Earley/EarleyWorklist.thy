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
  "Scan_L Bs k = map mv_dot (filter (\<lambda> b. next_symbol b = Some (Tm (w0 ! k))) Bs)"
                                           
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

fun WL_inv :: "('c, 'd) WorkList \<Rightarrow> bool" where
"WL_inv (WorkList as l m) = (l = length m \<and> (\<forall>x \<in> set as. from x < l) \<and> (\<forall>x. x \<in> set as \<longleftrightarrow> x \<in> set (m ! (l - from x - 1))))"

definition WL_empty :: "('c, 'd) WorkList" where
"WL_empty = (WorkList [] 1 [[]])"

fun isin :: "('c, 'd) WorkList \<Rightarrow> ('c,'d) state \<Rightarrow> bool" where
"isin (WorkList as l m) x = (from x < l \<and> member (m ! (l - from x - 1)) x)"

fun set_WorkList :: "('c, 'd) WorkList \<Rightarrow> ('c,'d) state set" where
  "set_WorkList wl = set (list wl)"

fun upsize :: "('c, 'd) WorkList \<Rightarrow> nat \<Rightarrow> ('c, 'd) WorkList" where
"upsize wl 0 = wl" |
"upsize (WorkList as l m) (Suc k) = upsize (WorkList as (Suc l) ([]#m)) k"

fun insert :: "('c,'d) WorkList \<Rightarrow> ('c,'d) state \<Rightarrow> ('c,'d) WorkList" where
"insert (WorkList as l m) x = (if isin (WorkList as l m) x then WorkList as l m else
                               (let wl = (upsize (WorkList as l m) (Suc (from x) - l)) 
                                in WorkList (x # (list wl)) (leng wl) ((list_map wl)[(leng wl) - from x - 1 := x#(list_map wl ! ((leng wl) - from x - 1))]) ))"

(*fun remove_first :: "('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList" where
"remove_first (WorkList [] l m) = WorkList [] l m" |
"remove_first (WorkList (a#as) l m) = WorkList as l (m[l - from a - 1 := list_remove (m ! (l - from a - 1)) a])"*)

fun union_LWL :: "('c,'d) state list \<Rightarrow> ('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList" where
"union_LWL [] wl = wl" |
"union_LWL (a#as) wl = insert (union_LWL as wl) a"

definition union_WL :: "('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList" where
"union_WL wl1 wl2 = union_LWL (list wl1) wl2"

definition WL_of_List :: "('c,'d) state list \<Rightarrow> ('c,'d) WorkList" where
"WL_of_List as = union_LWL as WL_empty"

fun minus_LWL :: "('c,'d) state list \<Rightarrow> ('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList" where
"minus_LWL [] wl = WL_empty" |
"minus_LWL (a#as) wl = (if \<not>(isin wl a) then insert (minus_LWL as wl) a else minus_LWL as wl)"

definition minus_WL :: "('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList \<Rightarrow> ('c,'d) WorkList" where
"minus_WL wl1 wl2 = minus_LWL (list wl1) wl2"


lemma set_WL_empty: "set_WorkList WL_empty = {}" by (simp add: WL_empty_def)

lemma empty_inv: "WL_inv WL_empty" by (auto simp add: WL_empty_def)

lemma isin_WL: "WL_inv (WorkList as l m) \<Longrightarrow> (isin (WorkList as l m) x) = (x \<in> set_WorkList (WorkList as l m))" 
  by (auto simp add: member_elem)

lemma isin_WL1: "WL_inv wl \<Longrightarrow> (isin wl x) = (x \<in> set_WorkList wl)"
  by (metis WL_inv.cases isin_WL)

lemma WL_inv_upsize: "WL_inv (WorkList as l m) \<Longrightarrow> WL_inv (upsize (WorkList as l m) k)"
proof (induction k arbitrary: l m)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then have "\<forall>x. x \<in> set as \<longleftrightarrow> x \<in> set ( ([]#m) ! ((Suc l) - from x - 1))"
    by (metis (no_types, lifting) ext Earley_Gw.WL_inv.simps diff_Suc_1 diff_commute in_set_conv_nth list.size(3) not_less_zero nth_Cons' zero_less_diff)
  then have "WL_inv (WorkList as (Suc l) ([]#m))" using Suc by auto
  then show ?case using Suc.IH[of "Suc l" "[]#m"] by auto
qed

lemma upsize_length: "upsize (WorkList as l m) k = WorkList as' l' m' \<Longrightarrow> l' = k + l"
proof (induction k arbitrary: m m' l l')
  case 0
  then show ?case by auto
next
  case (Suc k)
  then have "upsize (WorkList as (Suc l) ([]#m)) k = WorkList as' l' m'" by simp
  then show ?case using Suc.IH[of "Suc l" "[]#m"] by auto
qed

lemma upsize_list: "list (upsize (WorkList as l m) k) = as"
  by (induction k arbitrary: l m) auto

lemma upsize_list1: "list (upsize wl k) = list wl"
  using upsize_list by (metis WL_inv.cases WorkList.sel(1))

lemma set_upsize: "set_WorkList (upsize (WorkList as l m) k) = set_WorkList (WorkList as l m)"
  by (induction k arbitrary: l m) auto

lemma set_upsize1: "set_WorkList (upsize wl k) = set_WorkList wl"
  using set_upsize by (metis WL_inv.cases)

lemma WL_insert: "WL_inv (WorkList as l m) \<Longrightarrow> set_WorkList (insert (WorkList as l m) x) = set_WorkList ((WorkList as l m)) \<union> {x}"
  using set_upsize[of _ _ _ "(Suc (from x) - l)"] by (auto simp add: Let_def isin_WL simp del: isin.simps)

lemma WL_insert1: "WL_inv wl \<Longrightarrow> set_WorkList (insert wl x) = set_WorkList wl \<union> {x}"
  using WL_insert by (metis WL_inv.cases)

lemma insert_WL_inv: "WL_inv (WorkList as l m) \<Longrightarrow> WL_inv (insert (WorkList as l m) x)"
proof -
  let ?wl = "(upsize (WorkList as l m) (Suc (from x) - l))"
  assume assm: "WL_inv (WorkList as l m)"
  then have "WL_inv ?wl" by (auto simp add: WL_inv_upsize)
  then obtain bs k n where P: "?wl = WorkList bs k n \<and> WL_inv (WorkList bs k n)"
    by (metis Earley_Gw.WorkList.exhaust)
  have 1: "from x < k" using P upsize_length
    by (metis less_diff_conv less_not_refl not_less_eq)
  have "\<forall>y. y \<in> set bs \<union> {x} \<longleftrightarrow> y \<in> set ((n[k - from x - 1 := x#(n ! (k - from x - 1))]) ! (k - from y - 1))"
  proof
    fix y
    from 1 show "y \<in> set bs \<union> {x} \<longleftrightarrow> y \<in> set ((n[k - from x - 1 := x#(n ! (k - from x - 1))]) ! (k - from y - 1))"
    proof (cases "from x = from y")
      case True
      then show ?thesis using P 1 by auto
    next
      case False
      then have "y \<in> set (n[length n - Suc (from x) := x # n ! (length n - Suc (from x))] ! (length n - Suc (from y))) \<longleftrightarrow> y \<in> set (n ! (length n - Suc (from y)))"
        by (metis diff_less length_greater_0_conv list.set_intros(2) list_update_nonempty nth_list_update_eq nth_list_update_neq set_ConsD zero_less_Suc)
      then show ?thesis using P 1 by auto
    qed  
  qed
  
  then show ?thesis using P 1 by (auto simp add: Let_def)
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

lemma set_WL_of_List: "set_WorkList (WL_of_List as) = set as"
  using LWL_union empty_inv
  by (metis WL_of_List_def set_WL_empty sup_bot_right)

lemma WL_of_List_inv: "WL_inv (WL_of_List as)"
  using LWL_union_inv empty_inv by (auto simp add: WL_of_List_def)

lemma LWL_minus_inv: "WL_inv (minus_LWL as wl)"
  using insert_WL_inv1 empty_inv by (induction as) (auto simp add:)

lemma LWL_minus: "WL_inv wl \<Longrightarrow> set_WorkList (minus_LWL as wl) = set as - set_WorkList wl"
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
    then have "set_WorkList (minus_LWL (a # as) wl) = set_WorkList (insert (minus_LWL as wl) a)" by simp
    also have "... = set_WorkList (minus_LWL as wl) \<union> {a}" using WL_insert1 Cons LWL_minus_inv by blast
    then show ?thesis using Cons isin_WL1 by auto
  qed
qed

lemma WL_minus_inv: "WL_inv (minus_WL wl1 wl2)"
  using LWL_minus_inv by (auto simp add: minus_WL_def)

lemma WL_minus: "WL_inv wl2 \<Longrightarrow> set_WorkList (minus_WL wl1 wl2) = set_WorkList wl1 - set_WorkList wl2"
  using LWL_minus by (auto simp add: minus_WL_def)

abbreviation wf_WL :: "('n, 'a) WorkList \<Rightarrow> nat \<Rightarrow> bool" where
"wf_WL wl k \<equiv> wf_bin1 (set (list wl)) k"


fun step_fun :: "('n, 'a) state list list \<Rightarrow>  ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList" where
  "step_fun Bs ((WorkList [] l m), C) = undefined" |
  "step_fun Bs ((WorkList (b#bs) l m), C) = (let step = (if is_complete b then Complete_L Bs b else Predict_L b (length Bs)) in
    ( minus_WL (union_LWL step (WorkList (b#bs) l m)) (insert C b), insert C b) )"
(* (bs \<union> step) - (C \<union> {b}) *)

definition steps :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> (('n, 'a) WorkList \<times> ('n, 'a) WorkList) option" where
  "steps Bs BC = while_option (\<lambda>(B,C). list B \<noteq> []) (step_fun Bs) BC"

definition close2_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<Rightarrow> ('n, 'a) state list" where
"close2_L Bs B = list (snd (the (steps Bs (B, WL_empty))))"

fun bins_L :: "nat \<Rightarrow> ('n,'a) state list list" where
"bins_L 0 = [close2_L [] (WL_of_List Init_L)]" |
"bins_L (Suc k) = (let Bs = bins_L k in Bs @ [close2_L Bs (WL_of_List (Scan_L (last Bs) k))])"

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

lemma step_fun_sound: "as \<noteq> [] \<Longrightarrow> wf_WL (WorkList as l1 m1) (length Bs) \<Longrightarrow> WL_inv (WorkList as l1 m1) \<Longrightarrow> WL_inv (WorkList bs l2 m2)
 \<Longrightarrow> step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))
 \<Longrightarrow> step_rel (map set Bs) (set as,set bs) (set as', set bs')"
proof-
  assume assms: "as \<noteq> []" 
    and wf: "wf_WL (WorkList as l1 m1) (length Bs)"
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
  and wf: "wf_bins1 (map set Bs)" "wf_WL (WorkList as l1 m1) (length Bs)"
  and inv: "WL_inv (WorkList as l1 m1)" "WL_inv (WorkList bs l2 m2)"
  and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"  
  shows "wf_WL (WorkList as' l3 m3) (length Bs)"
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
  and wf: "wf_WL (WorkList as l1 m1) (length Bs)" "wf_WL (WorkList bs l2 m2) (length Bs)"
  and inv: "WL_inv (WorkList bs l2 m2)"
  and sf: "step_fun Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
  shows "wf_WL (WorkList bs' l4 m4) (length Bs)"
proof-
  from \<open>as \<noteq> []\<close> obtain a ass where P: "as = a#ass" by (meson neq_Nil_conv)
  then have "set bs' = set bs \<union> {a}" using inv sf P WL_insert1[of "(WorkList bs l2 m2)" a] by auto
  then show ?thesis using assms P by (auto simp add: wf_bin1_def)
qed

(*"wf_WL (WorkList bs l2 m2) (length Bs)"*)
lemma steps_sound: 
  assumes wf: "wf_WL (WorkList as l1 m1) (length Bs)"  "wf_bins1 (map set Bs)"
  and inv: "WL_inv (WorkList as l1 m1)" "WL_inv (WorkList bs l2 m2)"
  and step: "steps Bs ((WorkList as l1 m1),(WorkList bs l2 m2)) = Some ((WorkList as' l3 m3), (WorkList bs' l4 m4))"
  shows "((step_rel (map set Bs))^**) (set as, set bs) ({},set bs')"
proof -
  let ?P1 = "\<lambda>(wl1,wl2). WL_inv wl1 \<and> WL_inv wl2"
  let ?P2 = "\<lambda>(wl1,wl2). ((step_rel (map set Bs))^**) (set as, set bs) (set (list wl1),set (list wl2)) \<and> wf_WL wl1 (length Bs) \<and> wf_bins1 (map set Bs)"
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
  assumes wf: "wf_WL (WorkList as l1 m1) (length Bs)"  "wf_bins1 (map set Bs)"
  and inv: "WL_inv (WorkList as l1 m1)"
  and step: "steps Bs ((WorkList as l1 m1),WL_empty) = Some (B',C)" 
shows "((step_rel (map set Bs))^**) (set as,{}) ({},set (list C))"
proof-
  have 1: "WL_inv WL_empty"
    by (simp add: empty_inv)
  have 2: "wf_WL WL_empty (length Bs)" by (simp add: WL_empty_def wf_bin1_def)
  show ?thesis using steps_sound 1 2 assms
    by (metis (no_types, lifting) WorkList.exhaust set_WorkList.elims set_WL_empty upsize_list upsize_list1)
qed
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
  and wf: "wf_bins1 (map set Bs)" "wf_WL wl1 (length Bs)" "wf_WL wl2 (length Bs)"
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
    by (metis Earley_Gw.set_WorkList.elims length_map)
qed

end (*Earley_Gw*)

context Earley_Gw_eps
begin


lemma step_fun_wf_states: "\<lbrakk>wf_bins1 (map set Bs); wf_WL wl1 (length Bs); wf_WL wl2 (length Bs); WL_inv wl1; WL_inv wl2; (list wl1) \<noteq> [] \<rbrakk>
 \<Longrightarrow> \<exists>B' C'. step_fun Bs (wl1,wl2) = (B',C') \<and> WL_inv B' \<and> WL_inv C' \<and> wf_WL B' (length Bs) \<and> wf_WL C' (length Bs)"
proof-
  assume assms: "wf_bins1 (map set Bs)" "wf_WL wl1 (length Bs)" "wf_WL wl2 (length Bs)" "WL_inv wl1" "WL_inv wl2" "(list wl1) \<noteq> []"
  obtain as l1 m1 bs l2 m2 where P1: "wl1 = (WorkList as l1 m1) \<and> wl2 = (WorkList bs l2 m2)"
    by (meson Earley_Gw.WL_inv.cases)
  obtain as' l1' m1' bs' l2' m2' where P: "step_fun Bs (wl1,wl2) = ((WorkList as' l1' m1'),(WorkList bs' l2' m2'))"
    by (metis Earley_Gw.WorkList.exhaust surj_pair)
  then have 1: "wf_WL (WorkList as' l1' m1') (length Bs) \<and> wf_WL (WorkList bs' l2' m2') (length Bs)"
    using step_fun_wf step_fun_wf2 assms P1
    by (metis Earley_Gw.WorkList.sel(1))
  have "WL_inv (WorkList as' l1' m1') \<and> WL_inv (WorkList bs' l2' m2')" using P P1
    using assms(5,6) step_fun_inv1 step_fun_inv2
    by (metis Earley_Gw.WorkList.sel(1))
  then show ?thesis using P 1 by auto
qed


theorem Close2_L_NF: "\<lbrakk>wf_bins1 (map set Bs); wf_WL wl1 (length Bs); wf_WL wl2 (length Bs); WL_inv wl1; WL_inv wl2\<rbrakk>
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
      where "(wl1',wl2') = step_fun Bs (wl1,wl2)" and wf': "wf_WL wl1' (length Bs)" "wf_WL wl2' (length Bs)" and inv': "WL_inv wl1'" "WL_inv wl2'"
      using step_fun_wf_states[OF less.prems] by fastforce
    then have "((wl1',wl2'), (wl1, wl2)) \<in> step_fun_less (length Bs)"
      by (simp add: Earley_Gw.step_fun_less_step \<open>list wl1 \<noteq> []\<close> less.prems)
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf' inv']
    show ?thesis
      by (simp add: \<open>(wl1',wl2') = step_fun Bs (wl1,wl2)\<close> while_option_unfold)
  qed
qed

lemma close2_L_eq_Close1: "wf_bins1 (map set Bs) \<Longrightarrow> wf_WL wl (length Bs) \<Longrightarrow> WL_inv wl \<Longrightarrow> set (close2_L Bs wl) = Close1 (map set Bs) (set (list wl))"
proof-
  assume assms: "wf_bins1 (map set Bs)" "wf_WL wl (length Bs)" "WL_inv wl"

  have "wf_WL WL_empty (length Bs) \<and> WL_inv WL_empty" by (auto simp add: wf_bin1_def WL_empty_def)
  then obtain wl1 wl2 where D1: "steps Bs (wl,WL_empty) = Some (wl1,wl2)" using assms Close2_L_NF
    by blast
  then have "(map set Bs) \<turnstile> (set (list wl), {}) \<rightarrow>* ({}, set (list wl2))" using steps_sound
    by (metis Earley_Gw.WorkList.exhaust assms(1,2,3) step_rel_def steps_sound1 upsize_list upsize_list1)
  then have DC1: "set (list wl2) = Close1 (map set Bs) (set (list wl))"
    by (simp add: Close1_subset_Close2 Close2_steps_subset_Close1' subset_antisym)
  have "set (list wl2) = set (close2_L Bs wl)" using D1 by (auto simp add: close2_L_def)
  then show ?thesis using DC1 by auto
qed

lemma close2_L_eq_close2: "wf_bins1 (map set Bs) \<Longrightarrow> wf_WL wl (length Bs) \<Longrightarrow> WL_inv wl \<Longrightarrow> set (close2_L Bs wl) = close2 (map set Bs) (set (list wl))"
  by (auto simp add: close2_L_eq_Close1 close2_eq_Close1)

lemma close2_L_eq_Close: "wf_bins1 (map set Bs) \<Longrightarrow> wf_WL wl (length Bs) \<Longrightarrow> WL_inv wl \<Longrightarrow> set (close2_L Bs wl) = Close (map set Bs) (set (list wl))"
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
  then have "wf_bins1 (map set []) \<and> wf_WL (WL_of_List Init_L) 0 \<and> WL_inv (WL_of_List Init_L)"
    by (metis set_WorkList.simps WL_of_List_inv set_WL_of_List)
  then have "set (close2_L [] (WL_of_List Init_L)) = Close [] Init"
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
  then have 2: "wf_WL (WL_of_List (Scan_L (last ?Bs) k)) (Suc k)"
    by (metis Scan_L_eq_Scan set_WorkList.elims wf_bin1_Scan kl set_WL_of_List)
  have 3: "WL_inv (WL_of_List (Scan_L (last ?Bs) k))"
    by (simp add: WL_of_List_inv)
  have "wf_bins1 (map set (bins_L k))"
    by (simp add: Suc.IH Suc.prems Suc_leD wf_bins1_bins)
  
  then have "set (close2_L ?Bs (WL_of_List (Scan_L (last ?Bs) k))) = Close (map set ?Bs) (Scan (last (map set ?Bs)) k)"
    using 2 3 by (auto simp add: close2_L_eq_Close[of _ "WL_of_List (Scan_L (last ?Bs) k)"] length_bins_L 1 set_WL_of_List simp flip: set_WorkList.simps)
  then show ?case using Suc by (auto simp add: Let_def)
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

lemma card_wf1: "\<forall>x \<in> bs. wf_state x i \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
proof-
  assume assm: "\<forall>x \<in> bs. wf_state x i"
  have "K = Max (length ` (rhs ` (set ps)))" using K_def
    by (metis Setcompr_eq_image image_image)
  then have "\<forall>p \<in> (length ` (rhs ` (set ps))). p \<le> K" using K_def by (auto)
  then have "\<forall>p \<in> set ps. length (rhs p) \<le> K" by simp
  then show ?thesis using card_wf assm L_def by simp
qed

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

time_fun snd
time_fun fst

fun T_rhs where
"T_rhs x = T_snd x"

(* Copy of the length time function but with options*)
fun T_size :: "'a list \<Rightarrow> nat option" where
"T_size [] = Some 1" |
"T_size (x21 # x22) = Some (the (T_size x22) + 1)"

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

lemma T_Scan_L_bound: "T_Scan_L Bs k = length Bs"
  sorry

lemma T_Predict_L_bound: "T_Predict_L x k = length ps"
  sorry

lemma T_Complete_L_bound: "T_Complete_L Bs y = length (Bs ! from y)"
  sorry

(*Copied from time_fun*)
definition T_Init_L where
"T_Init_L = T_filter T_fst ps + T_map (\<lambda>p. 0) (filter (\<lambda>p. lhs p = S) ps)"

lemma T_Init_L_bound: "T_init_L = length ps"
  sorry


lemma T_member_bound: "T_member as a \<le> length as"
  sorry


(*Coppied from time_fun*)
fun T_step_fun :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> nat" where
"T_step_fun Bs (WorkList [] l m, C) = undefined" |
"T_step_fun Bs (WorkList (b # bs) l m, C) =
    T_is_complete b + (if is_complete b then T_Complete_L Bs b else the (T_size Bs) + T_Predict_L b (length Bs)) +
    (let step = if is_complete b then Complete_L Bs b else Predict_L b (length Bs)
     in T_union_LWL step (WorkList (b # bs) l m) + (T_insert C b + T_minus_WL (union_LWL step (WorkList (b # bs) l m)) (local.insert C b)) + T_insert C b)"

(*assumes that the stop condition check takes 0 time*)
fun steps_time :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> nat \<Rightarrow> ((('n, 'a) WorkList \<times> ('n, 'a) WorkList) \<times> nat) option" where
"steps_time Bs wls y = while_option (\<lambda>((wl1,wl2),k). (list wl1) \<noteq> []) (\<lambda>((wl1,wl2),k). (step_fun Bs (wl1,wl2), k + T_step_fun Bs (wl1,wl2))) (wls, y)"

fun T_steps :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<times> ('n, 'a) WorkList \<Rightarrow> nat" where
"T_steps Bs wls = snd (the (steps_time Bs wls 0))"


time_fun "the"

(*coppied from time_fun*)
fun T_close2_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) WorkList \<Rightarrow> nat" where
"T_close2_L Bs B =
    T_steps Bs (B, WL_empty) + Earley_Gw.T_the (steps Bs (B, WL_empty)) + T_snd (the (steps Bs (B, WL_empty))) +
    T_list (snd (the (steps Bs (B, WL_empty))))"

(*coppied from time_fun*)
fun T_bins_L :: "nat \<Rightarrow> nat" where
"T_bins_L 0 = T_WL_of_List Init_L + T_close2_L [] (WL_of_List Init_L) + 1" |
"T_bins_L (Suc k) =
    T_bins_L k +
    (let Bs = bins_L k
     in T_last Bs + T_Scan_L (last Bs) k + T_WL_of_List (Scan_L (last Bs) k) + T_close2_L Bs (WL_of_List (Scan_L (last Bs) k)) +
        T_append Bs [close2_L Bs (WL_of_List (Scan_L (last Bs) k))]) + 1"

end (*Context Earley_Gw*)


context Earley_Gw_eps
begin

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

lemma distinct_List_union: "distinct Bs \<Longrightarrow> distinct (List.union As Bs)"
  by simp

lemma distinct_List_minus: "distinct As \<Longrightarrow> distinct (As -l Bs)"
  unfolding minus_L_def
  by(induction Bs) (auto simp add: distinct_removeAll)

lemma distinct_step_fun: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> \<forall>i < length Bs. distinct (Bs ! i) \<Longrightarrow> distinct ps \<Longrightarrow> distinct (B@C) \<Longrightarrow> B \<noteq> [] 
  \<Longrightarrow> (step_fun Bs (B, C)) = (D, E) \<Longrightarrow> distinct (D@E)"
proof-
  assume comp_assm: "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" 
    and assm: "distinct ps" "distinct (B@C)" "B \<noteq> []" and step: "(step_fun Bs (B, C)) = (D, E)"
  then obtain b bs where bbs: "B = b # bs"
    using list.exhaust by blast
  then have "b \<notin> set C" using assm by auto
  then have 1: "distinct E" using bbs assm step by auto

  have "is_complete b \<longrightarrow> from b < length Bs" using bbs comp_assm wf_bin1_def
    by (simp add: wf_state1_def)
  then have "is_complete b \<longrightarrow> distinct (Complete_L Bs b)" using comp_assm step distinct_Complete_L by auto
  then have 2: "distinct D" using assm step bbs distinct_Predict_L by (auto simp add: distinct_List_union distinct_List_minus)

  show ?thesis using 1 2 step bbs by auto
qed

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

lemma T_Complete_Bound: "distinct ps \<Longrightarrow> Bs = bins_L k \<Longrightarrow> from y < length Bs \<Longrightarrow> k \<le> length w \<Longrightarrow> T_Complete_L Bs y \<le> L * (Suc K) * (Suc (length Bs))"
proof-
  assume assms: "distinct ps" "Bs = bins_L k" "from y < length Bs" "k \<le> length w"
  then have 1: "set (Bs ! (from y)) = \<S> (from y)" using bins_L_eq_\<S>
    by (simp add: length_bins_L)
  have 2: "length (Bs ! from y) = card (set (Bs ! (from y)))" using distinct_bins_L assms by (auto simp flip: distinct_card)
  have "from y \<le> length w" using assms by (auto simp add: length_bins_L)
  then have "T_Complete_L Bs y \<le> L * (Suc K) * (Suc (from y))" using 1 2 card_Si assms by auto
  then show ?thesis using \<open>from y < length Bs\<close>
    by (meson Suc_le_mono le_trans less_or_eq_imp_le mult_le_mono2)
qed

(*helper*)
lemma length_union: "length (List.union as bs) \<le> length as + length bs"
proof(induction as arbitrary: bs)
  case Nil
  then show ?case by (auto simp add: List.union_def)
next
  case (Cons a as)
  then have "length (fold List.insert as bs) \<le> length as + length bs" by (auto simp add: List.union_def List.insert_def)
  then show ?case using Cons.IH[of "a#bs"] by (auto simp add: List.union_def List.insert_def)
qed

lemma T_step_fun_bound: assumes "B \<noteq> []" "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf_bin1 (set B) (length Bs)" "distinct B"
  shows "T_step_fun Bs (B, C) \<le> 3*(L * (Suc K) * (Suc (length Bs)))"
proof-
  obtain b bs where bbs: "B = b#bs" using assms
    using list.exhaust by blast
  have "length (b#bs) \<le> L * (Suc K) * (Suc (length Bs))" using card_wf_bin1[of "set (b#bs)"] assms by (auto simp add: distinct_card bbs)
  then have 5: "length bs \<le> L * (Suc K) * (Suc (length Bs))" by simp

  show ?thesis
  proof(cases "is_complete b")
    case True
    then have 1: "from b < length Bs" using assms
      by (simp add: bbs wf_bin1_def wf_state1_def)
  
    then have 2: "distinct (Bs ! from b)" using assms
      by simp
    have "wf_bin1 (set (Bs ! from b)) (from b)" using assms 1
      by (simp add: wf_bins1_def)
    then have 3: "length (Bs ! from b) \<le> L * (Suc K) * (Suc (from b))" 
      using card_wf1 2
      by (metis card_wf_bin1 distinct_card)
    then have 4: "length (Bs ! from b) \<le> L * (Suc K) * (Suc (length Bs))" using 1
      by (meson Suc_le_mono le_trans mult_le_mono2 nat_less_le)
  
    have x: "wf_bin1 (set (Complete_L Bs b)) (length Bs)"
      by (metis Earley_Gw_eps.wf1_Complete_L Earley_Gw_eps_axioms True assms(3,5) bbs list.set_intros(1) wf_bin1_def)
    then have 6: "length (Complete_L Bs b) \<le> L * (Suc K) * (Suc (length Bs))" 
      using card_wf_bin1[of "set (Complete_L Bs b)"] assms distinct_Complete_L 2 by (auto simp add: distinct_card)

    have "wf_bin1 (set (List.union bs (Complete_L Bs b))) (length Bs)" using assms bbs x by (auto simp add: wf_bin1_def)
    then have "length (List.union bs (Complete_L Bs b)) \<le> L * (Suc K) * (Suc (length Bs))"
      by (metis "2" card_wf_bin1 distinct_Complete_L distinct_List_union distinct_card)
    then have "length (Bs ! from b) + length (Complete_L Bs b) + length (List.union bs (Complete_L Bs b))
      \<le> 3*(L * (Suc K) * (Suc (length Bs)))" using 4 6 by linarith
    then show ?thesis using True by (auto simp add: Let_def bbs)
  next
    case False
    have "length (Predict_L b (length Bs)) \<le> L" by (auto simp add: L_def Predict_L_def)
    then have 1: "length (Predict_L b (length Bs)) \<le> L * (Suc K) * (Suc (length Bs))" by simp

    have "wf_bin1 (set (Predict_L b (length Bs))) (length Bs)"
      by (metis assms(5) bbs list.set_intros(1) wf1_Predict_L wf_bin1_def)
    then have "wf_bin1 (set (List.union bs (Predict_L b (length Bs)))) (length Bs)" using assms bbs by (auto simp add: wf_bin1_def)
    then have 2: "length (List.union bs (Predict_L b (length Bs))) \<le> L * (Suc K) * (Suc (length Bs))"
      by (metis assms(2) card_wf_bin1 distinct_List_union distinct_Predict_L distinct_card)
    have "length ps \<le> L * (Suc K) * (Suc (length Bs))" by (simp add: L_def)

    then have "length ps + length (Predict_L b (length Bs)) + length (List.union bs (Predict_L b (length Bs)))
       \<le> 3*(L * (Suc K) * (Suc (length Bs)))"
      using 1 2 by linarith
    then show ?thesis using False by (auto simp add: Let_def bbs)
  qed
qed

lemma length_step_fun2: "B \<noteq> [] \<Longrightarrow> (B', C') = step_fun Bs (B, C) \<Longrightarrow> length C' = Suc (length C)"
  using step_fun.elims[of Bs "(B, C)" "step_fun Bs (B, C)"] by fastforce

lemma steps_time_time: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "wf_bin1 (set C) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct ps" "distinct (B@C)" 
  "steps_time Bs (B,C) k = Some ((B',C'), k')" "k \<le> (length C) * (3*(L * (Suc K) * (Suc (length Bs))))" "distinct C" 
  shows "k' \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))" and "wf_bin1 (set C') (length Bs)" and "distinct C'"
proof -
  let ?P3 = "\<lambda>((B',C'),k). wf_bin1 (set B') (length Bs) \<and> wf_bin1 (set C') (length Bs) \<and> wf_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((B',C'),k). wf_bin1 (set B') (length Bs) \<and> wf_bin1 (set C') (length Bs) \<and> wf_bins1 (map set Bs) \<and> distinct (B'@C') \<and> (\<forall>i < length Bs. distinct (Bs ! i)) \<and> distinct ps"
  let ?P2 = "\<lambda>((B',C'),k). k \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((as,bs),k). as \<noteq> [])"
  let ?c = "(\<lambda>((as,bs),k). (step_fun Bs (as, bs), k + T_step_fun Bs (as, bs)))"

  have init: "?P ((B,C), k)" using assms by auto


  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y using distinct_step_fun step_fun_wf step_fun_wf2
    by (smt (verit, ccfv_threshold) case_prodI2' case_prod_conv)
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_step_fun Bs (a, b) \<le> 3*(L * (Suc K) * (Suc (length Bs)))" using T_step_fun_bound by auto
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "(a', b') = step_fun Bs (a,b)" by auto
    then have "length b' = Suc (length b)" using length_step_fun2 assms by auto
    then have 2: "length b' * 3*(L * (Suc K) * (Suc (length Bs))) = length b * 3*(L * (Suc K) * (Suc (length Bs))) + 3*(L * (Suc K) * (Suc (length Bs)))"
      by (simp add: add.commute add_mult_distrib)
    have "y' \<le> y + 3*(L * (Suc K) * (Suc (length Bs)))" using P1 1 by auto
    also have "... \<le> length b * 3*(L * (Suc K) * (Suc (length Bs))) + 3*(L * (Suc K) * (Suc (length Bs)))" 
      using assms by (auto simp add: add_mult_distrib2)
    also have "... = length b' * 3*(L * (Suc K) * (Suc (length Bs)))" using 2 by auto
    finally have "y' \<le> length b' * 3*(L * (Suc K) * (Suc (length Bs)))".
    then show "?P2 (?c ((a,b), y))" using P1
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
  qed

  then have t: "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P (?c ((a,b), y)))" for a b y using P1 by auto
  then show "k' \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] assms init by auto
  show "wf_bin1 (set C') (length Bs)"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto
  show "distinct C'"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto
qed

theorem steps_time_NF: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> wf_bin1 (set C) (length Bs) \<Longrightarrow> \<exists>C' k'. steps_time Bs (B,C) k = Some (([],C'),k')"
using wf_step_fun_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C k rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "B = []"
    thus ?thesis by(simp add: while_option_unfold[of _ _ "(([],C),k)"])
  next
    let ?steps = "while_option (\<lambda>(as,bs). as \<noteq> []) (step_fun Bs)"
    assume cons: "B \<noteq> []"
    then obtain B' C'
      where "(B',C') = step_fun Bs (B,C)" and wf': "wf_bin1 (set B') (length Bs)" "wf_bin1 (set C') (length Bs)"
      using step_fun_wf_states[OF less.prems] by auto
    then have "((B',C'), (B, C)) \<in> step_fun_less (length Bs)"
      by (simp add: Earley_Gw.step_fun_less_step \<open>B \<noteq> []\<close> less.prems(1,2,3))
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf']
    show ?thesis
      by (simp add: \<open>(B', C') = step_fun Bs (B, C)\<close> while_option_unfold)
  qed
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