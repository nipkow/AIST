section \<open>Earley's Parser\<close>

theory Earley_Parser
imports
  "Earley_Recognizer"
  "Context_Free_Grammar.Parse_Tree"
begin

(* TODO in devel; rm after next release *)
text \<open>Parse tree definitions\<close>
definition valid_parse_tree :: "('n, 't) Prods => 'n \<Rightarrow> ('n, 't) sym list \<Rightarrow> ('n,'t) tree \<Rightarrow> bool" where
"valid_parse_tree P A ss t = (parse_tree P t \<and> root t = Nt A \<and> fringe t = ss)"

definition unambiguous :: "('n, 't) Cfg \<Rightarrow> bool" where
"unambiguous g = (\<forall>w \<in> LangS g.
 \<forall> t1 t2. (valid_parse_tree (Prods g) (Start g) (map Tm w) t1 \<and>
           valid_parse_tree (Prods g) (Start g) (map Tm w) t2) \<longrightarrow> t1 = t2)"

text \<open>The parser produces a single parse tree only.
Essentially, it only works for unambiguous grammars.\<close>


subsection \<open>Set Based Earley Parser\<close>

type_synonym ('n, 't) item_P = "('n, 't) item \<times> ('n, 't) tree list"

context Earley_Gw
begin

abbreviation item :: "('n,'t) item_P \<Rightarrow> ('n, 't) item" where
  "item \<equiv> fst"

abbreviation trees :: "('n,'t) item_P \<Rightarrow> ('n, 't) tree list" where
  "trees \<equiv> snd"

fun wf_item_P :: "nat \<Rightarrow> ('n, 't) item_P \<Rightarrow> bool" where
"wf_item_P k x = (wf_item k (item x)
                  \<and> (\<forall>t \<in> set (trees x). parse_tree P t) 
                  \<and> fringes (rev (trees x)) = slice (from (item x)) k w 
                  \<and> map root (rev (trees x)) = \<alpha> (item x))"

fun wf_item_P1 :: "nat \<Rightarrow> ('n, 't) item_P \<Rightarrow> bool" where
"wf_item_P1 k x = (wf_item1 k (item x)
                    \<and> (\<forall>t \<in> set (trees x). parse_tree P t) 
                    \<and> fringes (rev (trees x)) = slice (from (item x)) k w 
                    \<and> map root (rev (trees x)) = \<alpha> (item x))"
  
fun wf_parse_bin :: "nat \<Rightarrow> ('n, 't) item_P set \<Rightarrow> bool" where
"wf_parse_bin k xs = (\<forall>x \<in> xs. wf_item_P k x)"

fun wf_parse_bin1 :: "nat \<Rightarrow> ('n, 't) item_P set \<Rightarrow> bool" where
"wf_parse_bin1 k xs = (\<forall>x \<in> xs. wf_item_P1 k x)"

definition wf_parse_bins1 :: "('n, 't) item_P set list \<Rightarrow> bool" where
"wf_parse_bins1 Bs = (\<forall>k < length Bs. wf_parse_bin1 k (Bs!k))"

definition Predict_P :: "nat \<Rightarrow> ('n,'t) item \<Rightarrow> ('n,'t) item_P set" where 
  "Predict_P k x = { (Item r 0 k, []) | r. r \<in> P \<and> next_sym x (Nt(lhs r)) }"

definition Complete_P :: "('n, 't) item_P set list \<Rightarrow> ('n, 't) item_P \<Rightarrow> ('n, 't) item_P set" where
  "Complete_P Bs y = (\<lambda> (p, t). (mv_dot p, (Rule (lhs(prod (item y))) (rev (trees y)))#t)) ` {x. x \<in> Bs ! from (item y) \<and> next_sym (fst x) (Nt(lhs(prod (item y))))}"

definition Init_P :: "('n,'t) item_P set" where
  "Init_P = { (Item r 0 0, []) | r. r \<in> P \<and> lhs r = (S) }"

definition Scan_P :: "nat \<Rightarrow> ('n,'t) item_P set \<Rightarrow> ('n,'t) item_P set" where
  "Scan_P k B = { (mv_dot (item x), (Sym (w!k))#(trees x)) | x. x \<in> B \<and> next_sym (item x) (w!k) }"

inductive_set Close_P :: "('n,'t) item_P set list \<Rightarrow> ('n,'t) item_P set \<Rightarrow> ('n,'t) item_P set" for Bs B where
    Init: "x \<in> B \<Longrightarrow> x \<in> Close_P Bs B"
  | Predict: "\<lbrakk> x \<in> Close_P Bs B; x' \<in> Predict_P (length Bs) (item x) \<rbrakk> \<Longrightarrow> x' \<in> Close_P Bs B"
  | Complete: "\<lbrakk> y \<in> Close_P Bs B; is_complete (item y); x \<in> Complete_P Bs y\<rbrakk> \<Longrightarrow> x \<in> Close_P Bs B"

fun bins_P :: "nat \<Rightarrow> ('n, 't) item_P set list" where
  "bins_P 0 = [(Close_P [] Init_P)]" |
  "bins_P (Suc k) = (let bs = bins_P k in bs @ [Close_P bs (Scan_P k (last bs))])"

definition get_parse_tree_set :: "('n, 't) tree option"  where
"get_parse_tree_set = (let ts = (SOME ts. \<exists>i. (i,ts) \<in> (last (bins_P (length w))) \<and> is_final i) 
  in if (\<exists> i t. (i,t) \<in> (last (bins_P (length w))) \<and> is_final i) then Some ( Rule S (rev ts)) else None)"

lemma Predict_P_item: "Predict_P x k = Predict x k \<times> {[]}"
  by (auto simp add: Predict_P_def Predict_def)

lemma Init_P_item: "Init_P = Init \<times> {[]}"
  by (auto simp add: Init_P_def Init_def)

lemma Scan_P_item: "item ` Scan_P k B = Scan k (item ` B)"
proof (auto simp add: Scan_P_def Scan_def)
  fix s t 
  assume "next_sym s (w ! k)" "(s, t) \<in> B"
  then show "\<exists>x. mv_dot s = mv_dot x \<and> x \<in> item ` B \<and> next_sym x (w ! k)"
    by (metis fst_conv image_eqI)
next
  fix s t
  assume "next_sym s (w ! k)" "(s, t) \<in> B"
  then show "mv_dot s \<in> item ` {(mv_dot a, Sym (w ! k) # b) |a b. (a, b) \<in> B \<and> next_sym a (w ! k)}"
    by force
qed

lemma wf_parse_init: "wf_parse_bin 0 (Init_P)"
  by (auto simp add: Init_P_def slice_drop_take wf_item_def \<alpha>_def)

lemma wf_Predict_P: "wf_item_P k x \<Longrightarrow> wf_parse_bin k (Predict_P k (item x))"
  by (auto simp add: Predict_P_def wf_item_def slice_drop_take \<alpha>_def)

lemma wf_parse_bins1_impl_bins1: "wf_parse_bins1 xs \<Longrightarrow> wf_bins1 (map ((`) item) xs)"
  by (auto simp add: wf_bins1_def wf_parse_bins1_def wf_bin1_def)

lemma \<alpha>_mv_dot: "next_sym x (Nt A) \<Longrightarrow> \<alpha> (mv_dot x) = \<alpha> x @ [Nt A]"
  by (auto simp add: \<alpha>_def mv_dot_def next_sym_def is_complete_def take_Suc_conv_app_nth split: if_splits)

lemma wf_parse_complete: 
  assumes "wf_parse_bins1 Bs" "wf_item_P1 (length Bs) st" "is_complete (item st)" 
  shows "wf_parse_bin1 (length Bs) (Complete_P Bs st)"
  unfolding wf_parse_bin1.simps proof
  fix x
  assume "x \<in> Complete_P Bs st"
  then obtain a b where P: "x = (mv_dot a, Rule (lhs (item.prod (item st))) (rev (trees st)) # b) 
    \<and> (a, b) \<in> Bs ! from (item st) \<and> next_sym a (Nt(lhs(prod(item st)))) \<and> from (item st) < length Bs"
    using assms by (auto simp add: Complete_P_def wf_item1_def wf_parse_bins1_def)
  then have wf_ab: "wf_item_P1 (from (item st)) (a,b)" using assms by (auto simp add: wf_parse_bins1_def simp del: wf_item_P1.simps)
  then have 1: "wf_item1 (length Bs) (item x) \<and> (\<forall>t \<in> set (trees x). parse_tree P t)"
    using assms P by (auto simp add: wf_parse_bins1_def mv_dot_def wf_item1_def is_complete_def wf_item_def rhs_def \<alpha>_def next_sym_def split: if_splits)
  have "fringes (rev (trees x)) = slice (from (item x)) (length Bs) w"
    using wf_ab assms(2) P
    by (auto simp add: wf_item1_def wf_item_def mv_dot_def slice_concat)
  then show "wf_item_P1 (length Bs) x" using assms P wf_ab 1 by (auto simp add: \<alpha>_mv_dot)
qed

lemma wf_parse_scan: 
  assumes "k < length w" "wf_parse_bin1 k as" shows "wf_parse_bin1 (Suc k) (Scan_P k as)"
  unfolding wf_parse_bin1.simps proof 
  fix x
  assume "x \<in> Scan_P k as"
  then obtain a b where P: "x = (mv_dot a, Sym (w ! k) # b) \<and> (a, b) \<in> as \<and> next_sym a (w ! k)"
    by (auto simp add: Scan_P_def)
  then have Broots: "map root (rev b) = \<alpha> a" and Bfringes: "fringes (rev b) = slice (from a) k w" and Btree: "\<forall>x \<in> set b. parse_tree P x"
    using assms(2) by auto
  from P have 1: "wf_item1 (Suc k) (mv_dot a)" using assms(1,2) 
    by (auto simp add: wf_item1_def next_sym_def mv_dot_def is_complete_def wf_item_def split: if_splits)
  have "from a \<le> k" using P assms(2) by (auto simp add: wf_item1_def wf_item_def)
  then have 2: "fringes (rev b @ [Sym (w ! k)]) = slice (from (mv_dot a)) (Suc k) w"
    using Bfringes assms(1) by (auto simp add: slice_drop_take take_Suc_conv_app_nth mv_dot_def)
  have 3: "map root (rev b @ [Sym (w ! k)]) = \<alpha> (mv_dot a)"
    using Broots P by (auto simp add: \<alpha>_def mv_dot_def next_sym_def is_complete_def take_Suc_conv_app_nth split: if_splits)
  then show "wf_item_P1 (Suc k) x" using P 1 2 3 Btree by auto
qed

end

subsubsection \<open>Correctness of set based Earley parser\<close>

context Earley_Gw_eps
begin

lemma wf_Predict_P1: "wf_item_P1 k x \<Longrightarrow> wf_parse_bin1 k (Predict_P k (item x))"
  using \<epsilon>_free by (auto simp add: Predict_P_def wf_item1_def wf_item_def is_complete_def slice_drop_take \<alpha>_def)

lemma wf_parse_init1: "wf_parse_bin1 0 (Init_P)"
  using \<epsilon>_free by (auto simp add: Init_P_def slice_drop_take wf_item1_def wf_item_def is_complete_def \<alpha>_def)

lemma wf_parse_bin_close: 
  assumes "wf_parse_bins1 Bs" "wf_parse_bin1 (length Bs) B" 
  shows "wf_parse_bin1 (length Bs) (Close_P Bs B)"
  unfolding wf_parse_bin1.simps proof
  fix x
  assume "x \<in> Close_P Bs B"
  then show "wf_item_P1 (length Bs) x" using assms
  proof (induction x rule: Close_P.induct)
    case (Init x)
    then show ?case by simp
  next
    case (Predict x x')
    then show ?case using wf_Predict_P1[of _ x] by auto
  next
    case (Complete y x)
    then show ?case using wf_parse_complete[of Bs y] by auto
  qed
qed

lemma PClose_incl_Close: "x \<in> Close_P Bs B \<Longrightarrow> wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 (length Bs) B \<Longrightarrow>  item x \<in> Close (map ((`) item) Bs) (item ` B)"
proof (induction x rule: Close_P.induct) 
  case (Init x)
  then show ?case by (auto simp add: Close.Init)
next
  case (Predict x x')
  then show ?case by (auto simp add: Close.Predict Predict_P_item)
next
  case (Complete y x)
  then have l_from: "from (item y) < length Bs" using wf_parse_bin_close[of Bs B] by (auto simp add: wf_item1_def)
  then obtain a b where P: "(a, b) \<in> Bs ! from (item y) \<and> next_sym a (Nt(lhs(prod(item y))))
    \<and> x = (mv_dot a, Rule (lhs (item.prod (item y))) (rev (trees y)) # b)" using Complete by (auto simp add: Complete_P_def)
  then have a_in: "a \<in> (map ((`) item) Bs) ! from (item y)" using l_from
    by (metis fst_conv imageI nth_map)
  then have 1: "mv_dot a \<in> Complete (map ((`) item) Bs) (item y)" using P by (auto simp add: Complete_def)
  have "(item y) \<in> Close (map ((`) item) Bs) (item ` B)" using Complete wf_parse_bin_close by blast
  then have "mv_dot a \<in> Close (map ((`) item) Bs) (item ` B)" using 1 Close.Complete Complete l_from P a_in
         by auto
  then show ?case using P 1 by (auto simp add: Close.Complete)
qed

lemma Close_incl_PClose: "x \<in> Close (map ((`) item) Bs) (item ` B) \<Longrightarrow> wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 (length Bs) B \<Longrightarrow> \<exists>b. (x, b) \<in> Close_P Bs B"
proof(induction x rule: Close.induct)
  case (Init x)
  then show ?case
    using Close_P.Init by fastforce
next
  case (Predict x x')
  then show ?case using Close_P.Predict Predict_P_item by fastforce
next
  case (Complete y x)
  then have l_from: "from y < length (map ((`) item) Bs)" using wf_parse_bin_close[of Bs B] by (auto simp add: wf_item1_def)
  then have 1: "mv_dot x \<in> Close (map ((`) item) Bs) (item ` B) \<and> (\<exists> xb. (x,xb) \<in> Bs ! (from y))" using Close.Complete Complete by auto
  then obtain xb where P_xb: "(x,xb) \<in> Bs ! (from y)" by blast
  obtain yb where P_yb: "(y, yb) \<in> Close_P Bs B" using Complete by auto
  then obtain xbb where "(mv_dot x,xbb) \<in> Complete_P Bs (y,yb)" using Complete 1 l_from P_xb by (fastforce simp add: Complete_P_def)
  then show ?case using Complete Close_P.Complete[of "(y, yb)" Bs B "(mv_dot x,xbb)"] P_yb by auto
qed

lemma PClose_eq_Close: "wf_parse_bins1 Bs \<Longrightarrow> wf_parse_bin1 (length Bs) B \<Longrightarrow> item ` (Close_P Bs B) = Close (map ((`) item) Bs) (item ` B)"
  using PClose_incl_Close Close_incl_PClose image_iff by fastforce

lemma length_parse_bins: "length (bins_P k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma parse_bins_wf1_nth: "k \<le> length w \<Longrightarrow> i \<le> k \<Longrightarrow> wf_parse_bin1 i (bins_P k ! i)"
proof (induction k arbitrary: i)
  case 0
  then show ?case using wf_parse_init1 wf_parse_bin_close[of "[]" Init_P] by (auto simp add: wf_parse_bins1_def)
next
  case (Suc k)
  then have wf_bins: "wf_parse_bins1 (bins_P k)" unfolding wf_parse_bins1_def by (simp add: length_parse_bins less_Suc_eq_le)
  from Suc have 1: "\<not> i \<le> k \<longrightarrow> i = Suc k" by auto
  from Suc have "wf_parse_bin1 k (last (bins_P k))" 
    using length_parse_bins[of k] last_conv_nth[of "bins_P k"] by fastforce
  then show ?case 
    using Suc wf_parse_scan[of k "last (bins_P k)"] wf_bins wf_parse_bin_close[of "bins_P k" "Scan_P k (last (bins_P k))"] 
      length_parse_bins[of k] 1 by (cases "i \<le> k") (auto simp add: Let_def nth_append_left nth_append_right)
qed

lemma parse_bins_wf1: "k \<le> length w \<Longrightarrow> wf_parse_bins1 (bins_P k)"
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

lemma item_bins_P_eq_bins_nth: "k \<le> length w \<Longrightarrow> i \<le> k \<Longrightarrow> item ` (bins_P k ! i) = bins k ! i"
proof (induction k arbitrary: i)
  case 0
  then show ?case using Init_P_item wf_parse_init1 PClose_eq_Close[of "[]" Init_P] 
    by (auto simp add: wf_parse_bins1_def)
next
  case (Suc k)
  then have map_bins: "map ((`) item) (bins_P k) = bins k" using all_f_nth_impl_map[of _ _ "(`) item"] by (auto simp add: length_parse_bins)
  from Suc have wf_last: "wf_parse_bin1 k (last (bins_P k))" using parse_bins_wf1[of k] wf_parse_bins1_def length_parse_bins last_conv_nth
    by (metis One_nat_def Suc_leD Zero_not_Suc diff_Suc_1' eq_imp_le list.size(3) parse_bins_wf1_nth)
  then have wf_scan: "wf_parse_bin1 (Suc k) (Scan_P k (last (bins_P k)))" using Suc wf_parse_scan by (auto simp del: wf_parse_bin1.simps)
  have item_last: "item ` last (bins_P k) = last (bins k)"
    by (metis Earley_Gw.bins_nonempty last_map list.map_disc_iff map_bins)
  from Suc have 1: "\<not> i \<le> k \<longrightarrow> i = Suc k" by auto
  then show ?case using Suc Scan_P_item PClose_eq_Close[of "bins_P k" "Scan_P k (last (bins_P k))"] 
      parse_bins_wf1[of k] wf_scan map_bins item_last
    by (cases "i \<le> k") (auto simp add: Let_def length_parse_bins nth_append_left nth_append_right simp del: wf_parse_bin1.simps)
qed

lemma item_bins_P_eq_bins: "k \<le> length w \<Longrightarrow> map ((`) item) (bins_P k) = bins k"
  using item_bins_P_eq_bins_nth all_f_nth_impl_map[of _ _ "(`) item"] 
  by (auto simp add: length_parse_bins)

lemma get_parse_tree_set_iff: "(\<exists>t. get_parse_tree_set = Some t) \<longleftrightarrow> (P \<turnstile> [Nt S] \<Rightarrow>* w)"
proof
  assume "\<exists>t. get_parse_tree_set = Some t"
  then obtain i t where "(i,t) \<in> (last (bins_P (length w))) \<and> is_final i"
    using get_parse_tree_set_def
    by fastforce
  then have "i \<in> last (map ((`) item) (bins_P (length w))) \<and> is_final i"
    by (metis (no_types, lifting) List.list.map_disc_iff bins_nonempty fst_conv image_eqI item_bins_P_eq_bins last_map nat_le_linear)
  then have "i \<in> last (bins (length w)) \<and> is_final i"
    using item_bins_P_eq_bins[of "length w"] by auto
  then have "i \<in> \<E> (length w) \<and> is_final i" using bins_eq_\<E> last_conv_nth length_bins
    by (metis Earley.Earley_Gw.bins_nonempty diff_add_inverse2 le_refl)
  then show "P \<turnstile> [Nt S] \<Rightarrow>* w"
    using accepted_def accpted_sound by auto
next
  assume "P \<turnstile> [Nt S] \<Rightarrow>* w"
  then obtain i where 1: "i \<in> \<E> (length w) \<and> is_final i"
    using accepted_def using Earley_complete by (auto simp add: accepted_def recognized_def \<E>_def)
  then have "i \<in> last (bins (length w)) \<and> is_final i"
    using bins_eq_\<E> last_conv_nth length_bins by (metis Earley.Earley_Gw.bins_nonempty diff_add_inverse2 le_refl)
  then have "i \<in> last (map ((`) item) (bins_P (length w))) \<and> is_final i"
    using item_bins_P_eq_bins[of "length w"] by auto
  then have "i \<in> item ` last (bins_P (length w))" using last_map length_parse_bins
    by (metis bins_nonempty item_bins_P_eq_bins list.simps(8)le_refl)
  then have "\<exists>t. (i,t) \<in> (last (bins_P (length w)))" by auto
  then obtain t where "(i,t) \<in> (last (bins_P (length w))) \<and> is_final i" using 1 by blast
  then show "\<exists>t. get_parse_tree_set = Some t"
    by (auto simp add: get_parse_tree_set_def)
qed

lemma last_final_PItem_impl_valid: "(s, ts) \<in> last (bins_P (length (w ))) \<and> is_final s \<Longrightarrow> valid_parse_tree P S w (Rule S (rev ts))"
proof-
  assume assm: "(s, ts) \<in> last (bins_P (length (w ))) \<and> is_final s"
  moreover have "bins_P (length w) \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_parse_bins)
  ultimately have "wf_item_P1 (length w) (s, ts)" using parse_bins_wf1 length_parse_bins
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_item_P1.simps)
  then show "valid_parse_tree P S w (Rule S (rev ts))" using assm 
    by (auto simp add: valid_parse_tree_def is_final_def wf_item1_def wf_item_def \<alpha>_def rhs_def is_complete_def)
qed

lemma get_parse_tree_set_valid: "get_parse_tree_set = Some t \<Longrightarrow> valid_parse_tree P S w t"
proof (cases "\<exists>i ts. (i, ts) \<in> last (bins_P (length (w ))) \<and> is_final i")
  case True
  assume "get_parse_tree_set = Some t"

  moreover have "valid_parse_tree P S w (Rule S (rev (SOME t. \<exists>i. (i, t) \<in> last (bins_P (length w)) \<and> is_final i)))"
    using True last_final_PItem_impl_valid last_final_PItem_impl_valid True
    by (metis (full_types,lifting) ext)
  ultimately show ?thesis by (auto simp add: get_parse_tree_set_def split: if_splits)
next
  case False
  assume assm: "get_parse_tree_set = Some t"
  have "get_parse_tree_set = None" using False by (auto simp add: get_parse_tree_set_def)
  then show ?thesis using assm by (auto simp add: get_parse_tree_set_def)
qed

(*would need other direction as well 
(\<exists> s t. (s, t) \<in> bins_P (length w) ! (length w) \<and> valid_parse_tree P w S (Rule (lhs (prod s)) (rev t))) \<Longrightarrow> accepted*)
end


subsection \<open>List Based Earley Parser\<close>

context Earley_Gw
begin

subsubsection \<open>ParseIL definition\<close>

type_synonym ('c, 'd) parseIL = "('c,'d) item_list \<times> ('c,'d) tree list list"
type_synonym ('c, 'd) parseIL2 = "('c, 'd) parseIL * ('c, 'd) parseIL"

fun inv_PIL :: "('n, 't) parseIL \<Rightarrow> bool" where
"inv_PIL (il, ts) = (inv_IL il \<and> length (list il) = length ts)"

definition empty_PIL :: "nat \<Rightarrow> ('n, 't) parseIL" where
"empty_PIL k = (empty_IL k, [] )"

fun list2_PIL :: "('n, 't) parseIL \<Rightarrow> ('n, 't) item_P list" where
"list2_PIL (il, ts) = (zip (list il) ts)"

fun isin_PIL :: "('n, 't) parseIL \<Rightarrow> ('n, 't) item_P \<Rightarrow> bool" where
"isin_PIL (il, ts) (s, t) = isin_IL il s"

fun set_PIL :: "('n, 't) parseIL \<Rightarrow> ('n, 't) item_P set" where
"set_PIL (il, ts) = set (zip (list il) ts)"

fun insert_PIL :: "('n, 't) item_P \<Rightarrow> ('n, 't) parseIL \<Rightarrow> ('n, 't) parseIL" where
"insert_PIL (s, t) (il, ts) = (if isin_IL il s then (il, ts) else (insert_IL s il, t#ts))"

fun union_LPIL :: "('n, 't) item_P list \<Rightarrow> ('n, 't) parseIL \<Rightarrow> ('n, 't) parseIL" where
"union_LPIL [] pil = pil" |
"union_LPIL (a#as) pil = insert_PIL a (union_LPIL as pil)"

definition union_PIL :: "('n, 't) parseIL \<Rightarrow> ('n, 't) parseIL \<Rightarrow> ('n, 't) parseIL" where
"union_PIL pil1 pil2 = union_LPIL (list2_PIL pil1) pil2"

definition PIL_list :: "nat \<Rightarrow> ('n, 't) item_P list \<Rightarrow> ('n, 't) parseIL" where
"PIL_list k as = union_LPIL as (empty_PIL k)"

fun minus_LPIL :: "nat \<Rightarrow> ('n, 't) item_P list \<Rightarrow> ('n, 't) parseIL \<Rightarrow> ('n, 't) parseIL" where
"minus_LPIL k [] pil = empty_PIL k" |
"minus_LPIL k (a#as) pil = (if \<not>(isin_PIL pil a) then insert_PIL a (minus_LPIL k as pil) else minus_LPIL k as pil)"

definition minus_PIL :: "('n, 't) parseIL \<Rightarrow> ('n, 't) parseIL \<Rightarrow> ('n, 't) parseIL" where
"minus_PIL pil1 pil2 = minus_LPIL (length (froms (fst pil1)) - 1) (list2_PIL pil1) pil2"

fun hd_PIL :: "('n,'t) parseIL \<Rightarrow> ('n,'t) item_P" where
"hd_PIL (il, t#ts) = (hd (list il), t)"

fun wf_PIL :: "nat \<Rightarrow> ('n,'t) parseIL \<Rightarrow> bool" where
"wf_PIL k pil = wf_parse_bin1 k (set_PIL pil)"

definition list_PIL :: "('n, 't) parseIL \<Rightarrow> ('n,'t) item list" where
"list_PIL pil = list (fst pil)"


subsubsection \<open>ParseIL lemmas\<close>

lemma list_empty_IL[simp]: "list (empty_IL k) = []"
  by (simp add: empty_IL_def)

lemma list_insert_IL[simp]: "isin_IL il x \<Longrightarrow> list (insert_IL x il) = list il"
  by (cases il) auto

lemma list_insert_IL1[simp]: "\<not> isin_IL il x \<Longrightarrow> list (insert_IL x il) = x # (list il)"
  by (cases il) (auto simp add: Let_def)

lemma hd_PIL_in_set_PIL: 
  assumes "pil = (il, ts)" "ts \<noteq> []" "inv_PIL pil" shows "hd_PIL pil \<in> set_PIL pil"
proof-
  obtain a as t tss where "list il = a#as \<and> ts = t#tss"
    using assms by (metis inv_PIL.simps length_0_conv neq_Nil_conv)
  then show ?thesis using assms by auto
qed

lemma PIL_inv_empty: "inv_PIL (empty_PIL k)"
  by (auto simp add: empty_PIL_def empty_inv)

lemma wf_empty_PIL: "wf_PIL n (empty_PIL k)"
  by (auto simp add: empty_PIL_def)

lemma length_empty_PIL[simp]: "length (froms (fst (empty_PIL k))) = Suc k" by (simp add: empty_PIL_def)

lemma PIL_inv_insert: "inv_PIL pil \<Longrightarrow> from (item x) < length (froms (fst pil)) \<Longrightarrow> inv_PIL (insert_PIL x pil)"
  by (cases pil, cases x) (auto simp add: inv_insert_IL1)

lemma wf_PIL_insert: "wf_PIL k pil \<Longrightarrow> wf_item_P1 k x \<Longrightarrow> wf_PIL k (insert_PIL x pil)"
  by(cases pil, cases x) auto

lemma length_insert_parse[simp]: "length (froms (fst (insert_PIL x pil))) = length (froms (fst pil))" 
  by (cases pil, cases x) auto

lemma length_union_LPIL[simp]: "length (froms (fst (union_LPIL xs pil))) = length (froms (fst pil))"
  by (induction xs) auto

lemma PIL_inv_union_LPIL: "inv_PIL pil \<Longrightarrow> \<forall>x \<in> set xs. from (item x) < length (froms (fst pil)) 
  \<Longrightarrow> inv_PIL (union_LPIL xs pil)"
  by (cases pil, induction xs) (auto simp add: PIL_inv_insert)

lemma wf_union_LPIL: "wf_PIL k pil \<Longrightarrow> wf_parse_bin1 k (set xs) \<Longrightarrow> wf_PIL k (union_LPIL xs pil)"
  by (induction xs) (auto simp add: wf_PIL_insert simp del: wf_PIL.simps)

lemma PIL_inv_union_PIL: "inv_PIL pil1 \<Longrightarrow> inv_PIL pil2 \<Longrightarrow> length (froms (fst pil2)) \<ge> length (froms (fst pil1)) 
  \<Longrightarrow> inv_PIL (union_PIL pil1 pil2)"
proof-
  assume assms: "inv_PIL pil1" "inv_PIL pil2" "length (froms (fst pil2)) \<ge> length (froms (fst pil1))"
  then obtain xs fs ts where PIL: "pil1 = (IL xs fs, ts)"
    by (metis il_decomp set_PIL.cases)
  then have "\<forall>x \<in> set xs. from x < length (froms (fst pil2))" using assms(1,3) by auto
  then have "\<forall>x \<in> set (zip xs ts). from (item x) < length (froms (fst pil2))" by (auto simp add: set_zip_leftD)
  then show ?thesis using PIL_inv_union_LPIL[of pil2 "zip xs ts"] assms(2) by (auto simp add: union_PIL_def PIL)
qed

lemma wf_union_PIL: "wf_PIL k pil1 \<Longrightarrow> wf_PIL k pil2 \<Longrightarrow> wf_PIL k (union_PIL pil1 pil2)"
  by (metis Earley_Gw.wf_PIL.elims(1) Earley_Gw.wf_union_LPIL list2_PIL.simps set_PIL.cases set_PIL.simps union_PIL_def)

lemma PIL_inv_PIL_list: "\<forall>x \<in> set xs. from (item x) < Suc k \<Longrightarrow> inv_PIL (PIL_list k xs)"
  using PIL_inv_empty PIL_inv_union_LPIL PIL_list_def by simp

lemma wf_PIL_list: "wf_parse_bin1 n (set xs) \<Longrightarrow> wf_PIL n (PIL_list k xs)"
  using PIL_list_def wf_empty_PIL wf_union_LPIL by presburger

lemma length_PIL_list[simp]: "length (froms (fst (PIL_list k xs))) = Suc k"
  by (auto simp add: PIL_list_def)

lemma length_minus_LPIL[simp]: "length (froms (fst (minus_LPIL k xs pil))) = Suc k" 
  by (induction xs) auto

lemma length_minus_PIL[simp]: "inv_PIL pil1 \<Longrightarrow> length (froms (fst pil1)) > 0 \<Longrightarrow> length (froms (fst (minus_PIL pil1 pil2))) = length(froms (fst pil1))" 
  by (cases pil1, cases "fst pil1") (auto simp add: minus_PIL_def)

lemma PIL_inv_minus_LPIL: "\<forall>x \<in> set xs. from (item x) < Suc k \<Longrightarrow> inv_PIL (minus_LPIL k xs pil)"
  by (induction xs) (auto simp add: PIL_inv_empty PIL_inv_insert)

lemma wf_minus_LPIL: "wf_parse_bin1 n (set xs) \<Longrightarrow> wf_PIL n (minus_LPIL k xs pil)"
  by (induction xs) (auto simp add: wf_empty_PIL wf_PIL_insert simp del: wf_PIL.simps)

lemma PIL_inv_minus_PIL: "inv_PIL pil1 \<Longrightarrow> length (froms (fst pil1)) > 0 \<Longrightarrow> inv_PIL (minus_PIL pil1 pil2)"
proof-
  assume assms: "inv_PIL pil1" "length (froms (fst pil1)) > 0"
  obtain xs fs ts where PIL: "pil1 = (IL xs fs, ts)"
    by (metis il_decomp set_PIL.cases)
  then have "\<forall>x \<in> set xs. from x < length (froms (fst pil1))" using assms by auto
  then have "\<forall>x \<in> set (zip xs ts). from (item x) < length (froms (fst pil1))" by (auto simp add: set_zip_leftD)
  moreover have "length fs > 0" using assms by (auto simp add: PIL)
  ultimately show ?thesis using PIL_inv_minus_LPIL by (auto simp add: minus_PIL_def PIL)
qed

lemma wf_minus_PIL: "wf_PIL k pil1 \<Longrightarrow> wf_PIL k (minus_PIL pil1 pil2)"
  by (metis list2_PIL.simps minus_PIL_def set_PIL.elims wf_PIL.elims(2) wf_minus_LPIL)

lemma list_PIL_Cons2: "inv_PIL pil \<Longrightarrow> list_PIL pil = a#as \<Longrightarrow> \<exists>x xs. snd pil = x#xs"
  using list_PIL_def
  by (metis inv_PIL.simps length_Suc_conv prod.collapse)

lemma list_PIL_Cons1: "inv_PIL pil \<Longrightarrow> list_PIL pil = a#as \<Longrightarrow> \<exists>x xs m. fst pil = IL (x#xs) m"
  using list_PIL_Cons2
  by (metis item_list.exhaust item_list.sel(1) list_PIL_def)

(*parseIL operations are IL operations*)
lemma fst_empty_PIL[simp]: "fst (empty_PIL k) = empty_IL k"
  by (simp add: empty_PIL_def)
lemma fst_insert_PIL[simp]: "fst (insert_PIL x pil) = insert_IL (item x) (fst pil)"
  by (cases pil, cases x, cases "fst pil") auto
lemma fst_union_LPIL[simp]: "fst (union_LPIL xs pil) = union_LIL (map item xs) (fst pil)"
  by (cases pil,  induction xs) auto
lemma fst_minus_LPIL[simp]: "fst (minus_LPIL k xs pil) = minus_LIL k (map item xs) (fst pil)"
  by (cases pil, induction xs) (auto)
lemma fst_minus_PIL[simp]: "inv_PIL pil1 \<Longrightarrow> fst (minus_PIL pil1 pil2) = minus_IL (fst pil1) (fst pil2)"
  by (cases pil1) (auto simp add: minus_PIL_def minus_IL_def)


lemma set_zip_eq_length_rule: "length xs = length ys \<Longrightarrow> \<forall>x \<in> set (zip xs ys). Q (fst x) \<Longrightarrow> \<forall>x \<in> set xs. Q x"
  by (induction xs ys rule: list_induct2) auto

lemma wf_PIL_impl_wf1_IL: 
  assumes "inv_PIL pil" "wf_PIL k pil" shows "wf1_IL k (fst pil)"
proof-
  obtain as m ts where "pil = (IL as m, ts)"
    by (metis set_PIL.cases il_decomp)
  then show ?thesis using set_zip_eq_length_rule[of as ts "\<lambda>x. wf_item1 k x"] assms 
    by (auto simp add: wf_bin1_def)
qed


subsubsection \<open>Parsing algorithm\<close>

definition Predict_PL :: "nat \<Rightarrow> ('n,'t) item \<Rightarrow> ('n,'t) item_P list" where 
"Predict_PL k x = map (\<lambda>p. (Item p 0 k, [])) (filter (\<lambda>p. next_sym x (Nt(lhs p))) ps)"

(* The let version is acceptable to the time function package, the paired lambda version is not *)
definition Complete_PL :: "('n, 't) item_P list list \<Rightarrow> ('n, 't) item_P \<Rightarrow> ('n, 't) item_P list" where
  "Complete_PL Bs y = map (\<lambda> x. let (p,t) = x in (mv_dot p, (Rule (lhs(prod (item y))) (rev (trees y)))#t)) (filter (\<lambda> x. let (p,t) = x in next_sym p (Nt(lhs(prod(item y))))) (Bs ! from (item y)))"

(*definition Complete_PL :: "('n, 't) item_P list list \<Rightarrow> ('n, 't) item_P \<Rightarrow> ('n, 't) item_P list" where
  "Complete_PL Bs y = map (\<lambda> (p, t). (mv_dot p, (Rule (lhs(prod (item y))) (rev (trees y)))#t)) (filter (\<lambda> (p, t). next_sym_Nt p (lhs(prod (item y)))) (Bs ! from (item y)))"*)

definition Init_PL :: "('n,'t) item_P list" where
  "Init_PL = map (\<lambda>p. (Item p 0 0, [])) (filter (\<lambda> p. lhs p = (S)) ps)"


definition Scan_PL :: "nat \<Rightarrow> ('n,'t) item_P list \<Rightarrow> ('n,'t) item_P list" where
  "Scan_PL k Bs = (let s = w ! k in
  map (\<lambda>y. let (x,ts) = y in (mv_dot x, Sym s # ts)) (filter (\<lambda>y. let (x,ts) = y in next_sym x s) Bs))"

abbreviation "PreCo_PL Bs x \<equiv>
  if is_complete (item x) then Complete_PL Bs x else Predict_PL (length Bs) (item x)"

fun step2_PIL :: "('n, 't) item_P list list \<Rightarrow>  ('n, 't) parseIL2 \<Rightarrow> ('n, 't) parseIL2" where
  "step2_PIL Bs ((il1, ts1), pil2) =
   (let b = hd_PIL (il1, ts1) in 
    let step = PreCo_PL Bs b in
    (minus_PIL (union_LPIL step (il1, ts1)) (insert_PIL b pil2), insert_PIL b pil2) )"

fun test2_PIL :: "('n, 't) parseIL2 \<Rightarrow> bool" where
"test2_PIL (B,C) = (list_PIL B \<noteq> [])"

definition steps_PIL :: "('n, 't) item_P list list \<Rightarrow> ('n, 't) parseIL2 \<Rightarrow> ('n, 't) parseIL2 option" where
  "steps_PIL Bs BC = while_option test2_PIL (step2_PIL Bs) BC"

definition close2_PIL :: "('n, 't) item_P list list \<Rightarrow> ('n, 't) parseIL \<Rightarrow> ('n, 't) item_P list" where
"close2_PIL Bs B = list2_PIL (snd (the (steps_PIL Bs (B, empty_PIL (length Bs)))))"

fun bins_PIL :: "nat \<Rightarrow> ('n,'t) item_P list list" where
"bins_PIL 0 = [close2_PIL [] (PIL_list 0 Init_PL)]" |
"bins_PIL (Suc k) = (let Bs = bins_PIL k in Bs @ [close2_PIL Bs (PIL_list (length Bs) (Scan_PL k (last Bs)))])"

fun get_parse_tree :: "('n,'t) item_P list \<Rightarrow> ('n,'t) tree option" where
"get_parse_tree [] = None" |
"get_parse_tree (x#xs) = (if is_final (fst x) then Some (Rule S (rev (snd x))) else get_parse_tree xs)"

lemma get_parse_tree_NF: "is_final (fst x) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>s t. (s,t) \<in> set xs \<and> is_final s \<and> get_parse_tree xs = Some (Rule S (rev t))"
  by (induction xs) auto

abbreviation parse_tree_w where
"parse_tree_w \<equiv> get_parse_tree (last (bins_PIL (length w)))"
end

context Earley_G
begin
fun  get_parse_tree_w :: "'t list \<Rightarrow> ('n, 't) tree option" where                
"get_parse_tree_w w = Earley_Gw.parse_tree_w ps S w"
end

subsubsection \<open>Correctness of list based Earley parser\<close>

context Earley_Gw
begin

lemma PPredict_L_eq_Predict_L: "map item (Predict_PL k s) = Predict_L k s"
  by (auto simp add: Predict_PL_def Predict_L_def)

lemma PComplete_L_eq_Complete_L: 
  assumes "from (item b) < length Bs" 
  shows "map item (Complete_PL Bs b) = Complete_L (map (map item) Bs) (item b)"
proof-
  have "map item (Complete_PL Bs b)
    = map mv_dot (map item (filter (\<lambda>(p, t). next_sym p (Nt(lhs(prod(item b))))) (Bs ! from (item b))))" by (auto simp add: Complete_PL_def)
  also have "... = map mv_dot (map item (filter (\<lambda>x. next_sym (item x) (Nt(lhs(prod(item b))))) (Bs ! from (item b))))"
    by (simp add: case_prod_beta')
  also have "... = map mv_dot (filter (\<lambda>x. next_sym x (Nt(lhs(prod(item b))))) (map item (Bs ! from (item b))))"
    using filter_map
    by (metis (no_types, lifting) ext comp_def)
  finally show ?thesis
    using assms by (auto simp add: Complete_L_def)
qed

lemma Init_PL_eq_Init_L: "map item Init_PL = Init_L"
  by (auto simp add: Init_PL_def Init_L_def)

lemma Scan_PL_eq_Scan_L: "map item (Scan_PL k Bs) = Scan_L k (map item Bs)"
proof-
  have "map item (Scan_PL k Bs) = map mv_dot (map item (filter (\<lambda>(p, t).  next_sym p (w ! k)) Bs))"
    by (auto simp add: Scan_PL_def Let_def)
  also have "... = map mv_dot (map item (filter (\<lambda>x. next_sym (item x) (w ! k)) Bs))"
    by (simp add: case_prod_beta')
  also have "... = map mv_dot (filter (\<lambda>x. next_sym x (w ! k)) (map item Bs))"
    using filter_map
    by (metis (no_types, lifting) ext comp_def)
  finally show ?thesis
    by (auto simp add: Scan_L_def)
qed

lemma PCompleteL_sub_PComplete: "from (item st) < length Bs \<Longrightarrow> set (Complete_PL Bs st) \<subseteq> Complete_P (map set Bs) st"
  by (auto simp add: Complete_PL_def Complete_P_def)
  
lemma wf1_Complete_PL: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_item_P1 (length Bs) st" "is_complete (item st)" 
  shows "wf_parse_bin1 (length Bs) (set (Complete_PL Bs st))"
proof-
  have "set (Complete_PL Bs st) \<subseteq> Complete_P (map set Bs) st"
    using assms PCompleteL_sub_PComplete by (auto simp add: wf_item1_def)
  then show ?thesis using assms wf_parse_complete[of "map set Bs" st] by auto
qed

lemma PScanL_sub_PScan: "k < length w \<Longrightarrow> set (Scan_PL k xs) \<subseteq> Scan_P k (set xs)"
  by (auto simp add: Scan_PL_def Scan_P_def w_def Let_def)

lemma wf1_Scan_PL: "k < length w \<Longrightarrow> wf_parse_bin1 k (set xs) \<Longrightarrow> wf_parse_bin1 (Suc k) (set (Scan_PL k xs))"
  using PScanL_sub_PScan wf_parse_scan
  by (meson subset_code(1) wf_parse_bin1.elims(2,3))

end

context Earley_Gw_eps
begin

lemma wf1_Predict_PL: "wf_item_P1 k s \<Longrightarrow> wf_parse_bin1 k (set (Predict_PL k (item s)))"
  using \<epsilon>_free by (auto simp add: Predict_PL_def wf_item1_def wf_item_def slice_drop_take \<alpha>_def is_complete_def)

lemma wf1_Init_PL: "wf_parse_bin1 0 (set (Init_PL))"
  using \<epsilon>_free by (auto simp add: Init_PL_def wf_item1_def wf_item_def slice_drop_take \<alpha>_def is_complete_def) 

lemma forall_from_Suc_parse: "wf_parse_bin1 k xs \<Longrightarrow> \<forall>x \<in> xs. from (item x) < Suc k"
  by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)

lemma PIL_inv_parse_step1: "pil1 = (il1, t#ts) \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL (length Bs) pil1
  \<Longrightarrow> length (froms (fst pil1)) = Suc (length Bs) \<Longrightarrow> wf_parse_bins1 (map set Bs) \<Longrightarrow> step2_PIL Bs (pil1, pil2) = (pil3, pil4) \<Longrightarrow> inv_PIL pil3"
proof-
  assume assms: "pil1 = (il1, t#ts)" "inv_PIL pil1" "wf_PIL (length Bs) pil1" "length (froms (fst pil1)) = Suc (length Bs)"
    "step2_PIL Bs (pil1, pil2) = (pil3, pil4)" "wf_parse_bins1 (map set Bs)"
  let ?b = "hd_PIL pil1"
  let ?step = "PreCo_PL Bs ?b"
  have "wf_item_P1 (length Bs) ?b" using assms hd_PIL_in_set_PIL
    by (meson list.discI wf_PIL.simps wf_parse_bin1.elims(2))
  then have "wf_parse_bin1 (length Bs) (set ?step)" using wf1_Predict_PL wf1_Complete_PL assms
    by (smt (verit, del_insts))
  then have "inv_PIL (union_LPIL ?step pil1)" 
    using PIL_inv_union_LPIL assms(2,4) forall_from_Suc_parse by auto
  then show "inv_PIL pil3"
    using PIL_inv_minus_PIL[of "union_LPIL ?step pil1" "(insert_PIL (hd (list il1), t) pil2)"] 
      assms(1,4,5)
    by (metis (no_types, lifting) step2_PIL.simps hd_PIL.simps length_union_LPIL old.prod.inject zero_less_Suc)
qed

lemma PIL_inv_parse_step1': "list_PIL pil1 \<noteq> [] \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL (length Bs) pil1
  \<Longrightarrow> length (froms (fst pil1)) = Suc (length Bs) \<Longrightarrow> wf_parse_bins1 (map set Bs) 
  \<Longrightarrow> step2_PIL Bs (pil1, pil2) = (pil3, pil4) \<Longrightarrow> inv_PIL pil3"
  using PIL_inv_parse_step1 list_PIL_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma PIL_inv_parse_step2: 
  assumes "pil1 = (il1, t#ts)" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)"
  "inv_PIL pil2" "inv_PIL pil1" "length (froms (fst pil2)) = length (froms (fst pil1))"
shows "inv_PIL pil4"
proof-
  have "\<forall> x \<in> set (list il1). from x < length (froms (fst pil2))" using assms by (cases il1) auto
  then have "\<forall> x \<in> set (zip (list il1) (t#ts)). from (item x) < length (froms (fst pil2))" 
    by (auto simp add: set_zip_leftD)
  moreover have "(hd (list il1), t) \<in> set (zip (list il1) (t#ts))"
    by (metis hd_PIL.simps hd_PIL_in_set_PIL assms(1,4) list.distinct(1) set_PIL.simps)
  ultimately show ?thesis
    using PIL_inv_insert assms by (fastforce simp add: Let_def)
qed

lemma PIL_inv_parse_step2': 
  assumes "list_PIL pil1 \<noteq> []"  "step2_PIL Bs (pil1, pil2) = (pil3, pil4)"
  "inv_PIL pil2" "inv_PIL pil1" "length (froms (fst pil2)) = length (froms (fst pil1))"
shows "inv_PIL pil4"
  using PIL_inv_parse_step2 list_PIL_Cons2 assms
  by (metis recognized_L.cases surjective_pairing)

lemma Pstep2_IL_eq_step2_IL:
  assumes step: "list il1 \<noteq> []" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)" "step2_IL (map (map item) Bs) (il1, il2) = (il3, il4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_parse_bin1 (length Bs) (set_PIL pil1)" "wf_parse_bins1 (map set Bs)"
  and eq_start: "fst pil1 = il1" "fst pil2 = il2"
  shows "fst pil3 = il3 \<and> fst pil4 = il4"
proof- 
  from step obtain a as m where P_il1: "il1 = IL (a#as) m"
    by (metis item_list.sel(1) recognized_L.cases il_decomp)
  then obtain t ts where P_ts: "pil1 = (il1, t#ts)" using eq_start invs(1)
    by (metis item_list.sel(1) inv_PIL.simps Suc_length_conv fst_conv set_PIL.cases)
  let ?step = "PreCo_PL Bs (a, t)"
  have wf_at: "wf_item_P1 (length Bs) (a,t)" using wf P_il1 P_ts by auto
  then have "wf_parse_bin1 (length Bs) (set ?step)"
    using wf1_Predict_PL wf1_Complete_PL wf
    by (smt (verit, ccfv_threshold) fst_conv)
  then have "inv_PIL (union_LPIL (?step) pil1)" 
    using PIL_inv_union_LPIL invs forall_from_Suc_parse leng by auto
  then show ?thesis 
    using step eq_start invs P_ts P_il1 PPredict_L_eq_Predict_L PComplete_L_eq_Complete_L wf hd_PIL_in_set_PIL 
    by (auto simp add: Let_def wf_item1_def)
qed

lemma Pstep2_IL_eq_step2_IL1:
  assumes step: "list_PIL pil1 \<noteq> []" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_parse_bin1 (length Bs) (set_PIL pil1)" "wf_parse_bins1 (map set Bs)"
shows "(let x = step2_IL (map (map item) Bs) (fst pil1, fst pil2) in fst pil3 = (fst x) \<and> fst pil4 = (snd x))"
  using Pstep2_IL_eq_step2_IL
  by (metis list_PIL_def invs leng local.step(1,2) local.wf surjective_pairing)

lemma wf_parse_step1: 
  assumes "pil1 = (il1, t#ts)" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)" 
  and wf_parse: "wf_parse_bins1 (map set Bs)" "wf_PIL (length Bs) pil1" "inv_PIL pil1" 
shows "wf_PIL (length Bs) pil3"
proof-
  let ?b = "hd_PIL (il1, t#ts)"
  let ?step = "PreCo_PL Bs ?b"
  from assms have 3: "pil3 = minus_PIL (union_LPIL ?step (il1, t#ts)) (insert_PIL ?b pil2)" 
    by (auto simp add: Let_def)
  have "wf_item_P1 (length Bs) ?b" using wf_parse hd_PIL_in_set_PIL assms by (auto simp del: wf_item_P1.simps hd_PIL.simps)
  then have "wf_parse_bin1 (length Bs) (set ?step)" using wf1_Complete_PL wf1_Predict_PL wf_parse
    by presburger
  then show ?thesis 
  using wf_minus_PIL wf_union_LPIL 3 wf_parse assms(1) by blast
qed

lemma wf_parse_step1': "list_PIL pil1 \<noteq> [] \<Longrightarrow> step2_PIL Bs (pil1, pil2) = (pil3, pil4) 
  \<Longrightarrow> wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PIL (length Bs) pil1 \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL (length Bs) pil3"
  using wf_parse_step1 list_PIL_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma wf_parse_step2: 
  assumes "pil1 = (il1, t#ts)" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)" 
  and wf_parse: "wf_PIL (length Bs) pil1" "inv_PIL pil1" "wf_PIL (length Bs) pil2" 
  shows "wf_PIL (length Bs) pil4"
proof-
  let ?b = "hd_PIL (il1, t#ts)"
  from assms have 4: "pil4 = insert_PIL ?b pil2" by (auto simp add: Let_def)
  have "wf_item_P1 (length Bs) ?b" using wf_parse(1,2) hd_PIL_in_set_PIL assms(1) 
    by (auto simp del: wf_item_P1.simps hd_PIL.simps)
  then show ?thesis using wf_PIL_insert wf_parse(1) assms 4 by blast
qed

lemma wf_parse_step2': "list_PIL pil1 \<noteq> [] \<Longrightarrow> step2_PIL Bs (pil1, pil2) = (pil3, pil4) 
  \<Longrightarrow> wf_PIL (length Bs) pil1 \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> wf_PIL (length Bs) pil2 \<Longrightarrow> wf_PIL (length Bs) pil4"
  using wf_parse_step2 list_PIL_Cons2
  by (metis eq_snd_iff neq_Nil_conv)

lemma length_parse_step1: 
  assumes step: "pil1 = (il1, t#ts)" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_PIL (length Bs) pil1" "wf_parse_bins1 (map set Bs)"
  shows "length (froms (fst pil3)) = length (froms (fst pil1))"
proof- 
  have "list il1 \<noteq> []" using invs step
    by force
  then obtain a as m where P_il1: "il1 = IL (a#as) m"
    by (metis item_list.sel(1) il_decomp recognized_L.cases)
  then have m_ne: "m \<noteq> []" using leng step by force
  let ?step = "PreCo_PL Bs (a, t)"
  have wf_at: "wf_item_P1 (length Bs) (a,t)" using wf P_il1 step(1) by auto
  then have "wf_parse_bin1 (length Bs) (set ?step)"
    using wf1_Predict_PL wf1_Complete_PL wf
    by (smt (verit, ccfv_threshold) fst_conv)
  then have "inv_PIL (union_LPIL (?step) pil1)" 
    using PIL_inv_union_LPIL invs forall_from_Suc_parse leng by auto
  then show ?thesis using length_union_LPIL length_minus_PIL[of "union_LPIL (?step) pil1"] step P_il1 m_ne
    by (auto simp add: Let_def)
qed

lemma length_parse_step1': 
  assumes "list_PIL pil1 \<noteq> []" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)"
  and invs: "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and wf: "wf_PIL (length Bs) pil1" "wf_parse_bins1 (map set Bs)"
  shows "length (froms (fst pil3)) = length (froms (fst pil1))"
using length_parse_step1 list_PIL_Cons2 assms invs leng wf
  by (metis eq_snd_iff neq_Nil_conv)

lemma length_parse_step2: 
  assumes step: "pil1 = (il1, t#ts)" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)"
shows "length (froms (fst pil4)) = length (froms (fst pil2))" 
  using step by (auto simp add: Let_def)

lemma length_parse_step2': 
  assumes "list_PIL pil1 \<noteq> []" "step2_PIL Bs (pil1, pil2) = (pil3, pil4)" "inv_PIL pil1"
  shows "length (froms (fst pil4)) = length (froms (fst pil2))" 
using length_parse_step2 list_PIL_Cons2 assms
  by (metis eq_snd_iff neq_Nil_conv)

lemma test2_PIL_def: "test2_PIL = (\<lambda>(B,C). list_PIL B \<noteq> [])"
using test2_PIL.simps by blast

lemma steps_PIL_inv1:
  assumes inv: "inv_PIL pil1" and wf: "wf_PIL (length Bs) pil1" "wf_parse_bins1 (map set Bs)"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and step: "steps_PIL Bs (pil1,pil2) = Some (pil1', pil2')"
shows "inv_PIL pil1'"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). inv_PIL pil1 \<and> wf_PIL (length Bs) pil1 \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil1)) = Suc (length Bs)"] 
    PIL_inv_parse_step1' wf_parse_step1' length_parse_step1' step inv leng wf unfolding steps_PIL_def test2_PIL_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_PIL_inv2: 
  assumes inv: "inv_PIL pil2" "inv_PIL pil1"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)"
  and wf: "wf_PIL (length Bs) pil1" "wf_parse_bins1 (map set Bs)"
  and step: "steps_PIL Bs (pil1,pil2) = Some (pil1', pil2')"
shows "inv_PIL pil2'"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). inv_PIL pil2 \<and> inv_PIL pil1 
      \<and> length (froms (fst pil1)) = Suc (length Bs) \<and> length (froms (fst pil2)) = Suc (length Bs)
      \<and> wf_PIL (length Bs) pil1 \<and> wf_parse_bins1 (map set Bs)"] 
    PIL_inv_parse_step2' PIL_inv_parse_step1' length_parse_step1' length_parse_step2' wf_parse_step1' 
    step inv leng wf unfolding steps_PIL_def test2_PIL_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_PIL_wf1: 
  assumes wf: "wf_parse_bins1 (map set Bs)" "wf_PIL (length Bs) pil1"
  and inv: "inv_PIL pil1" 
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and sf: "steps_PIL Bs (pil1,pil2) = Some (pil1', pil2')"  
shows "wf_PIL (length Bs) pil1'"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). wf_PIL (length Bs) pil1 \<and> inv_PIL pil1 
      \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil1)) = Suc (length Bs)"] 
    wf_parse_step1' step2_IL_inv1_il PIL_inv_parse_step1' length_parse_step1' wf sf inv leng
  unfolding steps_PIL_def test2_PIL_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_PIL_wf2: 
  assumes wf: "wf_parse_bins1 (map set Bs)" "wf_PIL (length Bs) pil1" "wf_PIL (length Bs) pil2"
  and inv: "inv_PIL pil1" 
  and leng: "length (froms (fst pil1)) = Suc (length Bs)" "length (froms (fst pil2)) = Suc (length Bs)"
  and sf: "steps_PIL Bs (pil1,pil2) = Some (pil1', pil2')"  
shows "wf_PIL (length Bs) pil2'"
  using while_option_rule[where P= "\<lambda>(pil1,pil2). wf_PIL (length Bs) pil2 \<and> wf_PIL (length Bs) pil1
      \<and> inv_PIL pil1 \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil1)) = Suc (length Bs)
      \<and> length (froms (fst pil2)) = Suc (length Bs)"] 
    wf_parse_step1' wf_parse_step2' step2_IL_inv1_il PIL_inv_parse_step1' length_parse_step1'
    length_parse_step2' wf sf inv leng unfolding steps_PIL_def test2_PIL_def
  by (smt (verit, ccfv_SIG) case_prodE case_prodI2 case_prod_conv)

lemma steps_one_step: "list a \<noteq> [] \<Longrightarrow> steps2_IL Bs (a,b) = Some (a',b') \<Longrightarrow> step2_IL Bs (a,b) = (c,d) \<Longrightarrow> steps2_IL Bs (c,d) = Some (a',b')"
  unfolding steps2_IL_def
  by (simp add: while_option_unfold)

lemma steps_PIL_steps:
  assumes step: "list il1 \<noteq> []" "steps_PIL Bs (pil1, pil2) = Some (pil3, pil4)" "steps2_IL (map (map item) Bs) (il1, il2) = Some (il3, il4)"
  and eq_start: "fst pil1 = il1" "fst pil2 = il2"
  and leng: "length (froms (fst pil1)) = Suc (length Bs)"
  and invs: "inv_PIL pil1"
  and wf: "wf_parse_bin1 (length Bs) (set_PIL pil1)" "wf_parse_bins1 (map set Bs)"
shows "steps2_IL (map (map item) Bs) (fst pil3, fst pil4) = Some (il3, il4)"
proof-
  let ?P = "\<lambda>(pil3,pil4). steps2_IL (map (map item) Bs) (fst pil3, fst pil4) = Some (il3, il4) \<and> inv_PIL pil3 
      \<and> wf_PIL (length Bs) pil3 \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (fst pil3)) = Suc (length Bs)"
  let ?b = "(\<lambda>(B,C). list_PIL B \<noteq> [])" 
  let ?c = "(step2_PIL Bs)"
  have "?P s \<Longrightarrow> ?b s \<Longrightarrow> ?P (?c s)" for s
  proof-
    assume P: "?P s" and b: "?b s"
    then obtain il1' ts1 il2' ts2 il3' ts3 il4' ts4 where P_s: "s = ((il1', ts1), (il2', ts2)) \<and> step2_PIL Bs s = ((il3', ts3), (il4', ts4))"
      by (metis (no_types, opaque_lifting) old.prod.exhaust)
    obtain il5 il6 where step_f: "step2_IL (map (map item) Bs) (il1', il2') = (il5, il6)"
      using list_PIL_def by fastforce
    then have eq: "il5 = il3' \<and> il6  = il4'" using b P P_s 
        Pstep2_IL_eq_step2_IL[of _ _ "(il1', ts1)" "(il2', ts2)" "(il3', ts3)" "(il4', ts4)" il2' il5 il6]
      by (fastforce simp add: list_PIL_def)
    have 1: "inv_PIL (il3', ts3) \<and> wf_parse_bin1 (length Bs) (set_PIL (il3', ts3))
        \<and> wf_parse_bins1 (map set Bs) \<and> length (froms (il3')) = Suc (length Bs) "
      using P b P_s PIL_inv_parse_step1'[of "(il1', ts1)"] wf_parse_step1' length_parse_step1'
      by (auto simp del: wf_parse_bin1.simps )
    have "list il1' \<noteq> []" using b P_s by (auto simp add: list_PIL_def)
    then show "?P (?c s)" using P 1 P_s eq step_f steps_one_step[of il1' "(map (map item) Bs)" il2' il3 il4] 
       by (auto simp add:  simp del: wf_parse_bin1.simps)
  qed
  then show ?thesis
    using while_option_rule[where P= ?P, where b= ?b, where c= ?c] using eq_start invs wf step leng
    unfolding steps_PIL_def test2_PIL_def
  by (smt (verit) steps_PIL_def case_prod_conv wf_PIL.elims(1))
qed

theorem steps_PIL_NF: "wf_parse_bins1 (map set Bs) \<Longrightarrow> wf_PIL (length Bs) pil1
  \<Longrightarrow> wf_PIL (length Bs) pil2 \<Longrightarrow> inv_PIL pil1 \<Longrightarrow> inv_PIL pil2 
  \<Longrightarrow> length (froms (fst pil1)) = Suc (length Bs) \<Longrightarrow> length (froms (fst pil2)) = Suc (length Bs)
  \<Longrightarrow> \<exists>pil1' pil2'. steps_PIL Bs (pil1,pil2) = Some (pil1',pil2') "
using wf_step2_IL_less[of "length Bs"]
proof (induction "(fst pil1,fst pil2)" arbitrary: pil1 pil2 rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "list (fst pil1) = []"
    thus ?thesis by (simp add: while_option_unfold steps_PIL_def list_PIL_def)
  next
    let ?steps = "while_option (\<lambda>(as,bs). list_PIL as \<noteq> []) (step2_PIL Bs)"
    assume cons: "list (fst pil1) \<noteq> []"
    then obtain il1 t ts where P_pil1: "pil1 = (il1, t#ts)" using less.prems(4)
      by (metis list_PIL_Cons2 list_PIL_def list.exhaust surjective_pairing)
    then obtain pil1' pil2'
      where P_step: "(pil1',pil2') = step2_PIL Bs (pil1,pil2)"
      by (metis surj_pair)
    then have wf_inv: "wf_PIL (length Bs) pil1'" "wf_PIL (length Bs) pil2'" "inv_PIL pil1'" "inv_PIL pil2'"
      "length (froms (fst pil1')) = Suc (length Bs)" "length (froms (fst pil2')) = Suc (length Bs)"
      using wf_parse_step1 wf_parse_step2 PIL_inv_parse_step1 PIL_inv_parse_step2 
        length_parse_step1 length_parse_step2 less.prems P_pil1
      by (metis, metis, metis, metis, metis, metis)
      
    from P_step have step_f: "(fst pil1',fst pil2') = step2_IL (map (map item) Bs) (fst pil1, fst pil2)"
      using less.prems Pstep2_IL_eq_step2_IL1[of pil1 Bs pil2 pil1' pil2'] cons unfolding list_PIL_def by (auto simp add: Let_def)
    have "wf1_IL (length Bs) (fst pil1) \<and> wf1_IL (length Bs) (fst pil2)"
      using less.prems wf_PIL_impl_wf1_IL by (cases pil1, cases pil2) (auto simp del: wf_PIL.simps inv_PIL.simps)
    then have "((fst pil1',fst pil2'), (fst pil1, fst pil2)) \<in> step2_IL_less (length Bs)" 
      using less.prems step2_IL_less_step[of "fst pil1" "(map (map item) Bs)" "fst pil2"] \<open>list (fst pil1) \<noteq> []\<close> step_f 
      by (cases pil1, cases pil2) (auto simp add: wf_parse_bins1_def wf_bins1_def wf_bin1_def)
    from less.hyps[OF this \<open>wf_parse_bins1 (map set Bs)\<close> wf_inv]
    show ?thesis
      by (simp add: P_step while_option_unfold steps_PIL_def)
  qed
qed

lemma Pclose2_IL_eq_close2_IL: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_PIL (length Bs) pil1" "inv_PIL pil1" 
    "length (froms (fst pil1)) = Suc (length Bs)"
  shows "map item (close2_PIL Bs pil1) = close2_IL (map (map item) Bs) (fst pil1)"
proof-
  obtain pil3 pil4 where P_steps: "steps_PIL Bs (pil1, empty_PIL (length Bs)) = Some (pil3, pil4)"
    using assms steps_PIL_NF PIL_inv_empty wf_empty_PIL length_empty_PIL by blast
  then have P_pil3: "wf_PIL (length Bs) pil3 \<and> inv_PIL pil3 \<and> list (fst pil3) = []"
    using steps_PIL_wf1 steps_PIL_inv1 while_option_stop assms
    unfolding steps_PIL_def list_PIL_def test2_PIL_def
    by (metis (mono_tags, lifting) case_prodI)
  from P_steps have inv_pil4: "inv_PIL pil4" 
    using PIL_inv_empty wf_empty_PIL length_empty_PIL steps_PIL_inv2 assms by blast
  from assms have "wf_bins1 (map set (map (map item) Bs))" using wf_parse_bins1_impl_bins1[of "map set Bs"] 
    by (auto simp add: wf_bins1_def)
  then obtain il3 il4 where steps: "steps2_IL (map (map item) Bs) (fst pil1, empty_IL (length Bs)) = Some (il3, il4)"
    using assms Close2_L_NF[of "(map (map item) Bs)" "fst pil1" "empty_IL (length Bs)"] wf_PIL_impl_wf1_IL[of "pil1" "length Bs"] set_empty_IL
    by (cases pil1) (auto simp add: wf_bin1_def empty_inv)
  have "fst pil3 = il3 \<and> fst pil4 = il4"
  proof (cases "list (fst pil1) = []")
    case True
    then show ?thesis using P_steps steps unfolding steps_PIL_def steps2_IL_def list_PIL_def test2_PIL_def
      by (auto simp add: while_option_unfold)
  next
    case False
    then have "steps2_IL (map (map item) Bs) (fst pil3, fst pil4) = Some (il3, il4)"
      using steps_PIL_steps assms P_steps steps P_pil3 by auto
    then show ?thesis using P_pil3 unfolding steps2_IL_def by (auto simp add: while_option_unfold)
  qed
  then show ?thesis using P_steps steps inv_pil4 unfolding close2_PIL_def close2_IL_def 
    by (cases pil4) auto
qed

lemma set_list2_PIL_eq_set_PIL[simp]: "set (list2_PIL pil) = set_PIL pil"
  by (cases pil) auto

lemma wf_close2_PIL: 
  assumes "wf_parse_bins1 (map set Bs)" "wf_PIL (length Bs) pil" "inv_PIL pil" 
      "length (froms (fst pil)) = Suc (length Bs)"
  shows "wf_parse_bin1 (length Bs) (set (close2_PIL Bs pil))"
proof-
  obtain pil3 pil4 where P: "steps_PIL Bs (pil, empty_PIL (length Bs)) = Some (pil3, pil4)"
    using assms steps_PIL_NF wf_empty_PIL PIL_inv_empty length_empty_PIL by blast
  then have "wf_PIL (length Bs) pil4" using steps_PIL_wf2 assms
    using wf_empty_PIL length_empty_PIL by blast
  then show ?thesis unfolding close2_PIL_def P by (auto simp del: wf_parse_bin1.simps)
qed

lemma length_bins_P[simp]: "length (bins_PIL k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma wf_parse_bins_IL: "k \<le> length w \<Longrightarrow> wf_parse_bins1 (map set (bins_PIL k))"
proof (induction k)
  case 0
  then show ?case using wf_PIL_list wf_close2_PIL[of "[]"] 
      wf1_Init_PL PIL_inv_PIL_list[OF forall_from_Suc_parse] 
    by (auto simp add: wf_parse_bins1_def simp del: wf_parse_bin1.simps)
next
  case (Suc k)
  have "bins_PIL k \<noteq> []" using length_bins_P
    by (metis length_0_conv nat.distinct(1))
  then have "wf_parse_bin1 k (set (last (bins_PIL k)))" using Suc length_bins_P wf_parse_bins1_def 
    by (auto simp add: last_conv_nth simp del: wf_parse_bin1.simps)
  then have 1: "wf_parse_bin1 (Suc k) (set (close2_PIL (bins_PIL k) (PIL_list (Suc k) (Scan_PL k (last (bins_PIL k))))))"
    using Suc wf_PIL_list wf_close2_PIL[of "bins_PIL k"] wf1_Scan_PL 
        PIL_inv_PIL_list[OF forall_from_Suc_parse]
    by (auto simp del: wf_parse_bin1.simps)

  show ?case unfolding wf_parse_bins1_def
  proof
    fix n
    show "n < length (map set (bins_PIL (Suc k))) \<longrightarrow> wf_parse_bin1 n (map set (bins_PIL (Suc k)) ! n)"
    proof
      assume assm: "n < length (map set (bins_PIL (Suc k)))"
      show "wf_parse_bin1 n (map set (bins_PIL (Suc k)) ! n)"
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

lemma bins_PIL_eq_bins_IL: "k \<le> length w \<Longrightarrow> map (map item) (bins_PIL k) = bins_IL k"
proof (induction k)
  case 0
  have "fst (PIL_list 0 Init_PL) = IL_list 0 Init_L"
    using Init_PL_eq_Init_L by (auto simp add: PIL_list_def IL_list_def)
  then show ?case using Pclose2_IL_eq_close2_IL[of "[]" "PIL_list 0 Init_PL"] 
      PIL_inv_PIL_list[OF forall_from_Suc_parse] wf_PIL_list wf1_Init_PL
    by (auto simp add: wf_parse_bins1_def simp del: wf_parse_bin1.simps)
next
  case (Suc k)
  have cons: "bins_PIL k \<noteq> []" using length_bins_P
    by (metis length_0_conv nat.distinct(1))
  then have last_eq: "map item (last (bins_PIL k)) = last (bins_IL k)" using Suc
    by (metis Suc_leD last_map)
  have 1: "wf_parse_bins1 (map set (bins_PIL k))" using wf_parse_bins_IL Suc by auto
  then have "wf_parse_bin1 k (set (last (bins_PIL k)))" using Suc cons by (auto simp add: last_conv_nth wf_parse_bins1_def)
  then have wf_Scan: "wf_parse_bin1 (Suc k) (set (Scan_PL k (last (bins_PIL k))))"
    using wf1_Scan_PL Suc by (auto simp del: wf_parse_bin1.simps)
  let ?pil = "PIL_list (Suc k) (Scan_PL k (last (bins_PIL k)))"
  let ?il = "IL_list (Suc k) (Scan_L k (last (bins_IL k)))"
  have "fst ?pil = ?il"
    using Scan_PL_eq_Scan_L last_eq by (auto simp add: PIL_list_def IL_list_def)
  then have "map item (close2_PIL (bins_PIL k) ?pil) = close2_IL (bins_IL k) ?il"
    using Suc Pclose2_IL_eq_close2_IL PIL_inv_PIL_list[OF forall_from_Suc_parse] wf_PIL_list wf_Scan
    using "1" Suc_leD length_bins_P length_PIL_list by metis
  then show ?case using Suc 1 by (auto simp add: Let_def length_bins_IL)
qed

end

context Earley_Gw_eps
begin

lemma accepted_implies_Some_tree: 
  assumes "accepted" shows "\<exists> t. get_parse_tree (last (bins_PIL (length w))) = Some t"
proof-
  obtain s where P_s: "s \<in> \<E> (length w) \<and> is_final s" using assms by (auto simp add: accepted_def)
  have cons: "bins_PIL (length w) \<noteq> []" using length_bins_P
    by (metis length_0_conv nat.distinct(1))
  have "last (map (map item) (bins_PIL (length w))) = last (bins_IL (length w))"
    using bins_PIL_eq_bins_IL by auto
  then have "set (map item (last (bins_PIL (length w)))) = set (last (bins_IL (length w)))"
    using cons by (auto simp add: last_map)
  then have "set (map item (last (bins_PIL (length w)))) = \<E> (length w)" 
    using bins_IL_eq_\<E> length_bins_IL last_conv_nth
    by (metis bins_IL_eq_bins bins_nonempty diff_Suc_1 list.simps(8) nat_le_linear)
  then obtain t where "(s,t) \<in> set (last (bins_PIL (length w)))" using P_s by fastforce
  then obtain s1 t1 where P_s1t1: "(s1, t1) \<in> set (last (bins_PIL (length w)))
    \<and> is_final s1 
    \<and> get_parse_tree (last (bins_PIL (length w))) = Some (Rule S (rev t1))"
    using get_parse_tree_NF[of "(s,t)" "last (bins_PIL (length w))"] P_s by auto
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

theorem generated_parse_tree_is_valid:
  assumes "get_parse_tree (last (bins_PIL (length w))) = Some t"
  shows "valid_parse_tree P S w t"
proof -
  from assms obtain s ts where P_t: "(s,ts) \<in> set (last (bins_PIL (length w))) \<and> is_final s \<and> t = (Rule S (rev ts))" 
    using get_parse_tree_Some_t_decomp by blast
  moreover have "bins_PIL (length w) \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_bins_P)
  ultimately have "wf_item_P1 (length w) (s, ts)" using wf_parse_bins_IL 
    by (auto simp add: wf_parse_bins1_def last_conv_nth simp del: wf_item_P1.simps)
  then show "valid_parse_tree P S w t" using P_t 
    by (auto simp add: valid_parse_tree_def is_final_def wf_item1_def wf_item_def \<alpha>_def rhs_def is_complete_def)
qed

theorem find_parse_tree_iff_w_in_L: "(\<exists>t. get_parse_tree (last (bins_PIL (length w))) = Some t) \<longleftrightarrow> w0 \<in> Lang P S"
proof
  assume "\<exists>t. get_parse_tree (last (bins_PIL (length w))) = Some t"
  then obtain t where "get_parse_tree (last (bins_PIL (length w))) = Some t" by blast
  then have "valid_parse_tree P S w t" using generated_parse_tree_is_valid by blast
  then have "P \<turnstile> [Nt S] \<Rightarrow>* w" using fringe_steps_if_parse_tree[of P t] by (auto simp add: valid_parse_tree_def)
  then show "w0 \<in> lang ps S" by (auto simp add: w_def Lang_def)
next
  assume "w0 \<in> lang ps S"
  then have "recognized Earley" using correctness_Earley by (auto simp add: Lang_def w_def)
  then obtain x where "is_final x \<and> (length w, x) \<in> Earley" using recognized_def by blast
  then have "x \<in> \<E> (length w) \<and> is_final x"
    by (simp add: Earley_eq_\<E>) 
  then have "accepted"
    using accepted_def by blast
  then show "\<exists>t. get_parse_tree (last (bins_PIL (length w))) = Some t"
    using accepted_implies_Some_tree by auto
qed

corollary unambiguous_impl_the_parse_tree: 
  assumes "unambiguous (Cfg P S)" shows "valid_parse_tree P S w t \<longleftrightarrow> get_parse_tree (last (bins_PIL (length w))) = Some t"
proof
  assume valid: "valid_parse_tree P S w t"
  then have "P \<turnstile> [Nt S] \<Rightarrow>* w"
    by(auto simp: valid_parse_tree_def dest: fringe_steps_if_parse_tree)
  then have w0_in_L: "w0 \<in> Lang P S" by (auto simp add: Lang_def w_def)
  then obtain t1 where P_t1: "get_parse_tree (last (bins_PIL (length w))) = Some t1"
    using find_parse_tree_iff_w_in_L by blast
  then have "valid_parse_tree P S w t1"
    by (simp add: generated_parse_tree_is_valid)
  then have "t1 = t" using assms valid w0_in_L by (auto simp add: unambiguous_def w_def)
  then show "get_parse_tree (last (bins_PIL (length w))) = Some t" using P_t1 by auto
next 
  assume "get_parse_tree (last (bins_PIL (length w))) = Some t"
  then show "valid_parse_tree P S w t" using generated_parse_tree_is_valid by blast
qed

lemma unambiguous_impl_P_set_eq_P_L: "G = Cfg P S \<Longrightarrow> unambiguous G \<Longrightarrow> get_parse_tree_set = parse_tree_w"
proof (cases "P \<turnstile> [Nt S] \<Rightarrow>* w")
  case True
  assume assms: "G = Cfg P S" "unambiguous G"
  obtain t1 where "get_parse_tree_set = Some t1" using True get_parse_tree_set_iff by auto
  moreover then have "valid_parse_tree P S w t1" using get_parse_tree_set_valid by auto
  moreover obtain t2 where "parse_tree_w = Some t2" 
    using find_parse_tree_iff_w_in_L True w_def Lang_def accepted_implies_Some_tree Earley_complete assms
    by (auto simp add: accepted_def recognized_def \<E>_def)
  ultimately show ?thesis using assms
    using unambiguous_impl_the_parse_tree by auto
next
  case False
  then have "get_parse_tree_set = None" using get_parse_tree_set_iff
    by simp
  moreover have "parse_tree_w = None" using find_parse_tree_iff_w_in_L w_def False Lang_def
    by (metis Option.option.exhaust mem_Collect_eq)
  ultimately show ?thesis by simp
qed

end

context Earley_Gw
begin
(*parse code defs*)
  declare Earley_Gw.Init_PL_def[code]
  declare Earley_Gw.Predict_PL_def[code]
  declare Earley_Gw.Complete_PL_def[code]
  declare Earley_Gw.Scan_PL_def[code]
  
  declare Earley_Gw.test2_PIL.simps[code]
  declare Earley_Gw.step2_PIL.simps[code]
  declare Earley_Gw.steps_PIL_def[code]
  declare Earley_Gw.close2_PIL_def[code]
  declare Earley_Gw.bins_PIL.simps[code]
  declare Earley_Gw.get_parse_tree.simps[code]
  
  declare Earley_Gw.list2_PIL.simps[code]
  declare Earley_Gw.empty_PIL_def[code]
  declare Earley_Gw.isin_PIL.simps[code]
  declare Earley_Gw.insert_PIL.simps[code]
  declare Earley_Gw.union_LPIL.simps[code]
  declare Earley_Gw.minus_LPIL.simps[code]
  declare Earley_Gw.minus_PIL_def[code]
  declare Earley_Gw.PIL_list_def[code]
  declare Earley_Gw.hd_PIL.simps[code]
  declare Earley_Gw.list_PIL_def[code]
end

subsection \<open>Example\<close>
(* TODO: define Earley_G that can be instantiated independently of w *)

(* Note: only one parse tree; could be either one of 2 *)
lemma "Test.parse_tree_w =
  Some (Rule 0 [Rule 0 [Rule 0 [Sym (Tm 1)], Rule 0 [Sym (Tm 1)]], Rule 0 [Sym (Tm 1)]])"
  by eval

(*unused_thms*)

end