section \<open>Earley's Recognizer: Time Complexity\<close>

theory Earley_Recognizer_Time
imports
  "Earley_Recognizer"
  "HOL-Library.Time_Functions"  
begin

(* TODO rm after next release; is in HOL-Library.Time_Functions *)
lemma T_fst_0[simp]: "T_fst x = 0"
  by (metis T_fst.elims)

lemma T_snd_0[simp]: "T_snd x = 0"
  by (metis T_snd.elims)

time_fun the

declare T_append[simp]

time_fun list_update
time_fun last

lemma T_last[simp]: "as \<noteq> [] \<Longrightarrow> T_last as = length as"
  by (induction as) auto

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

(* not best bound but needed(?) below *)
lemma T_rev_bound: "T_rev xs \<le> 2*length xs * length xs + 1"
  by (induction xs) auto

(* TODO now in While_Combinator; rm after next release *)
(*assumes that the stop condition check takes 0 time*)
definition T_while_option2
  :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<times> nat \<Rightarrow> ('a \<times> nat) option" where
"T_while_option2 b f T_b T_f = while_option (\<lambda>(x,n). b x) (\<lambda>(x,n). (f x, n + T_b x + T_f x))"

definition T_while_option :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a \<Rightarrow> nat" where
"T_while_option b f T_b T_f x = snd (the (T_while_option2 b f T_b T_f (x,0)))"

lemma T_while_option_eq_T_while_option2:
  "while_option b f s = map_option fst (T_while_option2 b f tb tf (s,n0))"
unfolding T_while_option2_def
  using while_option_commute[of "\<lambda>(s,_). b s" b fst "(\<lambda>(s, n). (f s, n + tb s + tf s))" f "(s,n0)"]
  by (simp add: split_def)

lemma T_while_option_if_T_while_option2:
  "T_while_option2 b f tb tf (s,n0) = Some (t,n) \<Longrightarrow> while_option b f s = Some t"
by(simp add: T_while_option_eq_T_while_option2[of b f s tb tf n0])

lemma T_while_option2_if_T_while_option:
  "while_option b f s = Some t \<Longrightarrow> \<exists>n. T_while_option2 b f tb tf (s,n0) = Some (t,n)"
by(simp add: T_while_option_eq_T_while_option2[of b f s tb tf n0])


subsection \<open>Space analysis\<close>

context Earley_Gw
begin

definition "K = Max { length (rhs r) | r. r \<in> set ps }"
definition "L = length ps"

lemma card_wf: 
  assumes "\<forall>p \<in> set ps. length (rhs p) \<le> k" "\<forall>x \<in> bs. wf_item i x" 
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

lemma card_wf1: "\<forall>x \<in> bs. wf_item i x \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
  using card_wf L_def prod_length_bound by simp

lemma card_wf_bin1: "wf_bin1 i bs \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
  using card_wf1 by (simp add: wf_bin1_def wf_item1_def)

lemma card_Si: "card (\<E> i) \<le> L * (Suc K) * (Suc i)"
  using card_wf1 wf_EarleyS by simp

theorem card_Earley: "card Earley \<le> L * (Suc K) * (Suc (length w))^2"
proof-
  let ?X = "{x. (\<exists>i \<le> length w. x = {(k,y). wf_item k y \<and> k = i})}"

  have "Earley \<subseteq> {(k, x). wf_item k x \<and> k \<le> length w}"
    using wf_Earley by (fastforce simp add: wf_item_def)
  also have "... = \<Union> {x. (\<exists>i \<le> length w. x = {(k,y). wf_item k y \<and> k = i})}" by (auto simp add: wf_item_def)
  finally have 1: "Earley \<subseteq> \<Union> {x. (\<exists>i \<le> length w. x = {(k,y). wf_item k y \<and> k = i})}".

  have 2: "x \<in> ?X \<longrightarrow> card x \<le> L * (Suc K) * (Suc (length w))" for x 
  proof
    fix x
    assume assm: "x \<in> ?X"
    then have "\<exists>i \<le> length w. \<forall>(k,y) \<in> x. wf_item k y \<and> k = i" by auto
    then obtain i where P: "\<forall>(k,y) \<in> x. wf_item i y \<and> k = i" and l: "i \<le> length w" by blast
    then have 3: "x \<subseteq> {i} \<times> {y. wf_item i y}" by fastforce

    have "finite ({i} \<times> {y. wf_item i y})"
      by (simp add: finite_ex_wf_item)
    then have "card x \<le> card {y. wf_item i y}" 
      using Groups_Big.card_cartesian_product[of "{i}" "{y. wf_item i y}"] 
            Finite_Set.card_mono[of "{i} \<times> {y. wf_item i y}"] 3 by auto
    also have "... \<le> L * (Suc K) * (Suc i)" using card_wf1 by auto
    also have "... \<le> L * (Suc K) * (Suc (length w))" using l by auto
    finally show "card x \<le> L * (Suc K) * (Suc (length w))".
  qed

  let ?f = "\<lambda>i. {(k,x). wf_item k x \<and> i = k}"
  let ?Y = "{i. i \<le> (length w)}"

  have fin: "?X = ?f ` ?Y" and "finite ?Y" by auto
  then have "card ?X  \<le> card ?Y"
    using card_image_le by force
  then have 3: "card ?X \<le> Suc (length w)" by auto

  have "\<forall> x \<in> ?X. \<exists>i. x \<subseteq> {i} \<times> {y. wf_item i y}" by fastforce
  then have "\<forall>x \<in> ?X. finite x" using finite_wf_item
    by (metis (no_types, lifting) finite.emptyI finite_SigmaI finite_ex_wf_item finite_insert rev_finite_subset)
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

(*unused_thms*)

end (* Earley_Gw*)

subsection \<open>Running time analysis\<close>

subsubsection \<open>Timing functions and simple bounds\<close>

time_fun rhs

time_fun_0 Earley_Gw.w

time_fun prod
time_fun dot
time_fun "from"

lemma T_prod_0[simp]: "T_prod x = 0"
  using T_prod.elims by blast

lemma T_dot_0[simp]: "T_dot x = 0"
  using T_dot.elims by blast

lemma T_from_0[simp]: "T_from x = 0"
  using T_from.elims by blast

time_fun isin_list

time_fun item_list.list
time_fun item_list.froms

lemma T_list_0[simp]: "T_list il = 0"
  using T_list.elims by blast

lemma T_froms_0[simp]: "T_froms il = 0"
  using T_froms.elims by blast

text \<open>Cannot use \<open>time_fun\<close> on \<open>Init_L\<close> inside \<open>Earley_Gw\<close> because it has no parameters.
Strictly speaking, \<open>Init_L\<close> can be pre-computed once because it only depends on \<open>ps\<close> and \<open>S\<close>.
However, we are conservative and define \<open>T_Init_L\<close> outside of \<open>Earley_Gw\<close> as a function of \<open>ps\<close> and \<open>S\<close>;\<close>

time_fun Earley_Gw.Init_L equations Earley_Gw.Init_L_def

text \<open>The following trickery allows us to define \<open>T_Init_L\<close> inside \<open>Earley_Gw\<close> somewhat like this:
  \<open>T_Init_L(inside) = T_Init_L(outside) ps S\<close>\<close>
abbreviation "T_Init_L' \<equiv> T_Init_L"
hide_const T_Init_L

context Earley_Gw
begin

time_fun isin_IL
time_fun insert_IL
time_fun empty_froms
time_fun empty_IL
time_fun union_LIL
time_fun IL_list
time_fun minus_LIL
time_fun minus_IL

time_fun mv_dot
time_fun is_complete
time_fun next_sym

time_fun Scan_L
time_fun Predict_L
time_fun Complete_L

definition "T_Init_L = T_Init_L' ps S" (* see text above *)

time_fun test2_IL
time_fun step2_IL

(* For convenience, because of the proof structure *)
abbreviation "T_steps2_IL2 Bs il12 n
  \<equiv> T_while_option2 test2_IL (step2_IL Bs) T_test2_IL (T_step2_IL Bs) (il12,n)"

fun T_steps2_IL :: "('n, 't) item list list \<Rightarrow> ('n, 't) item_list \<times> ('n, 't) item_list \<Rightarrow> nat" where
"T_steps2_IL Bs = T_while_option test2_IL (step2_IL Bs) T_test2_IL (T_step2_IL Bs)"

time_fun close2_IL
time_fun bins_IL
time_fun is_final
time_fun recognized_L
time_fun earley_recognized1

end (*Context Earley_Gw*)


locale Earley_Gw_eps_T = Earley_Gw_eps where ps = ps for ps :: "('n,'t) prods" +
  fixes T_nth_IL:: "nat \<Rightarrow> nat"
  assumes T_nth_Bound: "(T_nth :: ('n, 't) item list list \<Rightarrow> nat \<Rightarrow> nat) as k \<le> T_nth_IL k"
  and T_update_Bound: "(T_list_update :: ('n, 't) item list list \<Rightarrow> nat \<Rightarrow> ('n, 't) item list \<Rightarrow> nat) as k a \<le> T_nth_IL k"
  and mono_nth: "mono T_nth_IL" (*mono f*)
begin

lemma T_is_complete_bound: "T_is_complete s = Suc (length (rhs (prod s)))"
  by (auto simp add: T_length)

lemma T_next_symbol_bound: 
  assumes "prod x \<in> set ps" shows "T_next_sym x s \<le> 2*(Suc K)"
proof-
  have "length (rhs (prod x)) \<le> K" using prod_length_bound assms by auto
  then show ?thesis 
    using assms T_nth[of "dot x" "rhs (item.prod x)"] by (auto simp add: T_length is_complete_def)
qed

subsubsection \<open>IL time bounds\<close>

lemma T_isin_list_bound: "T_isin_list xs x \<le> length xs + 1"
  by (induction xs) auto

lemma T_isin_IL: "T_isin_IL il (x::('n, 't) item) \<le> T_nth_IL (from x) + length ((froms il) ! from x) + 1"
proof-
  obtain as m where "il = IL as m"
    using inv_IL.cases by blast
  then show ?thesis 
    using T_isin_list_bound[of "m ! from x" x] T_nth_Bound[of m "from x"] by auto
qed

lemma T_empty_IL_bound[simp]: "T_empty_IL k = k + 1"
  by (induction k) auto

lemma T_isin_IL_wf: 
  assumes inv: "inv_IL il" and wf: "wf1_IL k il" "from x < length (froms il)"
  shows "T_isin_IL il x \<le> T_nth_IL (from x) + L * (Suc K) + 1"
proof-
  obtain as m where IL: "il = IL as m"
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
    by (auto simp add: L_def add_mono card_length elim: le_trans)
  then show ?thesis using wf(2) T_isin_IL[of il x] by auto
qed


lemma T_insert_IL_less: 
  assumes "inv_IL il" "wf1_IL k il" and le: "from x < length (froms il)" 
  shows "T_insert_IL x il \<le> 3 * T_nth_IL (from x) + L * (Suc K) + 1"
proof-
  obtain as m where "il = IL as m"
    using inv_IL.cases by blast
  then have "T_insert_IL x il \<le> T_isin_IL il x + T_nth m (from x) + T_list_update m (from x) (x # m ! from x)" using le by auto
  also have "... \<le> T_nth_IL (from x) + L * (Suc K) + 1 + T_nth_IL (from x) + T_nth_IL (from x)" 
    using assms T_isin_IL_wf[of il k x] T_nth_Bound[of m "from x"] T_update_Bound[of m "from x" "x # m ! from x"] by auto
  finally show ?thesis by auto
qed

lemma wf1_insert_IL:
  "inv_IL il \<Longrightarrow> wf1_IL k il \<Longrightarrow> from x < length (froms il) \<Longrightarrow> wf_item1 k x \<Longrightarrow> wf1_IL k (insert_IL x il)"
using set_insert_IL1 wf_bin1_def by auto

            
lemma wf1_IL_union_LIL: "inv_IL il \<Longrightarrow> wf1_IL k il \<Longrightarrow> \<forall>a\<in>set as. from a < length (froms il) \<Longrightarrow> wf_bin1 k (set as) \<Longrightarrow> wf1_IL k (union_LIL as il)"
  using LIL_union wf_bin1_def by fastforce

lemma T_union_LIL_wf: "inv_IL il \<Longrightarrow> wf1_IL (length (froms il) - 1) il \<Longrightarrow> wf_bin1 (length (froms il) - 1) (set as)
  \<Longrightarrow> \<forall>a\<in>set as. from a < length (froms il) \<Longrightarrow> T_union_LIL as il \<le> (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1"
proof (induction as arbitrary: il)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then have 1: "inv_IL (union_LIL as il) \<and> wf1_IL (length (froms il) - 1) (union_LIL as il)" using LIL_union_inv wf1_IL_union_LIL
    by (metis list.set_intros(2) wf_bin1_def)
  have wf_from: "\<forall>x \<in> set (a#as). from x < (length (froms il))" using Cons by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have 2: "from a < Suc (length (froms (union_LIL as il)))" using Cons length_LIL_union by auto
  have 3: "from a \<le> (length (froms il) - 1)" using wf_from by auto
  have "T_union_LIL (a#as) il = T_union_LIL as il + T_insert_IL a (union_LIL as il) + 1" by simp
  also have "... \<le> (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1 + 3 * T_nth_IL (from a) + L * (Suc K) + 1 + 1" 
    using Cons T_insert_IL_less[of "union_LIL as il" "(length (froms il)) - 1" a] 1 2 by (fastforce simp add: wf_bin1_def)
  also have "... \<le> (length as) * (3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 2) + 1 + 3 * T_nth_IL (length (froms il) - 1) + L * (Suc K) + 1 + 1"
    using mono_nth 3 by (auto simp add: monoD)
  finally show ?case by auto
qed

lemma wf1_empty_IL: "wf1_IL l (empty_IL k)"
  using set_empty_IL by (auto simp add: wf_bin1_def)

lemma T_minus_LIL_wf: "wf1_IL k il \<Longrightarrow>  inv_IL il \<Longrightarrow> wf_bin1 k (set as) \<Longrightarrow> Suc k \<le> length (froms il)
  \<Longrightarrow> T_minus_LIL k as il \<le> (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) + k + 2 + length as"
proof (induction as)
  case Nil
  then show ?case by (auto simp del: T_empty_IL.simps)
next
  case (Cons a as)
  then have 1: "wf_bin1 k (set as)" by (auto simp add: wf_bin1_def)
  hence 2: "inv_IL (minus_LIL k as il) \<and> wf1_IL k (minus_LIL k as il)"
    using Cons LIL_minus LIL_minus_inv forall_from_Suc by (auto simp add: wf_bin1_def)
  have 4: "\<forall>x \<in> set (a#as). from x < Suc k" using Cons by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have 3: "from a < length (froms (minus_LIL k as il))" by simp
  have "T_minus_LIL k (a#as) il \<le> T_isin_IL il a + T_minus_LIL k as il + T_insert_IL a (minus_LIL k as il) + 1" by auto
  also have "... \<le> T_nth_IL (from a) + L * (Suc K) + 1 + T_minus_LIL k as il + T_insert_IL a (minus_LIL k as il) + 1" 
    using Cons T_isin_IL_wf 4 by auto
  also have "... \<le> T_nth_IL (from a) + L * (Suc K) + 1 + (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4)
       + k + 3 + length as + T_insert_IL a (minus_LIL k as il) + 1"
    using Cons 1 by auto
  also have "... \<le> T_nth_IL (from a) + L * (Suc K) + 1 + (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) 
       + k + 3 + length as + 3 * T_nth_IL (from a) + L * (Suc K) + 1 + 1"
    using T_insert_IL_less[of "minus_LIL k as il" k a] Cons 2 3 by linarith
  also have "... \<le> T_nth_IL k + L * (Suc K) + 1 + (length as) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) 
       + k + 2 + length as + 3 * T_nth_IL k + L * (Suc K) + 2 + 1"
    using mono_nth 4 by (auto simp add: monoD)
  also have "... \<le> (length (a#as)) * (4 * T_nth_IL k + 2*L * (Suc K) + 4) + k + 2 + (length (a#as))" by simp
  finally show ?case by simp
qed

lemma T_minus_IL_wf: "wf1_IL (length (froms il1) - 1) il1 \<Longrightarrow> inv_IL il1 \<Longrightarrow> inv_IL il2 \<Longrightarrow> wf1_IL (length (froms il1) - 1) il2
  \<Longrightarrow> length (froms il2) \<ge> length (froms il1) \<Longrightarrow> length (froms il1) > 0
  \<Longrightarrow> T_minus_IL il1 il2 \<le> (length (list il1)) * (4 * T_nth_IL (length (froms il1) - 1) + 2*L * (Suc K) + 4) + (length (froms il1) - 1) + 3 + length (list il1) + length (froms il1)"
  using T_minus_LIL_wf[of "length (froms il1) - 1" il2 "list il1"] by (cases il1) (auto simp add: T_length)


subsubsection \<open>Earley recognizer time bounds\<close>

lemma T_Init_L_bound: "T_Init_L \<le> 2 * (L + 1)"
proof-
  have "T_map (\<lambda>p. 0) (filter (\<lambda>p. lhs p = S) ps) \<le> length (filter (\<lambda>p. lhs p = S) ps) + 1"
    using T_map_bound[of "(filter (\<lambda>p. lhs p = S) ps)" "(\<lambda>p. 0)" 0] by auto
  also have "... \<le> length ps + 1" by auto
  finally show ?thesis using T_filter_bound[of ps T_fst 0] by (auto simp add: T_Init_L_def L_def)
qed

lemma T_Scan_L_bound:
  assumes "k < length w" and wf: "wf_bin1 k (set Bs)" 
  shows "T_Scan_L k Bs \<le> k + 2*(K + 2) * length Bs + 3"
proof-
  have 1: "T_nth w k \<le> k+1" using assms by (auto simp add: T_nth)
  let ?T_nxt_sym = "\<lambda>x. T_next_sym x (w!k)"
  have 2: "T_filter ?T_nxt_sym Bs \<le> 2*(Suc K) * length Bs + length Bs + 1" 
    using T_next_symbol_bound wf T_filter_bound[of Bs ?T_nxt_sym "2*(Suc K)"] 
    by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)

  have "T_map T_mv_dot (filter (\<lambda>b. next_sym b (w ! k)) Bs) 
            \<le> length (filter (\<lambda>b. next_sym b (w ! k)) Bs) + 1"
    using T_map_bound[of _ T_mv_dot 0] by auto
  also have "... \<le> length Bs + 1" by auto

  finally show ?thesis using 1 2 assms(1) w_def by (auto simp add: Let_def T_nth)
qed

lemma T_Predict_L_bound:
  assumes "prod x \<in> set ps" shows "T_Predict_L k x \<le> 2*(K + 2)* length ps + 2"
proof-
  have "\<forall>p \<in> set ps. (\<lambda>p. T_next_sym x (Nt(lhs p)) + T_fst p) p \<le> 2*(Suc K)"
    using assms T_next_symbol_bound[of x] by auto
  then have 1: "T_filter (\<lambda>p. T_next_sym x (Nt(lhs p)) + T_fst p) ps \<le> 2*(Suc K) * length ps + length ps + 1"
    using T_filter_bound[of ps _ "2*(Suc K)"] by auto

  have "T_map (\<lambda>p. 0) (filter (\<lambda>p. next_sym x (Nt(lhs p))) ps) \<le> length (filter (\<lambda>p. next_sym x (Nt(lhs p))) ps) + 1"
    using T_map_bound[of _ "(\<lambda>p. 0)" 0] by auto
  also have "... \<le> length ps + 1" by auto
  finally show ?thesis using 1 by auto
qed

lemma T_Complete_L_bound: 
  assumes "from y < length Bs" "wf_bins1 (map set Bs)" 
  shows "T_Complete_L Bs y \<le> length Bs + 2*(K + 2) * length (Bs ! from y) + 2"
proof -
  have 1: "T_nth Bs (from y) \<le> length Bs" using assms by (simp add: T_nth)
  have "\<forall>x \<in> set (Bs ! from y). (\<lambda>b. T_next_sym b (Nt(lhs(prod y))) + (T_prod y + T_fst (item.prod y))) x \<le> 2*(Suc K)"
    using assms T_next_symbol_bound 
    by (auto simp add: wf_bins1_def wf_bin1_def wf_item1_def wf_item_def)
  then have 2: "T_filter (\<lambda>b. T_next_sym b (Nt(lhs(prod y))) + (T_prod y + T_fst (item.prod y))) (Bs ! from y)
            \<le> 2*(Suc K) * length (Bs ! from y) + length (Bs ! from y) + 1"
    using T_filter_bound[of "(Bs ! from y)" _ "2*(Suc K)"] by auto

  have "T_map T_mv_dot (filter (\<lambda>x. next_sym x (Nt(lhs(prod y)))) (Bs ! from y))
          \<le> length (filter (\<lambda>b. next_sym b (Nt(lhs(prod y)))) (Bs ! from y)) + 1"
    using T_map_bound[of _ T_mv_dot 0] by auto
  also have "... \<le> length (Bs ! from y) + 1" by auto
  finally show ?thesis using 1 2 by auto
qed

lemma Predict_Length: "length (Predict_L x k) \<le> L"
  by (auto simp add: Predict_L_def L_def)

lemma distinct_Complete_L:
  assumes "distinct (Bs ! from y)" shows "distinct (Complete_L Bs y)"
proof -                                           
  have "inj_on mv_dot (set (Bs ! from y))"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel item.expand item.inject)
  then have "distinct (map mv_dot (Bs ! from y))" using assms by (simp add: distinct_map)
  then show ?thesis using assms by (simp add: Complete_L_def distinct_map_filter)
qed

lemma mult_mono_mix: "i \<le> (j :: nat) \<Longrightarrow> k * i * l \<le> k * j * l"
  by simp

lemma T_step2_IL_bound: assumes "list il1 \<noteq> []" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf1_IL' Bs il1" "inv_IL il1" "length (froms il1) = Suc (length Bs)"
  "wf1_IL' Bs il2" "inv_IL il2" "length (froms il2) = Suc (length Bs)"
shows "T_step2_IL Bs (il1, il2) 
    \<le> L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + 7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
proof-
  obtain bs m where IL1: "il1 = IL bs m"
    using inv_IL.cases by blast
  obtain b bss where bbs: "bs = b#bss" using assms IL1
    using item_list.sel(1) T_last.cases by blast

  have from_b: "from b \<le> length Bs"
    using assms by (simp add: IL1 bbs wf_bin1_def wf_item1_def wf_item_def)

  let ?step = "PreCo_L Bs b"
  let ?t_step = "(if is_complete b then T_Complete_L Bs b else T_length Bs + T_Predict_L (length Bs) b)"
  have t_step: "?t_step \<le> 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2 + Suc (length Bs)"
  proof (cases)
    assume complete: "is_complete b"
    then have 1: "from b < length Bs" using assms
      using assms by (simp add: bbs IL1 wf_bin1_def wf_item1_def)
    then have 2: "distinct (Bs ! from b)" using assms
      by simp
    have "wf_bin1 (from b) (set (Bs ! from b))" using assms 1
      by (simp add: wf_bins1_def)
    then have "length (Bs ! from b) \<le> L * (Suc K) * (Suc (from b))" 
      using card_wf1 2
      by (metis card_wf_bin1 distinct_card)
    then have 4: "length (Bs ! from b) \<le> L * (Suc K) * (Suc (length Bs))" using 1
      by (meson Suc_le_mono le_trans mult_le_mono2 nat_less_le)

    have "T_Complete_L Bs b \<le> (length Bs) + 2 * (K + 2) * length (Bs ! from b) + 2"
      using assms T_Complete_L_bound 1 by (auto simp add: IL1 bbs simp del: T_Complete_L.simps)
    also have "... \<le> (length Bs) + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2" 
      using mult_le_mono2[OF 4]
      by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) add_le_mono1 nat_add_left_cancel_le)
    finally have "T_Complete_L Bs b \<le> length Bs + 2 * (K + 2) * L * (Suc K) * (Suc (length Bs)) + 2".
    then show ?thesis using complete by simp
  next
    assume incomplete: "\<not>is_complete b"
    have t_pred: "T_Predict_L (length Bs) b \<le> 2 * (K + 2) * L + 2" 
      using T_Predict_L_bound assms by (simp add: L_def IL1 bbs wf_bin1_def wf_item1_def wf_item_def)

    show ?thesis using t_pred incomplete by (auto simp add: T_length)
  qed

  have "T_length (rhs (item.prod b)) = Suc (length (rhs (prod b)))"
    by (simp add: T_length)
  then have 6: "T_length (rhs (item.prod b)) \<le> Suc K" 
    using prod_length_bound[of "prod b"] assms by (auto simp add: IL1 bbs wf_bin1_def wf_item1_def wf_item_def)

  have wfStep: "wf_bin1' Bs (set ?step)"
    using assms wf1_Complete_L[of Bs b] wf1_Predict_L[of "length Bs" b] IL1 bbs
    by (auto simp add: wf_bin1_def wf_item1_def)
  have "is_complete b \<Longrightarrow> distinct (Bs ! from b)" using assms
      by (simp add: wf_bin1_def wf_item1_def IL1 bbs)
  then have lengthStep: "length (?step) \<le> L * (Suc K) * (Suc (length Bs))" 
    using card_wf1[of "set (?step)" "length Bs"] assms distinct_Complete_L wfStep Predict_Length[of "length Bs" b]
    by (auto simp add: distinct_card  wf_bin1_def wf_item1_def)
  then have "T_union_LIL (?step) il1 \<le> length (?step) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1"
    using T_union_LIL_wf[of il1 ?step] assms wfStep forall_from_Suc[OF wfStep] by (auto simp add: IL1)
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1"
    using mult_le_mono1[OF lengthStep]
    using add_le_mono1 by blast
  finally have 7: "T_union_LIL ?step il1 \<le> L * (Suc K) * (Suc (length Bs)) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1".

  have "T_insert_IL b il2 \<le> 3 * T_nth_IL (from b) + L * Suc K + 1"
    using T_insert_IL_less[of il2 _ b] from_b assms by auto
  also have "... \<le> 3 * T_nth_IL (length Bs) + L * Suc K + 1"
    using mono_nth from_b by (auto simp add: monoD)
  finally have 8: "T_insert_IL b il2 \<le> 3 * T_nth_IL (length Bs) + L * Suc K + 1".

  have wf_Comp_union: "wf1_IL' Bs (union_LIL ?step il1)"
    using assms wfStep wf1_IL_union_LIL forall_from_Suc by auto
  have inv_Comp_union: "inv_IL (union_LIL ?step il1)"
    using LIL_union_inv assms wfStep forall_from_Suc by auto
  obtain bs' m' where decomp: "(union_LIL ?step il1) = IL bs' m'"
    using inv_IL.cases by blast
  then have length_Comp_union: "length bs' \<le> L * (Suc K) * (Suc (length Bs))"
    using card_wf_bin1[of "length Bs" "set bs'"] wf_Comp_union inv_Comp_union by (auto simp add: distinct_card)
  have "\<forall>x\<in>set ?step. from x < Suc (length Bs)" 
    using wfStep by (cases "is_complete b") (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  have wf_ins_b: "wf1_IL' Bs (insert_IL b il2)" 
    using assms wf1_insert_IL
    by (metis IL1 bbs item_list.sel(1) from_b less_Suc_eq_le list.set_intros(1) set_IL.elims wf_bin1_def)
  have inv_ins_b: "inv_IL (insert_IL b il2)"
    using inv_insert_IL1 assms(8)
    by (simp add: assms(9) from_b le_imp_less_Suc)

  let ?minus = "T_minus_IL (union_LIL ?step il1) (insert_IL b il2)"
  have "?minus \<le> length bs' * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 4) + length Bs + 3 + length bs' + length (froms il1)"
    using T_minus_IL_wf[of "union_LIL ?step il1" "insert_IL b il2"] decomp inv_Comp_union wf_Comp_union wf_ins_b inv_ins_b
    by (metis One_nat_def assms(6,9) diff_Suc_1' item_list.sel(1) length_froms_insert_IL length_LIL_union less_Suc_eq_0_disj
        less_or_eq_imp_le)
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 4) + length Bs + 3 + L * (Suc K) * (Suc (length Bs)) + Suc (length Bs)"
    using length_Comp_union mult_le_mono1
    using add_le_mono add_le_mono1 assms(6) by presburger
  also have "... \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 5) + 2*length Bs + 4"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"]
    by auto
  finally have 9: "?minus \<le> L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 5) + 2*length Bs + 4".

  have "T_step2_IL Bs (il1, il2) \<le> T_length (rhs (prod b)) + ?t_step +
  T_union_LIL ?step il1 +
   T_insert_IL b il2 + T_minus_IL (union_LIL ?step il1) (insert_IL b il2) +
   T_insert_IL b il2" by (auto simp add: Let_def IL1 bbs simp del: T_Complete_L.simps T_Predict_L.simps T_minus_IL.simps)

  also have "... \<le> Suc K + T_nth_IL (length Bs) + 2 * (K + 2) * L * (Suc K) * Suc (length Bs) + 2 + Suc (length Bs)
    + L * Suc K * (Suc (length Bs)) * (3 * T_nth_IL (length Bs) + L * Suc K + 2) + 1
    + 3 * T_nth_IL (length Bs) + L * Suc K + 1 + L * (Suc K) * (Suc (length Bs)) * (4 * T_nth_IL (length Bs) + 2 * L * Suc K + 5) + 2*length Bs + 4 +
   3 * T_nth_IL (length Bs) + L * Suc K + 1" using t_step 6 7 8 9 by linarith

  also have "... \<le> Suc K + 2 * (K + 2) * L * (Suc K) * Suc (length Bs)
    + L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7)
    + 7 * T_nth_IL (length Bs) + 2* L * Suc K + 3 * Suc (length Bs) + 7"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  also have "... = Suc K + L * (Suc K) * Suc (length Bs) * 2 * (K + 2)
    + L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7)
    + 7 * T_nth_IL (length Bs) + 2* L * Suc K + 3 * Suc (length Bs) + 7"
    by (smt (verit) mult.assoc mult.commute)
  also have "... = L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + 7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K"
    using add_mult_distrib2[of "L * (Suc K) * (Suc (length Bs))"] by auto

  finally show ?thesis.
qed

lemma step2_IL_dist: 
  assumes "list il1 \<noteq> []" "inv_IL il1" "inv_IL il2" "step2_IL Bs (il1, il2) = (il1', il2')" "wf_bins1 (map set Bs)" "wf1_IL' Bs il1"
    "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
  shows "set_IL il1' \<inter> set_IL il2' = {}"
proof-
  obtain a as m bs n where IL: "il1 = IL (a#as) m \<and> il2 = IL bs n"
    using il_decomp assms
    by (metis item_list.sel(1) neq_Nil_conv)
  let ?step = "PreCo_L Bs a"
  have wf_a: "wf_item1 (length Bs) a" using assms(6) IL by (auto simp add: wf_bin1_def)
  then have wf_step: "wf_bin1' Bs (set ?step)"
    using assms(5,6) IL wf1_Complete_L wf1_Predict_L by auto
  have from_a: "from a < length (froms il2)" using wf_a assms(8) by (auto simp add: wf_item1_def wf_item_def)
  have "il1' = minus_IL (union_LIL ?step il1) (insert_IL a il2)" using assms IL by auto
  then have "set_IL il1' \<inter> set_IL (insert_IL a il2) = {}" 
    using assms IL_minus[of "insert_IL a il2" "union_LIL ?step il1"] inv_insert_IL1 from_a LIL_union_inv wf_step forall_from_Suc by auto
  then show ?thesis using assms IL by auto
qed

lemma length_step2_IL_inc: 
  assumes "list il1 \<noteq> []" "inv_IL il2" "wf1_IL (length (froms il2) - 1) il1" "step2_IL Bs (il1, il2) = (il1', il2')" 
          "set_IL il1 \<inter> set_IL il2 = {}" "length (froms il2) > 0"
  shows "length (list il2') = Suc (length (list il2))"
proof-
  obtain a as m where IL1: "il1 = IL (a#as) m"
    using assms by (metis item_list.sel(1) T_last.cases il_decomp) 
  obtain bs n where IL2: "il2 = IL bs n"
    using il_decomp by blast
  have "from a \<le> length (froms il2) - 1" using assms(3) IL1 by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  moreover have "length (froms il2) > 0" using assms(6) IL2 by auto
  ultimately have from_a: "from a < length (froms il2)"
    by linarith
  have "il2' = insert_IL a il2" using assms IL1 by auto
  then have "list il2' = a#bs"
    using assms isin_IL_IL1 from_a by (auto simp add: IL1 IL2 Let_def simp del: isin_IL.simps)
  then show ?thesis by (simp add: IL2)
qed

lemma Tsteps2_IL2: 
  assumes wf_Bs:  "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" 
and il1_assms:  "wf1_IL' Bs il1" "inv_IL il1" "length (froms il1) = Suc (length Bs)"
and il2_assms:  "wf1_IL' Bs il2" "inv_IL il2" "length (froms il2) = Suc (length Bs)"
and dist_ils: "set_IL il1 \<inter> set_IL il2 = {}"
and step:  "T_steps2_IL2 Bs (il1,il2) k = Some ((il1',il2'), k')" "k \<le> (length (list il2)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K)"
  shows "k' \<le> (length (list il2')) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K)" 
proof -
  let ?C = "L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K"
  let ?P3 = "\<lambda>((il1',il2'),k). wf1_IL' Bs il1' \<and> wf1_IL' Bs il2' \<and> wf_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((il1',il2'),k). wf1_IL' Bs il1' \<and> wf1_IL' Bs il2' \<and> wf_bins1 (map set Bs) \<and> inv_IL il1' \<and> inv_IL il2' 
        \<and> length(froms il1') = Suc (length Bs) \<and> length (froms  il2') = Suc (length Bs) \<and> set_IL il1' \<inter> set_IL il2' = {} \<and> (\<forall>i < length Bs. distinct (Bs ! i))"
  let ?P2 = "\<lambda>((il1',il2'),k). k \<le> (length (list il2')) * (?C)"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((il1,il2),k). (list il1) \<noteq> [])"
  let ?c = "\<lambda>(il12,k). (step2_IL Bs il12, k + T_test2_IL il12 + T_step2_IL Bs il12)"


  have init: "?P ((il1,il2), k)" using assms by auto

  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y
    using step2_IL_inv1_il[of a Bs b] step2_IL_inv2_il[of a Bs b] step2_IL_wf2_il[of a Bs b] 
      step2_IL_wf_il[of a Bs b] length_step2_IL1_il[of a Bs b] length_step2_IL2_il[of a Bs b] step2_IL_dist[of a b Bs]
    by (smt (verit) case_prodI2' case_prod_conv wf_Bs(1)) 
  
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_step2_IL Bs (a, b) \<le> ?C" using T_step2_IL_bound by auto
    have b_ne: "froms b \<noteq> []" using assms
      by force
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "step2_IL Bs (a,b) = (a', b')" by auto
    then have "length (list b') = Suc (length (list b))" using length_step2_IL_inc[of a b Bs a' b'] assms b_ne by auto
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

  then have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P (?c ((a,b), y)))" for a b y using P1 by auto
  then show "k' \<le> (length (list il2')) * ?C"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((il1,il2),k)", where t="((il1',il2'), k')"] assms init
    by auto (simp add: T_while_option2_def test2_IL_def split_def) 
qed

lemma T_steps2_IL_bound: assumes
  "wf_bins1 (map set Bs)" "wf1_IL' Bs il1" "wf1_IL' Bs il2" "inv_IL il1" "inv_IL il2"
  "\<forall>i < length Bs. distinct (Bs ! i)"  "set_IL il1 \<inter> set_IL il2 = {}" 
  "length (froms il1) = Suc (length Bs)" "length (froms il2) = Suc (length Bs)"
shows "T_steps2_IL Bs (il1, il2) \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K)"
proof-
  obtain il1' il2' k' where P: "T_steps2_IL2 Bs (il1,il2) 0 = Some ((il1',il2'),k') \<and> steps2_IL Bs (il1, il2) = Some (il1', il2')"
    using assms Close2_L_NF T_while_option2_if_T_while_option unfolding steps2_IL_def by metis
  have "wf1_IL' Bs il2' \<and> inv_IL il2'"
    using P assms(1,2,3,4,5,8,9) steps2_IL_wf2 steps2_IL_inv2 by blast
  then have 1: "length (list il2') \<le> L * Suc K * Suc (length Bs)"
    using card_wf_bin1 distinct_card[of "list il2'"] inv_IL1
    by fastforce
  have "k' \<le> (length (list il2')) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K)"
    using Tsteps2_IL2[of Bs il1 il2 0] assms P by simp
  also have "... \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K)"
    using P mult_le_mono1[OF 1] by auto
  finally show ?thesis using P by (simp add: T_while_option_def)
qed

lemma T_close2_IL_bound: 
  assumes "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)"  "wf1_IL' Bs il" "inv_IL il" "length (froms il) = Suc (length Bs)"
shows "T_close2_IL Bs il \<le> (L * Suc K * Suc (length Bs)) * (L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (length Bs) +
       3 * Suc (length Bs) + 2 * L * Suc K + 7 + Suc K) + 2 * Suc (length Bs)"
proof-
  obtain il1' il2' where "steps2_IL Bs (il, empty_IL (length Bs)) = Some (il1', il2')"
    using Close2_L_NF empty_inv assms(1,3,4,5) wf1_empty_IL length_empty_IL by blast
  then show ?thesis using T_steps2_IL_bound[of Bs il "empty_IL (length Bs)"] empty_inv[of "length Bs"] set_empty_IL 
        wf1_empty_IL length_empty_IL assms T_length[of Bs] by (auto simp del: T_empty_IL.simps)
qed

lemma wf1_Init_L: "wf_bin1 0 (set Init_L)"
  by (simp add: Init_L_eq_Init wf_bin1_Init)

lemma wf1_Scan_L: "k < length w \<Longrightarrow> wf_bin1 k (set as) \<Longrightarrow> wf_bin1 (Suc k) (set (Scan_L k as))"
  using wf_bin1_Scan
  by (simp add: Scan_L_eq_Scan)

lemma wf_Scan_L: "k < length w \<Longrightarrow> wf_bin k (set as) \<Longrightarrow> wf_bin k (set (Scan_L k as))"
  by (auto simp add: Scan_L_def mv_dot_def next_sym_def wf_item_def is_complete_def)

lemma length_Init_L: "length Init_L \<le> L"
  by (auto simp add: Init_L_def L_def)

lemma length_Scan_L: "length (Scan_L k as) \<le> length as"
  by (auto simp add: Scan_L_def)
                                                
lemma wf1_IL_list: "wf_bin1 k (set as) \<Longrightarrow> wf1_IL k (IL_list k as)"
  using set_IL_list forall_from_Suc by auto

lemma distinct_close2: 
  assumes "wf_bins1 (map set Bs)" "wf1_IL' Bs il" "inv_IL il" "length (froms il) = Suc (length Bs)"
  shows "distinct (close2_IL Bs il)"
proof-
  obtain il1 il2 where "steps2_IL Bs (il, empty_IL (length Bs)) = Some (il1, il2)"
    using empty_inv wf1_empty_IL length_empty_IL Close2_L_NF assms by blast
  then show ?thesis using steps2_IL_inv2[of " empty_IL (length Bs)"] assms length_empty_IL
      inv_IL1[of "il2"] close2_IL_def by (auto simp add: close2_IL_def empty_inv)
qed

lemma distinct_bins_IL: "k \<le> length w \<Longrightarrow> i < Suc k \<Longrightarrow> distinct ((bins_IL k) ! i)"
proof(induction k arbitrary: i)
  case 0
  then show ?case using distinct_close2[of "[]" "IL_list 0 Init_L"] length_IL_list
    using IL_list_inv[OF forall_from_Suc] set_IL_list wf1_Init_L wf_bins1_def wf1_IL_list by auto
next
  case (Suc k)
  then have 1: "i < Suc k \<longrightarrow> distinct (bins_IL (Suc k) ! i)" using length_bins_IL by (auto simp add: Let_def nth_append_left)

  have 2: "wf_bins1 (map set (bins_IL k))" using "Suc.prems"(1)
    by (simp add: bins_IL_eq_bins wf_bins1_bins)
  have "wf_bin1 k (set (last (bins_IL k)))" using "Suc.prems"(1)
    by (metis Suc_leD Zero_not_Suc bins_IL_eq_bins last_map length_bins_IL list.size(3) wf_bin1_last)
  then have 3: "wf_bin1 (Suc k) (set (Scan_L k (last (bins_IL k))))"
    using Scan_L_eq_Scan Suc.prems(1) wf_bin1_Scan by auto
  have 5: "distinct (close2_IL (bins_IL k) (IL_list (Suc k) (Scan_L k (last (bins_IL k)))))" using 2 3 Suc distinct_close2
    using IL_list_inv[OF forall_from_Suc] length_bins_IL wf1_IL_list by auto

  have "\<not> i < Suc k \<longrightarrow> i = Suc k" using Suc by auto
  then show ?case using 1 5 using nth_append_length[of "bins_IL k"] length_bins_IL by (auto simp add: Let_def)
qed

(*(k+2)^3 * ((?a) + (?b))
    + 7*k + 18 
    + (k+2)^2 * ?a
    + Suc (Suc k) * ?b*)

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
    by (simp add: add_mult_distrib)
  show ?thesis using 1 2 by (simp add: add_mult_distrib add_mult_distrib2)
qed

lemma T_bins_IL_bound: "k \<le> length w \<Longrightarrow> T_bins_IL k 
  \<le> (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)))"
proof (induction k)
  case 0
  have "\<forall>x \<in> set (Init_L). from x = 0" using wf1_Init_L by (auto simp add: wf_bin1_def wf_item1_def wf_item_def)
  then have 1: "T_union_LIL Init_L (empty_IL 0) \<le> length Init_L * (3 * T_nth_IL (0) + L * Suc K + 2) + 1" 
    using T_union_LIL_wf[of "empty_IL 0"] 0 empty_inv wf1_empty_IL wf1_Init_L by (auto simp add:)
  have "length (froms (IL_list 0 Init_L)) = 1" 
    using length_IL_list by simp
  then have "T_close2_IL [] (IL_list 0 Init_L) \<le> (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 7 + Suc K) + 2"
    using 0 T_close2_IL_bound[of "[]" "(IL_list 0 Init_L)"] wf1_Init_L wf1_IL_list
        IL_list_inv[OF forall_from_Suc] by (auto simp add: wf_bins1_def simp del: T_close2_IL.simps)
  then have "T_bins_IL 0 \<le> length Init_L * (3 * T_nth_IL (0) + L * Suc K + 2) + 1 + (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 7 + Suc K) + 4" 
    unfolding T_bins_IL.simps T_IL_list.simps T_empty_IL.simps 
    using 1 by (auto)
  also have "... =  length Init_L * (3 * T_nth_IL (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 7 + Suc K) + 5" by auto
  also have "... \<le> L * (3 * T_nth_IL (0) + L * Suc K + 2) + (L * Suc K) * (L * Suc K * (7 * T_nth_IL (0) + 3 * L * Suc K + 7 + 2 * (K + 2)) + 7 * T_nth_IL (0) +
       3 * Suc (0) + 2 * L * Suc K + 7 + Suc K) + 5"
    using length_Init_L
    using add_le_mono1 mult_le_cancel2 by presburger
  also have "... \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 9 + Suc K)))"
    by (simp add: add_mult_distrib add_mult_distrib2)
  finally have 2: "T_bins_IL 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 9 + Suc K)))".

  have "7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2)
      \<le> 7 * T_nth_IL (1) + 3* L * Suc K + 10 + 2 * (K + 2)" using mono_nth by (auto simp add: monoD)
  then have 3: "Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (0) + 3* L * Suc K + 10 + 2 * (K + 2))
    \<le> Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (1) + 3* L * Suc K + 10 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 9 + Suc K \<le> 2 * (K + 2) + 10 * T_nth_IL (1) + 3* L * Suc K + 9 + Suc K"
    using mono_nth by (auto simp add: monoD)
  then have 4: "(Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (0) + 3* L * Suc K + 9 + Suc K)) \<le> (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (1) + 3* L * Suc K + 9 + Suc K))"
    using mult_le_mono2 by blast

  have "T_bins_IL 0 \<le> 8 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (1) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (1) + 3* L * Suc K + 9 + Suc K)))"
    using 2 3 4 by simp

  then show ?case by (simp add: numeral_eq_Suc)
next
  case (Suc k)
  have 1: "T_length (bins_IL k) = k + 2"
    by (simp add: length_bins_IL T_length)

  have 2: "T_last (bins_IL k) = Suc k"
    by (metis T_last Zero_not_Suc length_bins_IL list.size(3))

  have wf_last: "wf_bin1 k (set (last (bins_IL k)))" using Suc wf_bin1_last
    by (metis Suc_leD Zero_not_Suc bins_IL_eq_bins length_bins_IL list.size(3) last_map)
  then have length_last: "length (last (bins_IL k)) \<le> L * Suc K * Suc k"
    using distinct_bins_IL card_wf_bin1 last_conv_nth length_bins_IL
    by (metis Suc.prems(1) Suc_leD diff_Suc_1 distinct_card length_greater_0_conv lessI zero_less_Suc)
  have "T_Scan_L k (last (bins_IL k)) \<le> k + 2 * (K + 2) * length (last (bins_IL k)) + 3"
    using T_Scan_L_bound Suc w_def wf_last by auto
  also have "... \<le> k + 2 * (K + 2) * L * Suc K * Suc k + 3"
    using length_last
    by (metis (no_types, lifting) add_le_mono1 mult.assoc mult_le_mono2 nat_add_left_cancel_le)
  also have "... = k + L * Suc K * Suc k * 2 * (K + 2) + 3"
    by (metis (no_types, lifting) mult.commute mult.left_commute)
  finally have 3: "T_Scan_L k (last (bins_IL k)) \<le> k + L * Suc K * Suc k * 2 * (K + 2) + 3".

  have wf_Scan: "wf_bin1 (Suc k) (set (Scan_L k (last (bins_IL k))))"
    using wf_last wf_Scan_L Suc wf_bin1_def wf_item1_def
    by (meson Suc_le_eq wf1_Scan_L)
  then have from_Scan: "\<forall>a \<in> set (Scan_L k (last (bins_IL k))). from a < Suc (Suc k)"
    using forall_from_Suc by blast
  have length_Scan: "length (Scan_L k (last (bins_IL k))) \<le> L * Suc K * Suc k"
    using length_Scan_L length_last dual_order.trans by blast
  have "T_IL_list (length (bins_IL k)) (Scan_L k (last (bins_IL k))) \<le> k+2 + length (Scan_L k (last (bins_IL k))) * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + 1"
    using T_union_LIL_wf[of "(empty_IL (Suc k))" "Scan_L k (last (bins_IL k))"] empty_inv[of "Suc k"] wf1_empty_IL wf_Scan Suc
    length_IL_list from_Scan by (auto simp add: length_bins_IL wf_bin1_def wf_item1_def simp del: T_empty_IL.simps)
  also have "... \<le> k+2 + L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + 1" using length_Scan mult_le_mono1[OF length_Scan]
    using add_le_mono1 nat_add_left_cancel_le by presburger
  finally have 4: "T_IL_list (length (bins_IL k)) (Scan_L k (last (bins_IL k))) \<le> L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + k + 3" by linarith

  have wf_bins_IL: "wf_bins1 (map set (bins_IL k))" using wf_bins1_bins bins_IL_eq_bins Suc by auto
  have wf_IL_list: "wf1_IL (Suc k) (IL_list (length (bins_IL k)) (Scan_L k (last (bins_IL k))))"
    using set_IL_list[OF forall_from_Suc, of "Suc k" "Scan_L k (last (bins_IL k))"] 
    using Suc.prems(1) wf1_Scan_L[of "k" "last (bins_IL k)"] wf_last length_bins_IL by auto
  have leng_IL_list: "length (froms (IL_list (length (bins_IL k)) (Scan_L k (last (bins_IL k))))) = k+2"
    by (auto simp add: length_bins_IL)
  have 5: "T_close2_IL (bins_IL k) (IL_list (length (bins_IL k)) (Scan_L k (last (bins_IL k))))  
            \<le> (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) + 2* Suc (Suc k)"
    using T_close2_IL_bound[of "bins_IL k" "IL_list (length (bins_IL k)) (Scan_L k (last (bins_IL k)))"] 
      wf_bins_IL wf_Scan Suc distinct_bins_IL wf_IL_list IL_list_inv[OF forall_from_Suc] leng_IL_list 
    by (auto simp add: length_bins_IL simp del: T_close2_IL.simps)

  have 6: "T_append (bins_IL k) [close2_IL (bins_IL k) (IL_list (length (bins_IL k)) (Scan_L k (last (bins_IL k))))] = k+2"
    by (auto simp add: length_bins_IL)

  have "L * Suc K * Suc (Suc k) * 2 * Suc (Suc k) \<le>  L * Suc K * L * Suc K * Suc (Suc k) * 2* Suc (Suc k)" using le_square[of "L * Suc K"]
    by (metis (no_types, lifting) mult.assoc mult_le_mono1)
  then have test': "L * Suc K * Suc (Suc k) * 3 * Suc (Suc k) \<le> L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * 3"
    by (auto simp add: algebra_simps)
  have test'': "L \<le> Suc L" by simp

  have "T_bins_IL (Suc k) \<le> T_bins_IL k + k + 2 + Suc k + k + L * Suc K * Suc k * 2 * (K + 2) + 3
        + L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2) + k + 3
        + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K) + 2* Suc (Suc k)
      + k + 2 + 1" unfolding T_bins_IL.simps Let_def using 1 2 3 4 5 6 by presburger

  
  
  also have "... = T_bins_IL k + 7*k + 16 + L * Suc K * Suc k * 2 * (K + 2)
            + L * Suc K * Suc k * (3 * T_nth_IL (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    by simp

  also have "... = T_bins_IL k + 7*k + 16
            + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
            + (L * Suc K * Suc (Suc k)) * (L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
      + 7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2 by simp

  also have "... = T_bins_IL k + 7*k + 16 + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3 * Suc (Suc k) + 2* L * Suc K + 7 + Suc K)"
    by (metis (no_types, opaque_lifting) distrib_left group_cancel.add1 mult.assoc)

  also have "... = T_bins_IL k + 7*k + 16 + L * Suc K * Suc k * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * 3 * Suc (Suc k)
    + L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] by simp

  also have "... \<le>  T_bins_IL k + 7*k + 16 + L * Suc K * (Suc (Suc k)) * (2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2)
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 7 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * 3
    + L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 2* L * Suc K + 7 + Suc K)"
    using mult_mono_mix[of "Suc k" "(Suc (Suc k))" "L * Suc K" "2 * (K + 2) + 3 * T_nth_IL (Suc k) + L * Suc K + 2"] test' by presburger

  also have "... \<le> T_bins_IL k + 7*k + 16
    + L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))
    + L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)"
    using add_mult_distrib2[of "(L * Suc K * Suc (Suc k))"] 
          add_mult_distrib2[of "L * Suc K * Suc (Suc k) * L * Suc K * Suc (Suc k)"] by simp

  also have "... = T_bins_IL k + 7*k + 16 
    + L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (metis (no_types, opaque_lifting) mult.assoc)

  also have "... \<le> T_bins_IL k + 7*k + 16 
    + Suc L * (Suc K * Suc (Suc k) * L * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + Suc L * (Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K))" 
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_IL k + 7*k + 16 
    + L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)"
    by (metis (no_types, lifting) dual_order.refl mult.commute mult.left_commute mult.assoc)
  also have "... \<le> T_bins_IL k + 7*k + 16 
    + Suc L * (Suc L * Suc K * Suc (Suc k) * (Suc K * Suc (Suc k) * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))))
    + Suc L * Suc K * Suc (Suc k) * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)"
    using mult_le_mono1 by auto
  also have "... \<le> T_bins_IL k + 7*k + 16 
    + Suc (Suc k) * Suc (Suc k) * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (smt (verit, ccfv_threshold) mult.commute mult.left_commute verit_comp_simplify1(2))
  also have "... \<le> T_bins_IL k + 7*k + 16 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K))"
    by (metis add_2_eq_Suc' le_refl power2_eq_square)
  finally have short: "T_bins_IL (Suc k) \<le> T_bins_IL k + 7*k + 16 
    + (k+2)^2 * (Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)))
    + Suc (Suc k) * (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K))".

  let ?a = "Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))"
  let ?b = "Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)"

  have ff: "T_nth_IL (Suc k) \<le> T_nth_IL (Suc (Suc k))" using mono_nth
    by (simp add: monoD)
  then have "(7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2)) \<le> (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))"
    by auto
  then have a1: "?a \<le> Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))"
    using mult_le_mono2 by blast
  have "2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K \<le> 2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K"
    using ff by auto
  then have b1: "?b \<le> Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)"
    using mult_le_mono2 by blast

  have "T_bins_IL (Suc k) \<le> (k+2)^3 * ((?a) + (?b))
    + 7*k + 16 
    + (k+2)^2 * ?a
    + Suc (Suc k) * ?b" using short Suc by simp

  also have "... \<le> (k+3)^3 * ((?a) + (?b))"
    using bound_help[of ?a ?b k] by simp

  also have "... \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)))"
    using a1 b1 by simp
  finally have "T_bins_IL (Suc k)
  \<le> (k+3)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc (Suc k)) + 3* L * Suc K + 9 + Suc K)))".

  then show ?case
    by (metis add_Suc_shift eval_nat_numeral(3))
qed

subsubsection \<open>Final nice time bounds\<close>

definition C1 where "C1 = 28 * (L+1)^3 * (K+1)^3"
definition C2 where "C2 = 17 * (L+1)^2 * (K+1)^2"

corollary nice_T_bins_IL_bound: 
  assumes "k \<le> length w" 
  shows "T_bins_IL k \<le> C1 *(k+2)^3 + C2 * (k+2)^3 * T_nth_IL (k+1)"
proof-
  have "T_bins_IL k \<le> (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (7 * T_nth_IL (Suc k) + 3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 10 * T_nth_IL (Suc k) + 3* L * Suc K + 9 + Suc K)))"
    using T_bins_IL_bound assms by auto
  also have "... = (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * 7 * T_nth_IL (k+1) + Suc L * Suc K * 10 * T_nth_IL (k+1)) 
    + (k+2)^3 * ((Suc L * Suc K * Suc L * Suc K * (3* L * Suc K + 10 + 2 * (K + 2))) + (Suc L * Suc K * (2 * (K + 2) + 3* L * Suc K + 9 + Suc K)))"
    by (auto simp add: algebra_simps)
  also have "... \<le> (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * 17 * T_nth_IL (k+1))
                  + (k+2)^3 * (Suc L * Suc K * Suc L * Suc K * (6* L * Suc K + 18 + 5 * (K + 2)))"
    by (auto simp add: algebra_simps)
  also have "... \<le> 17 * (L+1) * (L+1) * (K+1) * (K+1) * (k+2)^3 * T_nth_IL (k+1)
                  + 28 * (L+1) * (L+1) * (L+1) * (K+1) * (K+1) * (K+1) * (k+2)^3"
    by (auto simp add: algebra_simps)
  also have "... = 17 * (L+1)^2 * (K+1)^2 * (k+2)^3 * T_nth_IL (k+1)
                  + 28 * (L+1)^3 * (K+1)^3 * (k+2)^3"
    by (auto simp add: monoid_mult_class.power2_eq_square monoid_mult_class.power3_eq_cube algebra_simps)
  finally show ?thesis by (auto simp add: C1_def C2_def)
qed


lemma T_final_bound: "prod x \<in> set ps \<Longrightarrow> T_is_final x \<le> Suc K"
  by (auto simp add: T_length prod_length_bound)

lemma T_recognized_bound: "wf_bin k (set as) \<Longrightarrow> T_recognized_L as \<le> Suc (length as) * (K+2)"
proof (induction as)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then show ?case using T_final_bound[of a] by (auto simp del: T_is_final.simps simp add: wf_item_def)
qed

definition C1' where "C1' = 30 * (L+1)^3 * (K+1)^3"

lemma T_earley_recognized_nice:
  shows "T_earley_recognized1 w0 \<le> C1' *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1)"
proof-
  have wf_last: "wf_bin1 (length w) (set (last (bins_IL (length w))))" using wf_bin1_last
    by (metis bins_IL_eq_bins length_bins_IL lessI less_Suc_eq_le list.size(3) not_less_zero last_map)
  then have length_last: "length (last (bins_IL (length w))) \<le> L * Suc K * Suc (length w)"
    using distinct_bins_IL card_wf_bin1 last_conv_nth length_bins_IL distinct_card
    by (metis diff_Suc_1 interval_class.less_imp_less_eq_dec lessI list.size(3) nat.distinct(1))
  have "T_recognized_L (last (bins_IL (length w))) \<le> Suc (length (last (bins_IL (length w)))) * (K+2)"
    using wf_last wf_bin1_def wf_item1_def T_recognized_bound by metis
  also have "... \<le> Suc (L * Suc K * Suc (length w)) * (K+2)" using length_last
    using Suc_le_mono mult_le_mono1 by presburger
  finally have 1: "T_recognized_L (last (bins_IL (length w))) \<le> Suc (L * Suc K * Suc (length w)) * (K+2)".

  have 2: "T_bins_IL (length w) \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1)"
    using nice_T_bins_IL_bound by simp

  have 3: "T_last (bins_IL (length w)) = Suc (length w)"
    using T_last length_bins_IL
    by (metis Zero_not_Suc list.size(3))

  have 4: "T_length w = Suc (length w)"
    using T_length by simp

  have "T_earley_recognized1 w0 \<le> T_bins_IL (length w) + T_last (bins_IL (length w)) + T_recognized_L(last (bins_IL (length w))) + T_length w"
    by simp
  also have "... \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1) + Suc (length w) + Suc (length w) + Suc (L * Suc K * Suc (length w)) * (K+2)" 
    using 1 2 3 4 by linarith
  also have "... \<le> C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1) + 2 * (L+1) * (L+1) * (L+1) * (K+1) * (K+1) * (K+1) * ((length w)+2) * ((length w)+2) * ((length w)+2)"
    by (simp add: algebra_simps)
  also have "... = C1 *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1) + 2 * (L+1)^3 * (K+1)^3 * ((length w)+2)^3"
    by (simp add: monoid_mult_class.power3_eq_cube algebra_simps)
  also have "... = C1' *((length w)+2)^3 + C2 * ((length w)+2)^3 * T_nth_IL ((length w)+1)"
    using C1_def C1'_def by auto
  finally show ?thesis .
qed

end

(*unused_thms*)

end