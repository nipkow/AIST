(*
Initial abstract development of Earley's recognizer.
Author: Tobias Nipkow, based on earlier work by Martin Rau.
*)

(*
TODO:
- represent dotted items w/o index; will lower complexity
*)

section \<open>Earley's Recognizer: Initial Development\<close>
theory Earley
imports
  "Context_Free_Grammar.Context_Free_Grammar"
  "HOL-Library.While_Combinator"
begin

subsection \<open>Slices\<close>

fun slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice _ _ [] = []"
| "slice _ 0 (x#xs) = []"
| "slice 0 (Suc b) (x#xs) = x # slice 0 b xs"
| "slice (Suc a) (Suc b) (x#xs) = slice a b xs"

lemma slice_drop_take:
  "slice a b xs = drop a (take b xs)"
  by (induction a b xs rule: slice.induct) auto

lemma slice_append_aux:
  "Suc b \<le> c \<Longrightarrow> slice (Suc b) c (x # xs) = slice b (c-1) xs"
  using Suc_le_D by fastforce

lemma slice_concat:
  "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> slice a b xs @ slice b c xs = slice a c xs"
proof (induction a b xs arbitrary: c rule: slice.induct)
  case (3 b x xs)
  thus ?case
      using Suc_le_D by(fastforce simp: slice_append_aux)
qed (auto simp: slice_append_aux)

lemma slice_concat_Ex:
  "a \<le> c \<Longrightarrow> slice a c xs = ys @ zs \<Longrightarrow> \<exists>b. ys = slice a b xs \<and> zs = slice b c xs \<and> a \<le> b \<and> b \<le> c"
proof (induction a c xs arbitrary: ys zs rule: slice.induct)
  case (3 b x xs)
  show ?case
  proof (cases ys)
    case Nil
    then obtain zs' where "x # slice 0 b xs = x # zs'" "x # zs' = zs"
      using "3.prems"(2) by auto
    thus ?thesis
      using Nil by force
  next
    case (Cons y ys')
    then obtain ys' where "x # slice 0 b xs = x # ys' @ zs" "x # ys' = ys"
      using "3.prems"(2) by auto
    thus ?thesis
      using "3.IH"[of ys' zs] by force
  qed
next
  case (4 a b x xs)
  thus ?case
    by (auto, metis slice.simps(4) Suc_le_mono)
qed auto

lemma slice_nth:
  "a < length xs \<Longrightarrow> slice a (a+1) xs = [xs!a]"
  unfolding slice_drop_take
  by (metis Cons_nth_drop_Suc One_nat_def diff_add_inverse drop_take take_Suc_Cons take_eq_Nil)

lemma slice_append_nth:
  "a \<le> b \<Longrightarrow> b < length xs \<Longrightarrow> slice a b xs @ [xs!b] = slice a (b+1) xs"
  by (metis le_add1 slice_concat slice_nth)

lemma slice_empty:
  "b \<le> a \<Longrightarrow> slice a b xs = []"
  by (simp add: slice_drop_take)

lemma slice_id[simp]:
  "slice 0 (length xs) xs = xs"
  by (simp add: slice_drop_take)

lemma slice_singleton:
  "b \<le> length xs \<Longrightarrow> [x] = slice a b xs \<Longrightarrow> b = a + 1"
  by (induction a b xs rule: slice.induct) (auto simp: slice_drop_take)

subsection \<open>Earley recognizer: Abstract inductive definition\<close>

subsubsection \<open>Earley items\<close>

abbreviation lhs :: "('n,'t) prod \<Rightarrow> 'n" where
  "lhs \<equiv> fst"

definition rhs :: "('n,'t) prod \<Rightarrow> ('n,'t) syms" where
  "rhs p = snd p"

datatype ('n,'t) item = 
  Item (prod: "('n,'t) prod") (dot : nat) ("from" : nat)

definition \<alpha> :: "('n,'t) item \<Rightarrow> ('n,'t) syms" where
  "\<alpha> x = take (dot x) (rhs(prod x))"

definition \<beta> :: "('n,'t) item \<Rightarrow> ('n,'t) syms" where 
  "\<beta> x = drop (dot x) (rhs(prod x))"

definition mv_dot :: "('n,'t) item \<Rightarrow> ('n,'t) item" where
"mv_dot x \<equiv> Item (prod x) (dot x + 1) (from x)"

definition is_complete :: "('n,'t) item \<Rightarrow> bool" where
  "is_complete x = (dot x \<ge> length (rhs(prod x)))"

definition next_sym :: "('n,'t) item \<Rightarrow> ('n,'t) sym \<Rightarrow> bool" where
  "next_sym x s = (if is_complete x then False else s = rhs(prod x) ! dot x)"

lemmas item_defs = \<alpha>_def \<beta>_def rhs_def

(* Unclear if separating out \<open>Earley_G\<close> helps much.
   It is used in the def of \<open>earley_recognized1\<close>
*)
locale Earley_G =
fixes ps :: "('n,'t) prods"
fixes S :: 'n
begin

abbreviation "P \<equiv> set ps"

end

locale Earley_Gw = Earley_G
  where ps = ps and S = S for ps :: "('n,'t) prods" and S :: 'n +
fixes w0 :: "'t list"
begin

definition w :: "('n,'t)syms" where "w \<equiv> map Tm w0"

definition is_final :: "('n,'t) item \<Rightarrow> bool" where
  "is_final x =
    (lhs(prod x) = S \<and>
    from x = 0 \<and>
    is_complete x)"

definition recognized :: "(nat \<times> ('n,'t) item) set \<Rightarrow> bool" where
  "recognized I \<equiv> \<exists>(k,x) \<in> I. is_final x \<and> k = length w"

definition Init :: "('n,'t) item set" where
  "Init = { Item r 0 0 | r. r \<in> P \<and> lhs r = (S) }"

definition Predict :: "nat \<Rightarrow> ('n,'t) item \<Rightarrow> ('n,'t) item set" where
  "Predict k x = { Item r 0 k | r. r \<in> P \<and> next_sym x (Nt(lhs r)) }"

(* TODO use Complete and Scan? *)
inductive_set Earley :: "(nat \<times>('n,'t) item) set" where
    Init: "x \<in> Init \<Longrightarrow> (0, x) \<in> Earley"
  | Scan: "\<lbrakk> (j, x) \<in> Earley;  j < length w;  next_sym x (w!j) \<rbrakk> \<Longrightarrow>
      (j+1, mv_dot x) \<in> Earley"
  | Predict: "\<lbrakk> (k,x) \<in> Earley; x' \<in> Predict k x \<rbrakk> \<Longrightarrow>
      (k,x') \<in> Earley"
  | Complete: "\<lbrakk> (k,y) \<in> Earley;  is_complete y;  (from y,x) \<in> Earley;
      next_sym x (Nt(lhs(prod y))) \<rbrakk> \<Longrightarrow>
        (k, mv_dot x) \<in> Earley"

definition \<E> :: "nat \<Rightarrow> ('n,'t) item set" where
"\<E> i = {x. (i,x) \<in> Earley}"

lemma Earley_eq_\<E>: "(i,x) \<in> Earley \<longleftrightarrow> x \<in> \<E> i"
by(simp add: \<E>_def)

definition accepted :: "bool" where
  "accepted = (\<exists>x \<in> \<E> (length w). is_final x)"


subsubsection \<open>Well-formedness\<close>

definition wf_item :: "nat \<Rightarrow> ('n,'t) item \<Rightarrow> bool" where 
  "wf_item k x =
    (prod x \<in> P \<and> 
    dot x \<le> length (rhs(prod x)) \<and>
    from x \<le> k \<and> 
    k \<le> length w)"

lemma wf_Init:
  assumes "x \<in> Init"
  shows "wf_item 0 x"
  using assms unfolding Init_def wf_item_def by auto

lemma wf_Scan:
  assumes "wf_item j x" "w!j = a" "j < length w" "next_sym x a"
  shows "wf_item (j+1) (mv_dot x)"
  using assms unfolding wf_item_def mv_dot_def
  by (auto simp: item_defs is_complete_def next_sym_def split: if_splits)

lemma wf_Predict:
  "\<lbrakk> wf_item k x; x' \<in> Predict k x \<rbrakk> \<Longrightarrow> wf_item k x'"
unfolding wf_item_def Predict_def by (auto)

lemma wf_Complete:
  assumes "wf_item j x" "j = from y" "wf_item k y"
  assumes "is_complete y" "next_sym x (Nt(lhs(prod y)))"
  shows "wf_item k (mv_dot x)"
  using assms unfolding wf_item_def is_complete_def next_sym_def mv_dot_def
  by (auto split: if_splits)

lemma wf_Earley:
  assumes "(k,x) \<in> Earley"
  shows "wf_item k x"
  using assms wf_Init wf_Scan wf_Predict wf_Complete
  by (induction rule: Earley.induct) fast+

lemmas wf_EarleyS = wf_Earley[unfolded Earley_eq_\<E>]

subsubsection \<open>Soundness\<close>

definition sound_item :: "nat \<Rightarrow> ('n,'t) item \<Rightarrow> bool" where
  "sound_item k x = (P \<turnstile> \<alpha> x \<Rightarrow>* slice (from x) k w)"

lemma sound_Init:
  assumes "x \<in> Init"
  shows "sound_item 0 x"
proof -
  have "(lhs(prod x), rhs(prod x)) \<in> P"
    using assms by (auto simp add: Init_def item_defs)
  hence "P \<turnstile> [Nt(lhs(prod x))] \<Rightarrow>* rhs(prod x)"
    using derive_singleton by blast
  thus ?thesis
    using assms unfolding Init_def sound_item_def by (auto simp add: \<alpha>_def slice_empty)
qed

lemma sound_Scan:
  assumes "x = Item r d i" "wf_item j x" "sound_item j x"
  assumes "w!j = a" "j < length w" "next_sym x a"
  shows "sound_item (j+1) (Item r (d+1) i)"
proof -
  define x' where [simp]: "x' = Item r (d+1) i"
  have *: "\<alpha> x' = \<alpha> x @ [w!j]"
    using assms(1,4,5,6) by (auto simp: item_defs next_sym_def is_complete_def take_Suc_conv_app_nth split: if_splits)
  have "slice i (j+1) w = slice i j w @ [w!j]"
    using * assms(1,2,5) slice_append_nth[symmetric, of i j w] by (auto simp: wf_item_def)
  moreover have "P \<turnstile> \<alpha> x \<Rightarrow>* slice i j w"
    using assms(1,3) by (simp add: sound_item_def)
  ultimately show ?thesis
    using * by (simp add: derives_append sound_item_def)
qed

lemma sound_Predict:
  assumes "wf_item k x" "sound_item k x"
  assumes "x' \<in> Predict k x"
  shows "sound_item k x'"
  using assms slice_empty unfolding Predict_def sound_item_def item_defs by fastforce

lemma sound_Complete:
  assumes "x = Item r\<^sub>x d\<^sub>x i" "wf_item j x" "sound_item j x"
  assumes "y = Item r\<^sub>y d\<^sub>y j" "wf_item k y" "sound_item k y"
  assumes "is_complete y" "next_sym x (Nt(lhs(prod y)))"
  shows "sound_item k (Item r\<^sub>x (d\<^sub>x + 1) i)"
proof -
  have *: "P \<turnstile> [Nt(lhs r\<^sub>y)] \<Rightarrow> rhs r\<^sub>y"
    using assms(4,5)unfolding rhs_def wf_item_def by (simp add: derive_singleton)
  moreover have *: "P \<turnstile> rhs r\<^sub>y \<Rightarrow>* slice j k w"
    using assms(4,6,7) by (auto simp: sound_item_def is_complete_def item_defs)
  ultimately have "P \<turnstile> [Nt(lhs r\<^sub>y)] \<Rightarrow>* slice j k w"
    by simp
  moreover have "P \<turnstile> take d\<^sub>x (rhs r\<^sub>x) \<Rightarrow>* slice i j w"
    using assms(1,3) by (auto simp: sound_item_def \<alpha>_def)
  moreover have "rhs r\<^sub>x ! d\<^sub>x = Nt(lhs r\<^sub>y)" and "d\<^sub>x < length(rhs r\<^sub>x)"
    using assms(1,4,8) unfolding next_sym_def is_complete_def by(auto split: if_splits)
  ultimately have "P \<turnstile> take (d\<^sub>x+1) (rhs r\<^sub>x) \<Rightarrow>* slice i j w @ slice j k w"
    using assms(1,8) apply(simp add: take_Suc_conv_app_nth)
    using derives_append_decomp by blast
  moreover have "i \<le> j"  "j \<le> k"
    using assms(1,2,4,5) by (simp_all add: wf_item_def)
  ultimately show ?thesis
    unfolding sound_item_def \<alpha>_def by (simp add: slice_concat)
qed

lemma sound_Earley:
  assumes "(k,x) \<in> Earley"
  shows "sound_item k x"
  using assms
proof (induction rule: Earley.induct)
  case (Init r)
  thus ?case
    using sound_Init by blast
next
  case Scan
  thus ?case
    using wf_Earley sound_Scan unfolding mv_dot_def by auto
next
  case Predict
  thus ?case using wf_Earley sound_Predict by blast
next
  case (Complete)
  thus ?case
    using sound_Complete wf_Earley unfolding mv_dot_def by (metis item.collapse)
qed

theorem soundness_Earley:
assumes "recognized Earley" shows "P \<turnstile> [Nt S] \<Rightarrow>* w"
proof -
  obtain x where *: "(length w,x) \<in> Earley" and "is_final x"
    using assms recognized_def by auto
  hence "prod x \<in> P" "lhs(prod x) = S" "from x = 0" "dot x \<ge> length (rhs(prod x))"
    "\<alpha> x = rhs(prod x)"
    using wf_Earley[OF *] unfolding is_final_def is_complete_def wf_item_def \<alpha>_def by auto
  with sound_Earley[OF *] derives_Cons_rule[of "lhs(prod x)" "rhs(prod x)"]
  show ?thesis
    by(auto simp add: sound_item_def rhs_def)
qed

corollary accpted_sound: "accepted \<Longrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w" (* used in Paper *)
using soundness_Earley unfolding \<E>_def accepted_def recognized_def by blast


subsubsection \<open>Completeness\<close>

text \<open>A canonical proof:
 by induction on the length of the derivation
 with a nested induction on the length of the right-hand side of the production.\<close>

lemma Earley_complete_induction:
  "\<lbrakk>j \<le> k; k \<le> length w; x = Item (A,\<gamma>) d i; (j,x) \<in> Earley;
    P \<turnstile> \<beta> x \<Rightarrow>(n) slice j k w \<rbrakk> \<Longrightarrow> (k, Item (A,\<gamma>) (length \<gamma>) i) \<in> Earley"
proof (induction n arbitrary: x d i j k A \<gamma> rule: less_induct)
  case (less n)
  have "\<exists>m \<le> n. P \<turnstile> \<beta> x \<Rightarrow>(m) slice j k w" using less.prems(5) by auto
  from less.prems(1,3,4) this show ?case
  proof (induction "\<beta> x" arbitrary: x d j)
    case Nil
    have "x = Item (A,\<gamma>) (length \<gamma>) i" using Nil.hyps Nil.prems(3,4) \<open>x = _\<close> wf_Earley[of _ x]
      unfolding wf_item_def item_defs by auto
    have "\<exists>m \<le> n. P \<turnstile> [] \<Rightarrow>(m) slice j k w"
      using Nil by auto
    hence "slice j k w = []"
      by simp
    hence "j = k"
      unfolding slice_drop_take using \<open>j \<le> k\<close> less.prems(2) by simp
    thus ?case
      using \<open>x = Item (A, \<gamma>) (length \<gamma>) i\<close> Nil.prems by blast
  next
    case (Cons s ss)
    from Cons.prems(4) obtain m where m: "m \<le> n" "P \<turnstile> \<beta> x \<Rightarrow>(m) slice j k w" by blast
    obtain j' n1 n2 where *: 
      "P \<turnstile> [s] \<Rightarrow>(n1) slice j j' w"
      "P \<turnstile> ss \<Rightarrow>(n2) slice j' k w"
      "j \<le> j'" "j' \<le> k" "n1 \<le> m" "n2 \<le> m"
      using deriven_append_decomp[of m P "[s]" ss "slice j k w"] slice_concat_Ex[OF \<open>j \<le> k\<close>]
        Cons.hyps(2) m(2) append_Nil[of ss] append_Cons[of s "[]" ss]
      by (metis le_add1 le_add2)
    let ?x = "Item (A, \<gamma>) (d+1) i"
    have nxt: "next_sym x s"
      using Cons.hyps(2) unfolding item_defs(2) next_sym_def is_complete_def
      by (auto, metis nth_via_drop)
    hence "(j', ?x) \<in> Earley"
    proof (cases n1)
      case 0
      hence "[s] = slice j j' w"
        using *(1,5) by auto
      from slice_singleton[OF le_trans[OF "*"(4) less.prems(2)] this] have "j' = j+1" .
      hence "j < length w"
        using "*"(4) less.prems(2) by linarith
      from slice_nth[OF this] \<open>[s] = slice j j' w\<close> \<open>j' = j + 1\<close>
      have "w!j = s"
        by simp
      hence "(j',mv_dot x) \<in> Earley"
        using Earley.Scan[OF \<open>(j,x) \<in> Earley\<close> \<open>j < length w\<close>] nxt \<open>j' = j + 1\<close>
        by (auto)
      thus ?thesis
        by (simp add: \<open>x = _\<close> mv_dot_def)
    next
      case (Suc n0)
      then obtain u where "P \<turnstile> [s] \<Rightarrow> u" and n0: "P \<turnstile> u \<Rightarrow>(n0) slice j j' w"
        using *(1) by (metis relpowp_Suc_E2)
      then obtain B where [simp]: "s = Nt B" and prod: "(B, u) \<in> P"
        using *(1)
        by (meson derive_singleton)
      define y where y_def: "y = Item (B,u) 0 j"
      have **: "P \<turnstile> \<beta> y \<Rightarrow>(n0) slice j j' w"
        using n0 by (auto simp: item_defs y_def)
      have "(j,y) \<in> Earley"
        using y_def \<open>(j,x) \<in> Earley\<close> nxt *(1) prod
        by (auto simp: item_defs Earley.Predict Predict_def)
      have "(j', Item (B,u) (length u) j) \<in> Earley"
        using less.IH [OF _ _ _ y_def \<open>(j,y) \<in> Earley\<close> **] *(3,4,5) m(1) Suc less.prems(2)
        by linarith
      from Earley.Complete[OF this, of x] show ?thesis
        using nxt Cons.prems(2,3) by (simp add: mv_dot_def is_complete_def rhs_def)
    qed
    moreover have "ss = \<beta> ?x"
      using Cons.hyps(2) \<open>x = _\<close> unfolding item_defs(2)
      by (auto, metis List.list.sel(3) drop_Suc drop_tl)
    ultimately show ?case
      using Cons.hyps(1) *(2,4,6) m(1) le_trans by blast
  qed
qed

text \<open>This completeness proof uses the definition \<open>w \<equiv> map Tm w0\<close> for the first time.
In particular soundness does not use it and thus works for \<open>Nt\<close>s as well.\<close>

theorem Earley_complete:
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* w"
  shows "recognized Earley"
proof -
  obtain \<alpha> n where *: "(S ,\<alpha>) \<in> P" "P \<turnstile> \<alpha> \<Rightarrow>(n) w"
    by (metis assms deriven_start1 rtranclp_power w_def)
  define x where x_def: "x = Item (S, \<alpha>) 0 0"
  have 1: "(0,x) \<in> Earley"
    using x_def Earley.Init *(1) by (fastforce simp: Init_def)
  have 2: "P \<turnstile> (\<beta> x) \<Rightarrow>(n) (slice 0 (length w) w)"
    using *(2) x_def by (simp add: item_defs)
  have "(length w, Item (S,\<alpha>) (length \<alpha>) 0) \<in> Earley"
    using Earley_complete_induction[OF _ _ _ 1 2] x_def by auto
  thus ?thesis
    unfolding recognized_def is_final_def by (auto simp: is_complete_def item_defs, force)
qed

text \<open>Completeness can also be proved if there are \<open>Nt\<close>s in the input \<open>w\<close>: does not use \<open>w_def\<close>!\<close>

lemma Derivation_start_nonstart:
  assumes "P \<turnstile> [Nt S] \<Rightarrow>(n) w" "w \<noteq> [Nt S]"
  shows "\<exists>\<alpha> m. n = Suc m \<and> P \<turnstile> \<alpha> \<Rightarrow>(m) w \<and> (S,\<alpha>) \<in> P"
proof (cases n)
  case 0
  thus ?thesis
    using assms by (auto)
next
  case (Suc m)
  then obtain \<alpha> where *: "P \<turnstile> [Nt S] \<Rightarrow> \<alpha>" "P \<turnstile> \<alpha> \<Rightarrow>(m) w"
    using assms by (metis relpowp_Suc_E2)
  from  derive.cases[OF *(1)] have "(S, \<alpha>) \<in> P"
    by (simp add: Cons_eq_append_conv) blast
  thus ?thesis using *(2) Suc by auto
qed

text\<open>Only the decomposition into n+1 steps is different to the earlier completeness proof.
Instead of \<open>w \<noteq> [S]\<close> one could also require \<open>[S] \<Rightarrow>(n+1) w\<close>, but that is a bit odd.\<close>

theorem Earley_complete_NT:
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* w" "w \<noteq> [Nt S]"
  shows "recognized Earley"
proof -
  obtain \<alpha> n where *: "(S ,\<alpha>) \<in> P" "P \<turnstile> \<alpha> \<Rightarrow>(n) w"
    using Derivation_start_nonstart assms by(metis rtranclp_imp_relpowp)
  define x where x_def: "x = Item (S, \<alpha>) 0 0"
  have 1: "(0,x) \<in> Earley"
    using x_def Earley.Init *(1) by (fastforce simp: Init_def)
  have 2: "P \<turnstile> (\<beta> x) \<Rightarrow>(n) (slice 0 (length w) w)"
    using *(2) x_def by (simp add: item_defs)
  have "(length w, Item (S,\<alpha>) (length \<alpha>) 0) \<in> Earley"
    using Earley_complete_induction[OF _ _ _ 1 2] x_def by auto
  thus ?thesis
    unfolding recognized_def is_final_def by (auto simp: is_complete_def item_defs, force)
qed


subsubsection \<open>Correctness\<close>

theorem correctness_Earley:
  shows "recognized Earley \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using soundness_Earley Earley_complete by blast

theorem correctness_Earley_NT:
  assumes "w \<noteq> [Nt S]"
  shows "recognized Earley \<longleftrightarrow> P \<turnstile> [Nt S] \<Rightarrow>* w"
  using assms soundness_Earley Earley_complete_NT by blast


subsubsection \<open>Finiteness\<close>

fun mk_item :: "('n,'t) prod \<times> nat \<times> nat \<times> nat \<Rightarrow> ('n,'t) item \<times> nat" where
  "mk_item (r, d, k, ends) = (Item r d k, ends)" 

lemma finite_wf_item:
  shows "finite { (x,k). wf_item k x }"
proof -
  define M where "M = Max { length (rhs r) | r. r \<in> P }"
  define Top where "Top = (P \<times> {0..M} \<times> {0..length w} \<times> {0..length w})"
  hence "finite Top"
    using finite_cartesian_product finite by blast
  have "inj_on mk_item Top"
    unfolding Top_def inj_on_def by simp
  hence "finite (mk_item ` Top)"
    using finite_image_iff \<open>finite Top\<close> by auto
  have "{ (x,k). wf_item k x } \<subseteq> mk_item ` Top"
  proof auto
    fix x k
    assume "wf_item k x"
    then obtain r d j where *: "x = Item r d j"
      "r \<in> P" "d \<le> length (rhs(prod x))" "j \<le> k" "k \<le> length w"
      unfolding wf_item_def using item.exhaust_sel le_trans by blast
    hence "length (rhs r) \<in> { length (rhs r) | r. r \<in> P }"
      using *(1,2) by blast
    moreover have "finite { length (rhs r) | r. r \<in> P }"
      using finite finite_image_set[of "\<lambda>x. x \<in> P"] by fastforce
    ultimately have "M \<ge> length (rhs r)"
      unfolding M_def by simp
    hence "d \<le> M"
      using *(1,3) by (metis item.sel(1) le_trans)
    hence "(r, d, j, k) \<in> Top"
      using *(2,4,5) unfolding Top_def by simp
    thus "(x,k) \<in> mk_item ` Top"
      using *(1) by force
  qed
  thus ?thesis
    using \<open>finite (mk_item ` Top)\<close> rev_finite_subset by auto
qed


subsection \<open>Earley recognizer: Standard recursive/inductive definition\<close>

definition Scan :: "nat \<Rightarrow> ('n,'t) item set \<Rightarrow> ('n,'t) item set" where
  "Scan k B = { mv_dot x | x. x \<in> B \<and> next_sym x (w!k) }"

inductive_set Close :: "('n,'t) item set list \<Rightarrow> ('n,'t) item set \<Rightarrow> ('n,'t) item set" for Bs B where
    Init: "x \<in> B \<Longrightarrow> x \<in> Close Bs B"
  | Predict: "\<lbrakk> x \<in> Close Bs B; x' \<in> Predict (length Bs) x \<rbrakk> \<Longrightarrow> x' \<in> Close Bs B"
  | Complete: "\<lbrakk> y \<in> Close Bs B;  is_complete y;
      from y = length Bs \<longrightarrow> x \<in> Close Bs B; from y < length Bs \<longrightarrow> x \<in> Bs ! from y;
      next_sym x (Nt(lhs(prod y))) \<rbrakk> \<Longrightarrow>
        mv_dot x \<in> Close Bs B"

text \<open>Cannot just write \<open>x \<in> (Bs @ [Close Bs B]) ! from y\<close>.
The monotonicity prover cannot deal with it and it is unclear what \<open>monos\<close> one would
need to add. However, we can derive that version easily:\<close>

definition "Complete Bs y = mv_dot ` {x \<in> Bs ! from y. next_sym x (Nt(lhs(prod y)))}"

lemma Close_Complete:(* used in Paper *)
  "\<lbrakk> y \<in> Close Bs B;  is_complete y; x' \<in> Complete (Bs @ [Close Bs B]) y
   \<rbrakk> \<Longrightarrow> x' \<in> Close Bs B"
apply(simp add: Complete_def image_def nth_append)
by (metis Close.Complete diff_is_0_eq' linorder_not_le nat_neq_iff nth_Cons_0)

abbreviation "wf_bin k B \<equiv> \<forall>s \<in> B. wf_item k s"
abbreviation "wf_bins Bs \<equiv> \<forall>k < length Bs. wf_bin k (Bs!k)"

fun bins :: "nat \<Rightarrow> ('n,'t) item set list" where
"bins 0 = [Close [] Init]" |
"bins (Suc k) = (let Bs = bins k in Bs @ [Close Bs (Scan k (last Bs))])"


subsubsection \<open>Correctness\<close>

lemma length_bins[simp]: "length (bins k) = k+1"
by(induction k) (auto simp: Let_def)

corollary bins_nonempty: "bins k \<noteq> []"
using length_bins[of k] by (auto simp del: length_bins)

lemma take_Suc_bins: "m \<le> n \<Longrightarrow> take (Suc m) (bins n) = bins m"
apply(induction n arbitrary: m)
 apply simp
apply(auto simp add: Let_def le_Suc_eq)
done

lemma nth_bins_eq: "\<lbrakk> i \<le> m; m \<le> n \<rbrakk> \<Longrightarrow> bins m ! i = bins n ! i"
by (metis le_imp_less_Suc nth_take take_Suc_bins)

lemma Close_Init_if_Earley0: "(0,x) \<in> Earley \<Longrightarrow> x \<in> Close [] Init"
proof(induction "0::nat" x rule: Earley.induct)
  case Init
  show ?case by(rule Close.Init[OF Init])
next
  case (Scan x j) (* not possible *)
  thus ?case by simp
next
  case (Predict x x')
  thus ?case by(simp add: Close.Predict)
next
  case (Complete y x)
  thus ?case using wf_Earley[OF Complete.hyps(1)] unfolding wf_item_def
    using Close.Complete[OF Complete.hyps(2,3)] by (simp)
qed

lemma Earley0_if_Close_Init: "x \<in> Close [] Init \<Longrightarrow> (0,x) \<in> Earley"
proof(induction rule: Close.induct)
  case (Init)
  then show ?case using Earley.Init by blast
next
  case (Predict)
  then show ?case using Earley.Predict by auto
next
  case (Complete)
  then show ?case using wf_Earley by (fastforce simp: Earley.Complete wf_item_def)
qed

lemma \<E>_0: "\<E> 0 = Close [] Init"
unfolding \<E>_def using Close_Init_if_Earley0 Earley0_if_Close_Init
by blast

lemma \<E>_Suc1:
assumes "\<forall>i\<le>n. bins n ! i = \<E> i" "n < length w"
shows "x \<in> Close (bins n) (Scan n (\<E> n))  \<Longrightarrow> x \<in> \<E>(Suc n)"
proof (induction rule: Close.induct)
  case (Init x)
  thus ?case using assms(2) unfolding \<E>_def Scan_def by (auto intro: Earley.Scan[simplified])
next
  case (Predict x x')
  thus ?case using Earley.Predict Earley_eq_\<E> by auto
next
  case (Complete y x)
  have "from y = Suc n \<or> from y < Suc n"
    using wf_EarleyS[OF Complete.IH(1)] unfolding wf_item_def by auto
  with assms(1) Complete Earley.Complete show ?case unfolding \<E>_def by (auto)
qed

lemma \<E>_Suc2:
  "(Suc n,x) \<in> Earley \<Longrightarrow> \<forall>i\<le>n. bins n ! i = \<E> i \<Longrightarrow> x \<in> Close (bins n) (Scan n (\<E> n))"
proof (induction "Suc n" x arbitrary: n rule: Earley.induct)
  case (Scan)
  thus ?case unfolding Scan_def
    by (metis (mono_tags, lifting) Close.Init Earley_eq_\<E> Suc_eq_plus1 add_right_imp_eq mem_Collect_eq)
next
  case (Predict)
  thus ?case
    by (metis (no_types, lifting) Earley_Gw.Close.Predict Earley_Gw.length_bins Suc_eq_plus1)
next
  case (Complete y x)
  have "from y = Suc n \<or> from y < Suc n"
    using wf_Earley[OF Complete.hyps(1)] unfolding wf_item_def by auto
  thus ?case
  proof
    assume "from y = Suc n"
    thus ?thesis
      using Complete.prems(1) Complete.hyps(3,5,6) Close.Complete[OF Complete.hyps(2)] length_bins
      by (metis (mono_tags, lifting) Suc_eq_plus1 less_irrefl_nat)
  next
    assume "from y < Suc n"
    thus ?thesis using Complete
      by (metis (no_types, lifting) Close.Complete Earley_eq_\<E> Suc_eq_plus1 le_SucE length_bins nless_le)
  qed
qed

lemma \<E>_Suc: "\<lbrakk> n < length w; \<forall>i \<le> n. bins n ! i = \<E> i \<rbrakk>
  \<Longrightarrow> \<E> (Suc n) = Close (bins n) (Scan n (\<E> n))"
using \<E>_Suc1 \<E>_Suc2 unfolding \<E>_def by auto

lemma bins_eq_\<E>_gen: "n \<le> length w \<Longrightarrow> \<forall>i \<le> n. bins n ! i = \<E> i"
proof(induction n)
  case 0
  thus ?case by (simp add: \<E>_0)
next
  case (Suc n)
  then have "n < length w" by auto
  hence IH: "\<forall>i\<le>n. bins n ! i = \<E> i" using Suc.IH by auto
  hence *: "\<forall>i\<le>n. bins (Suc n) ! i = \<E> i" by (metis le_add2 nth_bins_eq plus_1_eq_Suc)
  have "bins (Suc n) ! (Suc n) = \<E> (Suc n)" using * \<E>_Suc[OF \<open>n < length w\<close> IH] bins_nonempty
    by(simp add: Let_def nth_append last_conv_nth)
  thus ?case using * by (metis le_SucE)
qed

text \<open>Correctness w.r.t. abstract @{const Earley}/@{const \<E>} definition:\<close>

corollary bins_eq_\<E>:(* used in Paper *) "i \<le> length w \<Longrightarrow> bins (length w) ! i = \<E> i"
using bins_eq_\<E>_gen[of "length w"] by blast


subsubsection \<open>Simplification: \<open>\<epsilon>\<close>-free Grammars\<close>

definition wf_item1 :: "nat \<Rightarrow> ('n,'t) item \<Rightarrow> bool" where 
"wf_item1 k x = (wf_item k x \<and> (is_complete x \<longrightarrow> from x < k))"

definition "wf_bin1 k B = (\<forall>x \<in> B. wf_item1 k x)"
definition "wf_bins1 Bs = (\<forall>k < length Bs. wf_bin1 k (Bs!k))"

abbreviation (input) "wf_bin1' Bs \<equiv> wf_bin1 (length Bs)"

text \<open>Like @{const Close}, but in \<open>Complete\<close>, only one item is from the current item set:\<close>

inductive_set Close1 :: "('n,'t) item set list \<Rightarrow> ('n,'t) item set \<Rightarrow> ('n,'t) item set" for Bs B where
    Init: "x \<in> B \<Longrightarrow> x \<in> Close1 Bs B"
  | Predict: "\<lbrakk> x \<in> Close1 Bs B; x' \<in> Predict (length Bs) x \<rbrakk> \<Longrightarrow> x' \<in> Close1 Bs B"
  | Complete: "\<lbrakk> y \<in> Close1 Bs B;  is_complete y; x \<in> Bs ! from y;
      next_sym x (Nt(lhs(prod y))) \<rbrakk> \<Longrightarrow>
        mv_dot x \<in> Close1 Bs B"

lemma Close1_incr: "B \<subseteq> Close1 Bs B"
by (simp add: Close1.Init subsetI)

lemma Close1_mono1: assumes "B \<subseteq> B'"
shows "x \<in> Close1 Bs B \<Longrightarrow> x \<in> Close1 Bs B'"
proof(induction rule: Close1.induct)
  case (Init x) thus ?case using Close1.Init assms by blast
next
  case (Predict x x') thus ?case using Close1.Predict by blast
next
  case (Complete y x) thus ?case using Close1.Complete by blast
qed

corollary  Close1_mono: "B \<subseteq> B' \<Longrightarrow> Close1 Bs B \<subseteq> Close1 Bs B'"
using Close1_mono1 by blast

lemma Close1_idemp1: "x \<in> Close1 Bs (Close1 Bs B) \<Longrightarrow> x \<in> Close1 Bs B"
proof(induction rule: Close1.induct)
  case (Init x) thus ?case .
next
  case (Predict x x') thus ?case using Close1.Predict by blast
next
  case (Complete y x) thus ?case using Close1.Complete by blast
qed

lemma Close1_idemp: "Close1 Bs (Close1 Bs B) \<subseteq> Close1 Bs B"
using Close1_idemp1 by blast

end (* Earley_Gw *)

locale Earley_Gw_eps = Earley_Gw where ps = ps for ps :: "('n,'t) prods" +
assumes eps_free: "eps_free ps"
begin

lemma \<epsilon>_free: "\<forall>r \<in> P. length(rhs r) > 0"
  using eps_free unfolding rhs_def Eps_free_def by auto

lemma wf1_Predict:
  "\<lbrakk> wf_item1 k x; x' \<in> Predict k x \<rbrakk> \<Longrightarrow> wf_item1 k x'"
using \<epsilon>_free unfolding wf_item1_def wf_item_def Predict_def is_complete_def by (auto)

(* does not need \<epsilon> *)
lemma wf1_Complete:
  assumes "wf_item1 j x" "j = from y" "wf_item1 k y"
  assumes "is_complete y" "next_sym x (Nt(lhs(prod y)))"
  shows "wf_item1 k (mv_dot x)"
  using assms unfolding wf_item1_def wf_item_def is_complete_def next_sym_def mv_dot_def
  by (auto split: if_splits)
(*
lemma wf1_Complete': "\<lbrakk> wf_bins1 Bs; is_complete x; wf_item1 x (length Bs); y \<in> Complete Bs x\<rbrakk>
       \<Longrightarrow> wf_item1 y (length Bs)"
using wf1_Complete unfolding Complete_def wf_bin1_def wf_bins1_def wf_item1_def
by blast
*)
lemma wf_item1_Close1: assumes "wf_bins1 Bs" "wf_bin1' Bs B"
shows "y \<in> Close1 Bs B \<Longrightarrow> wf_item1 (length Bs) y"
proof (induction rule: Close1.induct)
  case (Init x)
  thus ?case using assms(2) unfolding wf_bins1_def wf_bin1_def by blast
next
  case (Predict x x')
  thus ?case using Close1.Predict wf1_Predict by blast
next
  case (Complete y x)
  show ?case using Complete.IH Complete.hyps assms(1) wf1_Complete wf_item1_def
    unfolding wf_bins1_def wf_bin1_def by blast
qed

lemma Close_if_Close1: assumes "wf_bins1 Bs" "wf_bin1' Bs B"
shows "x \<in> Close1 Bs B \<Longrightarrow> x \<in> Close Bs B"
proof (induction rule: Close1.induct)
  case (Init x)
  thus ?case by (simp add: Close.Init)
next
  case (Predict x x')
  thus ?case
    using Close.Predict by blast
next
  case (Complete y x)
  show ?case
    using Close.Complete[OF Complete.IH Complete.hyps(2) _ _ Complete.hyps(4)] Complete.hyps(2,3)
      wf_item1_Close1[OF assms Complete.hyps(1)] unfolding wf_item1_def
    by auto
qed

lemma Close1_if_Close: assumes "wf_bins1 Bs" "wf_bin1' Bs B"
shows "x \<in> Close Bs B \<Longrightarrow> x \<in> Close1 Bs B"
proof (induction rule: Close.induct)
  case (Init x)
  thus ?case by (simp add: Close1.Init)
next
  case (Predict x x')
  thus ?case
    using Close1.Predict by blast
next
  case (Complete y x)
  show ?case
    using Complete.IH(1) Complete.hyps(2,3) Close1.Complete[OF Complete.IH(1) Complete.hyps(2) _ Complete.hyps(4)]
      wf_item1_Close1[OF assms] unfolding wf_item1_def by blast
qed

theorem Close1_eq_Close:
  assumes "wf_bins1 Bs" "wf_bin1' Bs B"
  shows "Close1 Bs B = Close Bs B"
using Close1_if_Close[OF assms] Close_if_Close1[OF assms] by blast

end (* Earely_Gw_eps *)


subsection "Towards a single-pass worklist completion algorithm"

(* The worklist algorithm is quite generic and does not need \<epsilon> *)

context Earley_Gw
begin

(* TODO? Generic workset algorithm parameterized with next-function? *)

inductive Close2 :: "('n,'t) item set list \<Rightarrow> ('n,'t) item set * ('n,'t) item set \<Rightarrow> ('n,'t) item set * ('n,'t) item set \<Rightarrow> bool"
("(_ \<turnstile> _ \<rightarrow> _)" [50, 0, 50] 50)
  for Bs where
    Predict: "\<lbrakk> x \<in> B; \<not> is_complete x \<rbrakk> \<Longrightarrow>
    Close2 Bs (B,C) (B \<union> Predict (length Bs) x - (C \<union> {x}), insert x C)"
  | Complete: "\<lbrakk> x \<in> B; is_complete x \<rbrakk> \<Longrightarrow>
    Close2 Bs (B,C) ((B \<union> Complete Bs x) - (C \<union> {x}), (C \<union> {x}))"
(* TODO: Better: (todo - {x}) \<union> (Predict x (length Bs) - insert x done) *)

lemmas Close2_induct = Close2.induct[split_format(complete), consumes 1, case_names Predict Complete]

abbreviation Close2_steps ("(_ \<turnstile> _ \<rightarrow>* _)" [50, 0, 50] 50) where
"Bs \<turnstile> p \<rightarrow>* p' \<equiv> (Close2 Bs)^** p p'"

definition "close2 Bs B = (SOME C. Bs \<turnstile> (B,{}) \<rightarrow>* ({},C))"

lemma Close2_steps_disj: "Bs \<turnstile> (B,C) \<rightarrow>* (B',C') \<Longrightarrow> B \<inter> C = {} \<Longrightarrow> B' \<inter> C' = {}"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case .
next
  case step
  thus ?case by(auto simp add: Close2.simps)
qed


subsubsection \<open>\<open>Close2\<close> is Sound wrt \<open>Close1\<close>\<close>

theorem Close2_step_subset_Close1:
  "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> B' \<union> C' \<subseteq> Close1 Bs (B \<union> C)"
proof(induction rule: Close2_induct)
  case (Predict x B "C")
  thus ?case
    using Close1_incr Close1.Predict by blast
next
  case (Complete x B "C")
  have *: "B \<subseteq> Close1 Bs (B \<union> C)" using Close1_incr by blast
  moreover
  have "Complete Bs x \<subseteq> Close1 Bs (B \<union> C)"
    using Complete Close1.Complete * unfolding Complete_def next_sym_def by (auto split: if_splits)
  moreover
  have "insert x C \<subseteq> Close1 Bs (B \<union> C)"
    using Close1_incr Complete.hyps(1) by blast
  ultimately show ?case
    by blast
qed

theorem Close2_steps_subset_Close1:
  "Bs \<turnstile> (B,C) \<rightarrow>* (B',C') \<Longrightarrow> B' \<union> C' \<subseteq> Close1 Bs (B \<union> C)"
proof(induction rule: rtranclp_induct2)
  case refl
  thus ?case by(rule Close1_incr)
next
  case (step B' C' B'' C'')
  thus ?case
    using Close2_step_subset_Close1[OF step.hyps(2)] Close1_idemp Close1_mono by blast
qed

corollary Close2_steps_subset_Close1': "Bs \<turnstile> (B,{}) \<rightarrow>* ({},C) \<Longrightarrow> C \<subseteq> Close1 Bs B"
by (drule Close2_steps_subset_Close1) auto

subsubsection \<open>\<open>Close2\<close> is Complete wrt \<open>Close1\<close>\<close>

theorem Close2_steps_incr:
  "Bs \<turnstile> (B,C) \<rightarrow>* (B',C') \<Longrightarrow> B \<union> C \<subseteq> B' \<union> C'"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case by blast
next
  case (step) thus ?case by(auto simp add: Close2.simps)
qed

theorem Close2_steps_subdivide: assumes "x \<notin> C" "B \<inter> C = {}"
  shows "Bs \<turnstile> (B,C) \<rightarrow>* (B',C') \<Longrightarrow> x \<in> C' \<Longrightarrow>
  (\<exists>B1 C1 B2 C2. Bs \<turnstile> (B,C) \<rightarrow>* (B1,C1) \<and> x \<in> B1 \<and> Bs \<turnstile> (B1,C1) \<rightarrow> (B2,C2) \<and> x \<notin> B2 \<and> Bs \<turnstile> (B2,C2) \<rightarrow>* (B',C'))"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case using assms by blast
next
  case (step)
  thus ?case using step(2)[unfolded Close2.simps] Close2_steps_disj assms rtranclp.simps
    by (metis (no_types, lifting) Diff_iff Pair_inject Un_insert_right Un_empty_right insertE insert_iff)
qed

lemma Close2_sim_Close1:
 shows "\<lbrakk> x \<in> Close1 Bs B;  Bs \<turnstile> (B,{}) \<rightarrow>* ({},C) \<rbrakk> \<Longrightarrow> x \<in> C"
proof(induction rule: Close1.induct)
  case (Init x)
  thus ?case using Close2_steps_incr
    by blast
next
  case (Predict x y)
  from \<open>y \<in> _\<close> have n: "\<not> is_complete x"
    unfolding Predict_def next_sym_def by auto
  obtain B2 C2 B3 C3
  where "Bs \<turnstile> (B,{}) \<rightarrow>* (B2,C2)" "x \<in> B2" "Bs \<turnstile> (B2,C2) \<rightarrow> (B3,C3)" "x \<notin> B3" "Bs \<turnstile> (B3,C3) \<rightarrow>* ({},C)"
    using Close2_steps_subdivide[OF _ _ Predict.prems Predict.IH[OF Predict.prems]] by blast
  have "B2 \<inter> C2 = {}" using Close2_steps_disj \<open>Bs \<turnstile> (B, {}) \<rightarrow>* (B2, C2)\<close> by blast
  have "B3 = B2 \<union> Predict (length Bs) x - insert x C2" "C3 = insert x C2"
    using \<open>Bs \<turnstile> (B2,C2) \<rightarrow> _\<close> \<open>B2 \<inter> C2 = {}\<close> \<open>x \<in> B2\<close> \<open>x \<notin> B3\<close> n unfolding Close2.simps by auto
  show ?case
    using Close2_steps_incr[OF \<open>Bs \<turnstile> (B3, C3) \<rightarrow>* _\<close>] Predict.hyps(2) \<open>B3 = _\<close> \<open>C3 = _\<close> by blast
next
  case (Complete x y)
  have n: "is_complete x"
    by (simp add: Complete.hyps(2) next_sym_def)
  obtain B2 C2 B3 C3
    where "Bs \<turnstile> (B,{}) \<rightarrow>* (B2,C2)" "x \<in> B2" "Bs \<turnstile> (B2,C2) \<rightarrow> (B3,C3)" "x \<notin> B3" "Bs \<turnstile> (B3,C3) \<rightarrow>* ({},C)"
    using Close2_steps_subdivide[OF _ _ Complete.prems Complete.IH[OF Complete.prems]] by blast
  have "B2 \<inter> C2 = {}" using Close2_steps_disj \<open>Bs \<turnstile> (B, {}) \<rightarrow>* (B2, C2)\<close> by blast
  have "B3 = B2 \<union> Complete Bs x - insert x C2" "C3 = insert x C2"
    using \<open>Bs \<turnstile> (B2,C2) \<rightarrow> _\<close> \<open>B2 \<inter> C2 = {}\<close> \<open>x \<in> B2\<close> \<open>x \<notin> B3\<close> n unfolding Close2.simps by auto
  show ?case
    using Close2_steps_incr[OF \<open>Bs \<turnstile> (B3, C3) \<rightarrow>* _\<close>] Complete.hyps \<open>B3 = _\<close> \<open>C3 = _\<close>
    unfolding Complete_def by auto
qed

corollary Close1_subset_Close2:
 "Bs \<turnstile> (B,{}) \<rightarrow>* ({},D) \<Longrightarrow> Close1 Bs B \<subseteq> D"
using Close2_sim_Close1 by auto

corollary Close2_eq_Close1:
  "Bs \<turnstile> (B,{}) \<rightarrow>* ({},C) \<Longrightarrow> C = Close1 Bs B"
using Close1_subset_Close2 Close2_steps_subset_Close1' by blast


subsubsection \<open>Preparation for Termination of \<open>Close2\<close>\<close>

text \<open>Here we only define the well-founded relation that subsumes \<open>Close2\<close>.\<close>

definition Close2_less :: "nat \<Rightarrow> ((('n,'t) item set \<times> ('n,'t) item set) \<times> (('n,'t) item set \<times> ('n,'t) item set)) set" where
"Close2_less k = (\<lambda>(B,C). card({x. wf_item k x} - (B \<union> C))) <*mlex*> inv_image finite_psubset fst"

lemma wf_Close2_less: "wf (Close2_less k)"
by (simp add: Close2_less_def wf_mlex) 

lemma finite_ex_wf_item: "finite ({x. wf_item k x})"
using finite_subset[OF _ finite_imageI[OF finite_wf_item, of fst]]
  Collect_mono[of "wf_item k"]
by (auto simp: image_def)

lemma wf_items_mv_dot: "\<lbrakk> wf_bins1 Bs; wf_item1 (length Bs) x; is_complete x \<rbrakk> \<Longrightarrow>
  mv_dot ` {y \<in> Bs ! from x. next_sym y (Nt(lhs (prod x)))} \<subseteq> {x. wf_item (length Bs) x}"
    using wf_Complete unfolding next_sym_def wf_bin1_def wf_bins1_def wf_item1_def
    by (smt (verit, ccfv_threshold) image_Collect_subsetI mem_Collect_eq option.distinct(1))

lemma Close2_less_step:
assumes "wf_bins1 Bs"
shows
 "\<lbrakk> Bs \<turnstile> (B,C) \<rightarrow> (B',C'); wf_bin1' Bs B \<rbrakk>
  \<Longrightarrow> ((B',C'), (B,C)) \<in> Close2_less (length Bs)"
proof (induction rule: Close2_induct)
  case (Predict x B C)
  let ?C = "insert x C" let ?B = "B \<union> Predict (length Bs) x - ?C"
  have 1: "B \<subseteq> {x. wf_item (length Bs) x}"
    using Predict.prems(1) unfolding wf_bin1_def wf_item1_def by blast
  have "B \<union> C < ?B \<union> ?C \<or> B \<union> C = ?B \<union> ?C \<and> ?B < B"
    using Predict.hyps(1) by blast
  thus ?case
  proof
    assume "B \<union> C < ?B \<union> ?C"
    thus ?thesis using 1 Predict.hyps(1) Predict.prems(1) wf_Predict unfolding Close2_less_def mlex_iff wf_bin1_def
      apply simp
      apply(rule disjI1)
      apply(rule psubset_card_mono)
       using Collect_mono Diff_subset_conv finite_subset[OF _ finite_ex_wf_item] sup.coboundedI2
       apply (metis (mono_tags, lifting))
      by blast
  next
    assume "B \<union> C = ?B \<union> ?C \<and> ?B \<subset> B"
    thus ?thesis
      using 1 finite_subset[OF _ finite_ex_wf_item] unfolding Close2_less_def mlex_iff by simp
  qed
next
  case (Complete x B "C")
  let ?C = "insert x C" let ?B = "B \<union> Complete Bs x - ?C"
  have 1: "B \<subseteq> {x. wf_item (length Bs) x}"
    using Complete.prems(1) unfolding wf_bin1_def wf_item1_def by blast
  have *: "mv_dot ` {y \<in> Bs ! from x. next_sym y (Nt(lhs(prod x)))} \<subseteq> {y. wf_item (length Bs) y}"
    using wf_items_mv_dot[OF \<open>wf_bins1 Bs\<close> _ Complete.hyps(2)] Complete.hyps(1) Complete.prems(1) wf_bin1_def by auto
  have "B \<union> C < ?B \<union> ?C \<or> B \<union> C = ?B \<union> ?C \<and> ?B < B"
    using Complete.hyps(1) by blast
  thus ?case
  proof
    assume "B \<union> C < ?B \<union> ?C"
    thus ?thesis
      using 1 Complete.hyps(1) * unfolding Complete_def Close2_less_def mlex_iff wf_bin1_def
      apply simp
      apply(rule disjI1)
      apply(rule psubset_card_mono)
       using Collect_mono Diff_subset_conv finite_subset[OF _ finite_ex_wf_item] sup.coboundedI2
       apply (metis (mono_tags, lifting))
      by blast
  next
    assume "B \<union> C = ?B \<union> ?C \<and> ?B \<subset> B"
    thus ?thesis
      using 1 finite_subset[OF _ finite_ex_wf_item] unfolding Close2_less_def mlex_iff by simp
  qed
qed

end (* Earley_Gw *)


subsubsection \<open>\<open>Close2\<close> Terminates and is Complete wrt \<open>Close1\<close>\<close>

context Earley_Gw_eps
begin           

lemma Close2_step_pres1: assumes "wf_bins1 Bs"
shows "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> wf_bin1' Bs B \<Longrightarrow> wf_bin1' Bs B'"
proof(induction rule: Close2_induct)
  case (Predict x B "C")
  thus ?case using wf1_Predict unfolding wf_bin1_def by blast
next
  case (Complete x B "C")
  thus ?case using wf1_Complete assms unfolding Complete_def
    by (smt (verit, del_insts) DiffD1 UnE image_iff mem_Collect_eq option.distinct(1) next_sym_def wf_item1_def wf_bin1_def wf_bins1_def)
qed

lemma Close2_step_pres2: assumes "wf_bins1 Bs"
shows "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> wf_bin1' Bs B \<Longrightarrow> wf_bin1' Bs C \<Longrightarrow> wf_bin1' Bs C'"
proof(induction rule: Close2_induct)
  case (Predict x B "C")
  thus ?case using wf1_Predict unfolding wf_bin1_def by blast
next
  case (Complete x B "C")
  thus ?case unfolding wf_bin1_def by blast
qed

(* unify wf_bin1 and wf_items? *)
lemma Close2_NF: assumes "wf_bins1 Bs"
shows "wf_bin1' Bs B \<Longrightarrow> \<exists>C'. Bs \<turnstile> (B,C) \<rightarrow>* ({},C')"
using wf_Close2_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "B = {}"
    thus ?thesis by blast
  next
    assume "B \<noteq> {}"
    then obtain B' C' where step: "Bs \<turnstile> (B,C) \<rightarrow> (B',C')" by (meson Close2.intros equals0I)
    note 1 = Close2_step_pres1[OF assms step less.prems(1)]
    note 2 = Close2_step_pres2[OF assms step less.prems]
    from less(1)[OF Close2_less_step [OF \<open>wf_bins1 Bs\<close> step]] less.prems
    show ?thesis using 1 2 by (metis converse_rtranclp_into_rtranclp step)
  qed
qed

lemma close2_eq_Close1: assumes "wf_bins1 Bs" "wf_bin1' Bs B"
 shows "close2 Bs B = Close1 Bs B"
proof
  from Close2_NF[OF assms,of "{}"] Close2_steps_subset_Close1'
  show "close2 Bs B \<subseteq> Close1 Bs B" by(simp add: close2_def wf_bin1_def) (metis someI)
  from Close1_subset_Close2 Close2_NF[OF assms,of "{}"]
  show "Close1 Bs B \<subseteq> close2 Bs B" by(simp add: close2_def wf_bin1_def) (metis someI)
qed

lemma wf_bin1_Init: "wf_bin1 0 Init"
using \<epsilon>_free by(auto simp add: Init_def wf_bin1_def wf_item1_def wf_item_def is_complete_def)

lemma bins0_close2:(* used in Paper *) "bins 0 = [close2 [] Init]"
by(simp flip: Close1_eq_Close add: close2_eq_Close1 wf_bins1_def wf_bin1_Init)

lemma Close_Init: "x \<in> Close [] Init \<Longrightarrow> \<not> is_complete x"
unfolding is_complete_def Init_def
proof (induction rule: Close.induct)
  case (Init x)
  thus ?case
    using \<epsilon>_free by fastforce
next
  case (Predict x x')
  thus ?case
    using \<epsilon>_free Predict_def by fastforce
next
  case (Complete y x)
  thus ?case
    using is_complete_def by blast
qed

lemma Close_wf_bin1: "\<lbrakk> wf_bins1 Bs; wf_bin1' Bs B \<rbrakk>
 \<Longrightarrow> wf_bin1' Bs (Close Bs B)"
by (metis Close1_eq_Close wf_bin1_def wf_item1_Close1)

(* \<epsilon>_free not needed! *)
lemma wf_bin1_Scan: "\<lbrakk> k < length w; wf_bin1 k B \<rbrakk> \<Longrightarrow> wf_bin1 (Suc k) (Scan k B)"
by(auto simp: Scan_def mv_dot_def is_complete_def next_sym_def wf_bin1_def wf_item1_def wf_item_def)

lemma wf_bins1_bins: "k \<le> length w \<Longrightarrow> wf_bins1 (bins k)"
proof (induction k)
  case 0
  thus ?case
    using Close_Init by (auto simp: \<E>_0 wf_EarleyS wf_bins1_def wf_bin1_def wf_item1_def)
next
  case (Suc k)
  have "wf_bins1 (bins k)" using Suc.IH Suc.prems by auto
  hence "wf_bin1 (Suc k) (Scan k (last (bins k)))"
    using wf_bin1_Scan Suc.prems 
    by(simp add: last_conv_nth bins_nonempty wf_bins1_def)
  with Suc show ?case
    using Close_wf_bin1[of "bins k"]
    by(auto simp add: Let_def wf_bins1_def less_Suc_eq nth_append)
qed

lemma wf_bin1_last:
  "k \<le> length w \<Longrightarrow> wf_bin1 k (last (bins k))"
using wf_bins1_bins[of k]
by(simp add: last_conv_nth[OF bins_nonempty] wf_bins1_def)

lemma binsSuc_close2:(* used in Paper *)
  "k < length w \<Longrightarrow> bins (Suc k) = (let Bs = bins k in Bs @ [close2 Bs (Scan k (last Bs))])"
by(simp flip: Close1_eq_Close add: close2_eq_Close1 wf_bins1_bins wf_bin1_Scan wf_bin1_last Let_def)

end

(* List *)

(* TODO merge with list functions in WL;
WL: time_fun fold equations fold_simps;
Warning: union_list below inserts elements in different order from union_LWL
(not relevant because our refinement and the one by Haberl are not connected - YET)
*)

text \<open>Most of the following functions are already in theory \<open>List\<close> but are redefined
because either to clarify their timing behaviour (\<open>List.member\<close> uses sets)
or simply for uniform naming.\<close>

fun isin_list :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"  where
"isin_list [] a = False" |
"isin_list (x#xs) a = (if x=a then True else isin_list xs a)"

definition insert_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
"insert_list a xs = (if isin_list xs a then xs else a#xs)"

definition union_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
"union_list = List.union"

definition diff_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
"diff_list xs ys = filter (Not o isin_list ys) xs"

lemma isin_list[simp]: "isin_list xs a = (a \<in> set xs)"
by (induction xs) auto

lemma set_insert_list[simp]: "set(insert_list x xs) = {x} \<union> set xs"
by(auto simp add: insert_list_def)

lemma insert_list_eq_List_insert: "insert_list = List.insert"
by (metis (no_types, lifting) ext List.insert_def insert_list_def isin_list)

lemma union_list_def2: "union_list = fold insert_list"
by (simp add: List.union_def insert_list_eq_List_insert union_list_def)

lemma set_union_list[simp]: "set(union_list xs ys) = set xs \<union> set ys"
by(simp add: union_list_def)

lemma set_diff_list[simp]: "set(diff_list xs ys) = set xs - set ys"
unfolding diff_list_def by auto

context Earley_Gw
begin

definition Predict_L :: "nat \<Rightarrow> ('n,'t) item \<Rightarrow> ('n,'t) item list" where
  "Predict_L k x = map (\<lambda>p. Item p 0 k) (filter (\<lambda>p. next_sym x (Nt(lhs p))) ps)"

definition Complete_L :: "('n, 't) item list list \<Rightarrow> ('n, 't) item \<Rightarrow> ('n, 't) item list" where
  "Complete_L Bs y = map mv_dot (filter (\<lambda>x. next_sym x (Nt(lhs(prod y)))) (Bs ! from y))"

lemma set_Predict_L: "set (Predict_L k x) = Predict k x"
by(auto simp: Predict_L_def Predict_def)

lemma set_Complete_L: "is_complete x \<Longrightarrow> wf_item1 (length Bs) x \<Longrightarrow>
  set (Complete_L Bs x) = Complete (map set Bs) x"
by(auto simp: Complete_L_def Complete_def wf_item1_def wf_item_def)

inductive Close2L :: "('n,'t) item list list \<Rightarrow> ('n,'t) item list * ('n,'t) item list \<Rightarrow> ('n,'t) item list * ('n,'t) item list \<Rightarrow> bool"
("(_ \<turnstile>\<^sub>L _ \<rightarrow> _)" [50, 0, 50] 50)
  for Bs where
    Predict: "\<not> is_complete x \<Longrightarrow>
    Close2L Bs (x#B,C) (diff_list (union_list (Predict_L (length Bs) x) B) (insert_list x C), insert_list x C)"
  | Complete: "is_complete x \<Longrightarrow>
    Close2L Bs (x#B,C) (diff_list (union_list (Complete_L Bs x) B) (insert_list x C), insert_list x C)"

abbreviation Close2L_steps ("(_ \<turnstile>\<^sub>L _ \<rightarrow>* _)" [50, 0, 50] 50) where
"Bs \<turnstile>\<^sub>L p \<rightarrow>* p' \<equiv> (Close2L Bs)^** p p'"

lemma Close2_if_Close2L:
  "\<lbrakk> Close2L Bs (B,C) (B',C'); wf_bin1' Bs (set B) \<rbrakk>
  \<Longrightarrow> Close2 (map set Bs) (set B,set C) (set B',set C')"
by(auto simp: set_Predict_L set_Complete_L wf_bin1_def Close2L.simps Close2.simps)

end

context Earley_Gw_eps
begin

lemma wf1_Complete': "\<lbrakk> wf_bins1 Bs; is_complete x; wf_item1 (length Bs) x; y \<in> Complete Bs x\<rbrakk>
       \<Longrightarrow> wf_item1 (length Bs) y"
using wf1_Complete unfolding Complete_def wf_bin1_def wf_bins1_def wf_item1_def
by blast

lemma wf1_Close2L_1:
  "\<lbrakk> Close2L Bs (B,C) (B',C');
     wf_bins1 (map set Bs); wf_bin1' Bs (set B) \<rbrakk>
  \<Longrightarrow> wf_bin1' Bs (set B')"
apply(auto simp: set_Predict_L set_Complete_L wf_bin1_def Close2L.simps)
  using wf1_Predict apply blast
  using wf1_Complete' by (metis length_map)

lemma wf1_Close2L_2:
  "\<lbrakk> Close2L Bs (B,C) (B',C');
     wf_bin1' Bs (set B); wf_bin1' Bs (set C) \<rbrakk>
  \<Longrightarrow> wf_bin1' Bs (set C')"
by(auto simp: set_Predict_L set_Complete_L wf_bin1_def Close2L.simps)

lemma wf1_Close2Ls:
  "\<lbrakk> (Close2L Bs)^** (B,C) (B',C'); wf_bins1 (map set Bs); wf_bin1' Bs (set B) \<rbrakk>
  \<Longrightarrow> wf_bin1' Bs (set B')"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case by blast
next
  case (step) thus ?case by(auto intro: wf1_Close2L_1)
qed

lemma Close2s_if_Close2Ls: "\<lbrakk> (Close2L Bs)^** (B,C) (B',C');
   wf_bins1 (map set Bs); wf_bin1' Bs (set B) \<rbrakk>
  \<Longrightarrow> map set Bs \<turnstile> (set B,set C) \<rightarrow>* (set B',set C')"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case by blast
next
  case (step) thus ?case
    by (meson Close2_if_Close2L rtranclp.rtrancl_into_rtrancl wf1_Close2Ls)
qed

lemma Close2L_NF: assumes "wf_bins1 (map set Bs)"
  shows "wf_bin1' Bs (set B) \<Longrightarrow> \<exists>C'. (Close2L Bs)^** (B,C) ([],C')"
using wf_Close2_less[of "length Bs"]
proof (induction "(set B,set C)" arbitrary: B C rule: wf_induct_rule)
  case less
  show ?case
  proof (cases B)
    case Nil thus ?thesis by blast
  next
    case (Cons x bs)
    then obtain B' C' where step: "Close2L Bs (B,C) (B',C')"
      using Close2L.intros by blast
    note 1 = wf1_Close2L_1[OF step assms less.prems(1)]
    from less(1)[OF Close2_less_step[OF assms Close2_if_Close2L[OF step less(2)], simplified, OF less.prems] 1]
    show ?thesis by (meson converse_rtranclp_into_rtranclp step)
  qed
qed

lemma Close2L_Close2: assumes "wf_bins1 (map set Bs)" "wf_bin1' Bs (set B)"
  "(Close2L Bs)^** (B,[]) ([],C1)" "map set Bs \<turnstile> (set B,{}) \<rightarrow>* ({},C2)" shows "set C1 = C2"
using Close2_eq_Close1 Close2s_if_Close2Ls[OF assms(3,1,2),simplified] assms(4)
  by blast

end

(* While *)
context Earley_Gw
begin

abbreviation "PreCo_L Bs x \<equiv> if is_complete x then Complete_L Bs x else Predict_L (length Bs) x"

fun step2L :: "('n,'t) item list list \<Rightarrow> ('n,'t)item list \<times> ('n,'t) item list \<Rightarrow> ('n,'t) item list \<times> ('n,'t) item list" where
"step2L Bs (x#B, C) =
  (let nexts = PreCo_L Bs x in
     (diff_list (union_list nexts B) (insert_list x C), insert_list x C) )"

definition close2L :: "('n, 't) item list list \<Rightarrow> ('n,'t)item list \<times> ('n, 't) item list \<Rightarrow> (('n, 't) item list \<times> ('n, 't) item list) option" where
"close2L Bs = while_option (\<lambda>(B,C). B \<noteq> []) (step2L Bs)"

lemma Close2L_iff_step2L: "Close2L Bs (B,C) (B',C') \<longleftrightarrow> B \<noteq> [] \<and> step2L Bs (B,C) = (B',C')"
by(auto simp: neq_Nil_conv Close2L.simps)

lemma Close2Ls_if_close2L_Some:
  assumes "close2L Bs (B,C) = Some ([],C')"
  shows "(Close2L Bs)^** (B,C) ([],C')"
proof -
  let ?P = "\<lambda>BC'. (Close2L Bs)^** (B,C) (BC')"
  have "\<And>B C. B\<noteq>[] \<Longrightarrow> ?P (B,C) \<Longrightarrow> ?P (step2L Bs (B,C))"
    by (metis Close2L_iff_step2L old.prod.exhaust rtranclp.rtrancl_into_rtrancl)
  thus ?thesis using while_option_rule[where P = ?P, OF _ assms(1)[unfolded close2L_def]]
    by blast
qed

end

context Earley_Gw_eps
begin

lemma close2L_Some_if_Close2Ls: assumes "wf_bins1 (map set Bs)"
  shows "(Close2L Bs)^** (B,C) ([],C') \<Longrightarrow> wf_bin1' Bs (set B) \<Longrightarrow> close2L Bs (B,C) = Some ([],C')"
proof(induction rule: converse_rtranclp_induct2)
  case refl
  then show ?case by (simp add: close2L_def while_option_unfold)
next
  case (step B C B' C')
  show ?case using step.IH[OF wf1_Close2L_1[OF step(1) assms step.prems]] step.hyps Close2L_iff_step2L
    by (simp add: close2L_def while_option_unfold)
qed

corollary close2L_Some:
  assumes "wf_bins1 (map set Bs)" "wf_bin1' Bs (set B)"
  shows "\<exists>C'. close2L Bs (B,[]) = Some ([],C')"
using assms close2L_Some_if_Close2Ls[of _ _ "[]"] Close2L_NF[of Bs B "[]"]
by (auto simp add: wf_bin1_def)

corollary close2L_Some_iff_Close2Ls: "\<lbrakk> wf_bins1 (map set Bs); wf_bin1' Bs (set B) \<rbrakk> \<Longrightarrow>
  close2L Bs (B,[]) = Some ([],C) \<longleftrightarrow> (Close2L Bs)^** (B,[]) ([],C)"
using Close2Ls_if_close2L_Some close2L_Some_if_Close2Ls by blast

corollary close2L_Some_iff_Close2s: "\<lbrakk> wf_bins1 (map set Bs); wf_bin1' Bs (set B) \<rbrakk> \<Longrightarrow>
  close2L Bs (B,[]) = Some ([],C) \<Longrightarrow> (Close2 (map set Bs))^** (set B,{}) ({},set C)"
by (metis Close2s_if_Close2Ls close2L_Some_iff_Close2Ls empty_set)

end (* Earley_Gw_eps *)

(*unused_thms*)

end