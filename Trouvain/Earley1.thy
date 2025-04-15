theory Earley1
imports "../CFG"
begin

section \<open>Slices\<close>

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


section \<open>Earley recognizer: Abstract inductive definition\<close>

subsection \<open>Earley states\<close>

abbreviation lhs :: "'a prod \<Rightarrow> 'a" where
  "lhs \<equiv> fst"

definition rhs :: "'a prod \<Rightarrow> 'a list" where
  "rhs \<equiv> snd"

datatype 'a state = 
  State (prod: "'a prod") (dot : nat) ("from" : nat)

definition \<alpha> :: "'a state \<Rightarrow> 'a list" where
  "\<alpha> x = take (dot x) (rhs(prod x))"

definition \<beta> :: "'a state \<Rightarrow> 'a list" where 
  "\<beta> x = drop (dot x) (rhs(prod x))"

definition is_complete :: "'a state \<Rightarrow> bool" where
  "is_complete x = (dot x \<ge> length (rhs(prod x)))"

definition next_symbol :: "'a state \<Rightarrow> 'a option" where
  "next_symbol x = (if is_complete x then None else Some (rhs(prod x) ! dot x))"

lemmas state_defs = \<alpha>_def \<beta>_def rhs_def

locale Earley_Gw =
fixes G :: "'a cfg"
fixes w :: "'a list"
begin

definition is_final :: "'a state \<Rightarrow> bool" where
  "is_final x =
    (lhs(prod x) = start G \<and>
    from x = 0 \<and>
    is_complete x)"

definition recognized :: "('a state \<times> nat) set \<Rightarrow> bool" where
  "recognized I \<equiv> \<exists>(x,k) \<in> I. is_final x \<and> k = length w"

definition Init :: "'a state set" where
  "Init = { State r 0 0 | r. r \<in> set (prods G) \<and> lhs r = (start G) }"

definition Predict :: "'a state \<Rightarrow> nat \<Rightarrow> 'a state set" where
  "Predict x k = { State r 0 k | r. r \<in> set (prods G) \<and> next_symbol x = Some (lhs r) }"

definition mv_dot :: "'a state \<Rightarrow> 'a state" where
"mv_dot x \<equiv> State (prod x) (dot x + 1) (from x)"
(* TODO use Complete and Scan? *)
inductive_set Earley :: "('a state \<times> nat) set" where
    Init: "x \<in> Init \<Longrightarrow> (x,0) \<in> Earley"
  | Scan: "\<lbrakk> (x,j) \<in> Earley;  j < length w;  next_symbol x = Some (w!j) \<rbrakk> \<Longrightarrow>
      (mv_dot x, j + 1) \<in> Earley"
  | Predict: "\<lbrakk> (x,k) \<in> Earley; x' \<in> Predict x k \<rbrakk> \<Longrightarrow>
      (x',k) \<in> Earley"
  | Complete: "\<lbrakk> (y,k) \<in> Earley;  is_complete y;  (x,from y) \<in> Earley;
      next_symbol x = Some (lhs(prod y)) \<rbrakk> \<Longrightarrow>
        (mv_dot x, k) \<in> Earley"

definition \<S> :: "nat \<Rightarrow> 'a state set" where
"\<S> i = {x. (x,i) \<in> Earley}"

lemma Earley_eq_\<S>: "(x,i) \<in> Earley \<longleftrightarrow> x \<in> \<S> i"
by(simp add: \<S>_def)

definition accepted :: "bool" where
  "accepted = (\<exists>x \<in> \<S> (length w). is_final x)"


subsection \<open>Well-formedness\<close>

definition wf_state :: "'a state \<Rightarrow> nat \<Rightarrow> bool" where 
  "wf_state x k =
    (prod x \<in> set (prods G) \<and> 
    dot x \<le> length (rhs(prod x)) \<and>
    from x \<le> k \<and> 
    k \<le> length w)"

lemma wf_Init:
  assumes "x \<in> Init"
  shows "wf_state x 0"
  using assms unfolding Init_def wf_state_def by auto

lemma wf_Scan:
  assumes "wf_state x j" "w!j = a" "j < length w" "next_symbol x = Some a"
  shows "wf_state (mv_dot x) (j+1)"
  using assms unfolding wf_state_def mv_dot_def
  by (auto simp: state_defs is_complete_def next_symbol_def split: if_splits)

lemma wf_Predict:
  "\<lbrakk> wf_state x k; x' \<in> Predict x k \<rbrakk> \<Longrightarrow> wf_state x' k"
unfolding wf_state_def Predict_def by (auto)

lemma wf_Complete:
  assumes "wf_state x j" "j = from y" "wf_state y k"
  assumes "is_complete y" "next_symbol x = Some (lhs(prod y))"
  shows "wf_state (mv_dot x) k"
  using assms unfolding wf_state_def is_complete_def next_symbol_def mv_dot_def
  by (auto split: if_splits)

lemma wf_Earley:
  assumes "(x,k) \<in> Earley"
  shows "wf_state x k"
  using assms wf_Init wf_Scan wf_Predict wf_Complete
  by (induction rule: Earley.induct) fast+

lemmas wf_EarleyS = wf_Earley[unfolded Earley_eq_\<S>]

subsection \<open>Soundness\<close>

definition sound_state :: "'a state \<Rightarrow> nat \<Rightarrow> bool" where
  "sound_state x k = (G \<turnstile> \<alpha> x \<Rightarrow>* slice (from x) k w)"

lemma sound_Init:
  assumes "x \<in> Init"
  shows "sound_state x 0"
proof -
  have "(lhs(prod x), rhs(prod x)) \<in> set (prods G)"
    using assms by (auto simp add: Init_def state_defs)
  hence "G \<turnstile> [lhs(prod x)] \<Rightarrow>* rhs(prod x)"
    using deriv1_if_valid_prod by (metis r_into_rtranclp)
  thus "sound_state x 0"
    using assms unfolding Init_def sound_state_def by (auto simp add: \<alpha>_def slice_empty)
qed

lemma sound_Scan:
  assumes "x = State r d i" "wf_state x j" "sound_state x j"
  assumes "w!j = a" "j < length w" "next_symbol x = Some a"
  shows "sound_state (State r (d+1) i) (j+1)"
proof -
  define x' where [simp]: "x' = State r (d+1) i"
  have *: "\<alpha> x' = \<alpha> x @ [w!j]"
    using assms(1,4,6) by (auto simp: state_defs next_symbol_def is_complete_def take_Suc_conv_app_nth split: if_splits)
  have "slice i (j+1) w = slice i j w @ [w!j]"
    using * assms(1,2,5) by (auto simp: slice_append_nth wf_state_def)
  moreover have "G \<turnstile> \<alpha> x \<Rightarrow>* slice i j w"
    using assms(1,3) by (simp add:  sound_state_def)
  ultimately show ?thesis
    using * by (simp add: deriv_apppend sound_state_def)
qed

lemma sound_Predict:
  assumes "wf_state x k" "sound_state x k"
  assumes "x' \<in> Predict x k"
  shows "sound_state x' k"
  using assms unfolding Predict_def sound_state_def state_defs by (auto simp: deriv1_if_valid_prod slice_empty)

lemma sound_Complete:
  assumes "x = State r\<^sub>x d\<^sub>x i" "wf_state x j" "sound_state x j"
  assumes "y = State r\<^sub>y d\<^sub>y j" "wf_state y k" "sound_state y k"
  assumes "is_complete y" "next_symbol x = Some (lhs(prod y))"
  shows "sound_state (State r\<^sub>x (d\<^sub>x + 1) i) k"
proof -
  have *: "G \<turnstile> [lhs r\<^sub>y] \<Rightarrow> rhs r\<^sub>y"
    using assms(4,5)unfolding rhs_def wf_state_def by (simp add: deriv1_if_valid_prod)
  moreover have *: "G \<turnstile> rhs r\<^sub>y \<Rightarrow>* slice j k w"
    using assms(4,6,7) by (auto simp: sound_state_def is_complete_def state_defs)
  ultimately have "G \<turnstile> [lhs r\<^sub>y] \<Rightarrow>* slice j k w"
    by simp
  moreover have "G \<turnstile> take d\<^sub>x (rhs r\<^sub>x) \<Rightarrow>* slice i j w"
    using assms(1,3) by (auto simp: sound_state_def \<alpha>_def)
  moreover have "rhs r\<^sub>x ! d\<^sub>x = lhs r\<^sub>y" and "d\<^sub>x < length(rhs r\<^sub>x)"
    using assms(1,4,8) unfolding next_symbol_def is_complete_def by(auto split: if_splits)
  ultimately have "G \<turnstile> take (d\<^sub>x+1) (rhs r\<^sub>x) \<Rightarrow>* slice i j w @ slice j k w"
    using assms(1,8) apply(simp add: take_Suc_conv_app_nth)
    by (meson deriv_apppend deriv_prepend rtranclp_trans)
  moreover have "i \<le> j"  "j \<le> k"
    using assms(1,2,4,5) by (simp_all add: wf_state_def)
  ultimately show ?thesis
    unfolding sound_state_def \<alpha>_def by (simp add: slice_concat)
qed

lemma sound_Earley:
  assumes "(x,k) \<in> Earley"
  shows "sound_state x k"
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
    using sound_Complete wf_Earley unfolding mv_dot_def by (metis state.collapse)
qed

theorem soundness_Earley:
assumes "recognized Earley" shows "G \<turnstile> [start G] \<Rightarrow>* w"
proof -
  obtain x where *: "(x,length w) \<in> Earley" and "is_final x"
    using assms recognized_def by auto
  hence "prod x \<in> set (prods G)" "lhs(prod x) = start G" "from x = 0" "dot x \<ge> length (rhs(prod x))"
    "\<alpha> x = rhs(prod x)"
    using wf_Earley[OF *] unfolding is_final_def is_complete_def wf_state_def \<alpha>_def by auto
  with sound_Earley[OF *] deriv1_if_valid_prod[of "lhs(prod x)" "rhs(prod x)"]
  show ?thesis 
    apply(simp add: sound_state_def rhs_def)
    by (metis converse_rtranclp_into_rtranclp prod.collapse)
qed

corollary accpted_sound: "accepted \<Longrightarrow> G \<turnstile> [start G] \<Rightarrow>* w" (* used in Paper *)
using soundness_Earley unfolding \<S>_def accepted_def recognized_def by blast


subsection \<open>Completeness\<close>

text \<open>A canonical proof:
 by induction on the length of the derivation
 with a nested induction on the length of the right-hand side of the production.\<close>

lemma Earley_complete_induction:
  "\<lbrakk>j \<le> k; k \<le> length w; x = State (A,\<gamma>) d i; (x,j) \<in> Earley;
    G \<turnstile> \<beta> x \<Rightarrow>(n) slice j k w \<rbrakk> \<Longrightarrow> (State (A,\<gamma>) (length \<gamma>) i, k) \<in> Earley"
proof (induction n arbitrary: x d i j k A \<gamma> rule: less_induct)
  case (less n)
  have "\<exists>m \<le> n. G \<turnstile> \<beta> x \<Rightarrow>(m) slice j k w" using less.prems(5) by auto
  from less.prems(1,3,4) this show ?case
  proof (induction "\<beta> x" arbitrary: x d j)
    case Nil
    have "x = State (A,\<gamma>) (length \<gamma>) i" using Nil.hyps Nil.prems(3,4) \<open>x = _\<close> wf_Earley[of x]
      unfolding wf_state_def state_defs by auto
    have "\<exists>m \<le> n. G \<turnstile> [] \<Rightarrow>(m) slice j k w"
      using Nil by auto
    hence "slice j k w = []"
      using Derivation_from_empty by (metis relpowp_imp_rtranclp)
    hence "j = k"
      unfolding slice_drop_take using \<open>j \<le> k\<close> less.prems(2) by simp
    thus ?case
      using \<open>x = State (A, \<gamma>) (length \<gamma>) i\<close> Nil.prems by blast
  next
    case (Cons s ss)
    from Cons.prems(4) obtain m where m: "m \<le> n" "G \<turnstile> \<beta> x \<Rightarrow>(m) slice j k w" by blast
    obtain j' n1 n2 where *: 
      "G \<turnstile> [s] \<Rightarrow>(n1) slice j j' w"
      "G \<turnstile> ss \<Rightarrow>(n2) slice j' k w"
      "j \<le> j'" "j' \<le> k" "n1 \<le> m" "n2 \<le> m"
      using Derivation_concat_split[of m G "[s]" ss "slice j k w"] slice_concat_Ex
        \<open>j \<le> k\<close> Cons.hyps(2) m(2)
      by (metis append_Cons append_Nil)
    let ?x = "State (A, \<gamma>) (d+1) i"
    have nxt: "next_symbol x = Some s"
      using Cons.hyps(2) unfolding state_defs(2) next_symbol_def is_complete_def
      by (auto, metis nth_via_drop)
    hence "(?x, j') \<in> Earley"
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
      hence "(mv_dot x, j') \<in> Earley"
        using Earley.Scan[OF \<open>(x,j) \<in> Earley\<close> \<open>j < length w\<close>] nxt \<open>j' = j + 1\<close>
        by (auto)
      thus ?thesis
        by (simp add: \<open>x = _\<close> mv_dot_def)
    next
      case (Suc n0)
      then obtain u where "G \<turnstile> [s] \<Rightarrow> u" and n0: "G \<turnstile> u \<Rightarrow>(n0) slice j j' w"
        using *(1) by (metis relpowp_Suc_E2)
      hence prod: "(s, u) \<in> set (prods G)"
        using *(1)
        by (smt (verit, ccfv_threshold) Cons_eq_append_conv Derivation1_from_empty Nil_is_append_conv append.right_neutral append_Cons deriv1_if_valid_prod list.inject self_append_conv2 step1.cases)
      define y where y_def: "y = State (s, u) 0 j"
      have **: "G \<turnstile> \<beta> y \<Rightarrow>(n0) slice j j' w"
        using n0 by (auto simp: state_defs y_def)
      have "(y,j) \<in> Earley"
        using y_def \<open>(x,j) \<in> Earley\<close> nxt *(1) prod
        by (auto simp: state_defs Earley.Predict Predict_def)
      have "(State (s,u) (length u) j, j') \<in> Earley"
        using less.IH [OF _ _ _ y_def \<open>(y,j) \<in> Earley\<close> **] *(3,4,5) m(1) Suc less.prems(2)
        by linarith
      from Earley.Complete[OF this, of x] show ?thesis
        using nxt Cons.prems(2,3) by (simp add: mv_dot_def is_complete_def rhs_def)
    qed
    moreover have "ss = \<beta> ?x"
      using Cons.hyps(2) \<open>x = _\<close> unfolding state_defs(2)
      by (auto, metis List.list.sel(3) drop_Suc drop_tl)
    ultimately show ?case
      using Cons.hyps(1) *(2,4,6) m(1) le_trans by blast
  qed
qed

theorem Earley_complete:
  assumes "G \<turnstile> [start G] \<Rightarrow>* w" "nonterminals G \<inter> set w = {}"
  shows "recognized Earley"
proof -
  obtain \<alpha> n where *: "(start G ,\<alpha>) \<in> set (prods G)" "G \<turnstile> \<alpha> \<Rightarrow>(n) w"
    using Derivation_start1 assms by (metis rtranclp_imp_relpowp)
  define x where x_def: "x = State (start G, \<alpha>) 0 0"
  have 1: "(x,0) \<in> Earley"
    using x_def Earley.Init *(1) by (fastforce simp: Init_def)
  have 2: "G \<turnstile> (\<beta> x) \<Rightarrow>(n) (slice 0 (length w) w)"
    using *(2) x_def by (simp add: state_defs)
  have "(State (start G,\<alpha>) (length \<alpha>) 0, length w) \<in> Earley"
    using Earley_complete_induction[OF _ _ _ 1 2] x_def by auto
  thus ?thesis
    unfolding recognized_def is_final_def by (auto simp: is_complete_def state_defs, force)
qed

(* Completeness also if there are nonterminals in input \<open>w\<close> ! *)

lemma Derivation_start_nonstart:
  assumes "\<G> \<turnstile> [start \<G>] \<Rightarrow>(n) w" "w \<noteq> [start \<G>]"
  shows "\<exists>\<alpha> m. n = Suc m \<and> \<G> \<turnstile> \<alpha> \<Rightarrow>(m) w \<and> (start \<G>,\<alpha>) \<in> set (prods \<G>)"
proof (cases n)
  case 0
  thus ?thesis
    using assms by (auto)
next
  case (Suc m)
  then obtain \<alpha> where *: "\<G> \<turnstile> [start \<G>] \<Rightarrow> \<alpha>" "\<G> \<turnstile> \<alpha> \<Rightarrow>(m) w"
    using assms by (metis relpowp_Suc_E2)
  from  step1.cases[OF *(1)] have "(start \<G>, \<alpha>) \<in> set (prods \<G>)"
    by (simp add: Cons_eq_append_conv) blast
  thus ?thesis using *(2) Suc by auto
qed

(*
Only the decomposition into n+1 steps is different to the earlier completeness proof
Instead of \<open>w \<noteq> [start G]\<close> one could also require \<open>[start G] \<Rightarrow>(n+1) w\<close>, but that is a bit odd.
*)
theorem Earley_complete_NT:
  assumes "G \<turnstile> [start G] \<Rightarrow>* w" "w \<noteq> [start G]"
  shows "recognized Earley"
proof -
  obtain \<alpha> n where *: "(start G ,\<alpha>) \<in> set (prods G)" "G \<turnstile> \<alpha> \<Rightarrow>(n) w"
    using Derivation_start_nonstart assms by(metis rtranclp_imp_relpowp)
  define x where x_def: "x = State (start G, \<alpha>) 0 0"
  have 1: "(x,0) \<in> Earley"
    using x_def Earley.Init *(1) by (fastforce simp: Init_def)
  have 2: "G \<turnstile> (\<beta> x) \<Rightarrow>(n) (slice 0 (length w) w)"
    using *(2) x_def by (simp add: state_defs)
  have "(State (start G,\<alpha>) (length \<alpha>) 0, length w) \<in> Earley"
    using Earley_complete_induction[OF _ _ _ 1 2] x_def by auto
  thus ?thesis
    unfolding recognized_def is_final_def by (auto simp: is_complete_def state_defs, force)
qed

(* Only of historic interest:
  Streamlined version of the proof by Martin Rau
  with the derivation data type already removed in favour of the length of a derivation
*)

definition partially_completed :: "nat \<Rightarrow> bool" where
  "partially_completed n = (\<forall>i j x a m.
    i \<le> j \<and> j \<le> length w \<and>
    (x,i) \<in> Earley \<and> next_symbol x = Some a \<and>
    G \<turnstile> [a] \<Rightarrow>(m) slice i j w \<and> m \<le> n \<longrightarrow>
    (mv_dot x, j) \<in> Earley)"

lemma partially_completed_upto:
  assumes "partially_completed n"
  shows "\<lbrakk>j \<le> k; k \<le> length w; x = State (A,\<gamma>) d i; (x,j) \<in> Earley;
          m \<le> n; G \<turnstile> \<beta> x \<Rightarrow>(m) slice j k w \<rbrakk> \<Longrightarrow> (State (A,\<gamma>) (length \<gamma>) i, k) \<in> Earley"
proof (induction "\<beta> x" arbitrary: d j k x m)
  case Nil
  have "x = State (A,\<gamma>) (length \<gamma>) i" using Nil(1,4,5,6) wf_Earley[of x]
    unfolding wf_state_def state_defs by auto
  have "G \<turnstile> [] \<Rightarrow>(m) slice j k w"
    using Nil.hyps Nil.prems(6) by auto
  hence "slice j k w = []"
    using Derivation_from_empty by (metis relpowp_imp_rtranclp)
  hence "j = k"
    unfolding slice_drop_take using Nil.prems(1,2) by simp
  thus ?case
    using \<open>x = State (A, \<gamma>) (length \<gamma>) i\<close> Nil.prems(4) by blast
next
  case (Cons b bs)
  obtain j' m1 m2 where *: 
    "G \<turnstile> [b] \<Rightarrow>(m1) slice j j' w"
    "G \<turnstile> bs \<Rightarrow>(m2) slice j' k w"
    "j \<le> j'" "j' \<le> k" "m1 \<le> m" "m2 \<le> m"
    using Derivation_concat_split[of m G "[b]" bs "slice j k w"] slice_concat_Ex
    using Cons.hyps(2) Cons.prems(1,6)
    by (metis append_Cons append_Nil)
  have "next_symbol x = Some b"
    using Cons.hyps(2) unfolding state_defs(2) next_symbol_def is_complete_def by (auto, metis nth_via_drop)
  hence "(State (A, \<gamma>) (d+1) i, j') \<in> Earley"
    using assms unfolding partially_completed_def
    using Cons.prems(2-5) *(1,3-5)
    using mv_dot_def by fastforce
  moreover have "bs = \<beta> (State (A,\<gamma>) (d+1) i)"
    using Cons.hyps(2) Cons.prems(3) unfolding state_defs(2)
    by (auto, metis List.list.sel(3) drop_Suc drop_tl)
  ultimately show ?case
    using Cons.hyps(1) *(2,4,6) Cons.prems(2,5) assms le_trans by blast
qed

lemma partially_completed_Earley:
  "partially_completed n"
proof -
  have "(mv_dot x, j) \<in> Earley"
    if
    "i \<le> j" "j \<le> length w"
    "(x,i) \<in> Earley"
    "next_symbol x = Some a"
    "G \<turnstile> [a] \<Rightarrow>(n) slice i j w"
    for i j x a n
    using that
  proof (induction n arbitrary: i j x a rule: nat_less_induct)
    case (1 n)
    show ?case
    proof (cases n)
      case 0
      hence "[a] = slice i j w"
        using "1.prems"(5) by auto
      from slice_singleton[OF \<open>j \<le> length w\<close> this] have "j = i+1" .
      hence "i < length w"
        using \<open>j \<le> length w\<close> by simp
      hence "w!i = a"
        using slice_nth \<open>[a] = slice i j w\<close> \<open>j = i + 1\<close> by fastforce
      hence "(mv_dot x, j) \<in> Earley"
        using Earley.Scan "1.prems"(3-5) \<open>i < length w\<close> \<open>j = i + 1\<close> by (metis)
      thus ?thesis
        by (simp add: mv_dot_def \<open>j = i + 1\<close>)
    next
      case (Suc m)
      then obtain \<alpha> where *: "G \<turnstile> [a] \<Rightarrow> \<alpha>" "G \<turnstile> \<alpha> \<Rightarrow>(m) slice i j w"
        using "1.prems"(5) by (metis relpowp_Suc_E2)
      hence prod: "(a, \<alpha>) \<in> set (prods G)"
        using *(1)
        by (smt (verit, ccfv_threshold) Cons_eq_append_conv Derivation1_from_empty Nil_is_append_conv append.right_neutral append_Cons deriv1_if_valid_prod list.inject self_append_conv2 step1.cases)
      have pc: "partially_completed m"
        unfolding partially_completed_def using "1.IH" Suc by (meson le_imp_less_Suc)
      define y where y_def: "y = State (a ,\<alpha>) 0 i"
      have **: "G \<turnstile> \<beta> y \<Rightarrow>(m) slice i j w"
        using *(2) by (auto simp: state_defs y_def)
      have "(y,i) \<in> Earley"
        using y_def "1.prems"(3,4,5) prod by (auto simp: state_defs Earley.Predict Predict_def)
      have "(State (a,\<alpha>) (length \<alpha>) i, j) \<in> Earley"
        using partially_completed_upto[OF pc "1.prems"(1-2) y_def \<open>(y,i) \<in> Earley\<close> le_refl **] .
      thus ?thesis
        using Earley.Complete "1.prems"(3,4)
        by (simp add: mv_dot_def is_complete_def rhs_def)
    qed
  qed
  thus ?thesis unfolding partially_completed_def by blast
qed

theorem completeness_Earley:
  assumes "G \<turnstile> [start G] \<Rightarrow>* w" "nonterminals G \<inter> set w = {}"
  shows "recognized Earley"
proof -
  obtain \<alpha> n where *: "(start G ,\<alpha>) \<in> set (prods G)" "G \<turnstile> \<alpha> \<Rightarrow>(n) w"
    using Derivation_start1 assms by (metis rtranclp_imp_relpowp)
  define x where x_def: "x = State (start G, \<alpha>) 0 0"
  have 1: "(x,0) \<in> Earley"
    using x_def Earley.Init *(1) by (fastforce simp: Init_def)
  have 2: "G \<turnstile> (\<beta> x) \<Rightarrow>(n) (slice 0 (length w) w)"
    using *(2) x_def by (simp add: state_defs)
  have "(State (start G,\<alpha>) (length \<alpha>) 0, length w) \<in> Earley"
    using partially_completed_upto[OF partially_completed_Earley _ _ _ _ _ 2] wf_Earley 1 x_def by auto
  thus ?thesis
    unfolding recognized_def is_final_def by (auto simp: is_complete_def state_defs, force)
qed

(* end of unused *)


subsection \<open>Correctness\<close>

theorem correctness_Earley:
  assumes "nonterminals G \<inter> set w = {}"
  shows "recognized Earley \<longleftrightarrow> G \<turnstile> [start G] \<Rightarrow>* w"
  using assms soundness_Earley Earley_complete by blast

theorem correctness_Earley_NT:
  assumes "w \<noteq> [start G]"
  shows "recognized Earley \<longleftrightarrow> G \<turnstile> [start G] \<Rightarrow>* w"
  using assms soundness_Earley Earley_complete_NT by blast


subsection \<open>Finiteness\<close>

fun mk_state :: "'a prod \<times> nat \<times> nat \<times> nat \<Rightarrow> 'a state \<times> nat" where
  "mk_state (r, d, k, ends) = (State r d k, ends)" 

lemma finite_wf_state:
  shows "finite { (x,k). wf_state x k }"
proof -
  define M where "M = Max { length (rhs r) | r. r \<in> set (prods G) }"
  define Top where "Top = (set (prods G) \<times> {0..M} \<times> {0..length w} \<times> {0..length w})"
  hence "finite Top"
    using finite_cartesian_product finite by blast
  have "inj_on mk_state Top"
    unfolding Top_def inj_on_def by simp
  hence "finite (mk_state ` Top)"
    using finite_image_iff \<open>finite Top\<close> by auto
  have "{ (x,k). wf_state x k } \<subseteq> mk_state ` Top"
  proof auto
    fix x k
    assume "wf_state x k"
    then obtain r d j where *: "x = State r d j"
      "r \<in> set (prods G)" "d \<le> length (rhs(prod x))" "j \<le> k" "k \<le> length w"
      unfolding wf_state_def using state.exhaust_sel le_trans by blast
    hence "length (rhs r) \<in> { length (rhs r) | r. r \<in> set (prods G) }"
      using *(1,2) by blast
    moreover have "finite { length (rhs r) | r. r \<in> set (prods G) }"
      using finite finite_image_set[of "\<lambda>x. x \<in> set (prods G)"] by fastforce
    ultimately have "M \<ge> length (rhs r)"
      unfolding M_def by simp
    hence "d \<le> M"
      using *(1,3) by (metis state.sel(1) le_trans)
    hence "(r, d, j, k) \<in> Top"
      using *(2,4,5) unfolding Top_def by simp
    thus "(x,k) \<in> mk_state ` Top"
      using *(1) by force
  qed
  thus ?thesis
    using \<open>finite (mk_state ` Top)\<close> rev_finite_subset by auto
qed


section \<open>Earley recognizer: Standard recusrive/inductive definition\<close>

definition Scan :: "'a state set \<Rightarrow> nat \<Rightarrow> 'a state set" where
  "Scan B k = { mv_dot x | x. x \<in> B \<and> next_symbol x = Some (w!k) }"

inductive_set Close :: "'a state set list \<Rightarrow> 'a state set \<Rightarrow> 'a state set" for Bs B where
    Init: "x \<in> B \<Longrightarrow> x \<in> Close Bs B"
  | Predict: "\<lbrakk> x \<in> Close Bs B; x' \<in> Predict x (length Bs) \<rbrakk> \<Longrightarrow> x' \<in> Close Bs B"
  | Complete: "\<lbrakk> y \<in> Close Bs B;  is_complete y;
      from y = length Bs \<longrightarrow> x \<in> Close Bs B; from y < length Bs \<longrightarrow> x \<in> Bs ! from y;
      next_symbol x = Some (lhs(prod y)) \<rbrakk> \<Longrightarrow>
        mv_dot x \<in> Close Bs B"

text \<open>Cannot just write \<open>x \<in> (Bs @ [Close Bs B]) ! from y\<close>.
The monotonicity prover cannot deal with it and it is unclear what \<open>monos\<close> one would
need to add. However, we can derive that version easily:\<close>

lemma Close_Complete:(* used in Paper *)
  "\<lbrakk> y \<in> Close Bs B;  is_complete y; x \<in> (Bs @ [Close Bs B]) ! from y;
     next_symbol x = Some (lhs(prod y))
   \<rbrakk> \<Longrightarrow> mv_dot x \<in> Close Bs B"
apply(simp add: nth_append)
by (metis Close.Complete diff_is_0_eq' linorder_not_le nat_neq_iff nth_Cons_0)

abbreviation "wf_bin B k \<equiv> \<forall>s \<in> B. wf_state s k"
abbreviation "wf_bins Bs \<equiv> \<forall>k < length Bs. wf_bin (Bs!k) k"

fun bins :: "nat \<Rightarrow> 'a state set list" where
"bins 0 = [Close [] Init]" |
"bins (Suc k) = (let Bs = bins k in Bs @ [Close Bs (Scan (last Bs) k)])"


subsection \<open>Correctness\<close>

lemma length_bins[simp]: "length (bins k) = k+1"
by(induction k) (auto simp: Let_def)

corollary bins_nonempty: "bins k \<noteq> []"
using length_bins[of k] by (auto simp del: length_bins)

lemma take_Suc_bins: "m \<le> n \<Longrightarrow> take (Suc m) (bins n) = bins m"
apply(induction n arbitrary: m)
apply simp
apply(simp add: Let_def)
by (smt (verit) length_bins Suc_eq_plus1 add.commute add_diff_cancel_right' append.right_neutral bins.simps(2) diff_is_0_eq le_SucE le_add2 length_Cons list.size(3) take0 take_all)

lemma nth_bins_eq: "\<lbrakk> i \<le> m; m \<le> n \<rbrakk> \<Longrightarrow> bins m ! i = bins n ! i"
by (metis le_imp_less_Suc nth_take take_Suc_bins)

lemma Earley0_if_Close_Init: "(x,0) \<in> Earley \<Longrightarrow> x \<in> Close [] Init"
proof(induction x "0::nat" rule: Earley.induct)
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
  thus ?case using wf_Earley[OF Complete.hyps(1)] unfolding wf_state_def
    using Close.Complete[OF Complete.hyps(2,3)] by (simp)
qed

lemma Close_Init_if_Earley0: "x \<in> Close [] Init \<Longrightarrow> (x,0) \<in> Earley"
apply(induction rule: Close.induct)
  using Earley.Init apply blast
apply simp
  using Earley.Predict apply blast
apply simp
  by (metis Earley.Complete le_zero_eq wf_Earley wf_state_def)

lemma S0: "\<S> 0 = Close [] Init"
unfolding \<S>_def using Close_Init_if_Earley0 Earley0_if_Close_Init
by blast

lemma S_Suc1:
assumes "\<forall>i\<le>n. bins n ! i = \<S> i" "n < length w"
shows "x \<in> Close (bins n) (Scan (\<S> n) n)  \<Longrightarrow> x \<in> \<S> (Suc n)"
proof (induction rule: Close.induct)
  case (Init x)
  thus ?case using assms(2) unfolding \<S>_def Scan_def by (auto intro: Earley.Scan[simplified])
next
  case (Predict x x')
  thus ?case using Earley.Predict Earley_eq_\<S> by auto
next
  case (Complete y x)
  have "from y = Suc n \<or> from y < Suc n"
    using wf_EarleyS[OF Complete.IH(1)] unfolding wf_state_def by auto
  with assms(1) Complete Earley.Complete show ?case unfolding \<S>_def by (auto)
qed

lemma S_Suc2:
  "(x,Suc n) \<in> Earley \<Longrightarrow> \<forall>i\<le>n. bins n ! i = \<S> i \<Longrightarrow> x \<in> Close (bins n) (Scan (\<S> n) n)"
proof (induction x "Suc n" arbitrary: n rule: Earley.induct)
  case (Scan)
  thus ?case unfolding Scan_def
    by (metis (mono_tags, lifting) Close.Init Earley_eq_\<S> Suc_eq_plus1 add_right_imp_eq mem_Collect_eq)
next
  case (Predict)
  thus ?case
    by (metis (no_types, lifting) Earley_Gw.Close.Predict Earley_Gw.length_bins Suc_eq_plus1)
next
  case (Complete y x)
  have "from y = Suc n \<or> from y < Suc n"
    using wf_Earley[OF Complete.hyps(1)] unfolding wf_state_def by auto
  thus ?case
  proof
    assume "from y = Suc n"
    thus ?thesis
      using Complete.prems(1) Complete.hyps(3,5,6) Close.Complete[OF Complete.hyps(2)] length_bins
      by (metis (mono_tags, lifting) Suc_eq_plus1 less_irrefl_nat)
  next
    assume "from y < Suc n"
    thus ?thesis using Complete
      by (metis (no_types, lifting) Close.Complete Earley_eq_\<S> Suc_eq_plus1 le_SucE length_bins nless_le)
  qed
qed

lemma S_Suc: "\<lbrakk> n < length w; \<forall>i \<le> n. bins n ! i = \<S> i \<rbrakk>
  \<Longrightarrow> \<S> (Suc n) = Close (bins n) (Scan (\<S> n) n)"
using S_Suc1 S_Suc2 unfolding \<S>_def by auto

lemma bins_eq_\<S>_gen: "n \<le> length w \<Longrightarrow> \<forall>i \<le> n. bins n ! i = \<S> i"
proof(induction n)
  case 0
  thus ?case by (simp add: S0)
next
  case (Suc n)
  then have "n < length w" by auto
  hence IH: "\<forall>i\<le>n. bins n ! i = \<S> i" using Suc.IH by auto
  hence *: "\<forall>i\<le>n. bins (Suc n) ! i = \<S> i" by (metis le_add2 nth_bins_eq plus_1_eq_Suc)
  have "bins (Suc n) ! (Suc n) = \<S> (Suc n)" using * S_Suc[OF \<open>n < length w\<close> IH] bins_nonempty
    by(simp add: Let_def nth_append last_conv_nth)
  thus ?case using * by (metis le_SucE)
qed

text \<open>Correctness w.r.t. abstract @{const Earley}/@{const \<S>} definition:\<close>

corollary bins_eq_\<S>:(* used in Paper *) "i \<le> length w \<Longrightarrow> bins (length w) ! i = \<S> i"
using bins_eq_\<S>_gen[of "length w"] by blast


subsection \<open>Simplification: \<open>\<epsilon>\<close>-free Grammars\<close>

definition wf_state1 :: "'a state \<Rightarrow> nat \<Rightarrow> bool" where 
"wf_state1 x k = (wf_state x k \<and> (is_complete x \<longrightarrow> from x < k))"

definition "wf_bin1 B k = (\<forall>x \<in> B. wf_state1 x k)"
definition "wf_bins1 Bs = (\<forall>k < length Bs. wf_bin1 (Bs!k) k)"

text \<open>Like @{const Close}, but in \<open>Complete\<close>, only one state is from the current state set:\<close>

inductive_set Close1 :: "'a state set list \<Rightarrow> 'a state set \<Rightarrow> 'a state set" for Bs B where
    Init: "x \<in> B \<Longrightarrow> x \<in> Close1 Bs B"
  | Predict: "\<lbrakk> x \<in> Close1 Bs B; x' \<in> Predict x (length Bs) \<rbrakk> \<Longrightarrow> x' \<in> Close1 Bs B"
  | Complete: "\<lbrakk> y \<in> Close1 Bs B;  is_complete y; x \<in> Bs ! from y;
      next_symbol x = Some (lhs(prod y)) \<rbrakk> \<Longrightarrow>
        mv_dot x \<in> Close1 Bs B"

definition "\<epsilon>_free = (\<forall>r \<in> set(prods G). length(rhs r) > 0)"

end (* Earley_Gw *)

locale Earley_Gw_eps = Earley_Gw +
assumes \<epsilon>: \<epsilon>_free
begin

lemma wf1_Predict:
  "\<lbrakk> wf_state1 x k; x' \<in> Predict x k \<rbrakk> \<Longrightarrow> wf_state1 x' k"
using \<epsilon> unfolding wf_state1_def wf_state_def Predict_def is_complete_def \<epsilon>_free_def by (auto)

(* does not need \<epsilon> *)
lemma wf1_Complete:
  assumes "wf_state1 x j" "j = from y" "wf_state1 y k"
  assumes "is_complete y" "next_symbol x = Some (lhs(prod y))"
  shows "wf_state1 (mv_dot x) k"
  using assms unfolding wf_state1_def wf_state_def is_complete_def next_symbol_def mv_dot_def
  by (auto split: if_splits)

lemma wf_state1_Close1: assumes "wf_bins1 Bs" "wf_bin1 B (length Bs)"
shows "y \<in> Close1 Bs B \<Longrightarrow> wf_state1 y (length Bs)"
proof (induction rule: Close1.induct)
  case (Init x)
  thus ?case using assms(2) unfolding wf_bins1_def wf_bin1_def by blast
next
  case (Predict x x')
  thus ?case using Close1.Predict wf1_Predict by blast
next
  case (Complete y x)
  show ?case using Complete.IH Complete.hyps assms(1) wf1_Complete wf_state1_def
    unfolding wf_bins1_def wf_bin1_def by blast
qed

lemma Close_if_Close1: assumes "wf_bins1 Bs" "wf_bin1 B (length Bs)"
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
      wf_state1_Close1[OF assms Complete.hyps(1)] unfolding wf_state1_def
    by auto
qed

lemma Close1_if_Close: assumes "wf_bins1 Bs" "wf_bin1 B (length Bs)"
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
      wf_state1_Close1[OF assms] unfolding wf_state1_def by blast
qed

lemma Close1_eq_Close: assumes "wf_bins1 Bs" "wf_bin1 B (length Bs)"
shows "Close1 Bs B = Close Bs B"
using Close1_if_Close[OF assms] Close_if_Close1[OF assms] by blast

end (* Earely_Gw_eps *)


subsection "Towards a single-pass worklist completion algorithm"

(* The worklist algorithm is quite generic and does not need \<epsilon> *)

context Earley_Gw
begin

definition "Complete Bs y = mv_dot ` {x. x \<in> Bs ! from y \<and> next_symbol x = Some (lhs(prod y))}"

(* TODO? Generic workset algorithm parameterized with next-function? *)

inductive Close2 :: "'a state set list \<Rightarrow> 'a state set * 'a state set \<Rightarrow> 'a state set * 'a state set \<Rightarrow> bool"
("(_ \<turnstile> _ \<rightarrow> _)" [50, 0, 50] 50)
  for Bs where
    Predict: "\<lbrakk> x \<in> B; next_symbol x \<noteq> None \<rbrakk> \<Longrightarrow>
    Close2 Bs (B,C) (B \<union> Predict x (length Bs) - (C \<union> {x}), insert x C)"
  | Complete: "\<lbrakk> x \<in> B; next_symbol x = None \<rbrakk> \<Longrightarrow>
    Close2 Bs (B,C) ((B \<union> Complete Bs x) - (C \<union> {x}), (C \<union> {x}))"
(* Better: (todo - {x}) \<union> (Predict x (length Bs) - insert x done) *)

lemmas Close2_induct = Close2.induct[split_format(complete), consumes 1, case_names Predict Complete]

abbreviation Close2_steps ("(_ \<turnstile> _ \<rightarrow>* _)" [50, 0, 50] 50) where
"Bs \<turnstile> p \<rightarrow>* p' \<equiv> (Close2 Bs)^** p p'"

definition "close2 Bs B = (SOME C. Bs \<turnstile> (B,{}) \<rightarrow>* ({},C))"

lemma Close2_forward:
  "\<lbrakk> Bs \<turnstile> (B,C) \<rightarrow> (B',C'); B \<inter> C = {}; x \<in> B; x \<notin> B' \<rbrakk> \<Longrightarrow>
   ((next_symbol x \<noteq> None \<and> B' = B \<union> Predict x (length Bs) - insert x C) \<or>
    (next_symbol x = None \<and> B' = (B \<union> Complete Bs x) - insert x C)) \<and> C' = insert x C"
by(auto simp add: Close2.simps)

lemma Close2_disj: "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> B \<inter> C = {} \<Longrightarrow> B' \<inter> C' = {}"
by(auto simp add: Close2.simps)

lemma Close2_steps_disj: "Bs \<turnstile> (B,C) \<rightarrow>* (B',C') \<Longrightarrow> B \<inter> C = {} \<Longrightarrow> B' \<inter> C' = {}"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case .
next
  case step
  thus ?case using Close2_disj by blast
qed

lemma Close1_incr: "B \<subseteq> Close1 Bs B"
by (simp add: Close1.Init subsetI)

theorem Close2_step_incr2:
  "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> B \<union> C \<subset> B' \<union> C' \<or> B \<union> C = B' \<union> C' \<and> B' \<subseteq> B"
by(auto simp add: Close2.simps)

theorem Close2_step_incr:
  "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> B \<union> C \<subseteq> B' \<union> C'"
using Close2_step_incr2 by blast

theorem Close2_steps_incr2:
  "Bs \<turnstile> (B,C) \<rightarrow>* (B',C') \<Longrightarrow> B \<union> C \<subseteq> B' \<union> C'"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case by blast
next
  case (step) thus ?case using Close2_step_incr by blast
qed

theorem Close2_steps_incr:
  "Bs \<turnstile> (B,C) \<rightarrow>* (B',C') \<Longrightarrow> B \<union> C \<subseteq> B' \<union> C'"
using Close2_steps_incr2 by blast

theorem Close2_step_C'_subset:
  "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> C' \<subseteq> C \<union> B"
by(auto simp: Close2.simps)

theorem Close2_steps_subdivide:
  "Bs \<turnstile> (B,C) \<rightarrow>* (B1,C1) \<Longrightarrow> x \<notin> C \<Longrightarrow> B \<inter> C = {} \<Longrightarrow> x \<in> C1 \<Longrightarrow>
  (\<exists>B2 C2 B3 C3. Bs \<turnstile> (B,C) \<rightarrow>* (B2,C2) \<and> x \<in> B2 \<and> Bs \<turnstile> (B2,C2) \<rightarrow> (B3,C3) \<and> x \<notin> B3 \<and> Bs \<turnstile> (B3,C3) \<rightarrow>* (B1,C1))"
proof(induction rule: rtranclp_induct2)
  case refl thus ?case by blast
next
  case (step) thus ?case using Close2_step_C'_subset Close2_steps_disj
    by (smt (verit, ccfv_threshold) IntI UnE equals0D rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl subset_eq)
qed

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
    using Complete Close1.Complete * unfolding Complete_def next_symbol_def by (auto split: if_splits)
  moreover
  have "insert x C \<subseteq> Close1 Bs (B \<union> C)"
    using Close1_incr Complete.hyps(1) by blast
  ultimately show ?case
    by blast
qed

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

definition Close2_less :: "nat \<Rightarrow> (('a state set \<times> 'a state set) \<times> ('a state set \<times> 'a state set)) set" where
"Close2_less k = (\<lambda>(B,C). card({x. wf_state x k} - (B \<union> C))) <*mlex*> inv_image finite_psubset fst"

lemma wf_Close2_less: "wf (Close2_less k)"
by (simp add: Close2_less_def wf_mlex)

lemma finite_ex_wf_state: "finite ({x. wf_state x k})"
using finite_subset[OF _  finite_imageI[OF finite_wf_state, of fst]] unfolding image_def
apply auto
by (metis Collect_mono)

lemma wf_states_mv_dot: "\<lbrakk> wf_bins1 Bs; wf_state1 x (length Bs); next_symbol x = None \<rbrakk> \<Longrightarrow>
  mv_dot ` {y \<in> Bs ! from x. next_symbol y = Some (lhs (state.prod x))} \<subseteq> {x. wf_state x (length Bs)}"
    using wf_Complete unfolding next_symbol_def wf_bin1_def wf_bins1_def wf_state1_def
    by (smt (verit, ccfv_threshold) image_Collect_subsetI mem_Collect_eq option.distinct(1))

lemma Close2_less_step:
assumes "wf_bins1 Bs"
shows
 "\<lbrakk> Bs \<turnstile> (B,C) \<rightarrow> (B',C'); wf_bin1 B (length Bs); wf_bin1 C (length Bs) \<rbrakk>
  \<Longrightarrow> ((B',C'), (B,C)) \<in> Close2_less (length Bs)"
proof (induction rule: Close2_induct)
  case (Predict x B C)
  let ?C = "insert x C" let ?B = "B \<union> Predict x (length Bs) - ?C"
  have 1: "B \<subseteq> {x. wf_state x (length Bs)}"
    using Predict.prems(1) unfolding wf_bin1_def wf_state1_def by blast
  have "B \<union> C < ?B \<union> ?C \<or> B \<union> C = ?B \<union> ?C \<and> ?B < B"
    using Predict.hyps(1) by blast
  thus ?case
  proof
    assume "B \<union> C < ?B \<union> ?C"
    thus ?thesis using 1 Predict.hyps(1) Predict.prems(1) wf_Predict unfolding Close2_less_def mlex_iff wf_bin1_def
      apply simp
      apply(rule disjI1)
      apply(rule psubset_card_mono)
      using Collect_mono Diff_subset_conv finite_subset[OF _ finite_ex_wf_state] sup.coboundedI2
       apply (metis (mono_tags, lifting))
      by blast
  next
    assume "B \<union> C = ?B \<union> ?C \<and> ?B \<subset> B"
    thus ?thesis
      using 1 finite_subset[OF _ finite_ex_wf_state] unfolding Close2_less_def mlex_iff by simp
  qed
next
  case (Complete x B "C")
  let ?C = "insert x C" let ?B = "B \<union> Complete Bs x - ?C"
  have 1: "B \<subseteq> {x. wf_state x (length Bs)}"
    using Complete.prems(1) unfolding wf_bin1_def wf_state1_def by blast
  have *: "mv_dot ` {xa \<in> Bs ! from x. next_symbol xa = Some (lhs (state.prod x))} \<subseteq> {x. wf_state x (length Bs)}"
    using wf_states_mv_dot[ OF \<open>wf_bins1 Bs\<close> _ Complete.hyps(2)] Complete.hyps(1) Complete.prems(1) wf_bin1_def by auto
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
      using Collect_mono Diff_subset_conv finite_subset[OF _ finite_ex_wf_state] sup.coboundedI2
       apply (metis (mono_tags, lifting))
      by blast
  next
    assume "B \<union> C = ?B \<union> ?C \<and> ?B \<subset> B"
    thus ?thesis
      using 1 finite_subset[OF _ finite_ex_wf_state] unfolding Close2_less_def mlex_iff by simp
  qed
qed

lemma Close2_nonempty_step:
  assumes "B \<noteq> {}" shows "\<exists>B' C'. Bs \<turnstile> (B,C) \<rightarrow> (B',C')"
proof -
  from \<open>B \<noteq> {}\<close> obtain x where "x \<in> B" by blast
  show ?thesis
  proof (cases "next_symbol x")
    case None
    thus ?thesis using Close2.Complete \<open>x \<in> B\<close> by blast
  next
    case (Some a)
    thus ?thesis using Close2.Predict \<open>x \<in> B\<close> by blast
  qed
qed

lemma Close2_sim_Close1:
 shows "\<lbrakk> x \<in> Close1 Bs B;  Bs \<turnstile> (B,{}) \<rightarrow>* ({},C) \<rbrakk> \<Longrightarrow> x \<in> C"
proof(induction arbitrary: C rule: Close1.induct)
  case (Init x)
  thus ?case using Close2_steps_incr
    by blast
next
  case (Predict x y)
  from \<open>y \<in> _\<close> have n: "next_symbol x \<noteq> None"
    unfolding Predict_def by auto
  obtain B2 C2 B3 C3
  where "Bs \<turnstile> (B,{}) \<rightarrow>* (B2,C2)" "x \<in> B2" "Bs \<turnstile> (B2,C2) \<rightarrow> (B3,C3)" "x \<notin> B3" "Bs \<turnstile> (B3,C3) \<rightarrow>* ({},C)"
    using Close2_steps_subdivide[OF Predict.prems]  Predict.IH[OF Predict.prems] by blast
  have "B2 \<inter> C2 = {}" using Close2_steps_disj \<open>Bs \<turnstile> (B, {}) \<rightarrow>* (B2, C2)\<close> by blast
  have "B3 = B2 \<union> Predict x (length Bs) - insert x C2" "C3 = insert x C2"
    using Close2_forward[OF \<open>Bs \<turnstile> (B2,C2) \<rightarrow> _\<close> \<open>B2 \<inter> C2 = {}\<close> \<open>x \<in> B2\<close> \<open>x \<notin> B3\<close>] n by auto
  show ?case
    using Close2_steps_incr2[OF \<open>Bs \<turnstile> (B3, C3) \<rightarrow>* _\<close>] Predict.hyps(2) \<open>B3 = _\<close> \<open>C3 = _\<close> by blast
next
  case (Complete x y)
  have n: "next_symbol x = None"
    by (simp add: Complete.hyps(2) next_symbol_def)
  obtain B2 C2 B3 C3
    where "Bs \<turnstile> (B,{}) \<rightarrow>* (B2,C2)" "x \<in> B2" "Bs \<turnstile> (B2,C2) \<rightarrow> (B3,C3)" "x \<notin> B3" "Bs \<turnstile> (B3,C3) \<rightarrow>* ({},C)"
    using Close2_steps_subdivide[OF Complete.prems] Complete.IH[OF Complete.prems] by blast
  have "B2 \<inter> C2 = {}" using Close2_steps_disj \<open>Bs \<turnstile> (B, {}) \<rightarrow>* (B2, C2)\<close> by blast
  have "B3 = B2 \<union> Complete Bs x - insert x C2" "C3 = insert x C2"
    using Close2_forward[OF \<open>Bs \<turnstile> (B2,C2) \<rightarrow> _\<close> \<open>B2 \<inter> C2 = {}\<close> \<open>x \<in> B2\<close> \<open>x \<notin> B3\<close>] n by auto
  show ?case
    using Close2_steps_incr2[OF \<open>Bs \<turnstile> (B3, C3) \<rightarrow>* _\<close>] Complete.hyps \<open>B3 = _\<close> \<open>C3 = _\<close>
    unfolding Complete_def by auto
qed

corollary Close1_subset_Close2:
 "Bs \<turnstile> (B,{}) \<rightarrow>* ({},D) \<Longrightarrow> Close1 Bs B \<subseteq> D"
using Close2_sim_Close1 by auto

end (* Earley_Gw *)

context Earley_Gw_eps
begin

lemma Close2_step_pres1: assumes "wf_bins1 Bs"
shows "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> wf_bin1 B (length Bs) \<Longrightarrow> wf_bin1 B' (length Bs)"
proof(induction rule: Close2_induct)
  case (Predict x B "C")
  thus ?case using wf1_Predict unfolding wf_bin1_def by blast
next
  case (Complete x B "C")
  thus ?case using wf1_Complete assms unfolding Complete_def
    by (smt (verit, del_insts) DiffD1 UnE image_iff mem_Collect_eq option.distinct(1) next_symbol_def wf_state1_def wf_bin1_def wf_bins1_def)
qed

lemma Close2_step_pres2: assumes "wf_bins1 Bs"
shows "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> wf_bin1 B (length Bs) \<Longrightarrow> wf_bin1 C (length Bs) \<Longrightarrow> wf_bin1 C' (length Bs)"
proof(induction rule: Close2_induct)
  case (Predict x B "C")
  thus ?case using wf1_Predict unfolding wf_bin1_def by blast
next
  case (Complete x B "C")
  thus ?case unfolding wf_bin1_def by blast
qed

(* unify wf_bin1 and wf_states? *)
lemma Close2_NF: assumes "wf_bins1 Bs"
shows "wf_bin1 B (length Bs) \<Longrightarrow> wf_bin1 C (length Bs) \<Longrightarrow> \<exists>C'. Bs \<turnstile> (B,C) \<rightarrow>* ({},C')"
using wf_Close2_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "B = {}"
    thus ?thesis by blast
  next
    assume "B \<noteq> {}"
    then obtain B' C' where step: "Bs \<turnstile> (B,C) \<rightarrow> (B',C')" using Close2_nonempty_step by blast
    note 1 = Close2_step_pres1[OF assms step less.prems(1)]
    note 2 = Close2_step_pres2[OF assms step less.prems]
    from less(1)[OF Close2_less_step [OF \<open>wf_bins1 Bs\<close> step]] less.prems
    show ?thesis using 1 2 by (metis converse_rtranclp_into_rtranclp step)
  qed
qed

lemma close2_eq_Close1: assumes "wf_bins1 Bs" "wf_bin1 B (length Bs)"
 shows "close2 Bs B = Close1 Bs B"
proof
  from Close2_NF[OF assms,of "{}"] Close2_steps_subset_Close1'
  show "close2 Bs B \<subseteq> Close1 Bs B" by(simp add: close2_def wf_bin1_def) (metis someI)
  from Close1_subset_Close2 Close2_NF[OF assms,of "{}"]
  show "Close1 Bs B \<subseteq> close2 Bs B" by(simp add: close2_def wf_bin1_def) (metis someI)
qed

lemma wf_bin1_Init: "wf_bin1 Init 0"
using \<epsilon> by(auto simp add: Init_def wf_bin1_def wf_state1_def wf_state_def is_complete_def \<epsilon>_free_def)

lemma bins0_close2:(* used in Paper *) "bins 0 = [close2 [] Init]"
by(simp flip: Close1_eq_Close add: close2_eq_Close1 wf_bins1_def wf_bin1_Init)

lemma Close_Init: "x \<in> Close [] Init \<Longrightarrow> \<not> is_complete x"
unfolding is_complete_def Init_def
proof (induction rule: Close.induct)
  case (Init x)
  thus ?case
    using \<epsilon> \<epsilon>_free_def by fastforce
next
  case (Predict x x')
  thus ?case
    using \<epsilon> Predict_def \<epsilon>_free_def by fastforce
next
  case (Complete y x)
  thus ?case
    using is_complete_def by blast
qed

lemma Close_wf_bin1: "\<lbrakk> wf_bins1 Bs; wf_bin1 B (length Bs) \<rbrakk>
 \<Longrightarrow> wf_bin1 (Close Bs B) (length Bs)"
by (metis Close1_eq_Close wf_bin1_def wf_state1_Close1)

(* \<epsilon>_free not needed! *)
lemma wf_bin1_Scan: "\<lbrakk> k < length w; wf_bin1 B k \<rbrakk> \<Longrightarrow> wf_bin1 (Scan B k) (Suc k)"
by(auto simp: Scan_def mv_dot_def is_complete_def next_symbol_def wf_bin1_def wf_state1_def wf_state_def)

lemma wf_bins1_bins: "k \<le> length w \<Longrightarrow> wf_bins1 (bins k)"
proof (induction k)
  case 0
  thus ?case
    using Close_Init by (auto simp: S0 wf_EarleyS wf_bins1_def wf_bin1_def wf_state1_def)
next
  case (Suc k)
  have "wf_bins1 (bins k)" using Suc.IH Suc.prems by auto
  hence "wf_bin1 (Scan (last (bins k)) k) (Suc k)"
    using wf_bin1_Scan Suc.prems 
    by(simp add: last_conv_nth bins_nonempty wf_bins1_def)
  with Suc show ?case
    using Close_wf_bin1[of "bins k"]
    by(auto simp add: Let_def wf_bins1_def less_Suc_eq nth_append)
qed

lemma wf_bin1_last:
  "k \<le> length w \<Longrightarrow> wf_bin1 (last (bins k)) k"
using wf_bins1_bins[of k]
by(simp add: last_conv_nth[OF bins_nonempty] wf_bins1_def)

lemma binsSuc_close2:(* used in Paper *)
  "k < length w \<Longrightarrow> bins (Suc k) = (let Bs = bins k in Bs @ [close2 Bs (Scan (last Bs) k)])"
by(simp flip: Close1_eq_Close add: close2_eq_Close1 wf_bins1_bins wf_bin1_Scan wf_bin1_last Let_def)

end (* Earley_Gw_eps *)

unused_thms

end