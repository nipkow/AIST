(* Author: Moritz Roos, Tobias Nipkow *)

section "Dyck Languages"

theory Dyck_Language
imports Main
begin

text \<open>Dyck languages are sets of words/lists of balanced brackets. A bracket is a pair of type
\<^typ>\<open>bool \<times> 'a\<close> where \<open>True\<close> is an opening and \<open>False\<close> a closing bracket. Brackets are tagged with
elements of type \<open>'a\<close>.\<close>

type_synonym 'a bracket = "bool \<times> 'a"

abbreviation "Open a \<equiv> (True,a)"
abbreviation "Close a \<equiv> (False,a)"

subsection\<open>Balanced\<close>

text\<open>Definition of what it means to be a \emph{balanced} list of brackets:\<close>

inductive bal :: "'a bracket list \<Rightarrow> bool" where
  "bal []" |
  "bal xs \<Longrightarrow> bal ys \<Longrightarrow> bal (xs @ ys)" | 
  "bal xs \<Longrightarrow> bal (Open a # xs @ [Close a])" 

declare bal.intros(1)[iff] bal.intros(2)[intro,simp] bal.intros(3)[intro!,simp]

lemma bal2[iff]: "bal [Open a, Close a]" 
  using bal.intros(3) by fastforce

text \<open>The inductive definition of balanced is complemented with a functional version
that uses a stack to remember which opening brackets need to be closed:\<close>

fun bal_stk :: "'a list \<Rightarrow> 'a bracket list \<Rightarrow> 'a list * 'a bracket list" where
  "bal_stk s [] = (s,[])" |
  "bal_stk s (Open a # bs) = bal_stk (a # s) bs" |
  "bal_stk (a' # s) (Close a # bs) =
    (if a = a' then bal_stk s bs else (a' # s, Close a # bs))" | 
  "bal_stk bs stk = (bs,stk)"

lemma bal_stk_append:
  "bal_stk s1 (xs @ ys) = (let (s1',xs') = bal_stk s1 xs in bal_stk s1' (xs' @ ys))"
by(induction s1 xs rule:bal_stk.induct) (auto split: if_splits)

lemma bal_stk_append_if[simp]:
  "bal_stk s1 xs = (s2,[]) \<Longrightarrow> bal_stk s1 (xs @ ys) = bal_stk s2 ys"
by(simp add: bal_stk_append[of _ xs])


subsubsection "Equivalence of @{const bal} and @{const bal_stk}"

lemma bal_stk_if_bal:  "bal xs \<Longrightarrow> bal_stk s xs = (s,[])"
by(induction arbitrary: s rule: bal.induct)(auto split: if_splits)

lemma bal_insert_AB:
  "bal u \<Longrightarrow> u = v@w \<Longrightarrow> bal (v @ (Open x # Close x # w))"
proof(induction arbitrary: v w rule: bal.induct)
  case 1 thus ?case by blast
next
  case (3 u y)
  show ?case
  proof (cases v)
    case Nil
    hence "w = (Open y) # u @ [Close y]" using "3.prems" 
      by simp
    hence "bal w" using "3.hyps" 
      by blast
    hence "bal ([Open x, Close x] @ w)" 
      by blast
    thus ?thesis using Nil by simp
  next
    case (Cons X v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      from "3.hyps" have "bal ((Open x # u @ [Close x]) @ [Open x, Close x])"
        using bal.intros(2) by blast
      thus ?thesis using Nil Cons 3
        by (metis append_Nil append_Nil2 bal.simps)
    next
      case (snoc w' Y)
      hence u: "u=v'@w'" and [simp]: "X= Open y & Y= Close y"
        using Cons "3.prems" apply (smt (verit, ccfv_threshold) List.append.assoc List.list.inject append_Cons append_eq_append_conv last_snoc)
        by (metis "local.3.prems" Cons List.append.assoc List.list.inject append_Cons last_snoc snoc)
          \<comment> \<open>This also works by auto, but it takes 4 seconds.\<close>
      thus ?thesis
        by (metis "3.IH" append.assoc append_Cons local.Cons bal.intros(3) snoc)
    qed
  qed
next
  case (2 v' w')
  then obtain r where "v'=v@r \<and> r@w'=w \<or> v'@r=v \<and>w'=r@w" (is "?A \<or> ?B")
    by (meson append_eq_append_conv2)
  thus ?case
  proof
    assume A: ?A
    hence "bal (v @ Open x # Close x # r)" 
      using "2.IH"(1) by presburger
    hence "bal ((v @ Open x # Close x#r) @ w')" 
      using \<open>bal w'\<close> by(rule bal.intros(2))
    thus ?thesis using A by auto
  next
    assume B: ?B
    hence "bal (r @ Open x # Close x # w)" 
      using "2.IH"(2) by presburger
    with \<open>bal v'\<close> have "bal (v'@(r@Open x # Close x#w))" 
      by(rule bal.intros(2))
    thus ?thesis using B by force
  qed 
qed 

lemma bal_if_bal_stk: "bal_stk s w = ([],[]) \<Longrightarrow> bal (rev(map (\<lambda>x. Open x) s) @ w)"
proof(induction s w rule: bal_stk.induct)
  case 2
  then show ?case by simp
next
  case 3
  then show ?case by (auto simp add: bal_insert_AB split: if_splits) 
qed (auto)

corollary bal_stk_iff_bal: "bal_stk [] w = ([],[]) \<longleftrightarrow> bal w"
  using bal_if_bal_stk[of "[]"] bal_stk_if_bal by auto

lemma bal_stk_append_inv:
  \<open>bal_stk s1 (xs@ys) = (s', []) \<Longrightarrow> (let (s1', xs') = bal_stk s1 xs in bal_stk s1 xs = (s1', []))\<close>
proof(induction s1 xs arbitrary: ys rule: bal_stk.induct)
  case (1 s)
  then show ?case by auto
next
  case (2 g xs s)
  then show ?case by(auto split: prod.splits)
next
  case (3 g xs g' s)
  then show ?case apply simp by (metis List.list.distinct(1) Product_Type.prod.inject)
next
  case (4 A xs s)
  then show ?case by(auto split: prod.splits)
qed


subsection\<open>More properties of \<^const>\<open>bal\<close>, using \<^const>\<open>bal_stk\<close>\<close>

theorem bal_append_inv: "bal (u @ v) \<Longrightarrow> bal u \<Longrightarrow> bal v"
  using bal_stk_append_if bal_stk_iff_bal by metis

lemma bal_insert: 
  assumes u: "bal u"  and b: \<open>bal b\<close> and uvw: "u = v@w"
  shows "bal (v @ b @ w)" 
proof-
  have \<open>bal_stk [] b = ([],[])\<close> 
    using assms bal_stk_iff_bal by blast
  have \<open>bal_stk [] u = ([],[])\<close> 
    using assms bal_stk_iff_bal by blast
  then obtain s1' where s1'_def: \<open>bal_stk [] v = (s1', [])\<close> 
    by (metis (full_types, lifting) uvw case_prodE bal_stk_append_inv)
  then obtain s' where s'_def: \<open>bal_stk [] (v @ w) = bal_stk s' w\<close> 
    using bal_stk_append_if by blast
  then have \<open>([],[]) = bal_stk [] (v @ w)\<close> 
    using uvw using \<open>bal_stk [] u = ([], [])\<close> by presburger
  also have \<open>... = bal_stk s' w\<close> 
    using s'_def by simp
  also have \<open>... = bal_stk s' (b@w)\<close> 
    by (metis b bal_stk_append_if bal_stk_if_bal)
  finally have \<open>bal_stk s' (b@w) = ([],[])\<close> 
    by simp
  then have \<open>bal_stk [] (v @ b @ w) = ([],[])\<close> 
    using s1'_def by (metis b s'_def bal_stk_append_if bal_stk_if_bal)
  then show \<open>bal (v @ b @ w)\<close> 
    using bal_stk_iff_bal by blast
qed

lemma bal_del: 
  assumes u: "bal u" and b: \<open>bal b\<close> and uvbw: \<open>u = v @ b @ w\<close>
  shows "bal (v @ w)" 
proof-
  have bal_stk_b: \<open>bal_stk [] b = ([],[])\<close> 
    using assms bal_stk_iff_bal by blast
  have bal_stk_vbw: \<open>bal_stk [] (v @ b @ w) = ([],[])\<close> 
    using uvbw assms bal_stk_iff_bal by blast
  then obtain s1' where s1'_def: \<open>bal_stk [] v = (s1', [])\<close> 
    by (metis (full_types, lifting) case_prodE bal_stk_append_inv)
  then have \<open>bal_stk [] (v@b) = (s1', [])\<close> 
    by (metis b bal_stk_append_if bal_stk_if_bal)
  then have \<open>bal_stk [] (v @  w) = ([],[])\<close> 
    using bal_stk_vbw s1'_def by (metis bal_stk_append_if)
  then show \<open>bal (v @ w)\<close> 
    using bal_stk_iff_bal by blast
qed

corollary bal_iff_insert[iff]:
  assumes \<open>bal b\<close>
  shows \<open>bal (v @ b @ w) = bal (v @ w)\<close>
  using bal_del bal_insert by (metis assms)

lemma bal_start_Open: \<open>bal (x#xs) \<Longrightarrow>\<exists>a. x = Open a\<close>
  using bal_stk.elims bal_stk_iff_bal by blast 

lemma bal_Open_split: assumes bal_x_xs: \<open>bal (x # xs)\<close>
  shows \<open>\<exists>y r a. bal y \<and> bal r \<and> (x # xs) = Open a # y @ Close a # r\<close>
proof-
  from bal_x_xs obtain a where x_def: \<open>x = Open a\<close> 
    using bal_start_Open by blast
  then have \<open>bal (Open a # xs) \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> (x # xs) = Open a # y @ Close a # r\<close>
  proof(induction \<open>length (x # xs)\<close> arbitrary: xs rule: less_induct)
    case less
    have IH: \<open>\<And>w. \<lbrakk>length (Open a # w) < length (Open a # xs); bal (Open a # w)\<rbrakk> \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> Open a # w = Open a # y @ Close a # r\<close> 
      using less by blast
    have \<open>bal (Open a # xs)\<close> 
      using less bal_x_xs by blast
    then show ?case
    proof(induction \<open>Open a # xs\<close> rule: bal.induct)
      case (2 as bs)
      consider (as_empty)  \<open>as = []\<close> | (bs_empty)\<open>bs = []\<close> | (both_not_empty)\<open>as \<noteq> [] \<and> bs \<noteq> []\<close> by blast
      then show ?case
      proof(cases)
        case as_empty
        then show ?thesis using 2 by (metis append_Nil)
      next
        case bs_empty
        then show ?thesis using 2 by (metis append_self_conv)
      next
        case both_not_empty
        then obtain as' where as'_def: \<open>Open a # as' = as\<close> 
          using 2 by (metis append_eq_Cons_conv)
        then have \<open>length (Open a # as') < length (Open a # xs)\<close>
          using "2.hyps"(5) both_not_empty by fastforce
        with IH \<open>bal as\<close> obtain y r where yr: \<open>bal y \<and> bal r \<and> Open a # as' = Open a # y @ Close a # r\<close> 
          using as'_def by meson
        then have \<open>Open a # xs = Open a # y @ Close a # r @ bs\<close> 
          using as'_def by (metis "2.hyps"(5) List.append.assoc append_Cons)
        moreover have \<open>bal y\<close>
          using yr by blast
        moreover have \<open>bal (r@bs)\<close> 
          using yr by (simp add: "2.hyps"(3))
        ultimately show ?thesis using x_def by blast
      qed
    next
      case (3 xs)
      then show ?case using x_def by blast    
    qed
  qed
  then show ?thesis using x_def using bal_x_xs by blast
qed


subsection\<open>Dyck Language over an Alphabet\<close>

text\<open>The second components of a list of pairs are all in \<open>\<Gamma>\<close>:\<close>
abbreviation snds_in :: \<open>'a set  \<Rightarrow> ('b  \<times> 'a) list \<Rightarrow> bool\<close> where
  \<open>snds_in \<Gamma> bs \<equiv> snd ` (set bs) \<subseteq> \<Gamma>\<close>

text\<open>The Dyck/bracket language over a set \<open>\<Gamma>\<close> is the set of balanced words over \<open>\<Gamma>\<close>:\<close>

definition Dyck_lang :: "'a set \<Rightarrow> 'a bracket list set" where
"Dyck_lang \<Gamma> = {w. bal w \<and> snds_in \<Gamma> w}"

lemma Dyck_langI[intro]: 
  assumes \<open>bal w\<close>
    and \<open>snds_in \<Gamma> w\<close>
  shows \<open>w \<in> Dyck_lang \<Gamma>\<close>
  using assms unfolding Dyck_lang_def by blast

lemma Dyck_langD[dest]:
  assumes \<open>w \<in> Dyck_lang \<Gamma>\<close>
  shows \<open>bal w\<close>
    and \<open>snds_in \<Gamma> w\<close>
  using assms unfolding Dyck_lang_def by auto

text\<open>Balanced subwords are again in the Dyck Language.\<close>
lemma Dyck_lang_substring:
  \<open>bal w \<Longrightarrow> u @ w @ v \<in> Dyck_lang \<Gamma> \<Longrightarrow> w \<in> Dyck_lang \<Gamma>\<close>
unfolding Dyck_lang_def by auto

end