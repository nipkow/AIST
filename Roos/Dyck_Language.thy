(* Author: Moritz Roos, Tobias Nipkow *)

section "Dyck Languages"

theory Dyck_Language
  imports CFG.CFG
begin

(*TODO now in CFG *)
fun destTm :: "('a, 'b) sym  \<Rightarrow> 'b" where 
  \<open>destTm (Tm t) = t\<close> | 
  \<open>destTm (Nt A) = undefined\<close>

lemma destTm_Tm[simp]: \<open>destTm \<circ> Tm = id\<close>
by auto
(* until here*)

text \<open>Dyck languages are sets of words/lists of balanced brackets.\<close>

subsection\<open>Balanced\<close>

text\<open>A type of brackets for creating the \emph{Dyck_language}\<close>
datatype bracket = Open | Close

text\<open>Definition of what it means to be a \emph{balanced} list with elements of type \<open>bracket \<times> 'a\<close>,
i.e.\ the brackets are indexed with elements of type \<open>'a\<close>, i.e.\ we have multiple brackets.\<close>

inductive bal :: "(bracket  \<times> 'a) list \<Rightarrow> bool" where
  "bal []" |
  "bal xs \<Longrightarrow> bal ys \<Longrightarrow> bal (xs @ ys)" | 
  "bal xs \<Longrightarrow> bal ((Open, g) # xs @ [(Close, g)])" 

declare bal.intros(1)[iff] bal.intros(2)[intro,simp] bal.intros(3)[intro!,simp]

lemma bal2[iff]: "bal [(Open,g), (Close,g)]" 
  using bal.intros(3) by fastforce

text \<open>The inductive definition of balanced is complemented with a functional version
that uses a stack to remember which opening brackets need to be closed:\<close>

fun bal_stk :: "'a list \<Rightarrow> (bracket \<times> 'a) list \<Rightarrow> 'a list * (bracket \<times> 'a) list" where
  "bal_stk s [] = (s,[])" |
  "bal_stk s ((Open, a) # bs) = bal_stk (a # s) bs" |
  "bal_stk (a' # s) ((Close, a) # bs) =
    (if a = a' then bal_stk s bs else (a' # s, (Close, a) # bs))" | 
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
  "bal u \<Longrightarrow> u = v@w \<Longrightarrow> bal (v @ (Open, x) # (Close, x) # w)"
proof(induction arbitrary: v w rule: bal.induct)
  case 1 thus ?case by blast
next
  case (3 u y)
  show ?case
  proof (cases v)
    case Nil
    hence "w = ((Open, y)) # u @ [(Close, y)]" using "3.prems" 
      by simp
    hence "bal w" using "3.hyps" 
      by blast
    hence "bal ([(Open, x), (Close, x)] @ w)" 
      by blast
    thus ?thesis using Nil by simp
  next
    case (Cons X v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      from "3.hyps" have "bal (((Open, x) # u @ [(Close, x)]) @ [(Open, x), (Close, x)])"
        using bal.intros(2) by blast
      thus ?thesis using Nil Cons 3
        by (metis append_Nil append_Nil2 bal.simps)
    next
      case (snoc w' Y)
      hence u: "u=v'@w'" and [simp]: "X=(Open, y) & Y=(Close, y)"
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
    hence "bal (v @ (Open, x) # (Close, x) # r)" 
      using "2.IH"(1) by presburger
    hence "bal ((v @ (Open, x) # (Close, x)#r) @ w')" 
      using \<open>bal w'\<close> by(rule bal.intros(2))
    thus ?thesis using A by auto
  next
    assume B: ?B
    hence "bal (r @ (Open, x) # (Close, x) # w)" 
      using "2.IH"(2) by presburger
    with \<open>bal v'\<close> have "bal (v'@(r@(Open, x) # (Close, x)#w))" 
      by(rule bal.intros(2))
    thus ?thesis using B by force
  qed 
qed 

lemma bal_if_bal_stk: "bal_stk s w = ([],[]) \<Longrightarrow> bal (rev(map (\<lambda>x. (Open, x)) s) @ w)"
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

lemma bal_start_Open: \<open>bal (x#xs) \<Longrightarrow>\<exists>g. x = (Open,g)\<close>
  using bal_stk.elims bal_stk_iff_bal by blast 

lemma bal_Open_split: assumes bal_x_xs: \<open>bal (x # xs)\<close>
  shows \<open>\<exists>y r g. bal y \<and> bal r \<and> (x # xs) = (Open, g) # y @ (Close, g) # r\<close>
proof-
  from bal_x_xs obtain g where x_def: \<open>x = (Open, g)\<close> 
    using bal_start_Open by blast
  then have \<open>bal ((Open, g) # xs) \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> (x # xs) = (Open, g) # y @ (Close, g) # r\<close>
  proof(induction \<open>length (x # xs)\<close> arbitrary: xs rule: less_induct)
    case less
    have IH: \<open>\<And>w. \<lbrakk>length ((Open, g) # w) < length ((Open, g) # xs); bal ((Open, g) # w)\<rbrakk> \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> (Open, g) # w = (Open, g) # y @ (Close, g) # r\<close> 
      using less by blast
    have \<open>bal ((Open, g) # xs)\<close> 
      using less bal_x_xs by blast
    then show ?case
    proof(induction \<open>(Open,g) # xs\<close> rule: bal.induct)
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
        then obtain as' where as'_def: \<open>(Open, g) # as' = as\<close> 
          using 2 by (metis append_eq_Cons_conv)
        then have \<open>length ((Open, g) # as') < length ((Open, g) # xs)\<close> 
          by (metis "local.2.hyps"(5) List.append.right_neutral append_eq_conv_conj both_not_empty linorder_not_le take_all_iff)
        with IH \<open>bal as\<close> obtain y r where yr_def: \<open>bal y \<and> bal r \<and> (Open, g) # as' = (Open, g) # y @ (Close, g) # r\<close> 
          using as'_def by meson
        then have \<open>(Open, g) # xs = (Open, g) # y @ (Close, g) # r @ bs\<close> 
          using as'_def by (metis "local.2.hyps"(5) List.append.assoc append_Cons)
        moreover have \<open>bal y\<close> and \<open>bal (r@bs)\<close> 
          using yr_def apply blast by (simp add: "local.2.hyps"(3) yr_def)
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

definition Dyck_language :: "'a set \<Rightarrow> (bracket  \<times> 'a) list set" where
"Dyck_language \<Gamma> = {w. bal w \<and> snds_in \<Gamma> w}"

lemma Dyck_languageI[intro]: 
  assumes \<open>bal w\<close>
    and \<open>snds_in \<Gamma> w\<close>
  shows \<open>w \<in> Dyck_language \<Gamma>\<close>
  using assms unfolding Dyck_language_def by blast

lemma Dyck_languageD[dest]:
  assumes \<open>w \<in> Dyck_language \<Gamma>\<close>
  shows \<open>bal w\<close>
    and \<open>snds_in \<Gamma> w\<close>
  using assms unfolding Dyck_language_def by auto

text\<open>Balanced subwords are again in the Dyck Language.\<close>
lemma Dyck_language_substring:
  \<open>bal w \<Longrightarrow> u @ w @ v \<in> Dyck_language \<Gamma> \<Longrightarrow> w \<in> Dyck_language \<Gamma>\<close>
unfolding Dyck_language_def by auto


section\<open>Versions of \<^const>\<open>bal\<close> and \<^const>\<open>snds_in\<close> for @{type syms}\<close>


subsection\<open>Function \<^term>\<open>bal_tm\<close>\<close>

definition bal_tm where
  \<open>bal_tm \<equiv> bal o (map destTm) o (filter isTm)\<close>

(* TODO now in CFG *)
lemma isTm_Nt[simp]:\<open>(isTm (Nt A)) = False\<close>
  by (simp add: isTm_def)

lemma isTm_Tm[simp]: \<open>isTm (Tm a)\<close> 
  by (simp add: isTm_def)

lemma filter_isTm_map_Tm[simp]:\<open>filter isTm (map Tm xs') = map Tm xs'\<close>
  apply(induction xs') by auto
(* until here *)

lemma bal_tm_empty[iff]: \<open>bal_tm []\<close>
  by (simp add: bal_tm_def)

lemma bal_tm_Nt[iff]:\<open>bal_tm [Nt A]\<close>
  by (simp add: bal_tm_def)

lemma bal_tm_append[intro, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm ys \<Longrightarrow> bal_tm (xs @ ys)\<close> 
  unfolding bal_tm_def by simp

lemma bal_tm_surr[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (Tm (Open, g) # xs @ [Tm (Close, g)])\<close> 
  unfolding bal_tm_def by simp

lemma bal_tm_prepend_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (Nt A # xs)\<close> 
  by (simp add: bal_tm_def)

lemma bal_tm_append_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (xs@[Nt A])\<close> 
  by blast

lemma bal_tm2[iff]: "bal_tm [Tm (Open,g), Tm (Close,g)]" 
  using bal_tm_surr by force

lemma bal_tm2_Nt[iff]: "bal_tm [Tm (Open,g), Tm (Close,g), Nt A]" 
  using bal_tm_append_Nt by force

(* TODO: now in CFG *)
lemma map_Tm_inject_iff[simp]: "(map Tm xs = map Tm ys) = (xs = ys)"
by (metis sym.inject(2) list.inj_map_strong)
(* until here *)

text\<open>Relationship of \<^term>\<open>bal\<close> and \<^term>\<open>bal_tm\<close>:\<close>
lemma bal_imp_bal_tm: \<open>bal xs \<Longrightarrow> bal_tm (map Tm xs)\<close>
  by(induction xs rule: bal.induct; auto)

lemma bal_tm_imp_bal_for_tms: \<open>bal_tm (map Tm xs') \<Longrightarrow> bal xs'\<close>
  unfolding bal_tm_def by auto


subsection\<open>Function \<^term>\<open>snds_in_tm\<close>\<close>

text\<open>Version of \<^term>\<open>snds_in\<close> but for a list of symbols, that might contain Nonterminals.
Says that all right hand sides of \<open>x\<close> (here stripped of their \<open>Tm\<close>) are in \<open>\<Gamma>\<close>:\<close>
definition snds_in_tm where
  \<open>snds_in_tm \<Gamma> \<equiv> snds_in \<Gamma> o map destTm o filter isTm\<close>

text\<open>Useful lemmas about this:\<close>
lemma snds_in_tm_del_right: \<open>snds_in_tm \<Gamma> (xs@ys) \<Longrightarrow> snds_in_tm \<Gamma> xs\<close> 
  unfolding snds_in_tm_def by auto

lemma snds_in_tm_del_left: \<open>snds_in_tm \<Gamma> (xs@ys) \<Longrightarrow> snds_in_tm \<Gamma> ys\<close>
  unfolding snds_in_tm_def by auto

lemma snds_in_tm_append[simp]:
  \<open>snds_in_tm \<Gamma> xs \<Longrightarrow> snds_in_tm \<Gamma> ys \<Longrightarrow> snds_in_tm \<Gamma> (xs@ys)\<close>
unfolding snds_in_tm_def by auto

text\<open>Relationship between \<^term>\<open>bal_tm\<close>, \<^term>\<open>snds_in_tm\<close> and \<open>Dyck_Language\<close>\<close>
lemma Dyck_languageI_tm[intro]:
  \<open>bal_tm (map Tm xs') \<Longrightarrow> snds_in_tm \<Gamma> (map Tm xs') \<Longrightarrow> xs' \<in> Dyck_language \<Gamma>\<close>
unfolding bal_tm_def snds_in_tm_def by auto


subsection\<open>Lifting \<^const>\<open>bal\<close> and \<^const>\<open>bal_tm\<close> to @{type syms}\<close>


subsubsection\<open>Function \<open>bal_stk_tm\<close>\<close>

text\<open>A version of \<^term>\<open>bal_stk\<close> but for a symbol list that might contain nonterminals (they are ignored via filtering).\<close>
definition bal_stk_tm :: "'t list \<Rightarrow> ('n, bracket \<times> 't) syms \<Rightarrow> 't list * ('n, bracket \<times> 't) syms" where
\<open>bal_stk_tm x y \<equiv>
  (fst ((bal_stk x o map destTm o filter isTm) y), map Tm (snd ((bal_stk x o map destTm o filter isTm) y)))\<close>

lemma bal_stk_tm_append:
  "bal_stk_tm s1 (xs @ ys) = (let (s1',xs') = bal_stk_tm s1 xs in bal_stk_tm s1' (xs' @ ys))"
unfolding bal_stk_tm_def
apply simp
by (metis (no_types, lifting) bal_stk_append split_beta)

lemma bal_stk_tm_append_if[simp]:
  "bal_stk_tm s1 xs = (s2,[]) \<Longrightarrow> bal_stk_tm s1 (xs @ ys) = bal_stk_tm s2 ys"
by(simp add: bal_stk_tm_append[of _ xs])

lemma bal_stk_tm_if_bal_tm: "bal_tm xs \<Longrightarrow> bal_stk_tm s xs = (s,[])"
  unfolding bal_stk_tm_def 
  by (simp add: bal_tm_def bal_stk_if_bal)+

lemma bal_tm_insert_AB: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Tm (Open, x) # Tm (Close, x) # w)" using u
unfolding bal_tm_def by (auto intro!: bal_insert_AB)

lemma bal_tm_insert_Nt: "bal_tm u \<Longrightarrow> u = v@w \<Longrightarrow> bal_tm (v @ Nt A # w)"
unfolding bal_tm_def by auto

corollary bal_stk_tm_iff_bal_tm: "bal_stk_tm [] w = ([],[]) \<longleftrightarrow> bal_tm w"
  unfolding bal_stk_tm_def bal_tm_def o_def
  by (metis bal_stk_iff_bal map_is_Nil_conv split_pairs)

lemma bal_stk_tm_append_inv:
  \<open>bal_stk_tm s1 (xs@ys) = (s1', []) \<Longrightarrow>
  let (s1', xs') = bal_stk_tm s1 xs in bal_stk_tm s1 xs = (s1', [])\<close>
  unfolding bal_stk_tm_def Let_def apply auto 
  by (smt (verit, del_insts) case_prodE sndI bal_stk_append_inv surjective_pairing)

                              
subsection\<open>More properties of \<^term>\<open>bal_tm\<close>, using \<^term>\<open>bal_stk_tm\<close>\<close>

theorem bal_tm_append_inv: "bal_tm (u @ v) \<Longrightarrow> bal_tm u \<Longrightarrow> bal_tm v"
  using bal_stk_tm_append_if bal_stk_tm_iff_bal_tm by metis

lemma bal_tm_insert: 
  assumes u: "bal_tm u" 
    and b: \<open>bal_tm b\<close>
  shows "u = v@w \<Longrightarrow> bal_tm (v @ b @ w)" 
  by (metis b bal_iff_insert bal_tm_def comp_def filter_append map_append u)

lemma bal_tm_del: 
  assumes u: "bal_tm u" 
    and b: \<open>bal_tm b\<close>
  shows "u = v @ b @ w \<Longrightarrow> bal_tm (v @ w)" 
  by (metis b bal_iff_insert bal_tm_def comp_def filter_append map_append u)

corollary bal_tm_iff_insert[iff]:
  assumes \<open>bal_tm b\<close>
  shows \<open>bal_tm (v @ b @ w) = bal_tm (v @ w)\<close>
  using bal_tm_del bal_tm_insert by (metis assms)

end