(* Author: Moritz Roos *)
theory Dyck_Language
  imports CFG.CFG
begin

(*TODO where do i belong best?*)
fun stripTm :: "('a, 'b) sym  \<Rightarrow> 'b" where 
  \<open>stripTm (Tm t) = t\<close> | 
  \<open>stripTm (Nt A) = undefined\<close>

lemma stripTm_Tm[simp]: \<open>map (stripTm \<circ> Tm) xs' = xs'\<close>
  apply(induction xs') by auto
(* until here*)

section\<open>Balancedness\<close>

text\<open>A type of brackets for creating the \<open>Dyck_language\<close>\<close>
datatype bracket = Open | Close

text\<open>definition of what it means to be a balanced string with letters of type \<open>bracket \<times> ('a)\<close> \<close>
inductive bal :: "(bracket  \<times> 'a) list \<Rightarrow> bool" where
  "bal []" |
  "bal xs \<Longrightarrow> bal ys \<Longrightarrow> bal (xs @ ys)" | 
  "bal xs \<Longrightarrow> bal ((Open, g) # xs @ [(Close, g)])" 

declare bal.intros(1)[iff] bal.intros(2)[intro,simp] bal.intros(3)[intro!,simp]

lemma bal2[iff]: "bal [(Open,g), (Close,g)]" 
  using bal.intros(1,3) by fastforce



section\<open>Dyck Language Definition\<close>

text\<open>To verify, that all the letters in the (to be defined) Dyck language
come from the right set, we use this definition. 
It says that all right hand sides of pairs in \<open>x\<close> are in \<open>\<Gamma>\<close>.\<close>
definition rhs_in :: \<open> ('a  \<times> 'b) list \<Rightarrow> 'b set  \<Rightarrow> bool\<close> where
  \<open>rhs_in x \<Gamma> \<equiv> (\<forall>br \<gamma>. (br, \<gamma>) \<in> set x \<longrightarrow> \<gamma> \<in> \<Gamma>)\<close>

text\<open>Useful Lemmas about this:\<close>

lemma rhs_inI[intro]:
  assumes \<open>\<And>\<gamma> br. (br, \<gamma>) \<in> set x \<Longrightarrow> \<gamma> \<in> \<Gamma>\<close>
  shows \<open>rhs_in x \<Gamma>\<close>
  unfolding rhs_in_def using assms by blast

lemma rhs_inD[dest]:
  assumes \<open>rhs_in x \<Gamma>\<close>
  shows \<open>\<And>\<gamma> br. (br, \<gamma>) \<in> set x \<Longrightarrow> \<gamma> \<in> \<Gamma>\<close>
  using assms unfolding rhs_in_def by blast

lemmas rhs_inE = rhs_inD[elim_format]

lemma rhs_in_del_right: \<open>rhs_in (xs@ys) \<Gamma> \<Longrightarrow> rhs_in xs \<Gamma>\<close>
proof-
  assume assm: \<open>rhs_in (xs@ys) \<Gamma>\<close>
  have \<open>set xs \<subseteq> set (xs @ ys)\<close> 
    by simp
  then show ?thesis using rhs_inD[OF assm] by blast
qed

lemmas rhs_in_del_rightE = rhs_in_del_right[elim_format]

lemma rhs_in_del_left[dest]: \<open>rhs_in (xs@ys) \<Gamma> \<Longrightarrow> rhs_in ys \<Gamma>\<close>
proof-
  assume assm: \<open>rhs_in (xs@ys) \<Gamma>\<close>
  have \<open>set ys \<subseteq> set (xs @ ys)\<close> 
    by simp
  then show ?thesis using rhs_inD[OF assm] by blast
qed

lemmas rhs_in_del_leftE = rhs_in_del_left[elim_format]

lemma rhs_in_append[intro, simp]: \<open>rhs_in (xs) \<Gamma> \<Longrightarrow> rhs_in (ys) \<Gamma> \<Longrightarrow> rhs_in (xs@ys) \<Gamma>\<close>
proof-
  assume assm_xs: \<open>rhs_in (xs) \<Gamma>\<close>
  assume assm_ys: \<open>rhs_in (ys) \<Gamma>\<close>
  then have \<open>set (xs@ys) \<subseteq> set xs \<union> set ys\<close> 
    by simp
  then show ?thesis using rhs_inI[of \<open>xs@ys\<close> \<Gamma>] using assm_xs assm_ys by auto
qed

text\<open>The dyck/bracket language over a set \<open>\<Gamma>\<close>.  
Every element \<^prop>\<open>\<gamma> \<in> \<Gamma>\<close> will get a Closing and an Opening version of itself, 
via pairing with the type bracket.\<close>
definition Dyck_language :: "'a set \<Rightarrow> (bracket  \<times> ('a)) list set" where
  "Dyck_language \<Gamma> = {w. (bal w) \<and> rhs_in w \<Gamma>}"

lemma Dyck_languageI[intro]: 
  assumes \<open>bal w\<close>
    and \<open>rhs_in w \<Gamma>\<close>
  shows \<open>w \<in> Dyck_language \<Gamma>\<close>
  using assms unfolding Dyck_language_def by blast

lemma Dyck_languageD[dest]:
  assumes \<open>w \<in> Dyck_language \<Gamma>\<close>
  shows \<open>bal w\<close>
    and \<open>rhs_in w \<Gamma>\<close>
  using assms unfolding Dyck_language_def by auto

lemmas Dyck_languageE = Dyck_languageD[elim_format]

text\<open>Balanced subexpressions are again in the Dyck Language.\<close>
lemma Dyck_language_substring[intro]: \<open>bal w \<Longrightarrow> (xs@w@ys) \<in> Dyck_language \<Gamma> \<Longrightarrow> w \<in> Dyck_language \<Gamma>\<close> 
proof-
  assume assms: \<open>bal w\<close> and \<open>(xs@w@ys) \<in> Dyck_language \<Gamma>\<close>
  have \<open>set w \<subseteq> set (xs@w@ys)\<close> 
    by (simp add: subsetI)
  then show ?thesis using \<open>bal w\<close> \<open>xs @ w @ ys \<in> Dyck_language \<Gamma>\<close> by blast
qed



section\<open>Versions of \<^term>\<open>bal\<close> and \<^term>\<open>rhs_in\<close> for \<^term>\<open>syms\<close>\<close>

subsection\<open>Function \<^term>\<open>bal_tm\<close>\<close>

definition bal_tm where
  \<open>bal_tm \<equiv> bal o (map stripTm) o (filter isTm)\<close>

(* TODO Move *)
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

(* TODO: mv to CFG *)
lemma map_Tm_inject[dest!]: "map Tm xs = map Tm ys \<Longrightarrow> xs = ys"
  by (metis sym.inject(2) list.inj_map_strong)

lemma map_Tm_inject_iff[simp]: "(map Tm xs = map Tm ys) = (xs = ys)"
  by blast
(* until here *)

text\<open>Relationship of \<^term>\<open>bal\<close> and \<^term>\<open>bal_tm\<close>:\<close>
lemma bal_imp_bal_tm: \<open>bal xs \<Longrightarrow> bal_tm (map Tm xs)\<close>
  by(induction xs rule: bal.induct; auto)

lemma bal_tm_imp_bal_for_tms: \<open>bal_tm (map Tm xs') \<Longrightarrow> bal xs'\<close>
  unfolding bal_tm_def by auto


subsection\<open>Function \<^term>\<open>rhs_in_tm\<close>\<close>

text\<open>Version of \<^term>\<open>rhs_in\<close> but for a list of symbols, that might contain Nonterminals.
Says that all right hand sides of \<open>x\<close> (here stripped of their \<open>Tm\<close>) are in \<open>\<Gamma>\<close>:\<close>
definition rhs_in_tm where
  \<open>rhs_in_tm \<equiv> rhs_in o (map stripTm) o (filter isTm)\<close>

text\<open>Useful lemmas about this:\<close>
lemma rhs_in_tm_del_right[dest]: \<open>rhs_in_tm (xs@ys) \<Gamma> \<Longrightarrow> rhs_in_tm xs \<Gamma>\<close> 
  unfolding rhs_in_tm_def using rhs_in_del_right by auto

lemmas rhs_in_tm_del_rightE = rhs_in_tm_del_right[elim_format]

lemma rhs_in_tm_del_left[dest]: \<open>rhs_in_tm (xs@ys) \<Gamma> \<Longrightarrow> rhs_in_tm ys \<Gamma>\<close>
  unfolding rhs_in_tm_def by auto

lemmas rhs_in_tm_del_leftE = rhs_in_tm_del_left[elim_format]

lemma rhs_in_tm_append[intro, simp]: \<open>rhs_in_tm (xs) \<Gamma> \<Longrightarrow> rhs_in_tm (ys) \<Gamma> \<Longrightarrow> rhs_in_tm (xs@ys) \<Gamma>\<close>
  unfolding rhs_in_tm_def using rhs_in_append by simp

text\<open>Relationship between \<^term>\<open>bal_tm\<close>, \<^term>\<open>rhs_in_tm\<close> and \<open>Dyck_Language\<close>\<close>
lemma Dyck_languageI_tm[intro]: \<open>bal_tm (map Tm xs') \<Longrightarrow> rhs_in_tm (map Tm xs') \<Gamma> \<Longrightarrow> xs' \<in> Dyck_language \<Gamma>\<close>
  unfolding bal_tm_def rhs_in_tm_def by auto



section\<open>Function based equivalent description for \<^term>\<open>bal\<close> and \<^term>\<open>bal_tm\<close>\<close>

subsection\<open>Function \<^term>\<open>stk_bal\<close>\<close>
text\<open>This development is thankfully taken from T. Nipkow.\<close>

text\<open>A stack machine that puts open brackets to the stack, to remember that they must be matched by a closed bracket\<close>
fun stk_bal :: "(bracket \<times> 't) list \<Rightarrow> 't list \<Rightarrow> ((bracket \<times> 't) list) * 't list" where
  "stk_bal [] s = ([],s)" |
  "stk_bal ((Open, g) # xs) s = stk_bal xs (g#s)" |
  "stk_bal ((Close, g) # xs) (g'#s) = (if g=g' then stk_bal xs s else ((Close, g) # xs, g' # s))" | 
  "stk_bal xs s = (xs,s)"

lemma stk_bal_append: "stk_bal (xs @ ys) s1 = (let (xs',s1') = stk_bal xs s1 in
stk_bal (xs' @ ys) s1')"
  by(induction xs s1 rule:stk_bal.induct) (auto split: if_splits)

lemma stk_bal_append_if[simp]: "stk_bal xs s1 = ([],s2) \<Longrightarrow> stk_bal (xs @ ys) s1 =
stk_bal ys s2"
  by(simp add: stk_bal_append[of xs])

lemma stk_bal_if_bal:  "bal xs \<Longrightarrow> stk_bal xs s = ([],s)"
  by(induction arbitrary: s rule: bal.induct)(auto split: if_splits)

lemma bal_insert_AB: assumes u: "bal u" shows "u = v@w \<Longrightarrow> bal (v @ (Open, x) # (Close, x) # w)" using u
proof(induction arbitrary: v w)
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

lemma bal_if_stk_bal: "stk_bal w s = ([],[]) \<Longrightarrow> bal (rev(map (\<lambda>x. (Open, x)) s) @ w)"
proof(induction w s rule: stk_bal.induct)
  case (2 x xs s)
  then show ?case by simp
next
  case (3 x xs y s)
  then show ?case by (auto simp add: bal_insert_AB split: if_splits) 
qed (auto)

corollary stk_bal_iff_bal: "stk_bal w [] = ([],[]) \<longleftrightarrow> bal w"
  using bal_if_stk_bal[of w "[]"] stk_bal_if_bal by auto

lemma stk_bal_append_inv: \<open>stk_bal (xs@ys) s1 = ([], s') \<Longrightarrow> (let (xs', s1') = stk_bal xs s1 in stk_bal xs s1 = ([], s1'))\<close>
proof(induction xs s1 arbitrary: ys rule: stk_bal.induct)
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



subsection\<open>More properties of \<^term>\<open>bal\<close>, using \<^term>\<open>stk_bal\<close>\<close>

theorem bal_append_inv: "bal (u @ v) \<Longrightarrow> bal u \<Longrightarrow> bal v"
  using stk_bal_append_if stk_bal_iff_bal by metis

lemma bal_insert: 
  assumes u: "bal u" 
    and b: \<open>bal b\<close>
  shows "u = v@w \<Longrightarrow> bal (v @ b @ w)" 
proof-
  assume uvw: \<open>u = v@w\<close>
  have \<open>stk_bal (b) [] = ([],[])\<close> 
    using assms stk_bal_iff_bal by blast
  have \<open>stk_bal (u) [] = ([],[])\<close> 
    using assms stk_bal_iff_bal by blast
  then obtain s1' where s1'_def: \<open>stk_bal v [] = ([], s1')\<close> 
    by (metis (full_types, lifting) uvw case_prodE stk_bal_append_inv)
  then obtain s' where s'_def: \<open>stk_bal (v @ w) [] = stk_bal (w) s'\<close> 
    using stk_bal_append_if by blast
  then have \<open>([],[]) = stk_bal (v @ w) []\<close> 
    using uvw using \<open>stk_bal u [] = ([], [])\<close> by presburger
  also have \<open>... = stk_bal (w) s'\<close> 
    using s'_def by simp
  also have \<open>... = stk_bal (b@w) s'\<close> 
    by (metis b stk_bal_append_if stk_bal_if_bal)
  finally have \<open>stk_bal (b@w) s' = ([],[])\<close> 
    by simp
  then have \<open>stk_bal (v @ b @ w) [] = ([],[])\<close> 
    using s1'_def by (metis b s'_def stk_bal_append_if stk_bal_if_bal)
  then show \<open>bal (v @ b @ w)\<close> 
    using stk_bal_iff_bal by blast
qed

lemma bal_del: 
  assumes u: "bal u" 
    and b: \<open>bal b\<close>
  shows "u = v @ b @ w \<Longrightarrow> bal (v @ w)" 
proof-
  assume uvbw: \<open>u = v @ b @ w\<close>
  have stk_bal_b: \<open>stk_bal (b) [] = ([],[])\<close> 
    using assms stk_bal_iff_bal by blast
  have stk_bal_vbw: \<open>stk_bal (v @ b @ w) [] = ([],[])\<close> 
    using uvbw assms stk_bal_iff_bal by blast
  then obtain s1' where s1'_def: \<open>stk_bal v [] = ([], s1')\<close> 
    by (metis (full_types, lifting) case_prodE stk_bal_append_inv)
  then have \<open>stk_bal (v@b) [] = ([], s1')\<close> 
    by (metis b stk_bal_append_if stk_bal_if_bal)
  then have \<open>stk_bal (v @  w) [] = ([],[])\<close> 
    using stk_bal_vbw s1'_def by (metis stk_bal_append_if)
  then show \<open>bal (v @ w)\<close> 
    using stk_bal_iff_bal by blast
qed

corollary bal_iff_insert[iff]:
  assumes \<open>bal b\<close>
  shows \<open>bal (v @ b @ w) = bal (v @ w)\<close>
  using bal_del bal_insert by (metis assms)

lemma bal_start_Open: \<open>bal (x#xs) \<Longrightarrow>\<exists>g. x = (Open,g)\<close> 
proof(induction \<open>length (x#xs)\<close> arbitrary: x xs rule: less_induct)
  case less
  have IH: \<open>\<And>w (ws:: (bracket \<times> 'a) list). \<lbrakk>length (w # ws) < length (x # xs); bal (w # ws)\<rbrakk> \<Longrightarrow> \<exists>g. w = (Open, g)\<close> 
    using less by blast
  from less have \<open>bal (x # xs)\<close> 
    by simp
  then show ?case
  proof(induction \<open>x#xs\<close> rule:bal.induct)
    case (2 as bs)
    consider (as_empty)  \<open>as = []\<close> | (bs_empty)\<open>bs = []\<close> | (both_not_empty)\<open>as \<noteq> [] \<and> bs \<noteq> []\<close> 
      by blast
    then show ?case
    proof(cases)
      case as_empty
      then show ?thesis using "local.2.hyps"(4,5) eq_Nil_appendI by blast
    next
      case bs_empty
      then show ?thesis by (metis "local.2.hyps"(2,5) List.append.right_neutral)
    next
      case both_not_empty
      then have \<open>length as < length (x#xs)\<close> 
        by (metis "local.2.hyps"(5) List.append.right_neutral append_eq_conv_conj linorder_not_le take_all_iff)
      moreover have \<open>bal as\<close> 
        by (simp add: "local.2.hyps"(1))
      ultimately have \<open>\<exists>g. hd as = (Open, g)\<close> 
        using IH[of \<open>hd as\<close> \<open>tl as\<close>] using both_not_empty by auto
      moreover have \<open>x = hd as\<close> 
        using both_not_empty by (metis "local.2.hyps"(5) List.list.sel(1) hd_append2)
      ultimately show ?thesis by blast
    qed
  qed auto
qed

lemma bal_Open_split: \<open>bal (x # xs) \<Longrightarrow> \<exists>y r g. bal y \<and> bal r \<and> (x # xs) = (Open, g) # y @ (Close, g) # r\<close>
proof-
  assume bal_x_xs: \<open>bal (x # xs)\<close>
  then obtain g where x_def: \<open>x = (Open, g)\<close> 
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

lemma bal_not_empty:  
  assumes \<open>bal (x#xs)\<close>
  shows \<open>\<exists>g. x = (Open, g)\<close>
  using assms by (metis (full_types) List.list.distinct(1) List.listrel.simps Product_Type.prod.exhaust_sel bracket.exhaust stk_bal.simps(4) stk_bal_if_bal)



subsection\<open>Function \<^term>\<open>stk_bal_tm\<close>\<close>

text\<open>A version of \<^term>\<open>stk_bal\<close> but for a symbol list that might contain Nonterminals (they are ignored via filtering).\<close>
definition stk_bal_tm :: "('n, bracket \<times> 't) syms \<Rightarrow> 't list \<Rightarrow> ('n, bracket \<times> 't) syms * 't list" where
  \<open>stk_bal_tm \<equiv> (\<lambda>x y . (map Tm (fst ((stk_bal o (map stripTm) o (filter isTm)) x y)), snd ((stk_bal o (map stripTm) o (filter isTm)) x y)))\<close>

lemma stk_bal_tm_append: "stk_bal_tm (xs @ ys) s1 = (let (xs',s1') = stk_bal_tm xs s1 in
stk_bal_tm (xs' @ ys) s1')"
  unfolding stk_bal_tm_def apply auto
   apply (metis (no_types, lifting) old.prod.case stk_bal_append surjective_pairing)
  by (metis (no_types, lifting) split_beta stk_bal_append)

lemma stk_bal_tm_append_if[simp]: "stk_bal_tm xs s1 = ([],s2) \<Longrightarrow> stk_bal_tm (xs @ ys) s1 =
stk_bal_tm ys s2"
  by(simp add: stk_bal_tm_append[of xs])

lemma stk_bal_tm_if_bal_tm:  "bal_tm xs \<Longrightarrow> stk_bal_tm xs s = ([],s)"
  unfolding stk_bal_tm_def 
  by (simp add: bal_tm_def stk_bal_if_bal)+

lemma bal_tm_insert_AB: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Tm (Open, x) # Tm (Close, x) # w)" using u
  unfolding bal_tm_def apply auto
  by (metis bal_insert_AB)

lemma bal_tm_insert_Nt: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Nt A # w)" using u
  unfolding bal_tm_def by auto

corollary stk_bal_tm_iff_bal_tm: "stk_bal_tm w [] = ([],[]) \<longleftrightarrow> bal_tm w"
  unfolding stk_bal_tm_def bal_tm_def apply auto
    apply (metis prod.exhaust_sel stk_bal_iff_bal)
   apply (simp add: stk_bal_if_bal)
  by (simp add: stk_bal_if_bal)

lemma stk_bal_tm_append_inv: \<open>stk_bal_tm (xs@ys) s1 = ([], s') \<Longrightarrow> (let (xs', s1') = stk_bal_tm xs s1 in stk_bal_tm xs s1 = ([], s1'))\<close>
  unfolding stk_bal_tm_def apply auto 
  by (smt (verit, del_insts) case_prodE fstI stk_bal_append_inv surjective_pairing)



subsection\<open>More properties of \<^term>\<open>bal_tm\<close>, using \<^term>\<open>stk_bal_tm\<close>\<close>

theorem bal_tm_append_inv: "bal_tm (u @ v) \<Longrightarrow> bal_tm u \<Longrightarrow> bal_tm v"
  using stk_bal_tm_append_if stk_bal_tm_iff_bal_tm by metis

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