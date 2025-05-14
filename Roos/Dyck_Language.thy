(* Author: Moritz Roos *)
theory Dyck_Language
  imports CFG.CFG
begin

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

text\<open>Says that all right hand sides of letters in \<open>x\<close> are in \<open>\<Gamma>\<close>\<close>
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







text\<open>The bracket language over a set \<open>\<Gamma>\<close>.  
Every element \<^prop>\<open>\<gamma> \<in> \<Gamma>\<close> will get a Closing and an Opening version of itself, via pairing with the type bracket.\<close>
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



(*
text\<open>TODO add destructor to definition of \<open>Tm\<close>\<close>
fun strip_tm :: "('a, 'b) sym  \<Rightarrow> 'b" where 
  \<open>strip_tm (Tm t) = t\<close> | 
  \<open>strip_tm (Nt A) = undefined\<close>


definition bal_tm where
\<open>bal_tm \<equiv> bal o (map strip_tm) o (filter isTm)\<close>
*)

section\<open>\<^term>\<open>bal_tm\<close> and \<^term>\<open>rhs_in_tm\<close>\<close>

subsection\<open>\<^term>\<open>bal_tm\<close>\<close>
text\<open>balanced strings of brackets that may contain arbitrary interspersion of Nonterminals\<close>
inductive bal_tm :: "('n, bracket  \<times> ('a)) syms \<Rightarrow> bool" where
  "bal_tm []" |
  "bal_tm [Nt A]" |
  "bal_tm xs \<Longrightarrow> bal_tm ys \<Longrightarrow> bal_tm (xs @ ys)" | 
  "bal_tm xs \<Longrightarrow> bal_tm (Tm (Open, g) # xs @ [Tm (Close, g)])"

declare bal_tm.intros(1,2)[iff] bal_tm.intros(3)[intro, simp] bal_tm.intros(4)[intro!, simp]

lemma bal_tm_prepend_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (Nt A # xs)\<close> 
  using bal_tm.intros(3) by force

lemma bal_tm_append_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (xs@[Nt A])\<close> 
  by blast

lemma bal_tm2[iff]: "bal_tm [Tm (Open,g), Tm (Close,g)]" 
  using bal_tm.intros(1,4) by fastforce

lemma bal_tm2_Nt[iff]: "bal_tm [Tm (Open,g), Tm (Close,g), Nt A]" 
  using bal_tm.intros(1,3,4) by fastforce


(* TODO: mv to CFG *)
lemma map_Tm_inject[dest!]: "map Tm xs = map Tm ys \<Longrightarrow> xs = ys"
  by (metis sym.inject(2) list.inj_map_strong)

lemma map_Tm_inject_iff[simp]: "(map Tm xs = map Tm ys) = (xs = ys)"
  by blast

lemma split_tm_append: \<open>xs @ ys = map Tm zs \<Longrightarrow> \<exists> xs' ys'. (xs' @ ys' = zs) \<and> (xs = map Tm xs') \<and> (ys = map Tm ys')\<close> 
  by (metis append_eq_map_conv)


text\<open>Relationship of \<^term>\<open>bal\<close> and \<^term>\<open>bal_tm\<close>\<close>
lemma bal_imp_bal_tm: \<open>bal xs \<Longrightarrow> bal_tm (map Tm xs)\<close>
  by(induction xs rule: bal.induct; auto)

lemma bal_tm_imp_bal_for_tms: \<open>bal_tm (map Tm xs') \<Longrightarrow> bal xs'\<close>
proof-
  assume assm: \<open>bal_tm (map Tm xs':: ('a, bracket \<times> 'b) sym list)\<close>
  define xs::\<open>('a, bracket \<times> 'b) sym list\<close> where \<open>xs = map Tm xs'\<close> \<comment> \<open>need to enforce the same non-terminal type for xs as for map Tm xs' ...\<close>
  then have \<open>bal_tm xs\<close> 
    using xs_def assm by simp
  from \<open>bal_tm xs\<close> \<open>xs = map Tm xs'\<close> show ?thesis
  proof(induction xs arbitrary: xs' rule: bal_tm.induct)
    case (4 xs g)
    then obtain xs'' where \<open>xs = map Tm xs''\<close> and \<open>xs' = ((Open, g) # (xs'') @ [(Close, g)])\<close> 
      using map_eq_append_conv by (smt (verit, best) Cons_eq_map_D list.map_disc_iff sym.inject(2))
    then have \<open>bal xs''\<close> 
      using "local.4.IH" by blast
    then have \<open>bal ((Open, g) # (xs'') @ [(Close, g)])\<close> 
      by auto
    then show ?case by (simp add: \<open>xs' = (Open, g) # xs'' @ [(Close, g)]\<close>)
  next
    case (3 xs ys)
    then show ?case by (metis append_eq_map_conv bal.intros(2))
  qed auto
qed








subsection\<open>\<^term>\<open>rhs_in_tm\<close>\<close>
text\<open>Says that all right hand sides of \<open>x\<close> (here stripped of their \<open>Tm\<close>) are in \<open>\<Gamma>\<close>.\<close>
definition rhs_in_tm :: \<open>('n, 'a \<times> 'b ) sym list \<Rightarrow> 'b set \<Rightarrow> bool\<close> where
  \<open>rhs_in_tm x \<Gamma> \<equiv> (\<forall>br r. Tm (br, r) \<in> set x \<longrightarrow> r \<in> \<Gamma>)\<close>

lemma rhs_in_tmI[intro]:
  assumes \<open>\<And>r br. Tm (br, r) \<in> set x \<Longrightarrow> r \<in> \<Gamma>\<close>
  shows \<open>rhs_in_tm x \<Gamma>\<close>
  unfolding rhs_in_tm_def using assms by blast

lemma rhs_in_tmD[dest]:
  assumes \<open>rhs_in_tm x \<Gamma>\<close>
  shows \<open>\<And>r br. Tm (br, r) \<in> set x \<Longrightarrow> r \<in> \<Gamma>\<close>
  using assms unfolding rhs_in_tm_def by blast

lemmas rhs_in_tmE = rhs_in_tmD[elim_format]


lemma rhs_in_tm_del_right: \<open>rhs_in_tm (xs@ys) \<Gamma> \<Longrightarrow> rhs_in_tm xs \<Gamma>\<close>
proof-
  assume assm: \<open>rhs_in_tm (xs@ys) \<Gamma>\<close>
  have \<open>set xs \<subseteq> set (xs @ ys)\<close> 
    by simp
  then show ?thesis using rhs_in_tmD[OF assm] by blast
qed

lemmas rhs_in_tm_del_rightE = rhs_in_tm_del_right[elim_format]

lemma rhs_in_tm_del_left[dest]: \<open>rhs_in_tm (xs@ys) \<Gamma> \<Longrightarrow> rhs_in_tm ys \<Gamma>\<close>
proof-
  assume assm: \<open>rhs_in_tm (xs@ys) \<Gamma>\<close>
  have \<open>set ys \<subseteq> set (xs @ ys)\<close> 
    by simp
  then show ?thesis using rhs_in_tmD[OF assm] by blast
qed

lemmas rhs_in_tm_del_leftE = rhs_in_tm_del_left[elim_format]

lemma rhs_in_tm_append[intro, simp]: \<open>rhs_in_tm (xs) \<Gamma> \<Longrightarrow> rhs_in_tm (ys) \<Gamma> \<Longrightarrow> rhs_in_tm (xs@ys) \<Gamma>\<close>
proof-
  assume assm_xs: \<open>rhs_in_tm (xs) \<Gamma>\<close>
  assume assm_ys: \<open>rhs_in_tm (ys) \<Gamma>\<close>
  then have \<open>set (xs@ys) \<subseteq> set xs \<union> set ys\<close> 
    by simp
  then show ?thesis using rhs_in_tmI[of \<open>xs@ys\<close> \<Gamma>] using assm_xs assm_ys by auto
qed


text\<open>Relationship between \<^term>\<open>bal_tm\<close>, \<^term>\<open>rhs_in_tm\<close> and \<open>Dyck_Language\<close>\<close>
lemma Dyck_languageI_tm[intro]: \<open>bal_tm (map Tm xs') \<Longrightarrow> rhs_in_tm (map Tm xs') \<Gamma> \<Longrightarrow> xs' \<in> Dyck_language \<Gamma>\<close>
proof-
  assume bal: \<open>bal_tm (map Tm xs')\<close> and rhs: \<open>rhs_in_tm (map Tm xs') \<Gamma>\<close>
  then have \<open>bal xs'\<close> 
    using bal_tm_imp_bal_for_tms by blast
  moreover have \<open>\<And>br r. (br, r) \<in> set xs' \<Longrightarrow> r \<in> \<Gamma>\<close> 
    using rhs by (metis (no_types, lifting) List.list.simps(15,9) insert_iff map_append rhs_in_tmD rhs_in_tm_del_left split_list_last)
  ultimately show ?thesis using Dyck_languageI[of xs' \<Gamma>] by blast
qed













section\<open>Function based equivalent description of \<^term>\<open>bal\<close> and \<^term>\<open>bal_tm\<close>, from T. Nipkow\<close>

subsection\<open>\<^term>\<open>bal\<close>\<close>

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



lemma stk_bal_if_stk_bal: "stk_bal w s = ([],[]) \<Longrightarrow> bal (rev(map (\<lambda>x. (Open, x)) s) @ w)"
proof(induction w s rule: stk_bal.induct)
  case (2 x xs s)
  then show ?case by simp
next
  case (3 x xs y s)
  then show ?case by (auto simp add: bal_insert_AB split: if_splits) 
qed (auto)


corollary stk_bal_iff_bal: "stk_bal w [] = ([],[]) \<longleftrightarrow> bal w"
  using stk_bal_if_stk_bal[of w "[]"] stk_bal_if_bal by auto

theorem bal_append_inv: "bal (u @ v) \<Longrightarrow> bal u \<Longrightarrow> bal v"
  using stk_bal_append_if stk_bal_iff_bal by metis


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








subsection\<open>\<^term>\<open>bal_tm\<close>\<close>

text\<open>A stack machine that puts open brackets to the stack, to remember that they must be matched by a closed bracket\<close>
fun stk_bal_tm :: "('n, bracket \<times> 't) syms \<Rightarrow> 't list \<Rightarrow> ('n, bracket \<times> 't) syms * 't list" where
  "stk_bal_tm [] s = ([],s)" |
  "stk_bal_tm (Tm (Open, g) # xs) s = stk_bal_tm xs (g#s)" |
  "stk_bal_tm (Tm (Close, g) # xs) (g'#s) = (if g=g' then stk_bal_tm xs s else ((Tm (Close, g) # xs), g'#s))" | 
  \<open>stk_bal_tm (Nt A # xs) s = stk_bal_tm xs s\<close> | 
  "stk_bal_tm xs s = (xs,s)"

lemma stk_bal_tm_append: "stk_bal_tm (xs @ ys) s1 = (let (xs',s1') = stk_bal_tm xs s1 in
stk_bal_tm (xs' @ ys) s1')"
  by(induction xs s1 rule:stk_bal_tm.induct) (auto split: if_splits)

lemma stk_bal_tm_append_if[simp]: "stk_bal_tm xs s1 = ([],s2) \<Longrightarrow> stk_bal_tm (xs @ ys) s1 =
stk_bal_tm ys s2"
  by(simp add: stk_bal_tm_append[of xs])

lemma stk_bal_tm_if_bal_tm:  "bal_tm xs \<Longrightarrow> stk_bal_tm xs s = ([],s)"
  by(induction arbitrary: s rule: bal_tm.induct)(auto split: if_splits)



lemma bal_tm_insert_AB: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Tm (Open, x) # Tm (Close, x) # w)" using u
proof(induction arbitrary: v w)
  case 1 thus ?case by simp
next
  case (2 A v w)
  then show ?case
  proof(cases v)
    case Nil
    with 2 have \<open>w = [Nt A]\<close> 
      by (metis append_Nil)
    show ?thesis unfolding Nil \<open>w = [Nt A]\<close> by simp
  next
    case (Cons a list)
    with 2 have \<open>v = [Nt A]\<close> 
      by simp
    then have \<open>w = []\<close> using "2" 
      by blast
    then show ?thesis unfolding \<open>v = [Nt A]\<close> \<open>w = []\<close> by simp
  qed
next
  case (4 u y)
  show ?case
  proof (cases v)
    case Nil
    hence "w = (Tm (Open, y)) # u @ [Tm (Close, y)]" 
      using "4.prems" by simp
    hence "bal_tm w" 
      using "4.hyps" by blast
    hence "bal_tm ([Tm (Open, x), Tm (Close, x)] @ w)" 
      by blast
    thus ?thesis using Nil by simp
  next
    case (Cons X v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      from "4.hyps" have "bal_tm ((Tm (Open, x) # u @ [Tm (Close, x)]) @ [Tm (Open, x), Tm (Close, x)])"
        using bal.intros(2) by blast
      thus ?thesis using Nil Cons 4
        by (metis append_Nil append_Nil2 bal_tm.simps)
    next
      case (snoc w' Y)
      hence u: "u=v'@w'" and [simp]: "X=Tm (Open, y) & Y=Tm (Close, y)"
        using Cons "4.prems" apply (smt (verit, ccfv_threshold) List.append.assoc List.list.inject append_Cons append_eq_append_conv last_snoc)
        by (metis "local.4.prems" Cons List.append.assoc List.list.inject append_Cons last_snoc snoc)
          \<comment> \<open>This also works by auto, but it takes 4 seconds.\<close>
      thus ?thesis
        by (metis "4.IH" append.assoc append_Cons local.Cons bal_tm.intros(4) snoc)
    qed
  qed
next
  case (3 v' w')
  then obtain r where "v'=v@r \<and> r@w'=w \<or> v'@r=v \<and>w'=r@w" (is "?A \<or> ?B")
    by (meson append_eq_append_conv2)
  thus ?case
  proof
    assume A: ?A
    hence "bal_tm (v @ Tm (Open, x) # Tm (Close, x) # r)" 
      using "3.IH"(1) by presburger
    hence "bal_tm ((v @ Tm (Open, x) # Tm (Close, x)#r) @ w')" 
      using \<open>bal_tm w'\<close> by(rule bal_tm.intros(3))
    thus ?thesis using A by auto
  next
    assume B: ?B
    hence "bal_tm (r @ Tm (Open, x) # Tm (Close, x) # w)" 
      using "3.IH"(2) by presburger
    with \<open>bal_tm v'\<close> have "bal_tm (v'@(r@Tm (Open, x) # Tm (Close, x)#w))" 
      by(rule bal_tm.intros(3))
    thus ?thesis using B by force
  qed 
qed 


lemma bal_tm_insert_Nt: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Nt A # w)" using u
proof(induction arbitrary: v w)
  case 1
  then show ?case by blast
next
  case (2 A)
  then show ?case
  proof(cases v)
    case Nil
    with 2 have \<open>w = [Nt A]\<close> 
      by (metis append_Nil)
    show ?thesis unfolding Nil \<open>w = [Nt A]\<close> by simp
  next
    case (Cons a list)
    with 2 have \<open>v = [Nt A]\<close> 
      by simp
    then have \<open>w = []\<close> 
      using "2" by blast
    then show ?thesis unfolding \<open>v = [Nt A]\<close> \<open>w = []\<close> by simp
  qed 
next
  case (3 v' w')
  then obtain r where \<open>(v' = v@r) \<and> (r@w' = w) \<or> (w' = r@w) \<and> (v'@r = v)\<close> (is \<open>?A \<or> ?B\<close>) 
    by (meson append_eq_append_conv2)
  then show ?case
  proof
    assume A: ?A
    then have \<open>bal_tm (v @ Nt A # r)\<close> 
      using "3.IH" by presburger
    then have \<open>bal_tm (v @ Nt A # r @ w')\<close> 
      using \<open>bal_tm w'\<close> using bal_tm.intros(3) by fastforce 
    then show ?thesis using A by blast
  next
    assume B: ?B
    then have \<open>bal_tm (r @ Nt A # w)\<close> 
      using "3.IH" by presburger
    then have \<open>bal_tm (v' @ r @ Nt A # w)\<close> 
      using \<open>bal_tm v'\<close> using bal_tm.intros(3) by fastforce 
    then show ?thesis using B by (metis List.append.assoc)
  qed
next

  case (4 u y)
  show ?case
  proof (cases v)
    case Nil
    hence "w = (Tm (Open, y)) # u @ [Tm (Close, y)]" 
      using "4.prems" by simp
    hence "bal_tm w" 
      using "4.hyps" by blast
    hence "bal_tm ([Nt A] @ w)" 
      by blast
    thus ?thesis using Nil by simp
  next
    case (Cons X v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      thus ?thesis using Nil Cons 4
        by (metis append_Nil2 bal_tm.simps)
    next
      case (snoc w' Y)
      hence u: "u=v'@w'" and [simp]: "X=Tm (Open, y) & Y=Tm (Close, y)"
        using Cons "4.prems" apply (smt (verit, ccfv_threshold) List.append.assoc List.list.inject append_Cons append_eq_append_conv last_snoc)
        by (metis "local.4.prems" Cons List.append.assoc List.list.inject append_Cons last_snoc snoc)
          \<comment> \<open>This also works by auto, but it takes 4 seconds.\<close>
      thus ?thesis
        by (metis "4.IH" append.assoc append_Cons local.Cons bal_tm.intros(4) snoc)
    qed
  qed
qed


lemma stk_bal_if_stk_bal_tm: "stk_bal_tm w s = ([],[]) \<Longrightarrow> bal_tm (rev(map (\<lambda>x. Tm (Open, x)) s) @ w)"
proof(induction w s rule: stk_bal_tm.induct)
  case (2 x xs s)
  then show ?case by simp
next
  case (3 x xs y s)
  then show ?case by (auto simp add: bal_tm_insert_AB split: if_splits)
next
  case (4 A xs s)
  then have \<open>stk_bal_tm xs s = ([], [])\<close> 
    by simp
  then show ?case by (metis "local.4.IH" bal_tm_insert_Nt)
qed (auto)

corollary stk_bal_tm_iff_bal_tm: "stk_bal_tm w [] = ([],[]) \<longleftrightarrow> bal_tm w"
  using stk_bal_if_stk_bal_tm[of w "[]"] stk_bal_tm_if_bal_tm by auto

theorem bal_tm_append_inv: "bal_tm (u @ v) \<Longrightarrow> bal_tm u \<Longrightarrow> bal_tm v"
  using stk_bal_tm_append_if stk_bal_tm_iff_bal_tm by metis


lemma stk_bal_tm_append_inv: \<open>stk_bal_tm (xs@ys) s1 = ([], s') \<Longrightarrow> (let (xs', s1') = stk_bal_tm xs s1 in stk_bal_tm xs s1 = ([], s1'))\<close>
proof(induction xs s1 arbitrary: ys rule: stk_bal_tm.induct)
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
next
  case (5 vd va)
  then show ?case by(auto split: prod.splits)
qed


lemma bal_tm_insert: 
  assumes u: "bal_tm u" 
    and b: \<open>bal_tm b\<close>
  shows "u = v@w \<Longrightarrow> bal_tm (v @ b @ w)" 
proof-
  assume uvw: \<open>u = v@w\<close>
  have \<open>stk_bal_tm (b) [] = ([],[])\<close> 
    using assms stk_bal_tm_iff_bal_tm by blast
  have \<open>stk_bal_tm (u) [] = ([],[])\<close> 
    using assms stk_bal_tm_iff_bal_tm by blast
  then obtain s1' where s1'_def: \<open>stk_bal_tm v [] = ([], s1')\<close> 
    by (metis (full_types, lifting) uvw case_prodE stk_bal_tm_append_inv)
  then obtain s' where s'_def: \<open>stk_bal_tm (v @ w) [] = stk_bal_tm (w) s'\<close> 
    using stk_bal_tm_append_if by blast
  then have \<open>([],[]) = stk_bal_tm (v @ w) []\<close> 
    using uvw using \<open>stk_bal_tm u [] = ([], [])\<close> by presburger
  also have \<open>... = stk_bal_tm (w) s'\<close> 
    using s'_def by simp
  also have \<open>... = stk_bal_tm (b@w) s'\<close> 
    by (metis b stk_bal_tm_append_if stk_bal_tm_if_bal_tm)
  finally have \<open>stk_bal_tm (b@w) s' = ([],[])\<close> 
    by simp
  then have \<open>stk_bal_tm (v @ b @ w) [] = ([],[])\<close> 
    using s1'_def by (metis b s'_def stk_bal_tm_append_if stk_bal_tm_if_bal_tm)
  then show \<open>bal_tm (v @ b @ w)\<close> 
    using stk_bal_tm_iff_bal_tm by blast
qed




lemma bal_tm_del: 
  assumes u: "bal_tm u" 
    and b: \<open>bal_tm b\<close>
  shows "u = v @ b @ w \<Longrightarrow> bal_tm (v @ w)" 
proof-
  assume uvbw: \<open>u = v @ b @ w\<close>
  have stk_bal_tm_b: \<open>stk_bal_tm (b) [] = ([],[])\<close> 
    using assms stk_bal_tm_iff_bal_tm by blast
  have stk_bal_tm_vbw: \<open>stk_bal_tm (v @ b @ w) [] = ([],[])\<close> 
    using uvbw assms stk_bal_tm_iff_bal_tm by blast
  then obtain s1' where s1'_def: \<open>stk_bal_tm v [] = ([], s1')\<close> 
    by (metis (full_types, lifting) case_prodE stk_bal_tm_append_inv)
  then have \<open>stk_bal_tm (v@b) [] = ([], s1')\<close> 
    by (metis b stk_bal_tm_append_if stk_bal_tm_if_bal_tm)
  then have \<open>stk_bal_tm (v @  w) [] = ([],[])\<close> 
    using stk_bal_tm_vbw s1'_def by (metis stk_bal_tm_append_if)
  then show \<open>bal_tm (v @ w)\<close> 
    using stk_bal_tm_iff_bal_tm by blast
qed


corollary bal_tm_iff_insert[iff]:
  assumes \<open>bal_tm b\<close>
  shows \<open>bal_tm (v @ b @ w) = bal_tm (v @ w)\<close>
  using bal_tm_del bal_tm_insert by (metis assms)






end