(* Author: Moritz Roos, Tobias Nipkow *)

(*section \<open>Dyck Languages over Type @{typ "'a  syms"}\<close>*)

theory Dyck_Language_Syms
  imports Dyck_Language "CFG.CFG"
begin

(*TODO now in CFG *)
fun destTm :: "('a, 'b) sym  \<Rightarrow> 'b" where 
  \<open>destTm (Tm t) = t\<close> | 
  \<open>destTm (Nt A) = undefined\<close>

lemma destTm_Tm[simp]: \<open>destTm \<circ> Tm = id\<close>
by auto
(* until here*)

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

lemma bal_tm_surr[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (Tm (Open a) # xs @ [Tm (Close a)])\<close> 
  unfolding bal_tm_def by simp

lemma bal_tm_prepend_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (Nt A # xs)\<close> 
  by (simp add: bal_tm_def)

lemma bal_tm_append_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (xs@[Nt A])\<close> 
  by blast

lemma bal_tm2[iff]: "bal_tm [Tm (Open a), Tm (Close a)]"
  using bal_tm_surr by force

lemma bal_tm2_Nt[iff]: "bal_tm [Tm (Open a), Tm (Close a), Nt A]" 
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


subsection\<open>Function \<open>snds_in_tm\<close>\<close>

text\<open>Version of \<open>snds_in\<close> but for a list of symbols, that might contain Nonterminals.
Says that all right hand sides of \<open>x\<close> (here stripped of their \<open>Tm\<close>) are in \<open>\<Gamma>\<close>:\<close>
definition snds_in_tm where
  \<open>snds_in_tm \<Gamma> \<equiv> snds_in \<Gamma> o map destTm o filter isTm\<close>
(*
text\<open>Useful lemmas about this:\<close>
lemma snds_in_tm_del_right: \<open>snds_in_tm \<Gamma> (xs@ys) \<Longrightarrow> snds_in_tm \<Gamma> xs\<close> 
  unfolding snds_in_tm_def by auto

lemma snds_in_tm_del_left: \<open>snds_in_tm \<Gamma> (xs@ys) \<Longrightarrow> snds_in_tm \<Gamma> ys\<close>
  unfolding snds_in_tm_def by auto
*)
lemma snds_in_tm_Nt[simp]:
  \<open>snds_in_tm \<Gamma> (Nt A # xs) = snds_in_tm \<Gamma> xs\<close>
unfolding snds_in_tm_def by auto

lemma snds_in_tm_append[simp]:
  \<open>snds_in_tm \<Gamma> (xs@ys) = (snds_in_tm \<Gamma> xs \<and> snds_in_tm \<Gamma> ys)\<close>
unfolding snds_in_tm_def by auto

text\<open>Relationship between \<^term>\<open>bal_tm\<close>, \<^term>\<open>snds_in_tm\<close> and \<open>Dyck_Language\<close>\<close>
lemma Dyck_langI_tm[intro]:
  \<open>bal_tm (map Tm xs') \<Longrightarrow> snds_in_tm \<Gamma> (map Tm xs') \<Longrightarrow> xs' \<in> Dyck_lang \<Gamma>\<close>
unfolding bal_tm_def snds_in_tm_def by auto


subsection\<open>Lifting \<^const>\<open>bal\<close> and \<^const>\<open>bal_tm\<close> to @{type syms}\<close>


subsubsection\<open>Function \<open>bal_stk_tm\<close>\<close>

text\<open>A version of \<^term>\<open>bal_stk\<close> but for a symbol list that might contain nonterminals (they are ignored via filtering).\<close>
definition bal_stk_tm :: "'t list \<Rightarrow> ('n, 't bracket) syms \<Rightarrow> 't list * ('n, 't bracket) syms" where
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

lemma bal_tm_insert_AB: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Tm (Open x) # Tm (Close x) # w)" using u
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