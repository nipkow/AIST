theory detProds
imports "../CFG"
begin

text 
\<open>We call a non-terminal \<open>A\<close> deterministic if the grammar contains a single production of \<open>A\<close> and the form of this production is 
 \<open>(A,w)\<close>. In this case we could replace every occurrence of \<open>A\<close> with \<open>w\<close> on the right-hand sides of the productions and the 
 language of the grammar would be preserved\<close>

(* CFG? *)
lemma Nts_un: 
  "Nt ` Nts (a \<union> as) = Nt ` (Nts a) \<union> Nt ` (Nts as)"
  unfolding Nts_def by blast

(* CFG? *)
lemma Tms_un: 
  "Tm ` Tms (a \<union> as) = Tm ` (Tms a) \<union> Tm ` (Tms as)"
  unfolding Tms_def by blast

(* CFG? *)
lemma nt_tm: "Nt ` nts_of_syms u \<union> Tm ` tms_of_syms u = set u"
unfolding nts_of_syms_def tms_of_syms_def by (auto simp:image_iff) (metis sym.exhaust)

(* CFG? *)
lemma lhss_eq: "lhss ((A,u) # ps) = lhss ((A,s) # ps)"
  by (auto simp: Lhss_def)

(* CFG? *)
lemma Lhss_set: 
  "B \<notin> Lhss P \<Longrightarrow> (B,v) \<notin> P"
  by (auto simp: Lhss_def)

(* CFG? *)
lemma fresh_Lhss: "B \<notin> Nts P \<Longrightarrow> B \<notin> Lhss P"
by (auto simp: Lhss_def Nts_def)

(* CFG? *)
lemma nts_of_syms_set1: "B \<notin> nts_of_syms u \<Longrightarrow> Nt B \<notin> set u"
  by (simp add: nts_of_syms_def)

(* CFG? *)
lemma nts_of_syms_set2: "Nt B \<notin> set u \<Longrightarrow> B \<notin> nts_of_syms u"
  by (simp add: nts_of_syms_def)

(* CFG? *)
lemma Nts_to_syms: "B \<in> Nts P \<Longrightarrow> Nt B \<in> Syms P"
unfolding Nts_def Syms_def
apply (auto split: prod.splits)
 apply blast
using nts_of_syms_set2 by fastforce

(* CFG? *)
lemma syms_to_Nts: "Nt B \<in> Syms P \<Longrightarrow> B \<in> Nts P"
unfolding Nts_def Syms_def
apply (auto split: prod.splits)
 apply blast
using nts_of_syms_set1 by fastforce

(* CFG? *)
lemma Nts_syms_equI: "B \<in> Nts P \<longleftrightarrow> Nt B \<in> Syms P"
  using Nts_to_syms syms_to_Nts by metis

(* CFG? *)
lemma fresh_set: "B \<notin> Nts P \<Longrightarrow> (A,u) \<in> P \<Longrightarrow> Nt B \<notin> set u"
unfolding Nts_def using nts_of_syms_set1 by fastforce

(* CFG? *)
lemma syms_inv:
  "s \<in> Syms P \<longleftrightarrow> (\<exists>A u. (A,u) \<in> P \<and> (s = Nt A \<or> s \<in> set u))"
unfolding Syms_def by auto

(* CFG? *)
lemma syms_subset: 
  "P \<subseteq> P' \<Longrightarrow> s \<in> Syms P \<Longrightarrow> s \<in> Syms P'"
unfolding Syms_def by auto

(* CFG? *)
lemma syms_not_eq: "Nt B \<notin> Syms P \<Longrightarrow> (A,u) \<in> P \<Longrightarrow> A \<noteq> B"
  using syms_inv by blast

(* CFG? *)
lemma syms_not_set: "Nt B \<notin> Syms P \<Longrightarrow> (A,u) \<in> P \<Longrightarrow> Nt B \<notin> set u"
  using syms_inv by blast

(* CFG? *)
lemma syms_Lhss: "Nt B \<notin> Syms P \<Longrightarrow> B \<notin> Lhss P"
unfolding Lhss_def Syms_def by auto

(* CFG? *)
lemma syms_subset2: "Nt B \<notin> Syms P \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> Nt B \<notin> Syms P'"
  using syms_subset by blast

(* CFG? *)
lemma syms_set: "a \<notin> Syms P \<Longrightarrow> (A,u) \<in> P \<Longrightarrow> a \<notin> set u"
  using syms_inv by blast

(* CFG? *)
lemma fresh_syms: "B \<notin> Nts P \<Longrightarrow> Nt B \<notin> Syms P"
  by (metis syms_to_Nts)

(* CFG? *)
lemma syms_Lhss_not_eq: "Nt B \<notin> Syms P \<Longrightarrow> A \<in> Lhss P \<Longrightarrow> A \<noteq> B"
  using syms_Lhss by force

text 
\<open>\<open>substW xs y ys\<close> replaces every occurrence of the element \<open>y\<close> with the list of elements \<open>ys\<close> in the given list \<open>xs\<close>\<close>

fun substW :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "substW [] _ _ = []"
| "substW (x#xs) y ys = (if x = y then ys @ substW xs y ys else x # substW xs y ys)"

subsection \<open>Properties of \<open>substW\<close>\<close>

lemma substW_split: "substW (xs @ xs') y ys = substW xs y ys @ substW xs' y ys"
  by (induction xs) auto

lemma substW_skip: "y \<notin> set xs \<Longrightarrow> substW xs y ys = xs"
  by (induction xs) auto

lemma substW_len: "length (substW xs y [y']) = length xs"
  by (induction xs) auto

lemma substW_rev: "y' \<notin> set xs \<Longrightarrow> substW (substW xs y [y']) y' [y] = xs"
  by (induction xs) auto

lemma substW_der:
  "(B,v) \<in> P \<Longrightarrow> P \<turnstile> u \<Rightarrow>* substW u (Nt B) v"
proof (induction u)
  case Nil
  then show ?case by simp
next
  case (Cons a u)
  then show ?case
    by (metis (no_types, lifting) derivel_Nt_Cons derivel_imp_derive derives_Cons rtranclp.rtrancl_into_rtrancl substW.simps(2))
qed

text
\<open>\<open>substP ps s u\<close> replaces every occurrence of the symbol \<open>s\<close> with the list of symbols \<open>u\<close> on the right-hand sides of the production list \<open>ps\<close>\<close>

definition substP :: "('n, 't) prods \<Rightarrow>  ('n, 't) sym \<Rightarrow>  ('n, 't) syms \<Rightarrow> ('n, 't) prods" where
  "substP ps s u = map (\<lambda>(A,v). (A, substW v s u)) ps"

subsection \<open>Properties of \<open>substP\<close>\<close>

lemma substP_split: "substP (ps @ ps') s u = substP ps s u @ substP ps' s u"
  by (simp add: substP_def)

lemma substP_skip1: "s \<notin> set v \<Longrightarrow> substP ((A,v) # ps) s u = (A,v) # substP ps s u"
  by (auto simp add: substW_skip substP_def)

lemma substP_skip2: "s \<notin> syms ps \<Longrightarrow> substP ps s u = ps"
  by (induction ps) (auto simp add: substP_def substW_skip)

lemma substP_rev: "Nt B \<notin> syms ps \<Longrightarrow> substP (substP ps s [Nt B]) (Nt B) [s] = ps"
proof (induction ps)
  case Nil
  then show ?case
    by (simp add: substP_def)
next
  case (Cons a ps)
  let ?A = "fst a" let ?u = "snd a"
  have "substP (substP (a # ps) s [Nt B]) (Nt B) [s] = substP (map (\<lambda>(A,v). (A, substW v s [Nt B])) (a#ps)) (Nt B) [s]"
    by (simp add: substP_def)
  also have "... = substP ((?A, substW ?u s [Nt B]) # map (\<lambda>(A,v). (A, substW v s [Nt B])) ps) (Nt B) [s]"
    by (simp add: case_prod_unfold)
  also have "... = map ((\<lambda>(A,v). (A, substW v (Nt B) [s]))) ((?A, substW ?u s [Nt B]) # map (\<lambda>(A,v). (A, substW v s [Nt B])) ps)"
    by (simp add: substP_def)
  also have "... = (?A, substW (substW ?u s [Nt B]) (Nt B) [s]) # substP (substP ps s [Nt B]) (Nt B) [s]"
    by (simp add: substP_def)
  also from Cons have "... = (?A, substW (substW ?u s [Nt B]) (Nt B) [s]) # ps"
    using syms_subset set_subset_Cons by metis
  also from Cons.prems have "... = (?A, ?u) # ps"
    using substW_rev syms_inv by (metis list.set_intros(1) prod.collapse)
  also have "... = a # ps" by simp
  finally show ?case .
qed

lemma substP_lhss:
  "lhss ps = lhss (substP ps s u)"
by (auto simp add: Lhss_def substP_def)

lemma if_set_map:
  "x' \<in> set (map f l) \<Longrightarrow> (\<exists>x. x \<in> set l \<and> f x = x')"
  by auto

lemma substP_der:
  "(A,u) \<in> set (substP ps (Nt B) v) \<Longrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
proof -
  assume "(A,u) \<in> set (substP ps (Nt B) v)"
  then have "\<exists>u'. (A,u') \<in> set ps \<and> u = substW u' (Nt B) v" 
    using if_set_map by (smt (verit, del_insts) Pair_inject case_prod_conv old.prod.exhaust substP_def)
  then obtain u' where u'_def: "(A,u') \<in> set ps \<and> u = substW u' (Nt B) v" by blast
  then have path1: "set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u'"
    by (simp add: derive_singleton r_into_rtranclp)
  have "set ((B,v) # ps) \<turnstile> u' \<Rightarrow>* substW u' (Nt B) v"
    using substW_der by (metis list.set_intros(1))
  with u'_def have path2: "set ((B,v) # ps) \<turnstile> u' \<Rightarrow>* u" by simp
  from path1 path2 show ?thesis by simp
qed

text
\<open>In order to prove that the elimination of deterministic non-terminals preserves the language, we prove that a word can be derived if and
 only if the word can be derived after the procedure of elimination. We first show the simpler implication, namely that the list of symbols
 \<open>u\<close> can be derived before the procedure, if \<open>u\<close> can be derived after the procedure\<close>

lemma if_part:
  "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u \<Longrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
proof (induction rule: rtrancl_derive_induct)
  case (step u A v w)
  then show ?case 
    by simp (metis (no_types, lifting) derives_append derives_prepend list.simps(15) rtranclp_trans step.IH substP_der)
qed simp

text
\<open>For the other implication we first show that the list of symbols \<open>u\<close>, where the occurrences of the non-terminal \<open>B\<close> is replaced by the 
 list of symbols \<open>v\<close>, can be derived in the transformed production set if \<open>u\<close> can be derived in the original set of productions extended with
 the production \<open>(B,v)\<close>, under the following assumptions:\<close>

lemma substPW_der:
  assumes prem: "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u"
      and A_B_noteq: "A \<noteq> B"
      and B_notin_dom: "B \<notin> lhss ps"
      and B_notin_v: "Nt B \<notin> set v"
    shows "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* substW u (Nt B) v"
using assms(1) proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case using assms(2) by simp
next
  case (step s B' w v')
  then show ?case
  proof (cases "B = B'")
    case True
    then have "v = v'" 
      using B_notin_dom step.hyps unfolding Lhss_def by auto
    then have "substW (s @ [Nt B'] @ w) (Nt B) v = substW (s @ v' @ w) (Nt B) v" 
      using step.prems B_notin_v True by (simp add: substW_skip substW_split)
    then show ?thesis
      using step.IH by argo
  next
    case False
    then have "(B',v') \<in> set ps"
      using step by auto
    then have "(B', substW v' (Nt B) v) \<in> set (substP ps (Nt B) v)"
      by (metis (no_types, lifting) list.set_map pair_imageI substP_def)
    with rtrancl_into_rtrancl show ?thesis 
      by (smt (verit, ccfv_threshold) False step.IH step.prems derive.simps rtranclp.simps substW.simps(1) substW.simps(2) substW_split sym.inject(1))
  qed
qed

text
\<open>With the assumption that the non-terminal \<open>B\<close> is not in the list of symbols \<open>u\<close>, \<open>substW u (Nt B) v\<close> reduces to \<open>u\<close>\<close>

lemma only_if_part: 
  assumes "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u"
      and A_B_noteq: "A \<noteq> B"
      and B_notin_dom: "B \<notin> lhss ps"
      and B_notin_v: "Nt B \<notin> set v"
      and B_notin_u: "Nt B \<notin> set u"
    shows "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u"
  by (metis assms substW_skip substPW_der)

text
\<open>Combining the two implications gives us the desired property of language preservation\<close>

lemma substP_lang: 
  assumes "B \<notin> lhss ps" and
          "Nt B \<notin> set v" and
          "Nt B \<notin> set u" and
          "A \<noteq> B"
        shows "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u \<longleftrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
  using assms if_part only_if_part by metis

end