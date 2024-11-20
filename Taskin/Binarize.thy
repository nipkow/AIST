theory Binarize
imports "../CFG"
begin

(* FFPI *)
lemma funpow_fix: fixes f :: "'a \<Rightarrow> 'a" and m :: "'a \<Rightarrow> nat"
assumes "\<And>x. m(f x) < m x \<or> f x = x"
shows "f((f ^^ m x) x) = (f ^^ m x) x"
proof -
 have "n + m ((f^^n) x) \<le> m x \<or> f((f^^n) x) = (f^^n) x" for n
 proof(induction n)
   case 0
   then show ?case by simp
 next
   case (Suc n)
   then show ?case
   proof
     assume a1: "n + m ((f ^^ n) x) \<le> m x"
     then show ?thesis
     proof (cases "m ((f ^^ Suc n) x) < m ((f ^^ n) x)")
       case True
       then show ?thesis using a1 by auto
     next
       case False
       with assms have "(f ^^ Suc n) x = (f ^^ n) x" by auto
       then show ?thesis by simp
     qed
   next
     assume "f ((f ^^ n) x) = (f ^^ n) x"
     then show ?thesis by simp
   qed
 qed
  from this[of "m x"] show ?thesis using assms[of "(f ^^ m x) x"] by auto
qed

(* definition of binarize *)

fun binarize1 :: "('n :: infinite, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize1 ps' [] = []"
| "binarize1 ps' ((A, []) # ps) = (A, []) # binarize1 ps' ps"
| "binarize1 ps' ((A, [s0]) # ps) = (A,[s0]) # binarize1 ps' ps"
| "binarize1 ps' ((A, [s0,s1]) # ps) = (A, [s0,s1]) # binarize1 ps' ps"
| "binarize1 ps' ((A, s0 # u) # ps) = (let B = fresh ps' in (A,[s0, Nt B]) # (B, u) # ps)"

definition binarize' :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize' ps = binarize1 ps ps"

fun count :: "('n::infinite, 't) prods \<Rightarrow> nat" where
  "count [] = 0"
| "count ((A,u) # ps) = (if length u \<le> 2 then count ps else length u + count ps)"

definition binarize :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize ps = (binarize' ^^ (count ps)) ps"

(* fixed point iteration*)

lemma count_dec1:
  assumes "binarize1 ps' ps \<noteq> ps" 
  shows "count ps > count (binarize1 ps' ps)"
using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by simp
next
  case (3 ps' A s0 ps)
  then show ?case by simp
next
  case (4 ps' A s0 s1 ps)
  then show ?case by simp
next
  case (5 ps' A s0 v vb vc ps)
  then have "count (binarize1 ps' ((A, s0 # v # vb # vc) # ps)) = 
             count ((A,[s0, Nt (fresh ps')]) # (fresh ps', v # vb # vc) # ps)" by (metis binarize1.simps(5))
  also have "... = count ((fresh ps', v # vb # vc) # ps)" by simp
  also have "... < count ((fresh ps', s0 # v # vb # vc) # ps)" by simp
  also have "... = count ((A, s0 # v # vb # vc) # ps)" by simp
  finally show ?case by simp
qed

lemma count_dec:
  assumes "binarize' ps \<noteq> ps" 
  shows "count ps > count (binarize' ps)"
  using count_dec1 binarize'_def assms by metis

lemma binarize_ffpi:
  "binarize'((binarize' ^^ count x) x) = (binarize' ^^ count x) x"
proof -
  have "\<And>x. count(binarize' x) < count x \<or> binarize' x = x"
    using count_dec by blast
  then show ?thesis using funpow_fix by metis
qed

(* proof for binary productions only *)

lemma binarize_binary1: 
  assumes "ps = binarize1 ps' ps"
  shows "(A,w) \<in> set(binarize1 ps' ps) \<Longrightarrow> length w \<le> 2"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A s0 ps)
  then show ?case by auto
next
  case (4 ps' A s0 s1 ps)
  then show ?case by auto
next
  case (5 ps' A s0 v vb vc ps)
  then have "(A,[s0, Nt (fresh ps')]) # (fresh ps', v # vb # vc) # ps = binarize1 ps' ((A, s0 # v # vb # vc) # ps)"
    by (metis binarize1.simps(5))
  also from 5 have "... = (A, s0 # v # vb # vc) # ps"
    by argo
  finally have "(A,[s0, Nt (fresh ps')]) # (fresh ps', v # vb # vc) # ps = (A, s0 # v # vb # vc) # ps"
    by blast
  then show ?case
    by simp
qed

lemma binarize_binary':
  assumes "ps = binarize' ps"
  shows "(A,w) \<in> set(binarize' ps) \<Longrightarrow> length w \<le> 2"
  using assms binarize_binary1 binarize'_def by metis

lemma length_binarize: "(A,w) \<in> set(binarize ps) \<Longrightarrow> length w \<le> 2"
  unfolding binarize_def using binarize_ffpi binarize_binary' by metis

(* definitions for inlining *)

fun substW :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "substW [] _ _ = []"
| "substW (x#xs) y ys = (if x = y then ys @ substW xs y ys else x # substW xs y ys)"

(* facts about substW *)
(* may be unnecesarry *)

lemma substW_split: "substW (xs @ xs') y ys = substW xs y ys @ substW xs' y ys"
  by (induction xs) auto

lemma substW_skip: "y \<notin> set xs \<Longrightarrow> substW xs y ys = xs"
  by (induction xs) auto

lemma substW_len: "length (substW xs y [y']) = length xs"
  by (induction xs) auto

lemma substW_rev: "y' \<notin> set xs \<Longrightarrow> substW (substW xs y [y']) y' [y] = xs"
  by (induction xs) auto

(* refine *)
lemma substW_der:
  "(B,v) \<in> set ps \<Longrightarrow> (set ps) \<turnstile> u \<Rightarrow>* substW u (Nt B) v"
proof (induction u)
  case Nil
  then show ?case by simp
next
  case (Cons a u)
  then show ?case
    by (metis (no_types, lifting) derivel_Nt_Cons derivel_imp_derive derives_Cons rtranclp.rtrancl_into_rtrancl substW.simps(2))
qed

(* inlining *)
definition substP :: "('n::infinite, 't) prods \<Rightarrow>  ('n, 't) sym \<Rightarrow>  ('n, 't) syms \<Rightarrow> ('n, 't) prods" where
  "substP ps s u = map (\<lambda>(A,v). (A, substW v s u)) ps"

(* domain *)
fun dom :: "('n::infinite, 't) prods \<Rightarrow> 'n list" where
  "dom [] = []"
| "dom ((A,u) # ps) = A # dom ps"

(* symbols *)
fun syms :: "('n::infinite, 't) prods \<Rightarrow> ('n,'t) syms" where
  "syms [] = []"
| "syms ((A,v)#ps) = Nt A # v @ syms ps"

lemma syms_inv:
  "s \<in> set (syms ps) \<longleftrightarrow> (\<exists>A u. (A,u) \<in> set ps \<and> (s = Nt A \<or> s \<in> set u))"
proof
  assume "s \<in> set (syms ps)"
  then show "\<exists>A u. (A, u) \<in> set ps \<and> (s = Nt A \<or> s \<in> set u)"
  proof (induction ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a ps)
    let ?A = "fst a" let ?u = "snd a"
    have A_u_set: "(?A, ?u) \<in> set (a # ps)" by simp
    then show ?case proof (cases "s \<in> set (syms ps)")
      case True
      then show ?thesis using Cons.IH by auto
    next
      case False
      with Cons.prems have "s \<in> set (Nt ?A # ?u)" 
        by (metis (no_types, opaque_lifting) Un_iff append_eq_Cons_conv set_append split_pairs syms.simps(2))
      then have "(s = Nt ?A \<or> s \<in> set ?u)" by auto
      with A_u_set show ?thesis by blast
    qed
  qed
next
  assume asm: "\<exists>A u. (A, u) \<in> set ps \<and> (s = Nt A \<or> s \<in> set u)"
  then show "s \<in> set (syms ps)"
  proof (induction ps)
    case Nil
    then show ?case by simp
  next
    case (Cons a ps)
    with asm obtain A u where A_u_def: "(A, u) \<in> set (a # ps) \<and> (s = Nt A \<or> s \<in> set u)" by blast
    then show ?case proof (cases "(A, u) \<in> set ps")
      case True
      with Cons.IH A_u_def show ?thesis
        by (metis (mono_tags, lifting) Un_iff list.discI list.sel(3) list.set_intros(2) set_append syms.elims)
    next
      case False
      with A_u_def have "(A,u) = a" by simp
      then show ?thesis
        using A_u_def by force
    qed
  qed
qed

lemma syms_subset: 
  "set ps \<subseteq> set ps' \<Longrightarrow> s \<in> set (syms ps) \<Longrightarrow> s \<in> set (syms ps')"
  by (induction ps) (auto simp add: syms_inv)

(* facts about substP*)
(* may be unnecesarry *)

lemma substP_split: "substP (ps @ ps') s u = substP ps s u @ substP ps' s u"
  by (simp add: substP_def)

lemma substP_skip1: "s \<notin> set v \<Longrightarrow> substP ((A,v) # ps) s u = (A,v) # substP ps s u"
  by (auto simp add: substW_skip substP_def)

lemma substP_skip2: "s \<notin> set (syms ps) \<Longrightarrow> substP ps s u = ps"
  by (induction ps) (auto simp add: substP_def substW_skip)

lemma substP_rev: "Nt B \<notin> set (syms ps) \<Longrightarrow> substP (substP ps s [Nt B]) (Nt B) [s] = ps"
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
  finally show ?case by simp
qed

lemma substP_dom:
"dom ps = dom (substP ps s u)"
  by (induction ps) (auto simp add: substP_def)

(* inlining proofs *)

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

(* refine *)
lemma if_part:
  "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u \<Longrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case 
    using substP_der by (smt (verit, best) derive.simps derives_append derives_prepend rtranclp_trans)
qed

lemma dom_set: 
  "B \<notin> set (dom ps) \<Longrightarrow> (B,v) \<notin> set ps"
by (induction ps) auto

(* refine and rename *)
lemma subst_P_W: 
  assumes prem: "set ((B,v)#ps) \<turnstile> nta \<Rightarrow>* u"
      and NTA_def: "nta = [Nt A]"
      and A_B_noteq: "A \<noteq> B"
      and B_notin_dom: "B \<notin> set (dom ps)"
      and B_notin_v: "Nt B \<notin> set v"
    shows "set (substP ps (Nt B) v) \<turnstile> nta \<Rightarrow>* substW u (Nt B) v"
using assms proof (induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then obtain s B' v' w where b_c_def: "b = s @ [Nt B'] @ w \<and> c = s @ v' @ w \<and> (B',v') \<in> set ((B, v) # ps)" 
    by (meson derive.simps)
  then show ?case
  proof (cases "B = B'")
    case True
    then have "v = v'" 
      using B_notin_dom b_c_def dom_set by auto
    then have "substW b (Nt B) v = substW c (Nt B) v" 
      using b_c_def B_notin_v True by (simp add: substW_skip substW_split)
    then show ?thesis
      using A_B_noteq B_notin_dom B_notin_v rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by argo
  next
    case False
    then have "(B',v') \<in> set ps"
      using b_c_def by auto
    then have "(B', substW v' (Nt B) v) \<in> set (substP ps (Nt B) v)"
      by (metis (no_types, lifting) list.set_map pair_imageI substP_def)
    with rtrancl_into_rtrancl show ?thesis  
      by (smt (verit, ccfv_threshold) False b_c_def derive.simps rtranclp.simps substW.simps(1) substW.simps(2) substW_split sym.inject(1))
  qed
qed

(* rename *)
lemma only_if_part: 
  assumes "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u"
      and A_B_noteq: "A \<noteq> B"
      and B_notin_dom: "B \<notin> set (dom ps)"
      and B_notin_v: "Nt B \<notin> set v"
      and B_notin_u: "Nt B \<notin> set u"
    shows "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u"
  by (metis assms substW_skip subst_P_W)

lemma substP_lang: 
  assumes "B \<notin> set (dom ps)" and
          "Nt B \<notin> set v" and
          "Nt B \<notin> set u" and
          "A \<noteq> B"
        shows "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u \<longleftrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
  using assms if_part only_if_part by blast

(* Helper lemmas for binarization proofs *)

(* rename *)
lemma fresh_dom: "B \<notin> nts (set ps) \<Longrightarrow> B \<notin> set (dom ps)"
  by (induction ps) (auto simp add: nts_def)

(* rename *)
lemma nt11: "B \<notin> nt u \<Longrightarrow> Nt B \<notin> set u"
  by (induction u rule: nt.induct) auto

lemma nt12: "Nt B \<notin> set u \<Longrightarrow> B \<notin> nt u"
  by (induction u rule: nt.induct) auto

(* refine and rename *)
lemma fresh_sym: "B \<notin> nts (set ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> Nt B \<notin> set u"
  apply (induction ps) 
   apply simp
  using nt11 nts_def by fastforce

(* refine and rename *)
lemma fresh_syms: "B \<notin> nts (set ps) \<Longrightarrow> Nt B \<notin> set (syms ps)"
  apply (induction ps)
   apply simp
  by (metis dom_set fresh_dom fresh_sym sym.inject(1) syms_inv)

(* rename *)
lemma syms_not_eq: "Nt B \<notin> set (syms ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> A \<noteq> B"
  by (induction ps) auto

(* rename *)
lemma syms_not_set: "Nt B \<notin> set (syms ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> Nt B \<notin> set u"
  by (induction ps) auto

(* rename *)
lemma fresh_sym_dom: "Nt B \<notin> set (syms ps) \<Longrightarrow> N \<in> set (dom ps) \<Longrightarrow> N \<noteq> B"
  by (induction ps) auto

(* rename *)
lemma syms_dom: "Nt B \<notin> set (syms ps) \<Longrightarrow> B \<notin> set (dom ps)"
  by (induction ps) auto

(* rename and refine *)
lemma syms_dom2: "Nt B \<notin> set (syms ps) \<Longrightarrow> set ps' = set ps \<Longrightarrow> B \<notin> set (dom ps')"
  apply (induction ps) 
   apply auto
  by (metis insertE prod.sel(1) prod.sel(2) sym.inject(1) syms_dom syms_inv)

(* rename *)
lemma dom_eq: "set (dom ((A,u) # ps)) = set (dom ((A,s) # ps))"
  by auto

(* rename and refine *)
lemma syms_dom3: "Nt B \<notin> set (syms ps) \<Longrightarrow> set ps' \<subseteq> set ps \<Longrightarrow> Nt B \<notin> set (syms ps')"
  apply (induction ps')
   apply auto
  using syms_not_eq apply blast
  by (meson syms_not_set)

(* rename *)
lemma helpppp:"a \<notin> set (syms ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> a \<notin> set u"
  by (induction ps) auto

(* refine *)
lemma binarize1_cases:
  "binarize1 ps' ps = ps \<or> (\<exists>A ps'' B u s. set ps = {(A, s#u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A,[s,Nt B]),(B,u)} \<union> set ps'' \<and> Nt B \<notin> set (syms ps'))"
proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' C ps)
  then show ?case
  proof (cases "binarize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> set (syms ps')"
      using 2 by blast
    from defs have wit: "set ((C, []) # ps) = {(A, s # u)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit2: "set (binarize1 ps' ((C, []) # ps)) = {(A, [s, Nt B]), (B, u)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> set (syms ps')" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (3 ps' C s0 ps)
  then show ?case proof (cases "binarize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> set (syms ps')"
      using 3 by blast
    from defs have wit: "set ((C, [s0]) # ps) = {(A, s # u)} \<union> set ((C, [s0]) # ps'')" by simp
    from defs have wit2: "set (binarize1 ps' ((C, [s0]) # ps)) = {(A, [s, Nt B]), (B, u)} \<union> set ((C, [s0]) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> set (syms ps')" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (4 ps' C s0 s1 ps)
  then show ?case  proof (cases "binarize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> set (syms ps')"
      using 4 by blast
    from defs have wit: "set ((C, [s0,s1]) # ps) = {(A, s # u)} \<union> set ((C, [s0,s1]) # ps'')" by simp
    from defs have wit2: "set (binarize1 ps' ((C, [s0,s1]) # ps)) = {(A, [s, Nt B]), (B, u)} \<union> set ((C, [s0,s1]) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> set (syms ps')" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (5 ps' C s0 v vb vc ps)
  then show ?case 
    by (metis Un_insert_left binarize1.simps(5) fresh fresh_syms list.simps(15) sup_bot_left)
qed

(* Binarization proofs for preserving language *)

(* refine *)
lemma binarize_der1:
  assumes "N \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize1 ps ps) \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
 proof (cases "binarize1 ps ps = ps")
  case True
  then show ?thesis by simp
next
  case False
  then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> set (syms ps)"
    by (meson binarize1_cases)
  from defs have a_notb: "A \<noteq> B" using syms_not_eq by fast
  from defs have a3: "Nt B \<notin> set u" using syms_not_set by fastforce
  from defs have notB: "Nt B \<notin> set (syms ps'')" using syms_dom3 by auto
  then have 1: "set ps = set (substP ((A, [s, Nt B]) # ps'') (Nt B) u)" proof -
    from defs have "set ps = {(A, s # u)} \<union> set ps''" by simp
    also have "... = set ((A, s#u) # ps'')" by simp
    also have "... = set ([(A, s#u)] @ ps'')" by simp
    also from defs have "... = set ([(A,substW [s, Nt B] (Nt B) u)] @ ps'')" using helpppp by fastforce
    also have "... = set ((substP [(A, [s, Nt B])] (Nt B) u) @ ps'')" by (simp add: substP_def)
    also have "... = set ((substP [(A, [s, Nt B])] (Nt B) u) @ substP ps'' (Nt B) u)" using notB by (simp add: substP_skip2)
    also have "... = set (substP ((A, [s, Nt B]) # ps'') (Nt B) u)" by (simp add: substP_def)
    finally show ?thesis by simp
    qed
  from defs have 2: "set (binarize1 ps ps) = set ((A, [s, Nt B]) # (B, u) # ps'')" by auto
  from defs assms have a1: "N \<noteq> B" using fresh_sym_dom by auto
  from defs have a2: "Nt B \<notin> set (map Tm x)" by auto
  from defs have "set ps = set ((A, s # u) # ps'')" by simp
  with defs a_notb have a4: "B \<notin> set (dom ((A, [s, Nt B]) # ps''))" using syms_dom2 dom_eq by metis
  with 1 2 a1 a2 a3 a4 show ?thesis using substP_lang
    by (smt (verit) insert_commute list.simps(15))
qed

lemma binarize_der':
  assumes "N \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize' ps) \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
  unfolding binarize'_def by (simp add: assms binarize_der1)

(* refine *)
lemma dom_binarize1:
  "set (dom ps) \<subseteq> set (dom (binarize1 ps' ps))"
proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A s0 ps)
  then show ?case by auto
next
  case (4 ps' A s0 s1 ps)
  then show ?case by auto
next
  case (5 ps' A s0 v vb vc ps)
  then show ?case
    by (metis (mono_tags, opaque_lifting) binarize1.simps(5) dom.simps(2) list.set_intros(1) set_ConsD set_subset_Cons subset_code(1))
qed

lemma dom_binarize':
  "set (dom ps) \<subseteq> set (dom (binarize' ps))"
  by (simp add: binarize'_def dom_binarize1)

lemma dom_binarize'':
  "set (dom ps) \<subseteq> set (dom ((binarize'^^n) ps))"
  apply (induction n)
  apply auto
  using dom_binarize' by blast

lemma binarize_der'': 
  assumes "A \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((binarize'^^n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
using assms proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "A \<in> set (dom ((binarize' ^^ n) ps))"
    using assms dom_binarize'' by blast
  then have "set ((binarize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize' ((binarize' ^^ n) ps)) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    using binarize_der' by blast
  then have "set ((binarize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((binarize' ^^ Suc n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by simp
  with Suc show ?case by blast
qed

lemma binarize_der: 
  assumes "A \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  by (simp add: assms binarize_def binarize_der'')

lemma lang_binarize': 
  assumes "N \<in> set (dom ps)"
  shows "lang ps N = lang (binarize ps) N"
  by (meson Lang_eqI_derives assms binarize_der)

(* Extending assumption from domain to arbitrary non-terminal *)

(* refine *)
lemma dom_der:
  assumes "N \<notin> set (dom ps)"
  shows "\<nexists>x. set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
proof 
  from assms have nol: "\<nexists>u. (N,u) \<in> set ps" by (simp add: dom_set)
  assume "\<exists>x. set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
  then obtain x where x_def: "set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x" by blast
  then show False proof (induction rule: rtranclp.induct)
    case (rtrancl_refl a)
    with nol x_def show ?case
      by (meson deriven_start1 rtranclp_power)
  next
    case (rtrancl_into_rtrancl a b c)
    with nol x_def show ?case by blast
  qed
qed

lemma dom_lang:
  assumes "N \<notin> set (dom ps)"
  shows "lang ps N = {}"
  using dom_der Lang_def assms by fastforce

(* refine *)
lemma binarize_syms1:
  assumes  "Nt N \<in> set (syms ps)"
    shows  "Nt N \<in> set (syms (binarize1 ps' ps))"
using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A s0 ps)
  then show ?case by auto
next
  case (4 ps' A s0 s1 ps)
  then show ?case by auto
next
  case (5 ps' A s0 v vb vc ps)
  then show ?case
    by (metis (no_types, lifting) Un_iff binarize1.simps(5) list.set_intros(1) set_ConsD set_append set_subset_Cons syms.simps(2) syms_not_set syms_subset)
qed

lemma nts_to_syms: "N \<in> nts (set ps) \<Longrightarrow> Nt N \<in> set (syms ps)"
  apply (induction ps)
   apply (auto simp add: nts_def split: prod.splits)
  apply (meson nt12)
  done

lemma syms_to_nts: "Nt N \<in> set (syms ps) \<Longrightarrow> N \<in> nts (set ps)"
  apply (induction ps)
   apply (auto simp add: nts_def split: prod.splits)
  apply (meson nt11)
  done

lemma nts_syms_equI: "N \<in> nts (set ps) \<longleftrightarrow> Nt N \<in> set (syms ps)"
  using nts_to_syms syms_to_nts by blast

(* refine *)
lemma binarize_dom1:
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps')"
    shows "N \<notin> set (dom (binarize1 ps' ps))"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by simp
next
  case (3 ps' A s0 ps)
  then show ?case by simp
next
  case (4 ps' A s0 s1 ps)
  then show ?case by simp
next
  case (5 ps' A s0 v vb vc ps)
  then show ?case
    by (metis binarize1.simps(5) dom.simps(2) fresh insert_iff list.simps(15))
qed

lemma binarize_syms_dom1:
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps)"
    shows "N \<notin> set (dom (binarize1 ps ps)) \<and> N \<in> nts (set (binarize1 ps ps))"
  using assms binarize_syms1 binarize_dom1 nts_syms_equI by blast

lemma binarize_syms_dom':
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps)"
    shows "N \<notin> set (dom (binarize' ps)) \<and> N \<in> nts (set (binarize' ps))"
  unfolding binarize'_def by (simp add: assms binarize_syms_dom1)

lemma binarize_syms_dom'':
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps)"
    shows "N \<notin> set (dom ((binarize'^^n) ps)) \<and> N \<in> nts (set ((binarize'^^n) ps))"
  using assms by (induction n) (auto simp add: binarize_syms_dom')

lemma binarize_syms_dom:
   assumes "N \<notin> set (dom ps)"
      and  "N \<in> nts (set ps)"
    shows "N \<notin> set (dom (binarize ps)) \<and> N \<in> nts (set (binarize ps))"
  unfolding binarize_def using assms binarize_syms_dom'' by blast

(* Final proof *)
lemma lang_binarize: 
  assumes "N \<in> nts (set ps)"
  shows "lang ps N = lang (binarize ps) N"
proof (cases "N \<in> set (dom ps)")
  case True
  then show ?thesis
    using lang_binarize' by blast
next
  case False
  then show ?thesis
    using assms binarize_syms_dom dom_lang by blast
qed

end