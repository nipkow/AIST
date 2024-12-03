theory detProds
imports "../CFG"
begin

(* CFG? *)
(* domain *)
fun dom :: "('n, 't) prods \<Rightarrow> 'n list" where
  "dom [] = []"
| "dom ((A,u) # ps) = A # dom ps"

(* CFG? *)
(* symbols *)
fun syms :: "('n, 't) prods \<Rightarrow> ('n,'t) syms" where
  "syms [] = []"
| "syms ((A,v)#ps) = Nt A # v @ syms ps"

(* CFG? *)
fun tm :: "('n,'t) syms \<Rightarrow> 't set" where
  "tm [] = {}" |
  "tm (Nt A # v) = tm v" |
  "tm (Tm a # v) = {a} \<union> tm v"

(* CFG? *)
definition tms :: "('n,'t)prodS \<Rightarrow> 't set" where 
  "tms P = (\<Union>(A,w)\<in>P. tm w)"

(* CFG? *)
definition symS :: "('n,'t) prodS \<Rightarrow> ('n,'t) sym set" where 
  "symS ps = (Nt ` nts ps) \<union> (Tm ` tms ps)"

(* CFG? *)
lemma nts_un: 
  "Nt ` nts (a \<union> as) = Nt ` (nts a) \<union> Nt ` (nts as)"
  unfolding nts_def by blast

(* CFG? *)
lemma tms_un: 
  "Tm ` tms (a \<union> as) = Tm ` (tms a) \<union> Tm ` (tms as)"
  unfolding tms_def by blast

(* CFG? *)
lemma symS_un: "symS (a \<union> as) = symS a \<union> symS as"
  unfolding symS_def by (simp add: nts_un sup_assoc sup_left_commute tms_un)

(* CFG? *)
lemma nt_tm: "Nt ` nt u \<union> Tm ` tm u = set u"
  apply (induction u)
   apply simp
  apply (smt (verit, best) Un_commute image_insert image_is_empty insert_is_Un list.sel(1) list.sel(3) list.simps(15) nt.elims nt.simps(1) set_empty sup.idem sup_left_commute sym.distinct(1) tm.elims tm.simps(1))
  done

(* CFG? *)
lemma symS_one: "symS {(A,u)} = {Nt A} \<union> set u"
  unfolding symS_def nts_def tms_def using nt_tm by auto

(* CFG? *)
lemma "set (syms ps) = symS (set ps)"
proof (induction ps)
  case Nil
  then show ?case by (simp add: nts_def symS_def tms_def)
next
  case (Cons a ps)
  let ?A = "fst a" let ?u = "snd a"
  have "set (syms (a # ps)) = set (Nt ?A # ?u @ syms ps)"
    by (metis prod.collapse syms.simps(2))
  also have "... = {Nt ?A} \<union> set ?u \<union> set (syms ps)" by simp
  also from Cons.IH have "... = {Nt ?A} \<union> set ?u \<union> symS (set ps)" by simp
  also have "... = symS {a} \<union> symS (set ps)"
    using symS_one by (metis prod.collapse)
  also have "... = symS ({a} \<union> set ps)"
    using symS_un by blast
  also have "... = symS (set (a # ps))" by simp
  finally show ?case by simp
qed

(* CFG? *)
lemma dom_eq: "set (dom ((A,u) # ps)) = set (dom ((A,s) # ps))"
  by auto

(* CFG? *)
lemma dom_set: 
  "B \<notin> set (dom ps) \<Longrightarrow> (B,v) \<notin> set ps"
  by (induction ps) auto

(* CFG? *)
lemma fresh_dom: "B \<notin> nts (set ps) \<Longrightarrow> B \<notin> set (dom ps)"
  by (induction ps) (auto simp add: nts_def)

(* CFG? *)
lemma nt_set1: "B \<notin> nt u \<Longrightarrow> Nt B \<notin> set u"
  by (induction u rule: nt.induct) auto

(* CFG? *)
lemma nt_set2: "Nt B \<notin> set u \<Longrightarrow> B \<notin> nt u"
  by (induction u rule: nt.induct) auto

(* CFG? *)
lemma nts_to_syms: "N \<in> nts (set ps) \<Longrightarrow> Nt N \<in> set (syms ps)"
  apply (induction ps)
   apply (auto simp add: nts_def split: prod.splits)
  apply (meson nt_set2)
  done

(* CFG? *)
lemma syms_to_nts: "Nt N \<in> set (syms ps) \<Longrightarrow> N \<in> nts (set ps)"
  apply (induction ps)
   apply (auto simp add: nts_def split: prod.splits)
  apply (meson nt_set1)
  done

(* CFG? *)
lemma nts_syms_equI: "N \<in> nts (set ps) \<longleftrightarrow> Nt N \<in> set (syms ps)"
  using nts_to_syms syms_to_nts by metis

(* CFG? *)
lemma fresh_set: "B \<notin> nts (set ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> Nt B \<notin> set u"
  by (induction ps) (auto simp add: nt_set1 nts_def)

(* CFG? *)
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

(* CFG? *)
lemma syms_subset: 
  "set ps \<subseteq> set ps' \<Longrightarrow> s \<in> set (syms ps) \<Longrightarrow> s \<in> set (syms ps')"
  using syms_inv by (metis subset_code(1))

(* CFG? *)
lemma syms_not_eq: "Nt B \<notin> set (syms ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> A \<noteq> B"
  using syms_inv by blast

(* CFG? *)
lemma syms_not_set: "Nt B \<notin> set (syms ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> Nt B \<notin> set u"
  using syms_inv by blast

(* CFG? *)
lemma syms_dom: "Nt B \<notin> set (syms ps) \<Longrightarrow> B \<notin> set (dom ps)"
  by (induction ps) auto

(* CFG? *)
lemma syms_dom2: "Nt B \<notin> set (syms ps) \<Longrightarrow> set ps' = set ps \<Longrightarrow> B \<notin> set (dom ps')"
  by (induction ps)  (auto simp add: syms_dom syms_inv)

(* CFG? *)
lemma syms_subset2: "Nt B \<notin> set (syms ps) \<Longrightarrow> set ps' \<subseteq> set ps \<Longrightarrow> Nt B \<notin> set (syms ps')"
  using syms_subset by blast

(* CFG? *)
lemma syms_set: "a \<notin> set (syms ps) \<Longrightarrow> (A,u) \<in> set ps \<Longrightarrow> a \<notin> set u"
  using syms_inv by blast

(* CFG? *)
lemma fresh_syms: "B \<notin> nts (set ps) \<Longrightarrow> Nt B \<notin> set (syms ps)"
  using dom_set fresh_dom fresh_set syms_inv by fastforce

(* CFG? *)
lemma syms_dom_not_eq: "Nt B \<notin> set (syms ps) \<Longrightarrow> N \<in> set (dom ps) \<Longrightarrow> N \<noteq> B"
  using syms_dom2 by metis

fun substW :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "substW [] _ _ = []"
| "substW (x#xs) y ys = (if x = y then ys @ substW xs y ys else x # substW xs y ys)"

(* lemmas about substW *)

lemma substW_split: "substW (xs @ xs') y ys = substW xs y ys @ substW xs' y ys"
  by (induction xs) auto

lemma substW_skip: "y \<notin> set xs \<Longrightarrow> substW xs y ys = xs"
  by (induction xs) auto

lemma substW_len: "length (substW xs y [y']) = length xs"
  by (induction xs) auto

lemma substW_rev: "y' \<notin> set xs \<Longrightarrow> substW (substW xs y [y']) y' [y] = xs"
  by (induction xs) auto

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

definition substP :: "('n, 't) prods \<Rightarrow>  ('n, 't) sym \<Rightarrow>  ('n, 't) syms \<Rightarrow> ('n, 't) prods" where
  "substP ps s u = map (\<lambda>(A,v). (A, substW v s u)) ps"

(* lemmas about substP*)

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

lemma substPW_der: 
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
      using B_notin_dom b_c_def dom_set by fastforce
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

lemma only_if_part: 
  assumes "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u"
      and A_B_noteq: "A \<noteq> B"
      and B_notin_dom: "B \<notin> set (dom ps)"
      and B_notin_v: "Nt B \<notin> set v"
      and B_notin_u: "Nt B \<notin> set u"
    shows "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u"
  by (metis assms substW_skip substPW_der)

lemma substP_lang: 
  assumes "B \<notin> set (dom ps)" and
          "Nt B \<notin> set v" and
          "Nt B \<notin> set u" and
          "A \<noteq> B"
        shows "set (substP ps (Nt B) v) \<turnstile> [Nt A] \<Rightarrow>* u \<longleftrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
  using assms if_part only_if_part by metis

end