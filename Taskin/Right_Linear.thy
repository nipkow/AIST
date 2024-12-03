theory Right_Linear
imports "../Stimpfle/uProds" Binarize
begin

definition rlin :: "('n, 't) prodS \<Rightarrow> bool" where
"rlin ps = (\<forall>(A,w) \<in> ps. \<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B]))"

definition rlin_nounit :: "('n, 't) prodS \<Rightarrow> bool" where
"rlin_nounit ps = (\<forall>(A,w) \<in> ps. \<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"

definition rlin_eps :: "('n, 't) prodS \<Rightarrow> bool" where
"rlin_eps ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>u B. w = map Tm u @ [Nt B] \<and> length u > 0))"

definition rlin2 :: "('a, 't) prodS \<Rightarrow> bool" where
"rlin2 ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>a B. w = [Tm a, Nt B]))"

lemma "rlin2 ps \<Longrightarrow> rlin ps"
  unfolding rlin_def rlin2_def
  by (auto split: prod.splits) (metis (no_types, lifting) append_eq_Cons_conv map_eq_Cons_conv map_is_Nil_conv)

lemma rlin_split:
  assumes rlin_ps: "rlin ps" 
      and elem: "(A,w) \<in> ps"
    shows "(\<exists>B. w = [Nt B]) \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"
proof -
  from rlin_ps have "\<forall>(A,w) \<in> ps. (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u \<le> 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"
    using rlin_def by fastforce
  with elem have "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u \<le> 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by auto
  then have "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u = 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by simp
  then have "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = [Nt B])) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by auto
  then have "(\<exists>B. w = [Nt B]) \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by blast
  thus ?thesis .
qed

lemma uppr_rlin:
  assumes rlin_ps: "rlin (set ps')"
    and uppr_ps': "uppr ps' ps"
  shows "rlin_nounit (set ps)"
proof -
  from rlin_ps have "rlin_nounit (set ps' - {(A,w) \<in> set ps'. \<exists>B. w = [Nt B]})"
    unfolding rlin_nounit_def using rlin_split by (smt (verit, del_insts) Diff_iff case_prodI case_prodI2 mem_Collect_eq)
  then have "rlin_nounit (set ps' - (unitProds ps'))"
    by (simp add: unitProds_def)
  then have 1: "rlin_nounit (nonUnitProds ps')"
    by (simp add: nonUnitProds_def)
  then have 2: "rlin_nounit (newProds ps')"
    unfolding newProds_def rlin_nounit_def by (smt (verit, del_insts) mem_Collect_eq split_conv split_def)
  from 1 2 have "rlin_nounit (nonUnitProds ps' \<union> newProds ps')"
    unfolding rlin_nounit_def by fast
  then have "rlin_nounit (uppr_rules ps')"
    by (simp add: uppr_rules_def)
  with uppr_ps' have "rlin_nounit (set ps)"
    by (simp add: uppr_def)
  then show ?thesis .
qed

fun finalize1 :: "('n :: infinite, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
  "finalize1 ps' [] = []"
| "finalize1 ps' ((A,[])#ps) = (A,[]) # finalize1 ps' ps"
| "finalize1 ps' ((A,w)#ps) = 
    (if \<exists>u. w = map Tm u then let B = fresh ps' in (A,w @ [Nt B])#(B,[])#ps else (A,w) # finalize1 ps' ps)"

definition finalize' :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "finalize' ps = finalize1 ps ps"

fun countfin :: "('n::infinite, 't) prods \<Rightarrow> nat" where
  "countfin [] = 0"
| "countfin ((A,[])#ps) = countfin ps"
| "countfin ((A,w) # ps) = (if \<exists>u. w = map Tm u then 1 + countfin ps else countfin ps)"

definition finalize :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "finalize ps = (finalize' ^^ (countfin ps)) ps"

lemma countfin_dec1:
  assumes "finalize1 ps' ps \<noteq> ps" 
  shows "countfin ps > countfin (finalize1 ps' ps)"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by simp
next
  case (3 ps' A v va ps)
  then show ?case proof (cases "\<exists>u. v # va = map Tm u")
    case True
    let ?B = "fresh ps'"
    have not_tm: "\<nexists>u. v # va @ [Nt ?B] = map Tm u"
      by (simp add: ex_map_conv)
    from True have "countfin (finalize1 ps' ((A, v # va) # ps)) = countfin ((A,v#va @ [Nt ?B])#(?B,[])#ps)"
      by (metis append_Cons finalize1.simps(3))
    also from not_tm have "... = countfin ps" by simp
    also have "... < countfin ps + 1" by simp
    also from True have "... = countfin ((A, v # va) # ps)" by simp
    finally show ?thesis .
  next
    case False
    with 3 show ?thesis by simp
  qed
qed

lemma countfin_dec:
  assumes "finalize' ps \<noteq> ps" 
  shows "countfin ps > countfin (finalize' ps)"
  using countfin_dec1 finalize'_def assms by metis

lemma finalize_ffpi:
  "finalize'((finalize' ^^ countfin x) x) = (finalize' ^^ countfin x) x"
proof -
  have "\<And>x. countfin(finalize' x) < countfin x \<or> finalize' x = x"
    using countfin_dec by blast
  then show ?thesis using funpow_fix by metis
qed

lemma finalize_rlin1: 
  assumes "rlin_nounit (set ps)"
      and "ps = finalize1 ps' ps"
  shows "rlin_eps (set ps)"
  using assms proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  then show ?case
    by (simp add: rlin_eps_def)
next
  case (2 ps' A ps)
  then show ?case
    by (simp add: rlin_eps_def rlin_nounit_def)
next
  case (3 ps' A v va ps)
  then show ?case
    by (smt (verit, best) case_prod_conv finalize1.simps(3) list.sel(3) not_Cons_self2 rlin_eps_def rlin_nounit_def set_ConsD set_subset_Cons subset_code(1))
qed

lemma finalize_nounit1:
  "rlin_nounit (set ps) \<Longrightarrow> rlin_nounit (set (finalize1 ps' ps))"
proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case
    by (simp add: rlin_nounit_def)
next
  case (3 ps' A v va ps)
  then show ?case  proof (cases "\<exists>u. v # va = map Tm u")
    case True
    let ?B = "fresh ps'"
    from "3.prems" have 1: "rlin_nounit (set ps)"
      by (simp add: rlin_nounit_def)
    from True have 2: "\<exists>u B. v#va @ [Nt ?B] = map Tm u @ [Nt B] \<and> length u > 0" by force
    have 3: "\<exists>u. [] = map Tm u" by simp
    from 1 2 3 show ?thesis
      by (smt (verit, ccfv_threshold) True append_Cons case_prodI2 finalize1.simps(3) prod.sel(2) rlin_nounit_def set_ConsD)
  next
    case False
    with 3 show ?thesis
      by (metis (no_types, lifting) finalize1.simps(3) list.set_intros(1) rlin_nounit_def set_ConsD set_subset_Cons subset_code(1))
  qed
qed

lemma finalize_nounit':
  "rlin_nounit (set ps) \<Longrightarrow> rlin_nounit (set (finalize' ps))"
  unfolding finalize'_def using finalize_nounit1 by blast

lemma finalize_nounit:
  "rlin_nounit (set ps) \<Longrightarrow> rlin_nounit (set ((finalize'^^n) ps))"
  by (induction n) (auto simp add: finalize_nounit')

lemma finalize_rlin':
  assumes "rlin_nounit (set ps)"
      and "ps = finalize' ps"
  shows "rlin_eps (set ps)"
  using assms finalize_rlin1 finalize'_def by metis

lemma finalize_rlin: 
  "rlin_nounit (set ps) \<Longrightarrow> rlin_eps (set (finalize ps))"
proof -
  assume asm: "rlin_nounit (set ps)"
  then have 1: "rlin_nounit (set ((finalize' ^^ countfin ps) ps))"
    using finalize_nounit by auto
  have "finalize'((finalize' ^^ countfin ps) ps) = (finalize' ^^ countfin ps) ps"
    using finalize_ffpi by blast
  with 1 have "rlin_eps (set ((finalize' ^^ countfin ps) ps))"
    using finalize_rlin' by metis
  then have "rlin_eps (set (finalize ps))"
    by (simp add: finalize_def)
  then show ?thesis .
qed

lemma finalize1_cases:
  "finalize1 ps' ps = ps \<or> (\<exists>A w ps'' B. set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A,w @ [Nt B]),(B,[])} \<union> set ps'' \<and> Nt B \<notin> set (syms ps'))"
proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' C ps)
  then show ?case proof (cases "finalize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A w ps'' B where defs: "set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> set (syms ps')"
    using 2 by blast
    from defs have wit: "set ((C, []) # ps) = {(A, w)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit2: "set (finalize1 ps' ((C, []) # ps)) = {(A, w @ [Nt B]), (B, [])} \<union> set ((C, []) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> set (syms ps')" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (3 ps' C v va ps)
  then show ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    then show ?thesis by simp (metis append_Cons fresh fresh_syms list.simps(15))
  next
    case false1: False
    then show ?thesis proof (cases "finalize1 ps' ps = ps")
      case true2: True
      with false1 show ?thesis by simp
  next
    case False
    with false1 obtain A w ps'' B where defs: "set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> set (syms ps')"
    using 3 by blast
    from defs have wit: "set ((C, v#va) # ps) = {(A, w)} \<union> set ((C, v#va) # ps'')" by simp
    from defs false1 have wit2: "set (finalize1 ps' ((C, v#va) # ps)) = {(A, w @ [Nt B]), (B, [])} \<union> set ((C, v#va) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> set (syms ps')" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
  qed
qed

lemma finalize_der1:
  assumes "N \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize1 ps ps) \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
 proof (cases "finalize1 ps ps = ps")
  case True
  then show ?thesis by simp
next
  case False
  then obtain A w ps'' B where defs: "set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps ps) = {(A, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> set (syms ps)"
    by (meson finalize1_cases)
  from defs have a_not_b: "A \<noteq> B" using syms_not_eq by fast
  from defs assms have a1: "N \<noteq> B" using syms_dom_not_eq by fastforce
  from defs have a2: "Nt B \<notin> set (map Tm x)" by auto
  from defs have a3: "Nt B \<notin> set []" by simp
  from defs have "set ps = set ((A, w) # ps'')" by simp
  with defs a_not_b have a4: "B \<notin> set (dom ((A, w @ [Nt B]) # ps''))" using syms_dom2 dom_eq by metis
  from defs have notB: "Nt B \<notin> set (syms ps'')" using syms_subset2 by fastforce
  then have 1: "set ps = set (substP ((A, w @ [Nt B]) # ps'') (Nt B) [])" proof -
    from defs have s1: "Nt B \<notin> set (syms ps)" by simp
    from defs have s2: "(A,w) \<in> set ps" by blast
    from s1 s2 have b_notin_w: "Nt B \<notin> set w" using syms_not_set by fastforce
    from defs have "set ps = {(A, w)} \<union> set ps''" by simp
    also have "... = set ((A, w) # ps'')" by simp
    also have "... = set ([(A, w)] @ ps'')" by simp
    also from defs have "... = set ([(A,substW (w @ [Nt B]) (Nt B) [])] @ ps'')" using b_notin_w
      by (simp add: substW_skip substW_split)
    also have "... = set ((substP [(A, w @ [Nt B])] (Nt B) []) @ ps'')" by (simp add: substP_def)
    also have "... = set ((substP [(A, w @ [Nt B])] (Nt B) []) @ substP ps'' (Nt B) [])" using notB by (simp add: substP_skip2)
    also have "... = set (substP ((A, w @ [Nt B]) # ps'') (Nt B) [])" by (simp add: substP_def)
    finally show ?thesis by simp
  qed
  from defs have 2: "set (finalize1 ps ps) = set ((A, w @ [Nt B]) # (B, []) # ps'')" by auto
  with 1 2 a1 a2 a3 a4 show ?thesis using substP_lang
    by (smt (verit) insert_commute list.simps(15))
qed

lemma finalize_der':
  assumes "N \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize' ps) \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
  unfolding finalize'_def by (simp add: assms finalize_der1)

lemma dom_finalize1:
  "set (dom ps) \<subseteq> set (dom (finalize1 ps' ps))"
proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A v va ps)
  then show ?case by simp (metis dom.simps(2) list.set_intros(1) list.simps(15) set_subset_Cons subset_insertI2)
qed

lemma dom_finalize':
  "set (dom ps) \<subseteq> set (dom (finalize' ps))"
  by (simp add: finalize'_def dom_finalize1)

lemma dom_finalize'':
  "set (dom ps) \<subseteq> set (dom ((finalize'^^n) ps))"
  apply (induction n)
   apply simp
  using dom_finalize' by auto

lemma finalize_der'': 
  assumes "A \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((finalize'^^n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
using assms proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "A \<in> set (dom ((finalize' ^^ n) ps))"
    using assms dom_finalize'' by blast
  then have "set ((finalize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize' ((finalize' ^^ n) ps)) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    using finalize_der' by blast
  then have "set ((finalize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((finalize' ^^ Suc n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by simp
  with Suc show ?case by blast
qed

lemma finalize_der: 
  assumes "A \<in> set (dom ps)"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  by (simp add: assms finalize_def finalize_der'')

lemma lang_finalize':
  assumes "N \<in> set (dom ps)"
  shows "lang ps N = lang (finalize ps) N"
  by (meson Lang_eqI_derives assms finalize_der)

lemma finalize_syms1:
  assumes  "Nt N \<in> set (syms ps)"
    shows  "Nt N \<in> set (syms (finalize1 ps' ps))"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A v va ps)
  then show ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis by simp (metis UnCI list.set_intros(1) list.set_intros(2) set_append syms.simps(2))
  next
    case False
    with 3 show ?thesis by auto
  qed
qed

lemma finalize_nts1:
  assumes "N \<in> nts (set ps)"
  shows   "N \<in> nts (set (finalize1 ps ps))"
  using assms finalize_syms1 nts_syms_equI by metis

lemma finalize_nts':
  assumes "N \<in> nts (set ps)"
  shows   "N \<in> nts (set (finalize' ps))"
  unfolding finalize'_def by (simp add: assms finalize_nts1)

lemma finalize_nts'n:
  assumes "N \<in> nts (set ps)"
  shows   "N \<in> nts (set ((finalize' ^^ n) ps))"
  by (induction n) (auto simp add: assms finalize_nts')

lemma finalize_nts:
  assumes "N \<in> nts (set ps)"
  shows   "N \<in> nts (set (finalize ps))"
  unfolding finalize_def by (simp add: assms finalize_nts'n)

lemma finalize_dom1:
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps')"
    shows "N \<notin> set (dom (finalize1 ps' ps))"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A v va ps)
  then show ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis by simp (metis dom.simps(2) fresh set_ConsD)
  next
    case False
    with 3 show ?thesis by auto
  qed
qed

lemma finalize_syms_dom1:
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps)"
    shows "N \<notin> set (dom (finalize1 ps ps)) \<and> N \<in> nts (set (finalize1 ps ps))"
  using assms finalize_syms1 finalize_dom1 nts_syms_equI by metis

lemma finalize_syms_dom':
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps)"
    shows "N \<notin> set (dom (finalize' ps)) \<and> N \<in> nts (set (finalize' ps))"
  unfolding finalize'_def by (simp add: assms finalize_syms_dom1)

lemma finalize_syms_dom'':
  assumes "N \<notin> set (dom ps)"
      and "N \<in> nts (set ps)"
    shows "N \<notin> set (dom ((finalize'^^n) ps)) \<and> N \<in> nts (set ((finalize'^^n) ps))"
  using assms by (induction n) (auto simp add: finalize_syms_dom')

lemma finalize_syms_dom:
   assumes "N \<notin> set (dom ps)"
      and  "N \<in> nts (set ps)"
    shows "N \<notin> set (dom (finalize ps)) \<and> N \<in> nts (set (finalize ps))"
  unfolding finalize_def using assms finalize_syms_dom'' by blast

lemma lang_finalize: 
  assumes "N \<in> nts (set ps)"
  shows "lang ps N = lang (finalize ps) N"
proof (cases "N \<in> set (dom ps)")
  case True
  then show ?thesis
    using lang_finalize' by blast
next
  case False
  then show ?thesis
    using assms finalize_syms_dom dom_lang by metis
qed

lemma binarize1_rlin2: 
  assumes "rlin_eps (set ps)"
      and "ps = binarize1 ps' ps"
  shows "rlin2 (set ps)"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case
    by (simp add: rlin2_def)
next
  case (2 ps' A ps)
  then show ?case
    by (simp add: rlin2_def rlin_eps_def)
next
  case (3 ps' A s0 ps)
  then show ?case
    by (simp add: rlin2_def rlin_eps_def)
next
  case (4 ps' A s0 s1 ps)
  then have 1: "rlin2 (set ps)" by (simp add: rlin_eps_def)
  from 4(2) have "[s0, s1] = [] \<or> (\<exists>u B. [s0, s1] = map Tm u @ [Nt B] \<and> length u > 0)"
    by (simp add: rlin_eps_def)
  then obtain u B where 2: "[s0, s1] = map Tm u @ [Nt B] \<and> length u > 0" by blast
  from 1 2 show ?case by simp (smt (verit, del_insts) case_prodI2 insert_iff map_eq_Cons_D rlin2_def snd_conv)
next
  case (5 ps' A s0 v vb vc ps)
  then show ?case
    by (metis binarize1.simps(5) list.sel(3) not_Cons_self2)
qed

lemma binarize_eps1:
  "rlin_eps (set ps) \<Longrightarrow> rlin_eps (set (binarize1 ps' ps))"
proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case
    by (simp add: rlin_eps_def)
next
  case (3 ps' A s0 ps)
  then show ?case 
    by (simp add: rlin_eps_def)
next
  case (4 ps' A s0 s1 ps)
  then show ?case 
    by (simp add: rlin_eps_def)
next
  case (5 ps' A s0 v vb vc ps)
  from 5 have 1: "rlin_eps (set ps)"
    by (simp add: rlin_eps_def)
  from 5 have a1: "s0 # v # vb # vc = [] \<or> (\<exists>u B. s0 # v # vb # vc = map Tm u @ [Nt B] \<and> length u > 0)"
    by (simp add: rlin_eps_def)
  then have a2: "\<exists>x. s0 = Tm x"
    by (metis (no_types, opaque_lifting) append_eq_Cons_conv list.discI list.inject map_eq_Cons_conv)
  from a1 obtain u B where 2: "s0 # v # vb # vc = map Tm u @ [Nt B] \<and> length u > 0" by blast
  let ?B = "fresh ps'"
  from a2 have 2: "\<exists>u B. [s0, Nt ?B] = map Tm u @ [Nt B] \<and> length u > 0"
    by (metis Cons_eq_append_conv Cons_eq_map_conv length_Cons lessI list.map_disc_iff list.size(3))
  from a1 have 3: "\<exists>u B. v # vb # vc = map Tm u @ [Nt B] \<and> length u > 0" 
    by simp (metis (no_types, lifting) Nil_is_map_conv append_self_conv2 list.discI list.map_sel(2) list.sel(3) tl_append2)
  show ?case by simp (smt (verit) "1" "2" "3" case_prod_conv rlin_eps_def set_ConsD)
qed

lemma binarize_eps':
  "rlin_eps (set ps) \<Longrightarrow> rlin_eps (set (binarize' ps))"
  unfolding binarize'_def using binarize_eps1 by blast

lemma binarize_eps:
  "rlin_eps (set ps) \<Longrightarrow> rlin_eps (set ((binarize'^^n) ps))"
  by (induction n) (auto simp add: binarize_eps')

lemma binarize_rlin':
  assumes "rlin_eps (set ps)"
      and "ps = binarize' ps"
  shows "rlin2 (set ps)"
  using assms binarize1_rlin2 binarize'_def by metis

lemma binarize_rlin2: 
  "rlin_eps (set ps) \<Longrightarrow> rlin2 (set (binarize ps))"
proof -
  assume asm: "rlin_eps (set ps)"
  then have 1: "rlin_eps (set ((binarize' ^^ count ps) ps))"
    using binarize_eps by auto
  have "binarize'((binarize' ^^ count ps) ps) = (binarize' ^^ count ps) ps"
    using binarize_ffpi by blast
  with 1 have "rlin2 (set ((binarize' ^^ count ps) ps))"
    using binarize_rlin' by metis
  then have "rlin2 (set (binarize ps))"
    by (simp add: binarize_def)
  then show ?thesis .
qed

axiomatization uRemove :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  uRemove: "uppr ps (uRemove ps)"

definition clean :: "('n,'t) prods \<Rightarrow> ('n,'t)prods" where 
 "clean ps = uRemove ps"

lemma lang_clean: "lang ps A  = lang (clean ps) A"
  by (simp add: clean_def thm4_4 uRemove)

definition rlin2_of_rlin :: "('n::infinite,'t)prods \<Rightarrow> ('n,'t)prods" where
  "rlin2_of_rlin ps = binarize (finalize (clean ps))"

lemma rlin2_rlin2_of_rlin: 
  assumes "rlin (set ps)" 
  shows "rlin2 (set (rlin2_of_rlin ps))"
using assms proof -
  assume "rlin (set ps)"
  with uRemove have "rlin_nounit (set (uRemove ps))"
    using uppr_rlin by blast
  then have "rlin_eps (set (finalize (uRemove ps)))"
    by (simp add: finalize_rlin)
  then have "rlin2 (set (binarize (finalize (uRemove ps))))"
    by (simp add: binarize_rlin2)
  thus "rlin2 (set (rlin2_of_rlin ps))"
    by (simp add: clean_def rlin2_of_rlin_def)
qed


lemma lang_rlin2_of_rlin:
  assumes "N \<in> nts (set (clean ps))"
  shows "lang ps N = lang (rlin2_of_rlin ps) N"
proof -
  have "lang ps N = lang (clean ps) N"
    using lang_clean by fast
  also from assms have "... = lang (finalize (clean ps)) N"
    using lang_finalize by blast
  also from assms have "... = lang (binarize (finalize (clean ps))) N"
    using finalize_nts lang_binarize by blast
  also have "... = lang (rlin2_of_rlin ps) N"
    by (simp add: rlin2_of_rlin_def)
  finally show ?thesis .
qed

end