theory Right_Linear
imports "../Stimpfle/uProds" Binarize
begin

definition rlin :: "('n, 't) Prods \<Rightarrow> bool" where
  "rlin ps = (\<forall>(A,w) \<in> ps. \<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B]))"

definition rlin_noterm :: "('n, 't) Prods \<Rightarrow> bool" where
  "rlin_noterm ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>u B. w = map Tm u @ [Nt B]))"

definition rlin_bin :: "('n, 't) Prods \<Rightarrow> bool" where
  "rlin_bin ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>B. w = [Nt B] \<or> (\<exists>a. w = [Tm a, Nt B])))"

definition rlin2 :: "('a, 't) Prods \<Rightarrow> bool" where
  "rlin2 ps = (\<forall>(A,w) \<in> ps. w = [] \<or> (\<exists>a B. w = [Tm a, Nt B]))"

lemma rlin2_to_rlin: 
  "rlin2 ps \<Longrightarrow> rlin ps"
  unfolding rlin_def rlin2_def
  by (auto split: prod.splits) (metis (no_types, lifting) append_eq_Cons_conv map_eq_Cons_conv map_is_Nil_conv)

lemma rlin_cases:
  assumes rlin_ps: "rlin ps" 
      and elem: "(A,w) \<in> ps"
    shows "(\<exists>B. w = [Nt B]) \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"
proof -
  from rlin_ps have "\<forall>(A,w) \<in> ps. (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u \<le> 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))"
    using rlin_def by fastforce
  with elem have "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u \<le> 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by auto
  hence "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u = 0)) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by simp
  hence "(\<exists>u. w = map Tm u \<or> (\<exists>B. w = [Nt B])) 
                   \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by auto
  hence "(\<exists>B. w = [Nt B]) \<or> (\<exists>u. w = map Tm u \<or> (\<exists>B. w = map Tm u @ [Nt B] \<and> length u > 0))" by blast
  thus ?thesis .
qed

lemma uppr_rlin2:
  assumes rlinbin: "rlin_bin (set ps')"
    and uppr_ps': "uppr ps' ps"
  shows "rlin2 (set ps)"
proof - 
  from rlinbin have "rlin2 (set ps' - {(A,w) \<in> set ps'. \<exists>B. w = [Nt B]})"
    using rlin2_def rlin_bin_def by fastforce
  hence "rlin2 (set ps' - (unitProds ps'))"
    by (simp add: unitProds_def)
  hence 1: "rlin2 (nonUnitProds ps')"
    by (simp add: nonUnitProds_def)
  hence 2: "rlin2 (newProds ps')"
    unfolding newProds_def rlin2_def by fastforce
  from 1 2 have "rlin2 (nonUnitProds ps' \<union> newProds ps')"
    unfolding rlin2_def by auto
  hence "rlin2 (uppr_rules ps')"
    by (simp add: uppr_rules_def)
  with uppr_ps' have "rlin2 (set ps)"
    by (simp add: uppr_def)
  thus ?thesis .
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
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v # va = map Tm u")
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
qed simp_all

lemma countfin_dec':
  assumes "finalize' ps \<noteq> ps" 
  shows "countfin ps > countfin (finalize' ps)"
  using finalize'_def assms countfin_dec1 by metis

lemma finalize_ffpi:
  "finalize'((finalize' ^^ countfin x) x) = (finalize' ^^ countfin x) x"
proof -
  have "\<And>x. countfin(finalize' x) < countfin x \<or> finalize' x = x"
    using countfin_dec' by blast
  thus ?thesis using funpow_fix by metis
qed

lemma finalize_rlinnoterm1:
  assumes "rlin (set ps)"
      and "ps = finalize1 ps' ps"
    shows "rlin_noterm (set ps)"
  using assms proof (induction ps' ps rule: finalize1.induct)
  case (1 ps')
  thus ?case
    by (simp add: rlin_noterm_def)
next
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_def rlin_noterm_def)
next
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis 
      by simp (meson list.inject not_Cons_self)
  next
    case False
    with 3 show ?thesis
      by (simp add: rlin_def rlin_noterm_def)
  qed
qed

lemma finalize_rlin1:
  "rlin (set ps) \<Longrightarrow> rlin (set (finalize1 ps' ps))"
proof (induction ps' ps rule: finalize1.induct)
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_def)
next
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis
     by simp (smt (verit, del_insts) append_Cons case_prodI2 list.simps(15) list.simps(8) prod.sel(2) rlin_def set_ConsD set_subset_Cons subset_code(1))
  next
    case False
    with 3 show ?thesis
      by (simp add: rlin_def)
  qed
qed simp

lemma finalize_rlin':
  "rlin (set ps) \<Longrightarrow> rlin (set (finalize' ps))"
  unfolding finalize'_def using finalize_rlin1 by blast

lemma finalize_rlin'n:
  "rlin (set ps) \<Longrightarrow> rlin (set ((finalize'^^n) ps))"
  by (induction n) (auto simp add: finalize_rlin')

lemma finalize_rlinnoterm':
  assumes "rlin (set ps)"
      and "ps = finalize' ps"
  shows "rlin_noterm (set ps)"
  using finalize'_def assms finalize_rlinnoterm1 by metis

lemma finalize_rlinnoterm: 
  "rlin (set ps) \<Longrightarrow> rlin_noterm (set (finalize ps))"
proof -
  assume asm: "rlin (set ps)"
  hence 1: "rlin (set ((finalize' ^^ countfin ps) ps))"
    using finalize_rlin'n by auto
  have "finalize'((finalize' ^^ countfin ps) ps) = (finalize' ^^ countfin ps) ps"
    using finalize_ffpi by blast
  with 1 have "rlin_noterm (set ((finalize' ^^ countfin ps) ps))"
    using finalize_rlinnoterm' by metis
  hence "rlin_noterm (set (finalize ps))"
    by (simp add: finalize_def)
  thus ?thesis .
qed

lemma finalize1_cases:
  "finalize1 ps' ps = ps \<or> (\<exists>A w ps'' B. set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A,w @ [Nt B]),(B,[])} \<union> set ps'' \<and> Nt B \<notin> syms ps')"
proof (induction ps' ps rule: finalize1.induct)
  case (2 ps' C ps)
  thus ?case proof (cases "finalize1 ps' ps = ps")
    case False
    then obtain A w ps'' B where defs: "set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
    using 2 by blast
    from defs have wit: "set ((C, []) # ps) = {(A, w)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit2: "set (finalize1 ps' ((C, []) # ps)) = {(A, w @ [Nt B]), (B, [])} \<union> set ((C, []) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed simp
next
  case (3 ps' C v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    thus ?thesis by simp (metis append_Cons fresh fresh_syms list.simps(15))
  next
    case false1: False
    thus ?thesis proof (cases "finalize1 ps' ps = ps")
    case False
    with false1 obtain A w ps'' B where defs: "set ps = {(A, w)} \<union> set ps'' \<and> set (finalize1 ps' ps) = {(A, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
    using 3 by blast
    from defs have wit: "set ((C, v#va) # ps) = {(A, w)} \<union> set ((C, v#va) # ps'')" by simp
    from defs false1 have wit2: "set (finalize1 ps' ((C, v#va) # ps)) = {(A, w @ [Nt B]), (B, [])} \<union> set ((C, v#va) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed simp
  qed
qed simp

lemma finalize_der':
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize' ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  unfolding finalize'_def proof (cases "finalize1 ps ps = ps")
  case False
  then obtain C w ps'' B where defs: "set ps = {(C, w)} \<union> set ps'' \<and> set (finalize1 ps ps) = {(C, w @ [Nt B]), (B, [])} \<union> set ps'' \<and> Nt B \<notin> syms ps"
    by (meson finalize1_cases)
  from defs have a_not_b: "C \<noteq> B" using syms_not_eq by fast
  from defs assms have a1: "A \<noteq> B" using syms_Lhss_not_eq by fastforce
  from defs have a2: "Nt B \<notin> set (map Tm x)" by auto
  from defs have a3: "Nt B \<notin> set []" by simp
  from defs have "set ps = set ((C, w) # ps'')" by simp
  with defs a_not_b have a4: "B \<notin> lhss ((C, w @ [Nt B]) # ps'')"
    unfolding Lhss_def by auto (meson insert_iff syms_inv)
  from defs have notB: "Nt B \<notin> syms ps''" unfolding Syms_def by blast
  then have 1: "set ps = set (substP ((C, w @ [Nt B]) # ps'') (Nt B) [])" proof -
    from defs have s1: "Nt B \<notin> syms ps" unfolding Syms_def by meson
    from defs have s2: "(C,w) \<in> set ps" by blast
    from s1 s2 have b_notin_w: "Nt B \<notin> set w" using syms_not_set by fastforce
    from defs have "set ps = {(C, w)} \<union> set ps''" by simp
    also have "... = set ((C, w) # ps'')" by simp
    also have "... = set ([(C, w)] @ ps'')" by simp
    also from defs have "... = set ([(C,substW (w @ [Nt B]) (Nt B) [])] @ ps'')" using b_notin_w
      by (simp add: substW_skip substW_split)
    also have "... = set ((substP [(C, w @ [Nt B])] (Nt B) []) @ ps'')" by (simp add: substP_def)
    also have "... = set ((substP [(C, w @ [Nt B])] (Nt B) []) @ substP ps'' (Nt B) [])" using notB by (simp add: substP_skip2)
    also have "... = set (substP ((C, w @ [Nt B]) # ps'') (Nt B) [])" by (simp add: substP_def)
    finally show ?thesis .
  qed
  from defs have 2: "set (finalize1 ps ps) = set ((C, w @ [Nt B]) # (B, []) # ps'')" by auto
  with 1 2 a1 a2 a3 a4 show "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize1 ps ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by (simp add: substP_lang insert_commute)
qed simp

lemma lhss_finalize1:
  "lhss ps \<subseteq> lhss (finalize1 ps' ps)"
proof (induction ps' ps rule: finalize1.induct)
  case (2 ps' A ps)
  thus ?case unfolding Lhss_def by auto
next
  case (3 ps' A v va ps)
  thus ?case unfolding Lhss_def by (auto simp: Let_def)
qed simp

lemma lhss_binarize'n:
  "lhss ps \<subseteq> lhss ((finalize'^^n) ps)"
proof (induction n)
  case (Suc n)
  thus ?case unfolding finalize'_def using lhss_finalize1 by auto
qed simp

lemma finalize_der'n: 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((finalize'^^n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
using assms proof (induction n)
  case (Suc n)
  hence "A \<in> lhss ((finalize' ^^ n) ps)"
    using lhss_binarize'n by blast
  hence "set ((finalize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize' ((finalize' ^^ n) ps)) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    using finalize_der' by blast
  hence"set ((finalize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((finalize' ^^ Suc n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by simp
  with Suc show ?case by blast
qed simp

lemma finalize_der: 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (finalize ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  unfolding finalize_def using finalize_der'n[OF assms] by simp

lemma lang_finalize_lhss:
  assumes "A \<in> lhss ps"
  shows "lang ps A = lang (finalize ps) A"
  using finalize_der[OF assms] Lang_eqI_derives by metis

lemma finalize_syms1:
  assumes  "Nt A \<in> syms ps"
    shows  "Nt A \<in> syms (finalize1 ps' ps)"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis unfolding Syms_def by (auto simp: Let_def)
  next
    case False
    with 3 show ?thesis unfolding Syms_def by auto
  qed
qed auto

lemma finalize_nts'n:
  assumes "A \<in> nts ps"
  shows   "A \<in> nts ((finalize' ^^ n) ps)"
  using assms proof (induction n)
  case (Suc n)
  thus ?case
    unfolding finalize'_def by (simp add: finalize_syms1 Nts_syms_equI)
qed simp

lemma finalize_nts:
  assumes "A \<in> nts ps"
  shows   "A \<in> nts (finalize ps)"
  unfolding finalize_def using finalize_nts'n[OF assms] by simp

lemma finalize_lhss_nts1:
  assumes "A \<notin> lhss ps"
      and "A \<in> nts ps'"
    shows "A \<notin> lhss (finalize1 ps' ps)"
using assms proof (induction ps' ps rule: finalize1.induct)
  case (3 ps' A v va ps)
  thus ?case proof (cases "\<exists>u. v#va = map Tm u")
    case True
    with 3 show ?thesis unfolding Lhss_def by (auto simp: Let_def fresh)
  next
    case False
    with 3 show ?thesis unfolding Lhss_def by (auto simp: Let_def)
  qed
qed simp_all

lemma finalize_lhss_nts'n:
  assumes "A \<notin> lhss ps"
      and "A \<in> nts ps"
    shows "A \<notin> lhss ((finalize'^^n) ps) \<and> A \<in> nts ((finalize'^^n) ps)"
  using assms proof (induction n)
  case (Suc n)
  thus ?case
    unfolding finalize'_def by (simp add: finalize_lhss_nts1 finalize_syms1 Nts_syms_equI)
qed simp

lemma finalize_lhss_nts:
   assumes "A \<notin> lhss ps"
      and  "A \<in> nts ps"
    shows "A \<notin> lhss (finalize ps) \<and> A \<in> nts (finalize ps)"
  unfolding finalize_def using finalize_lhss_nts'n[OF assms] by simp

lemma lang_finalize: 
  assumes "A \<in> nts ps"
  shows "lang ps A = lang (finalize ps) A"
proof (cases "A \<in> lhss ps")
  case True
  thus ?thesis
    using lang_finalize_lhss by blast
next
  case False
  thus ?thesis
    using assms finalize_lhss_nts Lang_empty_if_notin_Lhss by fast
qed

lemma binarize_rlinbin1: 
  assumes "rlin_noterm (set ps)"
      and "ps = binarize1 ps' ps"
  shows "rlin_bin (set ps)"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  thus ?case
    by (simp add: rlin_bin_def)
next
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_noterm_def rlin_bin_def)
next
  case (3 ps' A s0 u ps)
  from "3.prems"(2) have a1: "length u \<le> 1" by simp (meson list.inject not_Cons_self)
  with "3.prems"(2) have a2: "ps = binarize1 ps' ps" by simp
  from "3.prems"(1) have a3: "rlin_noterm (set ps)"
    by (simp add: rlin_noterm_def)
  from a1 a2 a3 have 1: "rlin_bin (set ps)"
    using "3.IH" by blast
  from "3.prems"(1) have ex: "\<exists>v B. s0 # u = map Tm v @ [Nt B]"
    by (simp add: rlin_noterm_def)
  with a1 have 2: "\<exists>B. s0 # u = [Nt B] \<or> (\<exists>a. s0 # u = [Tm a, Nt B])" proof (cases "length u = 0")
    case True
    with ex show ?thesis by simp
  next
    case False
    with a1 have "length u = 1" by linarith
    with ex show ?thesis
      by auto (metis append_Cons append_Nil append_butlast_last_id butlast_snoc diff_Suc_1 hd_map last_snoc length_0_conv length_butlast list.sel(1) list.simps(8))
  qed
  from 1 2 show ?case
    by (simp add: rlin_bin_def)
qed

lemma binarize_noterm1:
  "rlin_noterm (set ps) \<Longrightarrow> rlin_noterm (set (binarize1 ps' ps))"
proof (induction ps' ps rule: binarize1.induct)
  case (2 ps' A ps)
  thus ?case
    by (simp add: rlin_noterm_def)
next
  case (3 ps' A s0 u ps)
  thus ?case proof (cases "length u \<le> 1")
    case True
    with 3 show ?thesis
      by (simp add: rlin_noterm_def)
  next
    case False
    let ?B = "fresh ps'"
    from "3.prems" have a1: "rlin_noterm (set ps)"
      by (simp add: rlin_noterm_def)
    from "3.prems" have ex: "\<exists>v B. s0 # u = map Tm v @ [Nt B]"
      by (simp add: rlin_noterm_def)
    with False have a2: "\<exists>v B. [s0, Nt ?B] = map Tm v @ [Nt B]"
      by auto (metis append_Cons append_Nil append_eq_map_conv bot_nat_0.extremum butlast.simps(2) butlast_snoc length_0_conv)
    from ex False have a3: "\<exists>v B. u = map Tm v @ [Nt B]" 
      by auto (metis Nil_is_map_conv add_leE add_le_same_cancel1 append_self_conv2 length_greater_0_conv list.map_sel(2) list.sel(3) not_le_imp_less tl_append2)
    from False a1 a3 show ?thesis
      by simp (smt (verit) a2 case_prodI2 rlin_noterm_def set_ConsD snd_conv)
  qed
qed simp

lemma binarize_noterm':
  "rlin_noterm (set ps) \<Longrightarrow> rlin_noterm (set (binarize' ps))"
  unfolding binarize'_def using binarize_noterm1 by blast

lemma binarize_noterm'n:
  "rlin_noterm (set ps) \<Longrightarrow> rlin_noterm (set ((binarize'^^n) ps))"
  by (induction n) (auto simp add: binarize_noterm')

lemma binarize_rlinbin':
  assumes "rlin_noterm (set ps)"
      and "ps = binarize' ps"
  shows "rlin_bin (set ps)"
  using binarize'_def assms binarize_rlinbin1 by metis

lemma binarize_rlinbin: 
  "rlin_noterm (set ps) \<Longrightarrow> rlin_bin (set (binarize ps))"
proof -
  assume asm: "rlin_noterm (set ps)"
  hence 1: "rlin_noterm (set ((binarize' ^^ count ps) ps))"
    using binarize_noterm'n by auto
  have "binarize'((binarize' ^^ count ps) ps) = (binarize' ^^ count ps) ps"
    using binarize_ffpi by blast
  with 1 have "rlin_bin (set ((binarize' ^^ count ps) ps))"
    using binarize_rlinbin' by fastforce
  hence "rlin_bin (set (binarize ps))"
    by (simp add: binarize_def)
  thus ?thesis .
qed

axiomatization uRemove :: "('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  uRemove: "uppr ps (uRemove ps)"

definition clean :: "('n,'t) prods \<Rightarrow> ('n,'t)prods" where 
 "clean ps = uRemove ps"

lemma lang_clean: "lang ps A  = lang (clean ps) A"
  by (simp add: clean_def uppr_lang_eq uRemove)

definition rlin2_of_rlin :: "('n::infinite,'t) prods \<Rightarrow> ('n,'t)prods" where
  "rlin2_of_rlin ps = clean (binarize (finalize ps))"

lemma rlin_to_rlin2: 
  assumes "rlin (set ps)" 
  shows "rlin2 (set (rlin2_of_rlin ps))"
using assms proof -
  assume "rlin (set ps)"
  hence "rlin_noterm (set (finalize ps))"
    using finalize_rlinnoterm by blast
  hence "rlin_bin (set (binarize (finalize ps)))"
    by (simp add: binarize_rlinbin)
  hence "rlin2 (set (uRemove (binarize (finalize ps))))"
    by (simp add: uRemove uppr_rlin2)
  thus "rlin2 (set (rlin2_of_rlin ps))"
    by (simp add: clean_def rlin2_of_rlin_def)
qed

lemma lang_rlin2_of_rlin:
  assumes "A \<in> Nts (set ps)"
  shows "lang ps A = lang (rlin2_of_rlin ps) A"
proof -
  from assms have "lang ps A = lang (finalize ps) A"
    using lang_finalize by blast
  also have "... = lang (binarize (finalize ps)) A"
    using lang_binarize assms finalize_nts by blast
  also  have "... = lang (clean (binarize (finalize ps))) A"
    using lang_clean assms finalize_nts binarize_nts by fast
  also have "... = lang (rlin2_of_rlin ps) A"
    by (simp add: rlin2_of_rlin_def)
  finally show ?thesis .
qed

end