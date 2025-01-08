theory cfg_renaming
  imports "../CFG" "../Stimpfle/CNF" "../Taskin/Right_Linear"
begin

(*
  This theory provides lemmas relevant when working with grammars
  derived from other grammars by mapping the nonterminals using
  a mapping function.

  The theory is completely proven. However, the proofs feature lots of
  code duplication.

  This is especially because of the following pattern:

  If there is a proof that specifies, that a predicate
  holds true for a renamed grammar if it holds true for the original,
  and if the mapping function is injective, then the reverse direction
  can also be proved by using the inverse of the mapping function.

  So there are analogous proofs for  different predicates.
  Abstracting this proof into an own lemma would reduce code duplication.
  However, the mapping function can map to a different type, and thus,
  the predicate takes grammars of different types for the original and the
  renamed grammar.
  Therefore, the simple lemma
    "(\<And>G. P G \<Longrightarrow> P (rename_cfg f G)) \<Longrightarrow> inj f \<Longrightarrow> (\<And>G. P (rename_cfg f G) \<Longrightarrow> P G)"
  would not be generic enough.
*)




(* definition of functions that, together, rename nonterminals of a cfg *)

fun rename_sym :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) sym \<Rightarrow> ('new,'t) sym" where
  "rename_sym f (Nt n) = Nt (f n)" |
  "rename_sym f (Tm t) = Tm t"

abbreviation "rename_syms f \<equiv> map (rename_sym f)"

fun rename_prod :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) prod \<Rightarrow> ('new,'t) prod" where
  "rename_prod f (lhs,rhs) = (f lhs, rename_syms f rhs)"

abbreviation "rename_prods f \<equiv> map (rename_prod f)"

fun rename_cfg :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) cfg \<Rightarrow> ('new,'t) cfg" where
  "rename_cfg f (cfg ps st) = cfg (rename_prods f ps) (f st)"




lemma rename_sym_isNt: "isNt s \<longleftrightarrow> isNt ((rename_sym f) s)"
  unfolding isNt_def
  by (metis rename_sym.elims sym.simps(4))

lemma rename_sym_isTm: "isTm s \<longleftrightarrow> isTm ((rename_sym f) s)"
  unfolding isTm_def
  by (metis rename_sym.elims sym.simps(4))

lemma isNt_isNt_o_rename_sym: "isNt = isNt o (rename_sym f)"
  using rename_sym_isNt by fastforce

lemma isNt_isTm_o_rename_sym: "isTm = isTm o (rename_sym f)"
  using rename_sym_isTm by fastforce


(* syms derived in the original grammar are also derivable in the renamed grammar
   (but the nonterminals are renamed accordingly *)
lemma cfg_rename_derive_dir1:
  shows "(set p) \<turnstile> a \<Rightarrow>* b \<Longrightarrow> (set (rename_prods f p)) \<turnstile> (rename_syms f a) \<Rightarrow>* (rename_syms f b)"
proof (induction rule: derives_induct')
  case base
  then show ?case
    by simp
next
  let ?sym_f = "rename_syms f"
  case (step u A v w)
  then have "(f A, rename_syms f w) \<in> set (rename_prods f p)"
    by (metis image_eqI list.set_map rename_prod.simps) 
  then have "set (rename_prods f p) \<turnstile> [Nt (f A)] \<Rightarrow>* ?sym_f w"
    using derive_singleton by blast
  then have "set (rename_prods f p) \<turnstile> ?sym_f [Nt A] \<Rightarrow>* ?sym_f w" by simp
  moreover
  from step have "set (rename_prods f p) \<turnstile> ?sym_f u @ ?sym_f w @ ?sym_f v \<Rightarrow>* rename_syms f b" by simp
  ultimately have "set (rename_prods f p) \<turnstile> ?sym_f u @ ?sym_f [Nt A] @ ?sym_f v \<Rightarrow>* rename_syms f b"
    by (meson derives_append derives_prepend rtranclp_trans) 
  then show ?case by auto
qed


(* renamed syms are derivable in the renamed grammar 
   iff their non-renamed counterpart is derivable in the original grammar *)
lemma cfg_rename_derive:
  assumes "inj (f:: 'a \<Rightarrow> 'b)"
  shows "(set p) \<turnstile> (a:: ('a,'t) syms) \<Rightarrow>* b \<longleftrightarrow> (set (rename_prods f p)) \<turnstile> (rename_syms f a) \<Rightarrow>* (rename_syms f b)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by (rule cfg_rename_derive_dir1)
next
  (* since f is injective, the second direction follows from the first by using the inverse *)
  obtain "g" where "g = the_inv f" and inv: "(\<And>x. (g (f x) = x))" using \<open>inj f\<close>
    by (simp add: the_inv_f_f)
  then have "\<And>(s::('a,'t) sym). rename_sym g (rename_sym f s) = s"
  proof -
    fix s
    show "rename_sym g (rename_sym f s) = (s::('a,'t) sym)"
    proof (cases s)
      case (Nt t)
      then have "(rename_sym f s) = Nt (f t)" by simp
      moreover have "rename_sym g (Nt (f t)) = Nt (g (f t))" by simp
      moreover have "Nt (g (f t)) = Nt t" using inv by simp
      ultimately show ?thesis using Nt by simp
    qed simp
  qed
  then have inv_rename_syms: "\<And>(ss::('a,'t) syms). rename_syms g (rename_syms f ss) = ss"
    by (simp add: map_idI)
  with inv have "\<And>(p::('a,'t) prod). rename_prod g (rename_prod f p) = p" by force
  then have inv_rename_prods: "\<And>(ps::('a,'t) prods). rename_prods g (rename_prods f ps) = ps"
    by (simp add: map_idI)
  then show "?r \<Longrightarrow> ?l" using cfg_rename_derive_dir1[where f=g]
    by (metis inv_rename_syms)
qed


(* renaming of nonterminals does not change language *)
lemma cfg_rename_L:
  assumes inj: "inj f" (* renaming function *)
  shows "L (G::('n,'t) cfg) = L (rename_cfg f G)"
proof -
  have "\<And>x. x \<in> L G \<longleftrightarrow> x \<in> L (rename_cfg f G)"
  proof -
    fix x
    let ?G' = "rename_cfg f G"
    let ?p = "prods G" and ?a = "[Nt (start G)]" and ?b = "map Tm (x::'t list)"
    let ?p' = "prods ?G'" and ?a' = "[Nt (start ?G')]"
  
    have "x \<in> L G \<longleftrightarrow> (set (?p)) \<turnstile> ?a \<Rightarrow>* ?b" unfolding Lang_def by simp
    moreover from inj have "(set (?p)) \<turnstile> ?a \<Rightarrow>* ?b \<longleftrightarrow>
        (set (rename_prods f ?p)) \<turnstile> (rename_syms f ?a) \<Rightarrow>* (rename_syms f ?b)"
      by (rule cfg_rename_derive)
    moreover have "rename_syms f ?a = [Nt (f (start G))]" by simp
    moreover have "[Nt (f (start G))] = [Nt (start (?G'))]"
      by (metis cfg.collapse cfg.sel(2) rename_cfg.simps)
    moreover have "?b = (rename_syms f ?b)" by simp
    moreover have "rename_prods f ?p = ?p'"
      by (metis cfg.collapse cfg.sel(1) rename_cfg.simps) 
    moreover have "x \<in> L (rename_cfg f G) \<longleftrightarrow> (set ?p') \<turnstile> ?a' \<Rightarrow>* ?b" unfolding Lang_def by simp
    ultimately show "x \<in> L G \<longleftrightarrow> x \<in> L (rename_cfg f G)"
      by metis
  qed
  then show "L G = L (rename_cfg f G)" by auto
qed

(* True only for right hand sides of stronly right linear grammars *)
definition "syms_rlin2 w \<longleftrightarrow> w = [] \<or> (\<exists>a B. w = [Tm a, Nt B])"

(* renaming of nonterminals in right hand sides preserves strong right linearity *)
lemma syms_rename_rlin2:
  assumes "syms_rlin2 w"
  shows "syms_rlin2 (rename_syms f w)"
proof -
  from assms have cases: "w = [] \<or> (\<exists>a B. w = [Tm a, Nt B])" unfolding syms_rlin2_def by simp
  have "rename_syms f w = [] \<or> (\<exists>a B. rename_syms f w = [Tm a, Nt B])"
  proof (cases "w = []")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis using cases by auto 
  qed
  then show "syms_rlin2 (rename_syms f w)" unfolding syms_rlin2_def by simp
qed

(* renaming of nonterminals in productions sides preserves strong right linearity *)
lemma prods_rename_rlin2:
  assumes "rlin2 (set ps)"
  shows "rlin2 (set (rename_prods f ps))"
proof -
  from assms have "\<forall>(A,w) \<in> set ps. w = [] \<or> (\<exists>a B. w = [Tm a, Nt B])" unfolding rlin2_def by simp
  then have "\<forall>(_,w) \<in> set ps. syms_rlin2 w" unfolding syms_rlin2_def by simp
  then have "\<forall>(_,w) \<in> set ps. syms_rlin2 (rename_syms f w)" by (auto simp add: syms_rename_rlin2)
  then have "\<forall>(_,w) \<in> set (rename_prods f ps). syms_rlin2 w" by auto
  then show "rlin2 (set (rename_prods f ps))" unfolding rlin2_def syms_rlin2_def by simp
qed


(* renamed grammar is stronly right linear iff the original cfg is *)
lemma cfg_rename_rlin2:
  assumes inj: "inj f" (* renaming function *)
  shows "rlin2 (set (prods (G::('n,'t) cfg))) \<longleftrightarrow> rlin2 (set (prods (rename_cfg f G)))" (is "?l \<longleftrightarrow> ?r")
proof
  (* TODO: remove code duplication *)
  assume "rlin2 (set (prods G))"
  then have "rlin2 (set (rename_prods f (prods G)))" by (simp only: prods_rename_rlin2)
  then show "rlin2 (set (prods (rename_cfg f G)))"
    by (metis cfg.collapse cfg.sel(1) rename_cfg.simps)
next
  (* since f is injective, the second direction follows from the first by using the inverse *)
  obtain "g" where "g = the_inv f" and inv: "(\<And>x. (g (f x) = x))" using \<open>inj f\<close>
    by (simp add: the_inv_f_f)
  then have "\<And>(s::('n,'t) sym). rename_sym g (rename_sym f s) = s"
  proof -
    fix s
    show "rename_sym g (rename_sym f s) = (s::('n,'t) sym)"
    proof (cases s)
      case (Nt t)
      then have "(rename_sym f s) = Nt (f t)" by simp
      moreover have "rename_sym g (Nt (f t)) = Nt (g (f t))" by simp
      moreover have "Nt (g (f t)) = Nt t" using inv by simp
      ultimately show ?thesis using Nt by simp
    qed simp
  qed
  then have inv_rename_syms: "\<And>(ss::('n,'t) syms). rename_syms g (rename_syms f ss) = ss"
    by (simp add: map_idI)
  with inv have "\<And>(p::('n,'t) prod). rename_prod g (rename_prod f p) = p" by force
  then have inv_rename_prods: "\<And>(ps::('n,'t) prods). rename_prods g (rename_prods f ps) = ps"
    by (simp add: map_idI)
  then have inv_rename_cfg: "\<And>(G::('n,'t) cfg). (rename_cfg g) ((rename_cfg f) G) = G"
    by (metis cfg.collapse inv rename_cfg.simps)
  then show "?r \<Longrightarrow> ?l" using prods_rename_rlin2[where f=g]
    by (metis cfg.sel(1) rename_cfg.elims)
qed

(* currenlty unused *)
lemma rename_sym_disjoint:
  assumes "range f \<inter> range g = {}"
  shows "range ((rename_sym f) o Nt) \<inter> range ((rename_sym g) o Nt) = {}"
proof -
  from assms have "\<And>y. (\<exists>x. f x = y) \<Longrightarrow> (\<nexists>x. g x = y)" by auto
  moreover have "\<And>y. (\<nexists>x. g x = y) \<Longrightarrow> (\<nexists>x. (rename_sym g) (Nt x) = Nt y)"
    by simp
  moreover have "\<And>y. (\<exists>x. (rename_sym f) (Nt x) = Nt y) \<Longrightarrow> (\<exists>x. f x = y)"
    by simp
  ultimately have "\<And>y. (\<exists>x. (rename_sym f) (Nt x) = Nt y) \<Longrightarrow> (\<nexists>x. (rename_sym g) (Nt x) = Nt y)" by simp
  then show "range ((rename_sym f) o Nt) \<inter> range ((rename_sym g) o Nt) = {}" by auto
qed

(* renaming words yields words with disjoint sets of nonterminals when
   different mapping functions having disjoint ranges are used *)
lemma rename_syms_disjoint:
  assumes "range f \<inter> range g = {}"
  shows "nts_of_syms (rename_syms f ss) \<inter> nts_of_syms (rename_syms g ss) = {}"
proof
  obtain "ns" where "set (ns) = nts_of_syms ss"
    by (meson finite_list finite_nts_of_syms) 

  have "\<And>ss. nts_of_syms ss = nts_of_syms (filter isNt ss)"
    by (metis (mono_tags, lifting) Collect_cong isNt_def mem_Collect_eq nts_of_syms_def set_filter)

  have "\<And>f ss. filter isNt (rename_syms f ss) = rename_syms f (filter isNt ss)"
    using isNt_isNt_o_rename_sym by (metis filter_map)

  show "nts_of_syms (rename_syms f ss) \<inter> nts_of_syms (rename_syms g ss) \<subseteq> {}"
  proof
    fix x
    assume "x \<in> nts_of_syms (rename_syms f ss) \<inter> nts_of_syms (rename_syms g ss)"
    then have "Nt x \<in> set (rename_syms f ss) \<and> Nt x \<in> set (rename_syms g ss)" 
      unfolding nts_of_syms_def by fast
    then show "x \<in> {}"
      by (metis IntI assms if_set_map isNt_def rangeI rename_sym.simps(1) rename_sym_isNt sym.inject(1))
  qed
qed simp



lemma in_Nts: "x \<in> Nts ps \<Longrightarrow> \<exists>p. p \<in> ps \<and> (x = fst p \<or> Nt x \<in> set (snd p))"
  by (metis Nts_syms_equI fst_conv snd_conv sym.inject(1) syms_inv)


(* nonterminals of renamed productions are contained
   in the renaming function*s image of the original production's nonterminals *)
lemma nts_rename_prod: "nts (rename_prods f ps) = f ` nts ps"
proof
  show "nts (rename_prods f ps) \<subseteq> f ` nts ps"
  proof
    fix y
    assume "y \<in> nts (rename_prods f ps)"
    then obtain p' where mapped: "p' \<in> set (rename_prods f ps)" and contained: "(y = fst p' \<or> Nt y \<in> set (snd p'))"
      by (meson in_Nts)
    
    from mapped obtain p where p: "p \<in> set ps \<and> p' = rename_prod f p"
      by (metis if_set_map)

    from contained have "y = f (fst p) \<or> (\<exists>x. y = f x \<and> Nt x \<in> set (snd p))"
    proof
      assume "y = fst p'"
      have "f (fst p) = fst p'"
        by (metis p fst_conv prod.collapse rename_prod.simps)
      then show ?thesis by (simp add: \<open>y = fst p'\<close>) 
    next
      assume "Nt y \<in> set (snd p')"
      then have "Nt y \<in> set (snd (rename_prod f p))" using p by simp
      then have "Nt y \<in> set ((rename_syms f) (snd p))"
        by (metis prod.collapse rename_prod.simps snd_conv)
      then obtain s where "Nt y \<in> set(s) \<and> s = rename_syms f (snd p)" by simp
      then obtain x where "y = f x \<and> Nt x \<in> set (snd p)"
        by (smt (z3) if_set_map rename_sym.elims slemma4_2_0 sym.distinct(1)) 
      then have "\<exists>x. y = f x \<and> Nt x \<in> set (snd p)" by auto
      then show ?thesis by simp
    qed

    then obtain x where "y = f x \<and> (x = fst p \<or> Nt x \<in> set (snd p))" by auto
    then have "y = f x \<and> x \<in> nts ps"
      by (metis fresh_set fresh_syms p prod.collapse syms_not_eq) 
    then show "y \<in> f ` nts ps" by auto
  qed
next
  show "f ` nts ps \<subseteq> nts (rename_prods f ps)"
  proof
    fix y
    assume "y \<in> f ` nts ps"
    then obtain x where x_y: "y = f x" and x_nts: "x \<in> nts ps" by blast
    then obtain p where "p \<in> (set ps)" and contained: "(x = fst p \<or> Nt x \<in> set (snd p))"
      by (meson in_Nts)
    then have "rename_prod f p \<in> set (rename_prods f ps)"
      by simp 
    moreover from contained have "(y = fst (rename_prod f p) \<or> Nt y \<in> set (snd (rename_prod f p)))"
      by (metis (mono_tags, opaque_lifting) x_y image_iff list.set_map rename_prod.simps rename_sym.simps(1) split_pairs)
    ultimately show "y \<in> nts (rename_prods f ps)"
      by (metis Lhss_set fresh_Lhss fresh_set prod.collapse)
  qed
qed

lemma prods_rename_cfg_rename_prods: "prods (rename_cfg f g) = rename_prods f (prods g)"
  by (metis cfg.collapse cfg.sel(1) rename_cfg.simps)

lemma rename_prods_disjoint:
  assumes "range f \<inter> range g = {} "
  shows "nts (rename_prods f ps1) \<inter> nts (rename_prods g ps2) = {}"
proof -
  have "(f ` nts ps1) \<inter> (g ` nts ps2) = {}"  using assms by auto
  moreover have "nts (rename_prods f ps1) = f ` nts ps1" by (rule nts_rename_prod)
  moreover have "nts (rename_prods g ps2) = g ` nts ps2" by (rule nts_rename_prod)
  ultimately show "nts (rename_prods f ps1) \<inter> nts (rename_prods g ps2) = {}" by simp
qed


(* True iff the given production is in CNF *)
definition prod_CNF where "prod_CNF p \<equiv> (\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. (snd p) = [Tm t])"


(* renaming productions in CNF yields productions in CNF *)
lemma prod_rename_cnf:
  shows "prod_CNF p \<Longrightarrow> prod_CNF (rename_prod f (p))"
unfolding prod_CNF_def
proof -
  assume cases: "(\<exists>B C. snd p = [Nt B, Nt C]) \<or> (\<exists>t. snd p = [Tm t])"
  show "(\<exists>B C. snd (rename_prod f p) = [Nt B, Nt C]) \<or> (\<exists>t. snd (rename_prod f p) = [Tm t])"
  proof (cases "(\<exists>B C. snd p = [Nt B, Nt C])")
    case True
    then obtain B C where "snd p = [Nt B, Nt C]" by auto

    moreover have "snd (rename_prod f p) = rename_syms f (snd p)"
      by (metis eq_snd_iff rename_prod.simps)
    moreover have "Nt (f B) = rename_sym f (Nt B)" by simp
    moreover have "Nt (f C) = rename_sym f (Nt C)" by simp
    ultimately have "snd (rename_prod f p) = [Nt (f B), Nt (f C)]"
      by simp
    then show ?thesis
      by blast
  next
    case False
    then have "(\<exists>t. snd p = [Tm t])" using cases by simp
    then obtain t where "snd p = [Tm t]" by auto
    moreover have "snd (rename_prod f p) = rename_syms f (snd p)"
      by (metis eq_snd_iff rename_prod.simps)
    ultimately have "snd (rename_prod f p) = [Tm t]" by simp
    then show ?thesis by blast
  qed
qed


(* renaming grammars in CNF yields grammars in CNF *)
lemma cfg_rename_cnf_dir1:
  shows "cnf G \<Longrightarrow> cnf (rename_cfg f G)"
unfolding CNF_def
proof -
  fix x
  assume "\<forall>(A, \<alpha>)\<in>set (prods G). (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t])"
  then have "\<forall>p\<in>set (prods G). prod_CNF p" unfolding prod_CNF_def by auto
  then have "\<forall>P\<in>set (prods (rename_cfg f G)). prod_CNF P"
    by (simp add: prod_rename_cnf prods_rename_cfg_rename_prods)
  then show "\<forall>(A, \<alpha>)\<in>set (prods (rename_cfg f G)). (\<exists>B C. \<alpha> = [Nt B, Nt C]) \<or> (\<exists>t. \<alpha> = [Tm t])"
    unfolding prod_CNF_def by auto
qed

(* renamed grammars are in CNF iff original grammars is in CNF *)
(* currently unused *)
lemma cfg_rename_cnf:
  assumes "inj f"
  shows "cnf (G::('n,'t) cfg) \<longleftrightarrow> cnf (rename_cfg f G)" (is "?l \<longleftrightarrow> ?r")
proof
  show "cnf G \<Longrightarrow> cnf (rename_cfg f G)" by (rule cfg_rename_cnf_dir1)
next
  (* TODO: remove code duplication *)
  (* since f is injective, the second direction follows from the first by using the inverse *)
  obtain "g" where "g = the_inv f" and inv: "(\<And>x. (g (f x) = x))" using \<open>inj f\<close>
    by (simp add: the_inv_f_f)
  then have "\<And>(s::('n,'t) sym). rename_sym g (rename_sym f s) = s"
  proof -
    fix s
    show "rename_sym g (rename_sym f s) = (s::('n,'t) sym)"
    proof (cases s)
      case (Nt t)
      then have "(rename_sym f s) = Nt (f t)" by simp
      moreover have "rename_sym g (Nt (f t)) = Nt (g (f t))" by simp
      moreover have "Nt (g (f t)) = Nt t" using inv by simp
      ultimately show ?thesis using Nt by simp
    qed simp
  qed                                             
  then have inv_rename_syms: "\<And>(ss::('n,'t) syms). rename_syms g (rename_syms f ss) = ss"
    by (simp add: map_idI)
  with inv have "\<And>(p::('n,'t) prod). rename_prod g (rename_prod f p) = p" by force
  then have inv_rename_prods: "\<And>(ps::('n,'t) prods). rename_prods g (rename_prods f ps) = ps"
    by (simp add: map_idI)
  then have inv_rename_cfg: "\<And>(G::('n,'t) cfg). (rename_cfg g) ((rename_cfg f) G) = G"
    by (metis cfg.collapse inv rename_cfg.simps)
  then show "?r \<Longrightarrow> ?l"
    by (metis cfg_rename_cnf_dir1)
qed


end
