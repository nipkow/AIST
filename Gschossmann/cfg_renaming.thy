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


(* The lemmas about derivel are analogous to those about derive *)


(* definition of functions that, together, rename nonterminals of a cfg *)

fun rename_sym :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) sym \<Rightarrow> ('new,'t) sym" where
  "rename_sym f (Nt n) = Nt (f n)" |
  "rename_sym f (Tm t) = Tm t"

abbreviation "rename_syms f \<equiv> map (rename_sym f)"

fun rename_prod :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) prod \<Rightarrow> ('new,'t) prod" where
  "rename_prod f (lhs,rhs) = (f lhs, rename_syms f rhs)"

(* abbreviation "rename_prods f \<equiv> map (rename_prod f)" *)

abbreviation "rename_Prods f P \<equiv> rename_prod f ` P"


(*fun rename_cfg :: "('old \<Rightarrow> 'new) \<Rightarrow> ('old,'t) cfg \<Rightarrow> ('new,'t) cfg" where
  "rename_cfg f (cfg ps st) = cfg (rename_prods f ps) (f st)"*)


lemma map_Nt_rename_syms: "rename_syms f (map Nt xs) = map Nt (map f xs)"
  by simp

lemma map_Tm_rename_syms: "rename_syms f (map Tm xs) = map Tm xs"
  by simp


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
lemma rename_Prods_derives_dir1:
  shows "P \<turnstile> a \<Rightarrow>* b \<Longrightarrow> (rename_Prods f P) \<turnstile> (rename_syms f a) \<Rightarrow>* (rename_syms f b)"
proof (induction rule: derives_induct')
  case base
  then show ?case
    by simp
next
  let ?sym_f = "rename_syms f"
  case (step u A v w)
  then have "(f A, rename_syms f w) \<in> rename_Prods f P"
    by (metis image_eqI rename_prod.simps) 
  then have "rename_Prods f P \<turnstile> [Nt (f A)] \<Rightarrow>* ?sym_f w"
    using derive_singleton by blast
  then have "rename_Prods f P \<turnstile> ?sym_f [Nt A] \<Rightarrow>* ?sym_f w" by simp
  moreover
  from step have "rename_Prods f P \<turnstile> ?sym_f u @ ?sym_f w @ ?sym_f v \<Rightarrow>* rename_syms f b" by simp
  ultimately have "rename_Prods f P \<turnstile> ?sym_f u @ ?sym_f [Nt A] @ ?sym_f v \<Rightarrow>* rename_syms f b"
    by (meson derives_append derives_prepend rtranclp_trans) 
  then show ?case by auto
qed


lemma rename_Prods_derivel_dir1:
  assumes "P \<turnstile> a \<Rightarrow>l b"
  shows "rename_Prods f P \<turnstile> (rename_syms f a) \<Rightarrow>l (rename_syms f b)"
proof -
  from assms obtain A w u1 u2 where A_w_u1_u2: "(A,w) \<in> P \<and>
                                          a = map Tm u1 @ Nt A # u2 \<and>
                                          b = map Tm u1 @ w @ u2"
    unfolding derivel_iff by fast
  then have "(f A, rename_syms f w) \<in> (rename_Prods f P) \<and> 
             rename_syms f a = map Tm u1 @ Nt (f A) # rename_syms f u2 \<and>
             rename_syms f b = map Tm u1 @ rename_syms f w @ rename_syms f u2"
    by force
  then have "(\<exists> (A,w) \<in> rename_Prods f P.
        \<exists>u1 u2. rename_syms f a = map Tm u1 @ Nt A # u2 \<and> rename_syms f b = map Tm u1 @ w @ u2)"
    by blast
  then show ?thesis by (simp only: derivel_iff)
qed

lemma rename_Prods_deriveln_dir1:
  shows "P \<turnstile> a \<Rightarrow>l(n) b \<Longrightarrow> rename_Prods f P \<turnstile> rename_syms f a \<Rightarrow>l(n) rename_syms f b"
proof (induction n arbitrary: b)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then obtain c where a_c: "P \<turnstile> a \<Rightarrow>l(n) c" and c_b: "P \<turnstile> c \<Rightarrow>l b"
    using relpowp_Suc_E by metis
  
  from a_c Suc(1) have "rename_Prods f P \<turnstile> rename_syms f a \<Rightarrow>l(n) rename_syms f c"
    by simp
  moreover from c_b have "rename_Prods f P \<turnstile> rename_syms f c \<Rightarrow>l rename_syms f b"
    by (rule rename_Prods_derivel_dir1)

  ultimately show ?case
    using relpowp_Suc_I by metis
qed

lemma rename_Prods_derivels_dir1:
  shows "P \<turnstile> a \<Rightarrow>l* b \<Longrightarrow> rename_Prods f P \<turnstile> rename_syms f a \<Rightarrow>l* rename_syms f b"
  by (metis rename_Prods_deriveln_dir1 rtranclp_power)



lemma inv_rename_Prods:
  assumes "\<And>(p::('a,'t) prod). rename_prod g (rename_prod f p) = p"
  shows "rename_Prods g (rename_Prods f (ps::('a,'t) Prods)) = ps"
proof
  show "rename_Prods g (rename_Prods f ps) \<subseteq> ps"
  proof
    fix x
    assume assm: "x \<in> rename_Prods g (rename_Prods f ps)"
    then obtain y where y: "rename_prod g y = x" and "y \<in> rename_Prods f ps"
      by auto
    then obtain z where z: "rename_prod f z = y" and z_ps: "z \<in> ps"
      by auto
    from assms y z have "x = rename_prod g (rename_prod f z)" by simp
    with assms have "x = z" by simp
    with z_ps show "x \<in> ps" by simp
  qed
next
  show "ps \<subseteq> rename_Prods g (rename_Prods f ps)"
  proof
    fix x
    assume "x \<in> ps"
    then have "rename_prod f x \<in> rename_Prods f ps" by simp
    then have "rename_prod g (rename_prod f x) \<in> rename_Prods g (rename_Prods f ps)" by simp
    with assms show "x \<in> rename_Prods g (rename_Prods f ps)" by simp
  qed
qed


(* renamed syms are derivable in the renamed grammar 
   iff their non-renamed counterpart is derivable in the original grammar *)
lemma rename_Prods_derives_iff:
  assumes "inj (f:: 'a \<Rightarrow> 'b)"
  shows "P \<turnstile> (a:: ('a,'t) syms) \<Rightarrow>* b \<longleftrightarrow> rename_Prods f P \<turnstile> (rename_syms f a) \<Rightarrow>* (rename_syms f b)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by (rule rename_Prods_derives_dir1)
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
  then have inv_rename_prods: "\<And>(ps::('a,'t) Prods). rename_Prods g (rename_Prods f ps) = ps"
    by (rule inv_rename_Prods)
  then show "?r \<Longrightarrow> ?l" using rename_Prods_derives_dir1[where f=g]
    by (metis inv_rename_syms)
qed







(* renamed syms are derivable in the renamed grammar 
   iff their non-renamed counterpart is derivable in the original grammar *)
lemma rename_Prods_derivels_iff:
  assumes "inj (f:: 'a \<Rightarrow> 'b)"
  shows "P \<turnstile> (a:: ('a,'t) syms) \<Rightarrow>l* b \<longleftrightarrow> rename_Prods f P \<turnstile> (rename_syms f a) \<Rightarrow>l* (rename_syms f b)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by (rule rename_Prods_derivels_dir1)
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
  then have inv_rename_prods: "\<And>(ps::('a,'t) Prods). rename_Prods g (rename_Prods f ps) = ps"
    by (rule inv_rename_Prods)
  then show "?r \<Longrightarrow> ?l" using rename_Prods_derivels_dir1[where f=g]
    by (metis inv_rename_syms)
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
  assumes "rlin2 P"
  shows "rlin2 (rename_Prods f P)"
proof -
  from assms have "\<forall>(A,w) \<in> P. w = [] \<or> (\<exists>a B. w = [Tm a, Nt B])" unfolding rlin2_def by simp
  then have "\<forall>(_,w) \<in> P. syms_rlin2 w" unfolding syms_rlin2_def by simp
  then have "\<forall>(_,w) \<in> P. syms_rlin2 (rename_syms f w)" by (auto simp add: syms_rename_rlin2)
  then have "\<forall>(_,w) \<in> rename_Prods f P. syms_rlin2 w" by auto
  then show "rlin2 (rename_Prods f P)" unfolding rlin2_def syms_rlin2_def by simp
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
lemma nts_rename_Prods: "Nts (rename_Prods f P) = f ` Nts P"
proof
  show "Nts (rename_Prods f P) \<subseteq> f ` Nts P"
  proof
    fix y
    assume "y \<in> Nts (rename_Prods f P)"
    then obtain p' where mapped: "p' \<in> rename_Prods f P" and contained: "(y = fst p' \<or> Nt y \<in> set (snd p'))"
      by (meson in_Nts)
    
    from mapped obtain p where p: "p \<in> P \<and> p' = rename_prod f p"
      by blast

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
    then have "y = f x \<and> x \<in> Nts P"
      by (metis fresh_set fresh_syms p prod.collapse syms_not_eq) 
    then show "y \<in> f ` Nts P" by auto
  qed
next
  show "f ` Nts P \<subseteq> Nts (rename_Prods f P)"
  proof
    fix y
    assume "y \<in> f ` Nts P"
    then obtain x where x_y: "y = f x" and x_nts: "x \<in> Nts P" by blast
    then obtain p where "p \<in> P" and contained: "(x = fst p \<or> Nt x \<in> set (snd p))"
      by (meson in_Nts)
    then have "rename_prod f p \<in> rename_Prods f P"
      by simp 
    moreover from contained have "(y = fst (rename_prod f p) \<or> Nt y \<in> set (snd (rename_prod f p)))"
      by (metis (mono_tags, opaque_lifting) x_y image_iff list.set_map rename_prod.simps rename_sym.simps(1) split_pairs)
    ultimately show "y \<in> Nts (rename_Prods f P)"
      by (metis Lhss_set fresh_Lhss fresh_set prod.collapse)
  qed
qed

(* using functions with disjoint ranges for renaming yields different sets of nonterminals *)
lemma rename_prods_disjoint:
  assumes "range f \<inter> range g = {} "
  shows "Nts (rename_Prods f ps1) \<inter> Nts (rename_Prods g ps2) = {}"
proof -
  have "(f ` Nts ps1) \<inter> (g ` Nts ps2) = {}"  using assms by auto
  moreover have "Nts (rename_Prods f ps1) = f ` Nts ps1" by (rule nts_rename_Prods)
  moreover have "Nts (rename_Prods g ps2) = g ` Nts ps2" by (rule nts_rename_Prods)
  ultimately show "Nts (rename_Prods f ps1) \<inter> Nts (rename_Prods g ps2) = {}" by simp
qed


(* True iff the given production is in CNF *)
definition prod_CNF where "prod_CNF p \<equiv> (\<exists>B C. (snd p) = [Nt B, Nt C]) \<or> (\<exists>t. (snd p) = [Tm t])"


(* renaming productions in CNF yields productions in CNF *)
(* currently unused *)
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
lemma rename_Prods_cnf_dir1:
  shows "CNF P \<Longrightarrow> CNF (rename_Prods f P)"
  unfolding CNF_def by auto

end
