theory Chomsky_Normal_Form_Fun
  imports Chomsky_Normal_Form
begin

section \<open>Uniformize\<close>
subsection \<open>uniformize_fun\<close>
subsubsection \<open>replaceTm\<close>


lemmas Tms_defs = Tms_def Tms_syms_def

subsubsection \<open>uniformize\<close>


fun uniformize_fun :: "'n::fresh0 \<Rightarrow> 't \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "uniformize_fun A t [] = [(A, [Tm t])]" |
  "uniformize_fun A t ((l,r) # ps) = 
    (let r' = substsTm t A r in 
      if r = r' \<or> length r \<le> 1 then (l,r) # uniformize_fun A t ps
      else (l,r') # uniformize_fun A t ps)"


lemma substsTm_eq_iff_no_t:
  "substsTm t A r = r \<longleftrightarrow> Tm t \<notin> set r"
  unfolding substsTm_def 
  by (smt (verit, ccfv_SIG) isTm_simps(1,2) map_eq_conv map_ident)

lemma substsTm_removes_ts:
  "Tms {(l,substsTm t A r)} = Tms {(l,r)} - {t}"
  unfolding substsTm_def Tms_defs by force

lemma substsTm_idem[simp]:
  "substsTm t A (substsTm t A r) = substsTm t A r"
  unfolding substsTm_def by simp

lemma uniformize_fun_recurses[elim]:
  obtains p' where "uniformize_fun A t (p#ps) = p' # uniformize_fun A t ps"
  by (smt (verit, ccfv_threshold) list.distinct(1) list.inject uniformize_fun.elims)

lemma uniformize_fun_length_preserved[simp]:
  "length (uniformize_fun A t ps) = Suc (length ps)"
proof (induction ps)
  case (Cons p ps)
  from uniformize_fun_recurses obtain p' where "uniformize_fun A t (p#ps) = p' # uniformize_fun A t ps"
    by metis
  then show ?case using Cons by simp
qed simp

lemma uniformize_fun_eq_iff_badProds_empty:
  "uniformize_fun A t ps = ps @ [(A, [Tm t])] \<longleftrightarrow> badProds (set ps) t = {}"
proof (induction ps)
  case Nil
  then show ?case unfolding badProds_def by simp
next
  case (Cons p ps)
  let ?unif_id = "uniformize_fun A t ps = ps @ [(A, [Tm t])]"
  obtain l r where lr: "p = (l,r)" by fastforce
  then have "uniformize_fun A t (p#ps) = (p#ps) @ [(A, [Tm t])]
        \<longleftrightarrow> uniformize_fun A t ((l,r)#ps) = (p#ps) @ [(A, [Tm t])]" by metis
  also have "... \<longleftrightarrow> (uniformize_fun A t ((l,r)#ps) = (l,r) # uniformize_fun A t ps) \<and> ?unif_id"
    by (metis append_Cons list.inject lr uniformize_fun_recurses)
  also have "(uniformize_fun A t ((l,r)#ps) = (l,r) # uniformize_fun A t ps) \<and> ?unif_id
        \<longleftrightarrow> (substsTm t A r = r \<or> length r < 2) \<and> ?unif_id" 
    using list.inject by fastforce
  also have "... \<longleftrightarrow> badProds {p} t = {} \<and> ?unif_id" using lr unfolding badProds_def 
    using lr substsTm_eq_iff_no_t by force
  also have "... \<longleftrightarrow> badProds {p} t = {} \<and> badProds (set ps) t = {}" using Cons by satx
  also have "... \<longleftrightarrow> badProds (set (p#ps)) t = {}" unfolding badProds_def by auto
  finally show ?case .
qed

corollary uniformize_fun_eq_impl_no_badProds:
  assumes "uniformize_fun A t ps = ps @ [(A, [Tm t])]"
  shows "\<forall>(l,r)\<in>set ps. Tm t \<notin> set r \<or> length r \<le> 1"
  using assms uniformize_fun_eq_iff_badProds_empty
  unfolding badProds_def by force

lemma uniformize_fun_contains_At:
  "(A,[Tm t]) \<in> set (uniformize_fun A t ps)"
proof (induction ps)
  case (Cons p ps)
  moreover from uniformize_fun_recurses obtain p' where 
    "uniformize_fun A t (p#ps) = p'#uniformize_fun A t ps" by metis
  ultimately show ?case by simp 
qed simp
  

lemma uniformize_fun_goodProds_preserved:
  "(l,r) \<in> set ps - (badProds (set ps) t) \<Longrightarrow> (l,r) \<in> set (uniformize_fun A t ps)"
proof (induction ps)
  case (Cons p ps)
  show ?case 
  proof (cases "(l,r) = p")
    case True
    from Cons(2) have "Tm t \<notin> set r \<or> length r \<le> 1" unfolding badProds_def by fastforce
    with True have "uniformize_fun A t (p#ps) = (l,r) # uniformize_fun A t ps" 
      using substsTm_eq_iff_no_t by (smt (verit, del_insts) uniformize_fun.simps(2))
    then show ?thesis by simp
  next
    case False
    with Cons(2) have "(l,r) \<in> set ps - badProds (set ps) t"
      unfolding badProds_def by fastforce
    moreover obtain p' where "uniformize_fun A t (p#ps) = p'#uniformize_fun A t ps"
      using uniformize_fun_recurses by metis
    ultimately show ?thesis using Cons(1) by simp
  qed
qed simp

lemma uniformize_fun_badProds_subst:
  "(l,r) \<in> badProds (set ps) t \<Longrightarrow> (l,substsTm t A r) \<in> set (uniformize_fun A t ps)"
proof (induction ps)
  case Nil
  then show ?case unfolding badProds_def by simp (* try0 example *)
next
  case (Cons p ps)
  show ?case
  proof (cases "(l,r) = p")
    case True
    have "uniformize_fun A t (p#ps) = (l,substsTm t A r) # uniformize_fun A t ps"
    proof -
      from Cons(2) have "length r > 1 \<and> Tm t \<in> set r" unfolding badProds_def by force
      with True show ?thesis by (smt (verit, best) linorder_not_le uniformize_fun.simps(2))
    qed
    then show ?thesis by simp
  next
    case False
    with Cons have "(l,substsTm t A r) \<in> set (uniformize_fun A t ps)" unfolding badProds_def 
      by simp (* try0 example *)
    moreover from uniformize_fun_recurses obtain p' where 
      "uniformize_fun A t (p#ps) = p' # uniformize_fun A t ps" by metis
    ultimately show ?thesis by simp
  qed
qed

lemma P'_insert:
  "(set ps - badProds (set ps) t) \<union> Unif A t (set ps) \<union> {(A, [Tm t])} 
    \<subseteq> (set (p#ps) - badProds (set (p#ps)) t) \<union> Unif A t (set (p#ps)) \<union> {(A, [Tm t])}"
  unfolding badProds_def Unif_def by auto

lemma uniformize_fun_subset_P':
  "set (uniformize_fun A t ps) \<subseteq> (set ps - badProds (set ps) t) \<union> Unif A t (set ps) \<union> {(A, [Tm t])}"
  (is "_ \<subseteq> ?P' ps")
proof (induction ps)
  case (Cons p ps)
  obtain l r where lr: "p = (l,r)" by fastforce
  consider (id) "substsTm t A r = r \<or> length r < 2" | 
          (subst) "substsTm t A r \<noteq> r \<and> length r \<ge> 2" by linarith
  then show ?case 
  proof cases
    case id
    hence "Tm t \<notin> set r \<or> length r \<le> 1" using substsTm_eq_iff_no_t by fastforce
    hence "(l,r) \<in> set (p#ps) - badProds (set (p#ps)) t"
      unfolding badProds_def using lr by fastforce
    moreover from Cons P'_insert have 
      "set (uniformize_fun A t ps) \<subseteq> ?P' (p#ps)" by fast
    moreover from id have "uniformize_fun A t (p#ps) = (l,r) # uniformize_fun A t ps" 
      using lr by fastforce
    ultimately show ?thesis by simp
  next
    case subst
    hence "uniformize_fun A t (p#ps) = (l, substsTm t A r) # uniformize_fun A t ps"
      using lr by force
    moreover with subst have "(l, substsTm t A r) \<in> Unif A t (set (p#ps))"
      unfolding Unif_def badProds_def using lr substsTm_eq_iff_no_t by fastforce
    moreover from Cons P'_insert have "set (uniformize_fun A t ps) \<subseteq> ?P' (p#ps)" by fast
    ultimately show ?thesis by simp
  qed
qed simp

lemma uniformize_fun_uniformizes:
  assumes "uniformize_fun A t ps \<noteq> ps @ [(A,[Tm t])]" 
  shows "set (uniformize_fun A t ps) = (set ps - badProds (set ps) t) \<union> Unif A t (set ps) \<union> {(A,[Tm t])}"
  using uniformize_fun_goodProds_preserved uniformize_fun_badProds_subst uniformize_fun_contains_At
    uniformize_fun_subset_P' unfolding Unif_def by fast

lemma uniformize_fun_uniformized:
  assumes "uniformize_fun A t ps \<noteq> ps @ [(A, [Tm t])]"
          "A \<notin> (Nts (set ps) \<union> {S})"
  shows "uniformize A t S (set ps) (set (uniformize_fun A t ps))"
  using assms uniformize_fun_uniformizes uniformize_fun_eq_iff_badProds_empty
  unfolding uniformize_def by metis

lemma uniformize_fun_dec_badTmsCount:
  assumes "uniformize_fun A t ps \<noteq> ps @ [(A, [Tm t])]"
          "A \<notin> Nts (set ps) \<union> {S}"
  shows "badTmsCount (set (uniformize_fun A t ps)) < badTmsCount (set ps)"
  using assms uniformize_fun_uniformized lemma6_a by fast

lemma uniformize_fun_Tms_insert:
  "Tms (set (uniformize_fun A t ps)) \<subseteq> Tms (set (uniformize_fun A t (p#ps)))"
  unfolding Tms_defs
  by (metis SUP_subset_mono dual_order.refl set_subset_Cons uniformize_fun_recurses)

lemma uniformize_fun_adds_t:
  "t \<notin> Tms (set ps) \<Longrightarrow> Tms (set ps) \<union> {t} = Tms (set (uniformize_fun A t ps))"
proof (induction ps)
  case Nil
  then show ?case unfolding Tms_def by simp
next
  case (Cons p ps)
  hence "Tm t \<notin> set (snd p)" unfolding Tms_defs by auto
  hence "uniformize_fun A t (p#ps) = p # uniformize_fun A t ps" 
    by (smt (verit, del_insts) snd_conv substsTm_eq_iff_no_t surj_pair uniformize_fun.simps(2))
  hence "Tms (set (uniformize_fun A t (p#ps))) = Tms {p} \<union> Tms (set (uniformize_fun A t ps))"
    unfolding Tms_def by simp
  also with Cons have "... = Tms {p} \<union> Tms (set ps) \<union> {t}" unfolding Tms_def by auto
  also have "... = Tms (set (p#ps)) \<union> {t}" unfolding Tms_def by simp
  finally show ?case by simp
qed


lemma uniformize_fun_unchanged_tms:
  "t \<in> Tms (set ps) \<Longrightarrow> Tms (set ps) = Tms (set (uniformize_fun A t ps))"
proof (induction ps)
  case Nil
  then show ?case unfolding Tms_def by simp
next
  case (Cons p ps)
  then show ?case 
  proof (cases "t \<in> Tms (set ps)")
    case True
    consider (goodProd) "uniformize_fun A t (p#ps) = p # uniformize_fun A t ps" |
             (badProd) "uniformize_fun A t (p#ps)  
                        = (fst p, substsTm t A (snd p)) # uniformize_fun A t ps"
      by (smt (verit, best) surjective_pairing uniformize_fun.simps(2))
    then show ?thesis 
    proof cases
      case goodProd
      hence "Tms (set (uniformize_fun A t (p#ps))) = Tms (set (p # uniformize_fun A t ps))"
        by metis
      also have "... = Tms {p} \<union> Tms (set (uniformize_fun A t ps))" unfolding Tms_def by auto
      also with Cons(1)[OF True] have "... = Tms {p} \<union> Tms (set ps)" by metis
      finally show ?thesis unfolding Tms_def by simp
    next
      case badProd
      hence "Tms (set (uniformize_fun A t (p#ps))) 
              = Tms (set ((fst p, substsTm t A (snd p)) # uniformize_fun A t ps))" by metis
      also have "... = Tms {(fst p, substsTm t A (snd p))} \<union> Tms (set (uniformize_fun A t ps))"
        unfolding Tms_def by force
      also have "... = Tms {p} - {t} \<union> Tms (set (uniformize_fun A t ps))"
        using substsTm_removes_ts[of "fst p" _ _ "snd p"] by simp
      also have "... = Tms {p} \<union> Tms (set ps)" using Cons(1)[OF True] True by blast
      finally show ?thesis unfolding Tms_def by simp
    qed
  next
    case False
    with Cons(2) have t_in_p: "Tm t \<in> set (snd p)" unfolding Tms_defs 
      by fastforce
    consider (goodProd) "length (snd p) \<le> 1" | (badProd) "length (snd p) > 1" by linarith
    then show ?thesis
    proof cases
      case goodProd
      hence "uniformize_fun A t (p#ps) = p # uniformize_fun A t ps"
        by (smt (verit, best) eq_snd_iff uniformize_fun.simps(2)) 
      hence "Tms (set (uniformize_fun A t (p#ps))) = Tms (set (p # uniformize_fun A t ps))" by metis
      also have "... = Tms {p} \<union> Tms (set (uniformize_fun A t ps))" unfolding Tms_def by auto
      also have "... = Tms {p} \<union> Tms (set ps) \<union> {t}" using uniformize_fun_adds_t[OF False] by simp
      also have "... = Tms (set (p#ps)) \<union> {t}" unfolding Tms_def by auto
      also have "... = Tms (set (p#ps))" using Cons(2) by blast
      finally show ?thesis by simp
    next
      case badProd
      with t_in_p have "uniformize_fun A t (p#ps) 
        = (fst p, substsTm t A (snd p)) # uniformize_fun A t ps" 
        by (smt (verit) less_le_not_le prod.collapse uniformize_fun.simps(2))
      hence "Tms (set (uniformize_fun A t (p#ps))) 
        = Tms (set ((fst p, substsTm t A (snd p)) # uniformize_fun A t ps))" 
        unfolding Tms_def by metis
      also have "... = Tms {(fst p, substsTm t A (snd p))} \<union> Tms (set (uniformize_fun A t ps))" 
        unfolding Tms_def by simp
      find_theorems name: substsTm
      also have "... = Tms {p} - {t} \<union> Tms (set (uniformize_fun A t ps))" 
        using substsTm_removes_ts[of "fst p" _ _ "snd p"] by simp
      also have "... = Tms {p} - {t} \<union> Tms (set ps) \<union> {t}"
        using uniformize_fun_adds_t[OF False] by auto
      also have "... = Tms {p} \<union> Tms (set ps)" using Cons(2) unfolding Tms_def by fastforce
      finally show ?thesis unfolding Tms_def by force
    qed
  qed
qed


lemma uniformize_fun_no_new_badTms:
  "\<lbrakk>ps' = uniformize_fun A t ps; \<forall>p\<in>set ps. Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1\<rbrakk> 
    \<Longrightarrow> \<forall>p\<in>set ps'. Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1"
proof (induction ps arbitrary: ps')
  case (Cons p ps)
  obtain l r where lr: "(l,r) = p" using old.prod.exhaust by metis
  with Cons(3) have p: "Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1" by fastforce
  with lr have no_new_bad_t': "Tm t' \<notin> (set r) \<or> length r \<le> 1" 
    "Tm t' \<notin> (set (substsTm t A r)) \<or> length (substsTm t A r) \<le> 1"
    unfolding substsTm_def by (fastforce, use lr p in auto)
  from lr consider "uniformize_fun A t ((l,r)#ps) = (l,r) # uniformize_fun A t ps" | 
    "uniformize_fun A t ((l,r)#ps) = (l,substsTm t A r) # uniformize_fun A t ps"
    by (smt (verit, ccfv_SIG) uniformize_fun.simps(2))
  then show ?case by cases (use no_new_bad_t' Cons lr in auto)
qed simp

lemma prod_lost_impl_t:
  assumes "p \<in> set ps \<and> p \<notin> set (uniformize_fun A t ps)"
  shows "Tm t \<in> set (snd p)"
  using assms 
  by (metis DiffI substsTm_eq_iff_no_t surjective_pairing uniformize_fun_badProds_subst
      uniformize_fun_goodProds_preserved)

lemma uniformize_fun_neq_impl_t_in_prods:
  assumes "uniformize_fun A t ps \<noteq> ps @ [(A, [Tm t])]"
          "A \<notin> Nts (set ps) \<union> {S}"
  shows "t \<in> Tms (set ps)"
proof -
  obtain p where "p \<in> set ps \<and> p \<notin> set (uniformize_fun A t ps)"
  proof -
    from uniformize_fun_eq_iff_badProds_empty obtain l r where lr: "(l,r)\<in>badProds (set ps) t"
      using assms by fast
    with uniformize_fun_uniformized[OF assms] have "(l,r) \<notin> set (uniformize_fun A t ps)"
      "(l,substsTm t A r) \<in> set (uniformize_fun A t ps)" 
      using uniformize_badProds_not_preserved uniformize_badProds_uniformized assms
       badProds_subset by fastforce+
    thus thesis using that lr
      by (metis lr \<open>(l, r) \<notin> set (uniformize_fun A t ps)\<close> badProds_subset subsetD)
  qed
  with prod_lost_impl_t show ?thesis unfolding Tms_defs by fastforce
qed

lemma uniformize_fun_comp_appends:
  "ps' = uniformize_fun A t ps \<Longrightarrow> uniformize_fun A t ps' = ps' @ [(A, [Tm t])]"
proof (induction ps' arbitrary: ps)
  case (Cons p' ps')
  note pps' = Cons.prems
  show ?case
  proof (cases ps)
    case Nil
    then show ?thesis using pps' by simp
  next
    case (Cons p ps'')
    then have "ps' = uniformize_fun A t ps''"   
      by (metis Cons.prems list.inject uniformize_fun_recurses)
    with Cons.IH have IH: "uniformize_fun A t ps' = ps' @ [(A, [Tm t])]" by metis
  from Cons.prems  consider (id) "p' = p" | (subst) "p' = (fst p, substsTm t A (snd p))"
    by (smt (verit, best) list.discI list.inject local.Cons split_pairs uniformize_fun.elims)
  then show ?thesis
  proof cases
    case id
    hence "uniformize_fun A t (p' # ps') = p' # uniformize_fun A t ps'"
      using Cons pps'
      by (smt (verit, best) Pair_inject list.distinct(1) list.inject uniformize_fun.elims)
    then show ?thesis using IH by auto
  next
    case subst
    have "uniformize_fun A t (p' # ps) = p' # uniformize_fun A t ps" using substsTm_idem
      by (simp add: local.subst)
    then show ?thesis using IH by (simp add: local.subst)
    qed
  qed
qed simp


lemma uniformize_fun_no_badProds:
  "badProds (set (uniformize_fun A t ps)) t = {}"
   using uniformize_fun_comp_appends by (metis uniformize_fun_eq_iff_badProds_empty)

subsection \<open>uniformize_tm\<close>

definition freshA :: "('n::fresh0,'t) prods \<Rightarrow> 'n \<Rightarrow> 'n" where
  "freshA ps S = fresh0 (Nts (set ps) \<union> {S})"

lemma freshA_notin_set: (* simp? *)
  shows "freshA ps S \<notin> (Nts (set ps) \<union> {S})"
  unfolding freshA_def by (metis ID.set_finite finite_Un finite_nts fresh0_notIn)

lemma uniformize_fun_unifRtc:
  assumes "uniformize_fun A t ps \<noteq> ps @ [(A, [Tm t])]"
          "A \<notin> Nts (set ps) \<union> {S}"
  shows "(\<lambda>x y. \<exists>A. uniformize A t S x y)\<^sup>*\<^sup>* (set ps) (set (uniformize_fun A t ps))"
  using assms uniformize_fun_uniformized by fastforce

subsection \<open>uniformize_all\<close>


fun uniformize_all :: "'n::fresh0 \<Rightarrow> 't list \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "uniformize_all _ [] ps = ps" |
  "uniformize_all S (t#ts) ps = (let ps' = uniformize_fun (freshA ps S) t ps in 
    if ps' = ps @ [(freshA ps S, [Tm t])] then uniformize_all S ts ps
    else uniformize_all S ts ps')"

lemma uniformize_all_unchanged_tms:
  "Tms (set ps) = Tms (set (uniformize_all S ts ps))"
proof (induction ts arbitrary: ps)
  case (Cons t ts)
  then show ?case
  proof (cases "uniformize_fun (freshA ps S) t ps = ps @ [(freshA ps S, [Tm t])]")
    case True
    then show ?thesis using Cons by auto
  next
    case False
    hence "uniformize_all S (t#ts) ps = uniformize_all S ts
            (uniformize_fun (freshA ps S) t ps)" by fastforce
    then show ?thesis using Cons uniformize_fun_neq_impl_t_in_prods False
      by (metis freshA_notin_set uniformize_fun_unchanged_tms)
  qed
qed simp

lemma uniformize_all_no_new_badTms:
    "\<lbrakk>\<forall>p\<in>set ps. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1; ps' = uniformize_all S ts ps\<rbrakk> 
      \<Longrightarrow> \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
proof (induction ts arbitrary: ps ps')
  case (Cons t' ts)
  let ?ps'' = "uniformize_fun (freshA ps S) t' ps"
  show ?case
  proof (cases "?ps'' = ps @ [(freshA ps S, [Tm t'])]")
    case True     
    then show ?thesis using Cons by simp
  next
    case False
    hence ps': "ps' = uniformize_all S ts ?ps''" by (simp add: Cons.prems(2))
    from uniformize_fun_no_new_badTms have 
      ps'': "\<forall>p\<in>set ?ps''. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1" using Cons.prems(1) by metis
    show ?thesis using Cons.IH[OF ps'' ps'] .
  qed
qed simp


lemma uniformize_all_no_badTms:
  assumes "Tms (set ps) \<subseteq> set ts" 
          "ps' = uniformize_all S ts ps"
  shows "badTmsCount (set ps') = 0"
proof -
  have "\<forall>t\<in>set ts. \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
    using assms(2) 
  proof (induction ts arbitrary: ps ps')
    case (Cons t ts)
    then show ?case 
    proof (cases "uniformize_fun (freshA ps S) t ps = ps @ [(freshA ps S, [Tm t])]")
      case True
      hence "uniformize_all S (t#ts) ps = uniformize_all S ts ps" by simp
      then show ?thesis using Cons uniformize_fun_eq_impl_no_badProds[OF True] 
         uniformize_all_no_new_badTms by fastforce
    next
      case False
      hence step: "uniformize_all S (t#ts) ps 
                  = uniformize_all S ts (uniformize_fun (freshA ps S) t ps)"
        by simp
      from uniformize_fun_no_badProds have 
        "\<forall>p\<in>set (uniformize_fun (freshA ps S) t ps). Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
        unfolding badProds_def by force
      then show ?thesis using Cons.IH[OF step] Cons.prems 
        by (metis insert_iff list.simps(15) local.step uniformize_all_no_new_badTms)
    qed
  qed simp
  with set_tms uniformize_all_unchanged_tms have 
    "\<forall>t\<in>Tms (set ps'). \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
    using assms by fast
  with assms show ?thesis unfolding Tms_defs
    by (metis (no_types, lifting) One_nat_def UnionI badTmsCountNot0 bot_nat_0.not_eq_extremum leD
        le_imp_less_Suc mem_Collect_eq numeral_2_eq_2 pair_imageI snd_conv list.set_finite)
qed


lemma uniformize_all_uniform:
  assumes "Tms (set ps) \<subseteq> set ts"
  shows "uniform (set(uniformize_all S ts ps))"
  using uniformize_all_no_badTms[OF assms] uniform_badTmsCount by blast


lemma uniformize_all_unifRtc:
  "(\<lambda>x y. \<exists>A t. uniformize A t S x y)\<^sup>*\<^sup>* (set ps) (set (uniformize_all S ts ps))"
proof (induction ts arbitrary: ps)
  case (Cons t ts)
  show ?case
  proof (cases "uniformize_fun (freshA ps S) t ps = ps @ [(freshA ps S, [Tm t])]")
    case True
    hence "uniformize_all S (t#ts) ps = uniformize_all S ts ps" by force
    then show ?thesis using Cons.IH[of ps] by metis
  next
    case False
    hence "uniformize_all S (t#ts) ps = uniformize_all S ts (uniformize_fun (freshA ps S) t ps)"
      by auto
    moreover from uniformize_fun_unifRtc[OF False freshA_notin_set] have 
      "(\<lambda>x y. \<exists>A t. uniformize A t S x y)\<^sup>*\<^sup>* (set ps) (set (uniformize_fun (freshA ps S) t ps))"
      by (smt (verit, ccfv_threshold) mono_rtranclp)
    ultimately show ?thesis using Cons.IH by (simp add: rtranclp_trans)
  qed
qed simp

section \<open>BinarizeNt\<close>
subsection \<open>binarizeNt_fun\<close>
subsubsection \<open>replaceNts\<close>

(*Simplifying the first two cases complicates proofs*)
fun replaceNts :: "'n::fresh0 \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n \<times> 'n) option \<times> ('n,'t) syms" where
  "replaceNts A [] = (None, [])" |
  "replaceNts A [s] = (None, [s])" |
  "replaceNts A (Nt s\<^sub>1 # Nt s\<^sub>2 # sl) = (Some (s\<^sub>1, s\<^sub>2), Nt A # sl)" |
  "replaceNts A (s#sl) = (let (nn_opt, sl') = replaceNts A sl in (nn_opt, s#sl'))"

lemma replaceNts_tm_unchanged_opt:
  assumes 
    "replaceNts A (s0#s1#sl) = (nn_opt, sl')"
    "\<exists>t. s0 = Tm t \<or> s1 = Tm t"
  obtains sl'' where "replaceNts A (s1#sl) = (nn_opt, sl'')"
proof -
  obtain nn_opt' sl'' where "replaceNts A (s1#sl) = (nn_opt', sl'')"
    by fastforce
  moreover with assms have "nn_opt = nn_opt'" by fastforce
  ultimately show thesis using that by blast
qed

lemma replaceNts_id_iff_None:
  assumes "replaceNts A sl = (nn_opt, sl')"
  shows "nn_opt = None \<longleftrightarrow> sl = sl'"
  using assms proof (induction sl arbitrary: nn_opt sl' rule: replaceNts.induct)
  case ("4_1" A t s sl)
  then obtain sl'' where rec: "replaceNts A (s#sl) = (nn_opt, sl'')"
    using replaceNts_tm_unchanged_opt by blast
  then show ?case using "4_1" by auto
next
  case ("4_2" A s t sl)
  then obtain sl'' where rec: "replaceNts A (Tm t#sl) = (nn_opt, sl'')"
    using replaceNts_tm_unchanged_opt by blast
  then show ?case using "4_2" by auto
qed auto



lemma replaceNts_replaces_pair:
  assumes 
    "replaceNts A sl = (nn_opt, sl')"
    "nn_opt \<noteq> None"
  obtains p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)"
    "sl = p@[Nt B\<^sub>1, Nt B\<^sub>2]@q"
    "sl' = p@[Nt A]@q" 
  using assms proof (induction sl arbitrary: thesis nn_opt sl' rule: replaceNts.induct)
  case ("4_1" A t s sl)
  then obtain sl'' where 
    "replaceNts A (s#sl) = (nn_opt, sl'')" 
    and sl'_def: "sl' = Tm t # sl''"
    using replaceNts_tm_unchanged_opt
    by (metis (lifting) case_prod_conv prod.inject replaceNts.simps(4))
  with "4_1"(1,4) obtain p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)" "s#sl = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl'' = p@[Nt A]@q" 
    by blast
  moreover with sl'_def have "Tm t #s#sl = (Tm t#p)@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl' = (Tm t#p)@[Nt A]@q"
    by auto
  ultimately show ?case using "4_1"(2) by blast
next
  case ("4_2" A s t sl)
  then obtain sl'' where 
    "replaceNts A (Tm t#sl) = (nn_opt, sl'')" 
    and sl'_def: "sl' = s # sl''"
    using replaceNts_tm_unchanged_opt
    by (metis (lifting) old.prod.case prod.inject replaceNts.simps(5))
  with "4_2"(1,4) obtain p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)" "Tm t#sl = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl'' = p@[Nt A]@q" 
    by blast
  moreover with sl'_def have "s#Tm t#sl = (s#p)@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "sl' = (s#p)@[Nt A]@q"
    by auto
  ultimately show ?case using "4_2"(2) by blast
qed fastforce+

corollary replaceNts_replaces_pair_Some:
  assumes "replaceNts A sl = (Some (B\<^sub>1,B\<^sub>2), sl')"
  obtains p q where 
    "sl = p@[Nt B\<^sub>1, Nt B\<^sub>2]@q"
    "sl' = p@[Nt A]@q"
  using replaceNts_replaces_pair 
  by (smt (verit) assms option.distinct(1) option.inject prod.inject)

subsubsection \<open>binarizeNt\<close>

fun binarizeNt_fun :: "'n::fresh0 \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "binarizeNt_fun A ps0 [] = ps0" |
  "binarizeNt_fun A ps0 ((l,r)#ps) = 
    (case replaceNts A r of 
      (None, _) \<Rightarrow> binarizeNt_fun A ps0 ps|
      (Some (B\<^sub>1,B\<^sub>2), r') \<Rightarrow> 
        if length r < 3 then binarizeNt_fun A ps0 ps 
        else (removeAll (l,r) ps0) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')])" 



lemma binarizeNt_fun_rec_if_id_or_lt3:
  assumes 
    "replaceNts A r = (nn_opt, r')"
    "r = r' \<or> length r < 3"
  shows "binarizeNt_fun A ps0 ((l,r)#ps) = binarizeNt_fun A ps0 ps"
  using assms replaceNts_id_iff_None by (cases nn_opt) auto
   

lemma binarizeNt_fun_binarizes:
  assumes "binarizeNt_fun A ps0 ps \<noteq> ps0"
  obtains l r r' B\<^sub>1 B\<^sub>2 where
    "(l,r) \<in> set ps"
    "length r > 2"
    "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')"
    "binarizeNt_fun A ps0 ps = (removeAll (l,r) ps0) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')]"
  using assms proof (induction ps arbitrary: thesis)
  case (Cons p ps)
  obtain l r r' nn_opt where lr_defs: "p = (l,r)" "replaceNts A r = (nn_opt,r')" 
    by fastforce
  consider (hd) "r \<noteq> r' \<and> length r > 2" | (tl) "r = r' \<or> length r < 3"  by fastforce
  then show ?case 
  proof cases
    case hd
    with replaceNts_id_iff_None lr_defs obtain B\<^sub>1 B\<^sub>2 where "nn_opt = Some (B\<^sub>1,B\<^sub>2)"
      by fast
    moreover from this hd have 
      "binarizeNt_fun A ps0 (p#ps) = (removeAll (l,r) ps0) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')]" 
      using lr_defs by auto
    ultimately show ?thesis using Cons(2) lr_defs hd by fastforce
  next
    case tl
    with lr_defs binarizeNt_fun_rec_if_id_or_lt3 
      have "binarizeNt_fun A ps0 (p#ps) = binarizeNt_fun A ps0 ps" by blast
    with Cons show ?thesis using lr_defs by (metis list.set_intros(2))
  qed
qed simp

lemma binarizeNt_fun_binarized:
  assumes 
    "A \<notin> Nts (set ps) \<union> {S}"
    "binarizeNt_fun A ps ps \<noteq> ps"
  obtains B\<^sub>1 B\<^sub>2 where  "binarizeNt A B\<^sub>1 B\<^sub>2 S (set ps) (set (binarizeNt_fun A ps ps))"
proof -
  from binarizeNt_fun_binarizes[OF assms(2)] obtain l r r' B\<^sub>1 B\<^sub>2 where 
  binarize_defs:
    "(l,r) \<in> set ps"
    "length r > 2"
    "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')"
    "binarizeNt_fun A ps ps = (removeAll (l,r) ps) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')]"
    by metis
  moreover from this obtain p s where "r = p@[Nt B\<^sub>1, Nt B\<^sub>2]@s"  "r' = p@[Nt A]@s"
    using replaceNts_replaces_pair by blast
  ultimately have "binarizeNt A B\<^sub>1 B\<^sub>2 S (set ps) (set (binarizeNt_fun A ps ps))" 
    unfolding binarizeNt_def using assms(1) by auto
  then show thesis using that by simp
qed

lemma binarizeNt_fun_dec_badNtsCount:
  assumes "binarizeNt_fun A ps ps \<noteq> ps" 
          "A \<notin> Nts (set ps) \<union> {S}"
  shows "badNtsCount (set (binarizeNt_fun A ps ps)) < badNtsCount (set ps)"
  using lemma6_b assms binarizeNt_fun_binarized 
  by (metis list.set_finite)

(* Needed to prove badNts_impl_binarizeNt_fun_not_id_unif *)

lemma removeAll_app_eq_impl_removed:
  "removeAll z xs @ ys = xs \<Longrightarrow> (\<forall>y\<in>set ys. y = z)"
  by (induction xs) 
    (simp, (metis Compl_iff append_self_conv compl_set insert_code(2) insert_iff removeAll_append
            removeAll_id))


lemma badNts_impl_binarizeNt_fun_not_id_unif:
  assumes "badNtsCount (set ps) = Suc n"
    "uniform (set ps)"
  shows "binarizeNt_fun A ps0 ps \<noteq> ps0"
  using assms proof (induction ps arbitrary: n)
  case (Cons p ps)
  obtain l r where lr_def: "(l,r) = p" using old.prod.exhaust by metis
  consider (no_badNts_hd) "badNtsCount (set [p]) = 0" | 
          (Suc_badNts_hd) m where "badNtsCount (set [p]) = Suc m"
    using not0_implies_Suc by blast
  then show ?case
  proof cases
    case no_badNts_hd
    from Cons(3) have only_Nts: "length r = 1 \<or> (\<forall>s\<in>(set r). \<exists>n. s = Nt n)"
      unfolding uniform_def using lr_def 
      by (metis (no_types, lifting) Cons.prems(2) One_nat_def badTmsCountSet isNt_def le_Suc_eq 
          le_zero_eq length_0_conv length_greater_0_conv length_pos_if_in_set list.set_finite 
          list.set_intros(1) noTms_prodTms0 uniform_badTmsCount)
    have "length r < 3"
    proof (rule ccontr)
      assume "\<not>?thesis"
      hence "length r \<ge> 2" by simp
      moreover with only_Nts have "\<forall>s\<in>set r. \<exists>n. s = Nt n" by presburger
      ultimately have "prodNts p \<noteq> 0" unfolding prodNts_def using lr_def 
        by (metis \<open>\<not> length r < 3\<close> filter_True isNt_def le_imp_less_Suc not_numeral_le_zero numeral_2_eq_2
            numeral_3_eq_3 snd_conv)
      with no_badNts_hd show False by simp
    qed
    with lr_def have "binarizeNt_fun A ps0 (p#ps) = binarizeNt_fun A ps0 ps" 
      using binarizeNt_fun_rec_if_id_or_lt3 by (metis old.prod.exhaust)
    with Cons show ?thesis 
      by (metis (no_types, lifting) badNtsCountSet bot_nat_0.not_eq_extremum gr0_conv_Suc 
          list.set_finite list.set_intros(1,2) no_badNts_hd set_ConsD uniform_def)
  next
    case Suc_badNts_hd
    with lr_def have all_Nts: "length r > 2 \<and> (\<forall>s\<in>set r. \<exists>n. s = Nt n)" using prodNts_def 
      by (metis (no_types, lifting) ext Cons.prems(2) One_nat_def add.commute add_Suc_right
          add_mono_thms_linordered_semiring(1) badNtsCountSet badTmsCountSet empty_iff empty_set isNt_def
          length_Suc_conv linorder_not_less list.set_intros(1) noTms_prodTms0 numeral_2_eq_2 plus_nat.add_0
          set_ConsD snd_conv uniform_badTmsCount zero_le list.set_finite)
    moreover obtain r' B\<^sub>1 B\<^sub>2 where replace_defs: "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')" "r' \<noteq> r"
    proof -
      from all_Nts obtain ns B\<^sub>1 B\<^sub>2 where "r = [Nt B\<^sub>1, Nt B\<^sub>2] @ ns"
        by (metis (no_types, lifting) append_Cons append_Nil le_imp_less_Suc length_Suc_conv 
            linorder_not_less list.exhaust list.set_intros(1,2) list.size(3) not_less_iff_gr_or_eq 
            numeral_2_eq_2)
      thus thesis using that by simp
    qed
    ultimately have "binarizeNt_fun A ps0 (p#ps) = removeAll (l,r) ps0 @ [(A, [Nt B\<^sub>1, Nt B\<^sub>2]), (l,r')]"
                    (is "_ = ?rem")
      using lr_def by fastforce
    also have "... \<noteq> ps0" 
    proof
      assume rem_eq: "... = ps0"
      then obtain xs where "ps0 = xs @ [(A, [Nt B\<^sub>1, Nt B\<^sub>2]), (l,r')]" by metis
      with rem_eq have "(l,r) = (l,r')" using removeAll_app_eq_impl_removed 
        by (metis insert_iff list.set(2))
      with replace_defs show False by blast
    qed
    finally show ?thesis .
  qed
qed simp


lemma binarizeNt_fun_preserves_uniform:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes ps_uniform: "uniform (set ps)"
      and ps'_def: "ps' = binarizeNt_fun A ps ps"
    shows "uniform (set ps')"
proof -
  consider (id) "binarizeNt_fun A ps ps = ps" | (not_id) "binarizeNt_fun A ps ps \<noteq> ps" by blast
  then show ?thesis
  proof cases
    case not_id
    from binarizeNt_fun_binarizes[OF not_id] obtain l r r' B\<^sub>1 B\<^sub>2 where lr_defs:
      "(l,r) \<in> set ps" "length r > 2" "replaceNts A r = (Some (B\<^sub>1,B\<^sub>2), r')" 
      "binarizeNt_fun A ps ps = removeAll (l,r) ps @ [(A,[Nt B\<^sub>1, Nt B\<^sub>2]), (l,r')]" by metis
    moreover from ps_uniform have "uniform (set (removeAll (l,r) ps))"
      unfolding uniform_def by simp
    moreover have "uniform (set [(l,r')])"
    proof -
      from replaceNts_replaces_pair_Some[OF lr_defs(3)] obtain p q where 
        "r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "r' = p@[Nt A]@q" .
      with lr_defs ps_uniform show ?thesis unfolding uniform_def by fastforce
    qed
    ultimately show ?thesis using ps'_def unfolding uniform_def by auto
  qed (use assms in simp)
qed

subsection \<open>binarizeNt_all\<close>

function binarizeNt_all :: "'n::fresh0 \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods" where
  "binarizeNt_all S ps = 
    (let ps' = binarizeNt_fun (freshA ps S) ps ps in
    if ps = ps' then ps else binarizeNt_all S ps')"
  by auto
termination
proof
  let ?R = "measure (\<lambda>(S,ps). badNtsCount (set ps))"
  show "wf ?R" by fast
  fix S :: "'n::fresh0"
  and ps ps' :: "('n,'t) prods"
  let ?A = "freshA ps S"
  assume ps'_def: "ps' = binarizeNt_fun ?A ps ps"
         and neq: "ps \<noteq> ps'"
  moreover with freshA_notin_set have "?A \<notin> Nts (set ps) \<union> {S}" by blast
  ultimately show "((S,ps'),(S,ps)) \<in> ?R" 
    using binarizeNt_fun_dec_badNtsCount by force
qed

lemma binarizeNt_all_binRtc:
  "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* (set ps) (set (binarizeNt_all S ps))"
proof (induction "badNtsCount (set ps)" arbitrary: ps rule: less_induct)
  case less
  let ?A = "freshA ps S"
  have A_notin_nts: "?A \<notin> Nts (set ps) \<union> {S}"
    using freshA_notin_set by metis
  consider (eq) "binarizeNt_fun ?A ps ps = ps" |
           (neq) "binarizeNt_fun ?A ps ps \<noteq> ps" by blast
  then show ?case 
  proof cases
    case neq
    let ?ps' = "binarizeNt_fun ?A ps ps"
    from binarizeNt_fun_dec_badNtsCount[OF neq A_notin_nts] have
      "badNtsCount (set ?ps') < badNtsCount (set ps)" .
    with less have "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* (set ?ps') (set (binarizeNt_all S ?ps'))"
      by blast
    moreover from neq A_notin_nts obtain B\<^sub>1 B\<^sub>2 where "binarizeNt ?A B\<^sub>1 B\<^sub>2 S (set ps) (set ?ps')"
      using binarizeNt_fun_binarized by blast
    ultimately show ?thesis 
      by (smt (verit, best) binarizeNt_all.simps
          converse_rtranclp_into_rtranclp)
  qed simp
qed

section \<open>Conversion to CNF\<close>

lemma binarizeNt_all_preserves_uniform:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes ps_uniform: "uniform (set ps)"
      and ps'_def: "ps' = binarizeNt_all S ps"
    shows "uniform (set ps')"
using assms proof (induction "badNtsCount (set ps)" arbitrary: ps ps' rule: less_induct)
  case less
  let ?A = "freshA ps S"
  consider (rec) "binarizeNt_fun ?A ps ps \<noteq> ps" | (no_rec) "binarizeNt_fun ?A ps ps = ps" by blast
  then show ?case 
  proof cases
    case rec
    let ?ps' = "binarizeNt_fun ?A ps ps"
    from rec have "binarizeNt_all S ps = binarizeNt_all S ?ps'" 
      by (smt (verit) binarizeNt_all.elims)
    with less binarizeNt_fun_dec_badNtsCount[OF rec] freshA_notin_set 
      binarizeNt_fun_preserves_uniform
      show ?thesis by metis
  qed (use less in simp)
qed

lemma binarizeNt_all_preserves_binary:
  assumes binary: "binary (set ps)"
      and ps'_def: "ps' = binarizeNt_all S ps"
    shows "binary (set ps')"
proof -
  from binary have "badNtsCount (set ps) = 0"
    by (metis badNtsCountNot0 binary_def bot_nat_0.not_eq_extremum leD le_imp_less_Suc numeral_2_eq_2
        numeral_3_eq_3 split_conv list.set_finite)
  hence "binarizeNt_all S ps = ps" using binarizeNt_fun_dec_badNtsCount freshA_notin_set 
    by (smt (verit, best) binarizeNt_all.simps bot_nat_0.extremum_strict)
  with assms show ?thesis by argo
qed

lemma binarizeNt_all_binary_if_uniform:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes ts_def: "ts = tm_list_of_prods ps"
      and ps'_def: "ps' = binarizeNt_all S ps"
      and uniform: "uniform (set ps)"
    shows "binary (set ps')"
proof -
  consider (bin) "binary (set ps)" | (not_bin) "\<not>binary (set ps)" by blast
  then show ?thesis
  proof cases
    case bin
    then show ?thesis using ps'_def binarizeNt_all_preserves_binary by blast
  next
    case not_bin
    with uniform binary_badNtsCount obtain n where Suc_badNts: "badNtsCount (set ps) = Suc n" 
      using not0_implies_Suc by blast
    with uniform ps'_def show ?thesis 
    proof (induction "badNtsCount (set ps)" arbitrary: ps ps' n rule: less_induct)
      case less
      let ?A = "freshA ps S"
      from less badNts_impl_binarizeNt_fun_not_id_unif have "binarizeNt_fun ?A ps ps \<noteq> ps"
        by fastforce
      hence badNtsCount_dec: "badNtsCount (set (binarizeNt_fun ?A ps ps)) < badNtsCount (set ps)" 
                              (is "badNtsCount ?ps' < _")
        using freshA_notin_set binarizeNt_fun_dec_badNtsCount by metis
      consider (zero_badNts) "badNtsCount ?ps' = 0" | (Suc_badNts) m where "badNtsCount ?ps' = Suc m"
        using not0_implies_Suc by blast
      then show ?case
      proof cases
        case zero_badNts
        moreover from less.prems(1) binarizeNt_fun_preserves_uniform have "uniform ?ps'" 
          by blast
        ultimately show ?thesis using binary_badNtsCount
          by (smt (verit, ccfv_threshold) List.finite_set binarizeNt_all.elims binarizeNt_all_preserves_binary
              freshA_def less.prems(2))
      next
        case Suc_badNts
        moreover from less.prems(1) binarizeNt_fun_preserves_uniform have unif: "uniform ?ps'"
          by blast
        ultimately show ?thesis using less(1)[OF badNtsCount_dec _ _ Suc_badNts] 
          by (smt (verit, best) binarizeNt_all.simps freshA_def less.prems(2))
      qed
    qed
  qed
qed


theorem cnf_noe_nou_binarizeNt_all_uniformize_all:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes eps_free: "Eps_free (set ps)" 
      and unit_free: "Unit_free (set ps)" 
      and ts_def: "Tms (set ps) \<subseteq> (set ts)"
      and ps'_def: "ps' = (binarizeNt_all S \<circ> uniformize_all S ts) ps"
    shows "uniform (set ps')" "binary (set ps')" "Lang (set ps) S = Lang (set ps') S" 
          "Eps_free (set ps')" "Unit_free (set ps')"
proof (goal_cases uniform binary lang_eq Eps_free Unit_free)
  case uniform
  let ?ps_unif = "uniformize_all S ts ps"
  from uniformize_all_uniform have "uniform (set ?ps_unif)" using ts_def by metis
  with binarizeNt_all_preserves_uniform ps'_def show ?case by auto
next
  case binary
  then show ?case using assms binarizeNt_all_binary_if_uniform using ts_def
    by (metis comp_apply uniformize_all_uniform)
next
  case lang_eq
  then show ?case using assms cnf_lemma binarizeNt_all_binRtc uniformize_all_unifRtc
    by (metis (mono_tags, lifting) comp_apply)
next
  case Eps_free
  let ?ps_unif = "uniformize_all S ts ps"
  from uniformize_all_unifRtc[THEN uniformizeRtc_Eps_free] eps_free have "eps_free ?ps_unif" 
    by blast
   with binarizeNt_all_binRtc binarizeNtRtc_Eps_free show ?case using ps'_def by fastforce
next
  case Unit_free
  let ?ps_unif = "uniformize_all S ts ps"
  from uniformize_all_unifRtc[THEN uniformizeRtc_Unit_free] unit_free have "Unit_free (set ?ps_unif)" 
    by blast
   with binarizeNt_all_binRtc binarizeNtRtc_Unit_free show ?case using ps'_def by fastforce
 qed

lemma unit_elim_o_eps_elim_Tms_subset:
  "Tms (set ((unit_elim \<circ> eps_elim) ps)) \<subseteq> Tms (set ps)"
unfolding comp_def  Unit_elim_set_code[of "eps_elim ps", symmetric] set_eps_elim[of ps]
using Tms_Unit_elim_subset Tms_Eps_elim_subset by fast 

definition cnf_of :: "('n::fresh0, 't) prods \<Rightarrow> 'n \<Rightarrow> ('n,'t) prods" where
  "cnf_of ps S \<equiv> let ts = tms ps in
    (binarizeNt_all S \<circ> uniformize_all S ts \<circ> unit_elim \<circ> eps_elim) ps"

theorem cnf_of_CNF_Lang:
  fixes ps :: "('n::fresh0, 't) prods"
  assumes ps'_def: "ps' = cnf_of ps S"
  shows "CNF (set ps')" "Lang (set ps') S = Lang (set ps) S - {[]}"
proof -
  obtain ps'' where ps''_def: "ps'' = (unit_elim \<circ> eps_elim) ps" by metis
  then have Lang_ps'': "Lang (set ps'') S = Lang (set ps) S - {[]}"
    by (metis lang_unit_elim lang_eps_elim comp_apply)
  from ps''_def have eps: "Eps_free (set ps'')" and unit: "Unit_free (set ps'')"
    by ((metis Unit_elim_correct Unit_elim_set_code comp_apply eps_free_eps_elim
        unit_elim_rel_Eps_free),
        use Unit_free_if_unit_elim_rel ps''_def unit_elim_correct in fastforce)
  let ?ts = "tms ps"
  from unit_elim_o_eps_elim_Tms_subset have subs: "Tms (set ps'') \<subseteq> (set ?ts)" 
    using ps''_def set_tms by metis
  moreover have ps'_eq_comp: "ps' = (binarizeNt_all S \<circ> uniformize_all S ?ts) ps''" 
    unfolding ps''_def ps'_def cnf_of_def by (metis comp_apply)
  ultimately show "Lang (set ps') S = Lang (set ps) S - {[]}"  "CNF (set ps')" 
    using CNF_eq cnf_noe_nou_binarizeNt_all_uniformize_all[OF eps unit subs ps'_eq_comp] 
    Lang_ps'' by auto
qed

lemma "set(cnf_of
 ([(0, [Tm 2, Nt 1]), (0, [Tm 1, Nt 2]),
   (1, [Tm 2, Nt 1, Nt 1]), (1, [Tm 1, Nt 0]), (1, [Tm 1]),
   (2, [Tm 1, Nt 2, Nt 2]), (2, [Tm 2, Nt 0]), (2, [Tm 2])]::(nat,int)prods) 0) =
 {(0, [Nt 6, Nt 1]), (0, [Nt 3, Nt 2]),
  (1, [Nt 4, Nt 0]), (1, [Nt 10, Nt 1]), (1, [Tm 1]),
  (2, [Nt 8, Nt 0]), (2, [Nt 9, Nt 2]), (2, [Tm 2]),
  (3, [Tm 1]), (4, [Tm 1]), (5, [Tm 1]), (6, [Tm 2]), (7, [Tm 2]), (8, [Tm 2]),
  (9, [Nt 5, Nt 2]), (10, [Nt 7, Nt 1])}"
  by eval

end
