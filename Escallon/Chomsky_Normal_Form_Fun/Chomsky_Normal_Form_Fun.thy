theory Chomsky_Normal_Form_Fun
  imports Context_Free_Grammar.Chomsky_Normal_Form
begin

definition uniformize' :: "['n::infinite, ('n,'t) prods, ('n,'t) prods] \<Rightarrow> bool" where
  "uniformize' S ps ps' \<equiv> \<exists>A t. uniformize A t S ps ps'"

fun tm_list_of_prods :: "('n,'t) prods \<Rightarrow> 't list" where
  "tm_list_of_prods ps = 
    (let rs = map snd ps in map destTm (filter isTm (concat rs)))"

lemma tm_list_of_prods_is_tms:
  "tm \<in> set (tm_list_of_prods ps) \<longleftrightarrow> tm \<in> tms ps"
proof -
  have "tm \<in> set (tm_list_of_prods ps) = 
    (tm \<in> set (map destTm (filter isTm (concat (map snd ps)))))"
    by force
  also have "... = (Tm tm \<in> set (filter isTm (concat (map snd ps))))" 
    using destTm_o_Tm
    by (smt (verit, best) destTm.simps filter_set in_set_conv_nth isTm_def length_map member_filter
        nth_map nth_mem)
  also have "... = (tm \<in> (\<Union>(A,w)\<in>(set ps). tms_syms w))"
    using tms_syms_def by fastforce
  also have "... = (tm \<in> tms ps)" unfolding Tms_def by blast
  finally show ?thesis .
qed

fun replace_tm :: "['n, ('n,'t) syms] \<Rightarrow> 't option \<times> ('n,'t) syms" where
  "replace_tm A [] = (None, [])" |
  "replace_tm A (s#sms) = (case s of 
    Tm t \<Rightarrow> (Some t, Nt A # sms) | 
    Nt _ \<Rightarrow> (let (t_opt,sms') = replace_tm A sms in 
            (t_opt,s#sms')))"


lemma replace_tm_length_unchanged[simp]: 
  "replace_tm A sms = (t,sms') \<Longrightarrow> length sms' = length sms"
  by (induction sms arbitrary: sms')(auto split: sym.splits prod.splits)

  

lemma replace_tm_id_iff_tm_notin_syms:
  assumes "replace_tm A sms = (t_opt,sms')"
  shows "(\<forall>t. Tm t \<notin> set sms) \<longleftrightarrow> sms = sms'"
  using assms by (induction sms arbitrary: sms') (auto split: sym.splits prod.splits)


(*Proofs break with iff lemma. Fix?*)
lemma tm_notin_syms_impl_replace_tm_id:
  assumes "\<forall>t. Tm t \<notin> set sms" 
          "replace_tm A sms = (t_opt,sms')"
  shows "sms = sms'"
  using assms replace_tm_id_iff_tm_notin_syms by fast
lemma replace_tm_id_impl_no_tms:
  assumes "replace_tm A sms = (t_opt,sms)" 
  shows "\<forall>t. Tm t \<notin> set sms"
  using assms replace_tm_id_iff_tm_notin_syms by fast

lemma replace_tm_none_iff_id:
  "replace_tm A sms = (t_opt,sms') \<Longrightarrow> t_opt = None \<longleftrightarrow> sms = sms'"
  by (induction sms arbitrary: sms')(auto split: sym.splits prod.splits)

corollary no_tms_impl_id:
  assumes "\<forall>t. Tm t \<notin> set sms"
  shows "replace_tm A sms = (None,sms)"
  using assms tm_notin_syms_impl_replace_tm_id replace_tm_none_iff_id 
  by (metis old.prod.exhaust)

lemma replace_tm_not_id_impl_some:
  assumes "replace_tm A sms = (t_opt,sms')"
          "sms \<noteq> sms'"
        obtains t where "t_opt = Some t"
  using assms replace_tm_none_iff_id option.exhaust by metis

lemma replace_tm_some_impl_not_id:
  assumes "replace_tm A sms = (Some t,sms')"
  shows "sms \<noteq> sms'"
  using assms by (induction sms arbitrary: sms') (auto split: sym.splits prod.splits)

(*Strengthen with "Tm t \<notin> set p?*)
lemma replace_tm_replaces_single:
  assumes "replace_tm A sms = (Some t,sms')"
  obtains p s t where "sms = p@[Tm t]@s"
                    "sms' = p@[Nt A]@s"
using assms proof (induction sms arbitrary: thesis sms' t)
  case (Cons s sms)
  consider (tm) "\<exists>t. s = Tm t" | (nt) "\<forall>t. s \<noteq> Tm t" by blast
  then show ?case 
  proof cases
    case tm
    then obtain p q t where "s = Tm t" "s#sms = p@[Tm t]@q" "p = []" by auto
    moreover from this(1) Cons(3) have "sms' = Nt A#sms" by simp
    ultimately show thesis using Cons(2) by fastforce
  next
    case nt
    with Cons(3) obtain t sms'' where sms''_def: "replace_tm A sms = (Some t,sms'')" 
      using  replace_tm_not_id_impl_some
      by (metis old.prod.exhaust replace_tm_id_iff_tm_notin_syms replace_tm_some_impl_not_id
          set_ConsD)
    with Cons(1)  
    obtain p q t' where pq_defs: "sms = p@[Tm t']@q" "sms'' = p@[Nt A]@q" 
      by metis
    with nt obtain n where "s = Nt n" using sym.exhaust by meson
    with pq_defs(2) Cons(3) sms''_def have "sms' = (s#p)@[Nt A]@q" by simp
    then show ?thesis using Cons(2,3) pq_defs by (metis Cons_eq_appendI)
  qed
qed simp


(*The current implementation corresponds to uniformize as defined in 
  Context_Free_Grammar.Chomsky_Normal_Form. This can be simplified with maps.*)
fun uniformize_fun :: "['n::infinite, ('n,'t) prods, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_fun S ps0 [] = ps0" |
  "uniformize_fun S ps0 ((l,r) # ps) = 
    (let A = fresh (nts ps0 \<union> {S}) in case replace_tm A r of
    (None,_) \<Rightarrow> uniformize_fun S ps0 ps |
    (Some t, r') \<Rightarrow> if length r < 2 then uniformize_fun S ps0 ps
      else (removeAll (l,r) ps0) @ [(A, [Tm t]), (l,r')])"

lemma uniformize_fun_id:
  "\<forall>(l,r)\<in>set ps. (\<forall>t. Tm t \<notin> set r) \<or> length r < 2 \<Longrightarrow> uniformize_fun S ps0 ps = ps0"
proof (induction ps)
  case (Cons p ps)
  have "uniformize_fun S ps0 (p#ps) = uniformize_fun S ps0 ps" 
  proof -
    let ?A = "fresh (nts ps0 \<union> {S})"
    obtain l r where p_def: "p = (l,r)" by fastforce
    with Cons(2) consider (tm_free) "\<forall>t. Tm t \<notin> set r" | (len_ub) "length r < 2" by auto
    then show ?thesis 
    proof cases
      case tm_free
      then have "replace_tm ?A r = (None,r)" 
        using no_tms_impl_id by metis
      then show ?thesis using p_def by simp
    next
      case len_ub
      consider r'   where "replace_tm ?A r = (None,r')" | 
               t r' where "replace_tm ?A r = (Some t,r')"
        using option.exhaust by (metis old.prod.exhaust)
      then show ?thesis by cases (use len_ub p_def in auto)
    qed
  qed
  then show ?case using Cons by simp
qed (fastforce split: prod.splits)

lemma len_lt_2_impl_uniformize_fun_rec:
  assumes "length r < 2"
  shows "uniformize_fun S ps0 ((l,r)#ps) = uniformize_fun S ps0 ps"
proof -
  let ?A = "fresh (nts ps0 \<union> {S})"
  consider r' where   "replace_tm ?A r = (None,r')" |
           r' t where "replace_tm ?A r = (Some t,r')"
    using option.exhaust old.prod.exhaust by metis
   then show ?thesis by cases (use assms in auto)
qed
  

lemma uniformize_fun_uniform_prepend:
   "\<forall>(l,r)\<in>set xs. (\<forall>t. Tm t \<notin> set r) \<or> length r < 2 \<Longrightarrow>
    uniformize_fun S ps0 (xs@ps) = uniformize_fun S ps0 ps"
proof (induction xs)
  case (Cons x xs)
  then obtain l r where lr_def: "x = (l,r)" by auto
  hence "uniformize_fun S ps0 ((x#xs)@ps) = uniformize_fun S ps0 ((l,r)#xs@ps)" by simp
  also have "... = uniformize_fun S ps0 (xs@ps)"
  proof -
    let ?A = "fresh (nts ps0 \<union> {S})"
    from Cons(2) lr_def have "(\<forall>t. Tm t \<notin> set r) \<or> length r < 2" by simp
    hence "replace_tm ?A r = (None,r) \<or> length r < 2" using no_tms_impl_id by fast 
    then consider (id) "replace_tm ?A r = (None,r)" | (len_ub) "length r < 2" by blast
    thus ?thesis by cases (fastforce split: prod.splits,
                           use len_lt_2_impl_uniformize_fun_rec in simp)
  qed
  also have "... = uniformize_fun S ps0 ps" using Cons by simp
  finally show ?case .
qed simp

lemma uniformize_fun_ps0_uniform_app:
  assumes "\<forall>(l,r)\<in>set xs. Tm t \<notin> set r \<or> length r < 2"
  shows "uniformize_fun S (xs@ys) ps = xs @ uniformize_fun S ys ps"
proof (induction ps)
  case (Cons p ps)
  then obtain l r where lr_def: "p = (l,r)" 
    by fastforce
  then consider (not_unif) "Tm t \<in> set r \<and> length r \<ge> 2" | (unif) "Tm t \<notin> set r \<or> length r < 2"
    by linarith
  then show ?case 
  proof cases
    case not_unif
    with assms(1) lr_def have p_notin_xs: "p \<notin> set xs" by auto
    let ?A = "fresh (nts (xs@ys) \<union> {S})"
    from not_unif lr_def have "uniformize_fun S (xs@ys) (p#ps) 
                      = removeAll p (xs@ys) @ [(?A, [Tm t]), (l,replace_tm ?A r)]" 
      by (smt (verit) replace_tm_id_iff_tm_notin_syms uniformize_fun.simps(2)
          verit_comp_simplify1(3))
    also have "... = xs @ removeAll p ys @ [(A, [Tm t]), (l,replace_tm A t r)]"
      using p_notin_xs by simp
    also have "... = xs @ uniformize_fun A t ys (p#ps)" using not_unif 
      by (smt (verit) lr_def replace_tm_id_impl_no_tms
          uniformize_fun.simps(2) verit_comp_simplify1(3))
    finally show ?thesis .
  next
    case unif
    hence unif_ite: "replace_tm A t r = r \<or> length r < 2" using tm_notin_syms_impl_replace_tm_id 
      by fast
    with lr_def have "uniformize_fun S (xs@ys) (p#ps) = uniformize_fun S (xs@ys) ps" 
      by fastforce
    also have "... = xs @ uniformize_fun S ys ps" using Cons .
    also have "... = xs @ uniformize_fun S ys (p#ps)" using unif_ite lr_def by fastforce
    finally show ?thesis .
  qed
qed simp
  

lemma uniformize_fun_neq_ps0_impl_uniformized:
  assumes "uniformize_fun A t ps0 ps \<noteq> ps0"
  obtains l r q s where "(l,r) \<in> set ps"
                    "r \<noteq> replace_tm A t r"
                    "length r \<ge> 2"
                    "ps = q@[(l,r)]@s"
                    "\<forall>(l,r)\<in>set q. length r < 2 \<or> Tm t \<notin> set r"
using assms proof (induction ps arbitrary: thesis)
  case (Cons p ps)
  obtain l0 r0 where lr0_def: "p = (l0,r0)" by fastforce
  consider (not_fst) "length r0 < 2 \<or> Tm t \<notin> set r0" | (fst) "length r0 \<ge> 2 \<and> Tm t \<in> set r0" 
    by linarith
  then show ?case 
  proof cases
    case not_fst
    hence "uniformize_fun A t ps0 (p#ps) = uniformize_fun A t ps0 ps"
      using lr0_def tm_notin_syms_impl_replace_tm_id by fastforce
    then obtain l r q s where lrqs_defs: 
                              "(l,r) \<in> set ps"
                              "r \<noteq> replace_tm A t r"
                              "length r \<ge> 2"
                              "ps = q@[(l,r)]@s"
                              "\<forall>(l,r)\<in>set q. length r < 2 \<or> Tm t \<notin> set r"
      using Cons(1,3) by (metis (lifting))
    moreover from this not_fst lr0_def have 
                               "(l,r) \<in> set (p#ps)" "p#ps = (p#q)@[(l,r)]@s"
                               "\<forall>(l,r)\<in> set (p#q). length r < 2 \<or> Tm t \<notin> set r"
      by simp+
    ultimately show ?thesis using Cons(2) by blast
  next
    case fst
    hence "r0 \<noteq> replace_tm A t r0" find_theorems name:replace_tm
      using replace_tm_id_impl_no_tms by metis
    with fst lr0_def show ?thesis using Cons(2)[of _ _ "[]"] by simp
  qed
qed simp

lemma uniformize_fun_uniformizes_fst:
  assumes "(l,r) \<in> set ps"
          "r \<noteq> replace_tm A t r"
          "ps = q@[(l,r)]@s"
          "\<forall>(l,r)\<in>set q. Tm t \<notin> set r \<or> length r < 2"
          "length r \<ge> 2"
          "A = fresh P"
          "nts ps \<subseteq> P"
        shows
    "uniformize_fun A t ps ps = ((removeAll (l,r) ps) @ [(A, [Tm t]), (l, replace_tm A t r)])" 
proof -
  from assms(3,4) uniformize_fun_ps0_uniform_app 
      uniformize_fun_uniform_prepend have
    "uniformize_fun A t ps ps = q @ uniformize_fun A t ([(l,r)]@s) ([(l,r)]@s)" by fastforce
  also have "... = q @ (removeAll (l,r) ([(l,r)]@s)) @ [(A, [Tm t]), (l, replace_tm A t r)]"
    using assms(2,5) by fastforce
  also have "... = removeAll (l,r) ps @ [(A, [Tm t]), (l, replace_tm A t r)]"
  proof -
    have "(l,r) \<notin> set q" 
      using assms(2,4,5) tm_notin_syms_impl_replace_tm_id by fastforce 
    thus ?thesis using assms(3) by simp
  qed
  finally show ?thesis .
qed

lemma uniformize_fun_is_uniformized:
  assumes "uniformize_fun S ps ps \<noteq> ps"
  shows "uniformize S ps (uniformize_fun S ps ps)"
proof -
  from assms obtain l r q s  where lr_in_ps: "(l,r) \<in> set ps"
                          and replace_neq: "r \<noteq> replace_tm A t r"
                          and len_lb: "length r \<ge> 2"
                          and ps_qs: "ps = q@[(l,r)]@s"
                          and q_uniform: "\<forall>(l,r)\<in>set q. length r < 2 \<or> Tm t \<notin> set r"
    using uniformize_fun_neq_ps0_impl_uniformized 
    by (smt (verit, del_insts) case_prodI2 case_prod_conv)
  moreover obtain p s' where "r = p@[Tm t]@s'"
                        and replace_eq_p_Nt_s: "replace_tm A t r = p@[Nt A]@s'"
                        and "p \<noteq> [] \<or> s' \<noteq> []"
  proof -
    from replace_tm_replaces_single replace_neq obtain p s' where
      "r = p@[Tm t]@s'"
      "replace_tm A t r = p@[Nt A]@s'"
      by metis
    with len_lb show thesis using that by fastforce
  qed
  moreover have "uniformize_fun A t ps ps = removeAll (l,r) ps @ [(A, [Tm t]), (l, p @ [Nt A] @ s')]" 
    using uniformize_fun_uniformizes_fst[OF lr_in_ps replace_neq ps_qs _ len_lb assms(2)] 
    replace_eq_p_Nt_s q_uniform by auto
  ultimately show ?thesis
    unfolding uniformize_def using assms by blast
qed



fun uniformize_each :: "['n, 't, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_each A t ps = 
    (let ps' = uniformize_fun A t ps ps in
      if ps' = ps then ps else uniformize_each A t ps')"
termination
proof        
  let ?R = "measure (\<lambda>(A,t,ps). sum_list (map (\<lambda>xs. count_list xs (Tm t)) (map snd ps)))"
  have "wf ?R" ..
  fix A :: 'n
  have "(A,t,ps) \<in> ?R"
        

lemma "(\<lambda>x y. \<exists>A t. uniformize A t S x y)^** ps (uniformize_rt A t ps ps)" (*TODO*)
  sorry

end