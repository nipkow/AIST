theory Chomsky_Normal_Form_Fun
  imports Chomsky_Normal_Form
begin



fun replaceTm :: "['n, 't, ('n,'t) syms] \<Rightarrow> ('n,'t) syms" where
  "replaceTm A t [] = []" |
  "replaceTm A t (s # ss) = (if s = Tm t then Nt A # ss else s # replaceTm A t ss)"

lemma replaceTm_length_unchanged[simp]: 
  "length (replaceTm A t ss) = length ss"
  by (induction ss) auto
  

lemma replaceTm_id_iff_tm_notin_syms:
  shows "Tm t \<notin> set ss \<longleftrightarrow> replaceTm A t ss = ss"
  by (induction ss) auto

(*Proofs break with iff lemma. Fix?*)
lemma tm_notin_syms_impl_replaceTm_id:
  assumes "Tm t \<notin> set ss" 
  shows "replaceTm A t ss = ss"
  using assms replaceTm_id_iff_tm_notin_syms by fast
lemma replaceTm_id_impl_tm_notin_syms:
  assumes "replaceTm A t ss = ss"
  shows "Tm t \<notin> set ss"
  using assms replaceTm_id_iff_tm_notin_syms by fast

(*Strengthen with "Tm t \<notin> set p?*)
lemma replaceTm_replaces_single:
  assumes "replaceTm A t ss \<noteq> ss"
  obtains p s where "ss = p@[Tm t]@s"
                    "replaceTm A t ss = p@[Nt A]@s"
using assms proof (induction ss arbitrary: thesis)
  case (Cons s ss)
  from Cons(3) have t_in_syms: "Tm t \<in> set (s#ss)" using replaceTm_id_iff_tm_notin_syms by fast
  consider (eq) "s = Tm t" | (neq) "s \<noteq> Tm t" by blast
  then show ?case 
  proof cases
    case eq
    then obtain p q where "s#ss = p@[Tm t]@q" "p = []" by auto
    moreover from eq have "replaceTm A t (s#ss) = Nt A#ss" by simp
    ultimately show thesis using Cons(2) by fastforce
  next
    case neq
    with t_in_syms have "Tm t \<in> set ss" 
      by simp
    with Cons(1) replaceTm_id_iff_tm_notin_syms 
    obtain p q where pq_defs: "ss = p@[Tm t]@q" "replaceTm A t ss = p@[Nt A]@q" by metis
    with neq have "replaceTm A t (s#ss) = (s#p)@[Nt A]@q" by auto
    then show ?thesis using Cons(2) pq_defs by (meson Cons_eq_appendI)
  qed
qed simp

lemma replaceTm_tms_changed:
  assumes "t \<in> tms [(l,r)]"
  shows "tms [(l,r)] = tms [(l,(replaceTm A t r))] \<union> {t}"
proof -
  from assms replaceTm_id_iff_tm_notin_syms have "replaceTm A t r \<noteq> r"
    unfolding Tms_def tms_syms_def by fastforce
  with replaceTm_replaces_single obtain p s where "r = p@[Tm t]@s" "replaceTm A t r = p@[Nt A]@s"
    by meson
  then show ?thesis using replaceTm_replaces_single unfolding Tms_def tms_syms_def by auto
qed


(*The current implementation corresponds to uniformize as defined in 
  Context_Free_Grammar.Chomsky_Normal_Form. This can be simplified with maps.*)
fun uniformize_fun :: "['n::infinite, 't, ('n,'t) prods, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_fun _ _ ps0 [] = ps0" |
  "uniformize_fun A t ps0 ((l,r) # ps) = 
    (let r' = replaceTm A t r in 
      if r = r' \<or> length r < 2 then uniformize_fun A t ps0 ps
      else (removeAll (l,r) ps0) @ [(A, [Tm t]), (l,r')])"

lemma uniformize_fun_id:
  "\<forall>(l,r)\<in>set ps. Tm t \<notin> set r \<or> length r < 2 \<Longrightarrow> uniformize_fun A t ps0 ps = ps0"
  using tm_notin_syms_impl_replaceTm_id by (induction ps) fastforce+

lemma uniformize_fun_id_conv:
  "uniformize_fun A t ps0 ps = ps0 \<Longrightarrow> \<forall>(l,r)\<in>set ps. Tm t \<notin> set r \<or> length r < 2"
proof (induction ps)
  case (Cons p ps)
  obtain l r where lr_def: "(l,r) = p" using old.prod.exhaust by metis
  moreover have "Tm t \<notin> set r \<or> length r < 2"
  proof (rule ccontr)
    let ?r' = "replaceTm A t r"
    assume "\<not>?thesis"
    hence "\<not>(?r' = r \<or> length r < 2)" using replaceTm_id_impl_tm_notin_syms by fast
    with lr_def have "uniformize_fun A t ps0 (p#ps) = (removeAll (l,r) ps0) @ [(A, [Tm t]), (l,?r')]" 
      by auto
    then show False 
      by (smt (verit) Cons.prems Diff_iff \<open>\<not> (replaceTm A t r = r \<or> length r < 2)\<close> 
          insert_iff list.distinct(1) prod.inject removeAll.simps(2) removeAll_append 
          removeAll_id self_append_conv set_removeAll)
  qed
  moreover from this lr_def have "uniformize_fun A t ps0 (p#ps) = uniformize_fun A t ps0 ps" 
    using tm_notin_syms_impl_replaceTm_id by fastforce
  ultimately show ?case using Cons by auto
qed simp

lemma uniformize_fun_uniform_prepend:
   "\<forall>(l,r)\<in>set xs. Tm t \<notin> set r \<or> length r < 2 \<Longrightarrow>
    uniformize_fun A t ps0 (xs@ps) = uniformize_fun A t ps0 ps"
proof (induction xs)
  case (Cons x xs)
  then obtain l r where lr_def: "x = (l,r)" by auto
  hence "uniformize_fun A t ps0 ((x#xs)@ps) = uniformize_fun A t ps0 ((l,r)#xs@ps)" by simp
  also have "... = uniformize_fun A t ps0 (xs@ps)"
  proof -
    from Cons(2) lr_def have "Tm t \<notin> set r \<or> length r < 2" by simp
    hence "replaceTm A t r = r \<or> length r < 2" using tm_notin_syms_impl_replaceTm_id by fast
    thus ?thesis by auto
  qed
  also have "... = uniformize_fun A t ps0 ps" using Cons by simp
  finally show ?case .
qed simp

lemma uniformize_fun_ps0_uniform_app:
  assumes "\<forall>(l,r)\<in>set xs. Tm t \<notin> set r \<or> length r < 2"
  shows "uniformize_fun A t (xs@ys) ps = xs @ uniformize_fun A t ys ps"
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
    from not_unif lr_def have "uniformize_fun A t (xs@ys) (p#ps) 
                      = removeAll p (xs@ys) @ [(A, [Tm t]), (l,replaceTm A t r)]" 
      by (smt (verit) replaceTm_id_iff_tm_notin_syms uniformize_fun.simps(2)
          verit_comp_simplify1(3))
    also have "... = xs @ removeAll p ys @ [(A, [Tm t]), (l,replaceTm A t r)]"
      using p_notin_xs by simp
    also have "... = xs @ uniformize_fun A t ys (p#ps)" using not_unif 
      by (smt (verit) lr_def replaceTm_id_impl_tm_notin_syms
          uniformize_fun.simps(2) verit_comp_simplify1(3))
    finally show ?thesis .
  next
    case unif
    hence unif_ite: "replaceTm A t r = r \<or> length r < 2" using tm_notin_syms_impl_replaceTm_id 
      by fast
    with lr_def have "uniformize_fun A t (xs@ys) (p#ps) = uniformize_fun A t (xs@ys) ps" 
      by fastforce
    also have "... = xs @ uniformize_fun A t ys ps" using Cons .
    also have "... = xs @ uniformize_fun A t ys (p#ps)" using unif_ite lr_def by fastforce
    finally show ?thesis .
  qed
qed simp
  

lemma uniformize_fun_neq_ps0_impl_uniformized:
  assumes "uniformize_fun A t ps0 ps \<noteq> ps0"
  obtains l r q s where "(l,r) \<in> set ps"
                    "r \<noteq> replaceTm A t r"
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
      using lr0_def tm_notin_syms_impl_replaceTm_id by fastforce
    then obtain l r q s where lrqs_defs: 
                              "(l,r) \<in> set ps"
                              "r \<noteq> replaceTm A t r"
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
    hence "r0 \<noteq> replaceTm A t r0" find_theorems name:replaceTm
      using replaceTm_id_impl_tm_notin_syms by metis
    with fst lr0_def show ?thesis using Cons(2)[of _ _ "[]"] by simp
  qed
qed simp

lemma uniformize_fun_uniformizes_fst:
  assumes "(l,r) \<in> set ps"
          "r \<noteq> replaceTm A t r"
          "ps = q@[(l,r)]@s"
          "\<forall>(l,r)\<in>set q. Tm t \<notin> set r \<or> length r < 2"
          "length r \<ge> 2"
        shows
    "uniformize_fun A t ps ps = (removeAll (l,r) ps) @ [(A, [Tm t]), (l, replaceTm A t r)]" 
proof -
  from assms(3,4) uniformize_fun_ps0_uniform_app 
      uniformize_fun_uniform_prepend have
    "uniformize_fun A t ps ps = q @ uniformize_fun A t ([(l,r)]@s) ([(l,r)]@s)" by fastforce
  also have "... = q @ (removeAll (l,r) ([(l,r)]@s)) @ [(A, [Tm t]), (l, replaceTm A t r)]"
    using assms(2,5) by fastforce
  also have "... = removeAll (l,r) ps @ [(A, [Tm t]), (l, replaceTm A t r)]"
  proof -
    have "(l,r) \<notin> set q" 
      using assms(2,4,5) tm_notin_syms_impl_replaceTm_id by fastforce 
    thus ?thesis using assms(3) by simp
  qed
  finally show ?thesis .
qed

lemma uniformize_fun_uniformized:
  assumes "uniformize_fun A t ps ps \<noteq> ps"
          "A \<notin> (nts ps \<union> {S})"
  shows "uniformize A t S ps (uniformize_fun A t ps ps)"
proof -
  from assms obtain l r q s  where lr_in_ps: "(l,r) \<in> set ps"
                          and replace_neq: "r \<noteq> replaceTm A t r"
                          and len_lb: "length r \<ge> 2"
                          and ps_qs: "ps = q@[(l,r)]@s"
                          and q_uniform: "\<forall>(l,r)\<in>set q. length r < 2 \<or> Tm t \<notin> set r"
    using uniformize_fun_neq_ps0_impl_uniformized 
    by (smt (verit, del_insts) case_prodI2 case_prod_conv)
  moreover obtain p s' where "r = p@[Tm t]@s'"
                        and replace_eq_p_Nt_s: "replaceTm A t r = p@[Nt A]@s'"
                        and "p \<noteq> [] \<or> s' \<noteq> []"
  proof -
    from replaceTm_replaces_single replace_neq obtain p s' where
      "r = p@[Tm t]@s'"
      "replaceTm A t r = p@[Nt A]@s'"
      by metis
    with len_lb show thesis using that by fastforce
  qed
  moreover have "uniformize_fun A t ps ps = removeAll (l,r) ps @ [(A, [Tm t]), (l, p @ [Nt A] @ s')]" 
    using uniformize_fun_uniformizes_fst[OF lr_in_ps replace_neq ps_qs _ len_lb] 
    replace_eq_p_Nt_s q_uniform by auto
  ultimately show ?thesis
    unfolding uniformize_def using assms by blast
qed

lemma uniformize_fun_dec_badTmsCount:
  assumes "uniformize_fun A t ps ps \<noteq> ps"
          "A \<notin> nts ps \<union> {S}"
  shows "badTmsCount (uniformize_fun A t ps ps) < badTmsCount ps"
  using assms uniformize_fun_uniformized lemma6_a by fast

lemma uniformize_fun_unchanged_tms:
  "set ps \<subseteq> set ps0 \<Longrightarrow> tms ps0 = tms (uniformize_fun A t ps0 ps)"
proof (induction ps)
  case (Cons p ps)
  then obtain l r where lr_def: "(l,r) = p" using old.prod.exhaust by metis
  let ?r' = "replaceTm A t r"
  consider (rec) "r = ?r' \<or> length r < 2" | (no_rec) "r \<noteq> ?r' \<and> length r \<ge> 2" by linarith
  then show ?case 
  proof cases
    case rec
    then show ?thesis using Cons lr_def by force
  next
    case no_rec
    with lr_def have "uniformize_fun A t ps0 (p#ps) = (removeAll (l,r) ps0) @ [(A,[Tm t]),(l,?r')]" 
      by fastforce
    moreover with replaceTm_tms_changed lr_def 
    have "tms [(A,[Tm t]),(l,?r')] = tms [(l,r)]"
    proof -
      from no_rec have "t \<in> tms [(l,r)]" unfolding Tms_def tms_syms_def 
        using tm_notin_syms_impl_replaceTm_id by fastforce
      then show ?thesis using replaceTm_tms_changed unfolding Tms_def tms_syms_def by fastforce
    qed
    moreover have "tms [(l,r)] \<subseteq> tms ps0" using Cons(2) lr_def 
      unfolding Tms_def tms_syms_def by auto
    ultimately show ?thesis unfolding Tms_def tms_syms_def by auto
  qed
qed simp

lemma uniformize_fun_no_new_badTms:
  assumes "\<forall>p\<in>set ps0. Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1"
  shows "\<lbrakk>ps' = uniformize_fun A t ps0 ps; set ps \<subseteq> set ps0\<rbrakk> 
          \<Longrightarrow> \<forall>p\<in>set ps'. Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1"
proof (induction ps arbitrary: ps')
  case (Cons p ps)
  obtain l r where lr_def: "(l,r) = p" using old.prod.exhaust by metis
  let ?r' = "replaceTm A t r" 
  consider (rec) "?r' = r \<or> length r < 2" | (no_rec) "?r' \<noteq> r \<and> length r \<ge> 2" 
    by linarith
  then show ?case 
  proof cases
    case no_rec
    hence "ps' = (removeAll (l,r) ps0) @ [(A, [Tm t]), (l, ?r')]" 
      using lr_def Cons(2) by fastforce
    moreover from assms have "\<forall>p\<in>set (removeAll (l,r) ps0). Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1" 
      by simp
    moreover have "\<forall>p\<in>set ([(A,[Tm t]),(l,?r')]). Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1"
    proof -
      from replaceTm_replaces_single obtain u s where "r = s@[Tm t]@u" "?r' = s@[Nt A]@u" 
        using no_rec by meson
      with assms Cons(3) lr_def show ?thesis by fastforce
    qed
    ultimately show ?thesis by auto
  qed (use Cons lr_def in auto)
qed (use assms in auto)

(* This special case of fresh is repeatedly used in multiple lemmas and functions. This lemma
simplifies or avoids several sledgehammer calls *)
lemma fresh_Nt_notin_set:
  fixes A :: "'n::infinite"
  assumes "A = fresh (nts ps \<union> {S})"
  shows "A \<notin> nts ps \<union> {S}" using fresh_finite 
  by (metis assms finite.emptyI finite_Un finite_insert finite_nts)

function uniformize_tm :: "['n::infinite, 't, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_tm S t ps = 
    (let ps' = uniformize_fun (fresh (nts ps \<union> {S})) t ps ps in 
        if ps = ps' then ps else uniformize_tm S t ps')"
  by auto
termination
proof 
  let ?R = "measure (\<lambda>(S,t,ps). badTmsCount ps)"
  show "wf ?R" ..
  fix S :: "'n::infinite" 
    and t :: 't 
    and x ps :: "('n,'t) prods" 
  let ?A = "fresh (nts ps \<union> {S})"
  assume "x = uniformize_fun ?A t ps ps"
         "ps \<noteq> x"
  moreover have "?A \<notin>  nts ps \<union> {S}"  using fresh_Nt_notin_set by auto
  ultimately show "((S,t,x), S,t,ps) \<in> ?R"
    using uniformize_fun_dec_badTmsCount by force 
qed

lemma uniformize_tm_unchanged_tms:
  "tms ps = tms (uniformize_tm S t ps)"
  by (induction "badTmsCount ps" arbitrary: ps rule: less_induct)
    (smt (verit, ccfv_SIG) fresh_Nt_notin_set dual_order.refl uniformize_fun_dec_badTmsCount 
      uniformize_fun_unchanged_tms uniformize_tm.elims)

lemma uniformize_tm_no_bad_t:
  "ps' = uniformize_tm S t ps \<Longrightarrow> \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
proof (induction "badTmsCount ps" arbitrary: ps ps' rule: less_induct)
  case less
  let ?A = "fresh (nts ps \<union> {S})"
  consider (id) "uniformize_fun ?A t ps ps = ps" | (not_id) "uniformize_fun ?A t ps ps \<noteq> ps"
    by blast
  then show ?case 
  proof cases
    case id
    then show ?thesis using less(2) uniformize_fun_id_conv by fastforce
  next
    case not_id
    hence "uniformize_tm S t ps = uniformize_tm S t (uniformize_fun ?A t ps ps)" 
            (is "_ = uniformize_tm _ _ ?ps'")
      by (smt (verit, best) uniformize_tm.simps)
    moreover with uniformize_fun_dec_badTmsCount[OF not_id] have "badTmsCount ?ps' < badTmsCount ps"
      using fresh_Nt_notin_set by blast
    ultimately show ?thesis using less by blast
  qed
qed
  

lemma uniformize_tm_no_new_badTms:
  assumes "ps' = uniformize_tm S t ps"
    "\<forall>p\<in>set ps. Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1"
  shows "\<forall>p\<in>set ps'. Tm t' \<notin> set (snd p) \<or> length (snd p) \<le> 1"
  using assms proof (induction "badTmsCount ps" arbitrary: ps ps' rule: less_induct)
  case less
  let ?A = "fresh (nts ps \<union> {S})"
  consider (id) "uniformize_fun ?A t ps ps = ps" | (not_id) "uniformize_fun ?A t ps ps \<noteq> ps" 
    by blast
  then show ?case 
  proof cases
    case not_id
    let ?ps' = "uniformize_fun ?A t ps ps"
    from not_id have "uniformize_tm S t ps = uniformize_tm S t ?ps'" 
      by (smt (verit, ccfv_threshold) uniformize_tm.simps) 
    moreover from uniformize_fun_dec_badTmsCount[OF not_id] have 
      "badTmsCount ?ps' < badTmsCount ps" using fresh_Nt_notin_set by blast
    ultimately show ?thesis using uniformize_fun_no_new_badTms less by fast
  qed (use less in auto)
qed
              
lemma uniformize_tm_unifRtc:
  "(\<lambda>x y. \<exists>A. uniformize A t S x y)\<^sup>*\<^sup>* ps (uniformize_tm S t ps)"
proof (induction "badTmsCount ps" arbitrary: ps rule: less_induct)
  case less
  let ?A = "fresh (nts ps \<union> {S})"
  consider (eq) "uniformize_fun ?A t ps ps = ps" |
           (neq) "uniformize_fun ?A t ps ps \<noteq> ps" by blast
  then show ?case 
  proof cases
    case neq
    let ?ps' = "uniformize_fun ?A t ps ps"
    from neq have "badTmsCount ?ps' < badTmsCount ps"
      using uniformize_fun_dec_badTmsCount fresh_Nt_notin_set by fast
    with less have uniformize_rtrancl: 
      "(\<lambda>x y. \<exists>A. uniformize A t S x y)\<^sup>*\<^sup>* ?ps' (uniformize_tm S t ?ps')" by simp
    moreover have "uniformize ?A t S ps ?ps'"
    proof -
      from fresh_Nt_notin_set have "?A \<notin> nts ps \<union> {S}" by meson
      with uniformize_fun_uniformized[OF neq] show ?thesis by simp 
    qed
    ultimately show ?thesis
      by (smt (verit, best) converse_rtranclp_into_rtranclp uniformize_tm.simps)
  qed auto
qed


fun uniformize_all :: "['n::infinite, 't list, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_all _ [] ps = ps" |
  "uniformize_all S (t#ts) ps = (let ps' = uniformize_tm S t ps in uniformize_all S ts ps')"

fun tm_list_of_prods :: "('n,'t) prods \<Rightarrow> 't list" where
"tm_list_of_prods ps = (let rs = map snd ps in map destTm (filter isTm (concat rs)))"

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
  also have "... = (tm \<in> (\<Union>(A,w)\<in> (set ps). tms_syms w))"
    using tms_syms_def by fastforce
  also have "... = (tm \<in> tms ps)" unfolding Tms_def by blast
  finally show ?thesis .
qed

lemma uniformize_all_unchanged_tms:
  "tms ps = tms (uniformize_all S ts ps)"
  by (induction ts arbitrary: ps) (use uniformize_tm_unchanged_tms in fastforce)+

lemma uniformize_all_no_new_badTms:
    "\<lbrakk>\<forall>p\<in>set ps. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1; ps' = uniformize_all S ts ps\<rbrakk> 
      \<Longrightarrow> \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
proof (induction ts arbitrary: ps ps')
  case (Cons t' ts)
  let ?ps_unif = "uniformize_tm S t' ps"
  from Cons(3) have "ps' = uniformize_all S ts ?ps_unif" by simp
  moreover from uniformize_tm_no_new_badTms[OF _ Cons(2)] have 
    "\<forall>p\<in>set ?ps_unif. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1" by simp
  ultimately show ?case using Cons(1) by blast
qed simp



lemma uniformize_all_no_badTms:
  assumes "ts = tm_list_of_prods ps" 
          "ps' = uniformize_all S ts ps"
  shows "badTmsCount ps' = 0"
proof -
  have "\<forall>t\<in>set ts. \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
    using assms(2) proof (induction ts arbitrary: ps ps')
    case (Cons t ts)
    from Cons(2) have rec: "ps' = uniformize_all S ts (uniformize_tm S t ps)" by simp
    with Cons(1) have "\<forall>t\<in>set ts. \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1" by fast
    moreover from rec have "\<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1" 
      using uniformize_tm_no_bad_t uniformize_all_no_new_badTms by fast
    ultimately show ?case by fastforce
  qed simp
  with tm_list_of_prods_is_tms uniformize_all_unchanged_tms have 
    "\<forall>t\<in>tms ps'. \<forall>p\<in>set ps'. Tm t \<notin> set (snd p) \<or> length (snd p) \<le> 1"
    using assms by fast
  with assms show ?thesis unfolding Tms_def tms_syms_def
    by (metis (no_types, lifting) One_nat_def UnionI badTmsCountNot0 bot_nat_0.not_eq_extremum leD
        le_imp_less_Suc mem_Collect_eq numeral_2_eq_2 pair_imageI snd_conv)
qed


lemma uniformize_all_uniform:
  assumes "ts = tm_list_of_prods ps"
  shows "uniform (set(uniformize_all S ts ps))"
  using uniformize_all_no_badTms[OF assms] uniform_badTmsCount by blast


lemma uniformize_all_unifRtc:
  "(\<lambda>x y. \<exists>A t. uniformize A t S x y)\<^sup>*\<^sup>* ps (uniformize_all S ts ps)"
  proof (induction ts arbitrary: ps)
    case (Cons t ts)
    let ?ps' = "uniformize_tm S t ps"
  have "uniformize_all S (t#ts) ps = uniformize_all S ts ?ps'" by simp
  moreover from Cons have "(\<lambda>x y. \<exists>A t. uniformize A t S x y)\<^sup>*\<^sup>* ?ps' (uniformize_all S ts ?ps')" 
    by simp
  moreover have "(\<lambda>x y. \<exists>A t. uniformize A t S x y)\<^sup>*\<^sup>* ps ?ps'"
    using uniformize_tm_unifRtc by (smt (verit, ccfv_threshold) mono_rtranclp)
  ultimately show ?case by simp
qed simp


(*Simplifying the first two cases complicates proofs*)
fun replaceNts :: "['n::infinite, ('n,'t) syms] \<Rightarrow> ('n \<times> 'n) option \<times> ('n,'t) syms" where
  "replaceNts A [] = (None, [])" |
  "replaceNts A [s] = (None, [s])" |
  "replaceNts A (Nt s\<^sub>1 # Nt s\<^sub>2 # ss) = (Some (s\<^sub>1, s\<^sub>2), Nt A # ss)" |
  "replaceNts A (s#ss) = (let (nn_opt, ss') = replaceNts A ss in (nn_opt, s#ss'))"

lemma replaceNts_tm_unchanged_opt:
  assumes 
    "replaceNts A (s0#s1#ss) = (nn_opt, ss')"
    "\<exists>t. s0 = Tm t \<or> s1 = Tm t"
  obtains ss'' where "replaceNts A (s1#ss) = (nn_opt, ss'')"
proof -
  obtain nn_opt' ss'' where "replaceNts A (s1#ss) = (nn_opt', ss'')"
    by fastforce
  moreover with assms have "nn_opt = nn_opt'" by fastforce
  ultimately show thesis using that by blast
qed

lemma replaceNts_id_iff_None:
  assumes "replaceNts A ss = (nn_opt, ss')"
  shows "nn_opt = None \<longleftrightarrow> ss = ss'"
  using assms proof (induction ss arbitrary: nn_opt ss' rule: replaceNts.induct)
  case ("4_1" A t s ss)
  then obtain ss'' where rec: "replaceNts A (s#ss) = (nn_opt, ss'')"
    using replaceNts_tm_unchanged_opt by blast
  then show ?case using "4_1" by auto
next
  case ("4_2" A s t ss)
  then obtain ss'' where rec: "replaceNts A (Tm t#ss) = (nn_opt, ss'')"
    using replaceNts_tm_unchanged_opt by blast
  then show ?case using "4_2" by auto
qed auto



lemma replaceNts_replaces_pair:
  assumes 
    "replaceNts A ss = (nn_opt, ss')"
    "nn_opt \<noteq> None"
  obtains p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)"
    "ss = p@[Nt B\<^sub>1, Nt B\<^sub>2]@q"
    "ss' = p@[Nt A]@q" 
  using assms proof (induction ss arbitrary: thesis nn_opt ss' rule: replaceNts.induct)
  case ("4_1" A t s ss)
  then obtain ss'' where 
    "replaceNts A (s#ss) = (nn_opt, ss'')" 
    and ss'_def: "ss' = Tm t # ss''"
    using replaceNts_tm_unchanged_opt
    by (metis (lifting) case_prod_conv prod.inject replaceNts.simps(4))
  with "4_1"(1,4) obtain p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)" "s#ss = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "ss'' = p@[Nt A]@q" 
    by blast
  moreover with ss'_def have "Tm t #s#ss = (Tm t#p)@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "ss' = (Tm t#p)@[Nt A]@q"
    by auto
  ultimately show ?case using "4_1"(2) by blast
next
  case ("4_2" A s t ss)
  then obtain ss'' where 
    "replaceNts A (Tm t#ss) = (nn_opt, ss'')" 
    and ss'_def: "ss' = s # ss''"
    using replaceNts_tm_unchanged_opt
    by (metis (lifting) old.prod.case prod.inject replaceNts.simps(5))
  with "4_2"(1,4) obtain p q B\<^sub>1 B\<^sub>2 where 
    "nn_opt = Some (B\<^sub>1,B\<^sub>2)" "Tm t#ss = p@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "ss'' = p@[Nt A]@q" 
    by blast
  moreover with ss'_def have "s#Tm t#ss = (s#p)@[Nt B\<^sub>1,Nt B\<^sub>2]@q" "ss' = (s#p)@[Nt A]@q"
    by auto
  ultimately show ?case using "4_2"(2) by blast
qed fastforce+

corollary replaceNts_replaces_pair_Some:
  assumes "replaceNts A ss = (Some (B\<^sub>1,B\<^sub>2), ss')"
  obtains p q where 
    "ss = p@[Nt B\<^sub>1, Nt B\<^sub>2]@q"
    "ss' = p@[Nt A]@q"
  using replaceNts_replaces_pair 
  by (smt (verit) assms option.distinct(1) option.inject prod.inject)

fun binarizeNt_fun :: "['n::infinite, ('n,'t) prods, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
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
    "A \<notin> nts ps \<union> {S}"
    "binarizeNt_fun A ps ps \<noteq> ps"
  obtains B\<^sub>1 B\<^sub>2 where  "binarizeNt A B\<^sub>1 B\<^sub>2 S ps (binarizeNt_fun A ps ps)"
  (* shows? *)
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
  ultimately have "binarizeNt A B\<^sub>1 B\<^sub>2 S ps (binarizeNt_fun A ps ps)" 
    unfolding binarizeNt_def using assms(1) by auto
  then show thesis using that by simp
qed

lemma binarizeNt_fun_dec_badNtsCount:
  assumes "binarizeNt_fun A ps ps \<noteq> ps" 
          "A \<notin> nts ps \<union> {S}"
  shows "badNtsCount (binarizeNt_fun A ps ps) < badNtsCount ps"
  using lemma6_b assms binarizeNt_fun_binarized by meson

(* Needed to prove the badNts_impl_binarizeNt_fun_not_id_unif *)
lemma removeAll_app_eq_impl_removed:
  "removeAll z xs @ ys = xs \<Longrightarrow> (\<forall>y\<in>set ys. y = z)"
  by (induction xs) 
    (simp, (metis member_remove removeAll_append removeAll_id remove_code(1) self_append_conv))


lemma badNts_impl_binarizeNt_fun_not_id_unif:
  assumes "badNtsCount ps = Suc n"
    "uniform (set ps)"
  shows "binarizeNt_fun A ps0 ps \<noteq> ps0"
  using assms proof (induction ps arbitrary: n)
  case (Cons p ps)
  obtain l r where lr_def: "(l,r) = p" using old.prod.exhaust by metis
  consider (no_badNts_hd) "badNtsCount [p] = 0" | (Suc_badNts_hd) m where "badNtsCount [p] = Suc m"
    using not0_implies_Suc by blast
  then show ?case
  proof cases
    case no_badNts_hd
    from Cons(3) have only_Nts: "length r = 1 \<or> (\<forall>s\<in>(set r). \<exists>n. s = Nt n)"
      unfolding uniform_def using lr_def 
      by (metis Cons.prems(2) One_nat_def Suc_leI badTmsCountSet isNt_def le_antisym length_pos_if_in_set
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
      by (metis badNtsCountSet badTmsCountSet list.set_intros(1,2) no_badNts_hd old.nat.exhaust set_ConsD
          uniform_badTmsCount)
  next
    case Suc_badNts_hd
    with lr_def have all_Nts: "length r > 2 \<and> (\<forall>s\<in>set r. \<exists>n. s = Nt n)" using prodNts_def 
      by (metis (no_types, lifting) ext Cons.prems(2) One_nat_def add.commute add_Suc_right
          add_mono_thms_linordered_semiring(1) badNtsCountSet badTmsCountSet empty_iff empty_set isNt_def
          length_Suc_conv linorder_not_less list.set_intros(1) noTms_prodTms0 numeral_2_eq_2 plus_nat.add_0
          set_ConsD snd_conv uniform_badTmsCount zero_le)
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
  fixes ps :: "('n::infinite, 't) prods"
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

function binarizeNt_all :: "['n::infinite, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "binarizeNt_all S ps = 
    (let ps' = binarizeNt_fun (fresh (nts ps \<union> {S})) ps ps in
    if ps = ps' then ps else binarizeNt_all S ps')"
  by auto
termination
proof
  let ?R = "measure (\<lambda>(S,ps). badNtsCount ps)"
  show "wf ?R" by fast
  fix S :: "'n::infinite"
  and ps ps' :: "('n,'t) prods"
  let ?A = "fresh (nts ps \<union> {S})"
  assume ps'_def: "ps' = binarizeNt_fun ?A ps ps"
         and neq: "ps \<noteq> ps'"
  moreover with fresh_Nt_notin_set have "?A \<notin> nts ps \<union> {S}" by blast
  ultimately show "((S,ps'),(S,ps)) \<in> ?R" 
    using binarizeNt_fun_dec_badNtsCount by force
qed

lemma binarizeNt_all_binRtc:
  "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* ps (binarizeNt_all S ps)"
proof (induction "badNtsCount ps" arbitrary: ps rule: less_induct)
  case less
  let ?A = "fresh (nts ps \<union> {S})"
  have A_notin_nts: "?A \<notin> nts ps \<union> {S}"
    using fresh_finite by (metis finite_Un finite_insert finite_nts insert_is_Un)
  consider (eq) "binarizeNt_fun ?A ps ps = ps" |
           (neq) "binarizeNt_fun ?A ps ps \<noteq> ps" by blast
  then show ?case 
  proof cases
    case neq
    let ?ps' = "binarizeNt_fun ?A ps ps"
    from binarizeNt_fun_dec_badNtsCount[OF neq A_notin_nts] have
      "badNtsCount ?ps' < badNtsCount ps" .
    with less have "(\<lambda>x y. \<exists>A B\<^sub>1 B\<^sub>2. binarizeNt A B\<^sub>1 B\<^sub>2 S x y)\<^sup>*\<^sup>* ?ps' (binarizeNt_all S ?ps')"
      by blast
    moreover from neq A_notin_nts obtain B\<^sub>1 B\<^sub>2 where "binarizeNt ?A B\<^sub>1 B\<^sub>2 S ps ?ps'"
      using binarizeNt_fun_binarized by blast
    ultimately show ?thesis 
      by (smt (verit, best) binarizeNt_all.simps
          converse_rtranclp_into_rtranclp)
  qed simp
qed

lemma binarizeNt_all_preserves_uniform:
  fixes ps :: "('n::infinite, 't) prods"
  assumes ps_uniform: "uniform (set ps)"
      and ps'_def: "ps' = binarizeNt_all S ps"
    shows "uniform (set ps')"
using assms proof (induction "badNtsCount ps" arbitrary: ps ps' rule: less_induct)
  case less
  let ?A = "fresh (nts ps \<union> {S})"
  consider (rec) "binarizeNt_fun ?A ps ps \<noteq> ps" | (no_rec) "binarizeNt_fun ?A ps ps = ps" by blast
  then show ?case 
  proof cases
    case rec
    let ?ps' = "binarizeNt_fun ?A ps ps"
    from rec have "binarizeNt_all S ps = binarizeNt_all S ?ps'" 
      by (smt (verit) binarizeNt_all.elims)
    with less binarizeNt_fun_dec_badNtsCount[OF rec] fresh_finite binarizeNt_fun_preserves_uniform
      show ?thesis by (metis finite.emptyI finite.insertI finite_UnI finite_nts)
  qed (use less in simp)
qed

lemma binarizeNt_all_preserves_binary:
  assumes binary: "binary (set ps)"
      and ps'_def: "ps' = binarizeNt_all S ps"
    shows "binary (set ps')"
proof -
  from binary have "badNtsCount ps = 0"
    by (metis badNtsCountNot0 binary_def bot_nat_0.not_eq_extremum leD le_imp_less_Suc numeral_2_eq_2
        numeral_3_eq_3 split_conv)
  hence "binarizeNt_all S ps = ps" using binarizeNt_fun_dec_badNtsCount fresh_Nt_notin_set 
    by (smt (verit, best) binarizeNt_all.simps bot_nat_0.extremum_strict)
  with assms show ?thesis by argo
qed

lemma binarizeNt_all_binary_if_uniform:
  fixes ps :: "('n::infinite, 't) prods"
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
    with uniform binary_badNtsCount obtain n where Suc_badNts: "badNtsCount ps = Suc n" 
      using not0_implies_Suc by blast
    with uniform ps'_def show ?thesis 
    proof (induction "badNtsCount ps" arbitrary: ps ps' n rule: less_induct)
      case less
      let ?A = "fresh (nts ps \<union> {S})"
      from less badNts_impl_binarizeNt_fun_not_id_unif have "binarizeNt_fun ?A ps ps \<noteq> ps"
        by fastforce
      hence badNtsCount_dec: "badNtsCount (binarizeNt_fun ?A ps ps) < badNtsCount ps" 
                              (is "badNtsCount ?ps' < _")
        using fresh_finite binarizeNt_fun_dec_badNtsCount 
        by (metis List.finite_set finite.emptyI finite.insertI finite_Nts finite_UnI)
      consider (zero_badNts) "badNtsCount ?ps' = 0" | (Suc_badNts) m where "badNtsCount ?ps' = Suc m"
        using not0_implies_Suc by blast
      then show ?case
      proof cases
        case zero_badNts
        moreover from less.prems(1) binarizeNt_fun_preserves_uniform have "uniform (set ?ps')" 
          by blast
        ultimately show ?thesis using binary_badNtsCount
          by (smt (verit, del_insts) binarizeNt_all.simps binarizeNt_all_preserves_binary less.prems(2))
      next
        case Suc_badNts
        moreover from less.prems(1) binarizeNt_fun_preserves_uniform have unif: "uniform (set ?ps')"
          by blast
        ultimately show ?thesis using less(1)[OF badNtsCount_dec _ _ Suc_badNts] 
          by (smt (verit, del_insts) binarizeNt_all.simps less.prems(2))
      qed
    qed
  qed
qed

theorem cnf_noe_nou_funs:
  fixes ps :: "('n::infinite, 't) prods"
  assumes eps_free: "Eps_free (set ps)" 
      and unit_free: "Unit_free (set ps)"
      and ts_def: "ts = tm_list_of_prods ps"
      and ps'_def: "ps' = (binarizeNt_all S o uniformize_all S ts) ps"
    shows "uniform (set ps')" "binary (set ps')" "lang ps S = lang ps' S" "Eps_free (set ps')" 
          "Unit_free (set ps')"
proof (goal_cases uniform binary lang_eq Eps_free Unit_free)
  case uniform
  let ?ps_unif = "uniformize_all S ts ps"
  from uniformize_all_uniform ts_def have "uniform (set ?ps_unif)" by fast
  with binarizeNt_all_preserves_uniform ps'_def show ?case by auto
  case binary
  then show ?case using assms binarizeNt_all_binary_if_uniform ts_def
    by (metis comp_apply uniform_badTmsCount uniformize_all_no_badTms)
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




end
