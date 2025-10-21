theory Chomsky_Normal_Form_Fun
  imports Chomsky_Normal_Form
begin

fun replaceTm :: "['n, 't, ('n,'t) syms] \<Rightarrow> ('n,'t) syms" where
  "replaceTm A t [] = []" |
  "replaceTm A t (s # sms) = (if s = Tm t then Nt A # sms else s # replaceTm A t sms)"

lemma replaceTm_length_unchanged[simp]: 
  "length (replaceTm A t sms) = length sms"
  by (induction sms) auto
  

lemma replaceTm_id_iff_tm_notin_syms:
  shows "Tm t \<notin> set sms \<longleftrightarrow> replaceTm A t sms = sms"
  by (induction sms) auto

(*Proofs break with iff lemma. Fix?*)
lemma tm_notin_syms_impl_replaceTm_id:
  assumes "Tm t \<notin> set sms" 
  shows "replaceTm A t sms = sms"
  using assms replaceTm_id_iff_tm_notin_syms by fast
lemma replaceTm_id_impl_tm_notin_syms:
  assumes "replaceTm A t sms = sms"
  shows "Tm t \<notin> set sms"
  using assms replaceTm_id_iff_tm_notin_syms by fast

(*Strengthen with "Tm t \<notin> set p?*)
lemma replaceTm_replaces_single:
  assumes "replaceTm A t sms \<noteq> sms"
  obtains p s where "sms = p@[Tm t]@s"
                    "replaceTm A t sms = p@[Nt A]@s"
using assms proof (induction sms arbitrary: thesis)
  case (Cons s sms)
  from Cons(3) have t_in_ssms: "Tm t \<in> set (s#sms)" using replaceTm_id_iff_tm_notin_syms by fast
  consider (eq) "s = Tm t" | (neq) "s \<noteq> Tm t" by blast
  then show ?case 
  proof cases
    case eq
    then obtain p q where "s#sms = p@[Tm t]@q" "p = []" by auto
    moreover from eq have "replaceTm A t (s#sms) = Nt A#sms" by simp
    ultimately show thesis using Cons(2) by fastforce
  next
    case neq
    with t_in_ssms have "Tm t \<in> set sms" 
      by simp
    with Cons(1) replaceTm_id_iff_tm_notin_syms 
    obtain p q where pq_defs: "sms = p@[Tm t]@q" "replaceTm A t sms = p@[Nt A]@q" by metis
    with neq have "replaceTm A t (s#sms) = (s#p)@[Nt A]@q" by auto
    then show ?thesis using Cons(2) pq_defs by (meson Cons_eq_appendI)
  qed
qed simp


  

(*The current implementation corresponds to uniformize as defined in 
  Context_Free_Grammar.Chomsky_Normal_Form. This can be simplified with maps.*)
fun uniformize_fun :: "['n::infinite, 't, ('n,'t) prods, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_fun _ _ ps0 [] = ps0" |
  "uniformize_fun A t ps0 ((l,r) # ps) = 
    (let r' = replaceTm A t r in 
      if r = r' \<or> length r < 2 then uniformize_fun A t ps0 ps
      else (removeAll (l,r) ps0) @ [(A, [Tm t]), (l,r')])"

lemma uniformize_fun_id:
  assumes "\<forall>(l,r)\<in>set ps. Tm t \<notin> set r \<or> length r < 2"
  shows "uniformize_fun A t ps0 ps = ps0"
  using assms tm_notin_syms_impl_replaceTm_id by (induction ps) fastforce+

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
    "uniformize_fun A t ps ps = ((removeAll (l,r) ps) @ [(A, [Tm t]), (l, replaceTm A t r)])" 
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

lemma uniformize_fun_decreases_badTmsCount:
  assumes "uniformize_fun A t ps ps \<noteq> ps"
          "A \<notin> nts ps \<union> {S}"
  shows "badTmsCount (uniformize_fun A t ps ps) < badTmsCount ps"
  using assms uniformize_fun_uniformized lemma6_a by fast


function uniformize_rt :: "['n::infinite, 't, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_rt S t ps = 
    (let ps' = uniformize_fun (fresh (nts ps \<union> {S})) t ps ps in 
        if ps = ps' then ps else uniformize_rt S t ps')"
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
  moreover have "?A \<notin>  nts ps \<union> {S}" using fresh_finite 
    by (metis finite_Un finite_insert finite_nts insert_is_Un)
  ultimately show "((S,t,x), S,t,ps) \<in> ?R"
    using uniformize_fun_decreases_badTmsCount by force 
qed

lemma "(\<lambda>x y. \<exists>A. uniformize A t S x y)^** ps (uniformize_rt S t ps)"
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
      using uniformize_fun_decreases_badTmsCount fresh_finite 
      by (metis finite.emptyI finite.insertI finite_nts infinite_Un)
    with less have uniformize_rtrancl: 
      "(\<lambda>x y. \<exists>A. uniformize A t S x y)\<^sup>*\<^sup>* ?ps' (uniformize_rt S t ?ps')" by simp
    moreover have "uniformize ?A t S ps ?ps'"
    proof -
      from fresh_finite have "?A \<notin> nts ps \<union> {S}" 
        by (metis finite.emptyI finite.insertI finite_nts infinite_Un)
      with uniformize_fun_uniformized[OF neq] show ?thesis by simp 
    qed
    ultimately show ?thesis
      by (smt (verit, best) converse_rtranclp_into_rtranclp uniformize_rt.simps)
  qed auto
qed

(*Simplifying the first two cases complicates proofs*)
fun replaceNts :: "['n::infinite, 'n, 'n, ('n,'t) syms] \<Rightarrow> ('n,'t) syms" where
  "replaceNts A B\<^sub>1 B\<^sub>2 [] = []" |
  "replaceNts A B\<^sub>1 B\<^sub>2 [s] = [s]" |
  "replaceNts A B\<^sub>1 B\<^sub>2 (s\<^sub>1#s\<^sub>2#sms) = 
    (if s\<^sub>1 = Nt B\<^sub>1 \<and> s\<^sub>2 = Nt B\<^sub>2 then Nt A # sms 
    else s\<^sub>1 # replaceNts A B\<^sub>1 B\<^sub>2 (s\<^sub>2#sms))"

lemma replaceNts_replaces_single:
  assumes "replaceNts A B\<^sub>1 B\<^sub>2 sms \<noteq> sms"
  obtains p s where "sms = p@[Nt B\<^sub>1, Nt B\<^sub>2]@s"
                    "replaceNts A B\<^sub>1 B\<^sub>2 sms = p@[Nt A]@s" 
  using assms proof (induction sms arbitrary: thesis rule: replaceNts.induct)
  case (3 A B\<^sub>1 B\<^sub>2 s\<^sub>1 s\<^sub>2 sms)
  consider (hd) "s\<^sub>1 = Nt B\<^sub>1 \<and> s\<^sub>2 = Nt B\<^sub>2" | 
            (tl) "s\<^sub>1 \<noteq> Nt B\<^sub>1 \<or> s\<^sub>2 \<noteq> Nt B\<^sub>2" by blast
  then show ?case 
  proof cases
    case tl
    hence "replaceNts A B\<^sub>1 B\<^sub>2 (s\<^sub>1#s\<^sub>2#sms) = s\<^sub>1 # replaceNts A B\<^sub>1 B\<^sub>2 (s\<^sub>2#sms)" by fastforce
    moreover with tl 3 obtain p s where "replaceNts A B\<^sub>1 B\<^sub>2 (s\<^sub>2#sms) = p@[Nt A]@s"
                                        "s\<^sub>2#sms = p@[Nt B\<^sub>1, Nt B\<^sub>2]@s" 
      by metis 
    ultimately have "replaceNts A B\<^sub>1 B\<^sub>2 (s\<^sub>1#s\<^sub>2#sms) = (s\<^sub>1#p)@[Nt A]@s"
                    "s\<^sub>1#s\<^sub>2#sms = (s\<^sub>1#p)@[Nt B\<^sub>1, Nt B\<^sub>2]@s" by simp+
    then show ?thesis using 3(2) by blast
  qed (use 3 in force)
qed simp+

fun binarizeNt_fun :: "['n::infinite, 'n, 'n, ('n,'t) prods, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 [] = ps0" |
  "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 ((l,r)#ps) = 
    (let r' = replaceNts A B\<^sub>1 B\<^sub>2 r in
      if r = r' \<or> length r < 3 then binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 ps
      else (removeAll (l,r) ps0) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')])"

lemma binarizeNt_binarizes:
  assumes "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 ps \<noteq> ps0"
  obtains l r p s r' where
    "(l,r) \<in> set ps"
    "length r > 2"
    "replaceNts A B\<^sub>1 B\<^sub>2 r = r'"
    "r \<noteq> r'"
    "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 ps = (removeAll (l,r) ps0) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')]"
  using assms proof (induction ps arbitrary: thesis)
  case (Cons p ps)
  obtain l r r' where lr_defs: "p = (l,r)"  "r' = replaceNts A B\<^sub>1 B\<^sub>2 r" 
    by fastforce
  consider (hd) "r \<noteq> r' \<and> length r > 2" | (tl) "r = r' \<or> length r < 3"  by fastforce
  then show ?case 
  proof cases
    case hd
    moreover from this have 
      "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 (p#ps) = (removeAll (l,r) ps0) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')]" 
      using lr_defs by (smt (verit, best) Suc_numeral binarizeNt_fun.simps(2) not_less_eq
          semiring_norm(5))
    ultimately show ?thesis using Cons(2) lr_defs by (meson list.set_intros(1))
  next
    case tl
    with lr_defs have "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 (p#ps) = binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps0 ps" by simp
    with Cons show ?thesis using lr_defs by auto
  qed
qed simp

lemma binarizeNt_fun_binarized:
  assumes "A \<notin> nts ps \<union> {S}"
          "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps ps \<noteq> ps"
  shows "binarizeNt A B\<^sub>1 B\<^sub>2 S ps (binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps ps)"
proof -
  from binarizeNt_binarizes[OF assms(2)] obtain l r r' where
    "(l,r) \<in> set ps"
    "length r > 2"
    "replaceNts A B\<^sub>1 B\<^sub>2 r = r'"
    "r \<noteq> r'"
    "binarizeNt_fun A B\<^sub>1 B\<^sub>2 ps ps = (removeAll (l,r) ps) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, r')]"
    using binarizeNt_binarizes by auto
  moreover from this obtain p s where "r = p@[Nt B\<^sub>1, Nt B\<^sub>2]@s"  "r' = p@[Nt A]@s" 
    using replaceNts_replaces_single by metis 
  ultimately show ?thesis unfolding binarizeNt_def using assms(1) by auto
qed

end