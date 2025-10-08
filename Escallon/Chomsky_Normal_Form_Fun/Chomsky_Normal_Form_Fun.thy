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

fun replace_tm :: "['n, ('n,'t) syms] \<Rightarrow> ('n,'t) syms" where
  "replace_tm A [] = []" |
  "replace_tm A (s#sms) = (case s of Tm t \<Rightarrow> Nt A # sms | Nt _ \<Rightarrow> s # replace_tm A sms)"


lemma replace_tm_length_unchanged[simp]: 
  "length (replace_tm A sms) = length sms"
  by (induction sms) (auto split: sym.split)
  

lemma replace_tm_id_iff_tm_notin_syms:
  shows "(\<forall>t. Tm t \<notin> set sms) \<longleftrightarrow> replace_tm A sms = sms"
  by (induction sms) (auto split: sym.splits)


(*Proofs break with iff lemma. Fix?*)
lemma tm_notin_syms_impl_replace_tm_id:
  assumes "\<forall>t. Tm t \<notin> set sms" 
  shows "replace_tm A sms = sms"
  using assms replace_tm_id_iff_tm_notin_syms by fast
lemma replace_tm_id_impl_tm_notin_syms:
  assumes "replace_tm A sms = sms"
  shows "\<forall>t. Tm t \<notin> set sms"
  using assms replace_tm_id_iff_tm_notin_syms by fast

(*Strengthen with "Tm t \<notin> set p?*)
lemma replace_tm_replaces_single:
  assumes "replace_tm A sms \<noteq> sms"
  obtains p s t where "sms = p@[Tm t]@s"
                    "replace_tm A sms = p@[Nt A]@s"
using assms proof (induction sms arbitrary: thesis)
  case (Cons s sms)
  consider (tm) "\<exists>t. s = Tm t" | (nt) "\<forall>t. s \<noteq> Tm t" by blast
  then show ?case 
  proof cases
    case tm
    then obtain p q t where "s = Tm t" "s#sms = p@[Tm t]@q" "p = []" by auto
    moreover from this(1) have "replace_tm A (s#sms) = Nt A#sms" by simp
    ultimately show thesis using Cons(2) by fastforce
  next
    case nt
    with Cons(3) have "replace_tm A sms \<noteq> sms" 
      by (metis replace_tm_id_iff_tm_notin_syms set_ConsD)
    with Cons(1)  
    obtain p q t where pq_defs: "sms = p@[Tm t]@q" "replace_tm A sms = p@[Nt A]@q" 
      by metis
    with nt obtain n where "s = Nt n" using sym.exhaust by meson
    with pq_defs(2) have "replace_tm A (s#sms) = (s#p)@[Nt A]@q" by simp
    then show ?thesis using Cons(2) pq_defs by (meson Cons_eq_appendI)
  qed
qed simp


(*TODO: Redefine uniformize_fun. Problem: t not accessible*)

(*The current implementation corresponds to uniformize as defined in 
  Context_Free_Grammar.Chomsky_Normal_Form. This can be simplified with maps.*)
fun uniformize_fun :: "['n::infinite, ('n,'t) prods, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_fun S ps0 [] = ps0" |
  "uniformize_fun _ _ _ = undefined"
  (*"uniformize_fun S ps0 ((l,r) # ps) = 
    (let A = fresh (nts ps0 \<union> {S}) in let r' = replace_tm A r in 
      if r = r' \<or> length r < 2 then uniformize_fun S ps0 ps
      else (removeAll (l,r) ps0) @ [(A, [Tm t]), (l,r')])"*)

lemma uniformize_fun_id:
  assumes "\<forall>(l,r)\<in>set ps. Tm t \<notin> set r \<or> length r < 2"
  shows "uniformize_fun A t ps0 ps = ps0"
  using assms tm_notin_syms_impl_replace_tm_id by (induction ps) fastforce+

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
    hence "replace_tm A t r = r \<or> length r < 2" using tm_notin_syms_impl_replace_tm_id by fast
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
                      = removeAll p (xs@ys) @ [(A, [Tm t]), (l,replace_tm A t r)]" 
      by (smt (verit) replace_tm_id_iff_tm_notin_syms uniformize_fun.simps(2)
          verit_comp_simplify1(3))
    also have "... = xs @ removeAll p ys @ [(A, [Tm t]), (l,replace_tm A t r)]"
      using p_notin_xs by simp
    also have "... = xs @ uniformize_fun A t ys (p#ps)" using not_unif 
      by (smt (verit) lr_def replace_tm_id_impl_tm_notin_syms
          uniformize_fun.simps(2) verit_comp_simplify1(3))
    finally show ?thesis .
  next
    case unif
    hence unif_ite: "replace_tm A t r = r \<or> length r < 2" using tm_notin_syms_impl_replace_tm_id 
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
      using replace_tm_id_impl_tm_notin_syms by metis
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
  assumes "uniformize_fun A t ps ps \<noteq> ps"
          "A = fresh (nts ps \<union> {S})"
  shows "uniformize A t S ps (uniformize_fun A t ps ps)"
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