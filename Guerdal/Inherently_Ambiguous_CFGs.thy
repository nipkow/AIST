theory Inherently_Ambiguous_CFGs
  imports 
     Main
     Inherently_Ambiguous_CFGs_Auxilliary_Lemmas
     Ambiguity
     "HOL-Lattice.Orders"
     Ambig_Lang_Aux
     "HOL-Library.Countable_Set"
     Context_Free_Grammar.Context_Free_Language
begin


    
section "Existence of an inherently ambiguous CFG"

text "We will prove here that 
  \<open>((\<Union>n.\<Union>m. {[a]^^n @ [b]^^n @ [c]^^m @ [d]^^m}) \<union> (\<Union>n.\<Union>m. {[a]^^n @ [b]^^m @ [c]^^m @ [d]^^n}))\<close>
  is inherently ambiguous, proving the existence of inherently ambiguous languages."


text "The first fact listed in the proof of theorem: if \<open>X \<Rightarrow>* wXz\<close>, then \<open>w\<close> and \<open>z\<close> needs to have each exactly one type of symbol."
theorem fact1: 
  fixes G' :: "('n, t) Cfg"
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'"
  shows   "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
          \<Longrightarrow> (\<forall>i < length x. \<forall>j < length x. (x ! i = x !j)) \<and> (\<forall>i < length y. \<forall>j < length y. y ! i = y !j)"
proof - 
  fix X x y
  assume der_assm: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y"
  text "Showing: \<open>S \<Rightarrow>* wXz\<close>"
  consider (empty) "x @ y = []" | (not_empty) "x @ y \<noteq> []" by auto
  then show "(\<forall>i < length x. \<forall>j < length x. (x ! i = x !j)) \<and> (\<forall>i < length y. \<forall>j < length y. y ! i = y !j)"
  text "Eliminating the trivial case of \<open>X \<Rightarrow>* X\<close>:"
    proof cases
      case empty
      then show ?thesis by auto
    next
      case not_empty     
      have in_L: "\<exists>ww zz xx. ww @ x @ x @ xx @ y @ y @ zz \<in> L_ambig" 
        using derives_two[OF usefulG' start_prod not_empty der_assm] unfolding langG' by blast
      then obtain ww zz xx where in_L: "ww @ x @ x @ xx @ y @ y @ zz \<in> L_ambig" by blast

      text "An additional fact that all words in \<open>L\<close> only have \<open>a,b,c,d\<close> as terminals: needed since \<open>rank\<close> is 
            defined properly (as a strict ordering) only for them"
      let ?w = "ww @ x @ x @ xx @ y @ y @ zz"
      let ?wwyl = "length (ww @ x @ x @ xx)"
      let ?wwl = "length ww"
      let ?xl = "length x" let ?yl = "length y"

      text "We prove that if there is an \<open>i,j\<close> pair for which \<open>x_i\<noteq>x_j\<close> or \<open>y_i\<noteq>y_j\<close>, 
            then the resulting word \<open>wxx|xx|yyz\<close> cannot be in the language ==> contradiction!"
      show "(\<forall>i < ?xl. \<forall>j < ?xl. (x ! i = x !j)) \<and> (\<forall>i < ?yl. \<forall>j < ?yl. y ! i = y !j)"
      proof (rule ccontr)
        assume "\<not> ((\<forall>i < length x. \<forall>j < length x. (x ! i = x !j)) \<and> (\<forall>i < length y. \<forall>j < length y. y ! i = y !j))"
        then have "(\<exists>i < length x. \<exists>j < length x. (x ! i \<noteq> x !j)) \<or> (\<exists>i < length y. \<exists>j < length y. y ! i \<noteq> y !j)" by auto
        then consider "\<exists>i < length x. \<exists>j < length x. (x ! i \<noteq> x !j)" |  "\<exists>i < length y. \<exists>j < length y. (y ! i \<noteq> y !j)" by auto
        thus "False" 
        proof cases
          case 1 
          then obtain i j where ij_obtain: "i < length x" "j < length x" "x ! i \<noteq> x ! j" "i \<noteq> j" by blast

          from ij_obtain(3) have "((x @ x) ! i) < ((x @ x) ! j) \<or> ((x @ x) ! i) > ((x @ x) ! j)"
            by (auto simp add: ij_obtain(1,2) nth_append)
          from ij_obtain(3) have "((x @ x) ! (length x + i)) < ((x @ x) ! j) \<or> ((x @ x) ! i) > ((x @ x) ! (length x + j))"
            by (auto simp add: ij_obtain(1,2) nth_append_left)
          then have ranky: "(?w ! (?wwl + ?xl + i)) < (?w ! (?wwl + j)) \<or> (?w ! (?wwl + i)) > (?w ! (?wwl + ?xl + j))"
            by (metis append_assoc ij_obtain(1,2) length_append nth_append_left nth_append_length_plus) 
          
          have ineqs: "?wwl + ?xl + i > ?wwl + j" "?wwl + ?xl + j > ?wwl + i"
            by (auto simp add: ij_obtain(1,2) trans_less_add1)
          have less_than_w: "?wwl + ?xl + i < length ?w" "?wwl + ?xl + j < length ?w"
            by (auto simp add: ij_obtain(1,2) trans_less_add1)

          from in_L have w_sorted: "\<And>i j. i < j \<and> j < length ?w \<Longrightarrow> (?w ! i) \<le> (?w ! j)"
            using w_sorted_ij by auto
          then show ?thesis using ineqs(1,2) leD less_than_w(1,2) ranky by blast
        next
          case 2
          then obtain i j where ij_obtain: "i < length y" "j < length y" "y ! i \<noteq> y ! j" "i \<noteq> j" by blast
          have x_i_xx_i: "y ! i = (y @ y) ! (?yl + i)" by auto
 
          from ij_obtain(3) have "((y @ y) ! i) < ((y @ y) ! j) \<or> ((y @ y) ! i) > ((y @ y) ! j)"
            by (auto simp add: ij_obtain(1,2) nth_append)
          from ij_obtain(3) have "((y @ y) ! (length y + i)) < ((y @ y) ! j) \<or> ((y @ y) ! i) > ((y @ y) ! (length y + j))"
            by (auto simp add: ij_obtain(1,2) nth_append_left)
          then have ranky: "(?w ! (?wwyl + ?yl + i)) < (?w ! (?wwyl + j)) \<or> (?w ! (?wwyl + i)) > (?w ! (?wwyl + ?yl + j))"
            by (metis append_assoc ij_obtain(1,2) length_append nth_append_left nth_append_length_plus) 
          
          have ineqs: "?wwyl + ?yl + i > ?wwyl + j" "?wwyl + ?yl + j > ?wwyl + i"
            by (auto simp add: ij_obtain(1,2) trans_less_add1)
          have less_than_w: "?wwyl + ?yl + i < length ?w" "?wwyl + ?yl + j < length ?w"
            by (auto simp add: ij_obtain(1,2) trans_less_add1)

          from in_L have w_sorted: "\<And>i j. i < j \<and> j < length ?w \<Longrightarrow> (?w ! i) \<le> (?w ! j)"
            using w_sorted_ij by auto
          then show ?thesis using ineqs(1,2) leD less_than_w(1,2) ranky by blast
        qed
     qed
   qed
 qed

corollary ex_one_symbol: 
  fixes G' :: "('n, t) Cfg"
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'"
  shows   "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
          \<Longrightarrow> (\<exists>s. \<forall>i < length x. (x ! i = s)) \<and> (\<exists>s. \<forall>i < length y. (y ! i = s))"
using assms fact1[OF assms] by meson



theorem fact2:
fixes G' :: "('n, t) Cfg"
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'"
  shows   "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
          \<Longrightarrow> \<forall>i < length x. \<forall>j < length y. (x ! i \<noteq> y !j)"
proof -
 fix X x y
 assume der_assm: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y"
    
  from assms have ex_one_type_symbol: 
    "(\<exists>s. \<forall>i < length x. (x ! i = s)) \<and> (\<exists>s. \<forall>i < length y. (y ! i = s))"
    using ex_one_symbol[OF assms der_assm] by blast
   
  then have one_type_for_xy: "(\<exists>s. \<forall>i < length x. (x ! i = s))" "(\<exists>s. \<forall>i < length y. (y ! i = s))"
     by auto

  have one_type_for_x: "\<exists>sx. \<forall>i < length x. x ! i = sx" and one_type_for_y: "\<exists>sy. \<forall>i < length y. y ! i = sy" 
    using one_type_for_xy apply blast
    using one_type_for_xy by blast
  then obtain sx sy where sx_def: "\<forall>i < length x. x ! i = sx" and sy_def: "\<forall>i < length y. y ! i = sy" by blast

  then have x_list_sx: "x = [sx] ^^ (length x)" and y_list_sy: "y = [sy] ^^ (length y)" 
    using singleton_power[of x] singleton_power[of y] by auto 

  then have count_x: "count_list x sx = length x" and count_y: "count_list y sy = length y"
    using count_list_pow_list One_nat_def count_list.simps(2) count_list_eq_length_filter filter.simps(1) length_pow_list list.size(4) apply metis
    using y_list_sy count_list_pow_list One_nat_def count_list.simps(2) count_list_eq_length_filter filter.simps(1) length_pow_list list.size(4) by metis


  then have x_not: "\<And>s :: t. s \<noteq> sx \<Longrightarrow> count_list x s = 0" and y_not: "\<And>s. s \<noteq> sy \<Longrightarrow> count_list y s = 0"   
    by (auto simp add: in_set_conv_nth sy_def sx_def)

  show "\<forall>i < length x. \<forall>j < length y. (x ! i \<noteq> y !j)"
  proof (rule ccontr)
   assume not_not_eq: "\<not>(\<forall>i<length x. \<forall>j<length y. x ! i \<noteq> y ! j)"
   then have "\<exists>i<length x. \<exists>j<length y. sx = sy" using sx_def sy_def by auto    
   then obtain i j where ij_obtain: "i<length x" "j<length y" "sx = sy" by blast
       
   have not_empty: "x @ y \<noteq> []" using ij_obtain(1) by force
   then have len_not_zero: "length x + length y > 0" by auto
      
        
   have "\<exists>ww zz xx. ww @ x @ xx @ y @ zz \<in> LangS G' \<and> ww @ x @ x @ xx @ y @ y @ zz \<in> LangS G'"
     by (rule derives_two[OF usefulG' start_prod not_empty der_assm])

   then obtain ww zz xx where wxXyz_in_L: "ww @ x @ xx @ y @ zz \<in> L_ambig" and wxxXyyz_in_L: "ww @ x @ x @ xx @ y @ y @ zz \<in> L_ambig" 
     unfolding langG' by force
      
   let ?wxXyz = "ww @ x @ xx @ y @ zz"  let ?wxxXyyz = "ww @ x @ x @ xx @ y @ y @ zz"
   
   have counts_or_wxXyz:
     "((count_list ?wxXyz A = count_list ?wxXyz B) \<and> (count_list ?wxXyz C = count_list ?wxXyz D))
     \<or> ((count_list ?wxXyz A = count_list ?wxXyz D) \<and> (count_list ?wxXyz B = count_list ?wxXyz C))" 
    using w_len_eq[OF wxXyz_in_L] by presburger

   have counts_or_wxxXyyz:
     "((count_list ?wxxXyyz A = count_list ?wxxXyyz B) \<and> (count_list ?wxxXyyz C = count_list ?wxxXyyz D))
     \<or> ((count_list ?wxxXyyz A = count_list ?wxxXyyz D) \<and> (count_list ?wxxXyyz B = count_list ?wxxXyyz C))"
   using w_len_eq[OF wxxXyyz_in_L] by presburger
    
      
   have sx_in_abcd: "sx \<in> {A,B,C,D}" 
     using t.exhaust by auto

     
   from wxXyz_in_L have "?wxXyz \<in> L_left \<or> ?wxXyz \<in> L_right" by auto
   then have "(\<exists>n m. (count_list ?wxXyz A = n \<and> count_list ?wxXyz B = n \<and> count_list ?wxXyz C = m \<and> count_list ?wxXyz D = m)) \<or> (\<exists>n m. (count_list ?wxXyz A = n \<and> count_list ?wxXyz B = m \<and> count_list ?wxXyz C = m \<and> count_list ?wxXyz D = n))"
     using w_len_eqn_left w_len_eqn_right by presburger
    
   then obtain n m where
        count_a: "count_list ?wxXyz A = n" 
    and count_b: "count_list ?wxXyz B = n \<or> count_list ?wxXyz B = m"
    and count_c: "(count_list ?wxXyz C = m)" 
    and count_d: "(count_list ?wxXyz D = m \<or> count_list ?wxXyz D = n)" 
     by blast

   have counts: "count_list (?wxxXyyz) sx = count_list ?wxXyz sx + count_list x sx + count_list y sx"
      by auto
   then have cl1: "count_list (?wxxXyyz) sx = count_list ?wxXyz sx + length x + length y" 
     using count_x count_y ij_obtain(3) by argo
   then have cl2: "\<And>s. s\<noteq>sx \<Longrightarrow> count_list ?wxxXyyz s = count_list ?wxXyz s" 
     using x_not y_not ij_obtain(3) counts by auto
   from this cl1 have counts_forall: "\<And>s. count_list ?wxxXyyz s = count_list ?wxXyz s + (if s = sx then length x + length y else 0)" 
     using x_not y_not ij_obtain(3) counts by force
   then have "count_list ?wxxXyyz sx \<noteq> count_list ?wxXyz sx" 
     using len_not_zero by auto

   then have cl3: "\<exists>c. count_list ?wxxXyyz c \<noteq> count_list ?wxXyz c \<and> (\<forall>x \<noteq> c. count_list ?wxxXyyz x = count_list ?wxXyz x)"
     using cl2 by auto

    thus "False" using w_lens_not_in_L[OF wxXyz_in_L cl3] wxxXyyz_in_L by blast
  qed
qed



theorem fact3:
fixes G' :: "('n, t) Cfg"
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" 
  shows   "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y
          \<Longrightarrow>length x = length y"
proof -

 fix X x y
 assume der_assm: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y"
 
 consider (empty) "x @ y = []" | (not_empty) "x @ y \<noteq> []" by auto
 thus "length x = length y"
 proof cases
   case empty
   then show ?thesis by auto
 next
   case not_empty

   have ex_one_type_symbol: 
     "(\<exists>s. \<forall>i < length x. (x ! i = s)) \<and> (\<exists>s. \<forall>i < length y. (y ! i = s))"
     using ex_one_symbol[OF assms(1,2,3) der_assm] by blast 
   then obtain sx sy where sx_obtain: "\<And>i. i < length x \<Longrightarrow> (x ! i = sx)" and sy_obtain: " \<And>i. i < length y \<Longrightarrow> (y ! i = sy)" by blast
   then have x_list_sx: "x = [sx] ^^ (length x)" and y_list_sy: "y = [sy] ^^ (length y)" using singleton_power[of x] singleton_power[of y] by auto

  then have count_x: "count_list x sx = length x" and count_y: "count_list y sy = length y"
    using count_list_pow_list One_nat_def count_list.simps(2) count_list_eq_length_filter filter.simps(1) length_pow_list list.size(4) apply metis
    using y_list_sy count_list_pow_list One_nat_def count_list.simps(2) count_list_eq_length_filter filter.simps(1) length_pow_list list.size(4) by metis 
  
   have not_same_type_symbol: 
    "\<And>i j. i  < length x \<Longrightarrow> j < length y \<Longrightarrow> (x ! i \<noteq> y !j)"
     using fact2[OF assms(1,2,3) der_assm] by blast


   have "\<exists>ww zz xx. ww @ x @ xx @ y @ zz \<in> LangS G' \<and> ww @ x @ x @ xx @ y @ y @ zz \<in> LangS G'"
     by (rule derives_two[OF usefulG' start_prod not_empty der_assm])
   then obtain ww zz xx where wxXyz_in_L: "ww @ x @ xx @ y @ zz \<in> L_ambig" and wxxXyyz_in_L: "ww @ x @ x @ xx @ y @ y @ zz \<in> L_ambig"
     unfolding langG' by force
   let ?wxXyz = "ww @ x @ xx @ y @ zz"  let ?wxxXyyz = "ww @ x @ x @ xx @ y @ y @ zz"


   show ?thesis 
   proof (rule ccontr)
     assume lens_not_eq: "length x \<noteq> length y"
     then have "count_list x sx \<noteq> count_list y sy" using count_x count_y by auto
    
     have counts_or_wxXyz:
     "((count_list ?wxXyz A = count_list ?wxXyz B) \<and> (count_list ?wxXyz C = count_list ?wxXyz D))
     \<or> ((count_list ?wxXyz A = count_list ?wxXyz D) \<and> (count_list ?wxXyz B = count_list ?wxXyz C))" 
       using w_len_eq[OF wxXyz_in_L] by presburger

     have counts_or_wxxXyyz:
       "((count_list ?wxxXyyz A = count_list ?wxxXyyz B) \<and> (count_list ?wxxXyyz C = count_list ?wxxXyyz D))
       \<or> ((count_list ?wxxXyyz A = count_list ?wxxXyyz D) \<and> (count_list ?wxxXyyz B = count_list ?wxxXyyz C))"
       using w_len_eq[OF wxxXyyz_in_L] by presburger
    
      
     have sx_in_abcd: "sx \<in> {A,B,C,D}" "sy \<in> {A,B,C,D}"
       using t.exhaust by auto

     
     from wxXyz_in_L have "?wxXyz \<in> L_left \<or> ?wxXyz \<in> L_right" by auto
     then have count_nms: "(\<exists>n m. (count_list ?wxXyz A = n \<and> count_list ?wxXyz B = n \<and> count_list ?wxXyz C = m \<and> count_list ?wxXyz D = m)) 
              \<or> (\<exists>n m. (count_list ?wxXyz A = n \<and> count_list ?wxXyz B = m \<and> count_list ?wxXyz C = m \<and> count_list ?wxXyz D = n))"
       using w_len_eqn_left w_len_eqn_right by presburger

     have set_y: "length y > 0 \<Longrightarrow> set y = {sy}" using singleton_pow_set y_list_sy by fast
     have set_x: "length x > 0 \<Longrightarrow> set x = {sx}" using singleton_pow_set x_list_sx by fast

     consider (x_empty) "length x = 0 \<and> length y > 0" | (y_empty) "length x > 0 \<and> length y = 0" | (not_empty_both) "length x > 0 \<and> length y > 0" using not_empty by auto
     thus "False"
     proof cases
       case x_empty
       then have not_eq: "count_list (?wxxXyyz) sy \<noteq> count_list ?wxXyz sy " using count_y x_empty by auto
       then have ys_0: "\<And>s. s \<noteq> sy \<longrightarrow> count_list y s = 0" using set_y x_empty by (auto iff:count_list_0_iff[of y sy])
       
       then have cl: "\<exists>c. count_list (?wxxXyyz) c \<noteq> count_list ?wxXyz c \<and> (\<forall>s. s \<noteq> c \<longrightarrow> count_list ?wxxXyyz s = count_list ?wxXyz s)" 
         using x_empty ys_0 not_eq by auto
       
       then show ?thesis using  w_lens_not_in_L[OF wxXyz_in_L cl] wxxXyyz_in_L by auto
     next
       case y_empty
       then have not_eq: "count_list (?wxxXyyz) sx \<noteq> count_list ?wxXyz sx" using count_x y_empty by auto
       have "set x = {sx}" using x_list_sx y_empty nth_mem pow_list_set_if in_pow_list_set pow_list_Nil list.simps(15) by metis
       then have ys_0: "\<And>s. s \<noteq> sx \<longrightarrow> count_list x s = 0" using set_x y_empty by (auto iff:count_list_0_iff[of x sx])
       
       then have cl: "\<exists>c. count_list (?wxxXyyz) c \<noteq> count_list ?wxXyz c \<and> (\<forall>s. s \<noteq> c \<longrightarrow> count_list ?wxxXyyz s = count_list ?wxXyz s)" 
         using y_empty ys_0 not_eq by auto
       
       then show ?thesis using  w_lens_not_in_L[OF wxXyz_in_L cl] wxxXyyz_in_L by auto
     next
       case not_empty_both
       then have sx_sy_not_eq: "sx \<noteq> sy" 
         using not_same_type_symbol sx_obtain sy_obtain by auto
       then have not_eq_sx: "count_list (?wxxXyyz) sx = count_list ?wxXyz sx + length x" 
         using set_x set_y count_x count_y not_empty_both by simp
       then have sx_not_eq: "count_list (?wxxXyyz) sx \<noteq> count_list ?wxXyz sx" using not_empty_both by auto
       from sx_sy_not_eq have not_eq_sy: "count_list (?wxxXyyz) sy = count_list ?wxXyz sy + length y" 
         using set_x set_y count_y not_empty_both count_x by simp
       then have sy_not_eq: "count_list (?wxxXyyz) sy \<noteq> count_list ?wxXyz sy" using not_empty_both by auto

      
       have so_eq: "\<And>s. s \<notin> {sx, sy} \<Longrightarrow>  count_list (?wxxXyyz) s = count_list (?wxXyz) s"
         using set_x set_y count_list_0_iff t.exhaust by fastforce
       then obtain so1 so2 where so1_eq: "count_list (?wxxXyyz) so1 = count_list (?wxXyz) so1" 
                           and   so2_eq: "count_list (?wxxXyyz) so2 = count_list (?wxXyz) so2"
         using t.exhaust empty_iff insert_iff t.distinct(11,3,5) by metis

       consider (nn_mm) "\<exists>n m. (count_list ?wxXyz A = n \<and> count_list ?wxXyz B = n \<and> count_list ?wxXyz C = m \<and> count_list ?wxXyz D = m)" | 
                (n_mm_n) "\<exists>n m. (count_list ?wxXyz A = n \<and> count_list ?wxXyz B = m \<and> count_list ?wxXyz C = m \<and> count_list ?wxXyz D = n)"
         using count_nms by fast
       then show ?thesis
       proof cases
         case nn_mm
         then obtain n m where
                  count_a: "count_list ?wxXyz A = n" 
              and count_b: "count_list ?wxXyz B = n"
              and count_c: "(count_list ?wxXyz C = m)" 
              and count_d: "(count_list ?wxXyz D = m)" 
           by blast
         
         then show ?thesis
           using so_eq counts_or_wxxXyyz lens_not_eq add_left_cancel empty_iff insert_iff 
                less_add_same_cancel1 not_add_less1 not_empty_both not_eq_sx not_eq_sy t.distinct(2,6)
               t.exhaust
           by (smt (verit))
       next
         case n_mm_n
         then obtain n m where
                  count_a: "count_list ?wxXyz A = n" 
              and count_b: "count_list ?wxXyz B = m"
              and count_c: "(count_list ?wxXyz C = m)" 
              and count_d: "(count_list ?wxXyz D = n)" 
           by blast
         
         then show ?thesis
           using so_eq counts_or_wxxXyyz lens_not_eq add_left_cancel empty_iff insert_iff 
                less_add_same_cancel1 not_add_less1 not_empty_both not_eq_sx not_eq_sy t.distinct(2,6)
               t.exhaust
           by (smt (verit))
       qed
     qed
   qed
 qed
qed




lemma derives_more_counts_eq:
  fixes G' :: "('n, t) Cfg" and X :: "'n" and x y :: "t list" 
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
          der_assm: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y"
        shows "(count_list (x @ y) A + count_list (x @ y) C = count_list (x @ y) B + count_list (x @ y) D)"
  apply (cases "(x @ y) = []")
  apply simp
proof -
  let ?xy = "\<lambda>n. (x ^^ n @ y ^^ n)"
  let ?cxy = "\<lambda>n c. count_list (?xy n) c"
  let ?cxy_s = "\<lambda>c. count_list (x @ y) c"
  
  assume not_empty: "(x @ y) \<noteq> []"

  have same_length: "length x = length y" by (rule fact3[OF assms(1,2,3,4)]) 

  let ?xl = "length x"
    
  have ex_one_type_symbol: 
   "(\<exists>s. \<forall>i < length x. (x ! i = s)) \<and> (\<exists>s. \<forall>i < length y. (y ! i = s))"
    by (rule ex_one_symbol[OF usefulG' langG' start_prod der_assm])  

  then obtain sx sy where sx_def: "\<forall>i < length x. x ! i = sx" and sy_def: "\<forall>i < length y. y ! i = sy"     
    using ex_one_type_symbol by blast
  
  
  then have uneq: "sx \<noteq> sy" using fact2[OF assms(1,2,3,4)] not_empty same_length by force
  
  from sx_def sy_def have x_list_sx: "x = [sx] ^^ (length x)" and y_list_sy: "y = [sy] ^^ (length x)" 
    using singleton_power[of x] singleton_power[of y] same_length by auto 

  from x_list_sx y_list_sy have cts: "count_list x sx = ?xl" "count_list y sy = ?xl" 
    using count_list_pow_list[of ?xl "[sx]" sx] count_list_pow_list[of ?xl "[sy]" sy] by auto

  with uneq have csx: "?cxy_s sx = ?xl" and csy: "?cxy_s sy = ?xl" 
    using y_list_sy apply fastforce
    using cts uneq x_list_sx y_list_sy append_Nil count_list.simps(2) count_list_append count_list_pow_list pow_list_Nil by metis

  with x_list_sx y_list_sy have rest_zero: "\<And>c. c \<notin> {sx,sy} \<Longrightarrow> ?cxy_s c = 0" 
    by (metis insert_iff count_list_append pow_list_single count_notin append_self_conv in_set_replicate empty_set)




  have "\<exists>ww xx zz. \<forall>n. (ww @ x ^^ n @ xx @ y ^^ n @ zz) \<in> LangS G'" 
    using derives_more[OF assms(1,3) not_empty assms(4)] by blast
  then obtain ww xx zz where ww_xx_zz_obtain: "\<forall>n. (ww @ x ^^ n @ xx @ y ^^ n @ zz) \<in> L_ambig" using langG' by force
  let ?w_plain = "ww @ xx @ zz"
  let ?w_xy = "ww @ x @ xx @ y @ zz"

  from ww_xx_zz_obtain have "(ww @ x ^^ 0 @ xx @ y ^^ 0 @ zz)  \<in> L_ambig"  by presburger 
  then have "?w_plain \<in> L_ambig" by simp 
  then have counts_eq: "((count_list ?w_plain A = count_list ?w_plain B) \<and> (count_list ?w_plain C = count_list ?w_plain D)) 
          \<or> ((count_list ?w_plain A = count_list ?w_plain D) \<and> (count_list ?w_plain B = count_list ?w_plain C))" 
    by (rule w_len_eq[of ?w_plain])

  from ww_xx_zz_obtain have "(ww @ x ^^ 1 @ xx @ y ^^ 1 @ zz)  \<in> L_ambig" by presburger 
  then have "?w_xy \<in> L_ambig" by simp 
  then have "((count_list ?w_xy A = count_list ?w_xy B) \<and> (count_list ?w_xy C = count_list ?w_xy D)) 
          \<or> ((count_list ?w_xy A = count_list ?w_xy D) \<and> (count_list ?w_xy B = count_list ?w_xy C))" 
    by (rule w_len_eq[of ?w_xy])

  then have counts_eq_xy: "((count_list ?w_plain A + ?cxy_s A = count_list ?w_plain B + ?cxy_s B) \<and> (count_list ?w_plain C + ?cxy_s C = count_list ?w_plain D + ?cxy_s D)) 
          \<or> ((count_list ?w_plain A + ?cxy_s A = count_list ?w_plain D + ?cxy_s D) \<and> (count_list ?w_plain B + ?cxy_s B = count_list ?w_plain C + ?cxy_s C))"
     by fastforce

  from counts_eq consider 
    (w_left) "(count_list ?w_plain A = count_list ?w_plain B) \<and> (count_list ?w_plain C = count_list ?w_plain D)" |
    (w_right) "(count_list ?w_plain A = count_list ?w_plain D) \<and> (count_list ?w_plain B = count_list ?w_plain C)" by auto
  thus acbd_eq: "(?cxy_s A + ?cxy_s C = ?cxy_s B + ?cxy_s D)"
  proof cases
    case w_left
    then obtain n m where nm_obtain: "count_list ?w_plain A = n" "count_list ?w_plain B = n" "count_list ?w_plain C = m" "count_list ?w_plain D = m" 
      by blast
    with counts_eq have "(?cxy_s A = ?cxy_s B \<and> ?cxy_s C = ?cxy_s D) \<or> ((n + ?cxy_s A = m + ?cxy_s D) \<and> (n + ?cxy_s B = m + ?cxy_s C))"
      using add_left_cancel counts_eq_xy by auto
   
    then show ?thesis by linarith
  next
    case w_right
     then obtain n m where nm_obtain: "count_list ?w_plain A = n" "count_list ?w_plain B = m" "count_list ?w_plain C = m" "count_list ?w_plain D = n" 
      by blast
    with counts_eq have "(?cxy_s A = ?cxy_s D \<and> ?cxy_s B = ?cxy_s C) \<or> ((n + ?cxy_s A = m + ?cxy_s B) \<and> (n + ?cxy_s D = m + ?cxy_s C))"
      using add_left_cancel counts_eq_xy by metis

    then show ?thesis by linarith
  qed
qed

  
theorem fact5:
fixes G' :: "('n, t) Cfg"
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
          xy_non_empty_distinct_singleton_pow_lists:  "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y  \<Longrightarrow> \<exists>s1 s2. (s1 \<noteq> s2) \<and> x = [s1] ^^ (length x) \<and>  y = [s2] ^^ (length x)" 
  shows   "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y
          \<Longrightarrow> x \<noteq> [] \<Longrightarrow>
           ((x = [A] ^^ (length x) \<longrightarrow> y = [B] ^^ (length x) \<or> y = [D] ^^ (length x))
             \<and> (x = [B] ^^ (length x) \<longrightarrow> y = [C] ^^ (length x))
             \<and> (x = [C] ^^ (length x) \<longrightarrow> y = [D] ^^ (length x))
             \<and> (x \<noteq> [D] ^^ (length x)))"
proof -
  fix X x y
  assume prod: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y" and empty: "x \<noteq> []"
   
  let ?xy = "\<lambda>n. (x ^^ n @ y ^^ n)"
  let ?cxy = "\<lambda>n c. count_list (?xy n) c"
  let ?cxy_s = "\<lambda>c. count_list (x @ y) c"
  let ?xl = "length x"

  from empty have "\<exists>s1 s2. (s1 \<noteq> s2) \<and> x = [s1] ^^ ?xl \<and> y = [s2] ^^ ?xl"
    using xy_non_empty_distinct_singleton_pow_lists[OF prod] by blast

  then obtain sx sy where s_not_eq: "sx \<noteq> sy" and x_def: "x = [sx] ^^ ?xl" and y_def: "y = [sy] ^^ ?xl" by blast

  then have len: "?xl > 0" using empty by auto 


  then have x_len: "x @ y \<noteq> []" using empty by blast

  have "\<exists>ww zz xx. \<forall>n. ww @ x^^ n @ xx @ y ^^ n @ zz \<in> LangS G'"
    by (rule derives_more[OF usefulG' start_prod x_len prod])
  then obtain ww zz xx where wn_in_L: "\<And>n. ww @ x^^n @ xx @ y^^n @ zz \<in> L_ambig" 
    unfolding langG' by blast
   
  let ?wn = "\<lambda>n. ww @ x^^n @ xx @ y^^n @ zz"
  let ?w1 = "ww @ x @ xx @ y @ zz"
  let ?wrest = "ww @ xx @ zz" 

  from wn_in_L have "?wn 1 \<in> L_ambig"  by presburger 
  then have w1_in_L: "?w1 \<in> L_ambig" by simp 
  then have w1_sorted: "sorted ?w1" using w_sorted by auto
  then have "sorted (x @ y)" 
    by (simp add: sorted_append)
  then have "sx \<le> sy" 
    by (metis in_set_replicate len nth_mem pow_list_single sorted_append x_def y_def) 
  then have sx_less_sy: "sx < sy" using s_not_eq by auto

  from x_def y_def have cts: "count_list x sx = ?xl" "count_list y sy = ?xl"
    using count_list_pow_list[of ?xl "[sx]" sx] count_list_pow_list[of ?xl "[sy]" sy] by auto

  from x_def y_def have rest_zero: "\<And>c. c \<notin> {sx,sy} \<Longrightarrow> ?cxy_s c = 0"
    by (metis insert_iff count_list_append pow_list_single count_notin append_self_conv in_set_replicate empty_set)

  from cts rest_zero have sxy_cts: "?cxy_s sx = ?xl" "?cxy_s sy = ?xl" 
    using s_not_eq y_def apply fastforce
    using cts s_not_eq x_def y_def append_Nil count_list.simps(2) count_list_append count_list_pow_list pow_list_Nil by metis

  
    
  have equation: "(count_list (x @ y) A + count_list (x @ y) C = count_list (x @ y) B + count_list (x @ y) D)"
    by (rule derives_more_counts_eq[OF usefulG' langG' start_prod prod])

  have 
    a_b_d:
    "x = [A] ^^ ?xl \<longrightarrow> y = [B] ^^ ?xl \<or> y = [D] ^^ ?xl"
  proof (rule ccontr)
     assume "\<not> (x = [A] ^^ ?xl \<longrightarrow> y = [B] ^^ ?xl \<or> y = [D] ^^ ?xl)"
     then have xy: "x = [A] ^^ ?xl " "(y \<noteq> [B] ^^ ?xl \<and> y \<noteq> [D] ^^ ?xl)" by auto

     from len x_def y_def have s1A: "sx = A" and "sy \<noteq> B"  and "sy \<noteq> D"
       using xy(1,2) pow_eq_eq list.inject apply (metis) 
       using y_def xy(1,2) by auto

     then have "sy = C" using s_not_eq t.exhaust by blast

     with s1A show False using cts rest_zero equation empty by force
   qed
      
   have 
    b_c:
    "x = [B] ^^ ?xl \<longrightarrow> y = [C] ^^ ?xl"
   proof (rule ccontr)
     assume "\<not> (x = [B] ^^ ?xl \<longrightarrow> y = [C] ^^ ?xl)"
     then have xy: "x = [B] ^^ ?xl " "(y \<noteq> [C] ^^ ?xl)" by auto
     from len x_def y_def have sxB: "sx = B" and synC: "sy \<noteq> C"
       using xy(1,2) pow_eq_eq list.inject apply metis
       using y_def xy(1,2) by auto
     from sx_less_sy have "sy \<noteq> A" using sxB by (auto simp add: less_t_def) 
      
     then have y_is_D :"sy = D" using synC sxB s_not_eq t.exhaust by blast
     with sxB show False using cts equation rest_zero empty by fastforce
   qed

   have 
    c_d:
    "x = [C] ^^ ?xl \<longrightarrow> y = [D] ^^ ?xl"
   proof (rule ccontr)
     assume "\<not> (x = [C] ^^ ?xl \<longrightarrow> y = [D] ^^ ?xl)"
     then have xy: "x = [C] ^^ ?xl " "(y \<noteq> [D] ^^ ?xl)" by auto
     from len x_def y_def have sxB: "sx = C" and synC: "sy \<noteq> D"
       using xy(1,2) pow_eq_eq list.inject apply metis
       using y_def xy(1,2) by auto
     from sx_less_sy have "sy \<noteq> A \<and> sy \<noteq> B" using sxB by (auto simp add: less_t_def) 

     with sxB show False using synC s_not_eq t.exhaust by blast
   qed

   have no_d: "x \<noteq> [D] ^^ ?xl"
   proof (rule ccontr)
     assume "\<not> (x \<noteq> [D] ^^ ?xl)"
     then have xy: "x = [D] ^^ ?xl " by auto
     from len x_def y_def have sxB: "sx = D" 
       using xy pow_eq_eq list.inject by metis

     with sx_less_sy sxB show False using s_not_eq t.exhaust using sxB by (auto simp add: less_t_def) 
   qed
   from a_b_d b_c c_d no_d show "((x = [A] ^^ ?xl \<longrightarrow> y = [B] ^^ ?xl \<or> y = [D] ^^ ?xl)
            \<and> (x = [B] ^^ ?xl \<longrightarrow> y = [C] ^^ ?xl)
            \<and> (x = [C] ^^ ?xl \<longrightarrow> y = [D] ^^ ?xl)
            \<and> (x \<noteq> [D] ^^ ?xl))" by auto
 qed



theorem fact5_classes:
fixes G' :: "('n, t) Cfg"
assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
        aXb: "(\<forall>X. X \<noteq> (Start G') \<and> X \<in> Nts (Prods G') \<longrightarrow> (\<exists>x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y \<and> x @ y \<noteq> []))" and
         langG': "LangS G' = L_ambig" and
         start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
         xy_non_empty_distinct_singleton_pow_lists:  "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y  \<Longrightarrow> \<exists>s1 s2. (s1 \<noteq> s2) \<and> x = [s1] ^^ (length x) \<and>  y = [s2] ^^ (length x)" 
  shows  "\<And>X. X \<noteq> (Start G') \<Longrightarrow> X \<in> Nts (Prods G') \<Longrightarrow> X \<in> Cab G' \<or>  X \<in> Cad G' \<or> X \<in> Cbc G' \<or> X \<in> Ccd G'"
proof -
  fix X
  assume x_not_S: "X \<noteq> (Start G')" and x_Nt: "X \<in> Nts (Prods G')"
  then have "useful (Prods G') (Start G') X" using usefulG' by auto

  from aXb x_not_S x_Nt obtain x y where prod: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y" and not_empty: "x @ y \<noteq> []" by blast
  let ?xl = "length x"

  have "?xl = length y" by (rule fact3[OF usefulG' langG' start_prod prod])

  then have x_not_empty: "x \<noteq> []" using not_empty by auto 
  then have xl_g_0: "?xl > 0" by simp
    
  have 5: "(x = [A] ^^ length x \<longrightarrow> y = [B] ^^ length x \<or> y = [D] ^^ length x) \<and> (x = [B] ^^ length x \<longrightarrow> y = [C] ^^ length x) \<and> (x = [C] ^^ length x \<longrightarrow> y = [D] ^^ length x) \<and> x \<noteq> [D] ^^ length x"
    by (rule fact5[OF usefulG' langG' start_prod xy_non_empty_distinct_singleton_pow_lists prod x_not_empty])
  then have "(x = [A] ^^ ?xl \<and> y = [B] ^^ ?xl) \<or> (x = [A] ^^ ?xl \<and> y = [D] ^^ ?xl) \<or> (x = [B] ^^ ?xl \<and> y = [C] ^^ ?xl) \<or> (x = [C] ^^ ?xl \<and> y = [D] ^^ ?xl)"
    by (metis (no_types, lifting) assms(5) prod t.exhaust)
  then have "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm ([A] ^^ ?xl) @ [Nt X] @ map Tm ([B] ^^ ?xl) \<or> (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm ([A] ^^ ?xl) @ [Nt X] @ map Tm ([D] ^^ ?xl) 
           \<or> (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm ([B] ^^ ?xl) @ [Nt X] @ map Tm ([C] ^^ ?xl) \<or> (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm ([C] ^^ ?xl) @ [Nt X] @ map Tm ([D] ^^ ?xl)" 
    using prod by presburger  
  then show "X \<in> Cab G' \<or>  X \<in> Cad G' \<or> X \<in> Cbc G' \<or> X \<in> Ccd G'" by (auto iff: xl_g_0)
qed


lemma derives_short:
  fixes G' :: "('n, t) Cfg" and X Y :: "'n" and x y :: "t list" 
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
          prod: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" "(Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta>" "(Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w"  and
          pump: "Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm [c1] ^^ l1 @ [Nt X] @ map Tm [c2] ^^ l1" "Prods G' \<turnstile> [Nt Y] \<Rightarrow>* map Tm [c3] ^^ l2 @ [Nt Y] @ map Tm [c4] ^^ l2" "l1 > 0 " "l2 > 0"
  
shows "\<exists>w1. w1 \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m}) \<union> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n}) \<and>  
             (\<forall>k l. \<exists>w2. w2 \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m}) \<union> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n}) \<and> 
               (\<forall>ch. count_list w2 ch = count_list w1 ch + k * count_list ([c1] ^^ l1) ch + k * count_list ([c2] ^^ l1) ch
             + l * count_list ([c3] ^^ l2) ch + l * count_list ([c4] ^^ l2) ch))"
proof -
  let ?P = "Prods G'"  let ?S = "[Nt (Start G')]"
  let ?x = "map Tm [c1] ^^ l1" let ?y = "map Tm [c2] ^^ l1"
  let ?x' = "map Tm [c3] ^^ l2" let ?y' = "map Tm [c4] ^^ l2"
  let ?xx = "[c1] ^^ l1"  let ?yy = "[c2] ^^ l1"
  let ?xx' = "[c3] ^^ l2" let ?yy' = "[c4] ^^ l2"

  have x_pump_k:
    "\<And>k. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* (?x) ^^ k  @ [Nt X] @ (?y) ^^ k"
    using derives_forever[OF pump(1)] by simp

  have y_pump_k:
    "\<And>l. (Prods G') \<turnstile> [Nt Y] \<Rightarrow>* (?x') ^^ l  @ [Nt Y] @ (?y') ^^ l"
    using derives_forever[OF pump(2)] by simp

  have x_pump_1: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* ?x @ [Nt X] @ ?y" 
    using derives_forever[OF pump(1), of 1] by auto

  have deriv: 
    "\<And>k. (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta>"
    using derives_prepend[OF derives_append[OF x_pump_k, of \<beta>], of \<alpha>] by simp
  with prod(1) have 
    x_pump_k_from_s: "\<And>k l. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta>"
    by (meson rtranclp_trans)

  have a_deriv: "\<exists>aa. (Prods G') \<turnstile> \<alpha> \<Rightarrow>* map Tm aa" 
    and rest_deriv: "\<And>k. \<exists>xx. (Prods G') \<turnstile> (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta> \<Rightarrow>* map Tm xx"
    using derives_useful_list_partial[OF start_prod usefulG'] x_pump_k_from_s by auto

  then have xx_bb_derivs: "\<exists>xx bb. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm xx \<and> (Prods G') \<turnstile> \<beta> \<Rightarrow>* map Tm bb" 
    using derives_append_map_Tm by meson
        
  with a_deriv obtain aa xx bb where
      aa: "(Prods G') \<turnstile> \<alpha> \<Rightarrow>* map Tm aa" and 
      xx: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm xx" and 
      bb: "(Prods G') \<turnstile> \<beta> \<Rightarrow>* map Tm bb" by blast

  from derive_decomp2[OF prod(2)]  
  obtain \<kappa> \<mu> where 
    "Prods G' \<turnstile> \<alpha> \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu> \<or>
     Prods G' \<turnstile> \<beta> \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu> \<or>
     Prods G' \<turnstile> [Nt X] \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu>" by blast
  then consider 
    (y_in_alpha) "?P \<turnstile> \<alpha> \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu>" |
    (y_in_X) "?P \<turnstile> [Nt X] \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu>" | 
    (y_in_beta) "?P \<turnstile> \<beta> \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu>"
    by blast
  then show "\<exists>w1. w1 \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m}) \<union> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n}) 
             \<and> (\<forall>k l. \<exists>w2. w2 \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m}) \<union> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n}) \<and> 
               (\<forall>ch. count_list w2 ch = count_list w1 ch + k * count_list ([c1] ^^ l1) ch + k * count_list ([c2] ^^ l1) ch
             + l * count_list ([c3] ^^ l2) ch + l * count_list ([c4] ^^ l2) ch))"
  proof (cases)
    case y_in_alpha
    have to_1: "?P \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu> @ [Nt X] @ \<beta>"
      using derives_append[OF y_in_alpha] by force
    then have s_to_1: "?P \<turnstile> ?S \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu> @ [Nt X] @ \<beta>" 
      using prod(1) by auto
    then obtain kk yy mm where
         kk: "?P \<turnstile> \<kappa> \<Rightarrow>* map Tm kk" and 
         yy: "?P \<turnstile> [Nt Y] \<Rightarrow>* map Tm yy" and 
         mm: "?P \<turnstile> \<mu> \<Rightarrow>* map Tm mm"
      using derives_useful_list_partial[OF start_prod usefulG'] derives_append_map_Tm
      by meson
    with s_to_1 have "?P \<turnstile> ?S \<Rightarrow>* map Tm (kk @ yy @ mm @ xx @ bb)"
      using derives_append_append[OF 
              derives_append_append[OF 
                derives_append_append[OF kk yy] 
                derives_append_append[OF mm xx]] 
             bb]
      by simp
    then have w1_in_L: "kk @ yy @ mm @ xx @ bb \<in> L_ambig" 
      using Lang_def[of ?P "Start G'"] langG' by auto
         
    let ?w1 = "kk @ yy @ mm @ xx @ bb"
    let ?w2 = "\<lambda>k l. kk @ (?xx') ^^ l @ yy @ (?yy') ^^ l @ mm @ (?xx) ^^ k @ xx @ (?yy) ^^ k @ bb"
        
    have der2: "\<And>k. ?P \<turnstile> \<alpha> @ (?x) ^^ k @ [Nt X] @  (?y) ^^ k  @ \<beta> \<Rightarrow>* \<kappa> @ [Nt Y] @ \<mu> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta>"
      using derives_append[OF y_in_alpha] by simp
    then have der1: "\<And>k. ?P \<turnstile> \<kappa> @ [Nt Y] @ \<mu> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta> \<Rightarrow>* \<kappa> @ (?x') ^^ l  @ [Nt Y] @ (?y') ^^ l @ \<mu> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta>"
      using derives_prepend[OF derives_append[OF y_pump_k], of "\<kappa>"] by simp

    then have der3: "\<And>k l. ?P \<turnstile> \<kappa> @ (?x') ^^ l  @ [Nt Y] @ (?y') ^^ l @ \<mu> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta> 
                            \<Rightarrow>* map Tm (?w2 k l)"
      using derives_append_append[OF 
                derives_append_append[OF 
                   derives_append_append[OF 
                      derives_append_append[OF 
                          kk derives_prepend[OF yy]] 
                          derives_prepend[OF mm]] 
                      derives_prepend[OF xx]] 
                   derives_prepend[OF bb]] 
       by simp
   with x_pump_k_from_s have 
        "\<And>k l. ?P \<turnstile> ?S \<Rightarrow>* map Tm (?w2 k l)"
     using der1 der2 append.assoc derives_append derives_prepend rtranclp_trans
       y_pump_k
     by (smt (verit, ccfv_threshold))

   then have w2_in_L: "\<And>k l. ?w2 k l \<in> L_ambig" 
     using Lang_def[of ?P "Start G'"] langG' by simp

   have cg: "\<And>k l. \<forall>ch. count_list (?w2 k l) ch =
          count_list ?w1 ch + count_list ((?xx') ^^ l) ch + count_list ((?yy') ^^ l) ch
        + count_list ((?xx) ^^ k) ch + count_list ((?yy) ^^ k) ch" 
      by auto
   then have counts:
      "\<And>k l. \<forall>ch. count_list (?w2 k l) ch =
          count_list ?w1 ch + l * count_list (?xx') ch + l * count_list (?yy') ch
        + k * count_list (?xx) ch + k * count_list (?yy) ch" 
     using count_list_pow_list by metis

  show ?thesis
     apply (rule exI[of _ "?w1"]; rule conjI) 
     using w1_in_L apply fast
     proof (rule allI; rule allI)
       fix k l 
       show "\<exists>w2. w2 \<in> L_ambig \<and> (\<forall>ch.
               count_list w2 ch = count_list ?w1 ch + k * count_list ?xx ch + k * count_list ?yy ch
             + l * count_list ?xx' ch + l * count_list ?yy' ch)"
         apply (rule exI[of _ "?w2 k l"]; rule conjI)
         using w2_in_L apply simp
         using counts by force
     qed
 next
   case y_in_X
   have to_1: "?P \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<alpha> @ \<kappa> @ [Nt Y] @ \<mu> @ \<beta>"
     using derives_prepend[OF derives_append[OF y_in_X]] by simp
   then have s_to_1: "?P \<turnstile> ?S \<Rightarrow>* \<alpha> @ \<kappa> @ [Nt Y] @ \<mu> @ \<beta>" 
     using prod(1) by auto
   then obtain kk yy mm where
     kk: "?P \<turnstile> \<kappa> \<Rightarrow>* map Tm kk" and 
     yy: "?P \<turnstile> [Nt Y] \<Rightarrow>* map Tm yy" and 
     mm: "?P \<turnstile> \<mu> \<Rightarrow>* map Tm mm"
    using derives_useful_list_partial[OF start_prod usefulG'] derives_append_map_Tm
      by meson
   with s_to_1 have "?P \<turnstile> ?S \<Rightarrow>* map Tm (aa @ kk @ yy @ mm @ bb)"
     using derives_append_append[OF 
             derives_append_append[OF 
               derives_append_append[OF aa kk] 
               derives_append_append[OF yy mm]] 
           bb]
     by simp
   then have w1_in_L: "aa @ kk @ yy @ mm @ bb \<in> L_ambig" 
     using Lang_def[of ?P "Start G'"] langG' by auto
         
   let ?w1 = "aa @ kk @ yy @ mm @ bb" 
   let ?w2 = "\<lambda>k l. aa @ (?xx) ^^ k @ kk @ (?xx') ^^ l @ yy @ (?yy') ^^ l @ mm @ (?yy) ^^ k @ bb"
        
   have der2: "\<And>k l. ?P \<turnstile> \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta> \<Rightarrow>* \<alpha> @ (?x) ^^ k @ \<kappa> @ [Nt Y] @ \<mu> @ (?y) ^^ k @ \<beta>"
    using derives_prepend[OF derives_append[OF y_in_X]] append.assoc by metis   

   then have der1: "\<And>k l. ?P \<turnstile> \<alpha> @ (?x) ^^ k @ \<kappa> @ [Nt Y] @ \<mu> @ (?y) ^^ k @ \<beta> \<Rightarrow>* \<alpha> @ (?x) ^^ k @ \<kappa> @ (?x') ^^ l @ [Nt Y] @ (?y') ^^ l @ \<mu> @ (?y) ^^ k @ \<beta>"
     using derives_prepend[OF derives_append[OF y_pump_k]] append.assoc by metis   

   then have der3: "\<And>k l. ?P \<turnstile> \<alpha> @ (?x) ^^ k @ \<kappa> @ (?x') ^^ l @ [Nt Y] @ (?y') ^^ l @ \<mu> @ (?y) ^^ k @ \<beta> \<Rightarrow>* map Tm (?w2 k l)"
     using derives_append_append[OF 
             derives_append[OF aa] 
             derives_append_append[OF 
               derives_append[OF kk] 
               derives_append_append[OF 
                 derives_append[OF yy]
                 derives_append_append[OF 
                   derives_append[OF mm]
                   bb ]]]]                                  
     by simp

   with x_pump_k_from_s have 
        "\<And>k l. ?P \<turnstile> ?S \<Rightarrow>* map Tm (?w2 k l)"
     using der1 der2 rtranclp_trans
     by meson

   then have w2_in_L: "\<And>k l. ?w2 k l \<in> L_ambig" 
     using Lang_def[of ?P "Start G'"] langG' by auto

   have cg: "\<And>k l. \<forall>ch. count_list (?w2 k l) ch =
          count_list ?w1 ch + count_list ((?xx') ^^ l) ch + count_list ((?yy') ^^ l) ch
        + count_list ((?xx) ^^ k) ch + count_list ((?yy) ^^ k) ch" 
      by auto
   then have counts:
      "\<And>k l. \<forall>ch. count_list (?w2 k l) ch =
          count_list ?w1 ch + l * count_list (?xx') ch + l * count_list (?yy') ch
        + k * count_list (?xx) ch + k * count_list (?yy) ch" 
     using count_list_pow_list by metis

  show ?thesis
     apply (rule exI[of _ "?w1"]; rule conjI) 
     using w1_in_L apply fast
     proof (rule allI; rule allI)
       fix k l 
       show "\<exists>w2. w2 \<in> L_ambig \<and> (\<forall>ch.
               count_list w2 ch = count_list ?w1 ch + k * count_list ?xx ch + k * count_list ?yy ch
             + l * count_list ?xx' ch + l * count_list ?yy' ch)"
         apply (rule exI[of _ "?w2 k l"]; rule conjI)
         using w2_in_L apply simp
         using counts by force
     qed
 next
   case y_in_beta
   have to_1: "?P \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<alpha> @ [Nt X] @ \<kappa> @ [Nt Y] @ \<mu>"
     using derives_prepend[OF y_in_beta, of "\<alpha> @ [Nt X]"] by force
   then have s_to_1: "?P \<turnstile> ?S \<Rightarrow>* \<alpha> @ [Nt X] @ \<kappa> @ [Nt Y] @ \<mu>" 
     using prod(1) by auto
   then obtain kk yy mm where
       kk: "?P \<turnstile> \<kappa> \<Rightarrow>* map Tm kk" and 
       yy: "?P \<turnstile> [Nt Y] \<Rightarrow>* map Tm yy" and 
       mm: "?P \<turnstile> \<mu> \<Rightarrow>* map Tm mm"
     using derives_useful_list_partial[OF start_prod usefulG'] derives_append_map_Tm
     by meson
   with s_to_1 have "?P \<turnstile> ?S \<Rightarrow>* map Tm (aa @ xx @ kk @ yy @ mm)"
      using derives_append_append[OF 
              derives_append_append[OF 
                derives_append_append[OF aa xx] 
                  derives_append_append[OF kk yy]] 
            mm]
      by simp
   then have w1_in_L: "aa @ xx @ kk @ yy @ mm \<in> L_ambig" 
      using Lang_def[of ?P "Start G'"] langG' by simp
         
   let ?w1 = "aa @ xx @ kk @ yy @ mm"
   let ?w2 = "\<lambda>k l. aa @ (?xx) ^^ k @ xx @ (?yy) ^^ k @ kk @ (?xx') ^^ l @ yy @ (?yy') ^^ l @ mm"
        
   have der2: "\<And>k l. ?P \<turnstile> \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<beta> \<Rightarrow>* \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<kappa> @ [Nt Y] @ \<mu>"
     using derives_prepend[OF y_in_beta] derives_prepend by blast

   then have der1: "\<And>k l. ?P \<turnstile> \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<kappa> @ [Nt Y] @ \<mu> \<Rightarrow>* \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<kappa> @ (?x') ^^ l @ [Nt Y] @ (?y') ^^ l @ \<mu>"
     using derives_prepend[OF derives_append[OF y_pump_k, of "\<mu>"]] 
     by (metis append.assoc)

   then have der3: "\<And>k l. ?P \<turnstile> \<alpha> @ (?x) ^^ k @ [Nt X] @ (?y) ^^ k @ \<kappa> @ (?x') ^^ l @ [Nt Y] @ (?y') ^^ l @ \<mu> \<Rightarrow>* map Tm (?w2 k l)"
     using derives_append_append[OF 
             derives_append_append[OF 
               derives_append_append[OF 
                 derives_append_append[OF 
                   aa derives_prepend[OF xx]] 
                 derives_prepend[OF kk]] 
             derives_prepend[OF yy]] 
          derives_prepend[OF mm]] 
     by simp
   with x_pump_k_from_s have 
      "\<And>k l. ?P \<turnstile> ?S \<Rightarrow>* map Tm (?w2 k l)"
     using der1 der2 rtranclp_trans
     by meson

   then have w2_in_L: "\<And>k l. ?w2 k l \<in> L_ambig" 
     using Lang_def[of ?P "Start G'"] langG' by simp

    have cg: "\<And>k l. \<forall>ch. count_list (?w2 k l) ch =
          count_list ?w1 ch + count_list ((?xx') ^^ l) ch + count_list ((?yy') ^^ l) ch
        + count_list ((?xx) ^^ k) ch + count_list ((?yy) ^^ k) ch" 
      by auto
   then have counts:
      "\<And>k l. \<forall>ch. count_list (?w2 k l) ch =
          count_list ?w1 ch + l * count_list (?xx') ch + l * count_list (?yy') ch
        + k * count_list (?xx) ch + k * count_list (?yy) ch" 
     using count_list_pow_list by metis

  show ?thesis
     apply (rule exI[of _ "?w1"]; rule conjI) 
     using w1_in_L apply fast
     proof (rule allI; rule allI)
       fix k l 
       show "\<exists>w2. w2 \<in> L_ambig \<and> (\<forall>ch.
               count_list w2 ch = count_list ?w1 ch + k * count_list ?xx ch + k * count_list ?yy ch
             + l * count_list ?xx' ch + l * count_list ?yy' ch)"
         apply (rule exI[of _ "?w2 k l"]; rule conjI)
         using w2_in_L apply simp
         using counts by force
     qed
 qed
qed



lemma fact6:
  fixes G' :: "('n, t) Cfg" and X Y :: "'n" and x y :: "t list" 
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          langG': "LangS G' = L_ambig" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
          disjoints_double: "(Cab G' \<union> Ccd G') \<inter> (Cad G' \<union> Cbc G') = {}"
   shows
     "\<And>\<alpha> \<beta> \<gamma> \<delta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta> 
          \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta> \<Longrightarrow> (Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w 
          \<Longrightarrow> (X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<notin> Cad G' \<union> Cbc G') \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<notin> Cab G' \<union> Ccd G')"
proof -
  fix \<alpha> \<beta> \<gamma> \<delta>
  assume prod: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" "(Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta>" "(Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w"
  
  show "(X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<notin> Cad G' \<union> Cbc G') \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<notin> Cab G' \<union> Ccd G')"
  proof (rule ccontr)
    assume not: "\<not>((X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<notin> Cad G' \<union> Cbc G') \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<notin> Cab G' \<union> Ccd G'))"
    then have "(X \<in> Cab G' \<union> Ccd G' \<and> Y \<in> Cad G' \<union> Cbc G') \<or> (X \<in> Cad G' \<union> Cbc G' \<and> Y \<in> Cab G' \<union> Ccd G') "
      by auto
    then have "\<exists>c1 c2 c3 c4. X \<in> C_set c1 c2 G' \<and> Y \<in> C_set c3 c4 G' \<and> c1 \<noteq> c2 \<and> c3 \<noteq> c4 \<and> (\<exists>cc. {c1, c2} \<inter> {c3, c4} = {cc})" 
      using t.exhaust t.distinct by blast

    then obtain c1 c2 c3 c4 cc where c_s_obtain: "X \<in> C_set c1 c2 G'" "Y \<in> C_set c3 c4 G'" "c1 \<noteq> c2" "c3 \<noteq> c4" "{c1, c2} \<inter> {c3, c4} = {cc}"
      by blast
    then have ors: "(c1 = c3 \<and> cc = c1) \<or> (c2 = c3 \<and> cc = c2) \<or> (c1 = c4 \<and> cc = c1) \<or> (c2 = c4 \<and> cc = c2)" by fast

  
    then obtain cc2 cc3 where   
        three_elems: "{c1, c2, c3, c4} = {cc, cc2, cc3}" and
        neqs: "cc \<noteq> cc2" "cc2 \<noteq> cc3" "cc \<noteq> cc3" 
      using c_s_obtain by blast 


    then obtain c where c_neq_anything: "c \<noteq> c1 \<and> c \<noteq> c2 \<and> c \<noteq> c3 \<and> c \<noteq> c4" 
      using ors t.distinct(1,11,3,5,7,9) by (smt (verit, best))

    from c_s_obtain obtain l1 l2 where l_obtain: "Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm [c1] ^^ l1 @ [Nt X] @ map Tm [c2] ^^ l1" "Prods G' \<turnstile> [Nt Y] \<Rightarrow>* map Tm [c3] ^^ l2 @ [Nt Y] @ map Tm [c4] ^^ l2" "l1 > 0 " "l2 > 0"
      by blast

    let ?P = "Prods G'"  let ?S = "[Nt (Start G')]"
    let ?x = "map Tm [c1] ^^ l1" let ?y = "map Tm [c2] ^^ l1"
    let ?x' = "map Tm [c3] ^^ l2" let ?y' = "map Tm [c4] ^^ l2"
    let ?xx = "[c1] ^^ l1"  let ?yy = "[c2] ^^ l1"
    let ?xx' = "[c3] ^^ l2" let ?yy' = "[c4] ^^ l2"
    let ?c = "\<lambda>w c. count_list w c" let ?cw1 = "\<lambda>w c. count_list w c" 
    let ?l = "\<lambda>w. length w"
        
    have xx'_cs: "count_list ?xx' c3 = l2" "\<And>c. c \<noteq> c3 \<Longrightarrow> count_list ?xx' c = 0" and
         xx_cs: "count_list ?xx c1 = l1" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?xx c = 0" and
         yy'_cs: "count_list ?yy' c4 = l2" "\<And>c. c \<noteq> c4 \<Longrightarrow> count_list ?yy' c = 0" and
         yy_cs: "count_list ?yy c2 = l1" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?yy c = 0" 
      using count_list_pow_list[of l2 "[c3]"] count_list_pow_list[of l1 "[c1]"] 
            count_list_pow_list[of l2 "[c4]"] count_list_pow_list[of l1 "[c2]"] by auto

    have words: "\<exists>w1. w1 \<in> L_ambig \<and>  
             (\<forall>k l. \<exists>w2. w2 \<in> L_ambig \<and> 
               (\<forall>ch. ?c w2 ch = ?c w1 ch + k * ?c ?xx ch + k * ?c ?yy ch
             + l * ?c ?xx' ch + l * ?c ?yy' ch))"
      using derives_short[OF usefulG' langG'  start_prod prod l_obtain]
      by simp
    
    then obtain wk1 where wk1_in_L: "wk1 \<in> L_ambig" and
         c_counts: 
          "\<And>k l. \<exists>w2. w2 \<in> L_ambig \<and> 
               (\<forall>ch. ?c w2 ch = ?c wk1 ch + k * ?c ?xx ch + k * ?c ?yy ch
             + l * ?c ?xx' ch + l * ?c ?yy' ch)" by force
    
    let ?s = "(?l wk1 + 1)"

    obtain wk2 where wk2_in_L: "wk2 \<in> L_ambig" and
               "(\<forall>ch. ?c wk2 ch = ?c wk1 ch + ?s * ?c ?xx ch + ?s * ?c ?yy ch
             + ?s * ?c ?xx' ch + ?s * ?c ?yy' ch)" 
      using c_counts[of "?s" "?s"] by force

    
    (* Express w2 counts entirely in terms of w1 counts + l1/l2 values *)
    then have w2_counts_expanded: "\<And>ch. count_list wk2 ch = count_list wk1 ch + 
      ?s * (if ch = c1 then l1 else 0) + ?s * (if ch = c2 then l1 else 0) + 
      ?s * (if ch = c3 then l2 else 0) + ?s * (if ch = c4 then l2 else 0)"
      using xx'_cs xx_cs yy_cs yy'_cs by presburger

    have sl1: "?s * l1 \<ge> ?s" 
      using l_obtain(3) nat_mult_le_cancel1[of "?s" "1" "l1"] by simp
    have sl2: "?s * l2 \<ge> ?s" 
      using l_obtain(4) nat_mult_le_cancel1[of "?s" "1" "l2"] by simp
    

    have cls: "count_list wk1 c < ?s" using count_le_length less_eq_iff_succ_less by fast

    have c1: "count_list wk2 cc \<ge> count_list wk1 cc + ?s" 
      using c_neq_anything w2_counts_expanded l_obtain(3,4) three_elems sl1 sl2 by auto
    have c2: "count_list wk2 cc2 \<ge> count_list wk1 cc2 + ?s" 
      using c_neq_anything w2_counts_expanded l_obtain(3,4) three_elems sl1 sl2 by auto
    have c3: "count_list wk2 cc3 \<ge> count_list wk1 cc3 + ?s" 
      using c_neq_anything w2_counts_expanded l_obtain(3,4) three_elems sl1 sl2 by auto
   

    have c_c: "count_list wk2 c = count_list wk1 c" 
      using c_neq_anything w2_counts_expanded by simp
    then have c_less_cc: "count_list wk2 c \<noteq> count_list wk2 cc"
          and c_less_c2: "count_list wk2 c \<noteq> count_list wk2 cc2"
          and c_less_c3: "count_list wk2 c \<noteq> count_list wk2 cc3"
      using c_c c1 c2 c3 cls by auto

    then have forall: "\<forall>c' \<noteq> c. count_list wk2 c \<noteq> count_list wk2 c'"
      using neqs t.exhaust by (smt (verit))
    
    have "wk2 \<notin> L_ambig" 
      by (rule w_len_not_eq[OF exI[of "\<lambda>c. \<forall>c' \<noteq> c. count_list wk2 c \<noteq> count_list wk2 c'" c, OF forall]])
    
    then show False using wk2_in_L by simp
  qed
qed






notation (input) P_left ("P_left")
declare [[show_abbrevs = true]]

text "We start our proof."

theorem
  assumes cfl: "CFL TYPE('n) L_ambig"
  shows "inherently_ambiguous_type TYPE('n) L_ambig"
proof (rule ccontr)

  
  text "Assume that there is an unambiguous grammar generating \<open>L_ambig\<close>."
  assume asm: "\<not> (inherently_ambiguous_type TYPE('n) L_ambig)"
    
  then obtain G :: "('n, t) Cfg" where 
    G_obtain: "LangS G = L_ambig" "\<not>ambiguous G" 
    using asm 
    by blast
     
  text "By Lemma 4.6 we can construct an unambiguous grammar \<open>G'\<close> generating \<open>L_ambig\<close> with no useless symbols,
       and for each \<open>X\<close> in \<open>V-{S}\<close>, \<open>A \<Rightarrow>* xAy\<close> for some \<open>x\<close> and \<open>y\<close> in \<open>\<Sigma>*\<close>, not both \<open>\<epsilon>\<close>."
  then obtain G' :: "('n, t) Cfg" where 
    G'_obtain: "LangS G = LangS G'" "\<not>ambiguous G'" 
               "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" 
               "(\<forall>X. X \<noteq> (Start G') \<and> X \<in> Nts (Prods G') \<longrightarrow>  
                  (\<exists>x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y \<and> x @ y \<noteq> []))"
    using lemma46[OF G_obtain(2)] by auto
    
  then have langG': "LangS G' = L_ambig" using G_obtain by auto

  then obtain w where "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" 
    unfolding Lang_def by blast

  then have start_prod: "\<exists>x. (Start G', x) \<in> Prods G'" 
    using derives_Nt_map_TmD[of \<open>Prods G'\<close> \<open>Start G'\<close>] by blast

  then have start_prod2: "\<exists>(S,x)\<in>Prods G'. S = Start G'" by auto

  text "We note that the grammar \<open>G'\<close> has following properties:"

  text "1) If \<open>X \<Rightarrow>* xXy\<close>, then \<open>x\<close> and \<open>y\<close> consist of only one type of symbol (\<open>a\<close> or \<open>b\<close> or \<open>c\<close> or \<open>d\<close>)."
  have one_type_symbol: 
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> (\<forall>i < length x. \<forall>j < length x. (x ! i = x !j)) \<and> (\<forall>i < length y. \<forall>j < length y. y ! i = y !j)"
    using fact1[OF G'_obtain(3) langG' start_prod2] by meson
    
  then have ex_one_type_symbol:
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> (\<exists>s. \<forall>i < length x. (x ! i = s)) \<and> (\<exists>s. \<forall>i < length y. (y ! i = s))" 
    by meson
  
  then have xy_singleton_pow_lists:
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> \<exists>s1 s2. x = [s1] ^^ (length x) \<and>  y = [s2] ^^ (length y)" 
    using singleton_power by meson


  text "2) If \<open>X \<Rightarrow>* xXy\<close>, then \<open>x\<close> and \<open>y\<close> consist of different symbols."
  have different_type_symbol: 
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> \<forall>i < length x. \<forall>j < length y. (x ! i \<noteq> y !j)"
    using fact2[OF G'_obtain(3) langG' start_prod2] by auto

  then have xy_distinct_singleton_pow_lists:
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> \<exists>s1 s2. ((x \<noteq> [] \<and> y \<noteq> []) \<longrightarrow> s1 \<noteq> s2) \<and> x = [s1] ^^ (length x) \<and>  y = [s2] ^^ (length y)" 
    using xy_singleton_pow_lists bot_nat_0.not_eq_extremum length_0_conv nth_pow_list_single
      by metis

  text "3) If \<open>X \<Rightarrow>* xXy\<close>, then \<open>length x = length y\<close>."
  have same_length: 
    "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
       \<Longrightarrow> length x = length y" 
    using fact3[OF G'_obtain(3) langG' start_prod2] by auto
 
  then have xy_non_empty_distinct_singleton_pow_lists:
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> \<exists>s1 s2. (s1 \<noteq> s2) \<and> x = [s1] ^^ (length x) \<and>  y = [s2] ^^ (length x)" 
    using xy_distinct_singleton_pow_lists 
    by fastforce

  then have xy_non_empty_distinct_singleton_pow_lists2:
    "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
       \<Longrightarrow> \<exists>s1 s2 l. l = 0 \<or> ((s1 \<noteq> s2) \<and> x = [s1] ^^ l \<and> y = [s2] ^^ l)"
    by blast
  

  have "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> (count_list (x @ y) A + count_list (x @ y) C = count_list (x @ y) B + count_list (x @ y) D)" 
    by (rule derives_more_counts_eq[OF G'_obtain(3) langG' start_prod2])


  text "5) If \<open>X \<Rightarrow>* xXy\<close>, then either 
          5.1) \<open>x\<close> consists solely of \<open>a\<close>'s and \<open>y\<close> solely of \<open>b\<close>'s or of \<open>d\<close>'s,
          5.2) \<open>x\<close> consists solely of \<open>b\<close>'s and \<open>y\<close> solely of \<open>c\<close>'s, or
          5.3) \<open>x\<close> consists solely of \<open>c\<close>'s and \<open>y\<close> solely of \<open>d\<close>'s.
        In any other cases (namely \<open>x\<close> consisting solely of \<open>d\<close>'s, the string is not in \<open>L\<close>.)"
  have consists: 
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y
       \<Longrightarrow> x \<noteq> [] \<Longrightarrow>
           ((x = [A] ^^ (length x) \<longrightarrow> y = [B] ^^ (length x) \<or> y = [D] ^^ (length x))
             \<and> (x = [B] ^^ (length x) \<longrightarrow> y = [C] ^^ (length x))
             \<and> (x = [C] ^^ (length x) \<longrightarrow> y = [D] ^^ (length x))
             \<and> (x \<noteq> [D] ^^ (length x)))" 
  by (rule fact5[OF G'_obtain(3) langG' start_prod2 xy_non_empty_distinct_singleton_pow_lists])
  
  have classes:
     "\<And>X. X \<in> Nts (Prods G') \<Longrightarrow> X \<noteq> (Start G') \<Longrightarrow> X \<in> Cab G' \<or>  X \<in> Cad G' \<or> X \<in> Cbc G' \<or> X \<in> Ccd G'" 
  by (rule fact5_classes[OF G'_obtain(3,4) langG' start_prod2 xy_non_empty_distinct_singleton_pow_lists])

  have c_c: "{(Start G')} \<union> Cab G' \<union> Cad G' \<union> Cbc G' \<union> Ccd G' = Nts (Prods G')"
    by (rule classes_complete[OF start_prod2 classes])

  have disjoints_classes: 
      "Cab G' \<inter> Cad G' = {} \<and> Cab G' \<inter> Cbc G' = {} \<and> Cab G' \<inter> Ccd G' = {} \<and> Cad G' \<inter> Cbc G' = {} \<and> Cad G' \<inter> Ccd G' = {} \<and> Cbc G' \<inter> Ccd G' = {}"
    using disjoints[OF xy_non_empty_distinct_singleton_pow_lists, of G' "\<lambda>x _ _. x"] by fastforce

  then have disjoint_double: "(Cab G' \<union> Ccd G') \<inter> (Cad G' \<union> Cbc G') = {}" by (auto simp only: Int_Un_distrib)

  have "Nts (Prods G') - (Cad G' \<union> Cbc G') \<subseteq> Cab G' \<union> Ccd G' \<union> {Start G'}"
    using c_c by auto
  have "Nts (Prods G') - (Cab G' \<union> Ccd G') \<subseteq> Cad G' \<union> Cbc G' \<union> {Start G'}"
    using c_c by auto

  have start_not: "Start G' \<notin> Cab G' \<union> Ccd G' \<union> Cad G' \<union> Cbc G'"
    by (rule start_not_in_classes[OF langG'])

  text "6) A derivation containing a symbol in \<open>C_ab\<close> or \<open>C_cd\<close> cannot contain a symbol in \<open>C_ad\<close> or \<open>C_bc\<close>, or vice versa.
          Otherwise,we could increase the number of three types of symbols of a sentence in \<open>L\<close> without increasing the number 
          of the fourth type of symbol. In that case, there would be a sentence in \<open>L\<close> for which the number of occurrences of 
          one type of symbol is smaller than that of any other."
  have classes_excl_deriv: "\<And>X Y w \<alpha> \<beta> \<gamma> \<delta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta> 
          \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta> \<Longrightarrow> (Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w \<Longrightarrow>
          (X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<notin> Cad G' \<union> Cbc G') \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<notin> Cab G' \<union> Ccd G')"
    by (rule fact6[OF G'_obtain(3) langG' start_prod2 disjoint_double])

  have start_not_in_deriv: "\<And>X Y w \<alpha> \<beta> \<gamma> \<delta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>
          \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta> \<Longrightarrow> (Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w
          \<Longrightarrow>
          (X \<in> Cab G' \<union> Ccd G' \<union> Cad G' \<union> Cbc G' \<longrightarrow> Y \<noteq> Start G')"
    sorry (* Similar logic to all proofs before, if X leads back to S, we can come to a variable in
             the opposite class. i.e., rule ccontr: we assume Y = S, we derive from Y the opposite class of
             X, and use the fact given above.*)

  have classes_same_deriv: "\<And>X Y w \<alpha> \<beta> \<gamma> \<delta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>
          \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta> \<Longrightarrow> (Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w
          \<Longrightarrow>
          (X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<in> Cab G' \<union> Ccd G' \<union> {Start G'}) \<and> 
          (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<in> Cad G' \<union> Cbc G' \<union> {Start G'})"
  proof - 
    fix X Y w \<alpha> \<beta> \<gamma> \<delta>
    assume assm: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" "(Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta>" "(Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w"
    then have x_der: "(Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w" by auto
    have not_equal_x: "\<alpha> @ [Nt X] @ \<beta> \<noteq> map Tm w" using UNIV_I derive.intros not_derive_map_Tm by metis
    hence "\<exists>\<alpha>. (X, \<alpha>) \<in> (Prods G')"
      using x_der derives_Nt_Cons_map_Tm derives_append_map_Tm
      by meson 
    hence x_in_nts: "X \<in> Nts (Prods G')" using Nts_def by fast
    hence x_in_rest:
          "X \<notin> Cad G' \<union> Cbc G' \<Longrightarrow> X \<in> (Nts (Prods G') - (Cad G' \<union> Cbc G'))" 
          "X \<notin> Cab G' \<union> Ccd G' \<Longrightarrow> X \<in> (Nts (Prods G') - (Cab G' \<union> Ccd G'))" by auto

    have not_equal_y: "\<gamma> @ [Nt Y] @ \<delta> \<noteq> map Tm w" using UNIV_I derive.intros not_derive_map_Tm by metis
    hence "\<exists>\<alpha>. (Y, \<alpha>) \<in> (Prods G')"
      using assm(3) derives_Nt_Cons_map_Tm derives_append_map_Tm
      by meson 
    hence y_in_nts: "Y \<in> Nts (Prods G')" using Nts_def by fast
    hence y_in_rest:
          "Y \<notin> Cad G' \<union> Cbc G' \<Longrightarrow> Y \<in> (Nts (Prods G') - (Cad G' \<union> Cbc G'))" 
          "Y \<notin> Cab G' \<union> Ccd G' \<Longrightarrow> Y \<in> (Nts (Prods G') - (Cab G' \<union> Ccd G'))" by auto
    
    from c_c have subset: 
        "Nts (Prods G') - (Cad G' \<union> Cbc G') \<subseteq> Cab G' \<union> Ccd G' \<union> {Start G'}"
        "Nts (Prods G') - (Cab G' \<union> Ccd G') \<subseteq> Cad G' \<union> Cbc G' \<union> {Start G'}"
      using disjoint_double disjoints by auto
    
    hence y_in_rest2:
         "\<And>Y. Y \<in> (Nts (Prods G') - (Cad G' \<union> Cbc G')) \<Longrightarrow> Y \<in> Cab G' \<union> Ccd G' \<union> {Start G'}" 
         "\<And>Y. Y \<in> (Nts (Prods G') - (Cab G' \<union> Ccd G')) \<Longrightarrow> Y \<in> Cad G' \<union> Cbc G' \<union> {Start G'}" 
      apply blast
      using subset by blast


    have x_imp_y: "(X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<notin> Cad G' \<union> Cbc G') \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<notin> Cab G' \<union> Ccd G')"
      using classes_excl_deriv[OF assm] by auto
    then have y_imp_x: "(Y \<in> Cab G' \<union> Ccd G' \<longrightarrow> X \<notin> Cad G' \<union> Cbc G') \<and> (Y \<in> Cad G' \<union> Cbc G' \<longrightarrow> X \<notin> Cab G' \<union> Ccd G')"
      by linarith
   
    from x_imp_y have "(X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<in> Nts (Prods G') - (Cad G' \<union> Cbc G')) \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<in> Nts (Prods G') - (Cab G' \<union> Ccd G'))"
      using y_in_rest by linarith
    then show "(X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<in> Cab G' \<union> Ccd G' \<union> {Start G'}) \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<in> Cad G' \<union> Cbc G' \<union> {Start G'})"
      using y_in_rest2[of Y] by linarith
  qed


  then have classes_same_deriv_iff: "\<And>X Y w \<alpha> \<beta> \<gamma> \<delta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>
        \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* \<gamma> @ [Nt Y] @ \<delta> \<Longrightarrow> (Prods G') \<turnstile> \<gamma> @ [Nt Y] @ \<delta> \<Rightarrow>* map Tm w
        \<Longrightarrow>
        (X \<in> Cab G' \<union> Ccd G' \<longleftrightarrow> Y \<in> Cab G' \<union> Ccd G') \<and> 
        (X \<in> Cad G' \<union> Cbc G' \<longleftrightarrow> Y \<in> Cad G' \<union> Cbc G')"
    sorry 



  have class_left: "\<And>X w \<alpha> \<beta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>
          \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w \<Longrightarrow> X \<in> Cab G' \<union> Ccd G' \<Longrightarrow>
          w \<in> L_left"
  proof - 
    fix X w \<alpha> \<beta>
    assume assm: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" " (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w" 
                 "X \<in> Cab G' \<union> Ccd G'"
    then have "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" by auto
    hence "w \<in> LangS G'" unfolding Lang_def by simp
    hence w_in_L:"w \<in> L_ambig" using langG' by simp

    from assm(3) obtain c1 c2 where in_c: "X \<in> C_set c1 c2 G'" and 
       c_neq: "c1 \<noteq> c2" and c_cases: "(c1 = A \<and> c2 = B) \<or> (c1 = C  \<and> c2 = D)" 
      by blast  

    from in_c obtain l where 
      l_obtains: "l>0" "Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm [c1] ^^ l @ [Nt X] @ map Tm [c2] ^^ l" by force
    let ?x = "map Tm [c1] ^^ l" let ?y = "map Tm [c2] ^^ l" 
    let ?px = "[c1] ^^ l" let ?py = "[c2] ^^ l" 
    let ?cw = "\<lambda>s. count_list w s"  let ?c = "\<lambda>w s. count_list w s"
    from l_obtains have xy_not_empty: "?px @ ?py \<noteq> []" by (simp add: pow_list_Nil_iff_0)

    have x_cs: "count_list ?px c1 = l" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?px c = 0" and
         y_cs: "count_list ?py c2 = l" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?py c = 0"
      using count_list_pow_list[of l "[c1]"] count_list_pow_list[of l "[c2]"] by auto

    obtain aa xx bb where w_axb: "w = aa @ xx @ bb" and
     pump_in_L: "\<And>k. aa @ [c1] ^^ (l * k) @ xx @ [c2] ^^ (l * k) @ bb \<in> L_ambig"
      using derives_pumps[OF start_prod2 assm(1,2) l_obtains(2,1)] unfolding langG' by blast

    show "w \<in> L_left"
    proof (rule ccontr)
      assume w_left: "w \<notin> L_left"
      hence w_right: "w \<in> L_right" using w_in_L by simp
      then obtain n m where n_m: "w = [A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n" "n \<noteq> m"
        using w_right w_left by blast

      then have n_m_cs: "?cw A = n" "?cw B = m" "?cw C = m" "?cw D = n" 
        using count_list_pow_list[of n "[A]" A] count_list_pow_list[of m "[B]" B]
              count_list_pow_list[of m "[C]" C] count_list_pow_list[of n "[D]" D] by auto
        
      let ?wl = "length w + 1" 
      let ?xx = "?x ^^ ?wl" let ?yy = "?y ^^ ?wl" 
      let ?ppx = "[c1] ^^ (l * ?wl)" let ?ppy = "[c2] ^^ (l * ?wl)"
      have x_pow_cs: "count_list ?ppx c1 = l * ?wl" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?ppx c = 0" and
           y_pow_cs: "count_list ?ppy c2 = l * ?wl" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?ppy c = 0"
        using count_list_pow_list[of "l * ?wl" "[c1]"] x_cs count_list_pow_list[of "l * ?wl" "[c2]"] y_cs by auto
    
      from pump_in_L[of ?wl] have w_in_L: "aa @ ?ppx @ xx @ ?ppy @ bb \<in> L_ambig" by presburger

      have len_too_big: "?wl * l > n" "?wl * l > m" 
        using l_obtains(1) mult_le_cancel2[of 1 ?wl l, THEN iffD2] n_m(1) by (auto simp add: mult.commute)

      let ?w = "aa @ ?ppx @ xx @ ?ppy @ bb"

      consider "(c1 = A \<and> c2 = B)" | "(c1 = C \<and> c2 = D)" using c_cases by linarith
      then have "?w \<notin> L_ambig"
      proof cases
        case 1
        then have case_dist: 
        "?c ?w A = n + ?wl * l \<and> ?c ?w B = m + ?wl * l \<and> ?c ?w C = m \<and> ?c ?w D = n" 
          using n_m_cs x_pow_cs(1) y_pow_cs(1) w_axb 
                x_pow_cs(2)[of C] x_pow_cs(2)[of D]
                y_pow_cs(2)[of C] y_pow_cs(2)[of D] by auto

        have "?c ?w A \<noteq> ?c ?w B" using case_dist n_m(2) by linarith
        moreover have "?c ?w A \<noteq> ?c ?w C" using case_dist len_too_big by linarith 
        moreover have "?c ?w A \<noteq> ?c ?w D" using case_dist len_too_big by linarith 
        ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?w c \<noteq> count_list ?w c'" 
          using exI[of _ A] t.exhaust by blast 
        then show ?thesis using w_len_not_eq[OF ex] by presburger
      next
        case 2
        then have case_dist: 
        "?c ?w A = n \<and> ?c ?w B = m \<and> ?c ?w C = m + ?wl * l \<and>  ?c ?w D = n + ?wl * l" 
          using n_m_cs x_pow_cs(1) y_pow_cs(1) w_axb 
                x_pow_cs(2)[of A] x_pow_cs(2)[of B]
                y_pow_cs(2)[of A] y_pow_cs(2)[of B] by simp

        have "?c ?w A \<noteq> ?c ?w B" using case_dist n_m(2) by linarith
        moreover have "?c ?w A \<noteq> ?c ?w C" using case_dist len_too_big by linarith 
        moreover have "?c ?w A \<noteq> ?c ?w D" using case_dist len_too_big by linarith 
        ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?w c \<noteq> count_list ?w c'" 
          using exI[of _ A] t.exhaust by blast 
        then show ?thesis using w_len_not_eq[OF ex] by presburger
      qed  
      then show "False" using w_in_L by presburger
    qed
  qed



  have prods_left: "\<And>X w \<alpha> \<beta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta> 
          \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w \<Longrightarrow> X \<in> Cab G' \<union> Ccd G' 
          \<Longrightarrow> P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" sorry
 (* proof -
    fix X ww \<alpha> \<beta>
    assume x_ass: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" "(Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm ww" "X \<in> Cab G' \<union> Ccd G'"
    then have left: "ww \<in> L_left" using class_left[OF x_ass] by simp
    
    from x_ass obtain n m where n_m:
        "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>(n) \<alpha> @ [Nt X] @ \<beta>" "(Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>(m) map Tm ww"
      using rtranclp_power[iff] by fast
    from x_ass(1) have "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" sorry
     an idea for proof is to induct: however, I could not find a way i can induct
       using the the whole fact S \<Rightarrow>* aAb \<Rightarrow>* \<alpha>X\<beta> so that I can use classes_excl_deriv
      --- also needs the fact that if A is S, then a,b=[], i.e., no derivations. This needs to be true,
      since if there was a way S\<Rightarrow>*aSb for some at least one non empty a or b, then one can append a or b,
      or what terminals they derive (they need to be useful afterall), to whatever word in the language we want. 
      --- similar reasoning and proof for right side needed *)
   (* proof (induct rule: derives_induct)
      case base
      then show ?case by blast
    next
      case (step u T v ww) 
      then have t_nts: "T \<in> Nts (Prods G')" unfolding Nts_def by blast
      then have t_useful: "useful (Prods G') (Start G') T" using G'_obtain(3) by presburger
      then obtain \<gamma> z where g_w: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<gamma>" "Nt T \<in> set \<gamma>" "(Prods G') \<turnstile> \<gamma> \<Rightarrow>* map Tm z" 
        unfolding useful_def by blast

      then obtain x y 
        where b_x_y: "\<gamma> = x @ [Nt T] @ y" 
                   "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* x @ [Nt T] @ y" 
                   "(Prods G') \<turnstile> x @ [Nt T] @ y \<Rightarrow>* map Tm z" 
        using in_set_conv_decomp[THEN iffD1, OF g_w(2)] by auto
      from step.hyps(3) have twd: "Prods G' \<turnstile> [Nt T] \<Rightarrow>* ww " using derive_singleton[of "Prods G'" "Nt T" w] by simp
      then have xty: "Prods G' \<turnstile> u @ [Nt T] @ v \<Rightarrow>* u @ ww @ v" 
        using derives_append[THEN derives_prepend, OF twd, of u v] by argo
    
      presume "T \<noteq> Start G'"
      then have plus: "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>+ u @ [Nt T] @ v"
        using rtranclpD[OF step.hyps(2)] by (simp add: Cons_eq_append_conv)
      then obtain \<alpha> where "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha>" " P_left G' \<turnstile> \<alpha> \<Rightarrow> u @ [Nt T] @ v"
        using tranclpD2[OF plus] by fast
      then obtain k where "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>(k) \<alpha> \<and>  P_left G' \<turnstile> \<alpha> \<Rightarrow> u @ [Nt T] @ v"
        using rtranclp_power by fast
      then have "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>(Suc k) u @ [Nt T] @ v" by auto
      hence "\<exists>l \<in> {1..k}. \<exists>d e. P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>(l) d \<and> P_left G' \<turnstile> d \<Rightarrow> e \<and> Nt T \<notin> set d \<and> Nt T \<in> set e"
        sorry

      then have "\<exists>(\<alpha>, \<beta>)\<in> (P_left G'). Nt T \<in> set \<beta>"
        by 

      have "T \<notin> Cad G' \<union> Cbc G'" sorry
      

      then consider (ab_cd) "T \<in> Cab G' \<union> Ccd G'" | (start) "T = Start G'" 
        using c_c t_nts sorry
      then have aw: "(T, ww) \<in> P_left G'"
      proof cases
        case ab_cd
        then show ?thesis 
          using step.hyps(3) by blast
      next
        case start
        then show ?thesis sorry
      qed
        
      then show ?case using rtranclp_trans[OF s step.hyps(2)] by sorry
    qed 
   show "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ww" sorry  
 qed*)


  have class_right: "\<And>X w \<alpha> \<beta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>
          \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w \<Longrightarrow> X \<in> Cad G' \<union> Cbc G' \<Longrightarrow>
          w \<in> L_right"
  proof - 
    fix X w \<alpha> \<beta>
    assume assm: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" " (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w" 
                 "X \<in> Cad G' \<union> Cbc G'"
    then have "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" by auto
    hence "w \<in> LangS G'" unfolding Lang_def by simp
    hence w_in_L:"w \<in> L_ambig" using langG' by simp

    from assm(3) obtain c1 c2 where in_c: "X \<in> C_set c1 c2 G'" and 
       c_neq: "c1 \<noteq> c2" and c_cases: "(c1 = A \<and> c2 = D) \<or> (c1 = B  \<and> c2 = C)" 
      by blast  

    from in_c obtain l where 
      l_obtains: "l>0" "Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm [c1] ^^ l @ [Nt X] @ map Tm [c2] ^^ l" by force
    let ?x = "map Tm [c1] ^^ l" let ?y = "map Tm [c2] ^^ l" 
    let ?px = "[c1] ^^ l" let ?py = "[c2] ^^ l" 
    let ?cw = "\<lambda>s. count_list w s"  let ?c = "\<lambda>w s. count_list w s"
    from l_obtains have xy_not_empty: "?px @ ?py \<noteq> []" by (simp add: pow_list_Nil_iff_0)

    have x_cs: "count_list ?px c1 = l" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?px c = 0" and
         y_cs: "count_list ?py c2 = l" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?py c = 0"
      using count_list_pow_list[of l "[c1]"] count_list_pow_list[of l "[c2]"] by auto

    obtain aa xx bb where w_axb: "w = aa @ xx @ bb" and
     pump_in_L: "\<And>k. aa @ [c1] ^^ (l * k) @ xx @ [c2] ^^ (l * k) @ bb \<in> L_ambig"
      using derives_pumps[OF start_prod2 assm(1,2) l_obtains(2,1)] unfolding langG' by blast

    show "w \<in> L_right"
    proof (rule ccontr)
      assume w_left: "w \<notin> L_right"
      hence w_right: "w \<in> L_left" using w_in_L by simp
      then obtain n m where n_m: "w = [A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m" "n \<noteq> m"
        using w_right w_left by blast

      then have n_m_cs: "?cw A = n" "?cw B = n" "?cw C = m" "?cw D = m" 
        using count_list_pow_list[of n "[A]" A] count_list_pow_list[of n "[B]" B]
              count_list_pow_list[of m "[C]" C] count_list_pow_list[of m "[D]" D] by auto 
        
      let ?wl = "length w + 1" 
      let ?xx = "?x ^^ ?wl" let ?yy = "?y ^^ ?wl" 
      let ?ppx = "[c1] ^^ (l * ?wl)" let ?ppy = "[c2] ^^ (l * ?wl)"
      have x_pow_cs: "count_list ?ppx c1 = l * ?wl" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?ppx c = 0" and
           y_pow_cs: "count_list ?ppy c2 = l * ?wl" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?ppy c = 0"
        using count_list_pow_list[of "l * ?wl" "[c1]"] x_cs count_list_pow_list[of "l * ?wl" "[c2]"] y_cs by auto
    
      from pump_in_L[of ?wl] have w_in_L: "aa @ ?ppx @ xx @ ?ppy @ bb \<in> L_ambig" by presburger

      have len_too_big: "?wl * l > n" "?wl * l > m" 
        using l_obtains(1) mult_le_cancel2[of 1 ?wl l, THEN iffD2] n_m(1) by (auto simp add: mult.commute)

      let ?w = "aa @ ?ppx @ xx @ ?ppy @ bb"

      consider "(c1 = A \<and> c2 = D)" | "(c1 = B \<and> c2 = C)" using c_cases by linarith
      then have "?w \<notin> L_ambig"
      proof cases
        case 1
        then have case_dist: 
        "?c ?w A = n + ?wl * l \<and> ?c ?w B = n \<and> ?c ?w C = m \<and> ?c ?w D = m + ?wl * l" 
          using n_m_cs x_pow_cs(1) y_pow_cs(1) w_axb by simp

        have "?c ?w A \<noteq> ?c ?w B" using case_dist len_too_big by linarith
        moreover have "?c ?w A \<noteq> ?c ?w C" using case_dist len_too_big by linarith 
        moreover have "?c ?w A \<noteq> ?c ?w D" using case_dist n_m(2) by linarith 
        ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?w c \<noteq> count_list ?w c'" 
          using exI[of _ A] t.exhaust by blast 
        then show ?thesis using w_len_not_eq[OF ex] by presburger
      next
        case 2
        then have case_dist: 
        "?c ?w A = n \<and> ?c ?w B = n + ?wl * l \<and> ?c ?w C = m + ?wl * l \<and>  ?c ?w D = m" 
          using n_m_cs x_pow_cs(1) y_pow_cs(1) w_axb by simp

        have "?c ?w A \<noteq> ?c ?w B" using case_dist len_too_big by linarith
        moreover have "?c ?w A \<noteq> ?c ?w C" using case_dist len_too_big by linarith 
        moreover have "?c ?w A \<noteq> ?c ?w D" using case_dist n_m(2) by linarith 
        ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?w c \<noteq> count_list ?w c'" 
          using exI[of _ A] t.exhaust by blast 
        then show ?thesis using w_len_not_eq[OF ex] by presburger
      qed  
      then show "False" using w_in_L by presburger
    qed
  qed

  have prods_right: "\<And>X w \<alpha> \<beta>. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta> 
        \<Longrightarrow> (Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w \<Longrightarrow> X \<in> Cad G' \<union> Cbc G' 
        \<Longrightarrow> P_right G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w"
    sorry

  have left_subst: "P_left G' \<subseteq> Prods G'" and right_subst: "P_right G' \<subseteq> Prods G'" by auto


  have "\<And>w. P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w \<Longrightarrow> w \<in> L_left"
  proof -
    fix w
    assume pl_der_w: "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w"
    then have p_der_w: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" using derives_mono[OF left_subst] by blast
 
    from pl_der_w obtain \<alpha> where alpha: "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow> \<alpha>" "P_left G' \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
      using derive_singleton derives_Nt_map_TmD[OF pl_der_w] by meson

    then have in_Pl: "(Start G', \<alpha>) \<in> P_left G'" using derive_singleton[THEN iffD1, OF alpha(1)] by fast

    consider (no_nts) "Nts_syms \<alpha> = {}" | (nts) "Nts_syms \<alpha> \<noteq> {}" by blast
    thus "w \<in> L_left" 
    proof cases
      case no_nts
      then obtain a where obt: "\<alpha> = map Tm a" using Nts_syms_empty_iff[THEN iffD1, OF no_nts] by blast
      then have "a = w" using alpha(2) by (simp add: derives_map_Tm_iff)
      then have "(Start G', map Tm w) \<in> P_left G'" using in_Pl obt by argo
      
      then have "(Start G', map Tm w) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> (X \<in> Cab G' \<union> Ccd G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G'))}
               \<or> (Start G', map Tm w) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> X = Start G' \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<and> n \<noteq> m)} " 
        by fast
      then have "((Start G', map Tm w) \<in> Prods G' \<and> (Start G' \<in> Cab G' \<union> Ccd G' \<or> (\<exists>s \<in> Nts_syms (map Tm w). s \<in> Cab G' \<union> Ccd G'))) 
               \<or> ((Start G', map Tm w) \<in> Prods G' \<and> Start G' = Start G' \<and> (\<exists>n m. w = [A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m \<and> n \<noteq> m))"
        using case_prod_conv[of _ "Start G'" "map Tm w"] map_Tm_inject_iff mem_Collect_eq[of "(Start G', map Tm w)"] 
        by (smt (verit, best))
      then show ?thesis using no_nts start_not by fastforce
    next
      case nts
      
      have "(Start G', \<alpha>) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> (X \<in> Cab G' \<union> Ccd G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G'))}
              \<or> (Start G', \<alpha>) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> X = Start G' \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<and> n \<noteq> m)} " 
        using in_Pl by fast
      then have "(\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G') 
               \<or> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<and> n \<noteq> m)"
        using case_prod_conv[of _ "Start G'" "\<alpha>"] mem_Collect_eq[of "(Start G', \<alpha>)"] in_Pl left_subst start_not nts Nts_syms_map_Tm by fast
      then obtain X where x_ob: "X \<in> Nts_syms \<alpha>" "X \<in> Cab G' \<union> Ccd G'" using nts Nts_syms_map_Tm by meson
      then obtain \<gamma> \<delta> where g_d: "\<alpha> = \<gamma> @ [Nt X] @ \<delta>" using in_Nts_syms[THEN iffD1, OF x_ob(1), THEN in_set_conv_decomp_first[THEN iffD1]] by force 
      then have f1: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<gamma> @ [Nt X] @ \<delta>" and f2: "Prods G' \<turnstile> \<gamma> @ [Nt X] @ \<delta> \<Rightarrow>* map Tm w"
        using alpha derives_mono left_subst apply blast
        using g_d alpha derives_mono left_subst by blast 
      show ?thesis using class_left[OF f1 f2 x_ob(2)] by simp
    qed
  qed

  have "\<And>w. P_right G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w \<Longrightarrow> w \<in> L_right"
  proof -
    fix w
    assume pl_der_w: "P_right G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w"
    then have p_der_w: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" using derives_mono[OF right_subst] by blast
 
    from pl_der_w obtain \<alpha> where alpha: "P_right G' \<turnstile> [Nt (Start G')] \<Rightarrow> \<alpha>" "P_right G' \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
      using derive_singleton derives_Nt_map_TmD[OF pl_der_w] by meson

    then have in_Pl: "(Start G', \<alpha>) \<in> P_right G'" using derive_singleton[THEN iffD1, OF alpha(1)] by fast

    consider (no_nts) "Nts_syms \<alpha> = {}" | (nts) "Nts_syms \<alpha> \<noteq> {}" by blast
    thus "w \<in> L_right" 
    proof cases
      case no_nts
      then obtain a where obt: "\<alpha> = map Tm a" using Nts_syms_empty_iff[THEN iffD1, OF no_nts] by blast
      then have "a = w" using alpha(2) by (simp add: derives_map_Tm_iff)
      then have "(Start G', map Tm w) \<in> P_right G'" using in_Pl obt by argo
      
      then have "(Start G', map Tm w) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> (X \<in> Cad G' \<union> Cbc G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G'))}
               \<or> (Start G', map Tm w) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> X = Start G' \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n) \<and> n \<noteq> m)} " 
        by fast
      then have "((Start G', map Tm w) \<in> Prods G' \<and> (Start G' \<in> Cad G' \<union> Cbc G' \<or> (\<exists>s \<in> Nts_syms (map Tm w). s \<in> Cad G' \<union> Cbc G'))) 
               \<or> ((Start G', map Tm w) \<in> Prods G' \<and> Start G' = Start G' \<and> (\<exists>n m. w = [A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n \<and> n \<noteq> m))"
        using case_prod_conv[of _ "Start G'" "map Tm w"] map_Tm_inject_iff mem_Collect_eq[of "(Start G', map Tm w)"] 
        by (smt (verit, best))
      then show ?thesis using no_nts start_not by fastforce
    next
      case nts
      have "(Start G', \<alpha>) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> (X \<in> Cad G' \<union> Cbc G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G'))}
              \<or> (Start G', \<alpha>) \<in> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> X = Start G' \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n) \<and> n \<noteq> m)} " 
        using in_Pl by fast
      then have "(\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G') 
               \<or> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n) \<and> n \<noteq> m)"
        using case_prod_conv[of _ "Start G'" "\<alpha>"] mem_Collect_eq[of "(Start G', \<alpha>)"] in_Pl left_subst start_not nts Nts_syms_map_Tm by fast
      then obtain X where x_ob: "X \<in> Nts_syms \<alpha>" "X \<in> Cad G' \<union> Cbc G'" using nts Nts_syms_map_Tm by meson
      then obtain \<gamma> \<delta> where g_d: "\<alpha> = \<gamma> @ [Nt X] @ \<delta>" using in_Nts_syms[THEN iffD1, OF x_ob(1), THEN in_set_conv_decomp_first[THEN iffD1]] by force 
      then have f1: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<gamma> @ [Nt X] @ \<delta>" and f2: "Prods G' \<turnstile> \<gamma> @ [Nt X] @ \<delta> \<Rightarrow>* map Tm w"
        using alpha derives_mono right_subst apply blast
        using g_d alpha derives_mono right_subst by blast 
      show ?thesis using class_right[OF f1 f2 x_ob(2)] by simp
    qed
  qed   


  have p_s_distinct: "P_left G' \<inter> P_right G' = {}"
  proof (rule ccontr)
    assume "\<not> P_left G' \<inter> P_right G' = {}"
    hence p_not_emp: "P_left G' \<inter> P_right G' \<noteq> {}" by simp
    then obtain S \<alpha> where "(S, \<alpha>) \<in> P_left G' \<inter> P_right G'" using ex_in_conv[THEN iffD2, OF p_not_emp] by force
    then have in_l: "(S, \<alpha>) \<in> P_left G'" and in_r: "(S, \<alpha>) \<in> P_right G'" by auto
    hence in_prods: "(S, \<alpha>) \<in> Prods G'" by auto
    hence nts: "S \<in> Nts (Prods G')" "Nts_syms \<alpha> \<subseteq> Nts (Prods G')" unfolding Nts_def by auto
    hence "useful (Prods G') (Start G') S" using G'_obtain(3) by simp
    then obtain \<beta> where b: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<beta>" "Nt S \<in> set \<beta>" "productives (Prods G') \<beta>"
      unfolding useful_def by blast
    then obtain \<beta>1 \<beta>2 where "\<beta> = \<beta>1 @ [Nt S] @ \<beta>2" 
      using in_set_conv_decomp_first[THEN iffD1, OF b(2)] by fastforce 
    hence s_der: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<beta>1 @ [Nt S] @ \<beta>2" using b(1) by simp

    let ?PL_left = "{(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> (X \<in> Cab G' \<union> Ccd G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G'))}"
    let ?PR_left = "{(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> (X \<in> Cad G' \<union> Cbc G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G'))}"
    let ?PL_right = "{(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> X = Start G' \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<and> n \<noteq> m)}"
    let ?PR_right = "{(X, \<alpha>). (X, \<alpha>) \<in> Prods G' \<and> X = Start G' \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n) \<and> n \<noteq> m)}"

    from in_l in_r have ins: "((S, \<alpha>) \<in> ?PL_left \<or> (S, \<alpha>) \<in> ?PL_right) \<and> ((S, \<alpha>) \<in> ?PR_left \<or> (S, \<alpha>) \<in> ?PR_right)"
      by auto

    have inNts: "\<And>F X. X \<in> Nts_syms \<alpha> \<Longrightarrow> X \<in> F \<Longrightarrow> (\<exists>\<gamma> X \<delta>. \<alpha> = \<gamma> @ [Nt X] @ \<delta> \<and> X \<in> F)" 
      using in_Nts_syms[THEN iffD1, OF _, THEN in_set_conv_decomp_first[THEN iffD1]] by fastforce

    from ins consider 
      (left_left) "(S, \<alpha>) \<in> ?PL_left \<and> (S, \<alpha>) \<in> ?PR_left" |
      (left_right) "(S, \<alpha>) \<in> ?PL_left \<and> (S, \<alpha>) \<in> ?PR_right" |
      (right_left) "(S, \<alpha>) \<in> ?PL_right \<and> (S, \<alpha>) \<in> ?PR_left" |
      (right_right) "(S, \<alpha>) \<in> ?PL_right \<and> (S, \<alpha>) \<in> ?PR_right" by argo
    thus False
    proof cases
      case left_left
      then have "(S \<in> Cab G' \<union> Ccd G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G')) \<and> (S \<in> Cad G' \<union> Cbc G' \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G'))" by auto
      then have 
         "(S \<in> Cab G' \<union> Ccd G' \<and> S \<in>  Cad G' \<union> Cbc G') \<or> ((\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G') \<and> S \<in>  Cad G' \<union> Cbc G') \<or>
          (S \<in> Cab G' \<union> Ccd G' \<and> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G')) \<or> ((\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G') \<and> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G'))"
        by argo
      hence  
        "((\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G') \<and> S \<in> Cad G' \<union> Cbc G') \<or>
         (S \<in> Cab G' \<union> Ccd G' \<and> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G')) \<or> ((\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G') \<and> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G'))"
        using disjoint_double by auto 
      then consider 
          "(\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G') \<and> S \<in> Cad G' \<union> Cbc G'" | 
           "S \<in> Cab G' \<union> Ccd G' \<and> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G')" | 
           "(\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G' \<union> Ccd G') \<and> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G' \<union> Cbc G')"
        by linarith
      then show ?thesis 
      proof cases
        case 1
        then obtain X where s: "X \<in> Nts_syms \<alpha>" "X \<in> Cab G' \<union> Ccd G'" by blast
        then obtain \<gamma> \<delta> where ob: "\<alpha> = \<gamma> @ [Nt X] @ \<delta>" using in_Nts_syms[THEN iffD1, OF s(1), THEN in_set_conv_decomp_first[THEN iffD1]] by fastforce
        then have s_x: "Prods G' \<turnstile> [Nt S] \<Rightarrow>* \<gamma> @ [Nt X] @ \<delta>" using in_prods derive_singleton by blast
        then have s_x_em: "Prods G' \<turnstile> \<beta>1 @ [Nt S] @ \<beta>2 \<Rightarrow>* (\<beta>1 @ \<gamma>) @ [Nt X] @ (\<delta> @ \<beta>2)" using derives_embed[OF s_x] by simp
        then have s_to_x: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* (\<beta>1 @ \<gamma>) @ [Nt X] @ (\<delta> @ \<beta>2)" using s_der by simp
        from nts(2) have "X \<in> Nts (Prods G')" using ob by simp
        from s_to_x obtain w where
           w: "Prods G' \<turnstile> (\<beta>1 @ \<gamma>) @ [Nt X] @ (\<delta> @ \<beta>2) \<Rightarrow>* map Tm w"  
          using derives_useful_list[OF start_prod2 G'_obtain(3)] derives_append_map_Tm by blast
        then have "(S \<in>  Cab G' \<union> Ccd G' \<longrightarrow> X \<notin> Cad G' \<union> Cbc G') \<and> (S \<in> Cad G' \<union> Cbc G' \<longrightarrow> X \<notin>  Cab G' \<union> Ccd G')" 
          using classes_excl_deriv[OF s_der s_x_em w] by simp
        then show ?thesis using 1 s(2) by presburger
      next
        case 2
        then obtain X where s: "X \<in> Nts_syms \<alpha>" "X \<in> Cad G' \<union> Cbc G'" by blast
        then obtain \<gamma> \<delta> where ob: "\<alpha> = \<gamma> @ [Nt X] @ \<delta>" using in_Nts_syms[THEN iffD1, OF s(1), THEN in_set_conv_decomp_first[THEN iffD1]] by fastforce
        then have s_x: "Prods G' \<turnstile> [Nt S] \<Rightarrow>* \<gamma> @ [Nt X] @ \<delta>" using in_prods derive_singleton by blast
        then have s_x_em: "Prods G' \<turnstile> \<beta>1 @ [Nt S] @ \<beta>2 \<Rightarrow>* (\<beta>1 @ \<gamma>) @ [Nt X] @ (\<delta> @ \<beta>2)" using derives_embed[OF s_x] by simp
        then have s_to_x: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* (\<beta>1 @ \<gamma>) @ [Nt X] @ (\<delta> @ \<beta>2)" using s_der by simp
        from nts(2) have "X \<in> Nts (Prods G')" using ob by simp
        from s_to_x obtain w where
           w: "Prods G' \<turnstile> (\<beta>1 @ \<gamma>) @ [Nt X] @ (\<delta> @ \<beta>2) \<Rightarrow>* map Tm w"  
          using derives_useful_list[OF start_prod2 G'_obtain(3)] derives_append_map_Tm by blast
        then have "(S \<in> Cab G' \<union> Ccd G' \<longrightarrow> X \<notin> Cad G' \<union> Cbc G') \<and> (S \<in> Cad G' \<union> Cbc G' \<longrightarrow> X \<notin>  Cab G' \<union> Ccd G')" 
          using classes_excl_deriv[OF s_der s_x_em w] by simp
        then show ?thesis using 2 s(2) by presburger
      next
        case 3
        then obtain X Y where s: "X \<in> Nts_syms \<alpha>" "X \<in> Cab G' \<union> Ccd G'" "Y \<in> Nts_syms \<alpha>" "Y \<in> Cad G' \<union> Cbc G'" by blast
        then obtain \<gamma>1 \<delta>1 \<gamma>2 \<delta>2 where ob: "\<alpha> = \<gamma>1 @ [Nt X] @ \<delta>1" "\<alpha> = \<gamma>2 @ [Nt Y] @ \<delta>2" 
          using in_Nts_syms[THEN iffD1, OF s(1), THEN in_set_conv_decomp_first[THEN iffD1]]
                in_Nts_syms[THEN iffD1, OF s(3), THEN in_set_conv_decomp_first[THEN iffD1]]
          by force
        then have s_x: "Prods G' \<turnstile> [Nt S] \<Rightarrow>* \<gamma>1 @ [Nt X] @ \<delta>1" "Prods G' \<turnstile> \<gamma>1 @ [Nt X] @ \<delta>1 \<Rightarrow>* \<gamma>2 @ [Nt Y] @ \<delta>2" 
          using in_prods derive_singleton apply fastforce 
          using ob in_prods derive_singleton by fastforce 
        then have s_to_y: "Prods G' \<turnstile> [Nt S] \<Rightarrow>* \<gamma>2 @ [Nt Y] @ \<delta>2" by auto
        then have s_x_em: "Prods G' \<turnstile> \<beta>1 @ [Nt S] @ \<beta>2 \<Rightarrow>* (\<beta>1 @ \<gamma>2) @ [Nt Y] @ (\<delta>2 @ \<beta>2)" using derives_embed[OF s_to_y] by simp
        then have s_to_y: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>*  (\<beta>1 @ \<gamma>2) @ [Nt Y] @ (\<delta>2 @ \<beta>2)" using s_der by simp
        have s_x_em: "Prods G' \<turnstile> \<beta>1 @ [Nt S] @ \<beta>2 \<Rightarrow>* (\<beta>1 @ \<gamma>1) @ [Nt X] @ (\<delta>1 @ \<beta>2)" using derives_embed[OF s_x(1)] by simp
        then have s_to_x: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>*  (\<beta>1 @ \<gamma>1) @ [Nt X] @ (\<delta>1 @ \<beta>2)" using s_der by simp
        have x_to_y: "Prods G' \<turnstile> (\<beta>1 @ \<gamma>1) @ [Nt X] @ (\<delta>1 @ \<beta>2) \<Rightarrow>* (\<beta>1 @ \<gamma>2) @ [Nt Y] @ (\<delta>2 @ \<beta>2)" using derives_embed[OF s_x(2)] by simp
        from s_to_y obtain w where
           w: "Prods G' \<turnstile> (\<beta>1 @ \<gamma>2) @ [Nt Y] @ (\<delta>2 @ \<beta>2) \<Rightarrow>* map Tm w"  
          using derives_useful_list[OF start_prod2 G'_obtain(3)] derives_append_map_Tm by blast
        then have "(X \<in> Cab G' \<union> Ccd G' \<longrightarrow> Y \<notin> Cad G' \<union> Cbc G') \<and> (X \<in> Cad G' \<union> Cbc G' \<longrightarrow> Y \<notin> Cab G' \<union> Ccd G')" 
          using classes_excl_deriv[OF s_to_x x_to_y w] by simp
        then show ?thesis using s(2) s(4) by presburger
      qed
    next
      case left_right
      then show ?thesis using Nts_syms_map_Tm start_not by fast
    next
      case right_left
      then show ?thesis using Nts_syms_map_Tm start_not by fast
    next
      case right_right
      then show ?thesis by force
    qed
  qed
    

  have start_empty: "\<And>u v. Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* u @ [Nt (Start G')] @ v \<Longrightarrow> \<forall>uw vw. Prods G' \<turnstile> u \<Rightarrow>* map Tm uw \<and> Prods G' \<turnstile> v \<Rightarrow>* map Tm vw \<longrightarrow> uw = [] \<and> vw = []"
  proof -
    fix u v 
    assume st_p: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* u @ [Nt (Start G')] @ v"
    show "\<forall>uw vw. Prods G' \<turnstile> u \<Rightarrow>* map Tm uw \<and> Prods G' \<turnstile> v \<Rightarrow>* map Tm vw \<longrightarrow> uw = [] \<and> vw = []"
    proof (rule ccontr)
      assume "\<not> (\<forall>uw vw. Prods G' \<turnstile> u \<Rightarrow>* map Tm uw \<and> Prods G' \<turnstile> v \<Rightarrow>* map Tm vw \<longrightarrow> uw = [] \<and> vw = [])"
      then obtain uw vw where not_empty: "Prods G' \<turnstile> u \<Rightarrow>* map Tm uw \<and> Prods G' \<turnstile> v \<Rightarrow>* map Tm vw \<Longrightarrow> uw \<noteq> [] \<and> vw \<noteq> []" by blast      
      
      then have lambig: "\<And>s. s \<in> L_ambig \<Longrightarrow> (uw @ s @ vw) \<in> L_ambig"
        using rtranclp_trans[OF derives_forever[OF st_p] ] 
              derives_append_append[OF _ [THEN derives_power] _, 
                 THEN derives_append_append[OF _ _[THEN derives_power]]] sorry

     let ?wl = "length w"
     have abcd: "\<And>k l. [A] ^^ k @ [B] ^^ l @ [C] ^^ l  @ [D] ^^  k \<in> L_right" by blast
     hence inl: "[A] ^^ ?wl @ [D] ^^  ?wl \<in> L_ambig" using abcd[of ?wl 0] by simp

     hence "(uw @ [A] ^^ ?wl @ [D] ^^  ?wl @ vw) \<in> L_ambig" using lambig[OF inl] by simp
     
     show False sorry 
        (*Proof idea: uw and vw need to be a string of a's and d's due to ordering. They also need to be of
          same length. Then, let i be a natural number s.t. a1 = {a}^i, a2 = {d}^i. We can now pump the word "cd" 
        (it is again in the language), which will give us {a}^ic{d}^i+1 \<longrightarrow> a contradiction.*)
    qed
  qed

  have "\<And>X. (X, [Nt X]) \<notin> Prods G'" sorry (* We should ensure this, maybe through an assumption, since these loops can be eliminated easily*)


  have ws: "\<And>w n m. n \<noteq> m \<Longrightarrow> w = [A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m \<Longrightarrow>  P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w"
  proof -
    fix w n m
    assume n_m_neq: "n \<noteq> m" and w: "w = [A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m" 

    have "w \<in> L_ambig" using w by fast 
    hence prods: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" using langG' unfolding Lang_def by auto 
    show "P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w"
    proof (rule ccontr)
      assume "\<not>P_left G' \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm w" 
      then have "\<exists>\<alpha>1 \<alpha>2 \<beta> X. Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha>1 @ [Nt X] @ \<alpha>2  
                 \<and> (X, \<beta>) \<in> (Prods G' - P_left G') \<and> Prods G' \<turnstile> \<alpha>1 @ \<beta> @ \<alpha>2  \<Rightarrow>* map Tm w" 
        sorry (* A generalized proof needed that if a subset does not derive w, there exists a derivation
                 step that is not in the subset*)
      then obtain \<alpha>1 \<alpha>2 \<beta> X where 
          deriv1: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha>1 @ [Nt X] @ \<alpha>2" and
          in_prods: "(X, \<beta>) \<in> Prods G'" and notin_left:  "(X, \<beta>)\<notin> (P_left G')" and
          deriv2: "Prods G' \<turnstile> \<alpha>1 @ \<beta> @ \<alpha>2  \<Rightarrow>* map Tm w"
        by auto
      then have notin_p: "(X \<notin> Cab G' \<union> Ccd G' \<and> \<not>(\<exists>s \<in> Nts_syms \<beta>. s \<in> Cab G' \<union> Ccd G')) \<and>
                 (X = Start G' \<longrightarrow> \<not>(\<exists>n m. \<beta> = map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<and> n \<noteq> m))"
        using notin_left in_prods by fast
      then have x_not: "X \<notin> Cab G' \<union> Ccd G'" and s_not: "(\<forall>s \<in> Nts_syms \<beta>. s \<notin> Cab G' \<union> Ccd G')" and
                start_tm: "(X = Start G' \<longrightarrow> (\<forall>n m. n \<noteq> m \<longrightarrow> \<beta> \<noteq> map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m)))"
          apply fast using notin_p apply fast using notin_p by blast
      
      from in_prods have beta: "Prods G' \<turnstile> [Nt X] \<Rightarrow>* \<beta>" using derive_singleton[iff] by blast
      hence "Prods G' \<turnstile> \<alpha>1 @ [Nt X] @ \<alpha>2 \<Rightarrow>* \<alpha>1 @ \<beta> @ \<alpha>2" using derives_embed[OF beta] by fast
      hence x_to_w: "Prods G' \<turnstile> \<alpha>1 @ [Nt X] @ \<alpha>2 \<Rightarrow>* map Tm w" using deriv2 by auto
      from deriv2  obtain a1 x a2 where 
            a1: "Prods G' \<turnstile> \<alpha>1 \<Rightarrow>* map Tm a1" 
        and x: "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm x" 
        and a2: "Prods G' \<turnstile> \<alpha>2 \<Rightarrow>* map Tm a2" 
        and w_comp: "w = a1 @ x @ a2"
       using derives_append_map_Tm[THEN iffD1] by blast                 
      
      have "X \<in> Nts (Prods G')" using in_prods unfolding Nts_def[of "Prods G'"] by auto
      then have "X \<in> Cad G' \<union> Cbc G' \<union> {Start G'}"
        using c_c Un_iff x_not by blast
      then consider "X \<in> Cad G' \<union> Cbc G'" | "X = Start G'" by blast
      thus False 
      proof cases
        case 1
        then have "w \<in> L_right" using class_right[OF deriv1 x_to_w 1] by argo
        then show ?thesis  using w n_m_neq by auto
      next
        case 2
        then have ss: "Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha>1 @ [Nt (Start G')] @ \<alpha>2" using deriv1 by auto
        then have empts: "a1 = []" "a2 = []" using start_empty[OF ss] a1 a2 by auto
 

        from empts have bw: "Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w" using w_comp x by simp
        then have "Nts_syms \<beta> \<noteq> {}" 
          using Nts_syms_empty_iff[iff] derives_map_Tm_iff[iff] w n_m_neq start_tm 2 by force
        then obtain S where s_ob: "S \<in> Nts_syms \<beta>" "S \<notin> Cab G' \<union> Ccd G'" using s_not by blast
        then obtain x y where xy: "\<beta> = x @ [Nt S] @ y" 
          using in_Nts_syms[THEN iffD1, OF s_ob(1), THEN in_set_conv_decomp_first[THEN iffD1]] by auto
        with empts have d1:"Prods G' \<turnstile> [Nt (Start G')] \<Rightarrow>* x @ [Nt S] @ y" using deriv1 2 beta by blast
        with xy bw have d2: "Prods G' \<turnstile> x @ [Nt S] @ y \<Rightarrow>* map Tm w" by blast

        have "S \<in> Nts (Prods G')" unfolding Nts_def[of "Prods G'"] using in_prods s_ob(1) by blast
        then have "S \<in> Cad G' \<union> Cbc G' \<union> {Start G'}"
          using c_c Un_iff s_ob(2) by blast
       then consider (r) "S \<in> Cad G' \<union> Cbc G'" |(s) "S = Start G'" by blast 
       thus False 
       proof cases
         case r
         then have "w \<in> L_right" using class_right[OF d1 d2 r] by argo
         then show ?thesis using w n_m_neq by auto
       next
         case s
         then have "(Start G',x @ [Nt (Start G')] @ y) \<in> Prods G'" using 2 xy in_prods by auto
         then show ?thesis sorry 
           (* Show that x and y needs to be empty, and if so, this cannot be in Prods.*)
       qed
      qed
    qed 
    
  qed
  text "We need the extra formulation of the epsilon-production removal and eliminating self-loops, since otherwise (S, xSy) productions can be still there,
       not be in P_left, and x and y can still derive empty lists. However otherwise, we will no allow nullable vbariables, which mean 
       if x y derive [], they also are []! Then (S,S) is also not in the production list, et voila!"
  text "One other idea is to show these properties on Prods G', since their absence implies ambiguity: if (S,S)\<in>P, one can self-loop to
       find a new derivation tree. Or, if one can pump however x,y's (that derive nothingness) they want, they can still create a derivation self-loop"

  then have n_m_l:
      "\<And>n m. n \<noteq> m \<Longrightarrow> 
          ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<in> Lang (P_left G') (Start G')"
    using ws[OF _] unfolding Lang_def by blast

  then have 
    "\<And>n m. n \<noteq> m \<Longrightarrow> 
          ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n) \<in> Lang (P_right G') (Start G')"
    sorry

  let ?Sl = "{(S, \<alpha>) \<in> P_left G'. S = Start G'}"

  have subs_Sl: "?Sl \<subseteq> Prods G'" by blast

  have card_l: "1 \<le> card ?Sl" sorry(* not hard to show: otherwise, language of P_left is empty*)

  (*It is important that the productions of G' is finite, since we want to index the *)
  have "finite (Prods G')" using cfl langG' unfolding CFL_def sorry (* CFL assumption is not good enough*)
  
  hence sl_f: "finite (?Sl)" using finite_subset[OF subs_Sl] by fast 
  then obtain f :: "nat \<Rightarrow> ('n, t) prod" where bij: "bij_betw f {1..card ?Sl} ?Sl" 
    using bij_betw_from_nat_into_finite ex_bij_betw_nat_finite_1 by blast

  have im_s: "f ` {1..card ?Sl} = ?Sl" using bij_betw_def[THEN iffD1, OF bij] by fast
  then have "{s. \<exists>i \<in> {1..card ?Sl}. s = f i} = ?Sl" unfolding image_def by fast

  then have"\<And>s. s \<in> {s. \<exists>i \<in> {1..card ?Sl}. s = f i} \<Longrightarrow> s \<in> ?Sl" by argo    
  then have"\<And>s. \<exists>i \<in> {1..card ?Sl}. s = f i \<Longrightarrow> s \<in> ?Sl" by (auto simp only: mem_Collect_eq) 
  then have i_in: "\<And>i. i \<in> {1..card ?Sl} \<Longrightarrow> f i \<in> ?Sl"  by (metis (no_types, lifting))
  

  have ss_im: "{(S, \<alpha>). \<exists>i\<in>{1..card ?Sl}. f i = (S, \<alpha>)} = image f {1..card ?Sl}" by force

  
  let ?Nl = "\<lambda>(i::nat). {n. let (S, \<alpha>) = f i in (\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))}"
  let ?Ml = "\<lambda>(i::nat). {m. let (S, \<alpha>) = f i in (\<exists>n. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))}"


  have "\<And>\<alpha> w. P_left G' \<turnstile> \<alpha> \<Rightarrow>* map Tm w \<Longrightarrow> (\<forall>c1 c2. Nts_syms \<alpha> \<subseteq> C_set c1 c2 G' \<longrightarrow> (\<exists>n.  w = [c1] ^^n @ [c2] ^^n))"
    sorry (*idea: a lemma like this can show the fact above: a left side of symbols from C_set c1 c2
           will always derive a word of form a^nb^n*)
  

  have s: "\<And>n i. n \<notin> ?Nl i \<and> n \<notin> ?Ml i \<Longrightarrow> 
      \<not>(\<exists>S \<alpha>. f i = (S, \<alpha>) \<and> (\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<and> 
                                   (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ m @ [B] ^^ m @ [C] ^^ n @ [D] ^^ n)))" 
    by auto


  have inml: "\<And>i n m. i\<in>{1..card ?Sl} \<Longrightarrow> n \<in> ?Nl i \<Longrightarrow> m \<in> ?Ml i 
          \<Longrightarrow> ((P_left G') \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"  
  proof -
    fix i n m
    assume ass: "i\<in>{1..card ?Sl}" "n \<in> ?Nl i" "m \<in> ?Ml i" 
   
    have fi: "f i \<in> ?Sl" using i_in[OF ass(1)] by simp
    from ass(2,3) have "let (S, \<alpha>) = f i in (\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
              "let (S, \<alpha>) = f i in (\<exists>n. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
      by auto
    then have r: "let (S, \<alpha>) = f i in f i \<in> ?Sl \<and> (\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
              "let (S, \<alpha>) = f i in f i \<in> ?Sl \<and>  (\<exists>n. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
      using fi by auto  
    then have ss: "let (S, \<alpha>) = f i in (S, \<alpha>) \<in> P_left G' \<and> (\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
              "let (S, \<alpha>) = f i in (S, \<alpha>) \<in>  P_left G' \<and>  (\<exists>n. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
      using fi apply force using fi r(2) by force
    
    then obtain S \<alpha> where ob: "(S, \<alpha>) = f i" by auto
    with ss have "(S, \<alpha>) \<in> P_left G' \<and> (\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
              "(S, \<alpha>) \<in>  P_left G' \<and>  (\<exists>n. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))"
      using old.prod.case[of "\<lambda>S \<alpha>. (S, \<alpha>) \<in> P_left G' \<and> (\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))" S \<alpha>] apply presburger
      using ss ob old.prod.case[of "\<lambda>S \<alpha>. (S, \<alpha>) \<in> P_left G' \<and> (\<exists>n. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))" S \<alpha>] by presburger
    then have factos: "(S, \<alpha>) \<in> P_left G'" "\<exists>m. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m)"
              "\<exists>n. (P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m)" by auto
    then obtain n' m' where m': "(P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m' @ [D] ^^ m')" 
       and n': "(P_left G') \<turnstile> \<alpha> \<Rightarrow>* map Tm ([A] ^^ n' @ [B] ^^ n' @ [C] ^^ m @ [D] ^^ m)" by blast

    from factos(1) have th: "(\<exists>A. (A, \<alpha>) \<in> P_left G' \<and> Nt (Start G') = Nt A)" using fi ob by force
    from factos(1) have "(P_left G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha>" using derive_singleton[THEN iffD2, OF th] by blast
    then have "(P_left G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m' @ [D] ^^ m')" 
              "(P_left G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ([A] ^^ n' @ [B] ^^ n' @ [C] ^^ m @ [D] ^^ m)" using m' n' by auto
    (* Need to talk about the specifics here: alpha consists of Cab and Ccd's (otherwise, derives words out of language)
       Then, these parts have a distinct line they are seperated (otherwise, derives unsorted words).
        I.e., alpha = a1 @ a2 where a1 \<Rightarrow>* anbn, a2 \<Rightarrow>*cmdm \<Longrightarrow> then alpha\<Rightarrow>*anbncmdm *)

    show "((P_left G') \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m))" sorry
  qed

  have comp_eq: "{n. \<not> (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i)} = - {n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i)}" 
    by fast

  have not_nm: "\<And>n m. n \<noteq> m \<Longrightarrow> \<exists>i\<in>{1..card ?Sl}. n \<in> ?Nl i \<and> m \<in> ?Ml i"
    sorry (*use n_m_l, show that n \<in> ?Nl i \<and> m \<in> ?Ml i is implied by being in P_left's language*)


  then have "finite {n. \<not> (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i)}"
    using lemma_45[OF card_l not_nm] by blast 
  then have fin_comp1: "finite (-{n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i)})" 
    using comp_eq by argo     

  (* Similar reasoning for P_right*)
  let ?Sr = "{(S, \<alpha>) \<in> P_left G'. S = Start G' \<and> (\<exists>E \<alpha>1 \<alpha>2. \<alpha> = \<alpha>1 @ [Nt E] @ \<alpha>2)}"
  have subs: "?Sr \<subseteq> ?Sl" by force
  hence sr_f: "finite ?Sr" using finite_subset[OF subs sl_f] by linarith
  have card_r: "1 \<le> card ?Sr" sorry(* not hard to show: otherwise, language of P_right is finite 
                                      (only finite amount of S\<rightarrow>w productions)*)

  from sr_f obtain g :: "nat \<Rightarrow> ('n, t) prod" where bij: "bij_betw g {1..card ?Sr} ?Sr" (* index from 1 for proof of lemma 4.5*)
    using ex_bij_betw_nat_finite_1[OF sr_f] by blast

  have im_s: "g ` {1..card ?Sr} = ?Sr" using bij_betw_def[THEN iffD1, OF bij] by fast
  then have "{s. \<exists>i \<in> {1..card ?Sr}. s = g i} = ?Sr" unfolding image_def by fast

  then have"\<And>s. s \<in> {s. \<exists>i \<in> {1..card ?Sr}. s = g i} \<Longrightarrow> s \<in> ?Sr" by argo    
  then have"\<And>s. \<exists>i \<in> {1..card ?Sr}. s = g i \<Longrightarrow> s \<in> ?Sr" by (auto simp only: mem_Collect_eq) 
  then have i_in: "\<And>i. i \<in> {1..card ?Sr} \<Longrightarrow> g i \<in> ?Sr"  by (metis (no_types, lifting))


  let ?Nr = "\<lambda>(i::nat). {n. \<exists>S E \<alpha>1 \<alpha>2. g i = (S, \<alpha>1 @ [Nt E] @ \<alpha>2) \<and> (\<exists>m. (P_right G') \<turnstile> \<alpha>1 @ [Nt E] @ \<alpha>2 \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n))}"
  let ?Mr = "\<lambda>(i::nat). {m. \<exists>S E \<alpha>1 \<alpha>2. g i = (S, \<alpha>1 @ [Nt E] @ \<alpha>2) \<and> (\<exists>n. (P_right G') \<turnstile> \<alpha>1 @ [Nt E] @ \<alpha>2 \<Rightarrow>* map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n))}"
  let ?Sr = "{(S, \<alpha>) \<in> P_left G'. S = Start G' \<and> (\<exists>E \<alpha>1 \<alpha>2. \<alpha> = \<alpha>1 @ [Nt E] @ \<alpha>2)}"

  have inmr: "\<And>i n m. i\<in>{1..card ?Sr} \<Longrightarrow> n \<in> ?Nr i \<Longrightarrow> m \<in> ?Mr i
        \<Longrightarrow> ((P_right G') \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n))"  
    sorry
  



  have comp_eq: "{n. \<not> (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)} = - {n. (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)}" 
    by fast

  have not_nm2: "\<And>n m. n \<noteq> m \<Longrightarrow> \<exists>i\<in>{1..card ?Sr}. n \<in> ?Nr i \<and> m \<in> ?Mr i" sorry

  have "finite {n. \<not> (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)}"
    using lemma_45[OF card_r not_nm2] by blast
  
  then have fin_comp2: "finite (- {n. (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)})" 
    using comp_eq by argo

  have "finite (- {n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i)} \<union> - {n. (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)})" 
    using finite_UnI[OF fin_comp1 fin_comp2] by blast 
  hence fin_inter: "finite (- ({n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i)} \<inter> {n. (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)}))"
    by (auto simp only: Set.Compl_Int)

  have "({n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i)} \<inter> {n. (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)}) = 
        ({n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i) \<and> (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)})" 
    by blast  
  
  hence fin_comp: "finite (- ({n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i) \<and> (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)}))"
    using fin_inter by argo

  have univ_nat: "infinite (UNIV :: nat set)" by auto 


  hence inf: "infinite ({n. (\<exists>i\<in>{(1::nat)..card ?Sl}. n \<in> ?Nl i \<and> n \<in> ?Ml i) \<and> (\<exists>i\<in>{(1::nat)..card ?Sr}. n \<in> ?Nr i \<and> n \<in> ?Mr i)})"
    using finite_comp[OF fin_comp univ_nat] by simp  


  then obtain n i1 i2 where 
            i1: "i1 \<in> {(1::nat)..card ?Sl}" 
        and i2: "i2 \<in> {(1::nat)..card ?Sr}" 
        and nr: "n \<in> ?Nl i1" "n \<in> ?Ml i1" 
        and mr: "n \<in> ?Nr i2" "n \<in> ?Mr i2"
    using infinite_imp_nonempty[OF inf] by blast

  have left_der: "((P_left G') \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ n @ [D] ^^ n))"
    using inml[OF i1 nr] by argo
  
  have right_der: "((P_right G') \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ n @ [D] ^^ n))"
    using inmr[OF i2 mr] by argo  
  
  have ex: "(P_left G') \<subseteq> Prods G' \<and> (P_right G') \<subseteq> Prods G' \<and> (P_left G') \<inter> (P_right G') = {} \<and>
        (P_left G') \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ n @ [D] ^^ n) 
      \<and> (P_right G') \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ n @ [D] ^^ n)"
    using left_der right_der p_s_distinct by blast

  
  then have ex_wps: "\<exists>w P1 P2. P1 \<subseteq> Prods G' \<and> P2 \<subseteq> Prods G' \<and> P1 \<inter> P2 = {} \<and>
          P1 \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm w \<and> P2 \<turnstile> [Nt (Start G')] \<Rightarrow>+ map Tm w"
    using exI[of _  "([A] ^^ n @ [B] ^^ n @ [C] ^^ n @ [D] ^^ n)"]
          exI[of _  "P_left G'"] exI[of _  "P_right G'"] by presburger

  then have "ambiguous G'" using prod_subsets_imp_ambig[OF ex_wps] by simp
  thus "False" using G'_obtain(2) by argo
qed

end