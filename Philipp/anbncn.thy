(* 
    Author:     Bruno Philipp, TU München
*)

theory AnBnCn
  imports  "../CFG" "../Stimpfle/CNF" "HOL-Library.Sublist"
begin                           



text \<open>this theory proves that the language {@term "{word. \<exists> n. word = (a^*n)@ (b^*n) @(c^*n) }"} is not context free using the Pumping lemma for context free languages.
      This proof follows the texbook proof closely, using the same strategy to chose a word useable with the Pumping lemma.
      In comparison to the coq proof by M.V.M Ramos et al. this proof is about 10% of the length, leaving out a lot of case analysis.
      This is achieved through defining the language via the amount of different letters instead of the concrete structure of the word and a smart way of proving that the subword contains either \<open>a\<close> or \<open>c\<close> \<close>

abbreviation repl :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<^sup>*/_")
  where "xs\<^sup>*n \<equiv> concat (replicate n xs)"

theorem pumping_lemma:
  assumes "cnf G"
  shows "\<exists>n. \<forall>word \<in> L G. length word \<ge> n \<longrightarrow>
     (\<exists>u v w x y. word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G))"
  sorry


section "Preliminaries"

abbreviation repl_one :: "'a  \<Rightarrow> nat \<Rightarrow> 'a list" ("_^*_")
  where "xs^*n \<equiv> replicate n xs"

lemma count_list_replicate:"count_list (a^*n) a = n"
  by (induction n)  auto

lemma take_two: "j\<ge>i \<Longrightarrow> take i y = take i (take j y) "
  by (induction i)  auto

lemma count_list_drop: "count_list y a = 0 \<Longrightarrow> count_list (take n y) a = 0"
  by (meson count_list_0_iff in_set_takeD)


section "count and words"


lemma  c_greater_count0:
  assumes "x@y = ((a^*n)@(b^*n)@(c^*n))" "length y\<ge>n" "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows "count_list x c=0"
  using assms proof -
   have "drop (2*n) (x@y)=(c^*n)" using assms
     by simp
   then have count_c_end: "count_list (drop (2*n) (x@y)) c =n" 
     by (simp add: count_list_replicate)
   have "count_list (x@y) c= n" using count_list_replicate assms 
     by fastforce
   then have count_c_front: "count_list (take (2*n) (x@y)) c = 0" using count_c_end
     by (metis add_cancel_left_left append_take_drop_id count_list_append)
   have  "\<exists> i. length y= n+i" using assms
     by presburger
   then obtain i where "length y= n+i" 
     by blast
   then have "x= take (3*n-n-i) (x@y)" 
     by (metis append_eq_conv_conj assms(1) comm_semiring_class.distrib diff_add_inverse2 diff_diff_left length_append length_replicate mult_2 nat_mult_1 numeral_plus_numeral numerals(1) semiring_norm(3))
   then have "x=take (3*n-n-i) (take (3*n-n) (x@y))" using take_two 
     by (metis diff_le_self)
   then have "x=take (3*n-n-i) (take (2*n) (x@y))" 
     by fastforce  
   text \<open>we are using @{thm count_list_drop} as we have proven {@term "count_list (take (2*n) (x@y)) c = 0} and {@term "x=take (3*n-n-i) (take (2*n) (x@y))"}\<close>
  then show ?thesis using count_c_front count_list_drop
     by (metis add.commute add_diff_cancel_left' diff_mult_distrib mult_numeral_1_right nat_mult_1 numeral_Bit1_eq_inc_double)
qed

lemma  a_greater_count0:
  assumes "x@y = ((a^*n)@(b^*n)@(c^*n)) " "length x\<ge>n" "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows "count_list y a=0"
  text \<open>this prof is easier than @{thm c_greater_count0} since a is at the start of the word rather than at the end \<close>
  using assms proof -
  have count_whole: "count_list (x@y) a = n" using assms count_list_replicate 
    by fastforce
  have take_n:"take (n) (x@y)=(a^*n)" using assms
    by simp
  then have count_take_n: "count_list (take (n) (x@y)) a = n" 
    by (simp add: count_list_replicate)
  have "\<exists> z. x=(take n (x@y))@z" 
    by (metis append_eq_conv_conj assms(2) nat_le_iff_add take_add)
  then have  count_a_x:"count_list x a =n" using count_take_n take_n count_whole 
    by (metis add_diff_cancel_left' append.right_neutral count_list_append diff_add_zero)
  have "count_list (x@y) a= n" using count_list_replicate assms 
     by fastforce
  then have "count_list y a =0" using count_a_x
    by simp
  then show ?thesis
    by presburger
qed



lemma a_or_b_zero:
  assumes  "a\<noteq>b" "b\<noteq>c" "c\<noteq>a" "u@w@y= ((a^*n)@ (b^*n) @(c^*n))" "length w\<le>n"
  shows "count_list w a =0\<or> count_list w c=0"
  text \<open>This lemma uses @{term "count_list (w) a=0\<or>count_list w c=0 "} similar to all following proofs, focusing on the number of \<open>a\<close> and \<open>c\<close> found in \<open>w\<close> rather than the concrete structure.
        It is also the merge of the two previous lemmas to make the final proof shorter\<close>
  using assms proof-
  show ?thesis using assms proof (cases "length u <n")
    case True 
    have "length (u@w@y) = 3*n"  using assms 
      by fastforce  
    then have "length u+ length w +length y= 3*n" 
      by auto
    then have "length u+ length y\<ge>2 *n" using assms 
      by linarith
    then have u_or_y: "length u\<ge>n \<or> length y \<ge>n" 
      by linarith
    then  have "length y\<ge>n" using True  
      by fastforce
    then show ?thesis using c_greater_count0[of "u@w" y n a b c ] assms 
      by force
  next
    case False
    then have "length u\<ge>n" 
      by simp
    then show ?thesis using a_greater_count0[of u "w@y" n a b c ]  assms 
      by auto
  qed
qed

lemma in_set_one_not0:
  assumes "v \<noteq>[]" " sublist v x "
  shows " \<exists> a\<in> set(x). count_list v a\<noteq>0"
proof -
  have "set v \<subseteq> set x" 
    by (simp add: assms(2) set_mono_sublist)
  then show ?thesis 
    by (metis assms(1) count_list_0_iff count_list_replicate replicate_0 replicate_length_same subset_iff)
qed

lemma count_vx_not_zero:
  assumes "u@v@w@x@y= ((a^*n)@ (b^*n) @(c^*n)) " " (v@x)\<noteq>[] " "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows " (count_list (v@x) a) \<noteq>0 \<or> (count_list (v@x) b)\<noteq>0 \<or> (count_list (v@x) c) \<noteq>0 "
proof -
  have sublist_v: "sublist (v) ((a^*n)@(b^*n) @(c^*n))" using assms 
    by (metis sublist_appendI)
  have sublist_x: "sublist (x) ((a^*n)@(b^*n) @(c^*n))" using assms 
    by (metis append.assoc sublist_appendI)
  have set: "set ((a^*n)@ (b^*n) @(c^*n)) = {a,b,c}" using assms 
    by fastforce
  show ?thesis proof (cases  "v\<noteq>[]")
    case True
    then  have "\<exists> d\<in>set ((a^*n)@(b^*n) @(c^*n)).  count_list v d \<noteq>0" using  set in_set_one_not0 sublist_v 
      by blast
    then have "(count_list (v) a) \<noteq>0 \<or> (count_list (v) b)\<noteq>0 \<or> (count_list (v) c) \<noteq>0 " using set 
      by simp
    then show ?thesis 
      by force
  next
    case False
    then have "x\<noteq>[]" using assms 
      by fast
    then  have "\<exists> d\<in>set ((a^*n)@(b^*n) @(c^*n)).  count_list x d \<noteq>0" using  set in_set_one_not0 sublist_x
       by blast
    then have "(count_list (x) a) \<noteq>0 \<or> (count_list (x) b)\<noteq>0 \<or> (count_list (x) c) \<noteq>0 " using set 
       by simp
    then show ?thesis 
       by force
   qed
qed

section "language definition via count"
lemma  not_ex_y_count:
  assumes "i\<noteq>k\<or> k\<noteq>j \<or> i\<noteq>j" "a\<noteq>b" "b\<noteq>c" "a\<noteq> c" "count_list w a=i"  "count_list w b=k"  "count_list w c=j"
  shows "\<not>(EX y. w= (a^*y)@(b^*y)@(c^*y))"
 proof 
   assume "(EX y. w= (a^*y)@(b^*y)@(c^*y))"
   then  obtain y where y: " w= (a^*y)@(b^*y)@(c^*y)" 
     by blast
   then have "count_list w a= y" using count_list_replicate assms 
     by force
   then have i_eq_y: "i=y" using assms 
     by argo
   then have "count_list w b= y" using count_list_replicate assms y  append_eq_append_conv2 append_self_conv count_list_append  
     by (smt (verit, ccfv_threshold) count_list.simps(1) count_notin in_set_replicate)
   then have k_eq_y: "k=y" using assms 
     by argo
   have "count_list w c= y" using count_list_replicate assms y
     by fastforce
   then have j_eq_y: "j=y" using assms  
     by argo
   show False  using i_eq_y k_eq_y j_eq_y assms 
      by presburger
 qed

lemma not_in_count:
  assumes "a\<noteq>b" "b\<noteq>c" "a\<noteq> c" "(count_list w a\<noteq>count_list w b) \<or> (count_list w b\<noteq> count_list w c) \<or> (count_list w c \<noteq> count_list w a)"
  shows "w \<notin> {word. \<exists> n.  word= (a^*n)@(b^*n)@(c^*n)}"
  text \<open>This lemma is the biggest line saver, because proving that a word has a different number of \<open>a\<close>, \<open>b\<close> or \<open>c\<close> is easier than proving something more specific\<close>
  using assms not_ex_y_count
  by (smt (verit, del_insts) mem_Collect_eq)

section "a^n b^n c^n is not contextfree"

lemma  pumping_application:
  assumes  "a\<noteq>b" "b\<noteq>c" "c\<noteq>a" "u@v@w@x@y= (a^*n)@ (b^*n) @(c^*n)" "count_list (v@w@x) a=0 \<or> count_list (v@w@x) c=0" "v@x\<noteq>[]"
  shows "u@w@y \<notin> {word. \<exists> n.  word= (a^*n)@(b^*n)@(c^*n)}"
  text \<open>In this lemma it is proven that a word  @{term "u@(v\<^sup>*0)@w@(x\<^sup>*0)@y"} is not in the language @{term "{word. \<exists> n.  word= (a^*n)@(b^*n)@(c^*n)}"} as this is the easiest counterexample
        useful for the Pumping lemma\<close>
proof-
  have count_word_a: "count_list (u@v@w@x@y) a = n" using add_diff_cancel_right' append_eq_append_conv2 assms(1) assms(2) assms(3) assms(4) count_list_append count_list_replicate 
    by fastforce
  have count_word_b: "count_list (u@v@w@x@y) b = n" using add_diff_cancel_right' append_eq_append_conv2 assms(1) assms(2) assms(3) assms(4) count_list_append count_list_replicate 
    by fastforce
  have count_word_c: "count_list (u@v@w@x@y) c = n" using add_diff_cancel_right' append_eq_append_conv2 assms(1) assms(2) assms(3) assms(4) count_list_append count_list_replicate 
    by fastforce
  have count_non_zero: "((count_list (v@x) a) \<noteq>0) \<or> (count_list (v@x) b\<noteq>0) \<or> (count_list (v@x) c \<noteq> 0)" using count_vx_not_zero[of u v w x y n a b c] assms
    by simp  
  consider "count_list (v@w@x) a=0"|"count_list (v@w@x) c=0" using assms 
    by argo
  then show ?thesis proof (cases)
    case 1
    then have  vx_b_or_c_not0: "(count_list (v@x) b\<noteq>0) \<or> (count_list (v@x) c \<noteq> 0)" using  count_non_zero
      by fastforce
    have "count_list (v@x) a =0" using 1 
      by fastforce
    then have uwy_count_a: "count_list (u@w@y) a=n" using 1 count_word_a 
      by auto 
    have "count_list (u@w@y) b \<noteq>n \<or> count_list (u@w@y) c \<noteq>n" using vx_b_or_c_not0 count_word_b count_word_c 
      by force
    then have "(count_list (u@w@y) a \<noteq> count_list (u@w@y) b) \<or> (count_list (u@w@y) c \<noteq> count_list (u@w@y) a)" using uwy_count_a
      by argo
    then show ?thesis using assms  not_in_count[of a b c "u@w@y" ] 
      by blast
  next
    case 2
    then have vx_a_or_b_not0: "(count_list (v@x) a\<noteq>0) \<or> (count_list (v@x) b \<noteq> 0)" using  count_non_zero
      by fastforce
    have "count_list (v@x) c =0" using 2
      by fastforce
    then have uwy_count_c: "count_list (u@w@y) c=n" using 2 count_word_c 
      by auto 
    have "count_list (u@w@y) a \<noteq>n \<or> count_list (u@w@y) b \<noteq>n" using vx_a_or_b_not0 count_word_a count_word_b
      by force
    then have "(count_list (u@w@y) a \<noteq> count_list (u@w@y) b) \<or> (count_list (u@w@y) c \<noteq> count_list (u@w@y) a)" using uwy_count_c
      by argo
    then show ?thesis using assms  not_in_count[of a b c "u@w@y" ] 
      by blast  
  qed
qed

theorem anbncn_not_cnf:
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"  "(L G = {word. \<exists> n.  word= (a^*n)@ (b^*n) @(c^*n) })"
  shows "\<not> cnf G  "
proof 
  assume cnf :"cnf G"
  then have pump:"\<exists>n. \<forall>word \<in> L G . length word \<ge> n \<longrightarrow>
     (\<exists>u v w x y. word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G))" using assms pumping_lemma 
    by blast
  then obtain n where a: "\<forall>word \<in> L G . length word \<ge> n \<longrightarrow>
     (\<exists>u v w x y. word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G))" 
    by blast
  let ?word ="(a^*n)@ (b^*n) @(c^*n)"
  have wInLg: "?word \<in> L G" using assms 
    by blast  
  have "length ?word \<ge> n" 
    by simp
  then  have pumpie: "(\<exists>u v w x y. ?word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G))" using a wInLg 
    by blast
  then obtain u v w x y where  uvwxy:" ?word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G)" 
    by blast
  let ?vwx= "v@w@x"
  have "sublist ?vwx ?word"  
    by (metis append.assoc sublist_appendI uvwxy)
  have "(count_list ?vwx  a=0 ) \<or> (count_list ?vwx c=0)" using  uvwxy a_or_b_zero assms 
    by (metis (no_types, lifting) append.assoc)
  text \<open>This theorem follows the texbook proof closely, we are choosing the \<open>?word\<close>  based on the pumping lemma number \<open>n\<close> 
        then we note that  @{term "(count_list ?vwx  a=0 ) \<or> (count_list ?vwx c=0)"} similar to the textbook proof 
        and finally applying @{thm pumping_application} to show that there is a word not in the language @{term "{word. \<exists> n.  word= (a^*n)@ (b^*n) @(c^*n) }"}\<close>
  then show False using  assms uvwxy pumping_application[of a b c u v w x y n]  
    by (metis (mono_tags, lifting) concat.simps(1) list.size(3) not_one_le_zero replicate_empty self_append_conv2)
qed

end
