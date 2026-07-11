theory Ambig_Lang_Aux
imports 
  Main
  Non_Terms
  Derives_Aux
begin

section "Lemmas about the nature of the language 
        \<open>(\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m}) \<union> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n})\<close>"

subsection "1) Definition of \<open>L_left\<close>, \<open>L_right\<close>, and \<open>L_ambig\<close>"

text "Defining abbreviations for the both sides of the union is beneficial, especially in cases
     we need to have case distinctions."
abbreviation L_left :: "(t list) set" where "L_left \<equiv> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m})"
abbreviation L_right :: "(t list) set" where "L_right \<equiv> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n})"
abbreviation L_ambig :: "(t list) set" where "L_ambig \<equiv> L_left \<union> L_right"

subsection "2) Well-sortedness of the language (w.r.t \<open>A < B < C < D\<close>)"

text "Every word in our language needs to be sorted w.r.t. \<open>A < B < C < D\<close>:"
lemma w_sorted:
  fixes w :: "t list"
  assumes "w \<in> L_ambig"
  shows "sorted w"
proof -
  from assms obtain n m l k where nmlk_obtain: "w = [A]^^n @ [B]^^m @ [C]^^k @ [D]^^l" by blast

  have sorted_single: "sorted ([A]^^n)" "sorted ([B]^^m)" "sorted ([C]^^k)"  "sorted ([D]^^l)"
    by (auto simp add: nth_pow_list_single iff: sorted_wrt_iff_nth_less)
    
  from this(1,2) have ab_sorted: "sorted ([A]^^n @ [B]^^m)" 
    using sorted_append  
    by fastforce  
  from sorted_single(3,4) have cd_sorted: "sorted ([C]^^k @ [D]^^l)"
    using sorted_append  
    by fastforce  
    
  have ranks: "A < C" "A < D" "B < C" "B < D"
    using less_t_def by auto

  from ab_sorted cd_sorted have "sorted (([A]^^n @ [B]^^m @ [C]^^k @ [D]^^l))"
     using ranks 
     by (auto simp add: sorted_append)

  then show "sorted w" using nmlk_obtain by auto
qed

text "Different way to say: every word in our language needs to be sorted w.r.t. \<open>a<b<c<d\<close>."
corollary w_sorted_ij:
  fixes w :: "t list"
  assumes "w \<in> L_ambig"
  shows "\<And>i j. i < j \<and> j < length w \<Longrightarrow> (w ! i) \<le> (w ! j)"
  using sorted_wrt_iff_nth_less w_sorted[OF assms]
  by blast


subsection "3) Counts of non-terminals"

text "Here, we prove some lemmas regarding the count of non-terminals in the language."

subsubsection "3.1) Equality of non-terminal counts in the two sides of the language"

text "If \<open>w \<in> L_left\<close>, then \<open>|w|_a=n,|w|_b=n,|w|_c=m,|w|_d=m\<close> for some \<open>n,m\<close>"
lemma w_len_eqn_left:
  fixes w :: "t list" 
  assumes "w \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m})"
  shows "\<exists>n m. (count_list w A = n \<and> count_list w B = n \<and> count_list w C = m \<and> count_list w D = m)" 
  using assms by (auto simp add: count_list_pow_list)

text "If \<open>w \<in> L_left\<close>, then \<open>|w|_a=|w|_b,|w|_c=|w|_d\<close>."
lemma w_len_eq_left:
  fixes w :: "t list" 
  assumes "w \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^n @ [C]^^m @ [D]^^m})"
  shows "count_list w A = count_list w B \<and> count_list w C = count_list w D" 
  using assms by (auto simp add: count_list_pow_list)

text "If \<open>w \<in> L_right\<close>, then \<open>|w|_a=n,|w|_b=m,|w|_c=m,|w|_d=n\<close> for some \<open>n,m\<close>"
lemma w_len_eqn_right:
  fixes w :: "t list" 
  assumes "w \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n})"
  shows "\<exists>n m. (count_list w A = n \<and> count_list w B = m \<and> count_list w C = m \<and> count_list w D = n)"
  using assms by (auto simp add: count_list_pow_list)


text "If \<open>w \<in> L_right\<close>, then \<open>|w|_a=|w|_d,|w|_b=|w|_c\<close>."
lemma w_len_eq_right:
  fixes w :: "t list" 
  assumes "w \<in> (\<Union>n.\<Union>m. {[A]^^n @ [B]^^m @ [C]^^m @ [D]^^n})"
  shows "count_list w A = count_list w D \<and> count_list w B = count_list w C"
  using assms by (auto simp add: count_list_pow_list)

text "Putting together: If \<open>w \<in> L_ambig\<close>, then \<open>|w|_a=|w|_b,|w|_c=|w|_d\<close> or 
     \<open>|w|_a=|w|_d,|w|_b=|w|_c\<close>."
corollary w_len_eq:
  fixes w :: "t list" 
  assumes "w \<in> L_ambig"
  shows "((count_list w A = count_list w B) \<and> (count_list w C = count_list w D)) 
          \<or> ((count_list w A = count_list w D) \<and> (count_list w B = count_list w C))" 
  using assms by (cases "w \<in> L_left"; simp add: w_len_eq_left; simp add: w_len_eq_right)

subsubsection "3.1) Count conditions for words outside of the language"

text "If the count of one character is not equal to any other character in a word, this word cannot
      be in the language."
lemma w_len_not_eq:
  fixes w :: "t list" 
  assumes "\<exists>c. \<forall>c'\<noteq>c. (count_list w c \<noteq> count_list w c')"
  shows "w \<notin> L_ambig"
  using w_len_eq[of w] assms t.exhaust t.distinct(1,11,5,7) by (metis (full_types))

text "Contraposition of the lemma \<open>w_len_eq\<close>"
lemma w_len_neq:
  fixes w w' :: "t list"
  assumes
    not_in_left: "((count_list w A \<noteq> count_list w B) \<or> (count_list w C \<noteq> count_list w D))" and
    not_in_right: "((count_list w A \<noteq> count_list w D) \<or> (count_list w B \<noteq> count_list w C))"
  shows "w \<notin> L_ambig"
  using assms contrapos_nn[OF _ w_len_eq[of w]] by blast


text "Given a word in the language, if the count of one character of the word is changed, while the count 
      of all the other characters stay the same, then the resulting word is not in the language"
lemma w_lens_not_in_L:
  fixes w w' :: "t list"
  assumes 
    w_in_L: "w \<in> L_ambig" and
    there_is_a_c: "\<exists>c. count_list w' c \<noteq> count_list w c \<and> (\<forall>x \<noteq> c. count_list w' x = count_list w x)"
  shows "w' \<notin> L_ambig"
proof - 
  from w_in_L have "w \<in> L_left \<or> w \<in> L_right" by auto
  then have cs: "(count_list w A = count_list w B  \<and> count_list w C = count_list w D) \<or> (count_list w A = count_list w D \<and> count_list w B = count_list w C)"
    using w_len_eq_left w_len_eq_right by presburger 
  from there_is_a_c obtain c where c_obtain: "count_list w' c \<noteq> count_list w c \<and> (\<forall>x \<noteq> c. count_list w' x = count_list w x)" by blast
  show ?thesis using cs t.distinct(1,11,5,7) t.exhaust c_obtain w_len_eq[of w'] by smt
qed

subsection "Lemmas involving power lists"

text "The set of a non-empty singleton power list is a singleton set."
lemma singleton_pow_set:
  assumes "x = [sx] ^^ (length x)"
  shows "length x > 0 \<Longrightarrow> set x = {sx}"
using assms pow_list_set_if[of "length x" "[sx]"] by simp

text "With this lemma and its corollary, we prove that any list with same character \<open>s\<close> repeating 
      throughout its length is a singleton power list"
lemma singleton_power:
  fixes x :: "'t list" and s :: "'t" 
  assumes "\<forall>i < length x. x ! i = s"
  shows "x = [s] ^^ (length x)"
using assms by (induct x; auto; fastforce)

corollary singleton_power_iff:
  fixes x :: "'t list" and s :: "'t" 
  shows  "(\<forall>i < length x. x ! i = s) = (x = [s] ^^ (length x))"
  by (auto simp add: singleton_power dest: nth_pow_list_single[of _ "length x" "s"])  


section "Lemmas about classes"

text "Our proof defines the following classes, which classify all the non-terminals other than \<open>S\<close> into 
     one distinct class."

subsection "1) Defining the classes"

text "To use as a generalization to use in our proofs, we start with \<open>C_set\<close>. It does not exclude cases
      not possible in our grammar."
abbreviation(input) C_set :: "t \<Rightarrow> t \<Rightarrow> ('n, t) Cfg \<Rightarrow> 'n set" ("Cset")
  where "C_set c1 c2 G \<equiv> {X. \<exists>l > 0. (Prods G) \<turnstile> [Nt X] \<Rightarrow>* (map Tm [c1] ^^ l) @ [Nt X] @ (map Tm [c2] ^^ l)}"

text "The cases in our grammar are as follows:"
abbreviation(input) Cab :: "('n, t) Cfg \<Rightarrow> 'n set" ("Cab") where "Cab \<equiv> Cset A B"
abbreviation(input) Cad :: "('n, t) Cfg \<Rightarrow> 'n set" ("Cad") where "Cad \<equiv> Cset A D"
abbreviation(input) Cbc :: "('n, t) Cfg \<Rightarrow> 'n set" ("Cbc") where "Cbc \<equiv> Cset B C"
abbreviation(input) Ccd :: "('n, t) Cfg \<Rightarrow> 'n set" ("Ccd") where "Ccd \<equiv> Cset C D"


text "The classes of productions \<open>P_left\<close> is defined as productions that have a variable from Cab or Ccd on
     either right or left. In addition, it contains all productions of form \<open>S \<rightarrow> a^n||b^n||c^m||d^m\<close> with 
     \<open>n \<noteq> m\<close>. Analogous for \<open>P_right\<close>"
abbreviation P_left :: "('n, t) Cfg \<Rightarrow> ('n, t) Prods" ("P_left")
  where "P_left G \<equiv> 
      {(X, \<alpha>). (X, \<alpha>) \<in> Prods G \<and> (X \<in> Cab G \<union> Ccd G \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cab G \<union> Ccd G))}
      \<union> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G \<and> X = Start G \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m) \<and> n \<noteq> m)} "

abbreviation(input) P_right :: "('n, t) Cfg \<Rightarrow> ('n, t) Prods" ("P_right")
  where "P_right G \<equiv> 
      {(X, \<alpha>). (X, \<alpha>) \<in> Prods G \<and> (X \<in> Cad G \<union> Cbc G \<or> (\<exists>s \<in> Nts_syms \<alpha>. s \<in> Cad G \<union> Cbc G))}
      \<union> {(X, \<alpha>). (X, \<alpha>) \<in> Prods G \<and> X = Start G \<and> (\<exists>n m. \<alpha> = map Tm ([A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n) \<and> n \<noteq> m)} "

notation
  P_left (\<open>Pleft\<close>) and
  P_right (\<open>Pright\<close>) and
  Cab (\<open>Cab\<close>) and
  Cad (\<open>Cad\<close>) and
  Cbc (\<open>Cbc\<close>) and
  Ccd (\<open>Ccd\<close>) and
  C_set (\<open>Cset\<close>)
declare [[show_abbrevs]]

subsection "2) Proving that the 4 classes and singleton set \<open>{S}\<close> form disjoint and complete classes"

subsubsection "2.1) Proving the classes are disjoint"


text "Fact 4 is exactly needed to show the distinctness of each class. With the assumption of the fact 1,
      it is easy to show that any variable should not be in two classes, pumping 3 characters at once.
      Fact 4: If \<open>X \<Rightarrow>* sXt\<close> and \<open>X \<Rightarrow>* uXv\<close>, then \<open>X\<Rightarrow>*usXtv\<close> and \<open>X\<Rightarrow>*suXvt\<close>. Hence, (Fact 1) needs to 
      hold also for \<open>u,s\<close> and \<open>t,v\<close> pairs."
lemma two_derivs: 
  fixes G' :: "('n, 't) Cfg"
  assumes  xy_non_empty_distinct_singleton_pow_lists:
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> \<exists>s1 s2. (s1 \<noteq> s2) \<and> x = [s1] ^^ (length x) \<and>  y = [s2] ^^ (length x)" 
  shows
   "\<And>X s t u v. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm s @ [Nt X] @ map Tm t \<Longrightarrow> 
                (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm u @ [Nt X] @ map Tm v 
      \<Longrightarrow> \<exists>s1 s2. (s1 \<noteq> s2) \<and> s = [s1] ^^ (length s) \<and> u = [s1] ^^ (length u) \<and> t = [s2] ^^ (length t) \<and> v = [s2] ^^ (length v)" 
proof -   
  fix X s t u v
  assume prods:"(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm s @ [Nt X] @ map Tm t" "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm u @ [Nt X] @ map Tm v" 
  then have prod1: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>*  map Tm (s @ u) @ [Nt X] @  map Tm (v @ t)"
    using rtranclp_trans[OF prods(1) derives_append[OF prods(2), of "map Tm t", THEN derives_prepend, of "map Tm s"]] by simp

  have comb1: 
   " \<exists>s1 s2. (s1 \<noteq> s2) \<and> (s @ u) = [s1] ^^ (length (s @ u)) \<and> (v @ t) = [s2] ^^ (length (v @ t))"
    using xy_non_empty_distinct_singleton_pow_lists[OF prod1] by fastforce    
  
  thus "\<exists>s1 s2. (s1 \<noteq> s2) \<and> s = [s1] ^^ (length s) \<and> u = [s1] ^^ (length u) \<and> t = [s2] ^^ (length t) \<and> v = [s2] ^^ (length v)"
    by (auto simp add: pow_list_add)
qed

text "Assuming the fact 1, we can show that the \<open>C\<close> classes are distinct"
lemma disjoints:  
  assumes  xy_non_empty_distinct_singleton_pow_lists:
     "\<And>X x y. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y 
        \<Longrightarrow> \<exists>s1 s2. (s1 \<noteq> s2) \<and> x = [s1] ^^ (length x) \<and>  y = [s2] ^^ (length x)"
   shows "Cab G' \<inter> Cad G' = {} \<and> Cab G' \<inter> Cbc G' = {} \<and> Cab G' \<inter> Ccd G' = {} \<and> Cad G' \<inter> Cbc G' = {} \<and> Cad G' \<inter> Ccd G' = {} \<and> Cbc G' \<inter> Ccd G' = {}"
proof (rule ccontr)
  assume "\<not>?thesis"
  then have "Cset A B G' \<inter> Cset A D G' \<noteq> {} \<or> Cset A B G' \<inter> Cset B C G' \<noteq> {} \<or> Cset A B G' \<inter> Cset C D G' \<noteq> {} \<or> Cset A D G' \<inter> Cset B C G' \<noteq> {} \<or> Cset A D G' \<inter> Cset C D G' \<noteq> {} \<or> Cset B C G' \<inter> Cset C D G' \<noteq> {}" 
    by auto
  then obtain c1 c2 c3 c4 where c_s_obtain: "C_set c1 c2 G' \<inter> C_set c3 c4 G' \<noteq> {}" "(c1, c2) \<in> {(A, B), (A, D), (B, C), (C, D)}" "(c3, c4) \<in> {(A, B), (A, D), (B, C), (C, D)}" "(c1, c2) \<noteq> (c3, c4)"
    by blast
  then obtain X where "X \<in> C_set c1 c2 G' \<inter> C_set c3 c4 G'" by blast
  then obtain l1 l2 where prod: "Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm [c1] ^^ l1 @ [Nt X] @ map Tm [c2] ^^ l1 \<and> Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm [c3] ^^ l2 @ [Nt X] @ map Tm [c4] ^^ l2" "l1 > 0 " "l2 > 0"
    by blast
  then obtain s1 s2 where  "(s1 \<noteq> s2) \<and> [c1] ^^ l1 = [s1] ^^ (length ([c1] ^^ l1)) \<and> [c3] ^^ l2 = [s1] ^^ (length ([c3] ^^ l2)) \<and> [c2] ^^ l1 = [s2] ^^ (length ([c2] ^^ l1)) \<and> [c4] ^^ l2 = [s2] ^^ (length ([c4] ^^ l2))"
    using two_derivs[of G' X "[c1] ^^ l1" "[c2] ^^ l1" "[c3] ^^ l2" "[c4] ^^ l2", OF xy_non_empty_distinct_singleton_pow_lists] by fastforce

  then have  "[c1] ^^ l1 = [s1] ^^ l1 \<and> [c3] ^^ l2 = [s1] ^^ l2 \<and> [c2] ^^ l1 = [s2] ^^ l1 \<and> [c4] ^^ l2 = [s2] ^^ l2" by auto
  with c_s_obtain(4) show False using prod(2,3) pow_eq_eq by blast
qed

text "We are left with the singleton set \<open>{S}\<close> being disjoint. We can then formulate this as follows:
      Assuming the language of \<open>G'\<close> is \<open>L_ambig\<close>, we can show that the \<open>S\<close> is not in any of our classes"
lemma start_not_in_classes:
  assumes langG': "LangS G' = L_ambig"
  shows "Start G' \<notin> Cab G' \<union> Ccd G' \<union> Cad G' \<union> Cbc G'"
proof (rule ccontr)   
  assume "\<not> Start G' \<notin> Cab G' \<union> Ccd G' \<union> Cad G' \<union> Cbc G'"
  then obtain c1 c2 where in_c: "Start G' \<in> Cset c1 c2 G'" and
      c_neq: "c1 \<noteq> c2" and
      c_cases: "(c1 = A \<and> c2 = B) \<or> (c1 = C \<and> c2 = D) \<or> (c1 = A \<and> c2 = D) \<or> (c1 = B  \<and> c2 = C)" 
    by blast

  let ?S = "Start G'"

  from in_c obtain l where 
    l_obtains: "l>0" "Prods G' \<turnstile> [Nt ?S] \<Rightarrow>* map Tm [c1] ^^ l @ [Nt ?S] @ (map Tm [c2] ^^ l)" by blast
  let ?x = "map Tm [c1] ^^ l" let ?y = "map Tm [c2] ^^ l"    
  let ?px = "[c1] ^^ l" let ?py = "[c2] ^^ l"
  let ?c = "\<lambda>w s. count_list w s"

  have xx_cs: "count_list ?px c1 = l" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?px c = 0" and
       yy_cs: "count_list ?py c2 = l" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?py c = 0" 
    using count_list_pow_list[of l "[c1]"] count_list_pow_list[of l "[c2]"] by auto


  have "LangS G' = L_left \<union> L_right" using langG' by auto
  then have l_to_lang: "\<And>w. w \<in> L_left \<Longrightarrow> w \<in> LangS G'" 
          "\<And>w. w \<in> L_right \<Longrightarrow> w \<in> LangS G'" by auto

  obtain n m where w_obtains:
    "[A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m \<in> L_left" 
    "[A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n \<in> L_right" 
                     "n \<noteq> m" by fastforce
  let ?w1 = "[A] ^^ n @ [B] ^^ n @ [C] ^^ m @ [D] ^^ m" 
  let ?w2 = "[A] ^^ n @ [B] ^^ m @ [C] ^^ m @ [D] ^^ n" 

  from w_obtains have "?w1 \<in> LangS G'" "?w2 \<in> LangS G'" using l_to_lang by auto
  hence word_deriv: "Prods G' \<turnstile> [Nt ?S] \<Rightarrow>* map Tm ?w1" "Prods G' \<turnstile> [Nt ?S] \<Rightarrow>* map Tm ?w2"
    unfolding Lang_def using langG' by auto

  let ?w1l = "length ?w1 + 1" let ?w2l = "length ?w2 + 1" 
  let ?xx1 = "?x ^^ ?w1l" let ?yy1 = "?y ^^ ?w1l" let ?xx2 = "?x ^^ ?w2l" let ?yy2 = "?y ^^ ?w2l" 
  let ?px1 = "?px ^^ ?w1l" let ?py1 = "?py ^^ ?w1l" let ?px2 = "?px ^^ ?w2l" let ?py2 = "?py ^^ ?w2l" 
  have x1_pow_cs: "count_list ?px1 c1 = ?w1l * l" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?px1 c = 0" and
       y1_pow_cs: "count_list ?py1 c2 = ?w1l * l" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?py1 c = 0" and
       x2_pow_cs: "count_list ?px2 c1 = ?w2l * l" "\<And>c. c \<noteq> c1 \<Longrightarrow> count_list ?px2 c = 0" and
       y2_pow_cs: "count_list ?py2 c2 = ?w2l * l" "\<And>c. c \<noteq> c2 \<Longrightarrow> count_list ?py2 c = 0" 
    using count_list_pow_list[of ?w1l "?px"] xx_cs count_list_pow_list[of ?w2l "?px"]
          count_list_pow_list[of ?w1l "?py"] yy_cs count_list_pow_list[of ?w2l "?py"] by auto
  

  have derives_xy1: "Prods G' \<turnstile> [Nt ?S] \<Rightarrow>* ?xx1 @ [Nt ?S] @ ?yy1"
    using derives_forever[OF l_obtains(2), of ?w1l] by simp
  have derives_xy2: "Prods G' \<turnstile> [Nt ?S] \<Rightarrow>* ?xx2 @ [Nt ?S] @ ?yy2"
    using derives_forever[OF l_obtains(2), of ?w2l] by simp

  have "Prods G' \<turnstile> ?xx1 @ [Nt ?S] @ ?yy1 \<Rightarrow>* ?xx1 @ map Tm ?w1 @ ?yy1" 
    using derives_prepend[OF derives_append[OF word_deriv(1), of ?yy1], of ?xx1] by simp
  hence "Prods G' \<turnstile> [Nt ?S] \<Rightarrow>* ?xx1 @ map Tm ?w1 @ ?yy1" 
    using derives_xy1 by simp
  hence "?px1 @ ?w1 @ ?py1 \<in> LangS G'" unfolding Lang_def by simp
  hence w1_in_L: "?px1 @ ?w1 @ ?py1 \<in> L_ambig" using langG' by simp


  have "Prods G' \<turnstile> ?xx2 @ [Nt ?S] @ ?yy2 \<Rightarrow>* ?xx2 @ map Tm ?w2 @ ?yy2" 
    using derives_prepend[OF derives_append[OF word_deriv(2), of ?yy2], of ?xx2] by simp
  hence "Prods G' \<turnstile> [Nt ?S] \<Rightarrow>* ?xx2 @ map Tm ?w2 @ ?yy2" 
    using derives_xy2 by simp
  hence "?px2 @ ?w2 @ ?py2 \<in> LangS G'" unfolding Lang_def by simp
  hence w2_in_L: "?px2 @ ?w2 @ ?py2 \<in> L_ambig" using langG' by simp

  have len_too_big1: "l * ?w1l > n" "l * ?w1l > m" 
    using l_obtains(1) mult_le_cancel2[of 1 ?w1l l] by auto
  have len_too_big: "l * ?w2l > n" "l * ?w2l > m" 
    using l_obtains(1) mult_le_cancel2[of 1 ?w2l l] by auto
    

  consider (c_left) "(c1 = A \<and> c2 = B) \<or> (c1 = C  \<and> c2 = D)" |
           (c_right) "(c1 = A \<and> c2 = D) \<or> (c1 = B  \<and> c2 = C)" using c_cases by argo
  then show False 
  proof cases
    case c_left      
    let ?ww2 = "?px2 @ ?w2 @ ?py2"
    have "?c ?ww2 c1 = ?c ?px2 c1 + ?c ?w2 c1 + ?c ?py2 c1" by simp
    hence c_c1: "?c ?ww2 c1 = ?c ?w2 c1 + ?w2l * l" using x2_pow_cs(1) y2_pow_cs(2)[OF c_neq] by presburger

    have "?c ?ww2 c2 = ?c ?px2 c2 + ?c ?w2 c2 + ?c ?py2 c2" by simp
    hence c_c2: "?c ?ww2 c2 = ?c ?w2 c2 + ?w2l * l" using x2_pow_cs(2)[OF c_neq[symmetric]] y2_pow_cs(1) by presburger

    have c_c3:  "\<And>c3. c3\<noteq>c1 \<Longrightarrow> c3\<noteq>c2 \<Longrightarrow> ?c ?ww2 c3 = ?c ?w2 c3" by simp
      
    consider "(c1 = A \<and> c2 = B)" | "(c1 = C \<and> c2 = D)" using c_left by auto
    then have "?ww2 \<notin> L_ambig"
    proof cases
      case 1
      then have case_dist: 
      "?c ?ww2 A = n + l * ?w2l \<and> ?c ?ww2 B = m + l * ?w2l \<and> ?c ?ww2 C = m \<and> ?c ?ww2 D = n" 
        using c_c1 c_c2 c_c3 w_obtains(1) t.distinct by (simp add: count_list_pow_list)
      have "?c ?ww2 A \<noteq> ?c ?ww2 B" using case_dist w_obtains(3) by linarith
      moreover have "?c ?ww2 A \<noteq> ?c ?ww2 C" using case_dist len_too_big by linarith 
      moreover have "?c ?ww2 A \<noteq> ?c ?ww2 D" using case_dist len_too_big by linarith 
      ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?ww2 c \<noteq> count_list ?ww2 c'" 
        using exI[of _ A] t.exhaust by blast 
      then show ?thesis using w_len_not_eq[OF ex] by presburger
    next
      case 2
      then have case_dist: 
      "?c ?ww2 A = n \<and> ?c ?ww2 B = m \<and> ?c ?ww2 C = m + l * ?w2l \<and> ?c ?ww2 D = n + l * ?w2l" 
        using c_c1 c_c2 c_c3 w_obtains(1) t.distinct by (simp add: count_list_pow_list)
      have "?c ?ww2 A \<noteq> ?c ?ww2 B" using case_dist w_obtains(3) by linarith
      moreover have "?c ?ww2 A \<noteq> ?c ?ww2 C" using case_dist len_too_big by linarith 
      moreover have "?c ?ww2 A \<noteq> ?c ?ww2 D" using case_dist len_too_big by linarith 
      ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?ww2 c \<noteq> count_list ?ww2 c'" 
        using exI[of _ A] t.exhaust by blast 
      then show ?thesis using w_len_not_eq[OF ex] by presburger
    qed  
    then show ?thesis using w2_in_L by presburger
  next
    case c_right      
    let ?ww1 = "?px1 @ ?w1 @ ?py1"
    have "?c ?ww1 c1 = ?c ?px1 c1 + ?c ?w1 c1 + ?c ?py1 c1" by simp
    hence c_c1: "?c ?ww1 c1 = ?c ?w1 c1 + ?w1l * l" using x1_pow_cs(1) y1_pow_cs(2)[OF c_neq] by presburger

    have "?c ?ww1 c2 = ?c ?px1 c2 + ?c ?w1 c2 + ?c ?py1 c2" by simp
    hence c_c2: "?c ?ww1 c2 = ?c ?w1 c2 + ?w1l * l" using x1_pow_cs(2)[OF c_neq[symmetric]] y1_pow_cs(1) by presburger

    have c_c3:  "\<And>c3. c3\<noteq>c1 \<Longrightarrow> c3\<noteq>c2 \<Longrightarrow> ?c ?ww1 c3 = ?c ?w1 c3" by simp
     
    consider "(c1 = A \<and> c2 = D)" | "(c1 = B \<and> c2 = C)" using c_right by auto
    then have "?ww1 \<notin> L_ambig"
    proof cases
      case 1
      then have case_dist: 
      "?c ?ww1 A = n + l * ?w1l \<and> ?c ?ww1 B = n \<and> ?c ?ww1 C = m \<and> ?c ?ww1 D = m + l * ?w1l" 
        using c_c1 c_c2 c_c3 w_obtains(1) t.distinct by (simp add: count_list_pow_list)
      have "?c ?ww1 A \<noteq> ?c ?ww1 B" using case_dist len_too_big1  by linarith
      moreover have "?c ?ww1 A \<noteq> ?c ?ww1 C" using case_dist len_too_big1 by linarith 
      moreover have "?c ?ww1 A \<noteq> ?c ?ww1 D" using case_dist w_obtains(3) by linarith 
      ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?ww1 c \<noteq> count_list ?ww1 c'" 
        using exI[of _ A] t.exhaust by blast 
      then show ?thesis using w_len_not_eq[OF ex] by presburger
    next
      case 2
      then have case_dist: 
      "?c ?ww1 A = n \<and> ?c ?ww1 B = n + l * ?w1l \<and> ?c ?ww1 C = m + l * ?w1l \<and> ?c ?ww1 D = m" 
        using c_c1 c_c2 c_c3 w_obtains(1) t.distinct by (simp add: count_list_pow_list)
      have "?c ?ww1 A \<noteq> ?c ?ww1 B" using case_dist len_too_big1  by linarith
      moreover have "?c ?ww1 A \<noteq> ?c ?ww1 C" using case_dist len_too_big1 by linarith 
      moreover have "?c ?ww1 A \<noteq> ?c ?ww1 D" using case_dist w_obtains(3) by linarith 
      ultimately have ex: "\<exists>c. \<forall>c' \<noteq> c. count_list ?ww1 c \<noteq> count_list ?ww1 c'" 
        using exI[of _ A] t.exhaust by blast 
      then show ?thesis using w_len_not_eq[OF ex] by presburger
    qed  
    then show ?thesis using w1_in_L by presburger
  qed
qed   


subsubsection "2.1) Proving the completeness of our classes"

lemma classes_complete:
  assumes start_prod2: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
          classes: "\<And>X. X \<in> Nts (Prods G') \<Longrightarrow> X \<noteq> (Start G') \<Longrightarrow> X \<in> Cab G' \<or>  X \<in> Cad G' \<or> X \<in> Cbc G' \<or> X \<in> Ccd G'" 
  shows "{(Start G')} \<union> Cab G' \<union> Cad G' \<union> Cbc G' \<union> Ccd G' = Nts (Prods G')"
proof 
  show "{(Start G')} \<union> Cab G' \<union> Cad G' \<union> Cbc G' \<union> Ccd G' \<subseteq> Nts (Prods G')"
  proof
    fix X
    assume "X \<in> {(Start G')} \<union> Cab G' \<union> Cad G' \<union> Cbc G' \<union> Ccd G'"

    then consider (start) "X = (Start G')" | (rest) "X \<in>  Cab G' \<union> Cad G' \<union> Cbc G' \<union> Ccd G'" by auto
    then show "X \<in> Nts (Prods G')" 
    proof cases
      case start
      then show ?thesis unfolding Nts_def using start_prod2 by blast
    next
      case rest
      then have "X \<in> Cab G' \<or>  X \<in> Cad G' \<or> X \<in> Cbc G' \<or> X \<in> Ccd G'" by auto
      then obtain x y l where prod: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y \<and> length x = l \<and> length y = l \<and> l > 0"           
        by (smt (verit, del_insts) length_pow_list_single map_pow_list mem_Collect_eq)
       
      then have not_equal: "[Nt X] \<noteq> map Tm x @ [Nt X] @ map Tm y"
         by (auto simp add: Cons_eq_append_conv)
       hence "\<exists>\<alpha>. (Prods G') \<turnstile> [Nt X] \<Rightarrow> \<alpha>" 
         using prod converse_rtranclpE by fastforce
       hence "\<exists>\<alpha>. (X, \<alpha>) \<in> (Prods G')" by (simp add: derive_singleton) 
       thus ?thesis using Nts_def by fast
    qed
  qed
next
   show "Nts (Prods G') \<subseteq> {(Start G')} \<union> Cab G' \<union> Cad G' \<union> Cbc G' \<union> Ccd G'"
    using classes by auto
qed

subsection "Finiteness lemma"

text "If universe is infinite, and a complement is "
lemma finite_comp:
  fixes A :: "'n set" 
  assumes "finite (-A)" "infinite (UNIV :: 'n set)"
  shows "infinite A"
  using assms(1,2) by auto


end