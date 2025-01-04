theory DFA_to_RegExp2

imports "DFA_Locale_simple"
begin


(** See proof of theorem 3.4 in **)
(**https://www-2.dc.uba.ar/staff/becher/Hopcroft-Motwani-Ullman-2001.pdf**)

context dfa begin


lemma lang_combine_plus:"lang (List.foldr Plus xs Zero) = \<Union>{lang x | x. x \<in> set xs}"
  apply(induction xs)
  apply(auto)
  done


definition arcs_rexp :: "nat \<Rightarrow> nat \<Rightarrow> 'a rexp" where
   "arcs_rexp i j = foldr Plus [Atom a . a \<leftarrow> sigma, nxt i a = j] Zero"



(** todo start at -1?**)
fun R :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a rexp " where
  "R i j 0 = (if i \<notin> S \<or> j \<notin> S then Zero else 
               (if i \<noteq> j then arcs_rexp i j else Plus One (arcs_rexp i j)))" |
  "R i j (Suc k) = (if i \<notin> S \<or> j \<notin> S then Zero else 
                   (  let R'= R    i       j    k in
                      let u = R    i    (Suc k) k in
                      let v = R (Suc k) (Suc k) k in
                      let w = R (Suc k)    j    k in
                    Plus  R' (Times u (Times (Star v) w))))"


 


lemma lang_arcs_rexp:" lang (arcs_rexp i j) = { [a] | a. a \<in> set sigma \<and>  nxt i a = j}"
proof -
    have " lang (arcs_rexp i j) = lang (foldr Plus [Atom a . a \<leftarrow> sigma, nxt i a = j] Zero)"
      by (simp add: arcs_rexp_def)
    also have "... = \<Union>{lang x | x. x \<in> set [Atom a . a \<leftarrow> sigma, nxt i a = j]}"
      using lang_combine_plus by blast
    also have "... = \<Union>{lang x | x. x \<in> {Atom a | a. a \<in> set sigma \<and> nxt i a = j}}"
      by auto
    also have "... = \<Union>{ lang (Atom a) | a. a \<in> set sigma \<and> nxt i a = j}"
      by blast
    also have "... =  { [a] | a. a \<in> set sigma \<and> nxt i a = j}"
      by(auto)
    finally show ?thesis 
      by auto
qed


lemma Rmono: "lang (R i j k) \<subseteq> lang (R i j (k + 1))"
  apply(induction  i j k rule:R.induct)
   apply(auto)
  done



lemma lang_Rij0:"lang (R i j 0) = (if i\<notin> S \<or> j \<notin> S then {} 
                                   else { [a] | a. a \<in> set sigma \<and>  nxt i a = j}  \<union> (if i = j then {[]} else {}))"
   by (simp add: lang_arcs_rexp)



lemma R_valid_path:"w\<in> lang (R i j k) \<Longrightarrow> i \<in> S \<and> j \<in> S"
  apply(induction i j k rule:R.induct)
  apply (metis empty_iff lang_Rij0)
  apply(auto)
  apply (smt (verit, ccfv_threshold) empty_iff lang.simps(1))
  by (smt (verit, best) all_not_in_conv lang.simps(1))




lemma path_Rij0:" w\<in> lang (R i j 0) \<Longrightarrow> path_of_word w i = (if w=[] then [i] else [i,j])"
proof -
  assume "w\<in> lang (R i j 0)"
  then have "w \<in> { [a] | a. a \<in> set sigma \<and>  nxt i a = j}  \<union> (if i = j then {[]} else {})"
    by (metis (no_types, lifting) lang_Rij0 R_valid_path)
  then show "path_of_word w i = (if w=[] then [i] else [i,j])"
    apply(cases "i=j")
    by(auto)
qed


lemma no_intermediate_path_k0:"i \<in> S \<Longrightarrow>  p = (path_of_word w i) \<Longrightarrow>  intermediate_path_restricted p 0 \<Longrightarrow> intermediate_path p = [] "
  unfolding  intermediate_path_restricted_def
  apply(induction w arbitrary:i)
  apply(simp)
  by (metis atLeastAtMost_iff intermediate_smaller le_zero_eq list.set_intros(1) neq_Nil_conv path_in_S state_set_def subset_iff zero_neq_one)
 
lemma path_shape_no_intermediate:"intermediate_path (path_of_word w i) = [] \<Longrightarrow> path_of_word w i = (if w=[] then [i] else [i,nxt i (hd w)])"
  unfolding word_run_from_i_j_def
  apply(induction w arbitrary:i)
  apply(auto)
  by (metis butlast.simps(2) butlast_tl list.discI list.sel(2))

lemma langR1j0_1:
  assumes "w \<in> lang (R i j 0)"
  shows "(word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) 0)"
 proof -
   have lang:"lang (R i j 0) =  { [a] | a. a \<in> set sigma \<and>  nxt i a = j}  \<union> (if i = j then {[]} else {})"
     by (metis (no_types, lifting) assms lang_Rij0 R_valid_path)

   have " i \<in> S "
     using assms R_valid_path by blast

   then have "word_run_from_i_j w i j"
     apply(cases "i = j")
     using lang assms word_run_from_i_j_def by force +

   have "intermediate_path (path_of_word w i) = [] "
     using assms path_Rij0 by force

   then have "intermediate_path_restricted (path_of_word w i) 0"
     unfolding intermediate_path_restricted_def
     by simp
  
   then show ?thesis
     by (simp add: \<open>word_run_from_i_j w i j\<close>)
 qed

 
lemma langR1j0_2:
  assumes "word_run_from_i_j w i j" and "intermediate_path_restricted (path_of_word w i) 0"
  shows "w \<in> lang (R i j 0)"
using assms proof -
   have "intermediate_path (path_of_word w i) = []"
     using assms(1) assms(2) no_intermediate_path_k0 word_run_sound by blast
 
  then have "path_of_word w i  =(if w=[] then [i] else [i,nxt i (hd w)])"
    using assms path_shape_no_intermediate by auto

  then have "w = (if w=[] then [] else [hd w])"
    by (metis list.distinct(1) list.inject list.sel(1) path_of_word.elims)

  then consider "w=[]" | "w=[hd w]"
    by meson
  then show "w \<in> lang (R i j 0)"
    apply(cases)
    using assms(1) word_run_from_i_j_def apply fastforce
    apply(auto simp add:lang_Rij0 lang_arcs_rexp)
    using assms word_run_from_i_j_def intermediate_path_restricted_def apply auto
    using word_run_sound apply blast
    by (metis in_mono list.set_intros(1) nxts.simps(1) nxts.simps(2)) +
qed


fun intersperse_alt :: "'b list \<Rightarrow> 'b \<Rightarrow> 'b list" where
 "intersperse_alt xs k = concat (map (\<lambda>x. [x,k]) xs)"


lemma path_decomposition:"(path_run_from_i_j p i j \<and> intermediate_path_restricted p k \<and> k \<in> set(intermediate_path  p)) \<Longrightarrow> 
                                                                         (\<exists> p1 pss p3. p = [i] @  p1 @ [k] @ (concat (intersperse_alt pss[k])) @ p3 @ [j]  
                                                                                      \<and>                 k \<notin> set( p1)
                                                                                      \<and> (\<forall>p \<in> set pss.  k \<notin> set( p ))
                                                                                      \<and>                 k \<notin> set( p3)
                                                                          )"
  unfolding path_run_from_i_j_def intermediate_path_restricted_def
  nitpick
  sorry
 
 
lemma " [i] @  p1 @ [k] @ (concat (intersperse_alt [x,y,z] [k])) @ p3 @ [j] =  
        [i] @  p1 @ [k] @ x @ [k] @  y @ [k] @ z @ [k] @  p3 @ [j]   "
  by auto


lemma word_run_from_i_j_trans:"word_run_from_i_j a i j \<Longrightarrow> word_run_from_i_j b j k \<Longrightarrow> word_run_from_i_j (a@b) i k"
  unfolding word_run_from_i_j_def
  apply(induction a arbitrary:i)
  apply(auto)
  by (simp add: transitions_in_S)

lemma start_end_in_path:"word_run_from_i_j u x y  \<Longrightarrow> {x,y} \<subseteq> set (path_of_word u x )" for u x y
    unfolding word_run_from_i_j_def
    apply(induction u arbitrary:x y)
    by (auto simp add: transitions_in_S)


fun replicate_list :: "'b list \<Rightarrow> nat \<Rightarrow> 'b list"
  where
  "replicate_list lst k = concat (replicate k lst)"



lemma langRijk: 
  assumes " k\<le>n "
  shows " w \<in> lang (R i j k) \<longleftrightarrow> (word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) k)"
using assms proof(induction k arbitrary: i j w)
  case 0
  then show ?case
    using langR1j0_1 langR1j0_2 by blast

next
  case (Suc k)

  let ?p = "path_of_word w i"

  let ?R'= "R    i       j    k" 
  let ?u = "R    i    (Suc k) k "
  let ?v = "R (Suc k) (Suc k) k" 
  let ?w = "R (Suc k)    j    k" 

 
  have w_case:"w \<in> lang (R i j (Suc k)) \<longleftrightarrow> w \<in> lang (Plus  ?R' (Times ?u (Times (Star ?v) ?w)))"
    apply(auto simp add:R_valid_path)
    using R_valid_path by blast

  have lang_times:"w \<in> lang (Times (R a b k) (R b c k)) \<Longrightarrow> word_run_from_i_j w a c" for a b c w
    using Suc.IH Suc.prems word_run_from_i_j_trans by fastforce

  have word_run_star:"a \<in> S \<Longrightarrow> w \<in> star (lang (R a a k)) \<Longrightarrow>  word_run_from_i_j w a a" for a w
  proof -
    assume "a \<in> S"
    show "w \<in> star (lang (R a a k)) \<Longrightarrow> word_run_from_i_j w a a"
      apply(induction rule:star_induct)
      apply (simp add: \<open>a \<in> S\<close> word_run_from_i_j_def)
      using Suc.IH Suc.prems Suc_leD word_run_from_i_j_trans by blast
  qed
  
 
  show ?case 
  proof(cases "\<forall>s. s \<in> set (intermediate_path (path_of_word w i)) \<longrightarrow> s \<le>  k")
    case not_through_k_plus_one:True

    have "w \<in> lang ?R' \<longleftrightarrow> (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))"
    proof(rule iffI)
      assume "w \<in> lang ?R'"
 
      show "(word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))"
        by (meson Suc.IH Suc.prems Suc_leD \<open>w \<in> lang (R i j k)\<close> intermediate_path_restricted_def le_SucI)
    next
      assume "(word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))"

      then have "intermediate_path_restricted (path_of_word w i) k"
        unfolding intermediate_path_restricted_def
        using not_through_k_plus_one le_Suc_eq by fastforce
       
      then  show "w \<in> lang ?R'"
        by (simp add: Suc.IH Suc.prems Suc_leD \<open>word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k)\<close>) 
    qed

    have "(w \<in> lang (R i j (Suc k))) \<Longrightarrow> (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))"
    proof -
      assume "(w \<in> lang (R i j (Suc k)))"
      then show ?thesis
      proof(cases "(w \<in> lang (R i j k))")
        case True
        then show ?thesis
          by (simp add: \<open>(w \<in> lang (R i j k)) = (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))\<close>) 
      next
        case False

        then have "w \<in> lang (Plus  ?R' (Times ?u (Times (Star ?v) ?w)))"
            using \<open>w \<in> lang (R i j (Suc k))\<close> w_case by blast

    
          then have "word_run_from_i_j w i j"
            apply (simp add: False)
            using lang_times word_run_star
            by (smt (verit, best) R_valid_path Suc.IH Suc.prems Suc_leD concE word_run_from_i_j_trans)

 
          then have " intermediate_path_restricted (path_of_word w i) (Suc k)"
            by (simp add: intermediate_path_restricted_def le_SucI not_through_k_plus_one)
  
        then show ?thesis
          by (simp add: \<open>word_run_from_i_j w i j\<close>)
      qed
    qed

   then show ?thesis
     by (metis Rmono Suc_eq_plus1 \<open>(w \<in> lang (R i j k)) = (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))\<close> subset_iff)  
           
  next
    case False

  
 
     then show ?thesis sorry
       

   qed
 qed



corollary langRn: "i \<in> S \<Longrightarrow> j \<in> S \<Longrightarrow> w \<in> lang (R i j n) \<longleftrightarrow>   word_run_from_i_j w i j"
  using langRijk restricted_n by auto


definition rexp_of :: "'a rexp" where
"rexp_of = List.foldr Plus 
             [ R 1 j n . j \<leftarrow> sorted_list_of_set Fin]
           Zero"

theorem "w \<in> lang (rexp_of) \<longleftrightarrow> accepted w"
proof -
  have f:"finite S"
    by (simp add: state_set_def)

  have "lang (rexp_of) = \<Union>{lang x | x. x \<in> set [ R 1 j n . j \<leftarrow> sorted_list_of_set Fin]}"
    by (simp add: lang_combine_plus rexp_of_def)
  also have "... = \<Union>{lang (R 1 j n) | j. j \<in> Fin} "
    using f finite_subset states_subset by fastforce
  also have "... = {w.  (\<exists>j \<in> Fin. w \<in> lang (R 1 j n))  }"
    by blast
   also have "... = {w.  (\<exists>j \<in> Fin. word_run_from_i_j w 1 j)  }"
     by (metis in_mono start_exist states_subset langRn)
   also have "... = {w.  (\<exists>j \<in> Fin.  set w \<subseteq> set sigma \<and> nxts w 1 = j)  }"
     using start_exist word_run_from_i_j_def by auto
   also have "...= {w. accepted w }"
     using accepted_def by auto
  ultimately show ?thesis
    by simp
qed

end



end