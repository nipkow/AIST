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
fun R:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a rexp " where
  "R i j 0 = (if i \<noteq> j then arcs_rexp i j else Plus One (arcs_rexp i j))" |
  "R i j (Suc k) = (  let R'= R    i       j    k in
                      let u = R    i    (Suc k) k in
                      let v = R (Suc k) (Suc k) k in
                      let w = R (Suc k)    j    k in
                    Plus  R' (Times u (Times (Star v) w)))"




lemma lang_arcs_rexp:" lang (arcs_rexp i j) = { [a] | a.  nxt i a = j}"
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
    also have "... =  { [a] | a.  nxt i a = j}"
      by (simp add: transitions_valid)
    finally show ?thesis 
      by auto
  qed

lemma Rmono: "lang (R i j k) \<subseteq> lang (R i j (k + 1))"
  by(auto)

lemma lang_Rij0:" lang (R i j 0) = { [a] | a.  nxt i a = j}  \<union> (if i = j then {[]} else {})"
   by (simp add: lang_arcs_rexp)


lemma path_Rij0:" w\<in> lang (R i j 0) \<Longrightarrow> path_of_word w i = (if w=[] then [i] else [i,j])"
proof -
  assume "w\<in> lang (R i j 0)"
  then have "w \<in> { [a] | a.  nxt i a = j}  \<union> (if i = j then {[]} else {})"
    using lang_Rij0 by fastforce
  then show "path_of_word w i = (if w=[] then [i] else [i,j])"
    apply(cases "i=j")
    by(auto)
qed


lemma no_intermediate_path_k0:"i \<in> S\<Longrightarrow> p = (path_of_word w i) \<Longrightarrow>  intermediate_path_restricted p 0 \<Longrightarrow> intermediate_path p = [] "
  unfolding  intermediate_path_restricted_def
  by (metis atLeastAtMost_iff dual_order.trans intermediate_smaller list.exhaust list.set_intros(1) not_one_le_zero path_in_S state_set_def subset_iff)

lemma path_shape_no_intermediate:"i \<in> S \<Longrightarrow> intermediate_path (path_of_word w i) = [] \<Longrightarrow> path_of_word w i = (if w=[] then [i] else [i,nxt i (hd w)])"
  unfolding word_run_from_i_j_def
  apply(induction w arbitrary:i)
  apply(auto)
  by (metis butlast.simps(2) butlast_tl list.discI list.sel(2) transitions_in_S)

lemma langR1j0_1:
  assumes "w \<in> lang (R i j 0)"
  shows "(word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) 0)"
  using assms unfolding word_run_from_i_j_def intermediate_path_restricted_def 
  apply(cases "i=j")
  by(auto simp add:lang_arcs_rexp)

lemma langR1j0_2:
  assumes "i \<in> S"
  and "word_run_from_i_j w i j" and "intermediate_path_restricted (path_of_word w i) 0"
  shows "w \<in> lang (R i j 0)"
using assms proof -
   have "intermediate_path (path_of_word w i) = []"
    using assms no_intermediate_path_k0 by auto

  then have "path_of_word w i  =(if w=[] then [i] else [i,nxt i (hd w)])"
    using assms path_shape_no_intermediate by auto

  then have "w = (if w=[] then [] else [hd w])"
    by (metis list.distinct(1) list.inject list.sel(1) path_of_word.elims)

  then consider "w=[]" | "w=[hd w]"
    by meson
  then show "w \<in> lang (R i j 0)"
    apply(cases)
    apply(auto simp add:lang_Rij0 lang_arcs_rexp)
    using assms word_run_from_i_j_def apply auto
    by (metis nxts.simps(1) nxts.simps(2) ) +
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
  sorry
 
 
lemma " [i] @  p1 @ [k] @ (concat (intersperse_alt [x,y,z] [k])) @ p3 @ [j] =  
        [i] @  p1 @ [k] @ x @ [k] @  y @ [k] @ z @ [k] @  p3 @ [j]   "
  by auto




lemma word_run_from_i_j_trans:"i \<in> S  \<Longrightarrow> j \<in> S \<Longrightarrow>word_run_from_i_j a i j \<Longrightarrow> word_run_from_i_j b j k \<Longrightarrow> word_run_from_i_j (a@b) i k"
  unfolding word_run_from_i_j_def
  apply(induction a arbitrary:i)
  apply(auto)
  by (simp add: transitions_in_S)

lemma start_end_in_path:"word_run_from_i_j u x y  \<Longrightarrow> {x,y} \<subseteq> set (path_of_word u x )" for u x y
    unfolding word_run_from_i_j_def
    apply(induction u arbitrary:x y)
    by(auto)
 


lemma langRijk: 
  assumes "i \<in> S  \<and> j \<in> S "
  shows " w \<in> lang (R i j k) =(word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) k)"
using assms proof(induction k arbitrary: i j)
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




 

  show ?case 
  proof(cases "(k+1) \<notin> set (intermediate_path ?p)")
    case True

    have "w \<in> lang ?R' \<Longrightarrow> (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))"
    proof -
      assume "w \<in> lang ?R'"

      then have "w \<in>  lang (Plus ?R' (Times ?u (Times (Star ?v) ?w)))"
        by(auto)

     then have "w \<in>  lang (Plus ?R' (Times ?u (Times (Star ?v) ?w)))"
        by(auto)

      show "(word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))"
        sorry
    qed



    then show ?thesis
      sorry
   
  next
    case False

    let ?u = "R    i    (Suc k) k"
    let ?v = "R (Suc k) (Suc k) k" 
    let ?w = "R (Suc k)    j    k"

    have "lang (R i j (Suc k)) =  lang (Plus  ?R' (Times ?u (Times (Star ?v) ?w)))"
      by (simp add: False)

    let ?p = "path_of_word w i"
    have " k \<in> set(?p)" 
  

    obtain p1 p2 p3 where "?p = p1 @ p1 @ p3" 
                            and "path_run_from_i_j p1 i k" and "k \<notin> set(intermediate_path p1)"
                            and "path_run_from_i_j p2 k k" and "k \<notin> set(intermediate_path p1)"
                            and "path_run_from_i_j p3 k j" and " k \<notin> set(intermediate_path p3)"

  
      have "k \<in> set(p)"

  have "word_run_from_i_j w (Suc k) k"

     then show ?thesis 
       sorry
  
  qed


qed


lemma langRijk: 
  assumes "i \<in> S  \<and> j \<in> S "
  shows"  w \<in> lang (R i j k) =  (word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) k)"
using assms proof(induction k arbitrary: i)
  case 0
  then show ?case
    using langR1j0_1 langR1j0_2 by blast

next
  case (Suc k)

  show ?case 
  proof(rule iffI)
    assume " w \<in> lang (R i j (Suc k))"

    show "word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k)"  
      sorry

  next
    assume "word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k)"  
    

  show "    w \<in> lang (R i j (Suc k))"
    sorry

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
  also have "...= {w. accepted w }"
    using accepted_def word_run_from_i_j_def by auto
  ultimately show ?thesis
    by simp
qed

end



end