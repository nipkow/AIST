theory DFA_to_RegExp

imports "DFA_Locale_simple"
begin

(** 
  This theory file contains the proof of the conversion of a (simplified) DFA to a regular expression.
  The proof is based on the book "Introduction to Automata Theory, Languages, and Computation" by John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman.

  The proof is based on the theorem 3.4 in the book.
  https://www-2.dc.uba.ar/staff/becher/Hopcroft-Motwani-Ullman-2001.pdf
**)


(** 
  I was able to prove correctness of the base case of the conversion function R i j 0, 
  and completed half of the induction step R i j (k+1).

  I got stuck in the induction step, because I could not get the claimed decomposition lemma to work.
  But i think there is not much missing to complete the proof.
**)


context dfa begin

section "Defintion of the conversion function R i j k"


(** 
  The function arcs_rexp i j generates a regular expression 
  generating all single letter paths from state i to state j.
**)
definition arcs_rexp :: "nat \<Rightarrow> nat \<Rightarrow> 'a rexp" where
   "arcs_rexp i j = foldr Plus [Atom a . a \<leftarrow> sigma, nxt i a = j] Zero"

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

(**
  The conversion function R i j k should generate a regular expression
  corresponding to the set of words that represent a path from state i to state j, only using states from S up to state k.
**)
fun R :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a rexp " where
  "R i j 0 = (if i \<notin> S \<or> j \<notin> S then Zero else 
               (if i \<noteq> j then arcs_rexp i j else Plus One (arcs_rexp i j)))" |
  "R i j (Suc k) = (if i \<notin> S \<or> j \<notin> S then Zero else 
                   (  let R'= R    i       j    k in
                      let u = R    i    (Suc k) k in
                      let v = R (Suc k) (Suc k) k in
                      let w = R (Suc k)    j    k in
                    Plus  R' (Times u (Times (Star v) w))))"



section "Proofs about the conversion function R i j k"







subsection "Proofs about the base case R i j 0"

lemma lang_base_case:"lang (R i j 0) = (if i\<notin> S \<or> j \<notin> S then {} 
                                   else { [a] | a. a \<in> set sigma \<and>  nxt i a = j}  \<union> (if i = j then {[]} else {}))"
   by (simp add: lang_arcs_rexp)



lemma R_valid_path:"w\<in> lang (R i j k) \<Longrightarrow> i \<in> S \<and> j \<in> S"
  apply(induction i j k rule:R.induct)
  apply (metis empty_iff lang_base_case)
  apply(auto)
  apply (smt (verit, ccfv_threshold) empty_iff lang.simps(1))
  by (smt (verit, best) all_not_in_conv lang.simps(1))


(** 
  First direction:
  If a word w is in the language of R i j 0, then w is a path from i to j and its intermediate path is restricted to 0.
**)
lemma langRij0_1:
  assumes "w \<in> lang (R i j 0)"
  shows "(word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) 0)"
 proof -
   have lang:"lang (R i j 0) =  { [a] | a. a \<in> set sigma \<and>  nxt i a = j}  \<union> (if i = j then {[]} else {})"
     by (metis (no_types, lifting) assms lang_base_case R_valid_path)

   have " i \<in> S "
     using assms R_valid_path by blast

   then have "word_run_from_i_j w i j"
     apply(cases "i = j")
     using lang assms word_run_from_i_j_def by force +

   have "w \<in> { [a] | a. a \<in> set sigma \<and>  nxt i a = j}  \<union> (if i = j then {[]} else {})"
      by (metis (no_types, lifting) lang_base_case R_valid_path assms)

    then  have "path_of_word w i = (if w=[] then [i] else [i,j])"
      by(cases "i=j") auto
 
    then  have "intermediate_path (path_of_word w i) = [] "
     using assms by force

   then have "intermediate_path_restricted (path_of_word w i) 0"
     unfolding intermediate_path_restricted_def
     by simp
  
   then show ?thesis
     by (simp add: \<open>word_run_from_i_j w i j\<close>)
 qed

(** 
  Second direction:
  If a word w is a path from i to j and its intermediate path is restricted to 0, then w is in the language of R i j 0.
**)
lemma langRij0_2:
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
    apply(auto simp add:lang_base_case lang_arcs_rexp)
    using assms word_run_from_i_j_def intermediate_path_restricted_def apply auto
    using word_run_sound apply blast
    by (metis in_mono list.set_intros(1) nxts.simps(1) nxts.simps(2)) +
qed

(** 
  The language of R i j 0 is the set of words that represent a path from i to j, only using states from S up to state 0.
**)
corollary langRij0_correct: "i \<in> S \<Longrightarrow> j \<in> S \<Longrightarrow> w \<in> lang (R i j 0) \<longleftrightarrow>   word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) 0"
  using langRij0_1 langRij0_2 by blast











subsection "Proofs about the induction step R i j (k+1)"

(** 
I cant get the following decomposition lemma to work / be sound. The proof in the book claims that it should work somehow like this. But nitpick, and metis are unhappy with it.
**)

(**
lemma word_decomposition:"(word_run_from_i_j w i j \<Longrightarrow> intermediate_path_restricted (path_of_word w i) k \<Longrightarrow> k>0 \<Longrightarrow>  k \<in> set( (path_of_word w i))) \<Longrightarrow> 
                                                                         (\<exists> w1 wss w3. w = w1 @ (concat ( wss)) @ w3 
                                                                          \<and>                word_run_from_i_j  w1 i k \<and>  k \<notin> set(intermediate_path (path_of_word w1 i))
                                                                          \<and> (\<forall>p \<in> set wss. word_run_from_i_j  p  k k \<and>  k \<notin> set(intermediate_path (path_of_word p  k)))
                                                                          \<and>                word_run_from_i_j  w3 k j \<and>  k \<notin> set(intermediate_path (path_of_word w3 k))
                                                                          )"
 
  sorry
**)
 

lemma Rmono: "lang (R i j k) \<subseteq> lang (R i j (k + 1))"
  apply(induction  i j k rule:R.induct)
   apply(auto)
  done

lemma langRijk: 
  assumes " k\<le>n "
  shows " w \<in> lang (R i j k) \<longleftrightarrow> (word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) k)"
using assms proof(induction k arbitrary: i j w)
  case 0
  then show ?case
    using langRij0_1 langRij0_2 by blast  
   
next
  case (Suc k)

  let ?R'= "R i j k" 
 
  show ?case 
  proof(cases "\<forall> x \<in> set (intermediate_path (path_of_word  w i)) . x < k+1")
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
        let ?u = "R    i    (Suc k) k "
        let ?v = "R (Suc k) (Suc k) k" 
        let ?w = "R (Suc k)    j    k" 

       

         have lang_times:"w \<in> lang (Times (R a b k) (R b c k)) \<Longrightarrow> word_run_from_i_j w a c" for a b c w
          using Suc.IH Suc.prems word_run_trans by fastforce
        
          have word_run_star:"a \<in> S \<Longrightarrow> w \<in> star (lang (R a a k)) \<Longrightarrow>  word_run_from_i_j w a a" for a w
          proof -
            assume "a \<in> S"
            show "w \<in> star (lang (R a a k)) \<Longrightarrow> word_run_from_i_j w a a"
              apply(induction rule:star_induct)
              apply (simp add: \<open>a \<in> S\<close> word_run_from_i_j_def)
              using Suc.IH Suc.prems Suc_leD word_run_trans by blast
          qed
          
          have "w \<in> lang (Plus  ?R' (Times ?u (Times (Star ?v) ?w)))"
           by (metis R.simps(2) R_valid_path \<open>w \<in> lang (R i j (Suc k))\<close>)
          then have "word_run_from_i_j w i j"
            using lang_times word_run_star apply (simp add: False)
            by (smt (verit, best) R_valid_path Suc.IH Suc.prems Suc_leD concE word_run_trans)

 
        then show ?thesis
          by (metis Suc_eq_plus1 intermediate_path_restricted_def less_or_eq_imp_le not_through_k_plus_one)
      qed
    qed

   then show ?thesis
     by (metis Rmono Suc_eq_plus1 \<open>(w \<in> lang (R i j k)) = (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) (Suc k))\<close> subset_iff)  
           
  next
    case False

    (**
    I got stuck here, because I cant get the decomposition lemma to work.
    **)
 
     then show ?thesis
       sorry

   qed
 qed



(** 
  The language of R i j k is the set of words that represent a path from i to j, only using states from S up to state k.
**)
corollary langRijk_correct: "i \<in> S \<Longrightarrow> j \<in> S \<Longrightarrow> w \<in> lang (R i j n) \<longleftrightarrow>   word_run_from_i_j w i j"
  using langRijk restricted_n by auto







section "Proofs about the final conversion function rexp_of"


(** 
  To create the final regular expression, we combine all regular expressions from the start state (1) to all final states (Fin).
**)
definition rexp_of :: "'a rexp" where
"rexp_of = List.foldr Plus 
             [ R 1 f n . f \<leftarrow> sorted_list_of_set Fin]
           Zero"

(** 
  The language of the created regular expression is the set of all accepted words.
**)
theorem rexp_of_correct: "w \<in> lang (rexp_of) \<longleftrightarrow> accepted w"
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
     by (metis in_mono start_exist states_subset langRijk_correct)
   also have "... = {w.  (\<exists>j \<in> Fin.  set w \<subseteq> set sigma \<and> nxts w 1 = j)  }"
     using start_exist word_run_from_i_j_def by auto
   also have "...= {w. accepted w }"
     using accepted_def by auto
  ultimately show ?thesis
    by simp
qed

corollary "{w. accepted w} = lang (rexp_of)"
  using rexp_of_correct by auto

end

end