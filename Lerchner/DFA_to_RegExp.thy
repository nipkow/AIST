(*  Title:      DFA_to_RegExp.thy
    Author:     Manuel Lerchner
*)

theory DFA_to_RegExp

imports "DFA_locale_simple"
begin

(** 
  This theory file contains the proof of the conversion of a (simplified) DFA to a regular expression.
  The proof is based on the book "Introduction to Automata Theory, Languages, and Computation" by John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman.

  The proof is based on the theorem 3.4 in the book.
  https://www-2.dc.uba.ar/staff/becher/Hopcroft-Motwani-Ullman-2001.pdf
**)

(** 
  I was able to prove correctness of the base case of the conversion function R i j 0, 
  and completed most of the induction step R i j (k+1).

  Moreover I was able to prove that the final construction of the regular expression is correct.

  I got stuck at two points:
    1. The decomposition of a word (or path) into three parts w1, ws, w2, as claimed in the book. 
       I think this needs a complicated split function, that detects loops in a path, and splits the word accordingly.
       I already spent to much time here, so I decided to sorry this part.

    2. The proof that the intermediate path of a word w is restricted to k, if w is a path from i to j. 
       (This should be trivial, but I could not get it to work. I proved a weaker version of this lemma, 
        that states that all paths are restricted to max i j k however.)
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


lemma langRij0_words_leq_1: "w \<in> lang (R i j 0) \<Longrightarrow> length w \<le> 1"
  apply(cases "i \<in> S \<and> j \<in> S")
  apply(auto)
  apply(cases "i=j")
  using lang_arcs_rexp by(auto)





subsection "Proofs about the induction step R i j (k+1)"



lemma Rmono: "lang (R i j k) \<subseteq> lang (R i j (k + 1))"
  apply(induction  i j k rule:R.induct)
   apply(auto)
  done

lemma ssdss: "w \<in>  lang (Plus  A B) \<Longrightarrow> w \<in> lang A \<or> w \<in> lang B"
  by simp

lemma lang_times_split:"w \<in> lang (Times a b) \<longleftrightarrow>( \<exists> w1 w2. w1 \<in> lang a \<and> w2 \<in> lang b \<and> w = w1 @ w2)"
  apply(auto)
  by (smt (verit) concE)

lemma lang_star_split: "w \<in> lang (Star A) \<longleftrightarrow> (\<exists> ws . concat ws = w \<and> (\<forall>w' \<in> set ws . w' \<in> lang A)) "
  apply(auto)
  apply (metis in_star_iff_concat subset_iff)
  by (metis concat_in_star subsetI)

lemma star_runs_loop:"w \<in> lang (Star A) \<Longrightarrow> s \<in> S\<Longrightarrow>  (\<forall>w' \<in> lang A . word_run_from_i_j w' s s) \<Longrightarrow> word_run_from_i_j w s s"
  unfolding word_run_from_i_j_def
  apply(simp)
  apply(induction arbitrary:s e  rule:star_induct)
   apply(auto)
  using word_run_from_i_j_def word_run_trans by auto


lemma last_concat_loops:"\<forall>w' \<in> set wss . last (path_of_word w' (Suc k)) = (Suc k)
 \<Longrightarrow> last (path_of_word (concat wss) (Suc k)) = Suc k"
       apply(induction wss)
       apply(auto)
       by (metis last_append last_tl nxts_last_of_path path_decomposition)


lemma R_ijk_path_run:"w \<in> lang (R i j k) \<Longrightarrow> hd (path_of_word w i) = i \<and> last (path_of_word w i) = j"
proof(induction k arbitrary:i j w)
  case 0
  then show ?case 
    by (meson "0" dfa.langRij0_1 dfa.word_run_has_path dfa_axioms)
next
  case (Suc k)
  then show ?case 
  proof(cases "w \<in> lang (R i j k)")
    case True
    then show ?thesis
      by (simp add: Suc.IH) 
  next
    case False

    let ?u = "R i (Suc k) k"
    let ?v = "R (Suc k) (Suc k) k"
    let ?w = "R (Suc k) j k"

    have "w \<in> lang ( (Times ?u (Times (Star ?v) ?w)))"
      by (smt (verit) False R.simps(2) R_valid_path Suc.prems ssdss)

    then obtain w1 ws w2 wss where "w1@ws@w2 = w" "w1 \<in> lang ?u" and "ws \<in> lang (Star ?v)" and "w2 \<in> lang ?w"
                              and "concat wss = ws" and "\<forall>w' \<in> set wss . w' \<in> lang ?v"
      using lang_star_split by fastforce

     have "\<forall>w' \<in> set wss . last (path_of_word w' (Suc k)) = (Suc k)"
      by (simp add: Suc.IH \<open>\<forall>w'\<in>set wss. w' \<in> lang (R (Suc k) (Suc k) k)\<close>)
 
     have "path_of_word w i = (path_of_word w1 i) @ tl (path_of_word ws (Suc k)) @  tl (path_of_word w2 (Suc k)) "
       by (metis Suc.IH \<open>\<forall>w'\<in>set wss. last (path_of_word w' (Suc k)) = Suc k\<close> \<open>concat wss = ws\<close> \<open>w1 @ ws @ w2 = w\<close> \<open>w1 \<in> lang (R i (Suc k) k)\<close> combine_looped_path last_concat_loops list.distinct(1) path_decomposition tl_append2 word_implies_path)
       
     then show ?thesis 
       apply(auto)
       apply (metis hd_of_path)
       by (smt (verit) Nil_is_append_conv Suc.IH \<open>\<forall>w'\<in>set wss. last (path_of_word w' (Suc k)) = Suc k\<close> \<open>concat wss = ws\<close> \<open>w1 \<in> lang (R i (Suc k) k)\<close> \<open>w2 \<in> lang (R (Suc k) j k)\<close> append.right_neutral hd_Cons_tl hd_Nil_eq_last last_appendR last_concat_loops last_snoc last_tl)
   qed
 qed




lemma Rijk_restricted:" w \<in> lang (R i j k) \<Longrightarrow> path_restricted (path_of_word w i) (max (max i j) k)"
  unfolding path_restricted_def intermediate_path_restricted_def
proof(induction k arbitrary:i j w)
  case 0
    then have "w\<in> ( { [a] | a. a \<in> set sigma \<and>  nxt i a = j}  \<union> (if i = j then {[]} else {}))"
      by (metis (no_types, lifting) R_valid_path lang_base_case)
    then show ?case  
      apply(cases "i=j")
      by(auto)
next
  case (Suc k)
  then show ?case 
  proof(cases "w \<in> lang (R i j k)")
    case True
    then show ?thesis
      by (smt (verit) Suc.IH le_SucI le_max_iff_disj) 
  next
    case False

    let ?u = "R i (Suc k) k"
    let ?v = "R (Suc k) (Suc k) k"
    let ?w = "R (Suc k) j k"

    have "w \<in> lang ( (Times ?u (Times (Star ?v) ?w)))"
      by (smt (verit) False R.simps(2) R_valid_path Suc.prems ssdss)

    then obtain w1 ws w2 wss where "w1@ws@w2 = w" "w1 \<in> lang ?u" and "ws \<in> lang (Star ?v)" and "w2 \<in> lang ?w"
                              and ws_def:"concat wss = ws" and "\<forall>w' \<in> set wss . w' \<in> lang ?v"
      using lang_star_split by fastforce

     have "\<forall>w' \<in> set wss . last (path_of_word w' (Suc k)) = (Suc k)"
      using R_ijk_path_run \<open>\<forall>w'\<in>set wss. w' \<in> lang (R (Suc k) (Suc k) k)\<close> by blast
   
     then have path_decomp:"path_of_word w i = (path_of_word w1 i) @ tl (path_of_word ws (Suc k)) @  tl (path_of_word w2 (Suc k)) "
       by (smt (verit, ccfv_SIG) \<open>w1 @ ws @ w2 = w\<close> \<open>w1 \<in> lang (R i (Suc k) k)\<close> append_eq_appendI dfa.R_ijk_path_run dfa.last_of_path dfa.path_decomposition dfa.path_decomposition_2 dfa_axioms last_concat_loops ws_def)
 
     then have "\<forall>w\<in>set wss. path_restricted (path_of_word w (Suc k)) (max (max (Suc k) (Suc k)) k)"
       using Suc.IH \<open>\<forall>w'\<in>set wss. w' \<in> lang (R (Suc k) (Suc k) k)\<close> path_restricted_def by blast
       
    have "(\<forall>w\<in> set wss. last (path_of_word w (Suc k)) = (Suc k))"
      using \<open>\<forall>w'\<in>set wss. w' \<in> lang (R (Suc k) (Suc k) k)\<close> dfa.R_ijk_path_run dfa_axioms by blast
    then have "path_of_word (concat wss) (Suc k) = (Suc k) #concat (map (\<lambda> w \<Rightarrow> tl (path_of_word w (Suc k))) wss)"
      by (simp add: combine_looped_path)

    then have " path_restricted (path_of_word ws (Suc k)) (max (max (Suc k) (Suc k)) k) "
      using ws_def unfolding path_restricted_def
      apply(auto)
      by (metis Suc.IH Suc_n_not_le_n \<open>\<forall>w'\<in>set wss. w' \<in> lang (R (Suc k) (Suc k) k)\<close> list.sel(2) list.set_sel(2) max_def)
 
    moreover have "path_restricted (path_of_word w1 i) (max k (max i (Suc k)))"
      by (metis Suc.IH \<open>w1 \<in> lang (R i (Suc k) k)\<close>  max.commute path_restricted_def)
 
    moreover have " path_restricted (path_of_word w2 (Suc k)) (max k (max (Suc k) j))"
      by (metis Suc.IH \<open>w2 \<in> lang (R (Suc k) j k)\<close>  max.commute path_restricted_def)



     ultimately show ?thesis
       using path_decomp unfolding path_restricted_def intermediate_path_restricted_def
       apply(cases "i=j")
       apply(auto)
       apply (metis \<open>path_of_word (concat wss) (Suc k) = Suc k # concat (map (\<lambda>x. tl (path_of_word x (Suc k))) wss)\<close> list.discI list.set_sel(2) max.coboundedI2 ws_def)
       apply (metis list.sel(2) list.set_sel(2) max.commute)
       apply (metis \<open>path_of_word (concat wss) (Suc k) = Suc k # concat (map (\<lambda>x. tl (path_of_word x (Suc k))) wss)\<close> list.distinct(1) list.set_sel(2) max.coboundedI2 ws_def)
       by (metis list.sel(2) list.set_sel(2) max.coboundedI2 max.commute max_def)
  qed
qed


 

lemma langRijk_left_to_right: 
  shows " w \<in> lang (R i j k) \<Longrightarrow> (word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) k)"
proof(induction k arbitrary: i j w)
  case 0
  then show ?case
    by (simp add: langRij0_1) 
next
  case (Suc k)
  then show ?case 
  proof(cases "w \<in> lang (R i j k) ")
    case True
    then show ?thesis
      by (metis Suc.IH intermediate_path_restricted_def le_SucI) 
  next
    case False

    let ?u = "R i (Suc k) k"
    let ?v = "R (Suc k) (Suc k) k"
    let ?w = "R (Suc k) j k"

    have "w \<in> lang ( (Times ?u (Times (Star ?v) ?w)))"
      by (smt (verit) False R.simps(2) R_valid_path Suc.prems ssdss)

    then obtain w1 ws w2 wss where "w1@ws@w2 = w" "w1 \<in> lang ?u" and "ws \<in> lang (Star ?v)" and "w2 \<in> lang ?w"
                              and ws_def:"concat wss = ws" and "\<forall>w' \<in> set wss . w' \<in> lang ?v"
      using lang_star_split by fastforce

    then have "word_run_from_i_j w i j"
      unfolding word_run_from_i_j_def
      apply(auto)
      using R_valid_path apply blast
      using Suc.IH dfa.word_run_from_i_j_def dfa_axioms apply blast
      apply (meson Suc.IH subset_code(1) word_run_from_i_j_def)
      apply (meson Suc.IH dfa.word_run_from_i_j_def dfa_axioms subsetD)
      using R_ijk_path_run Suc.prems nxts_last_of_path by blast

    (** this should be trivial, but I still got stuck here **)

    then have " intermediate_path_restricted (path_of_word w i) (Suc k)"
      sorry

    then show ?thesis
      by (simp add: \<open>word_run_from_i_j w i j\<close>)  
  qed
qed




subsection "Split function for words"

(** 
  I got stuck here, and decided to quit ^^
**)


lemma first_occurrence:"s \<in> set (xs) \<Longrightarrow> \<exists> pos. xs ! pos = s \<and> pos < length xs \<and> (\<forall>p<pos . xs!p \<noteq> s) "
proof(induction xs)
  case Nil
  then show ?case
    by simp 
next
  case (Cons a xs)
  then show ?case 
  proof(cases "a=s")
    case True
    then show ?thesis
      by force 
  next
    case False
  then obtain pos where pos: "xs ! pos = s" "pos < length xs" "\<forall>p<pos. xs!p \<noteq> s"
      using Cons.IH Cons.prems by (auto simp: in_set_conv_nth)
    let ?newpos = "pos + 1"
    have "(a#xs) ! ?newpos = s"
      using pos(1) by simp
    moreover have "?newpos < length (a#xs)"
      using pos(2) by simp
    moreover have "\<forall>p<?newpos. (a#xs)!p \<noteq> s"
      using pos(3) False by (auto simp: nth_Cons')
    ultimately show ?thesis
      by blast
  qed
qed


lemma last_occurrence: "s \<in> set xs \<Longrightarrow> \<exists>pos. xs ! pos = s \<and> pos < length xs \<and> (\<forall>p>pos. p < length xs \<longrightarrow> xs ! p \<noteq> s)"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc x xs)
  show ?case
  proof (cases "x = s")
    case True
    then have "(xs @ [x]) ! length xs = s"
      by simp
    moreover have "length xs < length (xs @ [x])"
      by simp
    moreover have "\<forall>p>length xs. p < length (xs @ [x]) \<longrightarrow> (xs @ [x]) ! p \<noteq> s"
      by simp
    ultimately show ?thesis
      by blast
  next
    case False
    then obtain pos where pos: "xs ! pos = s" "pos < length xs" "\<forall>p>pos. p < length xs \<longrightarrow> xs ! p \<noteq> s"
      using snoc.IH snoc.prems by (auto simp: in_set_conv_nth)
    then have "(xs @ [x]) ! pos = s"
      by (simp add: nth_append)
    moreover have "pos < length (xs @ [x])"
      using pos(2) by simp
    moreover have "\<forall>p>pos. p < length (xs @ [x]) \<longrightarrow> (xs @ [x]) ! p \<noteq> s"
      by (metis False butlast_snoc diff_Suc_1 le_less_Suc_eq length_butlast less_iff_Suc_add linorder_le_less_linear nth_append nth_append_length pos(3))
    ultimately show ?thesis
      by blast
  qed
qed


(**
  The following lemma should decompose a word w into three parts w1, ws, w2, as claimed in the book.
  But I could not get it to work.
**)

lemma split:
  assumes "word_run_from_i_j w i j"
    assumes "k + 1 \<in> set (intermediate_path (path_of_word w i))"
    assumes "intermediate_path_restricted (path_of_word w i) (k+1)"
  shows "\<exists>w1 ws w2. w = w1 @ concat ws @ w2 \<and>
     word_run_from_i_j w1 i (k+1) \<and> intermediate_path_restricted (path_of_word w1 i) k \<and>
     (\<forall>w' \<in> set ws. word_run_from_i_j w' (k+1) (k+1) \<and> intermediate_path_restricted (path_of_word w' (k+1)) k) \<and>
     word_run_from_i_j w2 (k+1) j \<and> intermediate_path_restricted (path_of_word w2 (k+1)) k"
using assms proof (induction "count_list (intermediate_path (path_of_word w i)) (k+1)")
  case 0
  then show ?case
    by (simp add: count_list_0_iff)
next
  case (Suc x)
  let ?ps = " intermediate_path (path_of_word w i)"

    have "k + 1 \<in> set (?ps)"
    using Suc.prems(2) intermediate_smaller by auto

  then obtain pos1 pos2 where "?ps ! pos1 = (k+1)" and "pos1 < length ?ps" and "(\<forall>p<pos1 . ?ps!p \<noteq> (k+1))"
    and "?ps ! pos2 = (k+1) \<and> pos2 < length ?ps \<and> (\<forall>p>pos2. p < length ?ps \<longrightarrow> ?ps ! p \<noteq> (k+1))"
    and "pos2 \<ge> pos1"
    by (smt (verit, best) first_occurrence last_occurrence leI)

  have "i # intermediate_path (path_of_word w i) @ [j] = path_of_word w i"
    apply(auto)
    by (metis Suc.prems(2) append_butlast_last_id assms(1) butlast.simps(1) dfa.word_implies_path dfa_axioms intermediate_path.simps last_tl list.collapse list.discI list.set_cases tl_Nil word_run_from_i_j_def)

  let ?w1 = "take (pos1 + 1) w"
  let ?ws = "take (pos2 - pos1  + 1 ) (drop (pos1 + 1) w)"
  let ?w2 = "drop (pos2 + 2) w"

 obtain substrings where
      sub:"(\<forall>substring \<in> set substrings. word_run_from_i_j substring (k+1) (k+1) \<and> 
                         intermediate_path_restricted (path_of_word substring (k+1)) k)" and
       "concat substrings = ?ws"
   sorry

  let ?wss = substrings

  have "?w1 @  concat (?wss) @ ?w2 = w"
    apply(auto)
   by (metis \<open>concat substrings = take (pos2 - pos1 + 1) (drop (pos1 + 1) w)\<close> \<open>pos1 \<le> pos2\<close> add.commute add_Suc_right append.assoc append_take_drop_id le_add_diff_inverse2 plus_1_eq_Suc take_add)


  moreover have " word_run_from_i_j ?w1 i (k+1) "
    by (metis Suc.prems(1) Suc.prems(2) \<open>intermediate_path (path_of_word w i) ! pos1 = k + 1\<close> \<open>pos1 < length (intermediate_path (path_of_word w i))\<close> length_greater_0_conv length_pos_if_in_set word_run_from_i_j_def word_to_inside_intermediate_path)

  moreover have " word_run_from_i_j ?ws (k+1) (k+1) "
    sorry

  moreover have " word_run_from_i_j ?w2 (k+1) j "
    sorry

  moreover have "intermediate_path_restricted (path_of_word ?w1 i) k"
    unfolding intermediate_path_restricted_def
    sorry

  moreover have "intermediate_path_restricted (path_of_word ?w2 (Suc k)) k"
    sorry

  moreover have "word_run_from_i_j (concat ?wss ) (Suc k) (Suc k)"
    unfolding word_run_from_i_j_def
    using sub   apply(auto)
    apply (metis \<open>word_run_from_i_j (take (pos1 + 1) w) i (k + 1)\<close> add.commute dfa.word_run_sound dfa_axioms plus_1_eq_Suc)
    apply (simp add: subset_iff word_run_from_i_j_def)
    by (simp add: last_concat_loops nxts_last_of_path word_run_from_i_j_def)

 
  ultimately show ?case
    apply(auto)
    by (metis Suc_eq_plus1 sub)
qed




lemma langRijk_right_to_left: 
  shows "(word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) k) \<Longrightarrow>  w \<in> lang (R i j k) "
proof(induction k arbitrary: i j w)
  case 0
  then show ?case
    using langRij0_2 by auto
next
  case (Suc k)
  then show ?case 
  proof(cases "k+1 \<notin> set (intermediate_path (path_of_word  w i))  ")
    case True
    then show ?thesis
      apply(auto)
      using Suc.prems word_run_sound apply blast
      using Suc.prems word_run_sound apply auto[1]
      by (metis Suc.IH Suc.prems intermediate_path.elims intermediate_path_restricted_def le_SucE)
  next
    case False

    then have "\<forall>p \<in> set (intermediate_path (path_of_word  w i)). p \<le> k+1 "
      by (metis Suc.prems Suc_eq_plus1 intermediate_path_restricted_def)
   
    have "w \<in> lang (R i j k) \<longleftrightarrow> (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) k)"  for i j w
     using Suc.IH dfa.langRijk_left_to_right dfa_axioms by blast

   have "  word_run_from_i_j w i j"
     by (simp add: Suc.prems)

   moreover have "k + 1 \<in> set (intermediate_path (path_of_word w i))"
     using False by blast
     have "k + 1 \<in> S"
       by (meson False \<open>word_run_from_i_j w i j\<close> in_mono intermediate_smaller path_in_S word_run_sound)

    moreover have "intermediate_path_restricted (path_of_word w i) (k+1)"
      using \<open>\<forall>p\<in>set (intermediate_path (path_of_word w i)). p \<le> k + 1\<close> intermediate_path_restricted_def by blast
   
    ultimately obtain w1 ws w2 where "w = w1 @ concat ws @ w2 \<and>
     word_run_from_i_j w1 i (k+1) \<and> intermediate_path_restricted (path_of_word w1 i) k \<and>
     (\<forall>w' \<in> set ws. word_run_from_i_j w' (k+1) (k+1) \<and> intermediate_path_restricted (path_of_word w' (k+1)) k) \<and>
     word_run_from_i_j w2 (k+1) j \<and> intermediate_path_restricted (path_of_word w2 (k+1)) k"
      using split  apply(auto)
      by (metis Suc_eq_plus1 \<open>k + 1 \<in> set (intermediate_path (path_of_word w i))\<close> intermediate_path.elims)


   have "w1 \<in> lang (R i (k+1) k)"
     using \<open>\<And>w j i. (w \<in> lang (R i j k)) = (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) k)\<close> \<open>w = w1 @ concat ws @ w2 \<and> word_run_from_i_j w1 i (k + 1) \<and> intermediate_path_restricted (path_of_word w1 i) k \<and> (\<forall>w'\<in>set ws. word_run_from_i_j w' (k + 1) (k + 1) \<and> intermediate_path_restricted (path_of_word w' (k + 1)) k) \<and> word_run_from_i_j w2 (k + 1) j \<and> intermediate_path_restricted (path_of_word w2 (k + 1)) k\<close> by auto
   
   have "concat ws \<in> lang (Star (R (k+1) (k+1) k))"
     using \<open>\<And>w j i. (w \<in> lang (R i j k)) = (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) k)\<close> \<open>w = w1 @ concat ws @ w2 \<and> word_run_from_i_j w1 i (k + 1) \<and> intermediate_path_restricted (path_of_word w1 i) k \<and> (\<forall>w'\<in>set ws. word_run_from_i_j w' (k + 1) (k + 1) \<and> intermediate_path_restricted (path_of_word w' (k + 1)) k) \<and> word_run_from_i_j w2 (k + 1) j \<and> intermediate_path_restricted (path_of_word w2 (k + 1)) k\<close> lang_star_split by blast
  
   have "w2 \<in> lang (R (k+1) j k)"
     using \<open>\<And>w j i. (w \<in> lang (R i j k)) = (word_run_from_i_j w i j \<and> intermediate_path_restricted (path_of_word w i) k)\<close> \<open>w = w1 @ concat ws @ w2 \<and> word_run_from_i_j w1 i (k + 1) \<and> intermediate_path_restricted (path_of_word w1 i) k \<and> (\<forall>w'\<in>set ws. word_run_from_i_j w' (k + 1) (k + 1) \<and> intermediate_path_restricted (path_of_word w' (k + 1)) k) \<and> word_run_from_i_j w2 (k + 1) j \<and> intermediate_path_restricted (path_of_word w2 (k + 1)) k\<close> by auto

   then show ?thesis
     apply(simp)
     by (metis Nat.add_diff_assoc \<open>concat ws \<in> lang (Star (R (k + 1) (k + 1) k))\<close> \<open>w = w1 @ concat ws @ w2 \<and> word_run_from_i_j w1 i (k + 1) \<and> intermediate_path_restricted (path_of_word w1 i) k \<and> (\<forall>w'\<in>set ws. word_run_from_i_j w' (k + 1) (k + 1) \<and> intermediate_path_restricted (path_of_word w' (k + 1)) k) \<and> word_run_from_i_j w2 (k + 1) j \<and> intermediate_path_restricted (path_of_word w2 (k + 1)) k\<close> \<open>w1 \<in> lang (R i (k + 1) k)\<close> concI dfa.word_run_sound dfa_axioms diff_add_inverse2 group_cancel.add2 lang.simps(6) le_numeral_extra(4) plus_1_eq_Suc)
   qed
qed
 

corollary langRijk: 
  shows " w \<in> lang (R i j k) \<longleftrightarrow> (word_run_from_i_j w i j \<and>  intermediate_path_restricted (path_of_word w i) k)"
  using dfa.langRijk_left_to_right dfa.langRijk_right_to_left dfa_axioms by blast



(** 
  The language of R i j k is the set of words that represent a path from i to j, only using states from S up to state k.
**)
corollary langRijk_correct: "i \<in> S \<Longrightarrow> j \<in> S \<Longrightarrow> w \<in> lang (R i j n) \<longleftrightarrow>  word_run_from_i_j w i j"
  by (simp add: langRijk restricted_n)





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