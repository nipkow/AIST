(*  Title:      DFA_Locale_simple.thy
    Author:     Manuel Lerchner
*)

theory DFA_locale_simple
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

(* 
  This theory file defines the simplified DFA (Deterministic Finite Automaton) locale.

  I added some extra assumptions, but I think they are all valid for any (non-empty) DFA.
*)

locale dfa =
  fixes 
    n :: nat                              (* Number of states *)
    and S :: "nat set"                    (* Set of states *)
    and sigma :: "'a list"                (* Alphabet *)
    and nxt :: "nat \<Rightarrow> 'a \<Rightarrow> nat"          (* Transition function *)
    and Fin :: "nat set"                  (* Set of accepting states *)

  assumes 
    "n > 0"                                                           (* At least one state *)
    and state_set_def: "S = {1..n}"                                   (* States are numbered 1 to n *)
    and states_subset: "Fin \<subseteq> S"                                      (* All accepting states are valid states *)
    and transitions_in_S: "i \<in> S \<longrightarrow> nxt i a \<in> S"                     (* Transitions stay within valid states *)
    and transitions_valid: "i \<in> S \<Longrightarrow> a \<in> set sigma \<Longrightarrow> nxt i a \<in> S"  (* Transitions are valid *)
begin

section \<open>Basic Definitions and Lemmas\<close>

subsection \<open>DFA Definition\<close>

(* Basic lemma showing that starting state exists in S *)
lemma start_exist: "1 \<in> S"
  by (metis atLeastAtMost_iff dfa_axioms dfa_def leI less_one not_gr_zero)

(* Extended transition function for words *)
fun nxts :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "nxts [] q = q" |
  "nxts (a#w) q = nxts w (nxt q a)"
  
(* Word acceptance predicate *)
definition accepted :: "'a list \<Rightarrow> bool" where
  "accepted w = ((nxts w 1 \<in> Fin) \<and> set w \<subseteq> set sigma)"


lemma nxts_split:"nxts (drop pos w) (nxts (take pos w) i) = nxts w i"
  apply(induction pos arbitrary: w i)
  apply(auto)
  by (smt (verit) Nil_is_append_conv append_self_conv2 append_take_drop_id drop_Suc_Cons list.inject nxts.elims take_Suc_Cons)



subsection \<open>Runs\<close>

(* Predicate for paths between states *)
definition word_run_from_i_j :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "word_run_from_i_j w i j = (i\<in> S \<and> set w \<subseteq> set sigma \<and> nxts w i = j)"


lemma word_run_sound:"word_run_from_i_j w i j \<Longrightarrow> i\<in> S \<and> j \<in> S"
  unfolding word_run_from_i_j_def
  apply(induction w arbitrary:i)
  using transitions_in_S by auto


lemma word_run_trans:"word_run_from_i_j x i k  \<Longrightarrow> word_run_from_i_j y k l \<Longrightarrow> word_run_from_i_j(x@y) i l   "
  unfolding word_run_from_i_j_def
  apply(induction x arbitrary:i)
  apply(auto)
  using transitions_in_S by blast


subsection \<open>Path\<close>

(* Compute sequence of states visited by a word *)
fun path_of_word :: "'a list \<Rightarrow> nat \<Rightarrow> nat list" where
  "path_of_word [] i = [i]" |
  "path_of_word (a#w) i = i # path_of_word w (nxt i a)"



(* Lemma fully describing path_of_word *)
lemma path_of_word_correct:
  "i \<in> S \<Longrightarrow> set (path_of_word w i) \<subseteq> S \<and>  length (path_of_word w i) = length w + 1 \<and> 
            (\<forall>k<length w. path_of_word w i ! k \<in> S \<and>   path_of_word w i ! (k + 1) = nxt (path_of_word w i ! k) (w ! k))"
proof (induction w arbitrary: i)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a w)
  let ?p = "path_of_word w (nxt i a)"
  have IH: "set ?p \<subseteq> S \<and> 
            length ?p = length w + 1 \<and> 
            (\<forall>k<length w. ?p ! k \<in> S \<and> ?p ! (k + 1) = nxt (?p ! k) (w ! k))"
    using Cons.IH Cons.prems transitions_in_S by presburger 

  have  "k<length (a # w) \<Longrightarrow> (i # ?p) ! k \<in> S \<and> (i # ?p) ! (k + 1) = nxt ((i # ?p) ! k) ((a # w) ! k)" for k
    apply(induction k)
    apply(auto)
    apply (simp add: Cons.prems)
    apply (metis nth_Cons_0 path_of_word.elims)
    using transitions_in_S apply blast
    using IH Suc_eq_plus1 by presburger
 
  then show ?case
    apply(auto)
    apply (simp add: Cons.prems)
    using IH apply blast
    using IH by linarith

qed

lemma nxts_last_of_path:"(nxts w i) = last (path_of_word w i)"
  apply(induction w arbitrary:i)
  apply(auto)
  using path_of_word.elims by blast

lemma path_implies_word:"last ((path_of_word w i)) = j \<Longrightarrow> \<exists>w. nxts w i = j"
  apply(induction w arbitrary:i)
  apply(auto)
  using nxts.simps(1) apply blast 
  using nxts.simps(1) apply blast
  by (metis nxts.simps(2))

lemma word_implies_path:"nxts w i = j \<Longrightarrow>\<exists>p. p=(path_of_word w i) \<and> hd p = i \<and> last p = j"
  apply(induction w arbitrary:i)
  apply(auto)
  using dfa.path_of_word.elims dfa_axioms by blast
 

lemma path_decomposition:" (path_of_word (w1 @ w2) i) = (path_of_word w1 i) @ (tl (path_of_word w2 (nxts w1 i)))"
  apply(induction w1 arbitrary: w2 i)
  apply(auto)
  by (metis list.sel(3) path_of_word.elims)

lemma path_decomposition_2:"(path_of_word (w1 @ w2) i) = butlast (path_of_word w1 i) @  (path_of_word w2 (nxts w1 i)) "
  apply(induction w1 arbitrary: w2 i)
  apply(auto)
  using path_of_word.elims by blast




definition path_run_from_i_j :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "path_run_from_i_j p i j = (if p=[] then i=j else hd p = i \<and> last p = j)"


lemma last_of_path:"last (path_of_word w i) = nxts w i "
  apply(induction w arbitrary:i)
  apply(auto)
  using path_of_word.elims by blast

lemma hd_of_path:"hd (path_of_word w i) =  i "
  apply(induction w arbitrary:i)
  by(auto)


lemma word_run_sound_path:"word_run_from_i_j w i j \<Longrightarrow> (set (path_of_word w i) \<subseteq> S)"
  apply(induction w arbitrary:i)
  apply(auto simp add: word_run_sound)
  by (metis nxts.simps(2) order_trans set_subset_Cons subsetD transitions_in_S word_run_from_i_j_def)


lemma length_of_path:"length (path_of_word w i) = length w + 1"
  apply(induction w arbitrary:i)
  apply(auto)
  done

(* All states in a path must be valid states *)
lemma path_in_S: "i \<in> S \<Longrightarrow> set (path_of_word w i) \<subseteq> S"
  apply(induction w arbitrary: i)
  apply(auto)
  by (meson in_mono transitions_in_S)

lemma start_end_in_path:"word_run_from_i_j u x y  \<Longrightarrow> {x,y} \<subseteq> set (path_of_word u x )" for u x y
    unfolding word_run_from_i_j_def
    apply(induction u arbitrary:x y)
    by (auto simp add: transitions_in_S)


lemma word_run_has_path:"word_run_from_i_j w i j = (i\<in> S \<and> set w \<subseteq> set sigma \<and> (let p=  path_of_word w i in hd p = i \<and> last p = j))"
  unfolding word_run_from_i_j_def
  apply(induction w i  rule:nxts.induct)
  apply (simp)
  by (smt (verit) dfa.path_of_word.elims dfa_axioms dual_order.trans last_ConsR list.discI list.inject list.sel(1) nxts.simps(2) set_subset_Cons transitions_in_S)
  

(* Get internal states of a path (excluding start and end) *)
fun intermediate_path :: "nat list \<Rightarrow> nat list" where
  "intermediate_path p = butlast (tl p)"


lemma intermediate_path:"length w > 1 \<Longrightarrow> [i] @ intermediate_path (path_of_word w i) @ [nxts w i] = path_of_word w i"
  apply(induction w arbitrary:i)
  apply(auto)
  by (metis append_butlast_last_id last_of_path list.distinct(1) path_of_word.elims)


(* Set of all paths between two states *)
definition paths_between :: "nat \<Rightarrow> nat \<Rightarrow> (nat list) set" where
  "paths_between i j = {path_of_word w i | w. word_run_from_i_j w i j}"




lemma path_take: "pos < length (path_of_word w i) \<Longrightarrow>(path_of_word w i) ! pos = s  \<longleftrightarrow>  nxts (take pos w) i = s "
  apply(induction pos arbitrary:i w)
  apply(auto)
  apply (metis nth_Cons_0 path_of_word.elims)
  apply (metis nth_Cons_0 path_of_word.elims)
   apply (smt (verit, del_insts) Suc_less_eq drop_Nil id_take_nth_drop length_Cons nth_Cons_Suc nxts.simps(2) path_of_word.elims snoc_eq_iff_butlast take_Suc_Cons)
  by (smt (verit, del_insts) Suc_less_eq drop_Nil id_take_nth_drop length_Cons nth_Cons_Suc nxts.simps(2) path_of_word.elims snoc_eq_iff_butlast take_Suc_Cons)


lemma combine_looped_path:"(\<forall>w\<in> set wss. last (path_of_word w x) = x) \<Longrightarrow>  path_of_word (concat wss) x = x #concat (map (\<lambda> w \<Rightarrow> tl (path_of_word w x)) wss)"
  apply(induction wss)
  apply(auto)
  by (metis append_Cons list.sel(3) path_decomposition path_of_word.simps(1) self_append_conv2 word_implies_path)


lemma word_to_inside__path:"i\<in> S \<Longrightarrow> set w \<subseteq> set sigma\<Longrightarrow> (path_of_word w i) \<noteq>[] \<Longrightarrow> pos < length ( (path_of_word w i)) \<Longrightarrow> (path_of_word w i) ! pos = x \<Longrightarrow>  word_run_from_i_j (take pos w) i x"
proof(induction w arbitrary:i)
  case Nil
  then show ?case
    by (simp add: word_run_from_i_j_def)
next
  case (Cons a w)
  then show ?case 
    unfolding word_run_from_i_j_def
    apply(auto)
    apply (meson Cons.prems(2) in_mono in_set_takeD)
    using Cons.prems(4) Cons.prems(5) path_take by blast
 qed

lemma word_to_inside_intermediate_path:"i\<in> S \<Longrightarrow> set w \<subseteq> set sigma\<Longrightarrow>intermediate_path (path_of_word w i) \<noteq>[] \<Longrightarrow> pos < length (intermediate_path (path_of_word w i)) \<Longrightarrow>intermediate_path (path_of_word w i) ! pos = x \<Longrightarrow>  word_run_from_i_j (take (pos +1) w) i x"
  apply(auto)
  by (smt (verit) Nitpick.size_list_simp(2) One_nat_def Suc_less_eq butlast.simps(1) diff_Suc_eq_diff_pred diff_less length_butlast length_greater_0_conv length_tl less_trans_Suc nth_butlast nth_tl plus_1_eq_Suc word_to_inside__path zero_less_two)


lemma sub_two_no_intermediate_path:"length x \<le> 2 \<Longrightarrow> intermediate_path x = []"
  apply(auto)
  using le_diff_conv by fastforce


lemma last_concat_loops:"\<forall>w' \<in> set wss . last (path_of_word w' (Suc k)) = (Suc k)
 \<Longrightarrow> last (path_of_word (concat wss) (Suc k)) = Suc k"
       apply(induction wss)
       apply(auto)
       by (metis last_append last_tl nxts_last_of_path path_decomposition)


 
subsection \<open>Restricted Paths\<close>


(* Predicate for paths where all nodes are bounded *)
definition path_restricted :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "path_restricted p k = (\<forall>s. s \<in> set ( p) \<longrightarrow> s \<le> k)"

(* Predicate for paths where intermediate nodes are bounded *)
definition intermediate_path_restricted :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "intermediate_path_restricted p k = (\<forall>s. s \<in> set (intermediate_path p) \<longrightarrow> s \<le> k)"

(* Set of paths between states with bounded intermediate nodes *)
definition restricetd_paths_between :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat list) set" where
  "restricetd_paths_between i j k = {p. p \<in> paths_between i j \<and> intermediate_path_restricted p k}"

(* All paths are automatically restricted by n *)
corollary path_word_restricted_n: 
  "i \<in> S \<Longrightarrow> j \<in> S \<Longrightarrow> paths_between i j = restricetd_paths_between i j n"
  unfolding restricetd_paths_between_def paths_between_def intermediate_path_restricted_def
  apply(auto)
  by (metis atLeastAtMost_iff in_mono in_set_butlastD list.sel(2) list.set_sel(2) 
        path_in_S state_set_def)

(* Intermediate states are subset of all states in path *)
lemma intermediate_smaller: "set (intermediate_path p) \<subseteq> set p"
  apply(auto)
  by (metis in_set_butlastD list.sel(2) list.set_sel(2))

(* All paths starting from valid states are restricted by n *)
corollary restricted_n: "i\<in> S \<Longrightarrow> intermediate_path_restricted (path_of_word w i) n"
  unfolding intermediate_path_restricted_def
  by (metis atLeastAtMost_iff in_mono intermediate_smaller path_in_S state_set_def)

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

lemma path_restricted_subword:"path_restricted (a@b@c) k \<Longrightarrow> path_restricted b k"
  unfolding path_restricted_def
  apply(induction a arbitrary: b c)
  by(auto)

lemma intermediate_path_restricted_subword:"intermediate_path_restricted (a@b@c) k \<Longrightarrow> intermediate_path_restricted b k"
  unfolding intermediate_path_restricted_def
  apply(cases "a=[] \<or> c = []")
  apply(auto)
  apply (metis Nil_is_append_conv butlast.simps(1) in_set_butlast_appendI list.distinct(1) list.sel(2) split_list tl_append2)
  apply (metis Nil_tl append_self_conv2 butlast_tl in_set_butlast_appendI list.set_sel(2) tl_append2)
  by (metis Nil_tl butlast_tl in_set_butlast_appendI list.set_sel(2))
 
  
lemma path_restricted_intermediate_path_restricted:"path_restricted (tl a) k \<and> path_restricted (butlast b) k \<Longrightarrow> intermediate_path_restricted (a@b) k"
  unfolding path_restricted_def intermediate_path_restricted_def
proof(induction a arbitrary:b)
  case Nil
  then show ?case
    by (metis append_self_conv2 butlast_tl intermediate_path.elims list.set_sel(2))  
next
  case (Cons a1 a2)

  have "intermediate_path ((a1 # a2) @ b) = butlast (a2 @ b)"
    by simp
  also have "... = (if b = [] then butlast a2 else a2  @ butlast b)  "
    apply(simp)
    by (simp add: butlast_append)
 
  then show ?case 
    apply(cases "b=[]")
    apply(auto)
    apply (metis Cons.prems in_set_butlastD list.sel(3))
    apply (simp add: Cons.prems)
    by (simp add: Cons.prems)
qed

lemma path_restricted_intermediate_path_restricted_2:"a\<noteq>[] \<Longrightarrow> b\<noteq>[] \<Longrightarrow> intermediate_path_restricted (a@b) k  \<Longrightarrow> hd a \<le>k \<Longrightarrow> last b \<le>k\<Longrightarrow> path_restricted (tl a) k \<and> path_restricted (butlast b) k"
  unfolding path_restricted_def intermediate_path_restricted_def
proof(induction a arbitrary:b)
  case Nil
  then show ?case
    by (metis append_self_conv2 butlast_tl intermediate_path.elims list.set_sel(2))  
next
  case (Cons a1 a2)

  have "intermediate_path ((a1 # a2) @ b) = butlast (a2 @ b)"
    by simp
  also have "... = (if b = [] then butlast a2 else a2  @ butlast b)  "
    apply(simp)
    by (simp add: butlast_append)
 
  then show ?case 
    apply(cases "b=[]")
    apply(auto)
    apply (simp add: Cons.prems(2))
    apply (simp add: Cons.prems)
    by (simp add: Cons.prems)
qed

lemma path_restricted_trans: " path_restricted p k \<Longrightarrow>  path_restricted (tl p) k \<and> path_restricted (butlast p) k"
  unfolding path_restricted_def
  apply(induction p)
  by(auto)

lemma path_restricted_append: " path_restricted p k \<Longrightarrow>  path_restricted q k \<Longrightarrow> path_restricted (p @ q) k"
  unfolding path_restricted_def
  apply(induction p)
  by(auto)




lemma path_restricted_combine_intermediate: "k'\<ge>k\<Longrightarrow> p \<noteq> [] \<Longrightarrow>  intermediate_path_restricted p k \<Longrightarrow> last p = k' \<Longrightarrow> 
                               path_restricted q k' \<Longrightarrow>    intermediate_path_restricted (p @ q  ) k'"
proof -
  assume "k \<le> k'"
  assume "p\<noteq>[]"
  assume "intermediate_path_restricted p k"
  assume "last p = k'" 
  assume "path_restricted q k'"

  then obtain ls l where "ls @ [l] = p"
    using \<open>p \<noteq> []\<close> append_butlast_last_id by auto
 
  have "path_restricted (tl ls) k' "
    by (metis \<open>intermediate_path_restricted p k\<close> \<open>k \<le> k'\<close> \<open>ls @ [l] = p\<close> append.right_neutral butlast.simps(2) butlast_append butlast_tl intermediate_path.elims intermediate_path_restricted_def not_Cons_self2 order.trans path_restricted_def)
  then have "path_restricted (tl (ls @ [l])) k' "
    apply(induction ls)
    apply(auto)
    by (metis \<open>last p = k'\<close> \<open>ls @ [l] = p\<close> append_self_conv2 last_snoc order_class.order_eq_iff path_restricted_append path_restricted_def path_restricted_subword set_ConsD)

 then have "path_restricted (tl (ls @ [l]) @ q) k' "
   by (simp add: \<open>path_restricted q k'\<close> path_restricted_append)
    

  then show "intermediate_path_restricted (p @ q  ) k'"
    using \<open>ls @ [l] = p\<close> \<open>path_restricted (tl (ls @ [l])) k'\<close> \<open>path_restricted q k'\<close> path_restricted_intermediate_path_restricted path_restricted_trans by blast
qed

lemma intermediate_to_path_restricted_tl:"intermediate_path_restricted x k \<Longrightarrow> last x = k' \<Longrightarrow> k' \<ge> k \<Longrightarrow> path_restricted (tl x) k'"
  by (smt (verit, ccfv_threshold) Orderings.order_eq_iff butlast.simps(2) dual_order.trans in_set_butlast_appendI intermediate_path.simps intermediate_path_restricted_def last.simps last_appendR last_tl list.distinct(1) list.sel(1) list.set_intros(1) path_restricted_def split_list split_list_first)


lemma intermediate_to_path_restricted_butlast:"intermediate_path_restricted x k \<Longrightarrow> hd x = k' \<Longrightarrow> k' \<ge> k \<Longrightarrow> path_restricted (butlast x) k'"
  by (smt (verit, ccfv_SIG) butlast.simps(1) butlast.simps(2) dual_order.trans intermediate_path.elims intermediate_path_restricted_def list.exhaust_sel nle_le path_restricted_def set_ConsD tl_Nil)

lemma combine_intermediate_restricted:"hd x = k' \<and> intermediate_path_restricted x k \<Longrightarrow> last x = k'' \<Longrightarrow> path_restricted x (max k' (max k k''))"
  apply(induction x)
  unfolding intermediate_path_restricted_def path_restricted_def
  apply fastforce
  by (smt (verit, ccfv_threshold) Orderings.order_eq_iff append_self_conv2 butlast.simps(2) in_set_butlast_appendI intermediate_path.elims last_ConsL last_appendR list.sel(1) list.set_intros(1) max.coboundedI1 max.coboundedI2 split_list_first tl_append2)

(* Lemmas about the language of a Regular Expression *)


lemma lang_combine_plus:"lang (List.foldr Plus xs Zero) = \<Union>{lang x | x. x \<in> set xs}"
  apply(induction xs)
  apply(auto)
  done

lemma star_restricted:"ws \<in> lang (Star X) \<Longrightarrow> (\<forall> w \<in> lang X. path_restricted w k) \<Longrightarrow> path_restricted ws k"
  apply(auto)
  apply(induction rule:star_induct)
   apply(auto)
  unfolding path_restricted_def
  by (auto simp add: path_restricted_def)

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
  apply(induction arbitrary:s  rule:star_induct)
   apply(auto)
  using word_run_from_i_j_def word_run_trans by auto

lemma lang_plus_either: "w \<in>  lang (Plus  A B) \<Longrightarrow> w \<in> lang A \<or> w \<in> lang B"
  by simp
 

end
end