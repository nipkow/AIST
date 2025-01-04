theory DFA_Locale_simple
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


(* Set of all paths between two states *)
definition paths_between :: "nat \<Rightarrow> nat \<Rightarrow> (nat list) set" where
  "paths_between i j = {path_of_word w i | w. word_run_from_i_j w i j}"



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



(* Lemmas about the language of a Regular Expression *)


lemma lang_combine_plus:"lang (List.foldr Plus xs Zero) = \<Union>{lang x | x. x \<in> set xs}"
  apply(induction xs)
  apply(auto)
  done



end
end