theory DFA_Locale_simple
imports
  "$AFP/Regular-Sets/Regular_Exp"
begin

(* 
  This theory file defines the basic DFA (Deterministic Finite Automaton) structure
  using Isabelle's locale mechanism. The DFA is represented with:
  - n: total number of states
  - S: set of states (numbered 1 to n)
  - sigma: alphabet as a list of symbols
  - nxt: transition function
  - Fin: set of accepting states
*)
locale dfa =
  fixes 
    n :: nat           (* Number of states *)
    and S :: "nat set" (* Set of states *)
    and sigma :: "'a list"  (* Alphabet *)
    and nxt :: "nat \<Rightarrow> 'a \<Rightarrow> nat"  (* Transition function *)
    and Fin :: "nat set"    (* Set of accepting states *)

  assumes 
    "n > 0"  (* At least one state *)
    and state_set_def: "S = {1..n}"  (* States are numbered 1 to n *)
    and states_subset: "Fin \<subseteq> S"     (* All accepting states are valid states *)
    and transitions_in_S: "\<And>i a. i \<in> S \<longrightarrow> nxt i a \<in> S"  (* Transitions stay within valid states *)
    and transitions_valid: "nxt i a = j \<Longrightarrow> a \<in> set sigma"  (* Transitions use valid symbols *)
begin

(* Basic lemma showing that starting state exists in S *)
lemma start_exist: "1 \<in> S"
  by (metis atLeastAtMost_iff dfa_axioms dfa_def leI less_one not_gr_zero)



(* Extended transition function for words *)
fun nxts :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "nxts [] q = q" |
  "nxts (a#w) q = nxts w (nxt q a)"
  
(* Word acceptance predicate *)
definition accepted :: "'a list \<Rightarrow> bool" where
  "accepted w = (nxts w 1 \<in> Fin)"

(* Predicate for paths between states *)
definition word_run_from_i_j :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "word_run_from_i_j w i j = (nxts w i = j)"






(* 
  Path-related operations and lemmas including:
  - path_of_word: Computes the sequence of states visited by a word
  - intermediate_path: Gets internal states of a path
  - paths_between: Set of all paths between two states
*)

(* Compute sequence of states visited by a word *)
fun path_of_word :: "'a list \<Rightarrow> nat \<Rightarrow> nat list" where
  "path_of_word [] i = [i]" |
  "path_of_word (a#w) i = i # path_of_word w (nxt i a)"

definition path_run_from_i_j :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "path_run_from_i_j p i j = (if p=[] then i=j else hd p = i \<and> last p = j)"


lemma length_of_path:"length (path_of_word w i) = length w + 1"
  apply(induction w arbitrary:i)
  apply(auto)
  done

(* All states in a path must be valid states *)
lemma path_in_S: "i \<in> S \<Longrightarrow> set (path_of_word w i) \<subseteq> S"
  apply(induction w arbitrary: i)
  apply(auto)
  by (meson in_mono transitions_in_S)

(* Get internal states of a path (excluding start and end) *)
fun intermediate_path :: "nat list \<Rightarrow> nat list" where
  "intermediate_path p = butlast (tl p)"

(* Simple lemma about intermediate path computation *)
lemma intermediate_effect: "intermediate_path (a # is @ [e]) = is"
  by simp

(* Set of all paths between two states *)
definition paths_between :: "nat \<Rightarrow> nat \<Rightarrow> (nat list) set" where
  "paths_between i j = {path_of_word w i | w. word_run_from_i_j w i j}"


(*
  Operations and lemmas for paths with restrictions on intermediate states:
  - intermediate_path_restricted: Predicate for paths with bounded intermediate states
  - restricetd_paths_between: Set of paths with bounded intermediate states
*)

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


end
end