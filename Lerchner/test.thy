theory test
  imports Main HOL.List DFA_to_RegExp
begin

locale dfa =
  fixes n :: nat
  and sigma :: "'a list"
  and nxt :: "nat \<Rightarrow> 'a \<Rightarrow> nat"
  and Fin :: "nat set"
begin
  
fun nxts :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "nxts [] q = q" |
  "nxts (a#w) q = nxts w (nxt q a)"
  
definition accepted :: "'a list \<Rightarrow> bool" where
  "accepted w = (nxts w 0 \<in> Fin)"

fun list_to_rexp :: "'a list \<Rightarrow> 'a rexp" where
  "list_to_rexp [] = Zero" |
  "list_to_rexp [x] = Atom x" |
  "list_to_rexp (x#xs) = Plus (Atom x) (list_to_rexp xs)"

definition arc :: "nat \<Rightarrow> nat \<Rightarrow> 'a rexp" where
  "arc i j = list_to_rexp [a \<leftarrow> sigma. nxt i a = j]"

(* Test instance *)
definition test_sigma :: "string list"
where "test_sigma = [''a'', ''b'']"

fun test_nxt :: "nat \<Rightarrow> string \<Rightarrow> nat" where
  "test_nxt 0 ''a'' = 1" |
  "test_nxt 0 ''b'' = 0" |
  "test_nxt (Suc 0) ''a'' = 1" |
  "test_nxt (Suc 0) ''b'' = 0"

definition test_Fin :: "nat set"
where "test_Fin = {1}"

(* Test cases *)
lemma "arc 0 1 = list_to_rexp [''a'']"
  by (simp add: arc_def test_sigma_def)

lemma "arc 0 0 = list_to_rexp [''b'']"
  by (simp add: arc_def test_sigma_def)

lemma "arc 1 1 = list_to_rexp [''a'']"
  by (simp add: arc_def test_sigma_def)

end

end


lemma start_exist: "1 \<in> S"
   by (metis atLeastAtMost_iff dfa_axioms dfa_def leI less_one not_gr_zero)


fun nxts :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "nxts [] q = q" |
  "nxts (a#w) q = nxts w (nxt q a)"
  
definition accepted :: "'a list \<Rightarrow> bool" where
  "accepted w = (nxts w 1 \<in> Fin)"

definition word_run_from_i_j :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "word_run_from_i_j w i j =  (nxts w i = j)"


corollary accepted_run:"accepted xs = (\<exists>j\<in> Fin. word_run_from_i_j xs 1 j) "
  by (simp add: accepted_def word_run_from_i_j_def)

(* Your work goes here: *)




(** The traversed states of a word w. **)
fun path_of_word :: "'a list \<Rightarrow> nat  \<Rightarrow> nat list" where
  "path_of_word [] i = [i]" |
  "path_of_word (a#w) i = i # path_of_word w (nxt i a) "

lemma path_in_S:"i \<in> S \<Longrightarrow> set (path_of_word w i) \<subseteq> S"
  apply(induction w arbitrary: i)
  apply(auto)
  by (meson in_mono transitions_in_S)



fun intermediate_path:: "nat list \<Rightarrow> nat list" where
  "intermediate_path p = butlast (tl p)"

lemma intermediate_effect:"intermediate_path (a # is @ [e]) = is"
  by simp

definition paths_between :: "nat \<Rightarrow> nat  \<Rightarrow> (nat list) set" where
  "paths_between i j = {path_of_word w i | w . word_run_from_i_j w i j}"

(** The intermediate path consists of all nodes except the first and last nodes. **)
definition intermediate_path_restricted :: "nat list \<Rightarrow> nat  \<Rightarrow> bool" where
  "intermediate_path_restricted p k = (\<forall>s. s \<in> set (intermediate_path p) \<longrightarrow> s \<le> k)"


(** A path is restricted to a node k if no intermediate node in the path is greater than k. **)
definition restricetd_paths_between :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat list) set" where
  "restricetd_paths_between i j k = {p. p \<in> paths_between i j \<and> intermediate_path_restricted p k}"


corollary path_word_restricted_n:"i \<in> S \<Longrightarrow> j \<in> S  \<Longrightarrow>paths_between i j = restricetd_paths_between i j n"
  unfolding restricetd_paths_between_def paths_between_def intermediate_path_restricted_def
  apply(auto)
  by (metis atLeastAtMost_iff in_mono in_set_butlastD list.sel(2) list.set_sel(2) path_in_S state_set_def)


lemma intermediate_smaller: "set (intermediate_path p) \<subseteq> set p"
  apply(auto)
  by (metis in_set_butlastD list.sel(2) list.set_sel(2))

corollary restricted_n:"i\<in> S \<Longrightarrow> intermediate_path_restricted (path_of_word w i) n"
  unfolding intermediate_path_restricted_def
  by (metis atLeastAtMost_iff in_mono intermediate_smaller path_in_S state_set_def)
 

(** somehow this is necessery for automation **)
lemma x:"\<Union>{lang x | x. x \<in> set (map A xs)} = \<Union>{ lang (A x) | x. x \<in> set (xs)} "
  by auto

lemma path_restricted_mono:"intermediate_path_restricted xs k \<Longrightarrow> intermediate_path_restricted xs (k+1)"
  unfolding intermediate_path_restricted_def
  apply(auto)
  done


  
 
(** Util **)

lemma accepted_path_k:"word_run_from_i_j w k j = (last (path_of_word w k) = j)"
  apply(induction w k rule: path_of_word.induct)
  apply(auto simp add:word_run_from_i_j_def)
  using dfa.path_of_word.elims dfa_axioms apply blast
  using dfa.path_of_word.elims dfa_axioms by blast

corollary accepted_path:"accepted w  = (\<exists>j \<in> Fin. word_run_from_i_j w 1 j)"
  unfolding accepted_def word_run_from_i_j_def
  by(auto)




end