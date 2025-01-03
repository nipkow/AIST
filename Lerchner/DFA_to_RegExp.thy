theory DFA_to_RegExp

imports 
"$AFP/Regular-Sets/Regular_Exp"   
begin


(** See proof of theorem 3.4 in **)
(**https://www-2.dc.uba.ar/staff/becher/Hopcroft-Motwani-Ullman-2001.pdf**)

locale dfa =
  fixes n :: nat
  and sigma :: "'a list"
  and nxt :: "nat \<Rightarrow> 'a \<Rightarrow> nat"
  (* initial state is 1 *)
  and Fin :: "nat set"
  assumes all_states_greater_than_0: "(\<forall>s . s \<in> Fin \<longrightarrow> s > 0) \<and> (\<forall>i a . nxt i a  > 0)"
begin

fun nxts :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "nxts [] q = q" |
  "nxts (a#w) q = nxts w (nxt q a)"
  
definition accepted :: "'a list \<Rightarrow> bool" where
  "accepted w = (nxts w 1 \<in> Fin)"
  
(* Your work goes here: *)

type_synonym 'b path = "nat * ('b list) * nat"

definition path_valid :: "'a path \<Rightarrow> bool" where
  "path_valid p \<longleftrightarrow> (let (i,w,j) = p in  (nxts w i = j))"

fun states_visited :: "'a path \<Rightarrow> nat list" where
  "states_visited (i, [], j) = []" | 
  "states_visited (i, a#w, j) = 
     (let next = nxt i a in 
      if next = j then [] 
      else next # states_visited (next, w, j))"

lemma states_visited_gt_0: "x \<in> set (states_visited (i,w,j)) \<Longrightarrow> x >0 "
  apply(induction w arbitrary:i)
  apply(auto)
  by (smt (verit, ccfv_threshold) all_states_greater_than_0 length_pos_if_in_set less_numeral_extra(3) list.size(3) set_ConsD)

lemma states_visited_valid:
  assumes "path_valid (i,w,j)"
  shows " (\<exists>xs ys. nxts xs i = k \<and> xs @ ys = w \<and> xs \<noteq> [] \<and> ys \<noteq> []) \<longleftrightarrow> k \<in> set (states_visited (i,w,j)) "
  sorry

definition path_restricted :: " 'a path \<Rightarrow> nat \<Rightarrow> bool" where
  "path_restricted p k \<longleftrightarrow> (path_valid p \<and> (\<forall>s. s \<in> set (states_visited p) \<longrightarrow> s \<le> k))"




fun path_goes_through_node :: "'a path \<Rightarrow> nat \<Rightarrow> bool" where
  "path_goes_through_node p k = (k \<in> set (states_visited p))"

 
fun rexp_goes_through_node :: "'a rexp \<Rightarrow> nat \<Rightarrow> bool" where
  "rexp_goes_through_node rexp k = (\<exists>w \<in> lang rexp. path_goes_through_node (1, w, nxts w 1) k) "


 (** todo  missing case y**)
lemma split_path_at_node:"p = (i, w, j) \<Longrightarrow> path_valid p \<Longrightarrow>  path_goes_through_node p k \<Longrightarrow> \<exists> x y z . (x @ y @ z = w \<and>
                                                                        \<not> path_goes_through_node (i, x, k) k \<and>
                                                                        \<not> path_goes_through_node (k, u, j) k)"
  sorry


definition arcs_rexp :: "nat \<Rightarrow> nat \<Rightarrow> 'a rexp" where
  "arcs_rexp i j =  List.foldr Plus 
                  (List.map Atom [ a \<leftarrow> sigma. nxt i a = j]) 
              Zero"

lemma lang_foldr:"lang (List.foldr Plus xs Zero) = \<Union>{lang x | x. x \<in> set xs} "
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)

 have "\<Union> {lang x |x. x \<in> set (a # xs)} = \<Union> {lang x |x. x \<in> (set xs \<union>  {a})} "
   by auto
  also have "... = \<Union> {lang x |x. x \<in> (set xs )} \<union> lang a"
    by blast
  then show ?case
    by (simp add: local.Cons sup_commute) 
qed


lemma arcs_lang:"[a] \<in> lang (arcs_rexp i j) \<longleftrightarrow>  nxt i a = j "
  unfolding arcs_rexp_def
  sorry

(** todo start at -1?**)
fun R:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a rexp " where
  "R i j 0 = (if i \<noteq> j then arcs_rexp i j else Plus Zero (arcs_rexp i j))" |
  "R i j (Suc k) = (let R' = R i j k in
                           if \<not>rexp_goes_through_node R' k then 
                              R'
                           else
                              let u = R    i    (Suc k) k in
                              let v = R (Suc k) (Suc k) k in
                              let w = R (Suc k)    j    k in
                              Plus  R' (Times u (Times (Star v) w)))"






lemma " path_restricted (i, w, j) k \<Longrightarrow> w \<in> lang (R i j k)"
proof(induction k arbitrary: i j)
  case 0

  then  show ?case 

  proof(cases "i=j")
    case True
    then show ?thesis 
      unfolding path_restricted_def path_valid_def 
      apply(auto)
      sorry
  next
    case False
    then show ?thesis sorry
  qed
next
  case (Suc k)
  then show ?case sorry
qed


  
definition rexp_of :: "'a rexp" where
"rexp_of = List.foldr Plus 
             [ R 0 j n . j \<leftarrow> sorted_list_of_set Fin]
           Zero"

theorem "w \<in> lang (rexp_of) \<longleftrightarrow> accepted w"
  sorry

end



end