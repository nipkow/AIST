(* Author: Bruno Philipp (and Tobias Nipkow) *)

theory Lsharp
  imports MealyMachine
begin

text \<open>This theory proves the correctness and running time of a modified version of the $L^#$ algorithm
proposed by Frits Vandraager et al. The algorithm is modeled as a transition system.\<close>


datatype ('in,'out) otree = Node "'in \<Rightarrow> (('in,'out) otree \<times> 'out) option"

fun run :: "('in,'out) otree \<Rightarrow> 'in list \<Rightarrow> (('in,'out) otree \<times> 'out list) option" where
"run ot [] = Some (ot, [])" |
"run (Node ft) (i # is) = (case ft i of
    Some (ot,o) \<Rightarrow> (case run ot is of
      Some (ot,os) \<Rightarrow> Some (ot,o # os) |
      None \<Rightarrow> None) |
    None \<Rightarrow> None)"
(* TODO: run ot is = (apply ot is, orun ot is) ? ? *)
fun orun :: "('in,'out) otree \<Rightarrow> 'in list \<Rightarrow> 'out list option" where
"orun ot [] = Some []" |
"orun (Node ft) (i # is) = (case ft i of
    Some (ot,o) \<Rightarrow>
    (case (orun ot is) of
      Some os \<Rightarrow> Some (o # os) |
      None \<Rightarrow> None) |
    None \<Rightarrow> None)"

definition func_sim :: "('s,'in,'out) mealy \<Rightarrow> ('in,'out) otree \<Rightarrow> ('in list \<Rightarrow> 's) \<Rightarrow> bool" where
"func_sim m T f = (case m of
    (q_0,t) \<Rightarrow> ((f [] = q_0) \<and> (\<forall> acc is ops. orun T (acc @ is) = Some ops \<longrightarrow>
      run_trans t (f acc) is = (f (acc @ is),(drop (length acc) ops)))))"

fun apart :: "('in,'out) otree \<Rightarrow> 'in list \<Rightarrow> 'in list \<Rightarrow> bool" where
"apart ot is1 is2 = (\<exists> is os1 os2. orun ot (is1 @ is) = Some os1 \<and>
    orun ot (is2 @ is) = Some os2 \<and>
    drop (length is1) os1 \<noteq> drop (length is2) os2)"

fun isolated :: "('in ,'out) otree \<Rightarrow> 'in list set \<Rightarrow> 'in list \<Rightarrow> bool" where
"isolated q_0 S f = (\<forall> s \<in> S. apart q_0 s f)"

fun apart_witness :: "('in,'out) otree \<Rightarrow> 'in list \<Rightarrow> 'in list \<Rightarrow> 'in  list \<Rightarrow> bool" where
"apart_witness q_0 t1 t2 is = (\<exists> x y. orun q_0 (t1 @ is) = Some x \<and>
    orun q_0 (t2 @ is) = Some y \<and>
    drop (length t1) x \<noteq> drop (length t2) y)"

fun output_query :: "('s,'in ,'out) mealy \<Rightarrow> 'in list \<Rightarrow> 'out list" where
"output_query (q_0,t) is = orun_trans t q_0 is"

fun process_output_query :: "('in,'out) otree \<Rightarrow> 'in  list \<Rightarrow> 'out list \<Rightarrow> ('in,'out) otree" where
"process_output_query ot [] [] = ot" |
"process_output_query (Node ft) (i # is) (o # os) = (case ft i of
    None \<Rightarrow> (Node (\<lambda> j. if j = i
      then Some (process_output_query (Node (\<lambda> k. None)) is os,o)
      else ft j)) |
    Some (ot,o) \<Rightarrow> (Node (\<lambda> j. if j = i
      then Some ((process_output_query ot is os),o)
      else ft j)))"

text \<open>@{const process_output_query} adds new knowledge about the original mealy machine to the Tree\<close>

type_synonym ('in,'out) state = "'in list set \<times> 'in list set \<times> ('in,'out) otree"

type_synonym ('in,'out) state_list = "'in list list \<times> 'in list list \<times> ('in,'out) otree"

fun sapart :: "('in ,'out) state \<Rightarrow> bool" where
"sapart (S,F,T) = (\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart T s1 s2)"

fun frontier :: "('in,'out) state \<Rightarrow> 'in list set" where
"frontier (S,F,T) = {f.((\<exists> s \<in> S. \<exists> i. f = s @ [i]) \<and> f \<notin> S \<and> orun T f \<noteq> None)}"

text \<open>in the original paper the definition of the Frontier F is rather implicit we use @{term "(frontier (S,F,T))"}
  as our F in many cases\<close>

fun hypothesis :: "('in ,'out) state \<Rightarrow> ('in list,'in,'out) trans \<Rightarrow> bool" where
"hypothesis (S,F,T) t =
    (\<forall> s \<in> S. \<forall> i. \<exists> tran op n out. (run T s = Some (Node tran,op)) \<and> 
      (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> S
        then t (s,i) = (s @ [i],out)
        else (\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out))))"

fun norm1 :: "('in ,'out) state \<Rightarrow> nat" where
"norm1 (S,F,T) = ((card S * (card S + 1)) div 2)"

fun norm2 :: "('in,'out) state \<Rightarrow> nat" where
"norm2 (S,F,T) = card {(q,i). q \<in> S \<and> orun T (q @ [i]) \<noteq> None}"

fun norm3 :: "('in ,'out) state \<Rightarrow> nat" where
"norm3 (S,F,T) = card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p}"

fun norm :: "('in ,'out) state \<Rightarrow> nat" where
"norm st = norm1 st + norm2 st + norm3 st"
text \<open>the norm is the same as proposed in the original L sharp paper.\<close>


section \<open>Relational Version\<close>

locale Lsharp_rel =
  fixes M :: "('s :: finite,'in :: finite,'out) mealy" and
    Ilist :: "'in list" and
    diff_query :: "('s,'in,'out) mealy \<Rightarrow> 'in list \<Rightarrow> 'in list \<Rightarrow> 'in list option"
  assumes
  Ilist_UNIV: "set Ilist = UNIV" and
  diff_query_def: "(diff_query (q_0,f) s fs = Some x) \<longrightarrow> (drop (length s) (orun_trans f q_0 (s @ x)) \<noteq>
      drop (length fs) (orun_trans f q_0 (fs @ x)))" and
  diff_query_def_none: "(diff_query (q_0,f) s fs = None) \<longleftrightarrow> (\<nexists> x.(drop (length s) (orun_trans f q_0 (s @ x)) \<noteq>
      drop (length fs) (orun_trans f q_0 (fs @ x))))"
begin

text \<open>this locale is helpful for proving the algorithm.
  \<^item> we fix \<open>M\<close> as our mealy machine as it will not change.
  \<^item> we assert that \<open>M\<close> can only have a finite number of states, and these states are represented as a finite datatype.
  \<^item> we fix \<open>Q\<close> as the finite Universe of the states datatype.
\<^item> we fix \<open>I\<close> as the finite Universe of the input datatype both \<open>I\<close> and \<open>Q\<close> are helpful only to the readability of the proof.
  \<^item> we fix \<open>diff_query\<close> as a query that returns None if the two states given are not apart and an example if they are.
  \<^item> we fix \<open>find3\<close> as the function that finds us a word that is applicable to rule3. explicitly it
  returns a word @{term "x = f@w"} where \<open>w\<close> is a witness to  the apartness
  of two states in \<open>S\<close>, which both are not apart from \<open>f\<close>. if no \<open>f\<close> exists that is not apart to two
  states in \<open>S\<close> it returns @{const None}\<close>

abbreviation Q :: "'s set" where "Q \<equiv> UNIV"
definition I :: "'in set" where "I \<equiv> set Ilist"

lemma univI: "I = UNIV"
  by (simp add: I_def Ilist_UNIV)

fun invar :: "('in,'out) state \<Rightarrow> bool" where
"invar (S,F,T) =
    (finite S \<and> finite F \<and> S \<inter> F = {} \<and>
    (\<forall> e \<in> S. orun T e \<noteq> None) \<and>
    sapart (S,F,T) \<and>
    (\<forall> i. orun T i \<noteq> None \<longrightarrow> orun T i = Some (output_query M i)) \<and>
    F = frontier (S,F,T) \<and>
    [] \<in> S \<and> (\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)))"

lemmas invar_def = invar.simps
declare invar.simps[simp del]

inductive algo_step :: "('in,'out) state \<Rightarrow> ('in,'out) state \<Rightarrow> bool" (infix "\<leadsto>" 50) where

rule1: "\<lbrakk>f \<in> F; \<forall> s \<in> S. apart T s f\<rbrakk> \<Longrightarrow>
    algo_step (S,F,T) (S \<union> {f},frontier (S \<union> {f},F,T),T)" |

rule2: "\<lbrakk>s \<in> S; (orun T (s @ [i]) = None);
      output_query M (s @ [i]) = os \<rbrakk> \<Longrightarrow>
    algo_step (S,F,T) (S,F \<union> {s @ [i]},process_output_query T (s @ [i]) os)" |

rule3: "\<lbrakk>s1 \<in> S; s2 \<in> S; s1 \<noteq> s2; f \<in> F;
      \<not> apart T f s1;
      \<not> apart T f s2;
      apart_witness T s1 s2 w;
      output_query M (f @ w) = os \<rbrakk> \<Longrightarrow>
    algo_step (S,F,T) (S,F,process_output_query T (f @ w) os)" |

rule4: "\<lbrakk>\<forall> s1 \<in> S. \<forall> i. orun T (s1 @ [i]) \<noteq> None;
      \<forall> f \<in> F. \<not> (isolated T S f);
      f \<in> F;
      s \<in> S;
      \<not> apart T s f;
      diff_query M s f = Some is;
      output_query M (s @ is) = oss;
      output_query M (f @ is) = osf\<rbrakk> \<Longrightarrow>
    algo_step (S,F,T) (S,F,process_output_query (process_output_query T (s @ is) oss) (f @ is) osf)"

text \<open>rule4 differs from the original definition by Vandraager et. al. as he compares two whole mealy machines
  while we compare only two states. this difference removes the need of further counterexample processing.\<close>


section \<open>invar\<close>


lemma invars:
  assumes "invar (S,F,T)"
  shows "\<forall> e. \<not> (e \<in> S \<and> e \<in> F)" and
    "\<forall> e \<in> S. orun T e \<noteq> None" and
    "finite S" and
    "finite F" and
    "sapart (S,F,T)" and
    "\<forall> i. orun T i \<noteq> None \<longrightarrow> orun T i = Some (output_query M i)" and
    "F = frontier (S,F,T)" and
    "[] \<in> S" and
    "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
      using assms
      unfolding invar_def
      by blast +


lemma is_invar:
  assumes "\<forall> e. \<not> (e \<in> S \<and> e \<in> F)" and
    "\<forall> e \<in> S. orun T e \<noteq> None" and
    "finite S" and
    "finite F" and
    "sapart (S,F,T)" and
    "\<forall> i. orun T i \<noteq> None \<longrightarrow> orun T i = Some (output_query M i)" and
    "F = frontier (S,F,T)" and
    "[] \<in> S" and
    "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
  shows "invar (S,F,T)"
    using assms
    unfolding invar_def
    by blast


lemma orun_map_empty:
  assumes "i \<noteq> []"
  shows "orun (Node (\<lambda> x. None)) i = None"
    using assms
    apply (induction i)
    apply simp
    by force


lemma empty_is_invar: "invar ({[]},{},Node Map.empty)"
text \<open>@{term "({[]},{},Node Map.empty)"} is the starting point for our algorithm\<close>
proof -
  have a: "\<forall> i. i \<noteq> [] \<longrightarrow> orun (Node (\<lambda> x. None)) i = None"
    using orun_map_empty
    by blast
  have "output_query M [] = []" 
    apply (induction M) 
    apply simp
    unfolding orun_trans_def 
    by simp
  then have "orun (Node (\<lambda> x. None)) [] = Some (output_query M [])"
    by simp
  then have b: "\<forall> i. (\<exists> y. orun (Node (\<lambda> x. None)) i = Some y) \<longrightarrow> orun (Node (\<lambda> x. None)) i = Some (output_query M i)"
    using a
    by (metis option.distinct(1))
  then show ?thesis
    unfolding invar_def
    by auto
qed


lemma invar_substring_in_s: "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s) \<Longrightarrow> s @ a \<in> S \<Longrightarrow> s \<in> S"
  by (induction a rule: rev_induct) auto


section \<open>frontier\<close>

lemma finiteF:
  assumes "finite S"
  shows "finite (frontier ((S,F,T) :: ('in,'out) state))"
proof -
  have fincross: "finite (S \<times> I)"
    using assms univI
    by fastforce
  have eq_img: "{s @ [i] | s i. s \<in> S \<and> i \<in> I} = (\<lambda> (s,i). s @ [i]) ` (S \<times> I)"
    by fast
  have eq_different: "{s @ [i] | s i. s \<in> S \<and> i \<in> I} = {f. (\<exists> s \<in> S. \<exists> i. f = s @ [i])}"
    using univI by blast
  have "{f. (\<exists> s \<in> S. \<exists> i. f = s @ [i])} \<supseteq> frontier (S,F,T)"
    by auto
  then have "finite (frontier (S,F,T))"
    using assms eq_img fincross finite_subset eq_different by auto
  then show ?thesis
    using assms by simp
qed


section \<open>run\<close>

lemma run_eq_out: "case run (Node r) i of
    None \<Rightarrow> orun (Node r) i = None |
    Some (n,out) \<Rightarrow> orun (Node r) i = Some out"
proof (induction i arbitrary: r)
  case Nil
  then show ?case
    by auto
next
  case (Cons a i)
  then show ?case proof (cases "r a")
    case None
    then show ?thesis
      by simp
  next
    case (Some b)
    then obtain r2 o2 where
      b: "b = (Node r2,o2)"
      by (metis otree.exhaust surj_pair)
    then have one: "run (Node r) (a # i) = (case run (Node r2) i of
        None \<Rightarrow> None |
        Some (node,out) \<Rightarrow> Some (node,o2 # out))"
      using Some by simp
    have two: "orun (Node r) (a # i) = (case orun (Node r2) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some b by simp
    have "case run (Node r2) i of
        None \<Rightarrow> orun (Node r2) i = None |
        Some (n,out) \<Rightarrow> orun (Node r2) i = Some out"
      using Cons by simp
    then show ?thesis
      using one two
      apply (cases "run (Node r2) i")
      by auto
  qed
qed

lemma run_eq_out_exhaust: "case run T i of
    None \<Rightarrow> orun T i = None |
    Some (n,out) \<Rightarrow> orun T i = Some out"
  using run_eq_out
  by (metis otree.exhaust)

lemma out_eq_run: "\<exists> node. (case orun (Node r) i of
    None \<Rightarrow> run (Node r) i = None |
    Some out \<Rightarrow> run (Node r) i = Some (node,out))"
proof (induction i arbitrary: r)
  case Nil
  then show ?case
    by auto
next
  case (Cons a i)
  then show ?case proof (cases "r a")
    case None
    then show ?thesis
      by simp
  next
    case (Some b)
    then obtain r2 o2 where
      b: "b = (Node r2,o2)"
      by (metis otree.exhaust surj_pair)
    then have one: "orun (Node r) (a # i) = (case orun (Node r2) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some
      by simp
    have two: "orun (Node r) (a # i) = (case orun (Node r2) i of
        None \<Rightarrow> None |
        Some out \<Rightarrow> Some (o2 # out))"
      using Some b
      by simp
    have three: "run (Node r) (a # i) = (case run (Node r2) i of
        None \<Rightarrow> None |
        Some (node,out) \<Rightarrow> Some (node,o2 # out))"
      using Some b
      by simp
    have "\<exists> node. (case orun (Node r2) i of
        None \<Rightarrow> run (Node r2) i = None |
        Some out \<Rightarrow> run (Node r2) i = Some (node,out))"
      using Cons
      by simp
    then show ?thesis
      using one two three
      apply (cases "orun (Node r2) i")
      by auto
  qed
qed

lemma run_induct_helper: "t i = (Some (tree,out)) \<Longrightarrow> length op = length acc \<Longrightarrow>
    run (process_output_query tree acc op) acc = Some (lt,lout) \<Longrightarrow>
    run (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (lt,out # lout)"
  by (induction acc) auto

lemma orun_induct_helper: "t i = (Some (tree,out)) \<Longrightarrow> length op = length acc \<Longrightarrow>
    orun (process_output_query tree acc op) acc = Some lout \<Longrightarrow>
    orun (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (out # lout)"
  by (induction acc) auto

lemma run_induct_helper_none: "t i = None \<Longrightarrow> length op = length acc \<Longrightarrow>
    run (process_output_query (Node Map.empty) acc op) acc = Some (lt,lout) \<Longrightarrow>
    run (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (lt,out # lout)"
  by (induction acc) auto

lemma orun_induct_helper_none: "t i = None \<Longrightarrow> length op = length acc \<Longrightarrow>
    orun (process_output_query (Node Map.empty) acc op) acc = Some lout \<Longrightarrow>
    orun (process_output_query (Node t) (i # acc) (out # op)) (i # acc) = Some (out # lout)"
  by (induction acc) auto

lemma run_split_existence: "run (Node r) (a # acc) = Some (tr1,out1) \<Longrightarrow> r a \<noteq> None"
  by (auto split: prod.splits option.splits)

lemma orun_split_existence: "orun (Node r) (a # acc) = Some (out1) \<Longrightarrow> r a \<noteq> None"
  by (auto split: prod.splits option.splits)

lemma run_split_none:
  assumes "t i = None" and
    "run (Node tq) acc = Some (Node t,ops)"
  shows "run (Node tq) (acc @ [i]) = None"
using assms proof (induction acc arbitrary: ops tq)
  case Nil
  then show ?case
    by simp
next
  case (Cons a acc)
  then show ?case proof (cases "tq a")
    case None
    then show ?thesis
      using Cons by auto
  next
    case (Some b)
    obtain tr on where
      b: "b = (tr,on)"
      by fastforce
    then have apart_i: "run (Node tq) ((a # acc @ [i])) =
        (case run tr (acc @ [i]) of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some by auto
    then have apart: "run (Node tq) ((a # acc)) =
        (case run tr acc of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some b by auto
    then have "run tr acc \<noteq> None"
      using Some Cons b by (metis option.distinct(1) option.simps(4))
    then obtain opl where
      opl: "run tr acc = Some (Node t,opl)"
      using Some Cons b apart by fastforce
    obtain ntq where
      ntq: "tr = Node ntq"
      using b Some Cons by (metis otree.exhaust)
    then have "run (Node ntq) (acc @ [i]) = None"
      using Cons opl by blast
    then show ?thesis
      using Cons b Some apart opl ntq apart_i by auto
  qed
qed

lemma run_split:
  assumes "t i = Some (tree,op)" and
    "run (Node tq) acc = Some (Node t,ops)"
  shows "run (Node tq) (acc @ [i]) = Some (tree,ops @ [op])"
using assms proof (induction acc arbitrary: ops tq)
  case Nil
  then show ?case
    by fastforce
next
  case (Cons a acc)
  then show ?case proof (cases "tq a")
    case None
    then show ?thesis
      using Cons by auto
  next
    case (Some b)
    obtain tr on where
      b: "b = (tr,on)"
      by fastforce
    then have apart_i: "run (Node tq) (a # acc @ [i]) =
        (case run tr (acc @ [i]) of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some by auto
    then have apart: "run (Node tq) ((a # acc)) =
        (case run tr acc of
          Some (n,opl) \<Rightarrow> Some (n,on # opl) |
          None \<Rightarrow> None)"
      using Some b by auto
    then have "run tr acc \<noteq> None"
      using Some Cons b by (metis option.distinct(1) option.simps(4))
    then obtain opl where
      opl: "run tr acc = Some (Node t,opl)"
      using Some Cons b apart by fastforce
    obtain ntq where
      ntq: "tr = Node ntq"
      using b Some Cons by (metis otree.exhaust)
    then have "run (Node ntq) (acc @ [i]) = Some (tree,opl @ [op])"
      using Cons opl by blast
    then show ?thesis
      using Cons b Some apart opl ntq apart_i by auto
  qed
qed

lemma orun_substring_not_none:
  assumes "orun T (p @ k) \<noteq> None"
  shows "orun T p \<noteq> None"
using assms proof (induction p arbitrary: T)
  case Nil
  then show ?case
    by simp
next
  case (Cons i "is")
  obtain t where
    t: "T = Node t"
    using otree.exhaust by blast
  then show ?case proof(cases "t i")
    case None
    then show ?thesis
      using Cons t by auto
  next
    case (Some a)
    obtain node out where
      a: "a = (node,out)"
      by fastforce
    then have "orun T ((i # is) @ k) = (case orun node (is @ k) of
        Some newout \<Rightarrow> Some (out # newout) |
        None \<Rightarrow> None)"
      using Some t by simp
    then have "orun node (is @ k) \<noteq> None"
      using Cons t by (metis option.simps(4))
    then have not_none: "orun node is \<noteq> None"
      using Cons by blast
    have "orun T (i # is) = (case orun node is of
        Some newout \<Rightarrow> Some (out # newout) |
        None \<Rightarrow> None)"
      using Some t a by auto
    then have "orun T (i # is) \<noteq> None"
      using not_none by auto
    then show ?thesis
      by blast
  qed
qed

lemma run_substring_not_none:
  assumes "run T (p @ k) \<noteq> None"
  shows "run T p \<noteq> None"
    using assms out_eq_run run_eq_out
    by (metis (mono_tags,lifting) otree.exhaust option.simps(4) orun_substring_not_none)

lemma run_not_none_split:
  assumes "run T (s @ [i]) \<noteq> None"
  shows "\<exists> trans out. run T s = Some (Node trans,out) \<and> trans i \<noteq> None"
proof(rule ccontr)
  assume ass: "\<not> (\<exists> trans out. run T s = Some (Node trans,out) \<and> trans i \<noteq> None)"
  have "\<exists> trans out. run T s = Some (Node trans,out)"
    using assms by (metis not_Some_eq otree.exhaust run_substring_not_none surj_pair)
  then obtain trans out where
    trans: "run T s = Some (Node trans,out)"
    by blast
  then have "trans i = None"
    using ass by blast
  then have "run T (s @ [i]) = None"
    by (metis local.trans otree.exhaust run_split_none)
  then show False
    using assms by simp
qed


section \<open>hypothesis\<close>

lemma trans_ex_aux:
  assumes "t = (\<lambda> (s,i). (case run T s of
      None \<Rightarrow> ([],none) |
      Some (Node tran,op) \<Rightarrow> (case tran i of
        None \<Rightarrow> ([],none) |
        Some (n,out) \<Rightarrow> (f (s @ [i]),out))))" and
  "\<exists> node out n op. run T s = Some (Node node,out) \<and> node i = Some (n,op)"
  shows "\<exists> node out n op. run T s = Some (Node node,out) \<and> node i = Some (n,op) \<and> t (s,i) = (f (s @ [i]),op)"
    using assms by auto

lemma exists_hypothesis:
  assumes "invar (S,F,T)" and
    "\<not> (\<exists> f \<in> F. \<forall> s \<in> S. apart T s f)" and
    "\<not> (\<exists> s \<in> S. EX i. (orun T (s @ [i]) = None))"
  shows "\<exists> t. hypothesis (S,F,T) t"
  text \<open>this lemma is equivalent to lemma 3.6 in the L sharp paper\<close>
proof -
  have notning_none: "\<forall> s \<in> S. \<forall> i. orun T (s @ [i]) \<noteq> None"
    using assms by meson
  then have nothing_none_otree: "\<forall> s \<in> S. \<forall> i. run T (s @ [i]) \<noteq> None"
    by (smt (verit) case_optionE option.discI run_eq_out run.elims)
  then have a: "\<forall> s \<in> S. run T s \<noteq> None"
    using run_substring_not_none by blast
  then have "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> (s @ [i]) \<in> frontier (S,F,T)"
    using notning_none by fastforce
  then have "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> (s @ [i]) \<in> F"
    using assms invars(7) by blast
  then have re: "\<forall> s \<in> S. \<forall> i. s @ [i] \<in> S \<or> s @ [i] \<in> F"
    by blast
  then have "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> (\<exists> s2 \<in> S. \<not> apart T s2 (s @ [i]))"
    using assms by blast
  then have "\<exists> f. \<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> f (s @ [i]) \<in> S \<and> \<not> apart T (f (s @ [i])) (s @ [i])"
    by (metis re assms(2))
  then obtain fone where
    fone: "\<forall> s \<in> S. \<forall> i. (s @ [i] \<notin> S \<longrightarrow> fone (s @ [i]) \<in> S \<and> \<not> apart T (fone (s @ [i])) (s @ [i]))"
    by blast
  then obtain f where
    f: "f = (\<lambda> i. (if i \<in> S
        then i
        else fone i))"
    by simp
  then have fsmame: "\<forall> inp \<in> S. f inp = inp"
    by simp
  then have fofnotinS: "\<forall> s \<in> S. \<forall> i. s @ [i] \<notin> S \<longrightarrow> \<not> apart T (f (s @ [i])) (s @ [i]) \<and> (f (s @ [i])) \<in> S"
    using f fone by auto
  have exists: "\<forall> s \<in> S. \<forall> i. \<exists> node out. run T s = Some (Node node,out) \<and> node i \<noteq> None"
    using run_not_none_split nothing_none_otree by meson
  obtain none where
    "none \<in> (UNIV :: 'out set)"
    by simp
  have "\<forall> s \<in> S. \<forall> i. \<exists> node outs out n. run T s = Some (Node node,outs) \<and> node i = Some (n,out)"
    using exists by fast
  have "\<exists> t. t = (\<lambda> (s,i). (case run T s of
      None \<Rightarrow> ([],none) |
      Some (Node tran,op) \<Rightarrow> (case tran i of
        None \<Rightarrow> ([],none) |
        Some (n,out) \<Rightarrow> (if s @ [i] \<in> S
          then (s @ [i],out)
          else (f (s @ [i]),out)))))"
    by simp
  then obtain t where
    thelp: "t = (\<lambda> (s,i). (case run T s of
        None \<Rightarrow> ([],none) |
        Some (Node tran,op) \<Rightarrow> (case tran i of
          None \<Rightarrow> ([],none) |
          Some (n,out) \<Rightarrow> (f (s @ [i]),out))))"
    by fast
  then have tdef: "\<forall> s \<in> S. \<forall> i. \<exists> node out n op.
      (run T s = Some (Node node,out)) \<and> (node i = Some (n,op) \<and> t (s,i) = (f (s @ [i]),op))"
    using exists trans_ex_aux thelp by fast
  then have "\<forall> s \<in> S. \<forall> i. \<exists> tran op n out.
      run T s = Some (Node tran,op) \<and>
      tran i = Some (n,out) \<and> (if s @ [i] \<in> S
        then t (s,i) = (s @ [i],out)
        else \<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out))"
    using f fone by fastforce
  then have "hypothesis (S,F,T) t"
    by simp
  then show ?thesis
    by blast
qed

lemma hypothesis_split_in_S:
  assumes "hypothesis (S,F,T) t" and
    "s \<in> S" and
    "run T s = Some (Node tran,op)" and
    "tran i = Some (n,out)" and
    "s @ [i] \<in> S"
  shows "t (s,i) = (s @ [i],out)"
proof -
  have "\<exists> tran op n out. (run T s = Some (Node tran,op)) \<and> (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> S
        then t (s,i) = (s @ [i],out)
        else (\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)))"
    using assms(1,2)
    by simp
  then have "t (s,i) = (s @ [i],out)"
    using assms by auto
  then show ?thesis
    by simp
qed

lemma hypothesis_split_notin_S:
  assumes "hypothesis (S,F,T) t" and
    "s \<in> S" and
    "run T s = Some (Node tran,op)" and
    "tran i = Some (n,out)" and
    "s @ [i] \<notin> S"
  shows "\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)"
proof -
  have "\<exists> tran op n out. (run T s = Some (Node tran,op)) \<and> (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> S
        then t (s,i) = (s @ [i],out)
        else (\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)))"
    using assms(1,2)
    by fastforce
  then have "\<exists> y \<in> S. \<not> apart T y (s @ [i]) \<and> t (s,i) = (y,out)"
    using assms by auto
  then show ?thesis
    by simp
qed


section \<open>apart\<close>

lemma apart_sim:
  assumes "apart T p q" and
    "func_sim (q_0,t) T f"
  shows "f q \<noteq> f p"
  text \<open>this lemma is a weaker version of lemma 2.7 in the L sharp paper.
    the original paper states that @{term "\<not>(eq_mealy (q_0,t) (f q) (q_0,t) (f p))"} holds.\<close>
proof
  assume as: "f q = f p"
  then have a: "\<forall> is ops. orun T (q @ is) =
      Some ops \<longrightarrow> run_trans t (f q) is = (f (q @ is),(drop (length q) ops))"
    using assms
    unfolding func_sim_def
    by blast
  have b: "\<forall> is ops. orun T (p @ is) =
      Some ops \<longrightarrow> run_trans t (f p) is = (f (p @ is),(drop (length p) ops))"
    using assms unfolding func_sim_def as by simp
  have "\<exists> i x y. orun T (q @ i) = Some x \<and> orun T (p @ i) = Some y \<and> drop (length q) x \<noteq>
      drop (length p) y"
    using assms by fastforce
  then show False
    using a b as by fastforce
qed

lemma apart_none:
  assumes "\<not> apart T f s1" and
    "\<not> apart T f s2" and
    "apart_witness T s1 s2 w"
  shows "orun T (f @ w) = None"
  text \<open>this lemma is useful as we know we can change the output for @{term "orun T (f @ w)"} in rule2\<close>
proof (rule ccontr)
  assume ass: "orun T (f @ w) \<noteq> None"
  obtain x where
    x: "orun T (s1 @ w) = Some x"
    using assms by auto
  obtain y where
    y: "orun T (s2 @ w) = Some y"
    using assms by auto
  have neq: "drop (length s2) y \<noteq> drop (length s1) x"
    using assms x y by fastforce
  then obtain z where
    z: "orun T (f @ w) = Some z"
    using ass by blast
  then have a: "drop (length f) z = drop (length s1) x"
    using z x assms by simp
  then have b: "drop (length f) z = drop (length s2) y"
    using z y assms by simp
  show False
    using a b neq by simp
qed

lemma not_none_not_both_apart:
  assumes "orun T (f @ w) = Some z" and
    "apart_witness T s1 s2 w"
  shows "apart T f s1 \<or> apart T f s2"
    by (metis apart_none assms option.discI)

lemma exsist_witness:
  assumes "apart T s1 s2"
  shows "\<exists> w. apart_witness T s1 s2 w"
proof -
  have "\<exists> i x y. orun T (s1 @ i) = Some x \<and>
      orun T (s2 @ i) = Some y \<and>
      drop (length s1) x \<noteq> drop (length (s2)) y"
    using assms by auto
  then obtain w where
    "\<exists> x y. orun T (s1 @ w) = Some x \<and>
        orun T (s2 @ w) = Some y \<and>
        drop (length s1) x \<noteq> drop (length (s2)) y"
    by blast
  then have "apart_witness T s1 s2 w"
    by simp
  then show ?thesis
    by fast
qed


section \<open>output query\<close>

lemma output_query_length:
  assumes "output_query M iss = os"
  shows "length iss = length os"
  text \<open>we base our \<open>process_output_query\<close> proofs on the length of input and output being the same, 
to combine this lemma is needed\<close>
proof -
  obtain q_0 t where
    m: "M = (q_0,t)"
    by fastforce
  then have "output_query (q_0,t) iss = os \<Longrightarrow> length iss = length os"
    using run_trans_length
    apply (simp split: prod.splits option.splits)
    using out_srun_trans by fastforce
  then show ?thesis
    using m assms by blast
qed


section \<open>process Output Query\<close>

lemma process_op_query_not_none:
"length ip = length op \<Longrightarrow> run (process_output_query (Node t) ip op) ip \<noteq> None"
proof (induction ip arbitrary: op t)
  case Nil
  then show ?case
    by auto
next
  case (Cons a ip)
  obtain ofs os where
    ofs: "op = os # ofs"
    using Cons
    apply simp
    by (meson Suc_length_conv)
  then show ?case proof (cases "t a")
    case None
    have "run (process_output_query (Node Map.empty) ip ofs) ip \<noteq> None"
      using Cons ofs by auto
    then obtain lt lout where
      "run (process_output_query (Node Map.empty) ip ofs) ip = Some (lt,lout)"
      by fast
    then have "run (process_output_query (Node t) (a # ip) op) (a # ip) = Some (lt,os # lout)"
      using Cons ofs None run_induct_helper_none by auto
    then show ?thesis
      by auto
  next
    case (Some b)
    then show ?thesis proof (cases b)
      case (Pair tree c)
      have "run (process_output_query tree ip ofs) ip \<noteq> None"
        using Cons ofs
        apply simp
        by (metis otree.exhaust surj_pair)
      then obtain lt lout where
        "run (process_output_query tree ip ofs) ip = Some (lt,lout)"
        by fast
      then have "run (process_output_query (Node t) (a # ip) op) (a # ip) = Some (lt,c # lout)"
        using Cons ofs Some Pair run_induct_helper
        by auto
      then show ?thesis
        by auto
    qed
  qed
qed

lemma output_query_different: "length op = length ip \<Longrightarrow> i \<noteq> ac \<Longrightarrow>
    (case process_output_query (Node t) (i # ip) (os # op) of
      (Node ts) \<Rightarrow> ts ac = t ac)"
  by (auto split: prod.splits option.splits)

lemma run_output_query_different:
  assumes "ac \<noteq> i" and
    "length ip = length op" and
    "t ac = Some (tree,outies)"
  shows "run (process_output_query (Node t) (i # ip) (os # op)) (ac # list) =
      (case run tree list of
        Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
        None \<Rightarrow> None)"
proof -
  have "case process_output_query (Node t) (i # ip) (os # op) of
      (Node ts) \<Rightarrow> ts ac = t ac"
    using assms output_query_different[of op ip i ac] by auto
  then show ?thesis
    using assms(3) by (auto split: prod.splits option.splits)
qed


lemma output_query_retains_some:
  assumes "length ip = length op" and
    "run q_0 acc \<noteq> None"
  shows "run (process_output_query q_0 ip op) acc \<noteq> None"
  text \<open>this lemma is important as it shows that if a input is not none before the processing of a query it will stay that way after,
    this is useful to prove that parts of the norm does not decrease.\<close>
using assms proof (induction ip arbitrary: op acc q_0)
  case Nil
  then show ?case
    by simp
next
  case a: (Cons a ip)
  obtain os ops where
    os: "op = os # ops"
    using a
    apply simp
    by (meson Suc_length_conv)
  then show ?case proof (cases acc)
    case Nil
    then show ?thesis
      by auto
  next
    case (Cons ac list)
    then show ?thesis
    proof (cases q_0)
      case (Node r)
      then show ?thesis using a proof (cases "a = ac")
        case True
        then show ?thesis proof (cases "r ac")
          case None
          then have "run (q_0) (ac # list) = None"
            using Node by auto
          then show ?thesis
            using a Cons by simp
        next
          case (Some c)
          then obtain tree outies where
            outies: "r ac = Some (tree,outies)"
            using Node Cons a Some by fastforce
          then have h2: "run (process_output_query q_0 (a # ip) (os # ops)) (ac # list) =
              (case run (process_output_query tree ip ops) list of
                Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
                None \<Rightarrow> None)"
            using Some True Node Cons a run_output_query_different by auto
          have h1: "run q_0 (ac # list) = (case run tree list of
              Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
              None \<Rightarrow> None)"
            using outies Node by auto
          have "run q_0 (ac # list) \<noteq> None"
            using a Cons by blast
          then have "run tree list \<noteq> None"
            using a h1 by (metis option.simps(4))
          then have "run (process_output_query tree ip ops) list \<noteq> None"
            using a os by force
          then show ?thesis
            using h2 os Cons by force
        qed
      next
        case False
        then show ?thesis proof (cases "r ac")
          case None
          then have "run q_0 (ac # list) = None"
            using Node by auto
          then show ?thesis
            using a Cons by simp
        next
          case (Some c)
          then obtain tree outies where
            outies: "r ac = Some (tree,outies)"
            using Node Cons a Some by fastforce
          then have h2: "run (process_output_query q_0 (a # ip) (os # ops)) (ac # list) =
              (case run tree list of
                Some (n,opl) \<Rightarrow> Some (n,outies # opl) |
                None \<Rightarrow> None)"
            using Some False Node Cons a run_output_query_different
            by (auto split: prod.splits option.splits)
          have h1: "run q_0 (ac # list) = (case run tree list of
              Some (n,opl) \<Rightarrow>
              Some (n,outies # opl) |
              None \<Rightarrow> None)"
            using outies Node by auto
          have "run q_0 (ac # list) \<noteq> None"
            using a Cons by blast
          then have "run tree list \<noteq> None"
            using h1 by (metis option.simps(4))
          then show ?thesis
            using h2 Cons a by (simp add: h1 os)
        qed
      qed
    qed
  qed
qed

lemma output_query_retains_some_output:
  assumes "length ip = length op" and
    "orun q_0 acc \<noteq> None"
  shows "orun (process_output_query q_0 ip op) acc \<noteq> None"
proof -
  obtain r where
    lr: "q_0 = Node r"
    using otree.exhaust by auto
  then have "run q_0 acc \<noteq> None"
    using out_eq_run[of r acc] assms by auto
  then have ot: "run (process_output_query q_0 ip op) acc \<noteq> None"
    using output_query_retains_some assms by blast
  obtain r2 where
    "(process_output_query q_0 ip op) = Node r2"
    using otree.exhaust by auto
  then have "orun (process_output_query q_0 ip op) acc \<noteq> None"
    using run_eq_out[of r2 acc] ot by auto
  then show ?thesis
    by simp
qed

lemma process_op_query_not_none_output:
  assumes "length ip = length op"
  shows "orun (process_output_query (Node t) ip op) ip \<noteq> None"
proof -
  have ot: "run (process_output_query (Node t) ip op) ip \<noteq> None"
    using output_query_retains_some assms process_op_query_not_none by blast
  obtain r2 where
    "(process_output_query (Node t) ip op) = Node r2"
    using otree.exhaust by auto
  then have "orun (process_output_query (Node t) ip op) ip \<noteq> None"
    using run_eq_out[of r2] ot
    by (metis (full_types,lifting) option.simps(4) out_eq_run)
  then show ?thesis
    by simp
qed

lemma output_query_retains_some_specific:
  assumes "length ip = length op" and
    "orun (Node r) acc = Some (out1)"
  shows "orun (Node r) acc = orun (process_output_query (Node r) ip op) acc"
using assms proof (induction acc arbitrary: ip op r out1)
  case Nil
  then show ?case
    by simp
next
  case c: (Cons a acc)
  then show ?case proof (cases ip)
    case Nil
    then have "op = []"
      using c by simp
    then show ?thesis
      using Nil c by force
  next
    case (Cons i ilist)
    then obtain ops olist where
      op: "op = ops # olist"
      using c by (metis Suc_length_conv)
    obtain r2 outs where
      ra: "r a = Some (Node r2,outs)"
      using c orun_split_existence option.exhaust by (metis otree.exhaust old.prod.exhaust)
    then show ?thesis proof (cases "i = a")
      case True
      then have "orun (process_output_query (Node r) ip op) (a # acc) =
          orun (process_output_query (Node r) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op by presburger
      also have "\<dots> = orun (case r i of
          None \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some ((process_output_query (Node (\<lambda> k. None)) ilist olist),ops)
            else r j)) |
          Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
            then Some ((process_output_query tree ilist olist),out)
            else r j))) (a # acc)"
        using True ra by simp
      also have "\<dots> = orun (Node (\<lambda> j. if j = i
          then Some ((process_output_query (Node r2) ilist olist,outs))
          else r j)) (a # acc)"
        using ra by (simp add: True)
      also have "\<dots> = (case orun (process_output_query (Node r2) ilist olist) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using ra True by auto
      finally have calc1: "orun (process_output_query (Node r) ip op) (a # acc) =
          (case orun (process_output_query (Node r2) ilist olist) acc of
            Some output \<Rightarrow> Some (outs # output) |
            None \<Rightarrow> None)"
        by blast
      have "orun (process_output_query (Node r2) ilist olist) acc \<noteq> None"
        using calc1 c(3) Cons True output_query_retains_some_output
        by (metis c.prems(1) option.discI option.simps(4))
      then obtain outputs1 where
        n1: "orun (process_output_query (Node r2) ilist olist) acc = Some (outputs1)"
        by fast
      have calc2: "orun (Node r) (a # acc) = (case orun (Node r2) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using c ra True by simp
      then have "orun (Node r2) acc \<noteq> None"
        using c by (metis not_Some_eq option.simps(4))
      then obtain outputs2 where
        n2: "orun (Node r2) acc = Some (outputs2)"
        by auto
      have "outputs1 = outputs2"
        using c.IH n1 n2 c(2) op Cons append1_eq_conv length_Cons by fastforce
      then show ?thesis
        using calc1 calc2 Cons c True by (simp add: n1 n2)
    next
      case False
      then have "orun (process_output_query (Node r) ip op) (a # acc) =
          orun (process_output_query (Node r) (i # ilist) (ops # olist)) (a # acc)"
        using Cons op by presburger
      also have "\<dots> = orun (case r i of
            None \<Rightarrow> (Node (\<lambda> j. if j = i
              then Some (process_output_query (Node (\<lambda> k. None)) ilist olist,ops)
              else r j)) |
            Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
              then Some ((process_output_query tree ilist olist),out)
              else r j)))
          (a # acc)"
        using False ra by simp
      also have "\<dots> = (case orun (Node r2) acc of
          Some output \<Rightarrow> Some (outs # output) |
          None \<Rightarrow> None)"
        using ra False
        by (cases "r i") auto
      also have "\<dots> = orun (Node r) (a # acc)"
        using ra by simp
      finally show ?thesis
        using c Cons by force
    qed
  qed
qed

lemma op_query_output_not_equal:
  assumes "i \<noteq> j"
  shows "orun (process_output_query (Node t) (i # is) (op # ops)) (j # js) = orun (Node t) (j # js)"
proof -
  have "(process_output_query (Node t) (i # is) (op # ops)) = (case t i of
      None \<Rightarrow> (Node (\<lambda> j. if j = i
        then Some (process_output_query (Node (\<lambda> k. None)) is ops,op)
        else t j)) |
      Some (tree,out) \<Rightarrow> (Node (\<lambda> j. if j = i
        then Some ((process_output_query tree is ops),out)
        else t j)))"
    by simp
  then show ?thesis proof (cases "t i")
    case None
    then have eq: "(process_output_query (Node t) (i # is) (op # ops)) =
        (Node (\<lambda> j. if j = i
          then Some (process_output_query (Node (\<lambda> k. None)) is ops,op)
          else t j))"
      by simp
    have "orun (Node (\<lambda> j. if j = i
          then Some (process_output_query (Node (\<lambda> k. None)) is ops,op)
          else t j)) (j # js) =
        orun (Node t) (j # js)"
      using assms by auto
    then show ?thesis
      using eq by argo
  next
    case (Some a)
    obtain tree out where
      "a = (tree,out)"
      by fastforce
    then have eq: "(process_output_query (Node t) (i # is) (op # ops)) =
        (Node (\<lambda> j. if j = i
          then Some ((process_output_query tree is ops),out)
          else t j))"
      using Some by fastforce
    have "orun (Node (\<lambda> j. if j = i
          then Some ((process_output_query tree is ops),out)
          else t j)) (j # js) =
        orun (Node t) (j # js)"
      using assms by auto
    then show ?thesis
      using eq by argo
  qed
qed

lemma substring_different_query:
  assumes "orun T i = None" and
    "length j = length out" and
    "orun (process_output_query T j out) i \<noteq> None"
  shows "\<exists> y. j = i @ y"
using assms proof (induction i arbitrary: out j T)
  case Nil
  then show ?case
    by blast
next
  case (Cons a i)
  obtain t where
    node: "T = Node t"
    using otree.exhaust by auto
  have lenj: "length j = length out"
    using Cons output_query_length by blast

  then show ?case proof (cases "j = []")
    case True
    then show ?thesis
      using Cons lenj by auto
  next
    case False
    then obtain jfront js where
      j: "j = jfront # js"
      by (metis list.exhaust)
    then obtain op os where
      out: "out = op # os"
      using list.exhaust lenj
      by (metis False length_greater_0_conv)
    have induc_two: "length js = length os"
      using lenj j out by auto
    then show ?thesis
    proof (cases "jfront = a")
      case eq: True
      then show ?thesis proof (cases "t jfront")
        case None

        have proc: "(process_output_query T (jfront # js) (op # os)) =
            (Node (\<lambda> j. if j = jfront
              then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
              else t j))"
          using node None by auto
        then have "orun (process_output_query T (jfront # js) (op # os)) (a # i) =
            orun (Node (\<lambda> j. if j = jfront
              then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
              else t j)) (a # i)"
          by force
        also have b: "\<dots> = (case (\<lambda> j. if j = jfront
              then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
              else t j) a of
            Some (n,op) \<Rightarrow>
            (case (orun n i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None) |
            None \<Rightarrow> None)"
          by auto
        also have c: "\<dots> =
            (case (orun (process_output_query (Node (\<lambda> k. None)) js os) i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None)"
          using eq by auto

        have induc_three: "(orun (process_output_query (Node (\<lambda> k. None)) js os) i) \<noteq> None"
          using calculation Cons proc by (metis c j option.simps(4) out)
        then show ?thesis
        proof (cases "i = []")
          case True
          then show ?thesis
            by (simp add: eq j)
        next
          case False
          obtain ifront "is" where
            "i = ifront # is"
            using False list.exhaust by auto
          then have "(orun (Node (\<lambda> k. None)) i) = (case (\<lambda> k. None) ifront of
              Some (n,op) \<Rightarrow>
              (case (orun n is) of
                Some ops \<Rightarrow> Some (op # ops) |
                None \<Rightarrow> None) |
              None \<Rightarrow> None)"
            by simp
          then have induc_one: "(orun (Node (\<lambda> k. None)) i) = None"
            by auto
          show ?thesis
            using Cons.IH[of "Node (\<lambda> k. None)" js os] induc_one induc_two induc_three eq j by auto
        qed
      next
        case (Some b)
        obtain atree aout where
          atree: "b = (atree,aout)"
          by (metis surj_pair)
        then have proc: "(process_output_query T (jfront # js) (op # os)) =
            Node (\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j)"
          using node Some by auto
        then have "orun (process_output_query T (jfront # js) (op # os)) (a # i) =
            orun (Node (\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j)) (a # i)"
          by argo
        also have "\<dots> = (case (\<lambda> j. if j = jfront
              then Some ((process_output_query atree js os),aout)
              else t j) a of
            Some (n,op) \<Rightarrow>
            (case (orun n i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None) |
            None \<Rightarrow> None)"
          by simp
        also have c: "\<dots> =
            (case (orun (process_output_query atree js os) i) of
              Some ops \<Rightarrow> Some (aout # ops) |
              None \<Rightarrow> None)"
          using eq by auto
        finally have induc_three: "orun (process_output_query atree js os) i \<noteq> None"
          using Cons by (metis j option.simps(4) out)
        have "(case t a of
            Some (n,op) \<Rightarrow> (case (orun n i) of
              Some ops \<Rightarrow> Some (op # ops) |
              None \<Rightarrow> None) |
            None \<Rightarrow> None) = None"
          using Cons node by auto
        then have "(case (orun atree i) of
            Some ops \<Rightarrow> Some (aout # ops) |
            None \<Rightarrow> None) = None"
          using Some atree eq by auto
        then have induc_one: "orun atree i = None"
          using not_None_eq by fastforce
        then show ?thesis
          using induc_one induc_two induc_three Cons j by (simp add: eq)
      qed
    next
      case False
      then show ?thesis
        using op_query_output_not_equal j node out Cons by metis
    qed
  qed
qed

lemma output_query_keeps_invar_aux:
  assumes "orun T i = None" and
    "orun_trans t q_0 j = out" and
    "T' = process_output_query T j out" and
    "\<forall> k y. orun T k = Some y \<longrightarrow> orun_trans t q_0 k = y"
  shows "orun T' i \<noteq> None \<longrightarrow> orun T' i = Some (orun_trans t q_0 i)"
proof (cases "orun T' i = None")
  case True
  then show ?thesis
    by blast
next
  case False
  have lenj: "length j = length out"
    using assms(2) run_trans_length out_srun_trans by fast
  then have subs: "\<exists> y. j = i @ y"
    using substring_different_query False assms by blast
  then show ?thesis using assms lenj proof (induction i arbitrary: q_0 j out T T')
    case Nil
    then show ?case
      by simp
  next
    case (Cons a i)
    obtain f where
      T: "T = Node f"
      by(cases T) auto
    obtain f' where
      T': "T' = Node f'"
      by(cases T') auto
    obtain b js where
      j: "j = b # js"
      using Cons by auto
    obtain op os where
      out: "out = op # os"
      using Cons by (metis j length_Suc_conv)
    obtain q' out' where
      q': "t (q_0,a) = (q',out')"
      by fastforce
    have eq: "b = a"
      using subs j Cons by auto

    have ih_prem1: "\<exists> y. js = i @ y"
      using Cons.prems(1) j by auto
    have ih_prem3: "orun_trans t q' js = os"
      using Cons.prems(3) eq j out q' unfolding orun_trans_def 
      by (metis orun_trans_def prod.inject split_orun_trans_rev)
    have ih_prem5: "length js = length os"
      using Cons.prems(6) j out by auto

    show ?case proof (cases "f a")
      case None
      have query: "process_output_query (Node f) (b # js) (op # os) = (Node (\<lambda> k. if k = b
          then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
          else f k))"
        using Cons None eq by auto
      have ca:"orun T' (a # i) = orun (process_output_query (Node f) (b # js) (op # os)) (a # i)"
        using Cons j out T by argo
      also have cb:"\<dots> = orun (Node (\<lambda> k. if k = b
          then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
          else f k)) (a # i)"
        using query by argo
      also have cd:"\<dots> = (case (\<lambda> k. if k = b
            then Some (process_output_query (Node (\<lambda> k. None)) js os,op)
            else f k) a of
          Some (n,op) \<Rightarrow>
          (case (orun n i) of
            Some ops \<Rightarrow> Some (op # ops) |
            None \<Rightarrow> None) |
          None \<Rightarrow> None)"
        by simp
      also have ce:"\<dots> = (case orun (process_output_query (Node (\<lambda> k. None)) js os) i of
          Some ops \<Rightarrow> Some (op # ops) |
          None \<Rightarrow> None)"
        by (simp add: eq)

      then show ?thesis proof (cases "i")
        case Nil
        then have "orun_trans t q_0 (a # i) =[op]" 
            using Cons.prems(3) T q' eq j out unfolding orun_trans_def 
            by (metis list.inject orun_trans_def run_trans.simps(1) snd_conv orun_trans_Cons)
        then show ?thesis
          using Cons.prems(3) Cons.prems(4) T q' eq j out query Nil by auto
      next
        case c:(Cons c list)
        have ih_prem2: "orun (Node (\<lambda> k. None)) i = None"
          using c by fastforce
        obtain T'' where
          T'': "T'' = process_output_query (Node (\<lambda> k. None)) js os"
          by simp
        have ih_prem4: "\<forall> k y. orun (Node (\<lambda> k. None)) k = Some y \<longrightarrow> orun_trans t q' k = y"
          unfolding orun_trans_def 
          by (metis option.distinct(1) option.inject orun.simps(1) orun_map_empty run_trans.simps(1) snd_conv)
        have "(orun T'' i) \<noteq> None \<longrightarrow>
            (orun T'' i) = Some (orun_trans t q' i)"
          using Cons.IH[of js "Node (\<lambda> k. None)" q' os T''] ih_prem1 ih_prem2 ih_prem3
          using ih_prem4 T'' ih_prem5
          by blast
        then have "(orun (process_output_query (Node (\<lambda> k. None)) js os) i) \<noteq> None \<longrightarrow>
            (orun (process_output_query (Node (\<lambda> k. None)) js os) i) = Some (orun_trans t q' i)"
          using T'' by blast
        then show ?thesis
          using Cons.prems(3) calculation eq j out q' 
          by (metis ce list.inject option.simps(4,5) orun_trans_Cons)
      qed
    next
      case (Some c)
      obtain nextnode nextout where
        nextnode: "c = (nextnode,nextout)"
        by fastforce
      have query: "process_output_query (Node f) (b # js) (op # os) =
          (Node (\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j))"
        using eq nextnode Some by auto
      then have a: "orun (process_output_query (Node f) (b # js) (op # os)) (a # i) =
          orun (Node (\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j)) (a # i)"
        by presburger
      also have b: "\<dots> = (case (\<lambda> j. if j = b
            then Some ((process_output_query nextnode js os),nextout)
            else f j) a of
          Some (n,op) \<Rightarrow> (case (orun n i) of
            Some ops \<Rightarrow> Some (op # ops) |
            None \<Rightarrow> None) |
          None \<Rightarrow> None)"
        by simp
      also have c: "\<dots> = (case (orun (process_output_query nextnode js os) i) of
          Some ops \<Rightarrow> Some (nextout # ops) |
          None \<Rightarrow> None)"
        by (simp add: eq)
      have "orun T (a # i) = (case (orun nextnode i) of
          Some ops \<Rightarrow> Some (nextout # ops) |
          None \<Rightarrow> None)"
        using T nextnode Some by auto
      then have ih_prem2: "orun nextnode i = None"
        using Cons by (metis not_None_eq option.simps(5))
      obtain T'' where
        T'': "T'' = process_output_query nextnode js os"
        by simp
      have alt_nextout: "orun T [a] = Some [nextout]"
        using Some nextnode T by simp
      have alt_out': "orun_trans t q_0 [a] = [out']"
        using q' unfolding orun_trans_def by simp
      have "orun T [a] \<noteq> None \<longrightarrow> Some (orun_trans t q_0 [a]) = orun T [a]"
        using Cons by fastforce
      then have nextout_eq_out': "nextout = out'"
        using alt_out' alt_nextout by simp
      have part: "\<forall> k. orun T (a # k) =
          (case (orun nextnode k) of
            Some ops \<Rightarrow> Some (nextout # ops) |
            None \<Rightarrow> None)"
        using T Some nextnode by auto
      have part2: "\<forall> k. orun_trans t q_0 (a # k) = out' # orun_trans t q' k"
        using q' orun_trans_Cons by fast
      have "\<forall> k y. orun T (a # k) = Some (out' # y) \<longrightarrow> orun_trans t q_0 (a # k) = (out' # y)"
        using Cons by fastforce
      then have ih_prem4: "\<forall> k y. orun nextnode k = Some y \<longrightarrow> orun_trans t q' k = y"
        using part q' part2 nextout_eq_out' by auto
      have "(orun (process_output_query nextnode js os) i) \<noteq> None \<longrightarrow>
          orun (process_output_query nextnode js os) i = Some (orun_trans t q' i)"
        using Cons.IH[of js nextnode q' os "process_output_query nextnode js os"]
      ih_prem1 ih_prem2 ih_prem3 ih_prem4 ih_prem5 T'' nextnode Some
        by argo
      then show ?thesis
        using Cons.prems(4) T c calculation j nextout_eq_out' option.simps(4) out part2 by auto
    qed
  qed
qed

lemma output_query_keeps_invar:
  assumes "orun T i = None" and
    "output_query M j = out" and
    "\<forall> k y. orun T k = Some y \<longrightarrow> output_query M k = y"
  shows "orun (process_output_query T j out) i \<noteq> None \<longrightarrow> 
  orun (process_output_query T j out) i = Some (output_query M i)"
proof -
  obtain t q_0 where
    "M = (q_0,t)"
    by fastforce
  then have "\<forall> is. output_query M is = orun_trans t q_0 is"
    by simp
  then show ?thesis
    by (metis (mono_tags,lifting) assms output_query_keeps_invar_aux)
qed

lemma proc_output_query_retains_apart:
  assumes "length ip = length op" and
    "apart T s1 s2"
  shows "apart (process_output_query T ip op) s1 s2"
    using output_query_retains_some_specific assms
    by (smt (verit,ccfv_SIG) apart.simps length_0_conv process_output_query.elims process_output_query.simps(1))

lemma proc_output_query_retains_sapart:
  assumes "length ip = length op" and
    "sapart (S,F,T)"
  shows "sapart (S,F,(process_output_query T ip op))"
    using proc_output_query_retains_apart assms by (metis sapart.simps)


section \<open>norm\<close>

abbreviation max_norm where
"max_norm S \<equiv> (card S * (card S + 1)) div 2 + card S * card I + card S * (card S * card I)"

lemma norm_max:
  assumes "invar (S,F,T)"
  shows "norm (S,F,T) \<le> max_norm S"
  text \<open>this shows that the norm is always smaller as @{term "max_norm S"}\<close>
proof -
  have fst: "norm1 (S,F,T) = (card S * (card S + 1) div 2)"
    by simp
  have fin_snd: "finite (S \<times> I)"
    using assms invars(3) by auto
  have "{(q,i). q \<in> S \<and> orun T (q @ [i]) \<noteq> None} \<subseteq> (S \<times> I)"
    using univI by blast
  then have "norm2 (S,F,T) \<le> (card (S \<times> I))"
    using fin_snd card_mono by auto
  then have snd: "norm2 (S,F,T) \<le> card S * card I"
    by (simp add: card_cartesian_product)
  have fin_trd: "finite ((\<lambda> (s,i). s @ [i]) ` (S \<times> I))"
    using fin_snd univI by blast
  have "\<forall> f \<in> F. \<exists> s \<in> S. \<exists> i. f = s @ [i]"
    using assms invars(7) by fastforce
  then have pre: "F \<subseteq> {s @ [i] |
      s i. s \<in> S \<and> i \<in> I}"
    using assms univI by blast
  have f_image: "{s @ [i] |
      s i. s \<in> S \<and> i \<in> I} = (\<lambda> (s,i). s @ [i]) ` (S \<times> I)"
    by fast
  then have card_pre: "card F \<le> card ((\<lambda> (s,i). s @ [i]) ` (S \<times> I))"
    using fin_trd pre card_mono by fastforce
  have "inj_on (\<lambda> (s,i). s @ [i]) (S \<times> I)"
    unfolding inj_on_def by (auto split: prod.splits)
  then have "card ((\<lambda> (s,i). s @ [i]) ` (S \<times> I)) = card (S \<times> I)"
    using card_image by blast
  then have card_f_less_cross: "card F \<le> card (S \<times> I)"
    using card_pre by argo
  have subs_trd: "{(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<subseteq> (S \<times> F)"
    by blast
  have "finite (S \<times> F)"
    using assms invars(3,4) by blast
  then have "norm3 (S,F,T) \<le> card (S \<times> F)"
    using subs_trd card_mono by fastforce
  then have trd: "norm3 (S,F,T) \<le> (card S * (card S * card I))"
    by (metis (full_types) card_cartesian_product card_f_less_cross dual_order.trans mult_le_mono2)
  then show ?thesis
    using fst snd trd by force
qed

lemma func_sim_of_output_query:
  assumes "\<forall> inp x. orun T inp = Some x \<longrightarrow> output_query M inp = x"
  shows "\<exists> f. func_sim M T f"
proof -
  obtain q_0 transmealy where
    m: "M = (q_0,transmealy)"
    by fastforce
  have "\<exists> f. \<forall> i. f i = fst (run_trans transmealy q_0 i)"
    by auto
  then obtain f where
    f: "\<forall> i. f i = fst (run_trans transmealy q_0 i)"
    by auto
  then have one: "f [] = q_0"
    by auto
  have b: "\<forall> inp out. orun T inp = Some out \<longrightarrow> out = snd (run_trans transmealy q_0 inp)"
    using assms m by (simp add: out_srun_trans)
  have c: "\<forall> acc is ops.
      run_trans transmealy (fst (run_trans transmealy q_0 acc)) is =
      (fst (run_trans transmealy q_0 (acc @ is)),drop (length acc) (snd (run_trans transmealy q_0 (acc @ is))))"
    using run_trans_two_nested by fast
  then have "\<forall> acc is ops. orun T (acc @ is) = Some ops \<longrightarrow> ops = output_query M (acc @ is)"
    using assms by simp
  then have "(\<forall> acc is ops. orun T (acc @ is) = Some ops \<longrightarrow> run_trans transmealy (f acc) is =
        (f (acc @ is),(drop (length acc) ops))) =
      (\<forall> acc is ops. orun T (acc @ is) = Some ops \<longrightarrow> ops = output_query M (acc @ is) \<longrightarrow>
        run_trans transmealy (f acc) is = (f (acc @ is),(drop (length acc) ops)))"
    by presburger
  also have "\<dots> = (\<forall> acc is ops. orun T (acc @ is) = Some ops \<longrightarrow> ops = output_query M (acc @ is) \<longrightarrow>
      run_trans transmealy (fst (run_trans transmealy q_0 acc)) is =
      (fst (run_trans transmealy q_0 (acc @ is)),(drop (length acc) ops)))"
    using f by presburger
  also have "\<dots> = (\<forall> acc is ops. orun T (acc @ is) = Some ops \<longrightarrow> ops =
      snd (run_trans transmealy q_0 (acc @ is)) \<longrightarrow>
      run_trans transmealy (fst (run_trans transmealy q_0 acc)) is =
      (fst (run_trans transmealy q_0 (acc @ is)),(drop (length acc) (snd (run_trans transmealy q_0 (acc @ is))))))"
    using b by (simp add: run_trans_two_nested)
  finally have calc: "\<forall> acc is ops. orun T (acc @ is) = Some ops \<longrightarrow>
      run_trans transmealy (f acc) is = (f (acc @ is),(drop (length acc) ops))"
    using c by presburger
  have "func_sim M T f"
    unfolding func_sim_def
    apply (simp add: one m)
    using calc by auto
  then show ?thesis
    by auto
qed

lemma max_size_S_aux:
  assumes "func_sim M T f" and
    "sapart (S,F,T)" and
    "finite S"
  shows "card S \<le> card Q"
proof (rule ccontr)
  assume ass: "\<not> card S \<le> card Q"
  then have gt: "card S > card Q"
    by simp
  have "\<forall> s \<in> S. f s \<in> Q"
    by simp
  have "card S \<ge> card (image f S)"
    using assms by (simp add: card_image_le)
  have "\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart T s1 s2"
    using assms by simp
  then have "\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> (f s1) \<noteq> (f s2)"
    by (metis apart_sim assms(1) old.prod.exhaust)
  then have "inj_on f S"
    by (meson inj_onI)
  then show False 
    using ass card_inj_on_le finite_UNIV by blast
qed

lemma max_size_S:
  assumes "invar (S,F,T)"
  shows "card S \<le> card Q"
  text \<open>this shows that \<open>S\<close> also has an upper bound, this not at maximum accuracy,
    as we know @{term "card S"} is smaller than the number of equivalence classes of \<open>m\<close>\<close>
proof -
  have "\<exists> f. func_sim M T f"
    using assms func_sim_of_output_query invars(6) by fastforce
  then obtain f where
    a: "func_sim M T f"
    by auto
  have b: "sapart (S,F,T)"
    using assms invars by presburger
  have c: "finite S"
    using assms invars by blast
  then show ?thesis
    using max_size_S_aux a b c by blast
qed

theorem max_norm_total:
  assumes "invar (S,F,T)"
  shows "norm (S,F,T) \<le> max_norm Q"
  text  \<open>this theorem is weaker then theorem 3.9 in the L sharp Paper, as theorem 3.9 shows is focused on equivalence classes
    while @{term "max_norm Q"} is dependent on the number of states in the mealy machine\<close>
proof (rule ccontr)
  assume "\<not> norm (S,F,T) \<le> max_norm Q"
  then have "max_norm S >max_norm Q"
    using norm_max assms by force
  then have "card S > card Q"
    using assms
    by (metis add_le_cancel_right add_mono div_le_mono linorder_not_le mult_le_mono mult_le_mono1)
  then show False
    using max_size_S assms by fastforce
qed

lemma norm3_subs:
  assumes "F \<subseteq> Fnew" and
    "finite Fnew" and
    "finite S"
  shows "norm3 (S,F,T) \<le> norm3 (S,Fnew,T)"
using assms proof -
  have fin_start: "finite {(q,p). q \<in> S \<and> p \<in> Fnew}"
    using assms by auto
  have "{(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p} \<subseteq> {(q,p). q \<in> S \<and> p \<in> Fnew}"
    by blast
  then have finite: "finite {(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p}"
    using fin_start finite_subset by blast
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<subseteq> {(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p}"
    using assms by blast
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<le>
      card{(q,p). q \<in> S \<and> p \<in> Fnew \<and> apart T q p}"
    using finite card_mono by blast
  then show ?thesis
    by auto
qed


section \<open>algo step\<close>

lemma sapart_extends:
  assumes "sapart (S,F,T)" and
    "\<forall> s \<in> S. apart T s f"
  shows "sapart (S \<union> {f},F2,T)"
proof -
  have a: "\<forall> s1 \<in> S. \<forall> s2 \<in> S. s1 \<noteq> s2 \<longrightarrow> apart T s1 s2"
    using assms by simp
  have b: "\<forall> s1 \<in> S. s1 \<noteq> f \<longrightarrow> apart T f s1"
    using assms by fastforce
  have c: "\<forall> s1 \<in> S. s1 \<noteq> f \<longrightarrow> apart T s1 f"
    using assms by fastforce
  show ?thesis
    using a b c by auto
qed

lemma substr_not_s:
  assumes "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)" and
    "x \<notin> S" and
    "s = x @ y"
  shows "s \<notin> S"
using assms proof (induction y arbitrary: s rule: rev_induct)
  case Nil
  then show ?case
    by simp
next
  case (snoc y ys)
  then have "x @ ys \<notin> S"
    by blast
  then have "x @ ys @ [y] \<notin> S"
    using snoc
    by (metis Nil_is_append_conv append1_eq_conv append_assoc)
  then show ?case
    by (simp add: snoc.prems(3))
qed

lemma substring_in_s:
  assumes "[] \<in> S" and
    "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)" and
    "s \<in> S" and
    "s = x @ y"
  shows "x \<in> S"
    using substr_not_s assms by blast

lemma algo_step_keeps_invar:
  assumes "algo_step (S,F,T) (S',F',T')" and
    "invar (S,F,T)"
  shows "invar (S',F',T')"
  text \<open>this lemma shows that @{const algo_step} keeps the invariant, this proof works over each
    rule and proves each part of the invariant separately.\<close>
using assms proof (induction rule: algo_step.induct)
  case (rule1 f F S T)
  have finS: "finite (S \<union> {f})"
    using rule1 invars by fast
  then have finF: "finite (frontier (S \<union> {f},F,T))"
    using finiteF by presburger
  have a: "\<forall> e. \<not> (e \<in> S \<union> {f} \<and> e \<in> (frontier (S \<union> {f},F,T)))"
    by force
  have b: "\<forall> e \<in> S \<union> {f}. orun T e \<noteq> None"
    using rule1 invars(2,7) by fastforce
  have c: "sapart (S \<union> {f},frontier (S \<union> {f},F,T),T)"
    using rule1 sapart_extends invars by metis
  have d: "\<forall> i. orun T i \<noteq> None \<longrightarrow> orun T i = Some (output_query M i)"
    using rule1 invars by metis
  have e: "frontier (S \<union> {f},F,T) = frontier (S \<union> {f},F,T)"
    by fast
  have f: "[] \<in> S \<union> {f}"
    using rule1 invars by fast
  have "\<exists> i. \<exists> s2 \<in> S. s2 \<in> S \<and> s2 @ [i] = f"
    using rule1 invars(7,9) by fastforce
  then have g: "\<forall> s \<in> S \<union> {f}. s = [] \<or> (\<exists> s2 \<in> S \<union> {f}. \<exists> i. s2 @ [i] = s)"
    using rule1 invars(9) by blast
  show ?case
    using finF finS a b c d e f g is_invar[of "S \<union> {f}" "frontier (S \<union> {f},F,T)" T] by auto
next
  case (rule2 s S T i out F)
  have finiteS: "finite S"
    using rule2 invars by blast
  have finiteF: "finite (F \<union> {s @ [i]})"
    using rule2 invars by blast
  have lens: "length (s @ [i]) = length out"
    using rule2 output_query_length by blast
  have a: "\<forall> e. \<not> (e \<in> S \<and> e \<in> (F \<union> {s @ [i]}))"
    using rule2 invars by blast
  have orunS: "\<forall> e \<in> S. orun T e \<noteq> None"
    using rule2 by (metis invars(2))
  then have b: "\<forall> e \<in> S. orun (process_output_query T (s @ [i]) out) e \<noteq> None"
    using lens output_query_retains_some_output by metis
  have c: "sapart (S,(F \<union> {s @ [i]}),process_output_query T (s @ [i]) out)"
    using lens rule2 proc_output_query_retains_sapart invars by (metis sapart.simps)
  have "\<forall> k y. orun T k = Some y \<longrightarrow> output_query M k = y"
    using rule2 by (metis invars(6) option.discI option.inject)
  then have d: "\<forall> j. orun (process_output_query T (s @ [i]) out) j \<noteq> None \<longrightarrow>
      orun (process_output_query T (s @ [i]) out) j = Some (output_query M j)"
    using rule2 output_query_keeps_invar[of T "s @ [i]" "s @ [i]" out]
    by (smt (verit) invars lens orun.elims output_query_keeps_invar output_query_retains_some_specific)
  have e_fst: "\<forall> f \<in> frontier (S,F,T). f \<in> frontier (S,F,(process_output_query T (s @ [i]) out))" apply simp
    using rule2 invars(1,7)
    by (metis not_Some_eq output_query_length output_query_retains_some_output)
  have e_snd: "(s @ [i]) \<in> frontier (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out))" apply simp
    using rule2 orunS process_op_query_not_none_output lens by (metis d otree.exhaust)
  have e_aux: "\<forall> f \<in> F \<union> {s @ [i]}. f \<in> frontier (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out))"
    using e_fst e_snd rule2 invars(7) by force
  have s_not_none: "orun T s \<noteq> None"
    using orunS rule2 by blast
  then have subs_s_not_None: "\<forall> is. \<exists> y. is @ y = s \<longrightarrow> orun T is \<noteq> None"
    using orun_substring_not_none by fast
  then have something: "\<forall> is. (\<exists> y. is @ y = s @ [i]) \<and> \<not> (\<exists> y. is @ y = s) \<longrightarrow> is = s @ [i]"
    by (metis append_self_conv butlast_append butlast_snoc)
  have "\<forall> is. orun T is = None \<and> orun (process_output_query T (s @ [i]) out) is \<noteq> None \<longrightarrow> (\<exists> y. is @ y = (s @ [i]))"
    using substring_different_query lens by metis
  then have only_si_different: "\<forall> is. orun T is = None \<and> orun (process_output_query T (s @ [i]) out) is \<noteq> None \<longrightarrow> is = (s @ [i])"
    using subs_s_not_None something by (metis orun_substring_not_none s_not_none)
  have finF: "\<forall> f. f \<in> frontier (S,F,T) \<longrightarrow> f \<in> F"
    using rule2 invars by fast
  then have supsF: "frontier (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) \<supseteq> frontier (S,F,T) \<union> {s @ [i]}"
    by (smt (verit) Un_iff e_aux mem_Collect_eq subsetI)
  have "\<forall> f. f \<in> frontier (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) \<longrightarrow> f \<in> frontier (S,F \<union> {s @ [i]},T) \<or> f = (s @ [i])" apply simp
    using only_si_different by fastforce
  then have "\<forall> f. f \<in> frontier (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) \<longrightarrow> f \<in> (F \<union> {s @ [i]})"
    using finF by auto
  then have subsF: "frontier (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) \<subseteq> (F \<union> {s @ [i]})"
    by blast
  then have e: "frontier (S,F \<union> {s @ [i]},(process_output_query T (s @ [i]) out)) = (F \<union> {s @ [i]})"
    using supsF rule2 invars(7) by fast
  have f: "[] \<in> S"
    using rule2 invars by fast
  have g: "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
    using rule2 invars by metis
  show ?case
    using a b finiteF finiteS c d e f g is_invar by presburger
next
  case (rule3 s1 S s2 f F T w out)
  have lens: "length (f @ w) = length out"
    using rule3 output_query_length by blast
  have finS: "finite S"
    using rule3 invars by blast
  have finF: "finite F"
    using rule3 invars by fast

  have a: "\<forall> e. \<not> (e \<in> S \<and> e \<in> F)"
    using rule3 by (meson invars)
  have b: "\<forall> e \<in> S. orun (process_output_query T (f @ w) out) e \<noteq> None"
    using rule3 by (metis invars(2) lens output_query_retains_some_output)

  have c: "sapart (S,F,process_output_query T (f @ w) out)"
    using lens rule3 proc_output_query_retains_sapart invars by metis
  have helper: "\<forall> k y. orun T k = Some y \<longrightarrow> output_query M k = y"
    using rule3 by (metis invars(6) option.discI option.inject)
  then have d: "\<forall> j. orun (process_output_query T (f @ w) out) j \<noteq> None \<longrightarrow>
      orun (process_output_query T (f @ w) out) j = Some (output_query M j)"
    using rule3 output_query_keeps_invar
    by (smt (verit,del_insts) invars lens orun.elims output_query_retains_some_specific)

  have "\<forall> fs \<in> frontier (S,F,T). fs \<in> frontier (S,F,(process_output_query T (f @ w) out))"
    apply simp
    using rule3 invars(1,7)
    by (metis not_Some_eq output_query_length output_query_retains_some_output)
  then have subsF: "F \<subseteq> frontier (S,F,(process_output_query T (f @ w) out))"
    using invars(7) rule3 by fast
  have "\<forall> fs. fs \<in> frontier (S,F,T) \<longrightarrow> fs \<in> F"
    using invars(7) rule3.prems(1) by auto
  have notnone_subs: "\<forall> s \<in> S. \<forall> i. orun T (s @ [i]) = None \<and> orun (process_output_query T (f @ w) out) (s @ [i]) \<noteq> None \<longrightarrow> (\<exists> y. (s @ [i] @ y = (f @ w)))"
    using substring_different_query[of T _ "f @ w" out] lens by (metis append_assoc)
  have fy_not_s: "\<forall> y. f @ y \<notin> S"
    using a invars(9) rule3.hyps(4) rule3.prems(1) by (meson substr_not_s)
  then have ins_subs_f: "\<forall> s \<in> S.(\<exists> y. s @ y = f @ w) \<longrightarrow> (\<exists> y. s @ y = f)"
    by (metis append_eq_append_conv2)
  then have "\<forall> s \<in> S. \<forall> i. \<exists> y. s @ [i] @ y = f @ w \<longrightarrow> run T (s @ [i]) \<noteq> None"
    by (metis append_assoc append_self_conv2 list.distinct(1))
  have "\<forall> s \<in> S. \<forall> i. orun T (s @ [i]) = None \<longrightarrow> s @ [i] \<noteq> f"
    using rule3 invars(7) by fastforce
  then have "\<forall> s \<in> S. \<forall> i. orun T (s @ [i]) = None \<longrightarrow> (\<nexists> y. s @ [i] @ y = f)"
    by (metis (mono_tags,lifting) append.assoc frontier.simps invars(7) mem_Collect_eq orun_substring_not_none rule3.hyps(4) rule3.prems)
  then have "\<forall> s \<in> S. \<forall> i. orun T (s @ [i]) = None \<and> orun (process_output_query T (f @ w) out) (s @ [i]) \<noteq> None \<longrightarrow>
      \<not> (\<exists> y. s @ [i] @ y = f @ w)"
    using rule3
    by (metis (no_types,opaque_lifting) append_Cons append_eq_append_conv2 fy_not_s ins_subs_f list.inject neq_Nil_conv same_append_eq)
  then have "\<forall> s \<in> S. \<forall> i. orun T (s @ [i]) = None \<longrightarrow> orun (process_output_query T (f @ w) out) (s @ [i]) = None"
    using notnone_subs by blast
  then have "\<forall> fs. fs \<in> frontier (S,F,(process_output_query T (f @ w) out)) \<longrightarrow> fs \<in> frontier (S,F,T)"
    by fastforce
  then have "\<forall> fs. fs \<in> frontier (S,F,(process_output_query T (f @ w) out)) \<longrightarrow> fs \<in> F"
    using rule3 invars(7) by blast
  then have "F \<supseteq> frontier (S,F,(process_output_query T (f @ w) out))"
    by blast
  then have e: "F = frontier (S,F,(process_output_query T (f @ w) out))"
    using subsF by blast
  have ins: "[] \<in> S"
    using rule3 invars by fast
  have f: "\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)"
    using rule3 invars by metis
  show ?case
    using a b finS finF c d e f ins is_invar[of S F "process_output_query T (f @ w) out"] by blast
next
  case (rule4 S T F fs s inp outs outf)
  have lens: "length (s @ inp) = length outs"
    using rule4 output_query_length by blast
  have lenf: "length (fs @ inp) = length outf"
    using rule4 output_query_length by blast
  have a: "\<forall> e. \<not> (e \<in> S \<and> e \<in> frontier (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)))"
    by force
  have b: "\<forall> e \<in> S. orun (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) e \<noteq> None"
    using rule4
    by (metis lenf lens orun_substring_not_none output_query_retains_some_output)
  have c: "sapart (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf))"
    using lens lenf rule4 proc_output_query_retains_sapart invars by metis
  have "\<forall> k y. orun T k = Some y \<longrightarrow> output_query M k = y"
    using rule4 by (metis invars(6) option.discI option.inject)
  then have "\<forall> j. orun (process_output_query T (s @ inp) outs) j \<noteq> None \<longrightarrow>
      orun (process_output_query T (s @ inp) outs) j = Some (output_query M j)"
    using rule4 output_query_keeps_invar
    by (smt (verit,del_insts) invars lens orun.elims output_query_retains_some_specific)
  then have d: "\<forall> j. orun (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) j \<noteq> None \<longrightarrow>
      orun (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) j = Some (output_query M j)"
    using rule4 output_query_keeps_invar[of "process_output_query T (s @ inp) outs" _"fs @ inp" "outf"]
    by (smt (verit) lenf option.discI option.inject orun.elims
    output_query_retains_some_specific process_output_query.simps(1))
  have never_none: "\<forall> ses \<in> S. \<forall> i. orun T (ses @ [i]) \<noteq> None"
    using rule4 by blast
  have feq: "F = frontier (S,F,T)"
    using rule4 invars(7) by blast
  have inf_eq: "frontier (S,F,T) = {f. ((\<exists> s \<in> S. \<exists> i. f = s @ [i]) \<and> f \<notin> S)}"
    using never_none by auto
  have "\<forall> ses \<in> S. \<forall> i. orun (process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf) (ses @ [i]) \<noteq> None"
    using never_none output_query_retains_some_output lenf lens by blast
  then have infnew_eq: "{f. ((\<exists> s \<in> S. \<exists> i. f = s @ [i]) \<and> f \<notin> S)} =
      frontier (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf))"
    by auto
  then have e: "F = frontier (S,F,(process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf))"
    using feq inf_eq by auto
  then show ?case
    using rule4 a b c d e is_invar
    by (simp add: invars(3,4,8,9))
qed

theorem algo_step_increases_norm:
  assumes "algo_step (S,F,T) (S',F',T')" and
    "invar (S,F,T)"
  shows "norm (S,F,T) < norm (S',F',T')"
  text \<open>this theorem is equivalent to Theorem 3.8 in the original L sharp Paper
    for each rule this proof is divided into three parts, for two of the norms it shows that they are not smaller
for one that it is bigger, this is similar to the proof of the original Paper.
  since we argue about cardinalities we work a lot with @{thm [source] card_mono}\<close>
using assms proof (induction "(S,F,T)" "(S',F',T')" rule: algo_step.induct)
  case (rule1 f)
  have finS: "finite S"
    using rule1 invars by blast
  have finI: "finite I"
    by fastforce
  have finF: "finite F"
    using rule1 invars by fast
  have "norm1 (S,F,T) \<le> norm1 (S \<union> {f},(frontier (S \<union> {f},F,T)),T)"
    by (simp add: add_mono card_insert_le div_le_mono mult_le_mono)
  have "f \<notin> S"
    using rule1 invars by metis
  then have "norm1 (S,F,T) + (card S + 1) \<le> norm1 (S \<union> {f},(frontier (S \<union> {f},F,T)),T)"
    using finS by auto
  then have fst: "norm1 (S,F,T) + (card S + 1) \<le> norm1 (S',F',T')"
    using rule1 by argo

  have finp: "finite ({q. q \<in> S \<union> {f}} \<times> {i. i \<in> I})"
    using finS finI by simp
  have "{(q,i). q \<in> S \<union> {f} \<and> i \<in> I} = {q. q \<in> S \<union> {f}} \<times> {i. i \<in> I}"
    using finS finI by fast
  then have finp2: "finite {(q,i). q \<in> S \<union> {f} \<and> i \<in> I}"
    using finp by argo
  have "{(q,i). (q = f \<or> q \<in> S) \<and> (\<exists> a b. orun T (q @ [i]) = Some b)} \<subseteq>
      {(q,i). q \<in> S \<union> {f} \<and> i \<in> I}"
    using univI by auto
  then have fin2: "finite {(q,i). (q = f \<or> q \<in> S) \<and> (\<exists> a b. orun T (q @ [i]) = Some b)}"
    using finp2 finite_subset by fast
  have "{(q,i). q \<in> S \<and> (\<exists> b. orun T (q @ [i]) = Some b)} \<subseteq>
      {(q,i). (q = f \<or> q \<in> S) \<and> (\<exists> b. orun T (q @ [i]) = Some b)}"
    by blast
  then have "norm2 (S,F,T) \<le> norm2 (S \<union> {f},(frontier (S \<union> {f},F,T)),T)"
    using fin2 card_mono by fastforce
  then have snd: "norm2 (S,F,T) \<le> norm2 (S',F',T')"
    using rule1 by fast

  have finSF: "finite {(q,p). (q \<in> S \<or> q = f) \<and> p \<in> F}"
    using finS finF by simp
  have "{(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p} \<subseteq>
      {(q,p). (q \<in> S \<or> q = f) \<and> p \<in> F}"
    by blast
  then have fin3: "finite {(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p}"
    using finSF finite_subset by fast
  have "{(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p} \<supseteq>
      {(q,p). (q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p}"
    by blast
  also have c1: "\<dots> \<supseteq> {(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - {(p,q). p \<in> S \<and> q = f}"
    by auto
  have s_cross_eq: "{(p,q). p \<in> S \<and> q = f} = (S \<times> {f})"
    using rule1 by blast
  then have "card (S \<times> {f}) = card S * card {f}"
    using card_cartesian_product by fast
  then have "card (S \<times> {f}) = card S"
    by force
  then have card_eq: "card {(p,q). p \<in> S \<and> q = f} = card S"
    using rule1 s_cross_eq by argo
  have "\<forall> fs \<in> F. f \<noteq> fs \<longrightarrow> fs \<in> (frontier (S,F,T))"
    using rule1 invars(7) by blast
  then have "\<forall> fs \<in> F. f \<noteq> fs \<longrightarrow> fs \<in> (frontier (S \<union> {f},F,T))"
    by fastforce
  then have fminus_subs: "F - {f} \<subseteq> (frontier (S \<union> {f},F,T))"
    by fast
  have "(S \<times> {f}) = {(p,q). p \<in> S \<and> q = f}"
    by simp
  then have "finite {(p,q). p \<in> S \<and> q = f}"
    using finS by simp
  then have le1: "card {(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - card {(p,q). p \<in> S \<and> q = f}
      \<le> card ({(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - {(p,q). p \<in> S \<and> q = f})"
    using diff_card_le_card_Diff by blast
  have le2: "card ({(q,p). (q \<in> S) \<and> p \<in> F \<and> apart T q p} - {(p,q). p \<in> S \<and> q = f}) \<le>
      card ({(q,p). (q = f \<or> q \<in> S) \<and> p \<in> F \<and> p \<noteq> f \<and> apart T q p})"
    using calculation fin3 card_mono c1 by meson
  have "norm3 (S \<union> {f},F - {f},T) \<ge> card {(q,p). (q \<in> S) \<and> p \<in> F \<and>
      apart T q p} - card {(p,q). p \<in> S \<and> q = f}"
    using le1 le2 by simp
  then have "norm3 (S \<union> {f},F - {f},T) \<ge> norm3 (S,F,T) - card {(p,q). p \<in> S \<and> q = f}"
    by simp
  then have "norm3 (S \<union> {f},F - {f},T) \<ge> norm3 (S,F,T) - card S"
    using rule1 card_eq by argo
  then have "norm3 (S \<union> {f},(frontier (S \<union> {f},F,T)),T) \<ge> norm3 (S,F,T) - card S"
    using norm3_subs fminus_subs
    by (smt (verit) dual_order.trans finS finite.emptyI finite.insertI finiteF infinite_Un)
  then have trd: "norm3 (S,F,T) - card S \<le> norm3 (S',F',T')"
    using rule1 by fast

  then show ?case
    using fst snd trd by simp
next
  case (rule2 s i out)
  have finS: "finite S"
    using rule2 invars by blast
  have finS': "finite S'"
    using rule2 invars by blast
  have finI: "finite I"
    by fastforce
  have finF: "finite F"
    using rule2 invars by blast
  then have finF': "finite F'"
    using rule2 by blast
  have fst: "norm1 (S,F,T) = norm1 (S',F',T')"
    apply simp
    using rule2(4)
    by fastforce

  have lens: "length (s @ [i]) = length out"
    using output_query_length rule2.hyps(3)
    by blast
  then have a: "orun T' (s @ [i]) \<noteq> None"
    using process_op_query_not_none_output rule2 by (metis otree.exhaust)
  have retain: "\<forall> is. orun T is \<noteq> None \<longrightarrow> orun T' is \<noteq> None"
    using rule2 lens output_query_retains_some_output by blast
  have "{q \<in> S. \<forall> i. \<exists> a b. q \<noteq> s \<and> run T' (q @ [i]) = Some (a,b)} \<subseteq> S"
    by force
  have finp: "finite ({q. q \<in> S} \<times> {i. i \<in> I})"
    using finS finI by simp
  have "{(q,i). q \<in> S \<and> i \<in> I} = {q. q \<in> S} \<times> {i. i \<in> I}"
    using finS finI by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp by argo
  have "{(q,i'). \<not> (q = s \<and> i' = i) \<and> (q \<in> S) \<and> (\<exists> b. orun T' (q @ [i']) = Some b)} \<subseteq>
      {(q,i). q \<in> S \<and> i \<in> I}"
    using univI by auto
  then have fin2: "finite {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)}"
    using finp2 finite_subset by fast
  have "{(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T (q @ [i']) = Some b)} \<subseteq>
      {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)}"
    using retain by auto
  then have lep: "card {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T (q @ [i']) = Some b)} \<le>
      card {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)}"
    using card_mono fin2 by fastforce
  have "{(q,i'). q = s \<and> i' = i \<and> (\<exists> b. orun T (q @ [i']) = Some b)} = {}"
    using rule2 by (smt (verit) all_not_in_conv case_prodE mem_Collect_eq not_None_eq)
  then have same: "{(q,i). q \<in> S \<and> (\<exists> b. orun T (q @ [i]) = Some b)} =
      {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T (q @ [i']) = Some b)}"
    by auto
  have nin: "(s,i) \<notin> {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)}"
    by blast
  have "{(q,i'). (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)} = {(s,i)}"
    using a rule2 by fast
  then have union: "{(q,i'). q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)} =
      {(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)} \<union> {(s,i)}"
    by force
  then have gt: "card ({(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)} \<union> {(s,i)}) =
      card ({(q,i'). \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)}) + 1"
    using fin2 nin by simp
  have "card {(q,i'). q \<in> S \<and> (\<exists> b. orun T (q @ [i']) = Some b)} \<le> card {(q,i').
      \<not> (q = s \<and> i' = i) \<and> q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)}"
    using lep same by argo
  then have "card {(q,i'). q \<in> S \<and> (\<exists> b. orun T (q @ [i']) = Some b)} <
      card {(q,i'). q \<in> S \<and> (\<exists> b. orun T' (q @ [i']) = Some b)}"
    using gt union by presburger
  then have "norm2 (S,F,T) < norm2 (S,F',T')"
    by simp
  then have snd: "norm2 (S,F,T) < norm2 (S',F',T')"
    using rule2(4) by simp

  have fincross: "finite (S' \<times> F')"
    using finS' finF' by simp
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (orun T' (q @ i) = Some x) \<and>
      (\<exists> y. orun T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (orun T' (q @ i) =
      Some x) \<and> (\<exists> y. orun T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))}"
    using fincross by (simp add: finite_subset)
  obtain r where
    lr: "T = Node r"
    using otree.exhaust by auto
  have front: "\<forall> p x i2. orun (Node r) (p @ i2) = Some x \<longrightarrow>
      orun (process_output_query (Node r) (s @ [i]) out) (p @ i2) = Some x"
    using rule2(6) lens output_query_retains_some_specific[of "s @ [i]" out r] by presburger
  have one: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (orun T' (q @ i) = Some x) \<and>
        (\<exists> y. orun T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<supseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (orun T (q @ i) = Some x) \<and>
        (\<exists> y. orun T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))}"
    using rule2(6) lens front lr by blast
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> (\<exists> i x. (orun T (q @ i) = Some x) \<and>
        (\<exists> y. orun T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<subseteq>
      {(q,p). q \<in> S \<and> p \<in> F \<union> {s @ [i]} \<and> (\<exists> i x. (orun T (q @ i) = Some x) \<and>
        (\<exists> y. orun T (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))}"
    by force
  then have subs3: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (\<exists> i x. (orun T' (q @ i) = Some x) \<and>
        (\<exists> y. orun T' (p @ i) = Some y \<and> drop (length q) x \<noteq> drop (length p) y))} \<supseteq>
      {(q,p). q \<in> S \<and> p \<in> F \<and> (\<exists> i x. (orun T (q @ i) = Some x) \<and> (\<exists> y. orun T (p @ i) = Some y \<and>
          drop (length q) x \<noteq> drop (length p) y))}"
    using one rule2 by blast
  then have trd: "norm3 (S,F,T) \<le> norm3 (S',F',T')"
    using fin3 card_mono by fastforce

  then show ?case
    using fst snd trd by simp
next
  case (rule3 s1 s2 f w out)
  have fst: "norm1 (S,F,T) = norm1 (S',F',T')"
    using rule3(9) by fastforce

  have lens: "length (f @ w) = length out"
    using output_query_length rule3 by blast
  have retain: "\<forall> is. orun T is \<noteq> None \<longrightarrow> orun T' is \<noteq> None"
    using rule3 lens output_query_retains_some_output by blast
  then have retain_specific: "\<forall> is x. orun T is = Some x \<longrightarrow> orun T' is = Some x"
    using output_query_retains_some_specific rule3 lens
    by (smt (verit) not_none_not_both_apart orun.elims)
  have "finite S"
    using rule3(12) invars by blast
  then have finp: "finite (S \<times> I)"
    using univI by simp

  have "{(q,i). q \<in> S \<and> i \<in> I} = S \<times> I"
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp by argo
  have "{(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)} \<subseteq> {(q,i). q \<in> S \<and> i \<in> I}"
    using rule3 univI by fast
  then have fin2: "finite {(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)}"
    using finp2 finite_subset by fast
  have "{(q,i). q \<in> S \<and> (\<exists> y. orun T (q @ [i]) = Some y)} \<subseteq>
      {(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)}"
    using retain rule3 by fast
  then have "card {(q,i). q \<in> S \<and> (\<exists> y. orun T (q @ [i]) = Some y)} \<le>
      card {(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)}"
    using fin2 card_mono by auto
  then have snd: "norm2 (S,F,T) \<le> norm2 (S',F',T')"
    by auto

  have fincross: "finite (S' \<times> F')"
    using rule3 by (meson finite_SigmaI invars)
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p}"
    using fincross finite_subset by fast
  then have split: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} =
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}
      \<union> {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    using rule3 by fast
  then have fin3_subs: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    using fin3 finite_subset by simp
  obtain z where
    z: "orun T' (f @ w) = Some z"
    using rule3 lens by (metis not_None_eq otree.exhaust process_op_query_not_none_output)
  have "apart_witness T' s1 s2 w"
    using retain_specific rule3(7) by auto
  then have apart_or: "apart T' s1 f \<or> apart T' s2 f"
    using not_none_not_both_apart rule3 z by (metis apart.simps)
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p} \<inter>
      {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p} = {}"
    by blast
  then have card_splitup: "card {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} =
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p} +
      card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p})"
    using split fin3 card_Un_disjoint by fastforce
  have fin_subs_part: "finite {(q,p). ((q = s2 \<or> q = s1) \<and> p = f)}"
    by simp
  have "{(q,p). ((q = s2 \<or> q = s1) \<and> p = f)} \<supseteq> {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    by fast
  then have fin_part_three: "finite {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    using fin_subs_part finite_subset by fast
  have union: "{(q,p). ((q = s2) \<and> p = f) \<and> apart T' q p} \<union> {(q,p). ((q = s1) \<and> p = f) \<and> apart T' q p} =
      {(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}"
    by fast
  have "({(q,p). ((q = s2) \<and> p = f) \<and> apart T' q p} = {(s2,f)}) \<or>
      ({(q,p). ((q = s1) \<and> p = f) \<and> apart T' q p} = {(s1,f)})"
    using apart_or by force
  then have "(card {(q,p). ((q = s2) \<and> p = f) \<and> apart T' q p} = 1) \<or> (card {(q,p). ((q = s1) \<and> p = f) \<and>
      apart T' q p} = 1)"
    by force
  then have card_not_zero: "card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p}) \<ge> 1"
    using union by (metis (no_types,lifting) Un_upper1 Un_upper2 card_mono fin_part_three)
  have equal_first_half: "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T q p} = {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p}"
    using rule3(5,6) by auto
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T q p} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    apply simp
    using retain_specific rule3 by blast
  then have "{(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    using equal_first_half by argo
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} \<le>
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p}"
    using fin3_subs card_mono by meson
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> apart T q p} <
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s1 \<or> q = s2) \<and> p = f) \<and> apart T' q p} +
      card ({(q,p). ((q = s2 \<or> q = s1) \<and> p = f) \<and> apart T' q p})"
    using card_not_zero by simp
  then have trd: "norm3 (S,F,T) < norm3 (S',F',T')"
    using card_splitup by auto

  show ?case
    using fst snd trd by fastforce
next
  case (rule4 fs s inp outs outf)
  then have fst: "norm1 (S,F,T) = norm1 (S',F',T')"
    using rule4(8,9) by auto

  have lens: "length (s @ inp) = length outs"
    using output_query_length rule4 by blast
  have lenf: "length (fs @ inp) = length outf"
    using output_query_length rule4 by blast
  have retain: "\<forall> is. orun T is \<noteq> None \<longrightarrow> orun T' is \<noteq> None"
    using rule4 lens lenf output_query_retains_some_output by blast
  then have retain_specific: "\<forall> is x. orun T is = Some x \<longrightarrow> orun T' is = Some x"
    using rule4 lens lenf by (metis algo_step_keeps_invar assms(1) invars(6) option.distinct(1))
  have finp: "finite ({q. q \<in> S} \<times> {i. i \<in> I})"
    using rule4 by (metis Collect_mem_eq finite_SigmaI finite_code invars(3))
  have "{(q,i). q \<in> S \<and> i \<in> I} = {q. q \<in> S} \<times> {i. i \<in> I}"
    by fast
  then have finp2: "finite {(q,i). q \<in> S \<and> i \<in> I}"
    using finp by argo
  have "{(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)} \<subseteq> {(q,i). q \<in> S \<and> i \<in> I}"
    using rule4 univI by blast
  then have fin2: "finite {(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)}"
    using finp2 finite_subset by fast
  have "{(q,i). q \<in> S \<and> (\<exists> y. orun T (q @ [i]) = Some y)} \<subseteq>
      {(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)}"
    using retain rule4 by fast
  then have "card {(q,i). q \<in> S \<and> (\<exists> y. orun T (q @ [i]) = Some y)} \<le>
      card {(q,i). q \<in> S' \<and> (\<exists> y. orun T' (q @ [i]) = Some y)}"
    using fin2 card_mono by auto
  then have snd: "norm2 (S,F,T) \<le> norm2 (S',F',T')"
    by auto

  have invar: "invar (S',F',T')"
    using rule4 algo_step_keeps_invar algo_step.rule4 by metis
  have "\<exists> x. orun T' (s @ inp) = Some x"
    by (metis lenf lens not_Some_eq otree.exhaust
      output_query_retains_some_output process_op_query_not_none_output rule4.hyps(11))
  then obtain new_outs where
    new_outs: "orun T' (s @ inp) = Some new_outs"
    by fast
  have "\<exists> y. orun T' (fs @ inp) = Some y"
    using process_op_query_not_none_output by (metis lenf not_Some_eq otree.exhaust rule4.hyps(11))
  then obtain new_outf where
    new_outf: "orun T' (fs @ inp) = Some new_outf"
    by fast
  have query_s: "new_outs = (output_query M (s @ inp))"
    using invar new_outs invars(6) by fastforce
  have query_fs: "new_outf = (output_query M (fs @ inp))"
    using invar new_outf invars by (metis not_None_eq option.inject)
  have "drop (length s) (output_query M (s @ inp)) \<noteq>
      drop (length fs) (output_query M (fs @ inp))"
    using rule4 diff_query_def by (metis output_query.elims output_query.simps)
  then have "drop (length s) new_outs \<noteq> drop (length fs) new_outf"
    using rule4 query_s query_fs by argo
  then have apart_s_fs: "apart T' s fs"
    using new_outs new_outf by auto
  have fincross: "finite (S' \<times> F')"
    using rule4 invars(3) invars(4) by blast
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p} \<subseteq> (S' \<times> F')"
    by blast
  then have fin3: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> apart T' q p}"
    using fincross finite_subset by fast
  have one_elem: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart T' q p} = {(s,fs)}"
    using apart_s_fs rule4 by fast
  have union: "{(q,p). q \<in> S' \<and> p \<in> F' \<and> (apart T' q p)} =
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} \<union>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart T' q p}"
    by fast
  then have finite_subs: "finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} \<and>
      finite {(q,p). q \<in> S' \<and> p \<in> F' \<and> (q = s \<and> p = fs) \<and> apart T' q p}"
    using fin3 by simp
  have "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> ((q = s) \<and> p = fs) \<and> apart T' q p} \<inter> {(s,fs)} = {}"
    by blast
  then have card_splitup: "card {(q,p). q \<in> S' \<and> p \<in> F' \<and> (apart T' q p)} =
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} +
      card {(s,fs)}"
    using fin3 union one_elem finite_subs card_Un_disjoint[of "{(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p}" "{(s,fs)}"]
    by argo
  have removed: "{(q,p). q \<in> S \<and> p \<in> F \<and> (apart T q p)} =
      {(q,p). q \<in> S \<and> p \<in> F \<and> \<not> (q = s \<and> p = fs) \<and> (apart T q p)}"
    using rule4 by fast
  have "{(q,p). q \<in> S \<and> p \<in> F \<and> \<not> (q = s \<and> p = fs) \<and> (apart T q p)} \<subseteq>
      {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p}"
    using retain_specific rule4
    by (smt (verit,ccfv_SIG) Pair_inject apart.simps case_prodE case_prodI2 mem_Collect_eq subsetI)
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> (apart T q p)} \<le>
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p}"
    using fin3 card_mono removed finite_subs by force
  then have "card {(q,p). q \<in> S \<and> p \<in> F \<and> (apart T q p)} <
      card {(q,p). q \<in> S' \<and> p \<in> F' \<and> \<not> (q = s \<and> p = fs) \<and> apart T' q p} + card {(s,fs)}"
    by simp
  then have trd: "norm3 (S,F,T) < norm3 (S',F',T')"
    using card_splitup by simp

  show ?case
    using fst snd trd by simp
qed

theorem norm_max_no_step:
  assumes "norm (S,F,T) \<ge> max_norm Q" and
    "invar (S,F,T)"
  shows "\<nexists> S' F' T'. algo_step (S,F,T) (S',F',T')"
proof (rule ccontr)
  assume "\<not> (\<nexists> S' F' T'. algo_step (S,F,T) (S',F',T'))"
  then obtain S' F' T' where
    S': "algo_step (S,F,T) (S',F',T')"
    by fast
  have a: "norm (S',F',T') > max_norm Q"
    using algo_step_increases_norm[OF S' assms(2)] assms(1) by linarith
  have inv: "invar (S',F',T')"
    by (rule algo_step_keeps_invar[OF S' assms(2)])
  then have "norm (S',F',T') \<le> max_norm S'"
    by(rule norm_max)
  then have "max_norm S' >max_norm Q"
    using a by linarith
  then show False
    using a max_norm_total[OF inv] by linarith
qed

lemma no_step_rule1:
  assumes "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))"
  shows "\<not> (\<exists> f \<in> F. \<forall> s \<in> S. apart T s f)"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> f \<in> F. \<forall> s \<in> S. apart T s f)"
  then obtain f where
    "f \<in> F \<and> (\<forall> s \<in> S. apart T s f)"
    by blast
  then have "algo_step (S,F,T) (S \<union> {f},frontier (S \<union> {f},F,T),T)"
    using rule1 ass by blast
  then show False
    using assms by simp
qed

lemma no_step_rule2:
  assumes "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))"
  shows "\<not> (\<exists> s i. s \<in> S \<and> (orun T (s @ [i]) = None))"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> s i. s \<in> S \<and> (orun T (s @ [i]) = None))"
  then obtain s i where
    si: "s \<in> S \<and> (orun T (s @ [i]) = None)"
    by blast
  then obtain out where
    out: "output_query M (s @ [i]) = out"
    by presburger
  then have "algo_step (S,F,T) (S,F \<union> {s @ [i]},process_output_query T (s @ [i]) out)"
    using rule2 si out by blast
  then show False
    using assms by simp
qed

lemma no_step_rule3:
  assumes "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))" and
    "invar (S,F,T)"
  shows "\<not> (\<exists> s1 s2 f. s1 \<in> S \<and> s2 \<in> S \<and> f \<in> F \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2)"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> s1 s2 f. s1 \<in> S \<and> s2 \<in> S \<and> f \<in> F \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2)"
  then obtain s1 s2 f where
    ss: "s1 \<in> S \<and> s2 \<in> S \<and> f \<in> F \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2"
    by blast
  have "sapart (S,F,T)"
    using assms invars by presburger
  then have "apart T s1 s2"
    using assms ss by (meson ass exsist_witness rule3 sapart.simps)
  then obtain w where
    w: "apart_witness T s1 s2 w"
    using assms exsist_witness by blast
  obtain out where
    out: "output_query M (f @ w) = out"
    by simp
  then have "algo_step (S,F,T) (S,F,process_output_query T (f @ w) out)"
    using rule3 ss out w by blast
  then show False
    using assms by simp
qed

lemma no_step_rule4:
  assumes "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))" and
    "invar (S,F,T)"
  shows "\<not> (\<exists> s fs inp. fs \<in> F \<and>
      s \<in> S \<and>
      \<not> apart T s fs \<and>
      diff_query M s fs = Some inp)"
proof (rule ccontr)
  assume ass: "\<not> \<not> (\<exists> s fs inp. fs \<in> F \<and>
      s \<in> S \<and>
      \<not> apart T s fs \<and>
      diff_query M s fs = Some inp)"
  then obtain s fs inp where
    ss: "fs \<in> F \<and>
        s \<in> S \<and>
        \<not> apart T s fs \<and>
        diff_query M s fs = Some inp"
    by blast
  have si_not_none: "\<forall> s1 \<in> S. \<forall> i. orun T (s1 @ [i]) \<noteq> None"
    using no_step_rule2 assms by metis
  have "~ (\<exists> f \<in> F. isolated T S f)"
    apply (simp only: isolated.simps)
    using no_step_rule1 assms by blast
  then have notiso: "\<forall> f \<in> F. \<not> isolated T S f"
    by blast
  obtain outf where
    outf: "outf = output_query M (fs @ inp)"
    by simp
  obtain outs where
    outs: "outs = output_query M (s @ inp)"
    by simp
  then have "algo_step (S,F,T) (S,F,process_output_query (process_output_query T (s @ inp) outs) (fs @ inp) outf)"
    using rule4[of S T F fs s inp outs outf] ss outs outf notiso si_not_none by blast
  then show False
    using assms by simp
qed

theorem no_step_exists_hypothesis:
  assumes "invar (S,F,T)" and
    "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))"
  shows "\<exists> t. hypothesis (S,F,T) t"
    using assms no_step_rule1 no_step_rule2 exists_hypothesis
    by auto

lemma not_apart_machines_snd_f:
  assumes "\<not> (apart_machines f notapartq f q)"
  shows "snd (f (notapartq,i)) = snd (f (q,i))"
proof (rule ccontr)
  assume ass: "\<not> snd (f (notapartq,i)) = snd (f (q,i))"
  have "orun_trans f notapartq [i] \<noteq> orun_trans f q [i]"
    using ass by (metis eq_snd_iff orun_trans_Cons split_orun_trans_rev)
  then have "apart_machines f notapartq f q"
    by (meson apart_machines.elims(3))
  then show False
    using assms by blast
qed

lemma apart_machines_propagates_function:
  assumes "\<not> (apart_machines f notapartq t q)"
  shows "\<not> apart_machines f (fst (f (notapartq,i))) t (fst (t (q,i)))"
proof (rule ccontr)
  assume ass: "\<not> \<not> apart_machines f (fst (f (notapartq,i))) t (fst (t (q,i)))"
  then have "\<exists> j. orun_trans f (fst (f (notapartq,i))) j \<noteq> orun_trans t (fst (t (q,i))) j"
    by simp
  then obtain j where
    "orun_trans f (fst (f (notapartq,i))) j \<noteq> orun_trans t (fst (t (q,i))) j"
    by blast
  then have "(let (st,op) = f (notapartq,i) in (let x = orun_trans f st j in (op # x))) \<noteq> (let (st,op) = t (q,i) in (let x = orun_trans t st j in (op # x)))"
    by (simp add: split_beta)
  then have "orun_trans f notapartq (i # j) \<noteq> orun_trans t q (i # j)"
     by (metis (mono_tags, lifting) split_beta orun_trans_Cons surjective_pairing)
  then show False
    using assms by (metis apart_machines.elims(1))
qed


text_raw  \<open>\snip{outsamenostep}{1}{1}{%\<close>
lemma hypothesis_no_step_output_same:
  assumes "invar (S,F,T)" and
    "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))" and
    "hypothesis (S,F,T) h" and
    "M = (q_0,f)" and
    "\<not> (apart_mealy M (srun_trans f q_0 p) q)" and
    "p \<in> S"
  shows "orun_trans f q inp = orun_trans h p inp"
text_raw \<open>}%endsnip\<close>
using assms proof (induction inp arbitrary: q p)
  case Nil
  show ?case
    unfolding orun_trans_def by simp
next
  case (Cons a inp)
  then have ass3:" \<not> apart_machines f (srun_trans f q_0 p) f q" unfolding apart_mealy_def 
    by auto
  have not_rule2: "\<not> (\<exists> s i. s \<in> S \<and> (orun T (s @ [i]) = None))"
    using no_step_rule2 assms by blast
  then have not_rule4: "\<not> (\<exists> s fs inp. fs \<in> F \<and>
      s \<in> S \<and>
      \<not> apart T s fs \<and>
      drop (length s) (orun_trans f (q_0) (s @ inp)) \<noteq>
      drop (length fs) (orun_trans f q_0 (fs @ inp)))"
    using no_step_rule4 assms diff_query_def diff_query_def_none by fast
  have "run T p \<noteq> None"
    using assms
    by (smt (verit) Cons.prems(6) case_optionE invars option.discI run_eq_out run.elims)
  then obtain tran op where
    tran: "run T p = Some (Node tran,op)"
    by (metis otree.exhaust option.exhaust surj_pair)
  have pa_not_none: "run T (p @ [a]) \<noteq> None"
    using assms
    by (smt (verit) Cons.prems(6) case_optionE not_rule2 option.discI run_eq_out run.elims)
  then have "tran a \<noteq> None"
    using tran by (metis otree.exhaust run_split_none)
  then obtain n out where
    nout: "tran a = Some (n,out)"
    by fast
  obtain tree where
    tree: "T = Node tree"
    using otree.exhaust by auto
  obtain ots ptrans where
    ots: "run_trans f q_0 p = (ptrans,ots)"
    by fastforce
  obtain q' out2 where
    out2: "f (q,a) = (q',out2)"
    by fastforce
  have output_same: "Some (orun_trans f q_0 (p @ [a])) = orun T (p @ [a])"
    using pa_not_none Cons(2,5) by (metis Cons.prems(6) invars(6) not_rule2 output_query.simps)
  have "run T (p @ [a]) = Some (n,op @ [out])"
    using tran nout by (metis otree.exhaust run_split)
  then have orun_out: "orun T (p @ [a]) = Some (op @ [out])"
    using run_eq_out[of tree "p @ [a]"] tree by simp
  obtain notapartq outq where
    run_transp: "run_trans f q_0 p = (notapartq,outq)"
    by fastforce
  then have "\<not> (apart_machines f notapartq f q)"
    using Cons ass3 by (metis Pair_inject out_srun_trans)
  then have "snd (f (notapartq,a)) = snd (f (q,a))"
    using not_apart_machines_snd_f by fast
  then have "snd (f (notapartq,a)) = out2"
    using out2 by auto
  then obtain notapartq' where
    notapartq': "f (notapartq,a) = (notapartq',out2)"
    by (metis prod.collapse)
  then have run_trans_pa: "(run_trans f q_0 (p @ [a])) = (notapartq',outq @ [out2])"
    using run_trans_split_end[of f notapartq a notapartq' out2 q_0 p outq] run_transp
    by linarith
  then have "orun_trans f q_0 (p @ [a]) = outq @ [out2]"
    by (simp add: out_srun_trans)
  then have out2_eq: "out2 = out"
    using orun_out output_same ots run_transp by auto
  have notapartq'_alt: "srun_trans f q_0 (p @ [a]) = notapartq'"
    using out_srun_trans run_trans_pa by (metis Pair_inject)
  have "\<not> apart_machines f (fst (f (srun_trans f q_0 p,a))) f q'"
    using apart_machines_propagates_function Cons ass3 by (metis fstI out2)
  then have "\<not> apart_machines f notapartq' f q'"
    using notapartq' by (metis split_pairs out_srun_trans run_transp)
  then have ih_prem: "\<not> apart_mealy M (srun_trans f q_0 (p @ [a]))  q'"
    using notapartq'_alt unfolding apart_mealy_def  by (simp add: assms(4))
  show ?case proof (cases "p @ [a] \<in> S")
    case True
    have "h(p,a) = (p @ [a],out)"
      using Cons(4) nout tran Cons(7) True by (simp add: hypothesis_split_in_S)
    then have aux: "orun_trans h p (a # inp) = (out # orun_trans h (p @ [a]) inp)"
      using orun_trans_Cons by fast
    then have "orun_trans f q' inp = orun_trans h (p @ [a]) inp"
      using Cons.IH ih_prem True assms(1-4) ass3 by blast
    then have "out2 # orun_trans f q' inp = out # orun_trans h (p @ [a]) inp"
      using out2_eq by blast
    then have "orun_trans f q (a # inp) = orun_trans h p (a # inp)"
      using aux out2 by (simp add: orun_trans_Cons)
    then show ?thesis
      by blast
  next
    case False
    have pa_frontier: "p @ [a] \<in> F"
      using Cons False frontier.simps invars(7) not_rule2 by fastforce
    obtain p' where
      p': "h (p,a) = (p',out)"
      using False by (meson Cons.prems(3,6) nout tran hypothesis_split_notin_S)
    then have notapart_p'pa: "\<not> apart T p' (p @ [a]) \<and> p' \<in> S"
      using hypothesis_split_notin_S[of S F T h p tran op a n out] assms(3,6)
      by (simp add: Cons.prems(6) False nout tran)
    have "\<not> apart_mealy M (srun_trans f q_0 (p')) q'"
    proof (rule ccontr)
      assume assapart: "\<not> \<not> apart_mealy M (srun_trans f q_0 (p')) q'"
      have "\<exists> inp. drop (length p') (orun_trans f (q_0) (p' @ inp)) \<noteq>
          drop (length (p @ [a])) (orun_trans f q_0 (p @ [a] @ inp))"
      proof (rule ccontr)
        assume "\<not> (\<exists> inp. drop (length p') (orun_trans f (q_0) (p' @ inp)) \<noteq>
            drop (length (p @ [a])) (orun_trans f q_0 (p @ [a] @ inp)))"
        then have same_output_pa_p': "\<forall> inp. drop (length p') (orun_trans f (q_0) (p' @ inp)) =
            drop (length (p @ [a])) (orun_trans f q_0 (p @ [a] @ inp))"
          by blast
        have pa_inp_run_trans_without_drop: "\<forall> inp. drop (length (p @ [a])) (orun_trans f (q_0) (p @ [a] @ inp)) =
            orun_trans f (srun_trans f q_0 (p @ [a])) inp"
          by (metis append_assoc fst_eqD notapartq'_alt snd_conv out_srun_trans run_trans_two_nested)
        have "\<forall> inp. drop (length p') (orun_trans f (q_0) (p' @ inp)) = orun_trans f (srun_trans f q_0 (p')) inp"
          by (metis fst_eqD snd_conv out_srun_trans run_trans_two_nested)
        then have trans_output_pa_p'_eq: "\<forall> inp. orun_trans f (srun_trans f q_0 (p')) inp = orun_trans f (srun_trans f q_0 (p @ [a])) inp"
          using pa_inp_run_trans_without_drop same_output_pa_p' by presburger
        have "\<forall> i. orun_trans f (srun_trans f q_0 (p @ [a])) i = orun_trans f q' i"
          using ih_prem unfolding apart_mealy_def by (simp add: assms(4))
        then have "\<forall> i. orun_trans f (srun_trans f q_0 (p')) i = orun_trans f q' i"
          using trans_output_pa_p'_eq by simp
        then have "\<not> apart_mealy M (srun_trans f q_0 p') q'" 
          unfolding apart_mealy_def assms(4) by simp
        then show False
          using assapart by blast
      qed
      then show False
        using not_rule4 notapart_p'pa pa_frontier by fastforce
    qed
    then have "\<not> apart_mealy M (srun_trans f q_0 p') q'"
      unfolding apart_mealy_def assms(4) by simp
    then have "orun_trans f q' inp = orun_trans h (p') inp"
      using Cons.IH p' False assms(1-4) notapart_p'pa  by blast
    then have "out2 # orun_trans f q' inp = out # orun_trans h (p') inp"
      using out2_eq by blast
    then have "orun_trans f q (a # inp) = orun_trans h p (a # inp)" unfolding orun_trans_def 
      by (simp add: out2 out_srun_trans p' orun_trans_Cons)
    then show ?thesis
      by blast
  qed
qed

fun find_not_apart :: "('in,'out) otree \<Rightarrow> 'in list \<Rightarrow> 'in list list \<Rightarrow> 'in list" where
"find_not_apart T f [] = []" |
"find_not_apart T f (s # ss) = (if \<not> apart T f s
    then s
    else find_not_apart T f ss)"

lemma find_not_apart_not_apart: "\<exists> s \<in> set S. \<not> apart T f s \<Longrightarrow> \<not> apart T f (find_not_apart T f S)"
  by (induction S) auto

fun hypo :: "'in list list \<Rightarrow> ('in,'out) otree \<Rightarrow> 'in list \<Rightarrow> (('in list \<times> 'in) \<Rightarrow> ('in list \<times> 'out))" where
"hypo S T acc ([],i) = (case orun T (acc @ [i]) of
    Some out \<Rightarrow> (if acc @ [i] \<in> set S
      then (acc @ [i],last out)
      else ((find_not_apart T (acc @ [i]) S),last out)))" |
"hypo S T acc (n # nlist,i) = (if (acc @ [n]) \<in> set S
    then hypo S T (acc @ [n]) (nlist,i)
    else hypo S T (find_not_apart T (acc @ [n]) S) (nlist,i))"

(* decribe a function that calculates the hypothesis *)

lemma find_nap_in_s_and_apart: "\<not> (\<forall> s \<in> set S. apart T s f) \<Longrightarrow> find_not_apart T f S \<in> set S \<and> \<not> apart T f (find_not_apart T f S)"
proof (standard,goal_cases)
  case 1
  then show ?case
    by (induction S) auto
next
  case 2
  then show ?case
    using find_not_apart_not_apart by (metis apart.simps)
qed

lemma hypo_works_input_in_S:
  assumes "invar (set S,F,T)" and
    "run T (acc @ s) = (Some (Node tran,op))" and
    "tran i = Some (n,out)" and
    "acc @ s @ [i] \<in> set S"
  shows "hypo S T acc (s,i) = (acc @ s @ [i],out)"
using assms proof (induction s arbitrary: acc)
  case Nil
  have "run T (acc @ [i]) = Some (n,op @ [out])"
    using Nil by (metis append.right_neutral otree.exhaust run_split)
  then have "orun T (acc @ [i]) = Some (op @ [out])"
    using run_eq_out_exhaust[of T "acc @ [i]"] by simp
  then show ?case
    using Nil.prems(4) by auto
next
  case (Cons a s)
  then have "acc @ [a] @ s @ [i] \<in> set S"
    by simp
  then have "acc @ [a] \<in> set S"
    using Cons(2) invars(9) invar_substring_in_s[of "set S" "acc @ [a]" "s @ [i]"] by simp
  then have hypo_step: "hypo S T acc (a # s,i) = hypo S T (acc @ [a]) (s,i)"
    by auto
  then have "hypo S T (acc @ [a]) (s,i) = (acc @ [a] @ s @ [i],out)"
    using Cons by fastforce
  then show ?case
    using hypo_step by fastforce
qed

lemma hypo_works_input_notin_S:
  assumes "invar (set S,F,T)" and
    "run T (acc @ s) = (Some (Node tran,op))" and
    "tran i = Some (n,out)" and
    "acc @ s \<in> set S" and
    "acc @ s @ [i] \<notin> set S" and
    "\<exists> z \<in> set S. \<not> apart T (acc @ s @ [i]) z" and
    "hypo S T acc (s,i) = (y,outh)"
  shows "\<not> apart T y (acc @ s @ [i]) \<and> outh = out \<and> y \<in> set S"
using assms proof(induction s arbitrary: acc)
  case Nil
  have "run T (acc @ [i]) = Some (n,op @ [out])"
    using Nil by (metis append.right_neutral otree.exhaust run_split)
  then have "orun T (acc @ [i]) = Some (op @ [out])"
    using run_eq_out_exhaust[of T "acc @ [i]"] by auto
  then have h: "hypo S T acc ([],i) = (find_not_apart T (acc @ [i]) S,out)"
    using Nil by force
  then have ydef: "y = find_not_apart T (acc @ [i]) S"
    using Nil by force
  then have "(\<not> apart T (find_not_apart T (acc @ [i]) S) (acc @ [i])) \<and> ((find_not_apart T (acc @ [i]) S)) \<in> set S"
    using find_nap_in_s_and_apart[of S T "acc @ [i]"] Nil(6) by fastforce
  then show ?case
    using ydef h Nil by simp
next
  case (Cons a s)
  then have z: "acc @ [a] @ s \<in> set S"
    by force
  then have "acc @ [a] \<in> set S"
    using Cons(2) invars(9) invar_substring_in_s[of "set S" "acc @ [a]" "s"] by simp
  then have hypoeq: "hypo S T acc (a # s,i) = hypo S T (acc @ [a]) (s,i)"
    by fastforce
  then have a: "(y,outh) = hypo S T (acc @ [a]) (s,i)"
    using Cons by argo

  have b: "run T (acc @ [a] @ s) = Some (Node tran,op)"
    using Cons by fastforce
  have c: "acc @ [a] @ s @ [i] \<notin> set S"
    using Cons by simp
  have "\<exists> z \<in> set S. \<not> apart T ((acc @ [a] @ s) @ [i]) z"
    using Cons by simp
  then have "\<not> apart T y (acc @ [a] @ s @ [i]) \<and> outh = out \<and> y \<in> set S"
    using Cons.IH[of "acc @ [a]"] z a b c Cons by auto
  then show ?case
    by simp
qed

lemma
  assumes "invar (set S,F,T)" and
    "\<not> (\<exists> f \<in> F. \<forall> s \<in> set S. apart T s f)" and
    "\<not> (\<exists> s \<in> set S. EX i. (orun T (s @ [i]) = None))"
  shows "hypothesis (set S,F,T) (hypo S T [])"
proof (rule ccontr)
  assume "\<not> hypothesis (set S,F,T) (hypo S T [])"
  then have assume1: "\<exists> s \<in> set S. \<exists> i. \<not> (\<exists> tran op n out. (run T s = Some (Node tran,op)) \<and> (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> set S
        then (hypo S T []) (s,i) = (s @ [i],out)
        else (\<exists> y \<in> set S. \<not> apart T y (s @ [i]) \<and> (hypo S T []) (s,i) = (y,out))))"
    by auto
  then obtain s i where
    si: "s \<in> set S \<and> \<not> (\<exists> tran op n out. (run T s = Some (Node tran,op)) \<and> (tran i = Some (n,out)) \<and>
        (if (s @ [i]) \<in> set S
          then (hypo S T []) (s,i) = (s @ [i],out)
          else (\<exists> y \<in> set S. \<not> apart T y (s @ [i]) \<and> (hypo S T []) (s,i) = (y,out))))"
    by blast

  have "run T s \<noteq> None"
    using assms(1) si invars(2)
    by (smt (verit) case_optionE not_None_eq otree.exhaust run_eq_out)
  then obtain tran op where
    tranop: "run T s = (Some (Node tran,op))"
    by (metis not_Some_eq otree.exhaust old.prod.exhaust)
  then have assume2: "\<not> (\<exists> n out. (tran i = Some (n,out)) \<and>
      (if (s @ [i]) \<in> set S
        then (hypo S T []) (s,i) = (s @ [i],out)
        else (\<exists> y \<in> set S. \<not> apart T y (s @ [i]) \<and> (hypo S T []) (s,i) = (y,out))))"
    using assume1 si by blast
  have "tran i \<noteq> None" proof(rule ccontr)
    assume "\<not> tran i \<noteq> None"
    then have "orun T (s @ [i]) = None"
      by (smt (verit) Nil_is_append_conv case_optionE not_Cons_self2 option.discI run_eq_out run_split_none orun.elims tranop)
    then show False
      using assms(3) si by blast
  qed
  then obtain n out where
    nout: "tran i = Some (n,out)"
    by auto
  then have assume3: "\<not> (if (s @ [i]) \<in> set S
      then (hypo S T []) (s,i) = (s @ [i],out)
      else (\<exists> y \<in> set S. \<not> apart T y (s @ [i]) \<and> (hypo S T []) (s,i) = (y,out)))"
    using assume2 si tranop by blast
  then show False proof (cases "s @ [i] \<in> set S")
    case True
    then have "(hypo S T []) (s,i) = (s @ [i],out)"
      using hypo_works_input_in_S tranop nout assms(1) by simp
    then show ?thesis
      using assume3 True by fastforce
  next
    case False
    have sinS: "s \<in> set S"
      using si by blast
    then have "[] @ s \<in> set S"
      by fastforce
    obtain y outh where
      youth: "hypo S T [] (s,i) = (y,outh)"
      by fastforce
    have "s @ [i] \<in> frontier (set S,F,T)"
      using False sinS assms by simp
    then have "s @ [i] \<in> F"
      using assms invars(7) by blast
    then have "\<exists> z \<in> set S. \<not> apart T (s @ [i]) z"
      using assms by fastforce
    then have napart: "\<not> apart T (s @ [i]) y \<and> outh = out \<and> y \<in> set S"
      using hypo_works_input_notin_S[of S F T "[]" s tran op i n out y outh] youth assms(1) tranop nout
      using sinS False
      by auto
    then have hypo: "hypo S T [] (s,i) = (y,out)"
      using youth by blast
    then have "\<not> (\<exists> y \<in> set S. \<not> apart T y (s @ [i]) \<and> hypo S T [] (s,i) = (y,out))"
      using assume3 False by argo
    then show ?thesis
      using napart hypo by auto
  qed
qed

theorem no_step_mealy_equal:
  assumes "invar (S,F,T)" and
    "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))" and
    "hypothesis (S,F,T) t"
  shows "M \<approx> ([],t)"
  text \<open>this theorem is used equivalent to theorem 3.7 in the L sharp paper, we use
    @{term "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))"} as our stopping argument instead of the number of states in S\<close>
proof (rule ccontr)
  assume ass: "~ (M \<approx> ([],t))"
  obtain q_0 f where
    two: "M = (q_0,f)"
    by fastforce
  then have "\<exists> inp. orun_trans f q_0 inp \<noteq> orun_trans t [] inp"
    using ass unfolding eq_mealy_def by blast
  then obtain inp where
    neq: "orun_trans f q_0 inp \<noteq> orun_trans t [] inp"
    by blast
  have one: "[] \<in> S"
    using assms by (simp add: invars(8))
  have three: "\<not> (apart_mealy M (srun_trans f q_0 [])  q_0)" 
    unfolding srun_trans_def apart_mealy_def by force
  have "orun_trans f q_0 inp = orun_trans t [] inp"
    using hypothesis_no_step_output_same[of S F T t q_0 f "[]" q_0 inp] one two three assms by blast
  then show False
    using neq by blast
qed

abbreviation algo_steps where
"algo_steps \<equiv> algo_step^**"
notation algo_steps (infix "\<Rightarrow>*" 45)


lemma invar_if_algo_steps: "algo_steps ({[]},{},Node Map.empty) (S,F,T) \<Longrightarrow> invar (S,F,T)"
proof(induction rule: rtranclp_induct)
  case base
  then show ?case
    by (simp add: empty_is_invar)
next
  case step
  then show ?case
    by (metis algo_step_keeps_invar surj_pair)
qed


corollary no_step_mealy_equal2:
  assumes "algo_steps ({[]},{},Node Map.empty) (S,F,T)" and
    "\<not> (\<exists> S' F' T'. algo_step (S,F,T) (S',F',T'))"
  shows "(\<exists> t. hypothesis (S,F,T) t) \<and>(\<forall> t. hypothesis (S,F,T) t \<longrightarrow> M \<approx> ([],t))"
    using no_step_mealy_equal no_step_exists_hypothesis invar_if_algo_steps assms
    by metis

  (* further possible beautification: replace triples (S,F,T)
      by single variables *)


section \<open>Functional Version\<close>

fun updateF_aux :: "('in,'out) otree \<Rightarrow> 'in list set \<Rightarrow> 'in list \<Rightarrow> 'in list \<Rightarrow> 'in list list" where
"updateF_aux T _ s [] = []" |
"updateF_aux T S s (i # is) = (if (s @ [i]) \<notin> S \<and> orun T (s @ [i]) \<noteq> None
    then (s @ [i]) # updateF_aux T S s is
    else updateF_aux T S s is)"

lemma updateF_aux_def: "set (updateF_aux T S s Ilist) = {f.((\<exists> i \<in> set Ilist. f = s @ [i]) \<and> f \<notin> S \<and> orun T f \<noteq> None)}"
  apply (induction "Ilist")
  using univI
  by auto

fun updateF :: "('in,'out) otree \<Rightarrow> 'in list set \<Rightarrow> 'in list list \<Rightarrow> 'in list list" where
"updateF T _ [] = []" |
"updateF T S (s # ss) = updateF_aux T S s Ilist @ (updateF T S ss)"

lemma updateF_def_aux: "set (updateF T sset S) = {f.((\<exists> s \<in> set S. \<exists> i \<in> set Ilist. f = s @ [i]) \<and> f \<notin> sset \<and> orun T f \<noteq> None)}"
  using updateF_aux_def
  by (induction S) auto

lemma updateF_def: "set (updateF T (set S) S) = frontier (set S,set F,T)"
  using updateF_def_aux[of T "set S" S] univI I_def
  by auto

fun find1 :: "('in,'out) otree \<Rightarrow> 'in list list \<Rightarrow> 'in list list \<Rightarrow> 'in list option" where
"find1 T S [] = None" |
"find1 T S (f # fs) = (if (\<forall> s \<in> set S. apart T s f)
    then Some f
    else find1 T S fs)"

lemma find1_def: "(find1 T S F = Some x) \<longrightarrow> (x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x))"
  by (induction F) auto

lemma find1_none_noapart: "(find1 T S F = None) \<Longrightarrow> (\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x))"
proof (induction F)
  case Nil
  then show ?case
    by simp
next
  case (Cons a F)
  then have a: "\<not> (\<forall> s \<in> set S. apart T s a)"
    by force
  have "(if (\<forall> s \<in> set S. apart T s a)
      then Some a
      else find1 T S F) = None"
    using Cons by auto
  then have "find1 T S F = None"
    using a by argo
  then have "\<nexists> x. x \<in> set (a # F) \<and> (\<forall> s \<in> set S. apart T s x)"
    using Cons a by auto
  then show ?case
    by blast
qed

lemma find1_noapart_none: "(\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)) \<Longrightarrow> (find1 T S F = None)"
proof (induction F)
  case Nil
  then show ?case
    by simp
next
  case (Cons a F)
  then have a: "\<not> (\<forall> s \<in> set S. apart T s a)"
    by force
  have "(if (\<forall> s \<in> set S. apart T s a)
      then Some a
      else find1 T S F) = None"
    using Cons by auto
  then have "find1 T S F = None"
    using a by argo
  then show ?case
    using a by simp
qed

lemma find1_def_none: "(find1 T S F = None) \<longleftrightarrow> (\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x))"
  using find1_noapart_none find1_none_noapart by blast

lemma find1_step:
  assumes "find1 T S F = Some f"
  shows "algo_step (set S,set F,T) (set (f # S),set (updateF T (set (f # S)) (f # S)),T)"
    using assms updateF_def find1_def rule1
    by (smt (verit) inf_sup_aci(5) insert_def list.simps(15) singleton_conv)

fun find2_aux :: "('in,'out) otree \<Rightarrow> 'in list \<Rightarrow> 'in list \<Rightarrow> 'in list option" where
"find2_aux T s [] = None" |
"find2_aux T s (i # is) = (if (orun T (s @ [i]) = None)
    then Some (s @ [i])
    else find2_aux T s is)"

fun find2 :: "('in,'out) otree \<Rightarrow> 'in list list \<Rightarrow> 'in list list \<Rightarrow> 'in list option" where
"find2 T [] F = None" |
"find2 T (s # ss) F = (case find2_aux T s Ilist of
    Some x \<Rightarrow> Some x |
    None \<Rightarrow> find2 T ss F)"

lemma find2_aux_def: "find2_aux T s Is = Some x \<longrightarrow> (\<exists> i \<in> set Is. x = s @ [i] \<and> orun T x = None)"
  by (induction Is) auto

lemma find2_aux_def_none: "find2_aux T s Is = None \<longleftrightarrow> \<not> (\<exists> i \<in> set Is. orun T (s @ [i]) = None)"
proof(standard,goal_cases)
  case 1
  then show ?case proof (induction Is)
    case Nil
    then show ?case
      by simp
  next
    case (Cons a Is)
    then have a: "\<not> (orun T (s @ [a]) = None)"
      by (metis find2_aux.simps(2) option.discI)
    have "(if orun T (s @ [a]) = None
        then Some (s @ [a])
        else find2_aux T s Is) = None"
      using Cons by auto
    then have "find2_aux T s Is = None"
      using a by argo
    then show ?case
      using Cons a by fastforce
  qed
next
  case 2
  then show ?case
  proof(induction Is)
    case Nil
    then show ?case
      by fastforce
  next
    case (Cons a Is)
    then have a: "\<not> (\<exists> i \<in> set Is. orun T (s @ [i]) = None)"
      by auto
    then have b: "find2_aux T s Is = None"
      using Cons by presburger
    have "\<not> (orun T (s @ [a]) = None)"
      using Cons by auto
    then show ?case
      using b by force
  qed
qed

lemma find2_def: "find2 T S F = Some x \<Longrightarrow> (\<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> orun T x = None)"
proof (induction S)
  case Nil
  then show ?case
    by force
next
  case (Cons s S)
  then show ?case proof (cases "find2_aux T s Ilist")
    case None
    then show ?thesis
      using Cons by simp
  next
    case (Some a)
    then have "find2 T (s # S) F = Some a"
      using Some Cons by force
    then show ?thesis
      using find2_aux_def Some Cons by fastforce
  qed
qed

lemma find2_def_none_aux: "(find2 T S F = None) \<longleftrightarrow> \<not> (\<exists> s \<in> set S. \<exists> i. orun T (s @ [i]) = None)"
proof(standard,goal_cases)
  case 1
  then show ?case proof(induction S)
    case Nil
    then show ?case
      by simp
  next
    case (Cons s S)
    then have none_aux: "find2_aux T s Ilist = None"
      using neq_Nil_conv by fastforce
    then have a: "\<not> (\<exists> i. orun T (s @ [i]) = None)"
      using find2_aux_def_none I_def univI by blast
    then have "find2 T S F = None"
      using Cons none_aux by fastforce
    then show ?case
      using a Cons by simp
  qed
next
  case 2
  then show ?case proof(induction S)
    case Nil
    then show ?case
      by simp
  next
    case (Cons s S)
    then have none_aux: "find2_aux T s Ilist = None"
      using find2_aux_def_none by simp
    then have "find2 T S F = None"
      using Cons by simp
    then show ?case
      using none_aux Cons by simp
  qed
qed

lemma find2_def_none: "(find2 T S F = None) \<longleftrightarrow> (\<nexists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> orun T x = None)"
  using find2_def_none_aux by metis

lemma find2_step:
  assumes "find2 T S F = Some x"
  shows "algo_step (set S,set F,T) (set S,set (x # F),process_output_query T x (output_query M x))"
    using assms find2_def rule2 by (metis Un_commute insert_is_Un list.simps(15))

end

locale Lsharp_fun = Lsharp_rel M for M :: "('s :: finite,'in :: finite,'out) mealy" +
fixes find3 :: "('in,'out) otree \<Rightarrow> 'in list list \<Rightarrow> 'in list list \<Rightarrow> 'in list option"

assumes
  find3_def: "(find3 T S F = Some x) \<longrightarrow> (\<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2 \<and>
      apart_witness T s1 s2 w)" and
  find3_def_none: "(find3 T S F = None) \<longleftrightarrow> (\<nexists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
      \<not> apart T f s1 \<and>
      \<not> apart T f s2 \<and>
      apart_witness T s1 s2 w)"
begin

lemma find3_step:
  assumes "find3 T S F = Some x"
  shows "algo_step (set S,set F,T) (set S,set F,process_output_query T x (output_query M x))"
    using find3_def rule3 assms by blast

fun find4_aux :: "('in,'out) otree \<Rightarrow> 'in list list \<Rightarrow> 'in list \<Rightarrow> ('in list \<times> 'in list) option" where
"find4_aux T [] f = None" |
"find4_aux T (s # ss) f = (if apart T s f
    then find4_aux T ss f
    else (case diff_query M s f of
      None \<Rightarrow> find4_aux T ss f |
      Some inp \<Rightarrow> Some(s @ inp,f @ inp)))"

fun find4 :: "('in,'out) otree \<Rightarrow> 'in list list \<Rightarrow> 'in list list \<Rightarrow> ('in list \<times> 'in list) option" where
"find4 T S [] = None" |
"find4 T S (f # fs) = (case find4_aux T S f of
    Some x \<Rightarrow> Some x |
    None \<Rightarrow> find4 T S fs)"

lemma find4_aux_def: "find4_aux T S f = Some (x,y) \<Longrightarrow> (\<exists> s \<in> set S. \<exists> inp.
    \<not> apart T s f \<and>
    diff_query M s f = Some inp \<and> x = s @ inp \<and> y = f @ inp)"
proof (induction S)
  case Nil
  then show ?case
    by simp
next
  case (Cons s S)
  then show ?case proof (cases "apart T s f")
    case True
    then show ?thesis
      using Cons by force
  next
    case False
    then show ?thesis proof (cases "diff_query M s f")
      case None
      then have "find4_aux T (s # S) f = find4_aux T S f"
        using False None by force
      then show ?thesis
        using Cons by force
    next
      case (Some inp)
      then have "x = s @ inp \<and> y = f @ inp"
        using False Cons
        by (metis (lifting) Pair_inject find4_aux.simps(2) option.inject option.simps(5))
      then show ?thesis
        using False Some Cons by simp
    qed
  qed
qed

lemma find4_aux_def_none: "find4_aux T S fs = None \<longleftrightarrow> \<not> (\<exists> x y. \<exists> s \<in> set S. \<exists> inp.
    \<not> apart T s fs \<and>
    diff_query M s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
proof(standard,goal_cases)
  case 1
  then show ?case proof(induction S)
    case Nil
    then show ?case
      by simp
  next
    case (Cons s S)
    have "\<not> apart T s fs \<and> diff_query M s fs \<noteq> None \<Longrightarrow> find4_aux T (s # S) fs \<noteq> None"
      by fastforce
    then have "apart T s fs \<or> diff_query M s fs = None"
      using Cons by argo
    then have "find4_aux T (s # S) fs = find4_aux T S fs"
      by fastforce
    then show ?case
      using Cons by auto
  qed
next
  case 2
  then show ?case proof(induction S)
    case Nil
    then show ?case
      by simp
  next
    case (Cons s S)
    then have "apart T s fs \<or> diff_query M s fs = None"
      using Cons by force
    then have "find4_aux T (s # S) fs = find4_aux T S fs"
      by fastforce
    then show ?case
      using Cons by auto
  qed
qed


lemma find4_def: "(find4 T S F = Some (x,y)) \<longrightarrow>
    (\<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
      \<not> apart T s fs \<and>
      diff_query M s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
proof (induction F)
  case Nil
  then show ?case
    by auto
next
  case (Cons f F)
  then show ?case proof (cases "find4_aux T S f")
    case None
    then show ?thesis
      using Cons by simp
  next
    case (Some a)
    then show ?thesis
      using find4_aux_def by simp
  qed
qed

lemma find4_def_none: "find4 T S F = None \<longleftrightarrow>
    (\<nexists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
      \<not> apart T s fs \<and>
      diff_query M s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
proof (standard,goal_cases)
  case 1
  then show ?case proof (induction F)
    case Nil
    then show ?case
      by auto
  next
    case (Cons f F)
    then have a: "find4_aux T S f = None"
      using not_None_eq by fastforce
    then have "\<not> (\<exists> x y. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s f \<and>
        diff_query M s f = Some inp \<and> x = s @ inp \<and> y = f @ inp)"
      using find4_aux_def_none by blast
    then show ?case
      using a Cons by auto
  qed
next
  case 2
  then show ?case proof (induction F)
    case Nil
    then show ?case
      by auto
  next
    case (Cons f F)
    then have "find4_aux T S f = None"
      using find4_aux_def_none by auto
    then show ?case
      using Cons by auto
  qed
qed

lemma find4_step:
  assumes "find1 T S F = None" and
    "find2 T S F = None" and
    "find4 T S F = Some (x,y)"
  shows "algo_step (set S,set F,T) (set S,set F,process_output_query (process_output_query T x (output_query M x)) y (output_query M y))"
proof -
  have "\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)"
    using assms find1_def_none by blast
  then have a: "\<forall> f1 \<in> set F. \<not> (isolated T (set S) f1)"
    by simp
  have "\<nexists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> orun T x = None"
    using assms find2_def_none by blast
  then have b: "\<forall> s1 \<in> set S. \<forall> i. orun T (s1 @ [i]) \<noteq> None"
    by auto
  have "\<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
      \<not> apart T s fs \<and>
      diff_query M s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp"
    using find4_def assms by blast
  then show ?thesis
    using a b rule4 by blast
qed

lemma norm_ge_invar_fin1:
  assumes "find1 T S F = Some f" and
    "invar (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set (f # S),set (updateF T (set (f # S)) (f # S)),T)" and
    "invar (set (f # S),set (updateF T (set (f # S)) (f # S)),T)"
      using assms find1_step algo_step_increases_norm algo_step_keeps_invar
      by blast +

lemma norm_ge_invar_fin2:
  assumes "find2 T S F = Some x" and
    "invar (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set S,set (x # F),process_output_query T x (output_query M x))" and
    "invar (set S,set (x # F),process_output_query T x (output_query M x))"
      using assms find2_step algo_step_increases_norm algo_step_keeps_invar
      by blast +

lemma norm_ge_invar_fin3:
  assumes "find3 T S F = Some x" and
    "invar (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set S,set F,process_output_query T x (output_query M x))" and
    "invar (set S,set F,process_output_query T x (output_query M x))"
      using assms find3_step algo_step_increases_norm algo_step_keeps_invar
      by blast +

lemma norm_ge_invar_fin4:
  assumes "find1 T S F = None" and
    "find2 T S F = None" and
    "find4 T S F = Some (x,y)" and
    "invar (set S,set F,T)"
  shows "norm (set S,set F,T) < norm (set S,set F,process_output_query (process_output_query T x (output_query M x)) y (output_query M y))" and
    "invar (set S,set F,process_output_query (process_output_query T x (output_query M x)) y (output_query M y))"
      using assms find4_step algo_step_increases_norm algo_step_keeps_invar
      by blast +

lemma not_algostep_find_none:
  assumes "\<nexists> S' F' T'. algo_step (set S,set F,T) (S',F',T')" and
    "invar (set S,set F,T)"
  shows "find1 T S F = None" and
    "find2 T S F = None" and
    "find3 T S F = None" and
    "find4 T S F = None"
      using assms no_step_rule1 find1_def_none apply meson
      using assms no_step_rule2 find2_def_none apply fast
      using assms no_step_rule3 find3_def_none apply fast
      using assms no_step_rule4 find4_def_none by fast

lemma norm_max_find_none:
  assumes "norm (set S,set F,T) \<ge> max_norm Q" and
    "invar (set S,set F,T)"
  shows "find1 T S F = None" and
    "find2 T S F = None" and
    "find3 T S F = None" and
    "find4 T S F = None"
using not_algostep_find_none norm_max_no_step assms by auto

lemma any_precon_algo_step:
  assumes "algo_step (set S,set F,T) (S',F',T')"
  shows "(\<exists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)) \<or>
      (\<exists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> orun T x = None) \<or>
      (\<exists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2 \<and>
        apart_witness T s1 s2 w) \<or>
      (\<exists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        diff_query M s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
    using assms
    apply (cases rule: algo_step.cases)
    by metis +

lemma nex_precondition_nex_algostep:
  assumes "\<nexists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)" and
    "\<nexists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> orun T x = None" and
    "\<nexists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2 \<and>
        apart_witness T s1 s2 w" and
    "\<nexists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        diff_query M s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp"
  shows "\<nexists> S' F' T'. algo_step (set S,set F,T) (S',F',T')"
proof
  assume "\<exists> S' F' T'. algo_step (set S,set F,T) (S',F',T')"
  then have "(\<exists> x. x \<in> set F \<and> (\<forall> s \<in> set S. apart T s x)) \<or>
      (\<exists> x. \<exists> s \<in> set S. \<exists> i. x = s @ [i] \<and> orun T x = None) \<or>
      (\<exists> x. \<exists> s1 \<in> set S. \<exists> s2 \<in> set S. \<exists> f \<in> set F. \<exists> w. x = f @ w \<and> s1 \<noteq> s2 \<and>
        \<not> apart T f s1 \<and>
        \<not> apart T f s2 \<and>
        apart_witness T s1 s2 w) \<or>
      (\<exists> x y. \<exists> fs \<in> set F. \<exists> s \<in> set S. \<exists> inp.
        \<not> apart T s fs \<and>
        diff_query M s fs = Some inp \<and> x = s @ inp \<and> y = fs @ inp)"
    using any_precon_algo_step by presburger
  then show False
    using assms by fast
qed

lemma find_none_no_step:
  assumes "find1 T S F = None" and
    "find2 T S F = None" and
    "find3 T S F = None" and
    "find4 T S F = None" and
    "invar (set S,set F,T)"
  shows "\<nexists> S' F' T'. algo_step (set S,set F,T) (S',F',T')"
    using nex_precondition_nex_algostep assms find1_def_none find2_def_none find3_def_none find4_def_none
    by simp

function lsharp :: "('in,'out) state_list \<Rightarrow> ('in,'out) state_list" where
"lsharp (S,F,T) = (if invar (set S,set F,T)
    then (case find1 T S F of
      Some f \<Rightarrow> lsharp (f # S,updateF T (set (f # S)) (f # S),T) |
      None \<Rightarrow> (case find2 T S F of
        Some x \<Rightarrow> lsharp (S,x # F,process_output_query T x (output_query M x)) |
        None \<Rightarrow> (case find3 T S F of
          Some x \<Rightarrow> lsharp (S,F,process_output_query T x (output_query M x)) |
          None \<Rightarrow> (case find4 T S F of
            Some (x,y) \<Rightarrow> lsharp (S,F,process_output_query (process_output_query T x (output_query M x)) y (output_query M y)) |
            None \<Rightarrow> (S,F,T)))))
    else ([], [],(Node Map.empty)))"
  by auto

termination lsharp
proof (relation "measure (\<lambda> (S,F,T). max_norm Q - norm (set S, set F,T))", goal_cases)
  case 1
  then show ?case 
    by blast
next
  case (2 S F T x2 x y)
 then have inv: "invar (set S, set F, process_output_query (process_output_query T x (output_query M x)) y (output_query M y))" 
    using norm_ge_invar_fin4 by blast
  have "norm (set S,set F,T) < 
    norm (set S, set F, process_output_query (process_output_query T x (output_query M x)) y (output_query M y)) " 
    using 2 norm_ge_invar_fin4 by blast
  then have "max_norm Q -norm (set S,set F,T) >
    max_norm Q - norm (set S, set F,  
    process_output_query (process_output_query T x (output_query M x)) y (output_query M y))" 
    using  max_norm_total inv by (simp add:  less_diff_conv2)
  then show ?case 
    by (metis (lifting) case_prod_conv in_measure)
next
  case (3 S F T x2)
  then have inv: "invar (set S, set F, process_output_query T x2 (output_query M x2))" 
    using norm_ge_invar_fin3  by blast
  have "norm (set S,set F,T) < 
    norm (set S, set F, process_output_query T x2 (output_query M x2)) " 
    using 3 norm_ge_invar_fin3 by blast
  then have "max_norm Q -norm (set S,set F,T) >
    max_norm Q - norm (set S, set F, process_output_query T x2 (output_query M x2))" using  max_norm_total inv 
    by (simp add: less_diff_conv2)
  then show ?case 
    by (metis (lifting) case_prod_conv in_measure)
next
  case (4 S F T x2)
  then have inv: "invar (set S,set  (x2 # F), process_output_query T x2 (output_query M x2))" 
    using norm_ge_invar_fin2
    by blast
  have "norm (set S,set F,T) < 
    norm (set S,set  (x2 # F), process_output_query T x2 (output_query M x2)) " 
    using 4 norm_ge_invar_fin2
    by blast
  then have "max_norm Q -norm (set S,set F,T) >
    max_norm Q - norm (set S,set  (x2 # F), process_output_query T x2 (output_query M x2))" using 4 max_norm_total inv 
    by (metis diff_less_mono2 le_eq_less_or_eq norm_max_find_none(2) option.distinct(1))
  then show ?case    
    by (metis (lifting) case_prod_conv in_measure)
next
  case (5 S F T x2)
   then have inv: "invar (set (x2 # S),set (updateF T (set (x2 # S)) (x2 # S)), T)" 
    using norm_ge_invar_fin1
    by blast
  have "norm (set S,set F,T) < 
    norm (set (x2 # S),set (updateF T (set (x2 # S)) (x2 # S)), T) " 
    using 5 norm_ge_invar_fin1
    by blast
  then have "max_norm Q -norm (set S,set F,T) >
    max_norm Q - norm (set (x2 # S),set (updateF T (set (x2 # S)) (x2 # S)), T)" using 5 max_norm_total inv 
    by (metis add_left_cancel le_add_diff_inverse2 le_diff_iff' nat_less_le)
  then show ?case    
    by (metis (lifting) case_prod_conv in_measure)
qed

end

end
