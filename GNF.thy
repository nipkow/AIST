theory GNF
imports CFG
begin

fun nt :: "('n,'t)symb \<Rightarrow> 'n set" where
"nt(N A) = {A}" |
"nt(T a) = {}"

fun rt :: "('n,'t)symbs \<Rightarrow> bool" where
"rt [] = True" |
"rt (T _ # _) = True" |
"rt _ = False"

definition rtps :: "('n,'t)prods \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> ps. rt(snd p))"

definition Lnt :: "('n, 't) prods \<Rightarrow> ('n * 'n * ('n,'t)symbs)set" where
"Lnt P = {(A,B,w). (A, N B # w) \<in> P}"

lemma [code]: "Lnt P = \<Union> ((\<lambda>(A,w). case w of N B#v \<Rightarrow> {(A,B,v)} | _ \<Rightarrow> {}) ` P)"
  by (auto simp: Lnt_def split: list.splits symb.splits)

definition rule where "rule = (\<lambda>(A, B, w). (A, N B # w))"

lemma Lnt_Un: "Lnt (A \<union> B) = Lnt A \<union> Lnt B"
by(auto simp: Lnt_def)

lemma Lnt_Diff: "Lnt (A - B) = Lnt A - Lnt B"
by(auto simp: Lnt_def)

lemma Lnt_rule: "Lnt(rule ` S) = S"
by(auto simp: Lnt_def rule_def image_def split:prod.splits)

(*
fun lnt :: "('n,'t)prod \<Rightarrow> 'n option" where
"lnt(_,N A # _) = Some A" |
"lnt _ = None"

definition "has_lnt p = (\<exists>A u. snd p = N A # u)"

lemma has_lnt_iff_lnt_split_Some: "has_lnt p = (\<exists>A. lnt_split p = Some A)"
by(cases p rule: lnt_split.cases) (auto simp: has_lnt_def)
*)
declare [[simproc add: finite_Collect]]

lemma inj_Lnt: "inj rule"
by(simp add: inj_def rule_def)

lemma finite_Lnt: "finite P \<Longrightarrow> finite(Lnt P)"
by(auto simp: Lnt_def finite_vimageI inj_Lnt[simplified rule_def])

lemma rtps_if_Lnt_empty: "Lnt P = {} \<Longrightarrow> rtps P"
by(auto simp: Lnt_def rtps_def elim!:  rt.elims(3)) (metis rt.elims(3))

definition eps_free where "eps_free R = (\<forall>(_,r) \<in> R. r \<noteq> [])"

lemma eps_freeI:
  assumes "\<And>A r. (A,r) \<in> R \<Longrightarrow> r \<noteq> []" shows "eps_free R"
  using assms by (auto simp: eps_free_def)

lemma "\<exists>R'. eps_free R' \<and> (\<forall>A. Lang R' A = Lang R A - {[]})"
sorry

lemma eps_free_Nil: "eps_free R \<Longrightarrow> (A,[]) \<notin> R"
sorry

lemma eps_freeE_Cons: "eps_free R \<Longrightarrow> (A,w) \<in> R \<Longrightarrow> \<exists>a u. w = a#u"
sorry

definition "rhs1 = fst o snd"
definition "Rhs1 R = rhs1 ` Lnt R"

lemma lem: "A - {x. P x} = {x\<in>A. \<not>P x}"
by auto

lemma Rhs1_subsetD: "Rhs1 R \<subseteq> M \<Longrightarrow> (A, N B # w) \<in> R \<Longrightarrow> B \<in> M"
sorry

lemma Lnt_subset: "R \<subseteq> S \<Longrightarrow> Lnt R \<subseteq> Lnt S"
  by (auto simp: Lnt_def)

lemma Rhs1_subset: "R \<subseteq> S \<Longrightarrow> Rhs1 R \<subseteq> Rhs1 S"
  by (auto simp: Rhs1_def Lnt_def)

lemma Rhs1_Un: "Rhs1 (R \<union> S) = Rhs1 R \<union> Rhs1 S"
  by (auto simp: Rhs1_def Lnt_def)

fun starts_with where "starts_with A (N B # w) \<longleftrightarrow> A = B"
  | "starts_with _ _ = False"

lemma starts_with_iff: "starts_with A w \<longleftrightarrow> (\<exists>v. w = N A # v)"
  apply (cases "(A,w)" rule: starts_with.cases) by auto

definition "solved_list R As \<longleftrightarrow>
  (\<forall> B \<in> set As. \<forall>(A,w) \<in> set R. \<not>starts_with B w)"

definition "solved R As \<longleftrightarrow>
  (\<forall>B \<in> As. \<forall>(A,w) \<in> R. \<not>starts_with B w)"

lemma solvedI:
  assumes "\<And>B A w. B \<in> As \<Longrightarrow> (A,w) \<in> R \<Longrightarrow> \<not> starts_with B w"
  shows "solved R As"
  using assms by (auto simp: solved_def)

lemma solved: "solved (set R) (set As) = solved_list R As"
  by (auto simp: solved_def solved_list_def)

lemma solved_not:
  "solved R As \<Longrightarrow> A \<in> As \<Longrightarrow> (B,N A#w) \<notin> R"
  apply (auto simp: solved_def split: prod.splits)
  by (metis starts_with.simps(1))

definition Nts where "Nts R = concat [A#[B. N B \<leftarrow> w]. (A,w) \<leftarrow> R]"

definition Nt where "Nt R = (\<Union>(A,w)\<in>R. {A}\<union>{B. N B \<in> set w})"

lemma set_Nts_def: "set (Nts R) = Nt (set R)"
  by (auto simp: Nts_def Nt_def)

definition "diff_list = fold removeAll"

lemma set_diff_list[simp]: "set(diff_list xs ys) = set ys - set xs"
unfolding diff_list_def
proof(induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by auto
qed 

definition unwind_new_list where
  "unwind_new_list R A A' =
  concat [[(A',w), (A',w@[N A'])]. (B,N C # w) \<leftarrow> R, B = A \<and> C = A \<and> w \<noteq> []]"

definition unwind_old_list where
  "unwind_old_list R A A' = (
  let X = [(B,w) \<leftarrow> R. starts_with A w] in
  diff_list X R @
  [(A, w@[N A']). (B,w) \<leftarrow> R, B = A \<and> \<not> starts_with A w] @
  [(B,w@N A'#tl v). (B,v) \<leftarrow> R, (C,w) \<leftarrow> diff_list X R, starts_with A v \<and> A \<noteq> B \<and> C = A ])"

definition "unwind_list R A A' = unwind_old_list R A A' @ unwind_new_list R A A'"

definition unwind_old where
  "unwind_old R A A' = (
  let X = {(B, N A # w) | B w. (B, N A # w) \<in> R} in
  R - X \<union> {(A, w@[N A']) |w. (A,w) \<in> R - X} \<union>
{(B, w@ N A' # v) |B v w.
 (B, N A # v) \<in> R \<and> A \<noteq> B \<and> (A,w) \<in> R - X })"

value "unwind_old_list [(2, [N 1::(int,int)symb])] 1 2"
lemma set_unwind_old_list: "set (unwind_old_list R A A') = unwind_old (set R) A A'"
  apply (auto simp: unwind_old_list_def unwind_old_def starts_with_iff
Cons_eq_append_conv )sorry

lemma eps_free_unwind_old_list:
  assumes "eps_free R"
  shows "eps_free (unwind_old R A A')"
  using assms
  by (auto simp: unwind_old_def eps_free_def)

definition unwind_new where
  "unwind_new R A A' = (
  \<Union>{{(A',w), (A',w@[N A'])} | w. (A,N A # w) \<in> R \<and> w \<noteq> []})"

lemma set_unwind_new_list: "set (unwind_new_list R A A') = unwind_new (set R) A A'"
  apply (auto simp: unwind_new_list_def unwind_new_def starts_with_iff)
  apply (metis insertI1)
  by (metis insert_subset subset_insertI)

definition "unwind R A A' =
  unwind_old R A A' \<union> unwind_new R A A'"

lemma set_unwind: "set (unwind_list R A A') = unwind (set R) A A'"

  sorry

lemma eps_free_unwind_new:
  "eps_free (unwind_new R A A')"
  by (auto intro!: eps_freeI simp: unwind_new_def)

definition "loop_free R A = (\<forall>(B,w) \<in> R. B = A \<longrightarrow> \<not> starts_with A w)"

lemma loop_freeI:
  assumes "\<And>w. (A,w) \<in> R \<Longrightarrow> \<not>starts_with A w" shows "loop_free R A"
  using assms by (auto simp: loop_free_def)

lemma loop_freeD: "loop_free R A \<Longrightarrow> (A, N A # w) \<notin> R"
  by (auto simp: loop_free_def)

definition "loop_free_list R A = (\<forall>(B,w) \<in> set R. B = A \<longrightarrow> \<not> starts_with A w)"

lemma loop_free_Un: "loop_free (R \<union> S) A \<longleftrightarrow> loop_free R A \<and> loop_free S A"
  by (auto simp:loop_free_def)

lemma in_Nt_if_starts_with: "(A, w) \<in> R \<Longrightarrow> starts_with B w \<Longrightarrow> B \<in> Nt R"
  apply (cases "(B,w)" rule: starts_with.cases)
    apply (auto simp: Nt_def split: prod.split)
  by (metis list.set_intros(1) prod.inject)
  
lemma loop_free_unwind_old_list:
  assumes "A' \<noteq> A"
  shows "loop_free (unwind_old R A A') A"
  using assms by (auto simp: loop_free_def starts_with_iff unwind_old_def Cons_eq_append_conv)

lemma solved_list_unwind_old_list:
  assumes "solved R As"
    and "eps_free R"
  shows "solved (unwind_old R A A') (insert A As)"
  using assms
  by (force simp: Cons_eq_append_conv solved_def starts_with_iff unwind_old_def
      eps_free_Nil
      split: prod.splits)


lemma solved_Un: "solved (R \<union> S) As \<longleftrightarrow> solved R As \<and> solved S As"
  by (auto simp:solved_def)

lemma loop_free_unwind_new_list:
  assumes "A' \<noteq> A"
  shows "loop_free (unwind_new R A A') A"
  using assms by (auto simp: loop_free_def starts_with_iff unwind_new_def Cons_eq_append_conv)

lemma loop_free_unwind:
  assumes "A' \<noteq> A"
  shows "loop_free (unwind R A A') A"
  using loop_free_unwind_old_list[OF assms] loop_free_unwind_new_list[OF assms]
  by (auto simp: unwind_def loop_free_Un)

definition Rhs1s where "Rhs1s R = [A. (B,N A # w) \<leftarrow> R]"

lemma set_Rhs1s: "set (Rhs1s R) = Rhs1 (set R)"
  by (auto simp: Rhs1s_def Rhs1_def Lnt_def rhs1_def image_Collect)

definition "eps_free_list R = (\<forall>(A,w) \<in> set R. w \<noteq> [])"

definition Rex :: "(int,int) prod list"
  where "Rex = [
  (1,[N 2, N 2]), (1, [T 0]),
  (2, [N 2, N 2, N 2]), (2, [T 0, N 2]), (2, [T 1])]"

definition Rex2 :: "(int,int) prod list"
  where "Rex2 = [
  (1, [N 2, T 0]),
  (2, [N 1, T 2]), (2, [T 1, N 1]), (2, [T 3])]"

value "unwind_list Rex 2 3"

(*
definition "expand_list_rec R A = (
  let X = filter (\<lambda>(B,w). starts_with A w) R in
  diff_list X R @ [(B,v@w). (B,N C # w) \<leftarrow> R, C = A, (D,v) \<leftarrow> R, D = A]
)"

value "expand_list_rec Rex2 1"

lemma
  assumes "eps_free_list R"
    and "\<forall>(B,w) \<in> set R. B = A \<longrightarrow> \<not>starts_with A w"
    and "(B,w) \<in> set (expand_list_rec R A)"
  shows "\<not>starts_with A w"
  sorry
*)

fun hdnt where
    "hdnt (N A#w) = Some A"
  | "hdnt _ = None"

definition "expand_list R S As =
  [(B,w). (B,w) \<leftarrow> R, hdnt w \<notin> Some ` set As] @
  [(B,v@w). (B,N C # w) \<leftarrow> R, C \<in> set As, (D,v) \<leftarrow> S, D = C]"

definition "expand R S As =
  {(B,w) \<in> R. hdnt w \<notin> Some ` As} \<union>
  {(B,v@w) |B v w. \<exists>C \<in> As. (B,N C # w) \<in> R \<and> (C,v) \<in> S}"

lemma set_expand_list: "set (expand_list R S As) = expand (set R) (set S) (set As)"
  by (auto simp: expand_list_def expand_def)

lemma expand_loop_free:
  assumes "A \<notin> As"
    and "solved S {A}"
    and "eps_free S"
    and "loop_free R A"
  shows "loop_free (expand R S As) A"
  using assms
  by (auto simp: expand_def Cons_eq_append_conv solved_not
      starts_with_iff eps_free_Nil
      loop_free_def split:prod.splits)

lemma expand_list_solved_list:
  assumes "solved S As"
    and "eps_free S"
  shows "solved (expand R S As) As"
  using assms
  by (fastforce simp: solved_def expand_def starts_with_iff
      Cons_eq_append_conv eps_free_Nil
      split: prod.splits)

lemma expand_list_solved_list2:
  assumes "solved R As"
    and "eps_free R"
  shows "solved (expand R R Bs) As"
  using assms
  by (force simp: solved_def expand_def starts_with_iff
      Cons_eq_append_conv eps_free_Nil
      split: prod.splits)

lemma eps_free_expand_list:
  assumes "eps_free R" "eps_free S"
  shows "eps_free (expand R S Bs)"
  using assms
  by (auto intro!: eps_freeI simp: expand_def eps_free_Nil)

definition Rex3 :: "(int,int) prod list" where "Rex3 = [
(0,[N 0]), (1,[N 1, N 0])]"

value "unwind_new_list Rex3 1 2"

value "expand_list (unwind_new_list Rex3 1 2) (unwind_old_list Rex3 1 2) [0]"

text \<open>The following is true without assuming solved_listness of \<open>As\<close>,
because of the definition of \<open>expand\<close>.\<close>

lemma hd_in_Nt: "(A,N B#w) \<in> R \<Longrightarrow> B \<in> Nt R"
  apply (auto simp: Nt_def split: prod.splits)
  by (metis list.set_intros(1) prod.inject)

lemma hd2_in_Nt: "(A,x#N B#w) \<in> R \<Longrightarrow> B \<in> Nt R"
  apply (auto simp: Nt_def split: prod.splits)
  by (metis list.set_intros(1,2) prod.inject)
  

lemma solved_list_expand_list_unwind_new_list:
  assumes "A' \<notin> As"
    and "eps_free R" "A' \<notin> Nt R"
    and "solved R As"
  shows "solved (expand (unwind_new R A A')
 (unwind_old R A A') (insert A As))
  (insert A' (insert A As))"
  using assms
  apply (intro solvedI)
  by (auto simp: expand_def solved_not
      unwind_new_def unwind_old_def neq_Nil_conv starts_with_iff
      Cons_eq_append_conv eps_free_Nil hd_in_Nt hd2_in_Nt)


text \<open>Instead, preservation of the language requires solved_listness
of \<open>R\<close> with respect to \<open>As\<close>.\<close>

lemma Lang_expand:
  assumes "solved R As"
  shows "Lang (S \<union> expand R S As) = Lang (S \<union> R)"
  sorry

definition "unwind_expand_list R As A A' =
 unwind_old_list R A A' @ expand_list (unwind_new_list R A A') (unwind_old_list R A A') (A#As)"

definition "unwind_expand R As A A' =
  unwind_old R A A' \<union>
  expand (unwind_new R A A') (unwind_old R A A') (insert A As)"

lemma set_unwind_expand_list: "set (unwind_expand_list R As A A') = unwind_expand (set R) (set As) A A'"
  by (auto simp: unwind_expand_def unwind_expand_list_def set_unwind_old_list set_unwind_new_list set_expand_list)

lemma solved_list_unwind_expand_list:
  assumes ef: "eps_free R" and A': "A' \<notin> Nt R \<union> As"
    and so: "solved R As"
  shows "solved (unwind_expand R As A A') (insert A (insert A' As))"
proof-
  have so2: "solved R (insert A' As)"
    using so A' 
    by (auto simp: solved_def in_Nt_if_starts_with split: prod.splits)
  show ?thesis
  apply (auto simp: unwind_expand_def solved_Un)
     apply (rule solved_list_unwind_old_list[OF so2 ef])
    apply (subst insert_commute)
    apply (rule solved_list_expand_list_unwind_new_list)
    using assms by auto
qed

definition step_list
  where "step_list R As A A' =
 expand_list (unwind_expand_list R As A A') (unwind_expand_list R As A A') [A]"

definition
  "step R As A A' =
 expand (unwind_expand R As A A') (unwind_expand R As A A') {A}"

lemma set_step_list: "set (step_list R As A A') = step (set R) (set As) A A'"
  by (auto simp: step_list_def step_def set_expand_list set_unwind_expand_list)

lemma solved_list_insert:
  assumes "solved R As"
    and "\<forall>(B,w) \<in> R. \<not>starts_with A w"
  shows "solved R (insert A As)"
  using assms
  by (auto simp: solved_def)

lemma eps_free_unwind_expand:
  assumes "eps_free R"
  shows "eps_free (unwind_expand R As A A')"
proof-
  note 1 =  eps_free_unwind_old_list[OF assms]
  with eps_free_expand_list[OF this eps_free_unwind_new]
  show ?thesis
  apply (auto intro!:eps_freeI simp: eps_free_Nil unwind_expand_def)
    by (smt (verit) eps_free_Nil eps_free_expand_list eps_free_unwind_new)
qed

lemma loop_free_expand_list:
  assumes "loop_free R A"
    and "solved S (insert A As)"
    and "eps_free S"
  shows "loop_free (expand R S As) A"
  using assms
  by (auto intro!:loop_freeI dest: loop_freeD solved_not
      simp: expand_def starts_with_iff append_eq_Cons_conv eps_free_Nil)

lemma loop_free_unwind_expand:
  assumes A': "A' \<noteq> A"
    and so: "solved R As"
    and ef: "eps_free R"
  shows "loop_free (unwind_expand R As A A') A"
proof-
  from solved_list_unwind_old_list[OF so ef]
  have 1: "solved (unwind_old R A A') (insert A As)"
    by auto
  then have 2: "solved (unwind_old R A A') As"
    by (auto simp: solved_def)
  show ?thesis
  apply (auto simp: unwind_expand_def loop_free_Un)
   apply (metis A' loop_free_unwind_old_list)
    apply (rule loop_free_expand_list[OF loop_free_unwind_new_list[OF A']])
    apply (simp)
     apply (rule 1)
    using eps_free_unwind_old_list[OF ef].
qed

theorem solved_list_step:
  assumes ef: "eps_free R" and notin: "A' \<notin> Nt R \<union> As"
    and neq: "A' \<noteq> A"
    and so: "solved R As"
  shows "solved (step R As A A') (insert A (insert A' As))"
proof-
  show ?thesis
    apply (auto simp: step_def)
    by (metis ef eps_free_unwind_expand expand_list_solved_list2 notin so solved_list_unwind_expand_list)
qed

fun realtime_list where
  "realtime_list R (A#As) (A'#As') = step_list (realtime_list R As As') (As@As') A A'"
| "realtime_list R _ _ = R"

context fixes R :: "('n,'t) prods" begin
fun realtime where
  "realtime (A#As) (A'#As') =
  step (realtime As As') (set (As@As')) A A'"
| "realtime _ _ = R"

end

lemma solved_list_if_disj:
  assumes disj: "set As' \<inter> Nt R = {}"
  shows "solved R (set As')"
  using disj
  by (auto simp: solved_def dest:in_Nt_if_starts_with)


lemma Nt_realtime_list: "Nt (realtime R As As') \<subseteq> Nt R \<union> set As \<union> set As'"
  sorry

context
  fixes R :: "('n,'t)prods"
  assumes ef: "eps_free R"
begin

lemma eps_free_realtime_list:
  shows "eps_free (realtime R As As')"
proof (induction As As' rule: realtime.induct)
  case (1 A As A' As')
  then show ?case apply auto sorry
next
  case ("2_1" uv)
  then show ?case sorry
next
  case ("2_2" uu)
  then show ?case sorry
qed

lemma solved_realtime:
  assumes "eps_free R"
    and "length As \<le> length As'"
    and "distinct (As @ As')" and "set As' \<inter> Nt R = {}"
  shows "solved (realtime R As As') (set As \<union> set As')"
  using assms
proof (induction As As' rule: realtime.induct)
  case (1 A As A' As')
  with Nt_realtime_list[of R]
    solved_list_step[where A=A and A'=A' and As = "set As \<union> set As'" and R ="realtime R As As'"]
  show ?case by (auto intro!: simp: eps_free_realtime_list insert_commute) 
next
  case ("2_1" As')
  with solved_list_if_disj show ?case by auto
next
  case ("2_2" As)
  then show ?case by (auto simp: solved_def)
qed

end

value "unwind_expand_list [(1,[N 1 :: (int,int)symb, N 1])] [] 1 2"

theorem GNF:
fixes R :: "('n,'t)prods" and new :: "'n set \<Rightarrow> 'n"
assumes "\<And>X. finite X \<Longrightarrow> new (X) \<notin> X"
assumes "finite R" and "eps_free R" and "Rhs1 R \<subseteq> set As" "distinct As"
shows "\<exists>R'::('n ,'t)prods. Lang S R' = Lang S R \<and> rtps R'"
  oops

end