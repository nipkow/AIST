theory GNF
imports CFG
begin

fun rt :: "('n,'t)syms \<Rightarrow> bool" where
"rt [] = True" |
"rt (Tm _ # _) = True" |
"rt _ = False"

definition rtps :: "('n,'t)prodS \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> ps. rt(snd p))"

definition Lnt :: "('n, 't) prodS \<Rightarrow> ('n * 'n * ('n,'t)syms)set" where
"Lnt P = {(A,B,w). (A, Nt B # w) \<in> P}"

lemma [code]: "Lnt P = \<Union> ((\<lambda>(A,w). case w of Nt B#v \<Rightarrow> {(A,B,v)} | _ \<Rightarrow> {}) ` P)"
  by (auto simp: Lnt_def split: list.splits sym.splits)

definition rule where "rule = (\<lambda>(A, B, w). (A, Nt B # w))"

lemma Lnt_Un: "Lnt (A \<union> B) = Lnt A \<union> Lnt B"
by(auto simp: Lnt_def)

lemma Lnt_Diff: "Lnt (A - B) = Lnt A - Lnt B"
by(auto simp: Lnt_def)

lemma Lnt_rule: "Lnt(rule ` S) = S"
by(auto simp: Lnt_def rule_def image_def split:prod.splits)

(*
fun lnt :: "('n,'t)prod \<Rightarrow> 'n option" where
"lnt(_,Nt A # _) = Some A" |
"lnt _ = None"

definition "has_lnt p = (\<exists>A u. snd p = Nt A # u)"

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

lemma Rhs1_subsetD: "Rhs1 R \<subseteq> M \<Longrightarrow> (A, Nt B # w) \<in> R \<Longrightarrow> B \<in> M"
sorry

lemma Lnt_subset: "R \<subseteq> S \<Longrightarrow> Lnt R \<subseteq> Lnt S"
  by (auto simp: Lnt_def)

lemma Rhs1_subset: "R \<subseteq> S \<Longrightarrow> Rhs1 R \<subseteq> Rhs1 S"
  by (auto simp: Rhs1_def Lnt_def)

lemma Rhs1_Un: "Rhs1 (R \<union> S) = Rhs1 R \<union> Rhs1 S"
  by (auto simp: Rhs1_def Lnt_def)

fun starts_with where
  "starts_with _ [] = False" |
  "starts_with A (a # w) \<longleftrightarrow> a = Nt A"

lemma starts_with_iff: "starts_with A w \<longleftrightarrow> (\<exists>v. w = Nt A # v)"
  apply (cases "(A,w)" rule: starts_with.cases) by auto

definition "ends_with A w = (\<exists>v. w = v @ [Nt A])"

lemma ends_with_iff_starts_with_rev: "ends_with A w \<longleftrightarrow> starts_with A (rev w)"
  apply (auto simp: starts_with_iff ends_with_def)
  by (metis rev_rev_ident)

definition "loop R A = {(A,Nt A # w) | w. (A, Nt A # w) \<in> R \<and> w \<noteq> []}"

definition "right_loop R A = {(A,w@[Nt A]) | w. (A, w@[Nt A]) \<in> R \<and> w \<noteq> []}"

lemma right_loop_eq_loop:
  "right_loop R A = map_prod id rev ` loop (map_prod id rev ` R) A"
  by (force simp: right_loop_def loop_def Cons_eq_rev_iff)

definition "loop_free R A = (\<forall>(B,w) \<in> R. B = A \<longrightarrow> \<not> starts_with A w)"

lemma loop_freeI:
  assumes "\<And>w. (A,w) \<in> R \<Longrightarrow> \<not>starts_with A w" shows "loop_free R A"
  using assms by (auto simp: loop_free_def)

lemma loop_freeD: "loop_free R A \<Longrightarrow> (A, Nt A # w) \<notin> R"
  by (auto simp: loop_free_def)

definition "loop_free_list R A = (\<forall>(B,w) \<in> set R. B = A \<longrightarrow> \<not> starts_with A w)"

lemma loop_free_Un: "loop_free (R \<union> S) A \<longleftrightarrow> loop_free R A \<and> loop_free S A"
  by (auto simp:loop_free_def)

definition "solved_list R As \<longleftrightarrow>
  (\<forall>A \<in> set As. \<forall>(B,w) \<in> set R. \<not>starts_with A w)"

definition "solved R As \<longleftrightarrow>
  (\<forall>A \<in> As. \<forall>(B,w) \<in> R. \<not>starts_with A w)"

lemma solvedI:
  assumes "\<And>A B w. A \<in> As \<Longrightarrow> (B,w) \<in> R \<Longrightarrow> \<not> starts_with A w"
  shows "solved R As"
  using assms by (auto simp: solved_def)

lemma solved: "solved (set R) (set As) = solved_list R As"
  by (auto simp: solved_def solved_list_def)

lemma solved_not:
  "solved R As \<Longrightarrow> A \<in> As \<Longrightarrow> (B,Nt A#w) \<notin> R"
  by (fastforce simp: solved_def starts_with_iff split: prod.splits)

definition nonterminals where "nonterminals R = concat [A#[B. Nt B \<leftarrow> w]. (A,w) \<leftarrow> R]"

definition Nonterminal where "Nonterminal R = (\<Union>(A,w)\<in>R. {A}\<union>{B. Nt B \<in> set w})"

fun hdnt where
    "hdnt (Nt A#w) = Some A"
  | "hdnt _ = None"

lemma set_nonterminals_def: "set (nonterminals R) = Nonterminal (set R)"
  by (auto simp: nonterminals_def Nonterminal_def)

definition "diff_list = fold removeAll"

lemma set_diff_list[simp]: "set(diff_list xs ys) = set ys - set xs"
  by (induction xs arbitrary: ys, auto simp: diff_list_def)

definition unwind_new where
  "unwind_new R A A' = (
  \<Union>{{(A',w), (A',w@[Nt A'])} | w. (A,Nt A # w) \<in> R \<and> w \<noteq> []})"

definition unwind_new_list where
  "unwind_new_list R A A' =
  concat [[(A',w), (A',w@[Nt A'])]. (B,Nt C # w) \<leftarrow> R, B = A \<and> C = A \<and> w \<noteq> []]"

lemma set_unwind_new_list: "set (unwind_new_list R A A') = unwind_new (set R) A A'"
  apply (auto simp: unwind_new_list_def unwind_new_def starts_with_iff)
  apply (metis insertI1)
  by (metis insert_subset subset_insertI)

definition unwind_old where
  "unwind_old R A A' = (
  let X = {(A, Nt A # w) | w. (A, Nt A # w) \<in> R} in
  R - X \<union> {(A, w@[Nt A']) |w. (A,w) \<in> R - X})"

definition unwind_old_list where
  "unwind_old_list R A A' = (
  let X = [(B,w) \<leftarrow> R. B = A \<and> starts_with A w] in
  diff_list X R @
  [(A, w@[Nt A']). (B,w) \<leftarrow> R, B = A \<and> \<not> starts_with A w])"

lemma set_unwind_old_list: "set (unwind_old_list R A A') = unwind_old (set R) A A'"
  by (auto simp: unwind_old_def unwind_old_list_def starts_with_iff)

definition unwind where
  "unwind R A A' = unwind_new R A A' \<union> unwind_old R A A'"

definition unwind_list where
  "unwind_list R A A' = unwind_new_list R A A' @ unwind_old_list R A A'"

lemma set_unwind_list: "set (unwind_list R A A') = unwind (set R) A A'"
  by (auto simp: unwind_list_def unwind_def set_unwind_old_list set_unwind_new_list)

lemma eps_free_unwind_old: "eps_free R \<Longrightarrow> eps_free (unwind_old R A A')"
  by (auto simp: eps_free_def unwind_old_def)

definition unwind_old_expand_list where
  "unwind_old_expand_list R A A' = (
  let X = [(B,w) \<leftarrow> R. starts_with A w] in
  diff_list X R @
  [(A, w@[Nt A']). (B,w) \<leftarrow> R, B = A \<and> \<not> starts_with A w] @
  concat [[(B,w@tl v),(B,w@Nt A'#tl v)]. (B,v) \<leftarrow> R, (C,w) \<leftarrow> diff_list X R, starts_with A v \<and> A \<noteq> B \<and> C = A ])"

definition unwind_old_expand where
  "unwind_old_expand R A A' = (
  let X = {(B, Nt A # w) | B w. (B, Nt A # w) \<in> R} in
  R - X \<union> {(A, w @ [Nt A']) |w. (A,w) \<in> R - X} \<union>
  \<Union>{{(B, w@v), (B, w @ Nt A' # v)} |B v w.
 (B, Nt A # v) \<in> R \<and> A \<noteq> B \<and> (A,w) \<in> R - X })"

lemma set_unwind_old_expand_list: "set (unwind_old_expand_list R A A') = unwind_old_expand (set R) A A'"
  apply (auto simp: unwind_old_expand_def unwind_old_expand_list_def starts_with_iff)
  sorry

definition "expand R S As =
  {(A, b # w) |A b w. (A, b # w) \<in> R \<and> b \<notin> Nt ` As} \<union>
  {(A,v@w) |A v w. \<exists>B \<in> As. (A,Nt B # w) \<in> R \<and> (B,v) \<in> S}"

lemma derive_expand_iff:
  shows "expand R S As \<turnstile> u \<Rightarrow> v \<longleftrightarrow>
  (\<exists>u1 u2 A b w. (A, b # w) \<in> R \<and> u = u1 @ Nt A # u2 \<and>
  (b \<notin> Nt ` As \<and> v = u1 @ b # w @ u2 \<or>
  (\<exists>(C,r) \<in> S. C \<in> As \<and> b = Nt C \<and> v = u1 @ r @ w @ u2)))"
  by (fastforce simp: Bex_def expand_def derive_iff split:prod.splits)

definition "expand_list R S As =
  [(A, b # w). (A, b # w) \<leftarrow> R, b \<notin> Nt ` set As] @
  [(A,v@w). (A, Nt B # w) \<leftarrow> R, B \<in> set As, (C,v) \<leftarrow> S, C = B]"

lemma set_expand_list: "set (expand_list R S As) = expand (set R) (set S) (set As)"
  by (auto simp: expand_list_def expand_def)

definition "unwind_expand R As A A' =
  expand (unwind_new R A A') (unwind_old_expand R A A') (insert A As) \<union>
  unwind_old_expand R A A'"

definition "unwind_expand_list R As A A' =
  expand_list (unwind_new_list R A A') (unwind_old_expand_list R A A') (A#As) @
  unwind_old_expand_list R A A'"

lemma set_unwind_expand_list:
  "set (unwind_expand_list R As A A') = unwind_expand (set R) (set As) A A'"
  by (simp add: unwind_expand_list_def unwind_expand_def
      set_expand_list set_unwind_old_expand_list set_unwind_new_list)

lemma unwind_old_expand:
  assumes ef: "eps_free R" and "A' \<noteq> A"
  shows "unwind_old_expand R A A' = expand (unwind_old R A A') (unwind_old R A A') {A}"
  using assms
  apply (simp add: unwind_old_expand_def unwind_old_def expand_def)
  apply safe
                  apply(auto dest: eps_freeE_Cons)[2]
                apply blast
               apply (metis Cons_eq_appendI append_assoc eq_Nil_appendI)
              apply blast
             apply blast
            apply blast
           apply (auto; blast)[]
          apply (auto; blast)[]
         apply (auto)[]
         apply (metis append_eq_Cons_conv list.inject sym.inject(1))
        apply (metis (no_types, lifting) Cons_eq_append_conv list.inject sym.inject(1))
       apply blast
      apply blast
     apply (metis (mono_tags, lifting) Cons_eq_appendI append_assoc eps_freeE_Cons list.inject)
    apply (metis (no_types, opaque_lifting) Cons_eq_appendI eps_freeE_Cons list.inject)
   apply (metis (no_types, lifting) append_eq_Cons_conv eps_free_Nil)
  apply auto[]
  by (metis append_eq_Cons_conv eps_free_Nil)

lemma expand_right_Un_id:
  assumes "As \<inter> fst ` S = {}"
  shows "expand R (S \<union> U) As = expand R U As"
  using assms
  apply (auto simp: expand_def)
  by (metis disjoint_iff fst_eqD imageI)

lemma expand_unwind_eq_expand_unwind_old:
  assumes "A' \<noteq> A"
  shows "expand R' (unwind R A A') {A} = expand R' (unwind_old R A A') {A}"
  using assms
  apply (unfold unwind_def)
  apply (subst expand_right_Un_id)
  by (auto simp: unwind_new_def)

lemma unwind_old_expand_2:
  assumes ef: "eps_free R" and A': "A' \<noteq> A"
  shows "unwind_old_expand R A A' = expand (unwind_old R A A') (unwind R A A') {A}"
  apply (unfold expand_unwind_eq_expand_unwind_old[OF A'])
  using unwind_old_expand[OF assms].

lemma expand_Un: "expand (R \<union> R') S As = expand R S As \<union> expand R' S As"
  by (fastforce simp: expand_def)

lemma expand_solved:
  assumes so: "solved R As" and ef: "eps_free R"
  shows "expand R S As = R"
  using so eps_freeE_Cons[OF ef]
  by (fastforce simp: starts_with_iff solved_def expand_def)

lemma eps_free_expand:
  assumes "eps_free R" "eps_free S"
  shows "eps_free (expand R S As)"
  using assms
  by (auto simp: eps_free_def expand_def split: prod.splits)

definition "unwind_expand' R As A A' = (
  let R' = unwind R A A' in
  expand R' R' (insert A As))"

definition "unwind_expand'_list R As A A' = (
  let R' = unwind_list R A A' in
  expand_list R' R' (A#As))"

value "unwind_old_expand_list [(2, [Nt 1::(int,int)sym])] 1 2"

value "solved_list [(2::int, [Nt 2::(int,int)sym, Nt 1]), (1, [Nt 2])] [1]"

lemma expand_derives_sound:
  assumes ef: "eps_free R"
  assumes "expand R S As \<union> S \<turnstile> u \<Rightarrow>* v"
  shows "R \<union> S \<turnstile> u \<Rightarrow>* v"
  using assms(2)
proof (induction)
  case base
  then show ?case by auto
next
  case (step y z)
  from \<open>expand R S As \<union> S \<turnstile> y \<Rightarrow> z\<close>[unfolded Un_derive]
  have "R \<union> S \<turnstile> y \<Rightarrow>* z"
    apply (auto simp add: )defer
     apply (meson Un_derive rtranclp.simps)
    apply (auto simp: derive_expand_iff)
     apply (rule r_into_rtranclp)
    using derive.intros Un_derive apply fastforce
    subgoal premises Aw  for u1 u2 A w B v
      apply (rule rtranclp_trans[of _ _ "u1@Nt B # w@u2",OF r_into_rtranclp r_into_rtranclp])
      using Aw Un_derive derive.intros apply fastforce
    proof-
      from Aw
      have "S \<turnstile> u1 @ Nt B # w @ u2 \<Rightarrow> u1 @ v @ w @ u2"
        using derive.simps by fastforce
      with Aw(1-5) show "R \<union> S \<turnstile> u1 @ Nt B # w @ u2 \<Rightarrow> u1 @ v @ w @ u2"
        using Un_derive ef eps_freeE_Cons by fastforce
    qed
    done
  with step.IH show ?case by auto
qed

fun leftmost_nt where "leftmost_nt [] = None" |
"leftmost_nt (Nt A # w) = Some A" |
"leftmost_nt (Tm c # w) = leftmost_nt w"

lemma leftmost_nt_map_Tm_append: "leftmost_nt (map Tm u @ v) = leftmost_nt v"
  by (induction u, auto)

lemma leftmost_nt_map_Tm: "leftmost_nt (map Tm u) = None"
  using leftmost_nt_map_Tm_append[of _ "[]"] by auto

lemma expand_derivels:
  assumes ef: "eps_free R"
    and RAs: "fst ` R \<inter> As = {}"
    and der: "R \<union> S \<turnstile> u \<Rightarrow>l* v" and vAs: "leftmost_nt v \<notin> Some ` As"
  shows "expand R S As \<union> S \<turnstile> u \<Rightarrow>l* v"
proof-
  from der
  obtain n where "R \<union> S \<turnstile> u \<Rightarrow>l(n) v"
    by (metis rtranclp_imp_relpowp)
  then show ?thesis
  proof (induction n arbitrary: u rule: less_induct)
    case (less n)
    then show ?case
    proof (cases n)
      case 0
      then show ?thesis using less.prems by auto
    next
      case [simp]: (Suc m)
      then obtain z where uz: "R \<union> S \<turnstile> u \<Rightarrow>l z" and zv: "R \<union> S \<turnstile> z \<Rightarrow>l(m) v"
        by (metis less.prems relpowp_Suc_E2)
      from uz have "R \<turnstile> u \<Rightarrow>l z \<or> (S \<turnstile> u \<Rightarrow>l z)"
        by (simp add: Un_derivel)
      then show ?thesis
      proof
        assume "S \<turnstile> u \<Rightarrow>l z"
        then show ?thesis
          by (metis Suc Un_derivel zv converse_rtranclp_into_rtranclp less.IH lessI)
      next
        assume "R \<turnstile> u \<Rightarrow>l z"
        then obtain p A w y2 where [simp]: "u = map Tm p @ Nt A # y2"
          and Aw: "(A,w) \<in> R"
          and [simp]:"z = map Tm p @ w @ y2"
          by (meson derivel.cases)
        with ef obtain a w2 where [simp]: "w = a # w2" by (auto dest: eps_freeE_Cons)
        show ?thesis
        proof (cases "a \<in> Nt ` As")
          case True
          then obtain B where [simp]: "a = Nt B" and B: "B \<in> As" by auto
          from zv B vAs have "m \<noteq> 0"
            apply (intro notI)
            by (auto simp: leftmost_nt_map_Tm_append deriveln_map_Tm_append Cons_eq_map_conv append_eq_map_conv)
          then obtain l where [simp]: "m = Suc l"
            using old.nat.exhaust by auto
          from zv obtain z' where zz': "R \<union> S \<turnstile> z \<Rightarrow>l z'"
            and z'v: "R \<union> S \<turnstile> z' \<Rightarrow>l(l) v"
            by (metis \<open>m = Suc l\<close> relpowp_Suc_D2)
          from zz' have "\<exists>y. (B,y) \<in> R \<union> S \<and> z' = map Tm p @ y @ w2 @ y2"
            by (auto simp:derivel_iff append_eq_append_conv2 map_eq_append_conv append_eq_map_conv append_eq_Cons_conv Cons_eq_append_conv)
          then obtain y where By: "(B,y) \<in> R \<union> S"
            and [simp]: "z' = map Tm p @ y @ w2 @ y2" by auto
          with B RAs have "(B,y) \<in> S" by auto
          with Aw B
          have "(A,y@w2) \<in> expand R S As" by (auto simp: expand_def)
          then have "expand R S As \<turnstile> u \<Rightarrow>l z'"
            using derivel.intros by fastforce
          then have "expand R S As \<union> S \<turnstile> u \<Rightarrow>l z'" by (auto simp: Un_derivel)
          also from less.IH[OF _ z'v]
          have "expand R S As \<union> S \<turnstile> z' \<Rightarrow>l* v" by auto
          finally show ?thesis by auto
        next
          case False
          with Aw have "(A,w) \<in> expand R S As"
            by (auto simp: expand_def Cons_eq_append_conv)
          then have "expand R S As \<union> S \<turnstile> u \<Rightarrow>l z"
            apply auto
            by (metis Un_derivel append_Cons derivel.intros)
          then show ?thesis
            using less.IH
            by (metis Suc zv converse_rtranclp_into_rtranclp lessI)
        qed
      qed
    qed
  qed
qed

lemma expand_derives:
  assumes ef: "eps_free R"
    and RAs: "fst ` R \<inter> As = {}"
  shows "expand R S As \<union> S \<turnstile> u \<Rightarrow>* map Tm v \<longleftrightarrow> R \<union> S \<turnstile> u \<Rightarrow>* map Tm v"
  using expand_derives_sound[OF ef]
    expand_derivels[OF ef RAs, of S u \<open>map Tm v\<close>]
  by (auto simp: derivels_iff_derives leftmost_nt_map_Tm)

lemma Lang_expand:
  assumes ef: "eps_free R"
    and RAs: "fst ` R \<inter> As = {}"
  shows "Lang (expand R S As \<union> S) A = Lang (R \<union> S) A"
  unfolding Lang_def
  using expand_derives[OF assms]
  by auto

subsection \<open>Soundness of unwind\<close>

lemma unwind_expand':
  assumes "solved R As" and "A' \<noteq> A" and "A' \<notin> Nonterminal R \<union> As"
  shows "unwind_expand R As A A' = unwind_expand' R As A A'"
  sorry

lemma eps_free_unwind_new: "eps_free (unwind_new R A A')"
  sorry

lemma in_loop: "(B, w) \<in> loop R A \<longleftrightarrow>
  A = B \<and> (A,w) \<in> R \<and> (\<exists>w'. w = Nt A # w' \<and> w' \<noteq> [])"
  by (auto simp: loop_def)

lemma extract_loop:
  assumes "R \<turnstile> Nt A # u \<Rightarrow>l(n) v" and vA: "\<not>starts_with A v"
  shows "\<exists>n1 n2 u' w.
    n1 + n2 < n \<and>
    loop R A \<turnstile> [Nt A] \<Rightarrow>l(n1) Nt A # u' \<and>
    (A,w) \<in> R \<and> \<not>starts_with A w \<and> R \<turnstile> w@u'@u \<Rightarrow>l(n2) v"
  using assms(1)
proof (induction n arbitrary: u)
  case 0
  with vA show ?case by auto
next
  case (Suc n)
  from Suc.prems
  obtain w where Aw: "(A,w) \<in> R" and wuv: "R \<turnstile> w@u \<Rightarrow>l(n) v"
    by (auto simp: relpowp_Suc_left derivel_Nt_Cons)
  show ?case
  proof (cases "starts_with A w")
    case True
    then obtain w' where [simp]: "w = Nt A # w'" by (auto simp: starts_with_iff)
    from Suc.IH[OF wuv[simplified]]
    obtain n1 n2 u' x where len: "n1 + n2 < n"
      and n1: "loop R A \<turnstile> [Nt A] \<Rightarrow>l(n1) Nt A # u'"
      and AxR: "(A, x) \<in> R"
      and Ax: "\<not> starts_with A x"
      and n2: "R \<turnstile> x @ u' @ w' @ u \<Rightarrow>l(n2) v"
      by auto
    show ?thesis
    proof (cases "w' = []")
      case [simp]: True
      from len n1 AxR Ax n2 show ?thesis by force
    next
      case w': False
      from w' Aw have "(A,w) \<in> loop R A" by (auto simp: in_loop)
      then have "loop R A \<turnstile> [Nt A] \<Rightarrow>l Nt A # w'" by (auto simp: derivel_Nt_Cons)
      also from deriveln_append[OF n1, of w']
      have "loop R A \<turnstile> \<dots> \<Rightarrow>l(n1) Nt A # u' @ w'" by simp
      finally show ?thesis using len AxR Ax n2 by force
    qed
  next
    case False
    with Aw wuv show ?thesis
      apply (rule_tac x=0 in exI) by auto
  qed
qed

lemma extract_right_loop:
  assumes "R \<turnstile> u @ [Nt A] \<Rightarrow>r(n) v" and vA: "\<not>ends_with A v"
  shows "\<exists>n1 n2 u' w.
    n1 + n2 < n \<and>
    right_loop R A \<turnstile> [Nt A] \<Rightarrow>r(n1) u' @ [Nt A] \<and>
    (A,w) \<in> R \<and> \<not>ends_with A w \<and> R \<turnstile> u@u'@w \<Rightarrow>r(n2) v"
proof-
  from extract_loop[of n "map_prod id rev ` R" A "rev u" "rev v"] assms
  show ?thesis
    apply (auto simp: ends_with_iff_starts_with_rev right_loop_eq_loop derivern_iff_rev_deriveln
        image_image prod.map_comp o_def)
    apply (rule_tac x=n1 in exI)
    apply (rule_tac x=n2 in exI)
    apply auto
    apply (rule_tac x="rev u'" in exI)
    by auto
qed

lemma unwind_new_simulate_loop:
  assumes "loop R A \<turnstile> [Nt A] \<Rightarrow>l+ Nt A # vs"
  shows "unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>* vs"
  using assms
proof (induction "Nt A # vs" arbitrary: vs rule: tranclp_induct)
  case base
  then show ?case
    apply (intro conjI r_into_rtranclp)
    by (auto simp: derivel_iff Cons_eq_append_conv unwind_new_def loop_def
        derive_singleton)
next
  case (step y z)
  then obtain y' where [simp]: "y = Nt A # y'"
    by (auto simp: derivel_iff in_loop Cons_eq_append_conv)
  from step[simplified]
  have IH: "unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>* y'" by auto
  obtain v where AAv: "(A,Nt A # v) \<in> R"
    and [simp]: "z = v @ y'"
    and v0: "v \<noteq> []"
    using step(2)
    by (auto simp: derivel_iff Cons_eq_append_conv in_loop)
  from v0 have "(A', v @ [Nt A']) \<in> unwind_new R A A'"
      using AAv by (auto simp: unwind_new_def)
  with IH show ?case apply auto
    by (meson converse_rtranclp_into_rtranclp derive_singleton derives_prepend)
qed

(*AY: could be generalized so that A is not left-most nonterminal of v. *)
lemma unwind_complete:
  assumes "R \<turnstile> u \<Rightarrow>l(n) map Tm v"
  shows "unwind R A A' \<turnstile> u \<Rightarrow>* map Tm v"
  using assms
proof (induction n arbitrary: u v rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0
    with less.prems show ?thesis by auto
  next
    case [simp]: (Suc m)
    with less.prems obtain p B w u' v' where Bw: "(B,w) \<in> R"
      and [simp]: "u = map Tm p @ Nt B # u'" "v = p @ v'"
      and m: "R \<turnstile> w @ u' \<Rightarrow>l(m) map Tm v'"
      apply (auto simp: relpowp_Suc_left derivel_iff[of R u] Cons_eq_append_conv append_eq_Cons_conv
          split: prod.splits)
      by (smt (z3) append_eq_map_conv deriveln_map_Tm_append)
    show ?thesis
    proof (cases "B = A")
      case [simp]: True
      have "R \<turnstile> Nt A # u' \<Rightarrow>l w @ u'" using Bw
        by (auto simp: derivel_Nt_Cons)
      also note m
      finally have "R \<turnstile> Nt A # u' \<Rightarrow>l(n) map Tm v'" by simp
      from extract_loop[OF this]
      obtain n1 n2 u'' w'
        where len: "n1 + n2 < n"
          and n1: "loop R A \<turnstile> [Nt A] \<Rightarrow>l(n1) Nt A # u''"
          and Aw'R: "(A, w') \<in> R"
          and Aw': "\<not> starts_with A w'"
          and n2: "R \<turnstile> w' @ u'' @ u' \<Rightarrow>l(n2) map Tm v'" by (fastforce simp: starts_with_iff)
      from less.IH[OF _ n2] len
      have IH: "unwind R A A' \<turnstile> w' @ u'' @ u' \<Rightarrow>* map Tm v'" by auto
      show ?thesis
      proof (cases "n1 > 0")
        case True
        from Aw' Aw'R have "(A,w'@[Nt A']) \<in> unwind R A A'"
          by (auto simp: unwind_def unwind_old_def)
        then have "unwind R A A' \<turnstile> u \<Rightarrow> map Tm p @ w' @ Nt A' # u'"
          by (force simp: derive_iff)
        also have "unwind R A A' \<turnstile> \<dots> \<Rightarrow>* map Tm p @ w' @ u'' @ u'"
        proof (intro derives_prepend)
          from True n1 have "loop R A \<turnstile> [Nt A] \<Rightarrow>l+ Nt A # u''"
            by (metis tranclp_power)
          from unwind_new_simulate_loop[OF this, of A']
          have "unwind R A A' \<turnstile> [Nt A'] \<Rightarrow>* u''"
            by (metis Un_derive mono_rtranclp unwind_def)
          from derives_append[OF this]
          show "unwind R A A' \<turnstile> Nt A' # u' \<Rightarrow>* u'' @ u'" by simp
        qed
        also have "unwind R A A' \<turnstile> \<dots> \<Rightarrow>* map Tm v"
          by (simp add: IH derives_prepend)
        finally show ?thesis.
      next
        case False
        from Aw'R Aw' have "unwind R A A' \<turnstile> Nt A # u' \<Rightarrow> w' @ u'"
          by (auto intro!: derivel_imp_derive simp: derivel_Nt_Cons unwind_def unwind_old_def)
        with n1 IH False show ?thesis by (auto intro!:derives_prepend)
      qed
    next
      case False
      with Bw have "(B,w) \<in> unwind_old R A A'"
        by (auto simp: unwind_old_def)
      then have "unwind R A A' \<turnstile> u \<Rightarrow> map Tm p @ w @ u'"
        by (auto simp: derive_iff unwind_def)
      also from less.IH[OF _ m]
      have "unwind R A A' \<turnstile> w @ u' \<Rightarrow>* map Tm v'" by auto
      then have "unwind R A A' \<turnstile> map Tm p @ w @ u' \<Rightarrow>* map Tm v"
        using derives_prepend by auto
      finally show ?thesis.
    qed
  qed
qed

lemma derive_Cons_undef:
  assumes "a \<notin> Nt ` fst ` R"
  shows "R \<turnstile> a # u \<Rightarrow> v \<longleftrightarrow> (\<exists>v'. v = a # v' \<and> R \<turnstile> u \<Rightarrow> v')"
  using assms
  apply (auto simp: derive_iff Cons_eq_append_conv split:prod.splits)
    apply (metis fst_conv image_eqI)
   apply blast
  by (metis Pair_inject)

lemma derive_append_undef:
  assumes "nt p \<inter> fst ` R = {}"
  shows "R \<turnstile> p @ u \<Rightarrow> v \<longleftrightarrow> (\<exists>v'. v = p @ v' \<and> R \<turnstile> u \<Rightarrow> v')"
  using assms
proof (induction p arbitrary: u v)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then have "a \<notin> Nt ` fst ` R"
    by (fastforce simp: image_iff)
  note * = derive_Cons_undef[OF this]
  from Cons.prems have "nt p \<inter> fst ` R = {}" by (auto simp: nt_Cons)
  from Cons.IH[OF this]
  show ?case by (auto simp: *)
qed

lemma deriven_append_undef:
  assumes "nt p \<inter> fst ` R = {}"
  shows "R \<turnstile> p @ u \<Rightarrow>(n) v \<longleftrightarrow> (\<exists>v'. v = p @ v' \<and> R \<turnstile> u \<Rightarrow>(n) v')"
  using derive_append_undef[OF assms]
  by (induction n arbitrary: u; fastforce simp: relpowp_Suc_left relcomppI)

lemma fst_unwind_new: "fst ` unwind_new R A A' \<subseteq> {A'}"
  by (auto simp: unwind_new_def)

lemma Nt_in_set_iff_nt: "Nt A \<in> set w \<longleftrightarrow> A \<in> nt w"
  by (induction w, auto simp: nt_Cons split: sym.splits)

lemma unwind_new_only_last:
  assumes A'R: "A' \<notin> Nonterminal R"
    and "unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(n) u"
  shows "Nt A' \<notin> set u \<or> (\<exists>u'. u = u' @ [Nt A'] \<and> Nt A' \<notin> set u')"
  using assms(2)
proof (induction n arbitrary: u)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc.prems obtain y where A'y: "unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(n) y"
    and yu: "unwind_new R A A' \<turnstile> y \<Rightarrow> u"
    by (auto simp: relpowp_Suc_right derive_singleton)
  from yu have "Nt A' \<in> set y" by (auto simp: derive_iff unwind_new_def)
  with Suc.IH[OF A'y]
  obtain u' where [simp]: "y = u' @ [Nt A']" and A'u': "Nt A' \<notin> set u'" by auto
  with yu have "\<exists>v. (A',v) \<in> unwind_new R A A' \<and> u = u' @ v"
    by (auto simp: derive_iff unwind_new_def append_eq_append_conv2
        append_eq_Cons_conv Cons_eq_append_conv)
  with A'R A'u' show ?case
    by (auto simp: unwind_new_def append_eq_append_conv2 append_eq_Cons_conv Nonterminal_def)
qed

lemma unwind_new_sound:
  assumes A'R: "A' \<notin> Nonterminal R"
    and "unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(n) vs"
    and A'vs: "Nt A' \<notin> set vs"
  shows "R \<turnstile> [Nt A] \<Rightarrow>* Nt A # vs"
  using assms(2-)
proof (induction n arbitrary: vs)
  case 0
  then show ?case by auto
next
  let ?R' = "unwind_new R A A'"
  case (Suc n)
  then obtain y where y: "?R' \<turnstile> [Nt A'] \<Rightarrow> y" 
    and yvs: "?R' \<turnstile> y \<Rightarrow>(n) vs" by (auto simp: relpowp_Suc_left)
  show ?case
  proof (cases n)
    case 0
    with yvs have [simp]: "y = vs" by auto
    with Suc y have "\<exists>v. (A,Nt A # v) \<in> R \<and> y = v"
      apply (simp add: unwind_new_def derive_singleton)
      by (auto simp: Nonterminal_def split: prod.splits)
    then show ?thesis apply (intro r_into_rtranclp)
      by (auto simp: derive_singleton)
  next
    case (Suc m)
    with yvs have "Nt A' \<in> set y"
      by (auto simp: relpowp_Suc_left unwind_new_def derive_iff)
    with A'R y obtain v
      where AAv: "(A,Nt A # v) \<in> R" and [simp]: "y = v @ [Nt A']"
      by (auto simp: unwind_new_def derive_singleton Nonterminal_def split: prod.splits)
    from AAv A'R have A'v: "Nt A' \<notin> set v" by (auto simp: Nonterminal_def)
    with fst_unwind_new[of R A A']
    have "nt v \<inter> fst ` ?R' = {}" by (auto simp: Nt_in_set_iff_nt)
    from yvs[simplified] deriven_append_undef[OF this]
    obtain w where [simp]: "vs = v @ w" and A'w: "?R' \<turnstile> [Nt A'] \<Rightarrow>(n) w"
      by blast
    have "Nt A' \<notin> set w" using Suc.prems(2) by auto
    note Suc.IH[OF A'w this]
    also have "R \<turnstile> Nt A # w \<Rightarrow> Nt A # vs"
      using AAv derivel_Nt_Cons derivel_imp_derive by fastforce
    finally show ?thesis.
  qed
qed

lemma right_loop_unwind:
  assumes A'R: "A' \<notin> Nonterminal R"
  shows "right_loop (unwind R A A') A' \<subseteq> unwind_new R A A'"
  using assms
  by (auto simp: right_loop_def unwind_def unwind_old_def unwind_new_def Nonterminal_def)

lemma map_Tm_eq_map_Tm: "map Tm u = map Tm v \<longleftrightarrow> u = v"
  by (metis list.inj_map_strong sym.inject(2))

lemma deriver_mono: "R \<subseteq> S \<Longrightarrow> deriver R \<le> deriver S"
  by (force simp: deriver.simps)

lemma unwind_sound:
  assumes "unwind R A A' \<turnstile> u \<Rightarrow>r(n) v"
    and "Nt A' \<notin> set u"
    and "Nt A' \<notin> set v"
    and A'R: "A' \<notin> Nonterminal R"
  shows "R \<turnstile> u \<Rightarrow>* v"
  using assms(1-3)
proof (induction n arbitrary: u v rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0
    with less show ?thesis by auto
  next
    case [simp]: (Suc m)
    from less.prems obtain B w l r
      where BwR': "(B,w) \<in> unwind_old R A A'"
        and [simp]: "u = l @ Nt B # map Tm r"
        and m: "unwind R A A' \<turnstile> l @ w @ map Tm r \<Rightarrow>r(m) v"
      by (auto simp: relpowp_Suc_left append_eq_append_conv2 unwind_def unwind_new_def
          dest!:deriver_iff[THEN iffD1])
    from less.prems
    have A'l: "Nt A' \<notin> set l" by auto
    show ?thesis
    proof (cases "Nt A' \<in> set w")
      case True
      with BwR' A'R obtain w'
        where [simp]: "B = A" "w = w' @ [Nt A']"
          and Aw'R: "(A,w') \<in> R" and A'w': "Nt A' \<notin> set w'"
        by (auto simp: unwind_old_def Nonterminal_def split: prod.splits)
      from m[folded append_assoc, unfolded derivern_append_map_Tm]
      obtain v' where v': "unwind R A A' \<turnstile> (l @ w') @ [Nt A'] \<Rightarrow>r(m) v'"
        and [simp]: "v = v' @ map Tm r"
        by auto
      from less.prems have "\<not>ends_with A' v'" by (auto simp: ends_with_def)
      from extract_right_loop[OF v' this]
      obtain n1 n2 u' w'' where len: "n1 + n2 < m"
        and n1: "right_loop (unwind R A A') A' \<turnstile> [Nt A'] \<Rightarrow>r(n1) u' @ [Nt A']"
        and w'': "(A', w'') \<in> unwind R A A'" "\<not> ends_with A' w''"
        and n2: "unwind R A A' \<turnstile> (l @ w') @ u' @ w'' \<Rightarrow>r(n2) v'" by auto
      from w'' A'R have A'w''R: "(A',w'') \<in> unwind_new R A A'"
        and A'w'': "Nt A' \<notin> set w''"
        by (auto simp: unwind_def unwind_old_def unwind_new_def Nonterminal_def ends_with_def)
      from n1 right_loop_unwind[OF A'R, THEN deriver_mono]
      have n1: "unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>r(n1) u' @ [Nt A']"
        apply (auto simp: le_fun_def)
        by (metis relpowp_mono)
      from unwind_new_only_last[OF A'R derivern_imp_deriven[OF n1]]
      have A'u': "Nt A' \<notin> set u'" by auto
      note n1
      also have "unwind_new R A A' \<turnstile> u' @ [Nt A'] \<Rightarrow>r u' @ w''"
        using A'w''R by (auto simp: deriver_snoc_Nt simp del: append_assoc)
      finally have "unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(Suc n1) u' @ w''"
        by (rule derivern_imp_deriven)
      from unwind_new_sound[OF A'R this] A'u' A'w' A'w''
      have "R \<turnstile> [Nt A] \<Rightarrow>* Nt A # u' @ w''" by auto
      also have "R \<turnstile> \<dots> \<Rightarrow> w' @ u' @ w''" using Aw'R
        by (auto intro!: derivel_imp_derive simp: derivel_Nt_Cons)
      finally have "R \<turnstile> [Nt A] \<Rightarrow>* \<dots>".
      note derives_prepend[OF this]
      also from A'u' A'w' A'w'' less.prems(2-3) less.IH[OF _ n2] len
      have "R \<turnstile> l @ w' @ u' @ w'' \<Rightarrow>* v'" by auto
      finally have "R \<turnstile> l @ [Nt A] \<Rightarrow>* v'".
      from derives_append[OF this]
      show ?thesis by simp
    next
      case False
      with BwR' have "(B,w) \<in> R" by (auto simp: unwind_old_def)
      then have "R \<turnstile> u \<Rightarrow> l @ w @ map Tm r" by (auto simp: derive_iff)
      also have "R \<turnstile> \<dots> \<Rightarrow>* v"
        apply (rule less.IH[OF _ m]) using A'R BwR' A'l False less.prems
        by (auto simp: Nonterminal_def split:prod.splits)
      finally show ?thesis.
    qed
  qed
qed

lemma unwind_derives:
  assumes "Nt A' \<notin> set u" and "A' \<notin> Nonterminal R"
  shows "unwind R A A' \<turnstile> u \<Rightarrow>* map Tm v \<longleftrightarrow> R \<turnstile> u \<Rightarrow>* map Tm v"
    (is "?l \<longleftrightarrow> ?r")
proof
  assume "?r"
  then have "R \<turnstile> u \<Rightarrow>l* map Tm v" by (simp add: derivels_iff_derives)
  then obtain n where "R \<turnstile> u \<Rightarrow>l(n) map Tm v"
    by (metis rtranclp_imp_relpowp)
  from unwind_complete[OF this]
  show "?l".
next
  assume "?l"
  then have "unwind R A A' \<turnstile> u \<Rightarrow>r* map Tm v" by (simp add: derivers_iff_derives)
  then obtain n where "unwind R A A' \<turnstile> u \<Rightarrow>r(n) map Tm v"
    by (metis rtranclp_imp_relpowp)
  from unwind_sound[OF this ] assms
  show "?r" by auto
qed

lemma Lang_unwind:
  assumes A'R: "A' \<notin> Nonterminal R" and "B \<noteq> A'"
  shows "Lang (unwind R A A') B = Lang R B"
  apply (rule Lang_eqI_derives)
  apply (rule unwind_derives)
  using assms by auto

(* broken
definition "eq0 S S' = (\<forall>v. S \<turnstile> v \<Rightarrow>h* [] \<longleftrightarrow> S' \<turnstile> v \<Rightarrow>h* [])"

definition "eqT1 S S' = (\<forall>c v w. S \<turnstile> v \<Rightarrow>h* T c # w \<longleftrightarrow> S' \<turnstile> v \<Rightarrow>h* T c # w)"

lemma decomp_derives_0:
  "R \<turnstile> v \<Rightarrow>* [] \<longleftrightarrow> R \<turnstile> v \<Rightarrow>h* []" sorry

lemma decomp_derives_T1:
  assumes "R \<turnstile> v \<Rightarrow>* T c # w"
  shows "\<exists>u. R \<turnstile> v \<Rightarrow>h* T c # u \<and> R \<turnstile> u \<Rightarrow>* w"
  sorry

lemma derives_if_derivehds: "R \<turnstile> v \<Rightarrow>h* w \<Longrightarrow> R \<turnstile> v \<Rightarrow>* w" sorry

lemma eqT1_derives:
  assumes "eq0 R R'" "eqT1 R R'"
  shows "R \<turnstile> v \<Rightarrow>* map T w \<Longrightarrow> R' \<turnstile> v \<Rightarrow>* map T w"
proof (induction w arbitrary:v)
  case Nil
  with assms decomp_derives_0 show ?case by (auto simp: eq0_def)
next
  case (Cons a w)
  then show ?case using decomp_derives_T1[of R v a "map T w"]
    using \<open>eqT1 R R'\<close>[unfolded eqT1_def]
    apply (auto)
    by (meson derives_Cons derives_if_derivehds rtranclp_trans)
qed

lemma eps_free_Un: assumes "eps_free R" "eps_free S"
  shows "eps_free (R \<union> S)"
  using assms by (auto simp: eps_free_def)

lemma eq0_if_eps_free:
  assumes "eps_free R" "eps_free S"
  shows "eq0 R S"
  using assms apply (simp add: eps_free_def eq0_def split: prod.splits)
  by (metis append_is_Nil_conv derivehd.simps rtranclp.cases rtranclp.rtrancl_refl)

lemma Un_derives:
  assumes "eps_free R" "eps_free S" "eps_free S'"
    and eq1: "eqT1 (R \<union> S) (R \<union> S')"
  shows "R \<union> S \<turnstile> v \<Rightarrow>* map T w \<longleftrightarrow> R \<union> S' \<turnstile> v \<Rightarrow>* map T w"
proof-
  have 1: "eq0 (R \<union> S) (R \<union> S')"
    using assms(1-3) eq0_if_eps_free eps_free_Un by auto 
  have 2: "eq0 (R \<union> S') (R \<union> S)"
    using assms(1-3) eq0_if_eps_free eps_free_Un by auto 
  from eqT1_derives[OF 1 eq1] eqT1_derives[OF 2]
  show ?thesis apply auto
    using eq1 eqT1_def by blast
qed

lemma eqT1_unwind':
"eqT1 (unwind_new R A A' \<union> expand (unwind_old R A A') (unwind_old R A A') {A})
     (unwind_new R A A' \<union> unwind_old R A A')"
  sorry

lemma unwind_derives:
  assumes "eps_free R"
  shows "unwind_new R A A' \<union>
   expand (unwind_old R A A') (unwind_old R A A') {A} \<turnstile> w \<Rightarrow>* map T v
\<longleftrightarrow> unwind_new R A A' \<union> unwind_old R A A' \<turnstile> w \<Rightarrow>* map T v"
  apply (rule Un_derives)
  using assms
  by (simp_all add: eps_free_unwind_new eps_free_unwind_old eps_free_expand
      eqT1_unwind')

*)

lemma Lang_unwind_expand:
  assumes ef: "eps_free R"
  assumes "solved R As" and "A' \<noteq> A" and A'RAs: "A' \<notin> Nonterminal R \<union> As"
    and "A' \<noteq> B"
  shows "Lang (unwind_expand R As A A') B = Lang R B"
  apply (simp add: unwind_expand_def Let_def del:)
  apply (subst Lang_expand[OF eps_free_unwind_new])
  using A'RAs apply (force simp: unwind_new_def Nonterminal_def)
  using Lang_unwind
  apply (auto simp:  )
  sorry

lemma eps_free_unwind_old_expand_list:
  assumes "eps_free R"
  shows "eps_free (unwind_old_expand R A A')"
  using assms
  by (auto simp: unwind_old_expand_def eps_free_def)

lemma in_Nonterminal_if_starts_with: "(A, w) \<in> R \<Longrightarrow> starts_with B w \<Longrightarrow> B \<in> Nonterminal R"
  apply (cases "(B,w)" rule: starts_with.cases)
    apply (auto simp: Nonterminal_def split: prod.split)
  by (metis list.set_intros(1) prod.inject)
  
lemma loop_free_unwind_old_expand:
  assumes "A' \<noteq> A"
  shows "loop_free (unwind_old_expand R A A') A"
  using assms by (auto simp: loop_free_def starts_with_iff unwind_old_expand_def Cons_eq_append_conv)

lemma solved_unwind_old_expand:
  assumes "solved R As"
    and "eps_free R"
  shows "solved (unwind_old_expand R A A') (insert A As)"
  using assms
  apply (auto simp: Cons_eq_append_conv solved_def starts_with_iff unwind_old_expand_def
      eps_free_Nil
      split: prod.splits)
  by metis+

lemma solved_Un: "solved (R \<union> S) As \<longleftrightarrow> solved R As \<and> solved S As"
  by (auto simp:solved_def)

lemma loop_free_unwind_new_list:
  assumes "A' \<noteq> A"
  shows "loop_free (unwind_new R A A') A"
  using assms by (auto simp: loop_free_def starts_with_iff unwind_new_def Cons_eq_append_conv)

definition Rhs1s where "Rhs1s R = [A. (B, Nt A # w) \<leftarrow> R]"

lemma set_Rhs1s: "set (Rhs1s R) = Rhs1 (set R)"
  by (auto simp: Rhs1s_def Rhs1_def Lnt_def rhs1_def image_Collect)

definition "eps_free_list R = (\<forall>(A,w) \<in> set R. w \<noteq> [])"

definition Rex :: "(int,int) prod list"
  where "Rex = [
  (1,[Nt 2, Nt 2]), (1, [Tm 0]),
  (2, [Nt 2, Nt 2, Nt 2]), (2, [Tm 0, Nt 2]), (2, [Tm 1])]"

definition Rex2 :: "(int,int) prod list"
  where "Rex2 = [
  (1, [Nt 2, Tm 0]),
  (2, [Nt 1, Tm 2]), (2, [Tm 1, Nt 1]), (2, [Tm 3])]"

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

definition Rex3 :: "(int,int) prod list" where "Rex3 = [
(0,[Nt 0]), (1,[Nt 1, Nt 0])]"

value "unwind_new_list Rex3 1 2"

value "expand_list (unwind_new_list Rex3 1 2) (unwind_old_expand_list Rex3 1 2) [0]"

text \<open>The following is true without assuming solved_listness of \<open>As\<close>,
because of the definition of \<open>expand\<close>.\<close>

lemma hd_in_Nonterminal: "(A,Nt B#w) \<in> R \<Longrightarrow> B \<in> Nonterminal R"
  apply (auto simp: Nonterminal_def split: prod.splits)
  by (metis list.set_intros(1) prod.inject)

lemma hd2_in_Nonterminal: "(A,x#Nt B#w) \<in> R \<Longrightarrow> B \<in> Nonterminal R"
  apply (auto simp: Nonterminal_def split: prod.splits)
  by (metis list.set_intros(1,2) prod.inject)
  

lemma solved_list_expand_list_unwind_new_list:
  assumes "A' \<notin> As"
    and "eps_free R" "A' \<notin> Nonterminal R"
    and "solved R As"
  shows "solved (expand (unwind_new R A A')
 (unwind_old_expand R A A') (insert A As))
  (insert A' (insert A As))"
  using assms
  apply (intro solvedI)
  by (auto simp: expand_def solved_not
      unwind_new_def unwind_old_expand_def neq_Nil_conv starts_with_iff
      Cons_eq_append_conv eps_free_Nil hd_in_Nonterminal hd2_in_Nonterminal)


text \<open>Instead, preservation of the language requires solved_listness
of \<open>R\<close> with respect to \<open>As\<close>.\<close>

lemma solved_unwind_expand:
  assumes ef: "eps_free R" and A': "A' \<notin> Nonterminal R \<union> As"
    and so: "solved R As"
  shows "solved (unwind_expand R As A A') (insert A (insert A' As))"
proof-
  have so2: "solved R (insert A' As)"
    using so A' 
    by (auto simp: solved_def in_Nonterminal_if_starts_with split: prod.splits)
  show ?thesis
    apply (auto simp: unwind_expand_def solved_Un
        solved_unwind_old_expand[OF so2 ef])
    apply (subst insert_commute)
    apply (rule solved_list_expand_list_unwind_new_list)
    using assms by auto
qed

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
  note 1 =  eps_free_unwind_old_expand_list[OF assms]
  with eps_free_expand[OF this eps_free_unwind_new]
  show ?thesis
  apply (auto intro!:eps_freeI simp: eps_free_Nil unwind_expand_def)
    by (smt (verit) eps_free_Nil eps_free_expand eps_free_unwind_new)
qed

lemma loop_free_expand:
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
  from solved_unwind_old_expand[OF so ef]
  have 1: "solved (unwind_old_expand R A A') (insert A As)"
    by auto
  then have 2: "solved (unwind_old_expand R A A') As"
    by (auto simp: solved_def)
  show ?thesis
    apply (auto simp: unwind_expand_def loop_free_Un loop_free_unwind_old_expand[OF A'])
    apply (rule loop_free_expand[OF loop_free_unwind_new_list[OF A']])
    apply (simp)
     apply (rule 1)
    using eps_free_unwind_old_expand_list[OF ef].
qed

fun realtime_list where
  "realtime_list R (A#As) (A'#As') = unwind_expand_list (realtime_list R As As') (As@As') A A'"
| "realtime_list R _ _ = R"

context fixes R :: "('n,'t) prodS" begin
fun realtime where
  "realtime (A#As) (A'#As') =
  unwind_expand (realtime As As') (set (As@As')) A A'"
| "realtime _ _ = R"

end

lemma solved_if_disj:
  assumes disj: "set As' \<inter> Nonterminal R = {}"
  shows "solved R (set As')"
  using disj
  by (auto simp: solved_def dest:in_Nonterminal_if_starts_with)


lemma Nonterminal_realtime: "Nonterminal (realtime R As As') \<subseteq> Nonterminal R \<union> set As \<union> set As'"
  sorry

context
  fixes R :: "('n,'t)prodS"
  assumes ef: "eps_free R"
begin

lemma eps_free_realtime:
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
    and "distinct (As @ As')" and "set As' \<inter> Nonterminal R = {}"
  shows "solved (realtime R As As') (set As \<union> set As')"
  using assms
proof (induction As As' rule: realtime.induct)
  case (1 A As A' As')
  with Nonterminal_realtime[of R]
    solved_unwind_expand[where A=A and A'=A' and As = "set As \<union> set As'" and R ="realtime R As As'"]
  show ?case by (auto intro!: simp: eps_free_realtime insert_commute) 
next
  case ("2_1" As')
  with solved_if_disj show ?case by auto
next
  case ("2_2" As)
  then show ?case by (auto simp: solved_def)
qed

lemma Lang_realtime:
  assumes "eps_free R"
    and "length As \<le> length As'"
    and "distinct (As @ As')" and "set As' \<inter> Nonterminal R = {}"
    and "B \<notin> set As'"
  shows "Lang (realtime R As As') B = Lang R B"
  using assms(2-)
proof (induction As As' rule: realtime.induct)
  case (1 A As A' As')
  with Nonterminal_realtime[of R] solved_realtime[OF \<open>eps_free R\<close> ]
    Lang_unwind_expand[where A=A and A'=A' and As = "set As \<union> set As'" and R ="realtime R As As'" and B=B]
  show ?case by (auto intro!: simp: eps_free_realtime insert_commute) 
next
  case ("2_1" As')
  then show ?case by auto
next
  case ("2_2" As)
  then show ?case by (auto simp: solved_def)
qed



end

value "unwind_expand_list [(1,[N 1 :: (int,int)sym, N 1])] [] 1 2"

theorem GNF:
fixes R :: "('n,'t)prodS" and new :: "'n set \<Rightarrow> 'n"
assumes "\<And>X. finite X \<Longrightarrow> new (X) \<notin> X"
assumes "finite R" and "eps_free R" and "Rhs1 R \<subseteq> set As" "distinct As"
shows "\<exists>R'::('n ,'t)prodS. Lang S R' = Lang S R \<and> rtps R'"
  oops

end