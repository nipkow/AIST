theory GNF
imports CFG
begin

lemma rtranclpE_power: "rtranclp r x y \<Longrightarrow> (\<And>n. (r^^n) x y \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: rtranclp_power)

fun rt :: "('n,'t)syms \<Rightarrow> bool" where
"rt [] = True" |
"rt (Tm _ # _) = True" |
"rt _ = False"

definition rtps :: "('n,'t)Prods \<Rightarrow> bool" where
"rtps ps = (\<forall>p \<in> ps. rt(snd p))"

definition Lnt :: "('n, 't) Prods \<Rightarrow> ('n * 'n * ('n,'t)syms)set" where
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

definition Eps_free where "Eps_free R = (\<forall>(_,r) \<in> R. r \<noteq> [])"

definition "eps_free R = (\<forall>(A,w) \<in> set R. w \<noteq> [])"

lemma Eps_freeI:
  assumes "\<And>A r. (A,r) \<in> R \<Longrightarrow> r \<noteq> []" shows "Eps_free R"
  using assms by (auto simp: Eps_free_def)

lemma Eps_free_Nil: "Eps_free R \<Longrightarrow> (A,[]) \<notin> R"
  by (auto simp: Eps_free_def)

lemma Eps_freeE_Cons: "Eps_free R \<Longrightarrow> (A,w) \<in> R \<Longrightarrow> \<exists>a u. w = a#u"
  by (cases w, auto simp: Eps_free_def)

lemma Eps_free_derives_Nil:
  assumes R: "Eps_free R" shows "R \<turnstile> l \<Rightarrow>* [] \<longleftrightarrow> l = []" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction rule: derives_induct')
    case base
    show ?case by simp
  next
    case (step u A v w)
    then show ?case by (auto simp: Eps_free_Nil[OF R])
  qed
qed auto

fun expand_eps where
  "expand_eps A [] = {[]}"
| "expand_eps A (a#w) =
  Cons a ` expand_eps A w \<union> (if a = Nt A then expand_eps A w else {})"

lemma expand_eps_self: "w \<in> expand_eps A w" by (induction w, auto)

lemma expand_eps_complete:
  "R \<turnstile> w \<Rightarrow>* v \<Longrightarrow> (\<exists>w' \<in> expand_eps A w. R \<turnstile> w' \<Rightarrow>* v)"
proof (induction rule: rtrancl_derive_induct)
  case base
  show ?case by (auto intro!: bexI[OF _ expand_eps_self])
next
  case (step u A v w)
  then show ?case by (auto intro!: bexI[OF _ expand_eps_self] intro: derives_rule)
qed

lemma expand_eps_sound:
  assumes A0: "(A,[]) \<in> R"
    and "w' \<in> expand_eps A w" and "R \<turnstile> w' \<Rightarrow>* v"
  shows "R \<turnstile> w \<Rightarrow>* v"
  using assms(3,2)
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case
  proof (induction w arbitrary: w')
    case Nil
    then show ?case by simp
  next
    case (Cons a w)
    then show ?case
      by (auto simp: derives_Cons derives_Cons_rule[OF A0] split: if_splits)
  qed
next
  case (step u A v w)
  then show ?case by (auto dest: derives_rule)
qed

definition Eps_remove where "Eps_remove R =
  {(A,r) \<in> R. r \<noteq> []} \<union>
  {(B,w') | A B w w'. (A,[]) \<in> R \<and> (B,w) \<in> R \<and> w' \<in> expand_eps A w - {[]}}"

definition Eps_extract where "Eps_extract R = {(A,[]) |A. R \<turnstile> [Nt A] \<Rightarrow>* []}"

lemma Eps_extract_derives: "R \<turnstile> v \<Rightarrow>* [] \<longleftrightarrow> Eps_extract R \<turnstile> v \<Rightarrow>* []" (is "?l \<longleftrightarrow> ?R \<turnstile> v \<Rightarrow>* []")
proof (safe elim!: rtranclpE_power)
  show "R \<turnstile> v \<Rightarrow>(n) [] \<Longrightarrow> ?R \<turnstile> v \<Rightarrow>* []" for n
  proof (induction n arbitrary: v rule: less_induct)
    case (less n)
    show ?case
    proof (cases n)
      case 0
      with less.prems show ?thesis by auto
    next
      case (Suc m)
      with less.prems
      obtain A u w n1 n2 where
        [simp]: "n = Suc (n1 + n2)" "v = Nt A # u"
        and Aw: "(A, w) \<in> R"
        and w: "R \<turnstile> w \<Rightarrow>(n1) []"
        and u: "R \<turnstile> u \<Rightarrow>(n2) []"
        by (auto simp: deriven_Suc_decomp_left)
      from Aw w have "R \<turnstile> [Nt A] \<Rightarrow>(Suc n1) []"
        by (auto simp: deriven_singleton)
      then have "(A,[]) \<in> Eps_extract R"
        by (auto simp: Eps_extract_def rtranclp_power)
      with less.IH[OF _ u]
      show ?thesis by (auto simp: Eps_extract_def derives_Cons_rule)
    qed
  qed
  show "Eps_extract R \<turnstile> v \<Rightarrow>(n) [] \<Longrightarrow> R \<turnstile> v \<Rightarrow>* []" for n
  proof (induction n arbitrary: v rule: less_induct)
    case (less n)
    show ?case
    proof (cases n)
      case 0
      with less.prems show ?thesis by auto
    next
      case (Suc m)
      with less.prems
      obtain A u w n1 n2 where
        [simp]: "n = Suc (n1 + n2)" "v = Nt A # u"
        and Aw: "(A,w) \<in> ?R"
        and w: "?R \<turnstile> w \<Rightarrow>(n1) []"
        and u: "?R \<turnstile> u \<Rightarrow>(n2) []"
        by (auto simp: deriven_Suc_decomp_left)
      from Aw have "R \<turnstile> [Nt A] \<Rightarrow>* []" by (auto simp: Eps_extract_def)
      with less.IH[OF _ u]
      show ?thesis
        apply (auto)
        by (metis derives_Cons rtranclp_trans)
    qed
  qed
qed

lemma Eps_free_Eps_remove: "Eps_free (Eps_remove R)"
  by (auto simp: Eps_free_def Eps_remove_def)

lemma Eps_remove_derives_sound: "Eps_remove R \<turnstile> x \<Rightarrow>* y \<Longrightarrow> R \<turnstile> x \<Rightarrow>* y"
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case by auto
next
  case (step u A v w)
  from this(2)[unfolded Eps_remove_def]
  show ?case
  proof (safe del: DiffE)
    show "(A, w) \<in> R \<Longrightarrow> w \<noteq> [] \<Longrightarrow> ?thesis"
      using step(3)
      by (auto simp: derives_rule[OF _ _ rtranclp.rtrancl_refl])
    fix B w' assume B: "(B,[]) \<in> R" and w: "w \<in> expand_eps B w' - {[]}"
      and A: "(A,w') \<in> R"
    show ?thesis
      apply (rule derives_rule[OF A step(3)[simplified]])
      using expand_eps_sound[OF B _ rtranclp.rtrancl_refl] w
      by (auto intro!: derives_prepend derives_append)
  qed
qed

lemma Eps_remove_derives_complete:
  assumes uv: "R \<turnstile> u \<Rightarrow>* v"
  shows "if v = [] then Eps_extract R \<turnstile> u \<Rightarrow>* [] else Eps_remove R \<turnstile> u \<Rightarrow>* v \<or> v = []"
  using uv
proof (elim rtranclpE_power)
  show "R \<turnstile> u \<Rightarrow>(n) v \<Longrightarrow> ?thesis" for n
  proof (induction n arbitrary: u v rule: less_induct)
    case (less n)
    show ?case
    proof (cases n)
      case 0
      with less.prems show ?thesis by auto
    next
      case [simp]: (Suc m)
      from less.prems
      obtain p A u2 w v1 v2 n1 n2
        where "u = p @ Nt A # u2" "v = p @ v1 @ v2"
          and w: "(A,w) \<in> R" and "m = n1 + n2"
          and wv1: "R \<turnstile> w \<Rightarrow>(n1) v1" and "R \<turnstile> u2 \<Rightarrow>(n2) v2"
        by (fastforce simp: deriven_Suc_decomp_left)
      note less.IH[OF _ wv1]
      show ?thesis
        oops

lemma "\<exists>R'. Eps_free R' \<and> (\<forall>A. Lang R' A = Lang R A - {[]})"
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

definition "Loop R A = {(A,Nt A # w) | w. (A, Nt A # w) \<in> R \<and> w \<noteq> []}"

definition "right_Loop R A = {(A,w@[Nt A]) | w. (A, w@[Nt A]) \<in> R \<and> w \<noteq> []}"

lemma right_Loop_eq_Loop:
  "right_Loop R A = map_prod id rev ` Loop (map_prod id rev ` R) A"
  by (force simp: right_Loop_def Loop_def Cons_eq_rev_iff)

definition "Loop_free R A = (\<forall>(B,w) \<in> R. B = A \<longrightarrow> \<not> starts_with A w)"

lemma Loop_freeI:
  assumes "\<And>w. (A,w) \<in> R \<Longrightarrow> \<not>starts_with A w" shows "Loop_free R A"
  using assms by (auto simp: Loop_free_def)

lemma Loop_freeD: "Loop_free R A \<Longrightarrow> (A, Nt A # w) \<notin> R"
  by (auto simp: Loop_free_def)

definition "Loop_free_list R A = (\<forall>(B,w) \<in> set R. B = A \<longrightarrow> \<not> starts_with A w)"

lemma Loop_free_Un: "Loop_free (R \<union> S) A \<longleftrightarrow> Loop_free R A \<and> Loop_free S A"
  by (auto simp:Loop_free_def)

definition "solved R As \<longleftrightarrow>
  (\<forall>A \<in> set As. \<forall>(B,w) \<in> set R. \<not>starts_with A w)"

definition "Solved R As \<longleftrightarrow>
  (\<forall>A \<in> As. \<forall>(B,w) \<in> R. \<not>starts_with A w)"

lemma SolvedI:
  assumes "\<And>A B w. A \<in> As \<Longrightarrow> (B,w) \<in> R \<Longrightarrow> \<not> starts_with A w"
  shows "Solved R As"
  using assms by (auto simp: Solved_def)

lemma Solved: "Solved (set R) (set As) = solved R As"
  by (auto simp: Solved_def solved_def)

lemma Solved_not:
  "Solved R As \<Longrightarrow> A \<in> As \<Longrightarrow> (B,Nt A#w) \<notin> R"
  by (fastforce simp: Solved_def starts_with_iff split: prod.splits)

definition nonterminals where "nonterminals R = concat [A#[B. Nt B \<leftarrow> w]. (A,w) \<leftarrow> R]"

definition Nonterminals where "Nonterminals R = (\<Union>(A,w)\<in>R. {A}\<union>{B. Nt B \<in> set w})"

lemma set_nonterminals_def: "set (nonterminals R) = Nonterminals (set R)"
  by (auto simp: nonterminals_def Nonterminals_def)

fun hdnt where
    "hdnt (Nt A#w) = Some A"
  | "hdnt _ = None"

definition "diff_list = fold removeAll"

lemma set_diff_list[simp]: "set(diff_list xs ys) = set ys - set xs"
  by (induction xs arbitrary: ys, auto simp: diff_list_def)

definition Unwind_new where
  "Unwind_new R A A' = (
  \<Union>{{(A',w), (A',w@[Nt A'])} | w. (A,Nt A # w) \<in> R \<and> w \<noteq> []})"

definition unwind_new where
  "unwind_new R A A' =
  concat [[(A',w), (A',w@[Nt A'])]. (B,Nt C # w) \<leftarrow> R, B = A \<and> C = A \<and> w \<noteq> []]"

lemma set_unwind_new: "set (unwind_new R A A') = Unwind_new (set R) A A'"
  apply (auto simp: unwind_new_def Unwind_new_def starts_with_iff)
  apply (metis insertI1)
  by (metis insert_subset subset_insertI)

definition Unwind_old where
  "Unwind_old R A A' = (
  let X = {(A, Nt A # w) | w. (A, Nt A # w) \<in> R} in
  R - X \<union> {(A, w@[Nt A']) |w. (A,w) \<in> R - X})"

definition unwind_old where
  "unwind_old R A A' = (
  let X = [(B,w) \<leftarrow> R. B = A \<and> starts_with A w] in
  diff_list X R @
  [(A, w@[Nt A']). (B,w) \<leftarrow> R, B = A \<and> \<not> starts_with A w])"

lemma set_unwind_old: "set (unwind_old R A A') = Unwind_old (set R) A A'"
  by (auto simp: Unwind_old_def unwind_old_def starts_with_iff)

definition Unwind where
  "Unwind R A A' = Unwind_new R A A' \<union> Unwind_old R A A'"

definition unwind where
  "unwind R A A' = unwind_new R A A' @ unwind_old R A A'"

lemma set_unwind: "set (unwind R A A') = Unwind (set R) A A'"
  by (auto simp: unwind_def Unwind_def set_unwind_old set_unwind_new)

lemma Eps_free_Unwind_old: "Eps_free R \<Longrightarrow> Eps_free (Unwind_old R A A')"
  by (auto simp: Eps_free_def Unwind_old_def)

definition unwind_old_expand where
  "unwind_old_expand R A A' = (
  let X = [(B,w) \<leftarrow> R. starts_with A w] in
  diff_list X R @
  [(A, w@[Nt A']). (B,w) \<leftarrow> R, B = A \<and> \<not> starts_with A w] @
  concat [[(B,w@tl v),(B,w@Nt A'#tl v)]. (B,v) \<leftarrow> R, (C,w) \<leftarrow> diff_list X R, starts_with A v \<and> A \<noteq> B \<and> C = A ])"

definition Unwind_old_Expand where
  "Unwind_old_Expand R A A' = (
  let X = {(B, Nt A # w) | B w. (B, Nt A # w) \<in> R} in
  R - X \<union> {(A, w @ [Nt A']) |w. (A,w) \<in> R - X} \<union>
  \<Union>{{(B, w@v), (B, w @ Nt A' # v)} |B v w.
 (B, Nt A # v) \<in> R \<and> A \<noteq> B \<and> (A,w) \<in> R - X })"

lemma set_unwind_old_expand: "set (unwind_old_expand R A A') = Unwind_old_Expand (set R) A A'"
  apply (auto simp: Unwind_old_Expand_def unwind_old_expand_def starts_with_iff)
  sorry

definition "Expand R S As =
  {(A, b # w) |A b w. (A, b # w) \<in> R \<and> b \<notin> Nt ` As} \<union>
  {(A,v@w) |A v w. \<exists>B \<in> As. (A,Nt B # w) \<in> R \<and> (B,v) \<in> S}"

definition "expand R S As =
  [(A, b # w). (A, b # w) \<leftarrow> R, b \<notin> Nt ` set As] @
  [(A,v@w). (A, Nt B # w) \<leftarrow> R, B \<in> set As, (C,v) \<leftarrow> S, C = B]"

lemma set_expand: "set (expand R S As) = Expand (set R) (set S) (set As)"
  by (auto simp: expand_def Expand_def)

lemma derive_Expand_iff:
  shows "Expand R S As \<turnstile> u \<Rightarrow> v \<longleftrightarrow>
  (\<exists>u1 u2 A b w. (A, b # w) \<in> R \<and> u = u1 @ Nt A # u2 \<and>
  (b \<notin> Nt ` As \<and> v = u1 @ b # w @ u2 \<or>
  (\<exists>(C,r) \<in> S. C \<in> As \<and> b = Nt C \<and> v = u1 @ r @ w @ u2)))"
  by (fastforce simp: Bex_def Expand_def derive_iff split:prod.splits)

definition "Unwind_Expand R As A A' =
  Expand (Unwind_new R A A') (Unwind_old_Expand R A A') (insert A As) \<union>
  Unwind_old_Expand R A A'"

definition "unwind_expand R As A A' =
  expand (unwind_new R A A') (unwind_old_expand R A A') (A#As) @
  unwind_old_expand R A A'"

lemma set_unwind_expand:
  "set (unwind_expand R As A A') = Unwind_Expand (set R) (set As) A A'"
  by (simp add: unwind_expand_def Unwind_Expand_def
      set_expand set_unwind_old_expand set_unwind_new)

lemma Unwind_old_Expand:
  assumes ef: "Eps_free R" and "A' \<noteq> A"
  shows "Unwind_old_Expand R A A' = Expand (Unwind_old R A A') (Unwind_old R A A') {A}"
  using assms
  apply (simp add: Unwind_old_Expand_def Unwind_old_def Expand_def)
  apply safe
                  apply(auto dest: Eps_freeE_Cons)[2]
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
     apply (metis (mono_tags, lifting) Cons_eq_appendI append_assoc Eps_freeE_Cons list.inject)
    apply (metis (no_types, opaque_lifting) Cons_eq_appendI Eps_freeE_Cons list.inject)
   apply (metis (no_types, lifting) append_eq_Cons_conv Eps_free_Nil)
  apply auto[]
  by (metis append_eq_Cons_conv Eps_free_Nil)

lemma Expand_right_Un_id:
  assumes "As \<inter> fst ` S = {}"
  shows "Expand R (S \<union> U) As = Expand R U As"
  using assms
  apply (auto simp: Expand_def)
  by (metis disjoint_iff fst_eqD imageI)

lemma Expand_Unwind_eq_Expand_Unwind_old:
  assumes "A' \<noteq> A"
  shows "Expand R' (Unwind R A A') {A} = Expand R' (Unwind_old R A A') {A}"
  using assms
  apply (unfold Unwind_def)
  apply (subst Expand_right_Un_id)
  by (auto simp: Unwind_new_def)

lemma Unwind_old_Expand_2:
  assumes ef: "Eps_free R" and A': "A' \<noteq> A"
  shows "Unwind_old_Expand R A A' = Expand (Unwind_old R A A') (Unwind R A A') {A}"
  apply (unfold Expand_Unwind_eq_Expand_Unwind_old[OF A'])
  using Unwind_old_Expand[OF assms].

lemma Expand_Un: "Expand (R \<union> R') S As = Expand R S As \<union> Expand R' S As"
  by (fastforce simp: Expand_def)

lemma Expand_Solved:
  assumes so: "Solved R As" and ef: "Eps_free R"
  shows "Expand R S As = R"
  using so Eps_freeE_Cons[OF ef]
  by (fastforce simp: starts_with_iff Solved_def Expand_def)

lemma Eps_free_Expand:
  assumes "Eps_free R" "Eps_free S"
  shows "Eps_free (Expand R S As)"
  using assms
  by (auto simp: Eps_free_def Expand_def split: prod.splits)

definition "Unwind_Expand' R As A A' = (
  let R' = Unwind R A A' in
  Expand R' R' (insert A As))"

definition "unwind_expand' R As A A' = (
  let R' = unwind R A A' in
  expand R' R' (A#As))"

value "unwind_old_expand [(2, [Nt 1::(int,int)sym])] 1 2"

value "solved [(2::int, [Nt 2::(int,int)sym, Nt 1]), (1, [Nt 2])] [1]"

lemma in_ExpandE:
  assumes "(A, w) \<in> Expand R S As"
    and "\<And>b w'. w = b # w' \<Longrightarrow> b \<notin> Nt ` As \<Longrightarrow> (A,w) \<in> R \<Longrightarrow> thesis"
    and "\<And>B w' v. w = v @ w' \<Longrightarrow> B \<in> As \<Longrightarrow>
    (A, Nt B # w') \<in> R \<Longrightarrow> (B,v) \<in> S \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: Expand_def)

lemma Expand_derives_sound:
  assumes ef: "Eps_free R"
  assumes "Expand R S As \<union> S \<turnstile> u \<Rightarrow>* v"
  shows "R \<union> S \<turnstile> u \<Rightarrow>* v"
  using assms(2)
proof (induction rule: rtrancl_derive_induct)
  case base
  then show ?case by auto
next
  case (step l A r w)
  from \<open>(A, w) \<in> Expand R S As \<union> S\<close>
  have "R \<union> S \<turnstile> [Nt A] \<Rightarrow>* w"
    apply (elim UnE in_ExpandE)
  proof goal_cases
    case (1 b w')
    then show ?case
      by (simp add: derive_singleton r_into_rtranclp)
  next
    case (2 B w' v)
    then have "R \<union> S \<turnstile> [Nt A] \<Rightarrow>* Nt B # w'"
      by (simp add: derive_singleton r_into_rtranclp)
    also from 2 have "R \<union> S \<turnstile> \<dots> \<Rightarrow> v @ w'"
      by (simp add: derivel_Nt_Cons derivel_imp_derive)
    finally show ?case using 2 by simp
  next
    case 3
    then show ?case
      by (simp add: derive_singleton r_into_rtranclp)
  qed
  with step(3)
  show ?case
    by (meson derives_append derives_prepend rtranclp_trans)
qed

fun leftmost_nt where "leftmost_nt [] = None" |
"leftmost_nt (Nt A # w) = Some A" |
"leftmost_nt (Tm c # w) = leftmost_nt w"

lemma leftmost_nt_map_Tm_append: "leftmost_nt (map Tm u @ v) = leftmost_nt v"
  by (induction u, auto)

lemma leftmost_nt_map_Tm: "leftmost_nt (map Tm u) = None"
  using leftmost_nt_map_Tm_append[of _ "[]"] by auto

lemma Expand_derivels:
  assumes ef: "Eps_free R"
    and RAs: "fst ` R \<inter> As = {}"
    and der: "R \<union> S \<turnstile> u \<Rightarrow>l* v" and vAs: "leftmost_nt v \<notin> Some ` As"
  shows "Expand R S As \<union> S \<turnstile> u \<Rightarrow>l* v"
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
        with ef obtain a w2 where [simp]: "w = a # w2" by (auto dest: Eps_freeE_Cons)
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
          have "(A,y@w2) \<in> Expand R S As" by (auto simp: Expand_def)
          then have "Expand R S As \<turnstile> u \<Rightarrow>l z'"
            using derivel.intros by fastforce
          then have "Expand R S As \<union> S \<turnstile> u \<Rightarrow>l z'" by (auto simp: Un_derivel)
          also from less.IH[OF _ z'v]
          have "Expand R S As \<union> S \<turnstile> z' \<Rightarrow>l* v" by auto
          finally show ?thesis by auto
        next
          case False
          with Aw have "(A,w) \<in> Expand R S As"
            by (auto simp: Expand_def Cons_eq_append_conv)
          then have "Expand R S As \<union> S \<turnstile> u \<Rightarrow>l z"
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

lemma Expand_derives:
  assumes ef: "Eps_free R"
    and RAs: "fst ` R \<inter> As = {}"
  shows "Expand R S As \<union> S \<turnstile> u \<Rightarrow>* map Tm v \<longleftrightarrow> R \<union> S \<turnstile> u \<Rightarrow>* map Tm v"
  using Expand_derives_sound[OF ef]
    Expand_derivels[OF ef RAs, of S u \<open>map Tm v\<close>]
  by (auto simp: derivels_iff_derives leftmost_nt_map_Tm)

lemma Lang_Expand:
  assumes ef: "Eps_free R"
    and RAs: "fst ` R \<inter> As = {}"
  shows "Lang (Expand R S As \<union> S) A = Lang (R \<union> S) A"
  unfolding Lang_def
  using Expand_derives[OF assms]
  by auto

subsection \<open>Soundness of Unwind\<close>

lemma Unwind_Expand':
  assumes "Solved R As" and "A' \<noteq> A" and "A' \<notin> Nonterminals R \<union> As"
  shows "Unwind_Expand R As A A' = Unwind_Expand' R As A A'"
  sorry

lemma Eps_free_Unwind_new: "Eps_free (Unwind_new R A A')"
  by (auto simp: Eps_free_def Unwind_new_def)

lemma in_Loop: "(B, w) \<in> Loop R A \<longleftrightarrow>
  A = B \<and> (A,w) \<in> R \<and> (\<exists>w'. w = Nt A # w' \<and> w' \<noteq> [])"
  by (auto simp: Loop_def)

lemma extract_Loop:
  assumes "R \<turnstile> Nt A # u \<Rightarrow>l(n) v" and vA: "\<not>starts_with A v"
  shows "\<exists>n1 n2 u' w.
    n1 + n2 < n \<and>
    Loop R A \<turnstile> [Nt A] \<Rightarrow>l(n1) Nt A # u' \<and>
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
      and n1: "Loop R A \<turnstile> [Nt A] \<Rightarrow>l(n1) Nt A # u'"
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
      from w' Aw have "(A,w) \<in> Loop R A" by (auto simp: in_Loop)
      then have "Loop R A \<turnstile> [Nt A] \<Rightarrow>l Nt A # w'" by (auto simp: derivel_Nt_Cons)
      also from deriveln_append[OF n1, of w']
      have "Loop R A \<turnstile> \<dots> \<Rightarrow>l(n1) Nt A # u' @ w'" by simp
      finally show ?thesis using len AxR Ax n2 by force
    qed
  next
    case False
    with Aw wuv show ?thesis
      apply (rule_tac x=0 in exI) by auto
  qed
qed

lemma extract_right_Loop:
  assumes "R \<turnstile> u @ [Nt A] \<Rightarrow>r(n) v" and vA: "\<not>ends_with A v"
  shows "\<exists>n1 n2 u' w.
    n1 + n2 < n \<and>
    right_Loop R A \<turnstile> [Nt A] \<Rightarrow>r(n1) u' @ [Nt A] \<and>
    (A,w) \<in> R \<and> \<not>ends_with A w \<and> R \<turnstile> u@u'@w \<Rightarrow>r(n2) v"
proof-
  from extract_Loop[of n "map_prod id rev ` R" A "rev u" "rev v"] assms
  show ?thesis
    apply (auto simp: ends_with_iff_starts_with_rev right_Loop_eq_Loop derivern_iff_rev_deriveln
        image_image prod.map_comp o_def)
    apply (rule_tac x=n1 in exI)
    apply (rule_tac x=n2 in exI)
    apply auto
    apply (rule_tac x="rev u'" in exI)
    by auto
qed

lemma Unwind_new_simulate_Loop:
  assumes "Loop R A \<turnstile> [Nt A] \<Rightarrow>l+ Nt A # vs"
  shows "Unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>* vs"
  using assms
proof (induction "Nt A # vs" arbitrary: vs rule: tranclp_induct)
  case base
  then show ?case
    apply (intro conjI r_into_rtranclp)
    by (auto simp: derivel_iff Cons_eq_append_conv Unwind_new_def Loop_def
        derive_singleton)
next
  case (step y z)
  then obtain y' where [simp]: "y = Nt A # y'"
    by (auto simp: derivel_iff in_Loop Cons_eq_append_conv)
  from step[simplified]
  have IH: "Unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>* y'" by auto
  obtain v where AAv: "(A,Nt A # v) \<in> R"
    and [simp]: "z = v @ y'"
    and v0: "v \<noteq> []"
    using step(2)
    by (auto simp: derivel_iff Cons_eq_append_conv in_Loop)
  from v0 have "(A', v @ [Nt A']) \<in> Unwind_new R A A'"
      using AAv by (auto simp: Unwind_new_def)
  with IH show ?case apply auto
    by (meson converse_rtranclp_into_rtranclp derive_singleton derives_prepend)
qed

(*AY: could be generalized so that A is not left-most nonterminal of v. *)
lemma Unwind_complete:
  assumes "R \<turnstile> u \<Rightarrow>l(n) map Tm v"
  shows "Unwind R A A' \<turnstile> u \<Rightarrow>* map Tm v"
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
      from extract_Loop[OF this]
      obtain n1 n2 u'' w'
        where len: "n1 + n2 < n"
          and n1: "Loop R A \<turnstile> [Nt A] \<Rightarrow>l(n1) Nt A # u''"
          and Aw'R: "(A, w') \<in> R"
          and Aw': "\<not> starts_with A w'"
          and n2: "R \<turnstile> w' @ u'' @ u' \<Rightarrow>l(n2) map Tm v'" by (fastforce simp: starts_with_iff)
      from less.IH[OF _ n2] len
      have IH: "Unwind R A A' \<turnstile> w' @ u'' @ u' \<Rightarrow>* map Tm v'" by auto
      show ?thesis
      proof (cases "n1 > 0")
        case True
        from Aw' Aw'R have "(A,w'@[Nt A']) \<in> Unwind R A A'"
          by (auto simp: Unwind_def Unwind_old_def)
        then have "Unwind R A A' \<turnstile> u \<Rightarrow> map Tm p @ w' @ Nt A' # u'"
          by (force simp: derive_iff)
        also have "Unwind R A A' \<turnstile> \<dots> \<Rightarrow>* map Tm p @ w' @ u'' @ u'"
        proof (intro derives_prepend)
          from True n1 have "Loop R A \<turnstile> [Nt A] \<Rightarrow>l+ Nt A # u''"
            by (metis tranclp_power)
          from Unwind_new_simulate_Loop[OF this, of A']
          have "Unwind R A A' \<turnstile> [Nt A'] \<Rightarrow>* u''"
            by (metis Un_derive mono_rtranclp Unwind_def)
          from derives_append[OF this]
          show "Unwind R A A' \<turnstile> Nt A' # u' \<Rightarrow>* u'' @ u'" by simp
        qed
        also have "Unwind R A A' \<turnstile> \<dots> \<Rightarrow>* map Tm v"
          by (simp add: IH derives_prepend)
        finally show ?thesis.
      next
        case False
        from Aw'R Aw' have "Unwind R A A' \<turnstile> Nt A # u' \<Rightarrow> w' @ u'"
          by (auto intro!: derivel_imp_derive simp: derivel_Nt_Cons Unwind_def Unwind_old_def)
        with n1 IH False show ?thesis by (auto intro!:derives_prepend)
      qed
    next
      case False
      with Bw have "(B,w) \<in> Unwind_old R A A'"
        by (auto simp: Unwind_old_def)
      then have "Unwind R A A' \<turnstile> u \<Rightarrow> map Tm p @ w @ u'"
        by (auto simp: derive_iff Unwind_def)
      also from less.IH[OF _ m]
      have "Unwind R A A' \<turnstile> w @ u' \<Rightarrow>* map Tm v'" by auto
      then have "Unwind R A A' \<turnstile> map Tm p @ w @ u' \<Rightarrow>* map Tm v"
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
  assumes "nts_of_syms p \<inter> fst ` R = {}"
  shows "R \<turnstile> p @ u \<Rightarrow> v \<longleftrightarrow> (\<exists>v'. v = p @ v' \<and> R \<turnstile> u \<Rightarrow> v')"
  using assms
proof (induction p arbitrary: u v)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  then have "a \<notin> Nt ` fst ` R"
    by (fastforce simp: nts_of_syms_def image_iff)
  note * = derive_Cons_undef[OF this]
  from Cons.prems have "nts_of_syms p \<inter> fst ` R = {}" by (auto simp: nts_of_syms_Cons)
  from Cons.IH[OF this]
  show ?case by (auto simp: *)
qed

lemma deriven_append_undef:
  assumes "nts_of_syms p \<inter> fst ` R = {}"
  shows "R \<turnstile> p @ u \<Rightarrow>(n) v \<longleftrightarrow> (\<exists>v'. v = p @ v' \<and> R \<turnstile> u \<Rightarrow>(n) v')"
  using derive_append_undef[OF assms]
  by (induction n arbitrary: u; fastforce simp: relpowp_Suc_left relcomppI)

lemma fst_Unwind_new: "fst ` Unwind_new R A A' \<subseteq> {A'}"
  by (auto simp: Unwind_new_def)

lemma Nt_in_set_iff_nts_of_syms: "Nt A \<in> set w \<longleftrightarrow> A \<in> nts_of_syms w"
  by (auto simp: nts_of_syms_def)

lemma Unwind_new_only_last:
  assumes A'R: "A' \<notin> Nonterminals R"
    and "Unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(n) u"
  shows "Nt A' \<notin> set u \<or> (\<exists>u'. u = u' @ [Nt A'] \<and> Nt A' \<notin> set u')"
  using assms(2)
proof (induction n arbitrary: u)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from Suc.prems obtain y where A'y: "Unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(n) y"
    and yu: "Unwind_new R A A' \<turnstile> y \<Rightarrow> u"
    by (auto simp: relpowp_Suc_right derive_singleton)
  from yu have "Nt A' \<in> set y" by (auto simp: derive_iff Unwind_new_def)
  with Suc.IH[OF A'y]
  obtain u' where [simp]: "y = u' @ [Nt A']" and A'u': "Nt A' \<notin> set u'" by auto
  with yu have "\<exists>v. (A',v) \<in> Unwind_new R A A' \<and> u = u' @ v"
    by (auto simp: derive_iff Unwind_new_def append_eq_append_conv2
        append_eq_Cons_conv Cons_eq_append_conv)
  with A'R A'u' show ?case
    by (auto simp: Unwind_new_def append_eq_append_conv2 append_eq_Cons_conv Nonterminals_def)
qed

lemma Unwind_new_sound:
  assumes A'R: "A' \<notin> Nonterminals R"
    and "Unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(n) vs"
    and A'vs: "Nt A' \<notin> set vs"
  shows "R \<turnstile> [Nt A] \<Rightarrow>* Nt A # vs"
  using assms(2-)
proof (induction n arbitrary: vs)
  case 0
  then show ?case by auto
next
  let ?R' = "Unwind_new R A A'"
  case (Suc n)
  then obtain y where y: "?R' \<turnstile> [Nt A'] \<Rightarrow> y" 
    and yvs: "?R' \<turnstile> y \<Rightarrow>(n) vs" by (auto simp: relpowp_Suc_left)
  show ?case
  proof (cases n)
    case 0
    with yvs have [simp]: "y = vs" by auto
    with Suc y have "\<exists>v. (A,Nt A # v) \<in> R \<and> y = v"
      apply (simp add: Unwind_new_def derive_singleton)
      by (auto simp: Nonterminals_def split: prod.splits)
    then show ?thesis apply (intro r_into_rtranclp)
      by (auto simp: derive_singleton)
  next
    case (Suc m)
    with yvs have "Nt A' \<in> set y"
      by (auto simp: relpowp_Suc_left Unwind_new_def derive_iff)
    with A'R y obtain v
      where AAv: "(A,Nt A # v) \<in> R" and [simp]: "y = v @ [Nt A']"
      by (auto simp: Unwind_new_def derive_singleton Nonterminals_def split: prod.splits)
    from AAv A'R have A'v: "Nt A' \<notin> set v" by (auto simp: Nonterminals_def)
    with fst_Unwind_new[of R A A']
    have "nts_of_syms v \<inter> fst ` ?R' = {}" by (auto simp: Nt_in_set_iff_nts_of_syms)
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

lemma right_Loop_Unwind:
  assumes A'R: "A' \<notin> Nonterminals R"
  shows "right_Loop (Unwind R A A') A' \<subseteq> Unwind_new R A A'"
  using assms
  by (auto simp: right_Loop_def Unwind_def Unwind_old_def Unwind_new_def Nonterminals_def)

lemma map_Tm_eq_map_Tm: "map Tm u = map Tm v \<longleftrightarrow> u = v"
  by (metis list.inj_map_strong sym.inject(2))

lemma deriver_mono: "R \<subseteq> S \<Longrightarrow> deriver R \<le> deriver S"
  by (force simp: deriver.simps)

lemma Unwind_sound:
  assumes "Unwind R A A' \<turnstile> u \<Rightarrow>r(n) v"
    and "Nt A' \<notin> set u"
    and "Nt A' \<notin> set v"
    and A'R: "A' \<notin> Nonterminals R"
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
      where BwR': "(B,w) \<in> Unwind_old R A A'"
        and [simp]: "u = l @ Nt B # map Tm r"
        and m: "Unwind R A A' \<turnstile> l @ w @ map Tm r \<Rightarrow>r(m) v"
      by (auto simp: relpowp_Suc_left append_eq_append_conv2 Unwind_def Unwind_new_def
          dest!:deriver_iff[THEN iffD1])
    from less.prems
    have A'l: "Nt A' \<notin> set l" by auto
    show ?thesis
    proof (cases "Nt A' \<in> set w")
      case True
      with BwR' A'R obtain w'
        where [simp]: "B = A" "w = w' @ [Nt A']"
          and Aw'R: "(A,w') \<in> R" and A'w': "Nt A' \<notin> set w'"
        by (auto simp: Unwind_old_def Nonterminals_def split: prod.splits)
      from m[folded append_assoc, unfolded derivern_append_map_Tm]
      obtain v' where v': "Unwind R A A' \<turnstile> (l @ w') @ [Nt A'] \<Rightarrow>r(m) v'"
        and [simp]: "v = v' @ map Tm r"
        by auto
      from less.prems have "\<not>ends_with A' v'" by (auto simp: ends_with_def)
      from extract_right_Loop[OF v' this]
      obtain n1 n2 u' w'' where len: "n1 + n2 < m"
        and n1: "right_Loop (Unwind R A A') A' \<turnstile> [Nt A'] \<Rightarrow>r(n1) u' @ [Nt A']"
        and w'': "(A', w'') \<in> Unwind R A A'" "\<not> ends_with A' w''"
        and n2: "Unwind R A A' \<turnstile> (l @ w') @ u' @ w'' \<Rightarrow>r(n2) v'" by auto
      from w'' A'R have A'w''R: "(A',w'') \<in> Unwind_new R A A'"
        and A'w'': "Nt A' \<notin> set w''"
        by (auto simp: Unwind_def Unwind_old_def Unwind_new_def Nonterminals_def ends_with_def)
      from n1 right_Loop_Unwind[OF A'R, THEN deriver_mono]
      have n1: "Unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>r(n1) u' @ [Nt A']"
        apply (auto simp: le_fun_def)
        by (metis relpowp_mono)
      from Unwind_new_only_last[OF A'R derivern_imp_deriven[OF n1]]
      have A'u': "Nt A' \<notin> set u'" by auto
      note n1
      also have "Unwind_new R A A' \<turnstile> u' @ [Nt A'] \<Rightarrow>r u' @ w''"
        using A'w''R by (auto simp: deriver_snoc_Nt simp del: append_assoc)
      finally have "Unwind_new R A A' \<turnstile> [Nt A'] \<Rightarrow>(Suc n1) u' @ w''"
        by (rule derivern_imp_deriven)
      from Unwind_new_sound[OF A'R this] A'u' A'w' A'w''
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
      with BwR' have "(B,w) \<in> R" by (auto simp: Unwind_old_def)
      then have "R \<turnstile> u \<Rightarrow> l @ w @ map Tm r" by (auto simp: derive_iff)
      also have "R \<turnstile> \<dots> \<Rightarrow>* v"
        apply (rule less.IH[OF _ m]) using A'R BwR' A'l False less.prems
        by (auto simp: Nonterminals_def split:prod.splits)
      finally show ?thesis.
    qed
  qed
qed

lemma Unwind_derives:
  assumes "Nt A' \<notin> set u" and "A' \<notin> Nonterminals R"
  shows "Unwind R A A' \<turnstile> u \<Rightarrow>* map Tm v \<longleftrightarrow> R \<turnstile> u \<Rightarrow>* map Tm v"
    (is "?l \<longleftrightarrow> ?r")
proof
  assume "?r"
  then have "R \<turnstile> u \<Rightarrow>l* map Tm v" by (simp add: derivels_iff_derives)
  then obtain n where "R \<turnstile> u \<Rightarrow>l(n) map Tm v"
    by (metis rtranclp_imp_relpowp)
  from Unwind_complete[OF this]
  show "?l".
next
  assume "?l"
  then have "Unwind R A A' \<turnstile> u \<Rightarrow>r* map Tm v" by (simp add: derivers_iff_derives)
  then obtain n where "Unwind R A A' \<turnstile> u \<Rightarrow>r(n) map Tm v"
    by (metis rtranclp_imp_relpowp)
  from Unwind_sound[OF this ] assms
  show "?r" by auto
qed

lemma Lang_Unwind:
  assumes A'R: "A' \<notin> Nonterminals R" and "B \<noteq> A'"
  shows "Lang (Unwind R A A') B = Lang R B"
  apply (rule Lang_eqI_derives)
  apply (rule Unwind_derives)
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

lemma Eps_free_Un: assumes "Eps_free R" "Eps_free S"
  shows "Eps_free (R \<union> S)"
  using assms by (auto simp: Eps_free_def)

lemma eq0_if_Eps_free:
  assumes "Eps_free R" "Eps_free S"
  shows "eq0 R S"
  using assms apply (simp add: Eps_free_def eq0_def split: prod.splits)
  by (metis append_is_Nil_conv derivehd.simps rtranclp.cases rtranclp.rtrancl_refl)

lemma Un_derives:
  assumes "Eps_free R" "Eps_free S" "Eps_free S'"
    and eq1: "eqT1 (R \<union> S) (R \<union> S')"
  shows "R \<union> S \<turnstile> v \<Rightarrow>* map T w \<longleftrightarrow> R \<union> S' \<turnstile> v \<Rightarrow>* map T w"
proof-
  have 1: "eq0 (R \<union> S) (R \<union> S')"
    using assms(1-3) eq0_if_Eps_free Eps_free_Un by auto 
  have 2: "eq0 (R \<union> S') (R \<union> S)"
    using assms(1-3) eq0_if_Eps_free Eps_free_Un by auto 
  from eqT1_derives[OF 1 eq1] eqT1_derives[OF 2]
  show ?thesis apply auto
    using eq1 eqT1_def by blast
qed

lemma eqT1_Unwind':
"eqT1 (Unwind_new R A A' \<union> Expand (Unwind_old R A A') (Unwind_old R A A') {A})
     (Unwind_new R A A' \<union> Unwind_old R A A')"
  sorry

lemma Unwind_derives:
  assumes "Eps_free R"
  shows "Unwind_new R A A' \<union>
   Expand (Unwind_old R A A') (Unwind_old R A A') {A} \<turnstile> w \<Rightarrow>* map T v
\<longleftrightarrow> Unwind_new R A A' \<union> Unwind_old R A A' \<turnstile> w \<Rightarrow>* map T v"
  apply (rule Un_derives)
  using assms
  by (simp_all add: Eps_free_Unwind_new Eps_free_Unwind_old Eps_free_Expand
      eqT1_Unwind')

*)

lemma Lang_Unwind_Expand:
  assumes ef: "Eps_free R"
  assumes "Solved R As" and "A' \<noteq> A" and A'RAs: "A' \<notin> Nonterminals R \<union> As"
    and "A' \<noteq> B"
  shows "Lang (Unwind_Expand R As A A') B = Lang R B"
  apply (simp add: Unwind_Expand_def Let_def del:)
  apply (subst Lang_Expand[OF Eps_free_Unwind_new])
  using A'RAs apply (force simp: Unwind_new_def Nonterminals_def)
  using Lang_Unwind
  apply (auto simp:  )
  sorry

lemma Eps_free_unwind_old_expand:
  assumes "Eps_free R"
  shows "Eps_free (Unwind_old_Expand R A A')"
  using assms
  by (auto simp: Unwind_old_Expand_def Eps_free_def)

lemma in_Nonterminals_if_starts_with: "(A, w) \<in> R \<Longrightarrow> starts_with B w \<Longrightarrow> B \<in> Nonterminals R"
  apply (cases "(B,w)" rule: starts_with.cases)
    apply (auto simp: Nonterminals_def split: prod.split)
  by (metis list.set_intros(1) prod.inject)
  
lemma Loop_free_Unwind_old_Expand:
  assumes "A' \<noteq> A"
  shows "Loop_free (Unwind_old_Expand R A A') A"
  using assms by (auto simp: Loop_free_def starts_with_iff Unwind_old_Expand_def Cons_eq_append_conv)

lemma Solved_Unwind_old_Expand:
  assumes "Solved R As"
    and "Eps_free R"
  shows "Solved (Unwind_old_Expand R A A') (insert A As)"
  using assms
  apply (auto simp: Cons_eq_append_conv Solved_def starts_with_iff Unwind_old_Expand_def
      Eps_free_Nil
      split: prod.splits)
  by metis+

lemma Solved_Un: "Solved (R \<union> S) As \<longleftrightarrow> Solved R As \<and> Solved S As"
  by (auto simp:Solved_def)

lemma Loop_free_unwind_new:
  assumes "A' \<noteq> A"
  shows "Loop_free (Unwind_new R A A') A"
  using assms by (auto simp: Loop_free_def starts_with_iff Unwind_new_def Cons_eq_append_conv)

definition Rhs1s where "Rhs1s R = [A. (B, Nt A # w) \<leftarrow> R]"

lemma set_Rhs1s: "set (Rhs1s R) = Rhs1 (set R)"
  by (auto simp: Rhs1s_def Rhs1_def Lnt_def rhs1_def image_Collect)

definition Rex :: "(int,int) prod list"
  where "Rex = [
  (1,[Nt 2, Nt 2]), (1, [Tm 0]),
  (2, [Nt 2, Nt 2, Nt 2]), (2, [Tm 0, Nt 2]), (2, [Tm 1])]"

definition Rex2 :: "(int,int) prod list"
  where "Rex2 = [
  (1, [Nt 2, Tm 0]),
  (2, [Nt 1, Tm 2]), (2, [Tm 1, Nt 1]), (2, [Tm 3])]"

value "unwind Rex 2 3"

(*
definition "expand_rec R A = (
  let X = filter (\<lambda>(B,w). starts_with A w) R in
  diff_list X R @ [(B,v@w). (B,N C # w) \<leftarrow> R, C = A, (D,v) \<leftarrow> R, D = A]
)"

value "expand_rec Rex2 1"

lemma
  assumes "eps_free R"
    and "\<forall>(B,w) \<in> set R. B = A \<longrightarrow> \<not>starts_with A w"
    and "(B,w) \<in> set (expand_rec R A)"
  shows "\<not>starts_with A w"
  sorry
*)

lemma Expand_Loop_free:
  assumes "A \<notin> As"
    and "Solved S {A}"
    and "Eps_free S"
    and "Loop_free R A"
  shows "Loop_free (Expand R S As) A"
  using assms
  by (auto simp: Expand_def Cons_eq_append_conv Solved_not
      starts_with_iff Eps_free_Nil
      Loop_free_def split:prod.splits)

lemma expand_solved:
  assumes "Solved S As"
    and "Eps_free S"
  shows "Solved (Expand R S As) As"
  using assms
  by (fastforce simp: Solved_def Expand_def starts_with_iff
      Cons_eq_append_conv Eps_free_Nil
      split: prod.splits)

lemma expand_solved2:
  assumes "Solved R As"
    and "Eps_free R"
  shows "Solved (Expand R R Bs) As"
  using assms
  by (force simp: Solved_def Expand_def starts_with_iff
      Cons_eq_append_conv Eps_free_Nil
      split: prod.splits)

definition Rex3 :: "(int,int) prod list" where "Rex3 = [
(0,[Nt 0]), (1,[Nt 1, Nt 0])]"

value "unwind_new Rex3 1 2"

value "expand (unwind_new Rex3 1 2) (unwind_old_expand Rex3 1 2) [0]"

text \<open>The following is true without assuming solvedness of \<open>As\<close>,
because of the definition of \<open>Expand\<close>.\<close>

lemma hd_in_Nonterminals: "(A,Nt B#w) \<in> R \<Longrightarrow> B \<in> Nonterminals R"
  apply (auto simp: Nonterminals_def split: prod.splits)
  by (metis list.set_intros(1) prod.inject)

lemma hd2_in_Nonterminals: "(A,x#Nt B#w) \<in> R \<Longrightarrow> B \<in> Nonterminals R"
  apply (auto simp: Nonterminals_def split: prod.splits)
  by (metis list.set_intros(1,2) prod.inject)
  

lemma solved_expand_unwind_new:
  assumes "A' \<notin> As"
    and "Eps_free R" "A' \<notin> Nonterminals R"
    and "Solved R As"
  shows "Solved (Expand (Unwind_new R A A')
 (Unwind_old_Expand R A A') (insert A As))
  (insert A' (insert A As))"
  using assms
  apply (intro SolvedI)
  by (auto simp: Expand_def Solved_not
      Unwind_new_def Unwind_old_Expand_def neq_Nil_conv starts_with_iff
      Cons_eq_append_conv Eps_free_Nil hd_in_Nonterminals hd2_in_Nonterminals)


text \<open>Instead, preservation of the language requires solvedness
of \<open>R\<close> with respect to \<open>As\<close>.\<close>

lemma Solved_Unwind_Expand:
  assumes ef: "Eps_free R" and A': "A' \<notin> Nonterminals R \<union> As"
    and so: "Solved R As"
  shows "Solved (Unwind_Expand R As A A') (insert A (insert A' As))"
proof-
  have so2: "Solved R (insert A' As)"
    using so A' 
    by (auto simp: Solved_def in_Nonterminals_if_starts_with split: prod.splits)
  show ?thesis
    apply (auto simp: Unwind_Expand_def Solved_Un
        Solved_Unwind_old_Expand[OF so2 ef])
    apply (subst insert_commute)
    apply (rule solved_expand_unwind_new)
    using assms by auto
qed

lemma solved_insert:
  assumes "Solved R As"
    and "\<forall>(B,w) \<in> R. \<not>starts_with A w"
  shows "Solved R (insert A As)"
  using assms
  by (auto simp: Solved_def)

lemma Eps_free_Unwind_Expand:
  assumes "Eps_free R"
  shows "Eps_free (Unwind_Expand R As A A')"
proof-
  note 1 =  Eps_free_unwind_old_expand[OF assms]
  with Eps_free_Expand[OF this Eps_free_Unwind_new]
  show ?thesis
  apply (auto intro!:Eps_freeI simp: Eps_free_Nil Unwind_Expand_def)
    by (smt (verit) Eps_free_Nil Eps_free_Expand Eps_free_Unwind_new)
qed

lemma Loop_free_Expand:
  assumes "Loop_free R A"
    and "Solved S (insert A As)"
    and "Eps_free S"
  shows "Loop_free (Expand R S As) A"
  using assms
  by (auto intro!:Loop_freeI dest: Loop_freeD Solved_not
      simp: Expand_def starts_with_iff append_eq_Cons_conv Eps_free_Nil)

lemma Loop_free_Unwind_Expand:
  assumes A': "A' \<noteq> A"
    and so: "Solved R As"
    and ef: "Eps_free R"
  shows "Loop_free (Unwind_Expand R As A A') A"
proof-
  from Solved_Unwind_old_Expand[OF so ef]
  have 1: "Solved (Unwind_old_Expand R A A') (insert A As)"
    by auto
  then have 2: "Solved (Unwind_old_Expand R A A') As"
    by (auto simp: Solved_def)
  show ?thesis
    apply (auto simp: Unwind_Expand_def Loop_free_Un Loop_free_Unwind_old_Expand[OF A'])
    apply (rule Loop_free_Expand[OF Loop_free_unwind_new[OF A']])
    apply (simp)
     apply (rule 1)
    using Eps_free_unwind_old_expand[OF ef].
qed

fun realtime where
  "realtime R (A#As) (A'#As') = unwind_expand (realtime R As As') (As@As') A A'"
| "realtime R _ _ = R"

context fixes R :: "('n,'t) Prods" begin
fun Realtime where
  "Realtime (A#As) (A'#As') =
  Unwind_Expand (Realtime As As') (set (As@As')) A A'"
| "Realtime _ _ = R"

end

lemma Solved_if_disj:
  assumes disj: "set As' \<inter> Nonterminals R = {}"
  shows "Solved R (set As')"
  using disj
  by (auto simp: Solved_def dest:in_Nonterminals_if_starts_with)


lemma Nonterminals_Realtime: "Nonterminals (Realtime R As As') \<subseteq> Nonterminals R \<union> set As \<union> set As'"
  sorry

context
  fixes R :: "('n,'t)Prods"
  assumes ef: "Eps_free R"
begin

lemma Eps_free_Realtime:
  shows "Eps_free (Realtime R As As')"
proof (induction As As' rule: Realtime.induct)
  case (1 A As A' As')
  then show ?case apply auto sorry
next
  case ("2_1" uv)
  then show ?case sorry
next
  case ("2_2" uu)
  then show ?case sorry
qed

lemma Solved_Realtime:
  assumes "Eps_free R"
    and "length As \<le> length As'"
    and "distinct (As @ As')" and "set As' \<inter> Nonterminals R = {}"
  shows "Solved (Realtime R As As') (set As \<union> set As')"
  using assms
proof (induction As As' rule: Realtime.induct)
  case (1 A As A' As')
  with Nonterminals_Realtime[of R]
    Solved_Unwind_Expand[where A=A and A'=A' and As = "set As \<union> set As'" and R ="Realtime R As As'"]
  show ?case by (auto intro!: simp: Eps_free_Realtime insert_commute) 
next
  case ("2_1" As')
  with Solved_if_disj show ?case by auto
next
  case ("2_2" As)
  then show ?case by (auto simp: Solved_def)
qed

lemma Lang_Realtime:
  assumes "Eps_free R"
    and "length As \<le> length As'"
    and "distinct (As @ As')" and "set As' \<inter> Nonterminals R = {}"
    and "B \<notin> set As'"
  shows "Lang (Realtime R As As') B = Lang R B"
  using assms(2-)
proof (induction As As' rule: Realtime.induct)
  case (1 A As A' As')
  with Nonterminals_Realtime[of R] Solved_Realtime[OF \<open>Eps_free R\<close> ]
    Lang_Unwind_Expand[where A=A and A'=A' and As = "set As \<union> set As'" and R ="Realtime R As As'" and B=B]
  show ?case by (auto intro!: simp: Eps_free_Realtime insert_commute) 
next
  case ("2_1" As')
  then show ?case by auto
next
  case ("2_2" As)
  then show ?case by (auto simp: Solved_def)
qed


end

value "unwind_expand [(1,[N 1 :: (int,int)sym, N 1])] [] 1 2"

theorem GNF:
fixes R :: "('n,'t)Prods" and new :: "'n set \<Rightarrow> 'n"
assumes "\<And>X. finite X \<Longrightarrow> new (X) \<notin> X"
assumes "finite R" and "Eps_free R" and "Rhs1 R \<subseteq> set As" "distinct As"
shows "\<exists>R'::('n ,'t)Prods. Lang S R' = Lang S R \<and> rtps R'"
  oops

end