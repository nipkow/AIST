(*<*)
theory Replace_Terminals
  imports Greibach_Normal_Form.Greibach_Normal_Form Context_Free_Grammar.Expansion
begin
(*>*)

(* unused, but a better replacement for inj_on_cong *)
lemma inj_on_cong2: "(\<And>a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> A = B \<Longrightarrow> inj_on f A \<longleftrightarrow> inj_on g B"
  by (auto simp: inj_on_def)

section \<open>Replacing Terminals by (Fresh) Nonterminals\<close>

lemma Lhss_image_Pair: "Lhss ((\<lambda>x. (f x, g x)) ` X) = f ` X"
  by (auto simp: Lhss_def)

lemma Rhss_image_Pair_inj_on:
  assumes f: "inj_on f X" and x: "x \<in> X"
  shows "Rhss ((\<lambda>x. (f x, g x)) ` X) (f x) = {g x}"
  using inj_onD[OF f] x by (auto simp: Rhss_def)

text \<open>First, we define the grammar where fresh nonterminals produce the corresponding terminals.
We abstract the map from terminals to the fresh nonterminals by \<open>f\<close>.\<close>

abbreviation Replace_Tm_new where
"Replace_Tm_new f as \<equiv> (\<lambda>a. (f a, [Tm a])) ` as"

text \<open>Expansion with respect to this grammar should preserve terminals and
locked nonterminals,
and the fresh nonterminals should be reverted to the original terminals.\<close>

lemma Rhss_Un_Replace_Tm_new:
  assumes inj: "inj_on f as" and a: "a \<in> as" and fa: "f a \<notin> Lhss P"
  shows "Rhss (P \<union> Replace_Tm_new f as) (f a) = {[Tm a]}"
  by (simp add: Rhss_Un Rhss_image_Pair_inj_on[OF inj a] fa[unfolded notin_Lhss_iff_Rhss])

lemma Expand_sym_Replace_Tm_Tm:
  "Expand_sym (Replace_Tm_new f as) L (Tm a) = {[Tm a]}"
  by (auto simp: Expand_sym_def)

lemma Expand_sym_Replace_Tm_Nt:
  assumes inj: "inj_on f as" and A: "A \<in> L"
  shows "Expand_sym (Replace_Tm_new f as) L (Nt A) = {[Nt A]}"
  using A by (auto simp: Expand_sym_def)

lemma Expand_sym_Replace_Tm_new:
  assumes inj: "inj_on f as" and L: "L \<inter> f ` as = {}" and a: "a \<in> as"
  shows "Expand_sym (Replace_Tm_new f as) L (Nt (f a)) = {[Tm a]}"
  using a L by (auto simp: Expand_sym_def Rhss_image_Pair_inj_on[OF inj])

text \<open>The function replacing a terminal by the corresponding fresh nonterminal is
formalized as follows.\<close>

definition replace_Tm_sym where
"replace_Tm_sym f x = (case x of Tm a \<Rightarrow> Nt (f a) | _ \<Rightarrow> x)"

lemma replace_Tm_sym_simps:
  "replace_Tm_sym f (Nt A) = Nt A"
  "replace_Tm_sym f (Tm a) = Nt (f a)"
  by (auto simp: replace_Tm_sym_def)

lemma Expand_all_syms_Replace_Tm:
  assumes inj: "inj_on f as" and L: "L \<inter> f ` as = {}"
    and \<alpha>: "Tms_syms \<alpha> \<subseteq> as" "Nts_syms \<alpha> \<subseteq> L"
  shows "Expand_all_syms (Replace_Tm_new f as) L (map (replace_Tm_sym f) \<alpha>) = {\<alpha>}"
  by (insert \<alpha>, induction \<alpha>,
      auto split: sym.splits simp: replace_Tm_sym_def
      Expand_sym_Replace_Tm_new[OF inj L] Expand_sym_Replace_Tm_Nt[OF inj] insert_conc)


subsection \<open>Mapping to Fresh Nonterminals\<close>

text \<open>We provide an implementation of a function that maps terminals to corresponding
fresh nonterminals.\<close>

fun fresh_map :: "'a :: fresh0 set \<Rightarrow> 'b list \<Rightarrow> 'b \<rightharpoonup> 'a" where
  "fresh_map A [] = Map.empty"
| "fresh_map A (x#xs) = (let a = fresh0 A in (fresh_map (insert a A) xs)(x \<mapsto> a))"

abbreviation fresh_fun where
"fresh_fun A xs x \<equiv> the (fresh_map A xs x)"

lemma fresh_fun_notIn: "finite A \<Longrightarrow> x \<in> set xs \<Longrightarrow> fresh_fun A xs x \<notin> A"
  apply (induction xs arbitrary: A)
  by (auto simp: Let_def fresh0_notIn)

lemma fresh_fun_disj: "finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> X \<subseteq> set xs \<Longrightarrow> B \<inter> fresh_fun A xs ` X = {}"
  by (force simp: fresh_fun_notIn)

lemma fresh_fun_inj_on: "finite A \<Longrightarrow> inj_on (fresh_fun A xs) (set xs)"
proof (induction xs arbitrary: A)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  define a where "a = fresh0 A"
  from Cons
  have IH: "inj_on (fresh_fun (insert a A) xs) (set xs)"
    and fin: "finite (insert a A)" by auto
  { fix y assume "y \<in> set xs"
    from fresh_fun_notIn[OF fin this]
    have "fresh_fun (insert a A) xs y \<notin> A" "a \<noteq> fresh_fun (insert a A) xs y" by auto
  } note * = this this(2)[symmetric]
  show ?case
    by (auto simp flip: a_def intro!: inj_onI split: if_splits simp: inj_onD[OF IH] *)
qed

lemma fresh_fun_distinct:
  assumes fin: "finite A"
  shows "distinct (map (fresh_fun A xs) xs) \<longleftrightarrow> distinct xs" (is "?l \<longleftrightarrow> ?r")
  using fresh_fun_inj_on[OF fin] by (auto simp: distinct_map)

subsubsection \<open>Replacing non-head terminals\<close>

definition replace_Tm_tl_syms where
"replace_Tm_tl_syms f xs = (case xs of x#xs' \<Rightarrow> x # map (replace_Tm_sym f) xs' | _ \<Rightarrow> xs)"

abbreviation Replace_Tm_tl_old where
"Replace_Tm_tl_old f P \<equiv> {(A, replace_Tm_tl_syms f \<alpha>) | A \<alpha>. (A,\<alpha>) \<in> P}"

definition Replace_Tm_tl where
"Replace_Tm_tl f P = Replace_Tm_tl_old f P \<union> Replace_Tm_new f (Tms P)"

definition replace_Tm_tl where
"replace_Tm_tl f P = [(A, replace_Tm_tl_syms f \<alpha>). (A,\<alpha>) \<leftarrow> P] @ [(f a, [Tm a]). a \<leftarrow> tms P]"

lemma set_replace_Tm_tl: "set (replace_Tm_tl f P) = Replace_Tm_tl f (set P)"
  by (auto simp: replace_Tm_tl_def Replace_Tm_tl_def set_tms)

lemma Expand_all_syms_Replace_Tm_tl:
  assumes inj: "inj_on f as" and L: "L \<inter> f ` as = {}"
    and \<alpha>: "Tms_syms \<alpha> \<subseteq> as" "Nts_syms \<alpha> \<subseteq> L"
  shows "Expand_all_syms (Replace_Tm_new f as) L (replace_Tm_tl_syms f \<alpha>) = {\<alpha>}"
proof (cases \<alpha>)
  case Nil
  then show ?thesis by (simp add: replace_Tm_tl_syms_def)
next
  case [simp]: (Cons x xs)
  from \<alpha> have xs: "Tms_syms xs \<subseteq> as" "Nts_syms xs \<subseteq> L" by auto
  note [simp] = Expand_all_syms_Replace_Tm[OF inj L xs]
  show ?thesis
  proof (cases x)
    case [simp]: (Nt A)
    with \<alpha> have "A \<in> L" by auto
    note [simp] = Expand_sym_Replace_Tm_Nt[OF inj this]
    show ?thesis by (auto simp: replace_Tm_tl_syms_def insert_conc)
  next
    case [simp]: (Tm a)
    show ?thesis by (auto simp: replace_Tm_tl_syms_def insert_conc Expand_sym_Replace_Tm_Tm)
  qed
qed

lemma Expand_all_Replace_Tm_tl:
  assumes inj: "inj_on f as" and L: "L \<inter> f ` as = {}"
    and P: "Tms P \<subseteq> as" "Rhs_Nts P \<subseteq> L"
  shows "Expand_all (Replace_Tm_new f as) L (Replace_Tm_tl_old f P) = P"
proof-
  have *: "(A,\<alpha>) \<in> P \<Longrightarrow> Expand_all_syms (Replace_Tm_new f as) L (replace_Tm_tl_syms f \<alpha>) = {\<alpha>}" for A \<alpha>
    apply (rule Expand_all_syms_Replace_Tm_tl[OF inj L])
    using P by (auto simp: Tms_def Rhs_Nts_def)
  then show ?thesis by (force simp: Expand_def)
qed

lemma Lang_Replace_Tm_tl:
  assumes inj: "inj_on f (Tms P)" and disj: "Nts P \<inter> f ` Tms P = {}"
    and A: "A \<notin> f ` Tms P"
  shows "Lang (Replace_Tm_tl f P) A = Lang P A"
    (is "?l = ?r")
proof-
  from disj have L: "Lhss P \<inter> f ` Tms P = {}" and R: "Rhs_Nts P \<inter> f ` Tms P = {}"
    by (auto simp: Nts_Lhss_Rhs_Nts)
  have "?l = Lang (Replace_Tm_tl_old f P \<union> Replace_Tm_new f (Tms P)) A"
    by (simp add: Replace_Tm_tl_def)
  also have "\<dots> = Lang (Expand_all (Replace_Tm_new f (Tms P)) (Nts P) (Replace_Tm_tl_old f P) \<union> Replace_Tm_new f (Tms P)) A"
    apply (subst Lang_Expand_all)
    by (auto simp: Nts_def Lhss_def)
  also have "\<dots> = Lang (P \<union> Replace_Tm_new f (Tms P)) A"
    using Expand_all_Replace_Tm_tl[OF inj disj]
    by (simp add: Nts_Lhss_Rhs_Nts)
  also have "\<dots> = ?r"
    apply (rule Lang_Un_disj_Lhss) using disj A by (auto simp: Lhss_image_Pair)
  finally show ?thesis.
qed




definition GNF where
"GNF P = (\<forall>(A,\<alpha>) \<in> P. \<exists>a Bs. \<alpha> = Tm a # map Nt Bs)"

abbreviation gnf where
"gnf P \<equiv> GNF (set P)"

lemma GNF_I: "(\<And>A \<alpha>. (A,\<alpha>) \<in> P \<Longrightarrow> \<exists>a Bs. \<alpha> = Tm a # map Nt Bs) \<Longrightarrow> GNF P"
  by (auto simp: GNF_def)

lemma GNF_Un: "GNF (P \<union> Q) \<longleftrightarrow> GNF P \<and> GNF Q"
  by (auto simp: GNF_def ball_Un)

lemma GNF_Replace_Tm_tl:
  assumes P: "GNF_hd P"
  shows "GNF (Replace_Tm_tl f P)"
  apply (unfold Replace_Tm_tl_def set_append GNF_Un)
proof (intro conjI GNF_I)
  fix A \<alpha>' assume "(A,\<alpha>') \<in> Replace_Tm_tl_old f P"
  then obtain \<alpha> where "(A,\<alpha>) \<in> P" and \<alpha>': "\<alpha>' = replace_Tm_tl_syms f \<alpha>" by auto
  with P obtain a \<beta> where "\<alpha> = Tm a # \<beta>" by (auto simp: GNF_hd_def)
  with \<alpha>' have \<alpha>': "\<alpha>' = Tm a # map (replace_Tm_sym f) \<beta>" by (auto simp: replace_Tm_tl_syms_def)
  define Bs where "Bs \<equiv> [case x of Nt B \<Rightarrow> B | Tm b \<Rightarrow> f b. x \<leftarrow> \<beta>]"
  have "map (replace_Tm_sym f) \<beta> = map Nt Bs"
    by (unfold Bs_def, induction \<beta>, auto simp: replace_Tm_sym_simps split: sym.splits)
  with \<alpha>' have "\<alpha>' = Tm a # map Nt Bs" by simp
  then show "\<exists>a Bs. \<alpha>' = Tm a # map Nt Bs" by blast
qed auto

definition GNF_of :: "'n list \<Rightarrow> 't list \<Rightarrow> ('n::fresh0,'t)Prods \<Rightarrow> ('n,'t)Prods" where
"GNF_of As as P =
 (let As' = freshs (set As) As;
      P' = Expand_tri (As' @ rev As) (Solve_tri As As' (Eps_elim P));
      f = fresh_fun (set As \<union> set As') as
  in Replace_Tm_tl f P')"

definition gnf_of :: "('n::fresh0,'t)prods \<Rightarrow> ('n,'t)prods" where
"gnf_of P =
 (let As = nts P;
      As' = freshs (set As) As;
      P' = expand_tri (As' @ rev As) (solve_tri As As' (eps_elim P));
      f = fresh_fun (set As \<union> set As') (tms P)
  in replace_Tm_tl f P')"

lemma set_gnf_of: "set (gnf_of P) = GNF_of (nts P) (tms P) (set P)"
  by (simp add: gnf_of_def GNF_of_def Let_def set_replace_Tm_tl set_expand_tri set_solve_tri set_eps_elim)

lemma GNF_of_via_GNF_hd_of:
  "GNF_of As as P =
  (let As' = freshs (set As) As;
       f = fresh_fun (set As \<union> set As') as
   in Replace_Tm_tl f (GNF_hd_of As P))"
  by (auto simp: GNF_of_def GNF_hd_of_def Let_def)

theorem GNF_GNF_of:
  assumes "distinct As" and "Nts P \<subseteq> set As"
  shows "GNF (GNF_of As as P)"
  apply (unfold GNF_of_via_GNF_hd_of Let_def)
  apply (rule GNF_Replace_Tm_tl)
  using GNF_hd_GNF_hd_of[OF assms].

theorem Lang_GNF_of:
  assumes As: "distinct As" and PAs: "Nts P \<subseteq> set As" and Pas: "Tms P \<subseteq> set as"
    and AAs: "A \<in> set As"
  shows "Lang (GNF_of As as P) A = Lang P A - {[]}"
proof-
  define As' where "As' = freshs (set As) As"
  define f where "f = fresh_fun (set As \<union> set As') as"
  show ?thesis
    apply (unfold GNF_of_via_GNF_hd_of Let_def)
    apply (fold As'_def)
    apply (fold f_def)
    apply (fold Lang_GNF_hd_of[OF As PAs AAs])
  proof (rule Lang_Replace_Tm_tl[OF _ _ ])
    have as: "Tms (GNF_hd_of As P) \<subseteq> set as"
      using subset_trans[OF Tms_GNF_hd_of Pas].
    show "inj_on f (Tms (GNF_hd_of As P))"
      apply (unfold f_def)
      apply (rule inj_on_subset[OF fresh_fun_inj_on])
      by (simp_all add: finite_Nts as)
    have "(set As \<union> set As') \<inter> f ` Tms (GNF_hd_of As P) = {}"
      apply (unfold f_def)
      apply (rule fresh_fun_disj)
      by (simp_all add: as)
    with AAs as PAs
    show "A \<notin> f ` Tms (GNF_hd_of As P)"
      and "Nts (GNF_hd_of As P) \<inter> f ` Tms (GNF_hd_of As P) = {}"
      by (auto simp: As'_def dest!: subsetD[OF Nts_GNF_hd_of])
  qed
qed

value "GNF_of [1,2,3] [0,1] {
(1::nat, [Nt 2, Nt 3]),
(2,[Nt 3, Nt 1]), (2, [Tm (1::int)]),
(3,[Nt 1, Nt 2]), (3,[Tm 0])}"


corollary gnf_gnf_of: "gnf (gnf_of P)"
  apply (unfold set_gnf_of)
  apply (rule GNF_GNF_of)
  using distinct_nts by (auto simp: set_nts)

theorem lang_gnf_of:
  assumes A: "A \<in> set (nts P)"
  shows "lang (gnf_of P) A = lang P A - {[]}"
  apply (unfold set_gnf_of)
  apply (rule Lang_GNF_of)
  using distinct_nts A by (auto simp: set_nts set_tms)

value "remdups (gnf_of [
(1::nat, [Nt 2, Nt 3]),
(2,[Nt 3, Nt 1]), (2, [Tm (1::int)]),
(3,[Nt 1, Nt 2]), (3,[Tm 0])])"

end