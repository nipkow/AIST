theory Replace_Terminals
  imports Context_Free_Grammar.Context_Free_Grammar
begin

(* unused, but a better replacement for inj_on_cong *)
lemma inj_on_cong2: "(\<And>a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> A = B \<Longrightarrow> inj_on f A \<longleftrightarrow> inj_on g B"
  by (auto simp: inj_on_def)


fun fresh_map :: "'a :: fresh0 set \<Rightarrow> 'b list \<Rightarrow> 'b \<Rightarrow> 'a" where
  "fresh_map A [] = undefined"
| "fresh_map A (x#xs) = (let a = fresh0 A in (fresh_map (insert a A) xs)(x := a))"

lemma fresh_map_notIn: "finite A \<Longrightarrow> x \<in> set xs \<Longrightarrow> fresh_map A xs x \<notin> A"
  apply (induction xs arbitrary: A)
  by (auto simp: Let_def fresh0_notIn)

lemma inj_on_fresh_map: "finite A \<Longrightarrow> inj_on (fresh_map A xs) (set xs)"
proof (induction xs arbitrary: A)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  define a where "a = fresh0 A"
  from Cons
  have IH: "inj_on (fresh_map (insert a A) xs) (set xs)"
    and fin: "finite (insert a A)" by auto
  { fix y assume "y \<in> set xs"
    from fresh_map_notIn[OF fin this]
    have "fresh_map (insert a A) xs y \<notin> A" "a \<noteq> fresh_map (insert a A) xs y" by auto
  } note * = this this(2)[symmetric]
  show ?case
    by (auto simp flip: a_def intro!: inj_onI split: if_splits simp: inj_onD[OF IH] *)
qed

lemma fresh_map_distinct:
  assumes fin: "finite A"
  shows "distinct (map (fresh_map A xs) xs) \<longleftrightarrow> distinct xs" (is "?l \<longleftrightarrow> ?r")
  using inj_on_fresh_map[OF fin] by (auto simp: distinct_map)

definition replace_grammar where
"replace_grammar As as = [(fresh_map As as a, [Tm a]). a \<leftarrow> as]"

lemma Lang_Un_replace_grammar:
  assumes As: "Nts P \<subseteq> As" and A: "A \<in> Nts P"
  shows "Lang (P \<union> set (replace_grammar As as)) A = Lang P A"
  sorry

lemma lhss_replace_grammar: "lhss (replace_grammar As as) = fresh_map As as ` set as"
  by (auto simp: replace_grammar_def Lhss_def)

lemma rhss_replace_grammar:
  assumes fin: "finite As" and a: "a \<in> set as"
  shows "Rhss (set (replace_grammar As as)) (fresh_map As as a) = {[Tm a]}"
  using inj_on_fresh_map[OF fin, of as, THEN inj_onD]
  by (auto simp: replace_grammar_def Rhss_def a)

lemma Rhss_Un_replace_grammar:
  assumes fin: "finite As" and As: "Lhss P \<subseteq> As" and a: "a \<in> set as"
  shows "Rhss (P \<union> set (replace_grammar As as)) (fresh_map As as a) = {[Tm a]}"
proof-
  from As fresh_map_notIn[OF fin a]
  have "fresh_map As as a \<notin> Lhss P" by auto
  then show ?thesis
    by (simp add: Rhss_Un rhss_replace_grammar[OF fin a] notin_Lhss_iff_Rhss)
qed

lemma Lang_replace_grammar1:
  assumes fin: "finite As" and PAs: "Lhss P \<subseteq> As" and a: "a \<in> set as"
    and AAs: "A \<in> As"
  shows "Lang (insert (A, \<alpha> @ Nt (fresh_map As as a) # \<beta>) (P \<union> set (replace_grammar As as))) =
         Lang (insert (A, \<alpha> @ Tm a # \<beta>) (P \<union> set (replace_grammar As as)))"
proof-
  note Rhss = Rhss_Un_replace_grammar[OF fin PAs a]
  have neq: "A \<noteq> fresh_map As as a" using fresh_map_notIn[OF fin a] AAs by auto
  note * = Lang_subst1[OF neq Rhss, where \<alpha> = \<alpha> and \<gamma> = \<beta>, simplified]
  show ?thesis by (simp add: *)
qed

definition replace_sym where
"replace_sym As as x = (case x of Tm a \<Rightarrow> Nt (fresh_map As as a) | _ \<Rightarrow> x)"

lemma replace_sym_Nt: "replace_sym As as (Nt A) = Nt A"
  and replace_sym_Tm: "replace_sym As as (Tm a) = Nt (fresh_map As as a)"
  by (auto simp: replace_sym_def)

lemma Lang_replace_grammar_append:
  assumes fin: "finite As" and PAs: "Lhss P \<subseteq> As" and Pas: "Tms P \<subseteq> set as"
    and AAs: "A \<in> As"
  shows "Tms_syms \<beta> \<subseteq> set as \<Longrightarrow>
 Lang (insert (A, \<alpha> @ map (replace_sym As as) \<beta>) (P \<union> set (replace_grammar As as))) =
 Lang (insert (A, \<alpha> @ \<beta>) (P \<union> set (replace_grammar As as)))"
proof (induction \<beta> arbitrary: \<alpha>)
  case Nil
  show ?case by simp
next
  case (Cons x \<beta>)
  from Cons.prems have "Tms_syms \<beta> \<subseteq> set as" by auto
  note IH = Cons.IH[OF this, where \<alpha> = "\<alpha> @ [x]"]
  show ?case
  proof (cases x)
    case (Nt A)
    with IH show ?thesis by (auto simp: replace_sym_Nt)
  next
    case [simp]: (Tm a)
    from Cons.prems have "a \<in> set as" by auto
    note * = Lang_replace_grammar1[OF fin PAs this AAs]
    from IH show ?thesis by (simp add: replace_sym_Tm *)
  qed
qed



end