theory Replace_Terminals
  imports Context_Free_Grammar.Context_Free_Grammar
begin

(* unused, but a better replacement for inj_on_cong *)
lemma inj_on_cong2: "(\<And>a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> A = B \<Longrightarrow> inj_on f A \<longleftrightarrow> inj_on g B"
  by (auto simp: inj_on_def)

lemma Lhss_image_Pair: "Lhss ((\<lambda>x. (f x, g x)) ` X) = f ` X"
  by (auto simp: Lhss_def)

lemma Rhss_image_Pair_inj_on:
  assumes f: "inj_on f X" and x: "x \<in> X"
  shows "Rhss ((\<lambda>x. (f x, g x)) ` X) (f x) = {g x}"
  using inj_onD[OF f] x by (auto simp: Rhss_def)

lemma Lang_Un_disj_Lhss:
  assumes disj: "Nts P \<inter> Lhss Q = {}" and A: "A \<in> Nts P"
  shows "Lang (P \<union> Q) A = Lang P A"
  sorry



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

definition Replace_grammar where
"Replace_grammar f as = (\<lambda>a. (f a, [Tm a])) ` as"

definition replace_grammar where
"replace_grammar f as = [(f a, [Tm a]). a \<leftarrow> as]"

lemma set_replace_grammar: "set (replace_grammar f as) = Replace_grammar f (set as)"
  by (auto simp: replace_grammar_def Replace_grammar_def)

lemma Lhss_Replace_grammar: "Lhss (Replace_grammar f as) = f ` as"
  by (simp add: Replace_grammar_def Lhss_image_Pair)

lemma Rhss_Replace_grammar:
  assumes inj: "inj_on f as" and a: "a \<in> as"
  shows "Rhss (Replace_grammar f as) (f a) = {[Tm a]}"
  by (auto simp: Replace_grammar_def Rhss_image_Pair_inj_on[OF inj a])

lemma Rhss_Un_Replace_grammar:
  assumes inj: "inj_on f as" and a: "a \<in> as" and fa: "f a \<notin> Lhss P"
  shows "Rhss (P \<union> Replace_grammar f as) (f a) = {[Tm a]}"
  by (simp add: Rhss_Un Rhss_Replace_grammar[OF inj a] fa[unfolded notin_Lhss_iff_Rhss])

lemma Lang_Replace_grammar1:
  assumes inj: "inj_on f as" and a: "a \<in> as"
    and faP: "f a \<notin> Lhss P" and A: "A \<noteq> f a"
  shows "Lang (insert (A, \<alpha> @ Nt (f a) # \<beta>) (P \<union> Replace_grammar f as)) =
         Lang (insert (A, \<alpha> @ Tm a # \<beta>) (P \<union> Replace_grammar f as))"
proof-
  note Rhss = Rhss_Un_Replace_grammar[OF inj a faP]
  note * = Lang_subst1[OF A Rhss, where \<alpha> = \<alpha> and \<gamma> = \<beta>, simplified]
  show ?thesis by (simp add: *)
qed

definition replace_sym where
"replace_sym f x = (case x of Tm a \<Rightarrow> Nt (f a) | _ \<Rightarrow> x)"

lemma replace_sym_Nt: "replace_sym f (Nt A) = Nt A"
  and replace_sym_Tm: "replace_sym f (Tm a) = Nt (f a)"
  by (auto simp: replace_sym_def)

lemma Lang_Replace_grammar_append:
  assumes inj: "inj_on f as" and Pfas: "Lhss P \<inter> f ` as = {}" and Afas: "A \<notin> f ` as"
  defines "P' \<equiv> P \<union> Replace_grammar f as"
  shows "Tms_syms \<beta> \<subseteq> as \<Longrightarrow>
 Lang (insert (A, \<alpha> @ map (replace_sym f) \<beta>) P') = Lang (insert (A, \<alpha> @ \<beta>) P')"
proof (induction \<beta> arbitrary: \<alpha>)
  case Nil
  show ?case by simp
next
  case (Cons x \<beta>)
  from Cons.prems have "Tms_syms \<beta> \<subseteq> as" by auto
  note IH = Cons.IH[OF this, where \<alpha> = "\<alpha> @ [x]"]
  show ?case
  proof (cases x)
    case (Nt A)
    with IH show ?thesis by (auto simp: replace_sym_Nt)
  next
    case [simp]: (Tm a)
    from Cons.prems have a: "a \<in> as" by auto
    from a Pfas have fa: "f a \<notin> Lhss P" by auto
    from a Afas have A: "A \<noteq> f a" by auto
    note * = Lang_Replace_grammar1[OF inj a fa A]
    from IH show ?thesis by (simp add: replace_sym_Tm * P'_def)
  qed
qed

definition map_tl where
"map_tl f xs = (case xs of x#xs' \<Rightarrow> x # map f xs' | _ \<Rightarrow> xs)"

lemma map_tl_simps[simp]:
"map_tl f [] = []"
"map_tl f (x#xs) = x # map f xs"
  by (auto simp: map_tl_def)

lemma Lang_map_tl_replace:
  assumes pre: "inj_on f as" "Lhss P \<inter> f ` as = {}" "A \<notin> f ` as"
    and \<alpha>: "Tms_syms \<alpha> \<subseteq> as"
  defines "P' \<equiv> P \<union> Replace_grammar f as"
  shows "Lang (insert (A, map_tl (replace_sym f) \<alpha>) P') = Lang (insert (A,\<alpha>) P')"
proof (cases \<alpha>)
  case Nil
  then show ?thesis by simp
next
  case [simp]: (Cons x \<beta>)
  with \<alpha> have \<beta>: "Tms_syms \<beta> \<subseteq> as" by simp
  from Lang_Replace_grammar_append[OF pre \<beta>, where \<alpha> = "[x]"]
  show ?thesis by (simp add: P'_def)
qed

definition replace_tl where
"replace_tl f P = [(A, map_tl (replace_sym f) \<alpha>). (A,\<alpha>) \<leftarrow> P]"

lemma "replace_tl f = map (map_prod id (map_tl (replace_sym f)))"
  by (simp add: fun_eq_iff replace_tl_def split: prod.split)

lemma replace_tl_simps[simp]:
"replace_tl f [] = []"
"replace_tl f ((A,\<alpha>)#P) = (A, map_tl (replace_sym f) \<alpha>) # replace_tl f P"
  by (simp_all add: replace_tl_def)

definition replace_Tm_tl where
"replace_Tm_tl f P = replace_tl f P @ replace_grammar f (tms P)"

lemma lang_replace_Tm_tl:
  assumes inj: "inj_on f (Tms (set P))" and Nts: "Nts (set P) \<inter> f ` Tms (set P) = {}"
    and A: "A \<in> Nts (set P)"
  shows "lang (replace_Tm_tl f P) A = lang P A"
proof-
  have Lhss: "Lhss (set P) \<inter> f ` Tms (set P) = {}" using Nts by (auto simp: Nts_Lhss_Rhs_Nts)
  { fix as
    assume inj: "inj_on f as"
      and Pfas: "Lhss (set P) \<inter> f ` as = {}"
      and Pas: "Tms (set P) \<subseteq> as"
    from Pfas Pas
    have "\<And>Q. Lhss Q \<inter> f ` as = {} \<Longrightarrow> Lang (Q \<union> set (replace_tl f P) \<union> Replace_grammar f as) = Lang (Q \<union> set P \<union> Replace_grammar f as)"
    proof (induction P)
      case Nil
      show ?case by simp
    next
      case (Cons p P)
      show ?case
      proof (cases p)
        case [simp]: (Pair A \<alpha>)
        from Cons
        have Afas: "A \<notin> f ` as" and Pfas: "lhss P \<inter> f ` as = {}"
          and Qfas: "Lhss Q \<inter> f ` as = {}"
          and Pas: "Tms (set P) \<subseteq> as" and \<alpha>as: "Tms_syms \<alpha> \<subseteq> as"
          by (auto simp: Tms_def)
        from Afas Qfas have "Lhss (Q \<union> {(A,\<alpha>')}) \<inter> f ` as = {}" for \<alpha>' by (simp add: ac_simps)
        note IH = Cons.IH[OF this Pfas Pas, simplified]
        from Pfas Qfas have QPfas: "Lhss (Q \<union> set P) \<inter> f ` as = {}" by auto
        from Lang_map_tl_replace[OF inj QPfas Afas \<alpha>as]
        show ?thesis by (simp add: IH)
      qed
    qed
  }
  from this[of "set (tms P)" "{}",simplified] inj Lhss
  have 1: "lang (replace_Tm_tl f P) = Lang (set P \<union> Replace_grammar f (Tms (set P)))"
    by (simp add: replace_Tm_tl_def set_tms set_replace_grammar)
  have 2: "\<dots> A = lang P A"
    apply (subst Lang_Un_disj_Lhss[OF _ A])
     apply (simp add: Lhss_Replace_grammar Nts) (* !? *)
    apply (rule refl).
  show ?thesis by (simp add: 1 2)
qed



end