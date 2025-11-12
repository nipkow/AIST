theory Replace_Terminals
  imports Greibach_Normal_Form.Greibach_Normal_Form
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

lemma fresh_map_disj: "finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> X \<subseteq> set xs \<Longrightarrow> B \<inter> fresh_map A xs ` X = {}"
  by (force simp: fresh_map_notIn)

lemma fresh_map_inj_on: "finite A \<Longrightarrow> inj_on (fresh_map A xs) (set xs)"
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
  using fresh_map_inj_on[OF fin] by (auto simp: distinct_map)

definition Replace_Tm_new where
"Replace_Tm_new f as = (\<lambda>a. (f a, [Tm a])) ` as"

definition replace_Tm_new where
"replace_Tm_new f as = [(f a, [Tm a]). a \<leftarrow> as]"

lemma set_replace_Tm_new: "set (replace_Tm_new f as) = Replace_Tm_new f (set as)"
  by (auto simp: replace_Tm_new_def Replace_Tm_new_def)

lemma Lhss_Replace_Tm_new: "Lhss (Replace_Tm_new f as) = f ` as"
  by (simp add: Replace_Tm_new_def Lhss_image_Pair)

lemma Rhss_Replace_Tm_new:
  assumes inj: "inj_on f as" and a: "a \<in> as"
  shows "Rhss (Replace_Tm_new f as) (f a) = {[Tm a]}"
  by (auto simp: Replace_Tm_new_def Rhss_image_Pair_inj_on[OF inj a])

lemma Rhss_Un_Replace_Tm_new:
  assumes inj: "inj_on f as" and a: "a \<in> as" and fa: "f a \<notin> Lhss P"
  shows "Rhss (P \<union> Replace_Tm_new f as) (f a) = {[Tm a]}"
  by (simp add: Rhss_Un Rhss_Replace_Tm_new[OF inj a] fa[unfolded notin_Lhss_iff_Rhss])

lemma Lang_Replace_Tm_new1:
  assumes inj: "inj_on f as" and a: "a \<in> as"
    and faP: "f a \<notin> Lhss P" and A: "A \<noteq> f a"
  shows "Lang (insert (A, \<alpha> @ Nt (f a) # \<beta>) (P \<union> Replace_Tm_new f as)) =
         Lang (insert (A, \<alpha> @ Tm a # \<beta>) (P \<union> Replace_Tm_new f as))"
proof-
  note Rhss = Rhss_Un_Replace_Tm_new[OF inj a faP]
  note * = Lang_subst1[OF A Rhss, where \<alpha> = \<alpha> and \<gamma> = \<beta>, simplified]
  show ?thesis by (simp add: *)
qed

definition replace_Tm_sym where
"replace_Tm_sym f x = (case x of Tm a \<Rightarrow> Nt (f a) | _ \<Rightarrow> x)"

lemma replace_Tm_sym_simps[simp]:
  "replace_Tm_sym f (Nt A) = Nt A"
  "replace_Tm_sym f (Tm a) = Nt (f a)"
  by (auto simp: replace_Tm_sym_def)

lemma Lang_replace_Tm_sym:
  assumes inj: "inj_on f as" and Pfas: "Lhss P \<inter> f ` as = {}" and Afas: "A \<notin> f ` as"
  defines "P' \<equiv> P \<union> Replace_Tm_new f as"
  shows "Tms_syms \<beta> \<subseteq> as \<Longrightarrow>
 Lang (insert (A, \<alpha> @ map (replace_Tm_sym f) \<beta>) P') = Lang (insert (A, \<alpha> @ \<beta>) P')"
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
    with IH show ?thesis by simp
  next
    case [simp]: (Tm a)
    from Cons.prems have a: "a \<in> as" by auto
    from a Pfas have fa: "f a \<notin> Lhss P" by auto
    from a Afas have A: "A \<noteq> f a" by auto
    note * = Lang_Replace_Tm_new1[OF inj a fa A]
    from IH show ?thesis by (simp add: * P'_def)
  qed
qed

definition replace_Tm_tl_syms where
"replace_Tm_tl_syms f xs = (case xs of x#xs' \<Rightarrow> x # map (replace_Tm_sym f) xs' | _ \<Rightarrow> xs)"

definition replace_Tm_tl where
"replace_Tm_tl f P = [(A, replace_Tm_tl_syms f \<alpha>). (A,\<alpha>) \<leftarrow> P] @ replace_Tm_new f (tms P)"

lemma Lang_replace_Tm_tl_syms:
  assumes pre: "inj_on f as" "Lhss P \<inter> f ` as = {}" "A \<notin> f ` as"
    and \<alpha>: "Tms_syms \<alpha> \<subseteq> as"
  defines "P' \<equiv> P \<union> Replace_Tm_new f as"
  shows "Lang (insert (A, replace_Tm_tl_syms f \<alpha>) P') = Lang (insert (A,\<alpha>) P')"
proof (cases \<alpha>)
  case Nil
  then show ?thesis by (simp add: replace_Tm_tl_syms_def)
next
  case [simp]: (Cons x \<beta>)
  with \<alpha> have \<beta>: "Tms_syms \<beta> \<subseteq> as" by simp
  from Lang_replace_Tm_sym[OF pre \<beta>, where \<alpha> = "[x]"]
  show ?thesis by (simp add: replace_Tm_tl_syms_def P'_def)
qed

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
    have "\<And>Q. Lhss Q \<inter> f ` as = {} \<Longrightarrow> Lang (Q \<union> set [(A, replace_Tm_tl_syms f \<alpha>). (A,\<alpha>) \<leftarrow> P] \<union> Replace_Tm_new f as) = Lang (Q \<union> set P \<union> Replace_Tm_new f as)"
      apply simp
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
        note * = Lang_replace_Tm_tl_syms[OF inj QPfas Afas \<alpha>as]
        show ?thesis by (simp add: * IH)
      qed
    qed
  }
  from this[of "set (tms P)" "{}",simplified] inj Lhss
  have 1: "lang (replace_Tm_tl f P) = Lang (set P \<union> Replace_Tm_new f (Tms (set P)))"
    by (simp add: replace_Tm_tl_def set_tms set_replace_Tm_new)
  have 2: "\<dots> A = lang P A"
    apply (subst Lang_Un_disj_Lhss[OF _ A])
     apply (simp add: Lhss_Replace_Tm_new Nts) (* !? *)
    apply (rule refl).
  show ?thesis by (simp add: 1 2)
qed

definition replace_Tm_tl_fresh where
"replace_Tm_tl_fresh P = replace_Tm_tl (fresh_map (Nts (set P)) (tms P)) P"

lemma lang_replace_Tm_tl_fresh:
  assumes A: "A \<in> Nts (set P)"
  shows "lang (replace_Tm_tl_fresh P) A = lang P A"
proof-
  have fin: "finite (Nts (set P))" by (auto intro!: finite_Nts)
  from fresh_map_inj_on[OF fin, where xs = "tms P"]
    fresh_map_notIn[OF fin, where xs="tms P"]
  show ?thesis
    by (auto simp: replace_Tm_tl_fresh_def set_tms intro!: lang_replace_Tm_tl[OF _ _ A])
qed

definition GNF where
"GNF P = (\<forall>(A,\<alpha>) \<in> P. \<exists>a Bs. \<alpha> = Tm a # map Nt Bs)"

abbreviation gnf where
"gnf P \<equiv> GNF (set P)"

lemma GNF_I: "(\<And>A \<alpha>. (A,\<alpha>) \<in> P \<Longrightarrow> \<exists>a Bs. \<alpha> = Tm a # map Nt Bs) \<Longrightarrow> GNF P"
  by (auto simp: GNF_def)

lemma GNF_Un: "GNF (P \<union> Q) \<longleftrightarrow> GNF P \<and> GNF Q"
  by (auto simp: GNF_def ball_Un)

lemma gnf_replace_Tm_new: "gnf (replace_Tm_new f as)"
  by (auto intro!: GNF_I simp: replace_Tm_new_def)

lemma gnf_replace_Tm_tl:
  assumes P: "gnf_hd P"
  shows "gnf (replace_Tm_tl f P)"
  apply (unfold replace_Tm_tl_fresh_def replace_Tm_tl_def set_append GNF_Un)
proof (intro conjI gnf_replace_Tm_new GNF_I)
  fix A \<alpha>' assume "(A,\<alpha>') \<in> set [(A, replace_Tm_tl_syms f \<alpha>). (A,\<alpha>) \<leftarrow> P]"
  then obtain \<alpha> where "(A,\<alpha>) \<in> set P" and \<alpha>': "\<alpha>' = replace_Tm_tl_syms f \<alpha>" by auto
  with P obtain a \<beta> where "\<alpha> = Tm a # \<beta>" by (auto simp: GNF_hd_def)
  with \<alpha>' have \<alpha>': "\<alpha>' = Tm a # map (replace_Tm_sym f) \<beta>" by (auto simp: replace_Tm_tl_syms_def)
  define Bs where "Bs \<equiv> [case x of Nt B \<Rightarrow> B | Tm b \<Rightarrow> f b. x \<leftarrow> \<beta>]"
  have "map (replace_Tm_sym f) \<beta> = map Nt Bs"
    by (unfold Bs_def, induction \<beta>, auto split: sym.splits)
  with \<alpha>' have "\<alpha>' = Tm a # map Nt Bs" by simp
  then show "\<exists>a Bs. \<alpha>' = Tm a # map Nt Bs" by blast
qed

definition gnf_of where
"gnf_of P = replace_Tm_tl (fresh_map (Nts (set P)) (tms P)) (gnf_hd_of P)"

theorem gnf_gnf_of: "gnf (gnf_of P)"
  apply (unfold gnf_of_def)
  apply (rule gnf_replace_Tm_tl)
  using gnf_hd_gnf_hd_of.

lemma Tms_GNF_hd_of: "Tms (GNF_hd_of As P) \<subseteq> Tms P" sorry

theorem lang_gnf_of:
  assumes A: "A \<in> set (nts P)"
  shows "lang (gnf_of P) A = lang P A - {[]}"
  apply (fold lang_gnf_hd_of[OF A])
  apply (unfold gnf_of_def)
proof (rule lang_replace_Tm_tl)
  define f where "f = fresh_map (Nts (set P)) (tms P)"
  show "inj_on f (Tms (set (gnf_hd_of P)))"
    apply (unfold f_def)
    apply (rule inj_on_subset[OF fresh_map_inj_on])
    by (simp_all add: finite_Nts set_tms set_gnf_hd_of Tms_GNF_hd_of)
  show "Nts (set (gnf_hd_of P)) \<inter>
    f ` Tms (set (gnf_hd_of P)) = {}"
    apply (unfold f_def)
    apply (fold set_tms)
    apply (rule fresh_map_disj)
    apply (auto simp: finite_Nts set_gnf_hd_of)
    oops


end