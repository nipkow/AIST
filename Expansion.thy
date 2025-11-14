theory Expansion
  imports Context_Free_Grammar.Context_Free_Grammar "Regular-Sets.Regular_Set"
begin

lemma insert_conc: "insert w W @@ V = {w @ v | v. v \<in> V} \<union> W @@ V"
  by auto

text \<open>Language is extended over mixed words.\<close>

definition Lang_of where
"Lang_of P \<alpha> = {w. P \<turnstile> \<alpha> \<Rightarrow>* map Tm w}"

lemma Lang_of_Nil[simp]: "Lang_of P [] = {[]}"
  by (auto simp: Lang_of_def)

lemma Lang_of_iff_derives: "w \<in> Lang_of P \<alpha> \<longleftrightarrow> P \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
  by (auto simp: Lang_of_def)

lemma Lang_eq_iff_Lang_of_eq: "Lang P = Lang P' \<longleftrightarrow> Lang_of P = Lang_of P'"
  by (unfold Lang_eq_iff_derives, auto simp: fun_eq_iff Lang_of_def)

lemma Lang_of_Tm: "Lang_of P (Tm a # \<alpha>) = {[a]} @@ Lang_of P \<alpha>"
  by (auto simp: Lang_of_def derives_Tm_Cons conc_def)

lemma Lang_of_map_Tm: "Lang_of P (map Tm w) = {w}"
  by (induction w, simp_all add: Lang_of_Tm insert_conc)

lemma Lang_of_Nt: "Lang_of P (Nt A # \<alpha>) = Lang P A @@ Lang_of P \<alpha>"
  by (force simp add: Lang_of_def Lang_def derives_Cons_decomp map_eq_append_conv conc_def)

lemma Lang_of_Cons: "Lang_of P (x # \<alpha>) = (case x of Tm a \<Rightarrow> {[a]} | Nt A \<Rightarrow> Lang P A) @@ Lang_of P \<alpha>"
  by (simp add: Lang_of_Tm Lang_of_Nt split: sym.splits)

lemma Lang_of_append: "Lang_of P (\<alpha> @ \<beta>) = Lang_of P \<alpha> @@ Lang_of P \<beta>"
  by (induction \<alpha> arbitrary: \<beta>, simp_all add: Lang_of_Cons conc_assoc split: sym.splits)

abbreviation Lang_of_set where
"Lang_of_set P X \<equiv> \<Union>(Lang_of P ` X)"

lemma Lang_of_set_conc: "Lang_of_set P (X @@ Y) = Lang_of_set P X @@ Lang_of_set P Y"
  by (force simp: Lang_of_append elim!: concE)

lemma Lang_of_set_Rhss: "Lang_of_set P (Rhss P A) = Lang P A"
  by (auto simp: Lang_def Lang_of_def Rhss_def converse_rtranclp_into_rtranclp derive_singleton
      dest: derives_start1)

lemma Lang_of_prod_subset: "(A,\<alpha>) \<in> P \<Longrightarrow> Lang_of P \<alpha> \<subseteq> Lang P A"
  apply (fold Lang_of_set_Rhss) by (auto simp: Rhss_def)


lemma Lang_of_set_pow: "Lang_of_set P (X ^^ n) = Lang_of_set P X ^^ n"
  by (induction n, simp_all add: Lang_of_set_conc)

lemma Lang_of_set_star: "Lang_of_set P (star X) = star (Lang_of_set P X)"
  by (auto simp: star_def Lang_of_set_pow)

section \<open>General Expansion\<close>

text \<open>We consider the set of admissible expansions of grammars.
For a symbol,
one option is not to expand it,
and another option for (unlocked) nonterminals is to expand to the all rhss.\<close>

definition Expand_sym_ops :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) syms set set" where
"Expand_sym_ops P L x =
  insert {[x]} (case x of Nt A \<Rightarrow> if A \<in> L then {} else {Rhss P A} | _ \<Rightarrow> {})"

lemma Expand_sym_ops_simps:
  "Expand_sym_ops P L (Tm a) = {{[Tm a]}}"
  "Expand_sym_ops P L (Nt A) = insert {[Nt A]} (if A \<in> L then {} else {Rhss P A})"
  by (auto simp: Expand_sym_ops_def)

lemma Expand_sym_ops_self: "{[x]} \<in> Expand_sym_ops P L x"
  by (simp add: Expand_sym_ops_def)

text \<open>Mixed words allow all possible combinations of the options of the symbols.\<close>

fun Expand_syms_ops where
  "Expand_syms_ops P L [] = {{[]}}"
| "Expand_syms_ops P L (x#xs) =
   {\<alpha>s @@ \<beta>s | \<alpha>s \<beta>s. \<alpha>s \<in> Expand_sym_ops P L x \<and> \<beta>s \<in> Expand_syms_ops P L xs}"

lemma Expand_sym_ops_Lang_of_Cons:
  assumes X: "X \<in> Expand_sym_ops P L x"
    and L: "Lhss Q \<subseteq> L"
  shows "Lang_of (P \<union> Q) (x#xs) = Lang_of_set (P \<union> Q) X @@ Lang_of (P \<union> Q) xs"
proof-
  { fix A assume "A \<notin> L"
    with L have "A \<notin> Lhss Q" by auto
    then have "Rhss (P \<union> Q) A = Rhss P A" by (auto simp: Rhss_Un notin_Lhss_iff_Rhss)
    with Lang_of_set_Rhss[of "P \<union> Q" A]
    have "Lang_of_set (P \<union> Q) (Rhss P A) = Lang (P \<union> Q) A" by auto
  } note * = this
  show ?thesis
  proof (cases "X = {[x]}")
    case True
    with assms show ?thesis by (simp add: Expand_sym_ops_simps Lang_of_Cons)
  next
    case False
    with assms show ?thesis
      by (cases x, simp_all add: Expand_sym_ops_simps Lang_of_Nt * split: if_splits)
  qed
qed

lemma Expand_syms_ops_Lang_of:
  assumes X: "X \<in> Expand_syms_ops P L \<alpha>"
    and L: "Lhss Q \<subseteq> L"
  shows "Lang_of (P \<union> Q) \<alpha> = Lang_of_set (P \<union> Q) X"
proof (insert X, induction \<alpha> arbitrary: X)
  case Nil
  then show ?case by simp
next
  case (Cons x \<alpha>)
  from Cons.prems obtain Y Z
    where X: "X = Y @@ Z"
      and Y: "Y \<in> Expand_sym_ops P L x"
      and Z: "Z \<in> Expand_syms_ops P L \<alpha>"
    by auto
  show ?case by (simp add: X Cons.IH[OF Z] Expand_sym_ops_Lang_of_Cons[OF Y L] Lang_of_set_conc)
qed

definition Expand where
"Expand f Q = (\<Union>(A,\<alpha>) \<in> Q. Pair A ` f \<alpha>)"

lemma Lhss_Expand: "Lhss (Expand f Q) \<subseteq> Lhss Q"
  by (auto simp: Lhss_def Expand_def split: prod.splits)

lemma Rhss_Expand: "Rhss (Expand f Q) A = \<Union>(f ` Rhss Q A)"
  by (auto simp: Rhss_def Expand_def)

text \<open>When each production is expanded in an admissible way,
then the language is preserved.\<close>

lemma Lang_Expand:
  assumes f: "\<forall>(A,\<alpha>) \<in> Q. f \<alpha> \<in> Expand_syms_ops P L \<alpha>" and L: "Lhss Q \<subseteq> L"
  shows "Lang (P \<union> Expand f Q) = Lang (P \<union> Q)"
proof (intro ext Lang_eqI_derives iffI)
  have "P \<union> Expand f Q \<turnstile> xs \<Rightarrow>(n) map Tm w \<Longrightarrow> w \<in> Lang_of (P \<union> Q) xs" for xs w n
  proof (induction n arbitrary: xs w rule: less_induct)
    case (less n)
    show ?case
    proof (cases "\<exists>A. Nt A \<in> set xs")
      case False
      with less.prems have "xs = map Tm w"
        by (metis (no_types, lifting) deriven_from_TmsD destTm.cases ex_map_conv)
      then show ?thesis by (auto simp: Lang_of_map_Tm)
    next
      case True
      then obtain ys zs A where xs: "xs = ys @ Nt A # zs" by (metis split_list) 
      from less.prems[unfolded this deriven_Nt_map_Tm]
      obtain \<delta> m l k v u t where A\<delta>: "(A,\<delta>) \<in> P \<union> Expand f Q"
        and Lys: "P \<union> Expand f Q \<turnstile> ys \<Rightarrow>(m) map Tm v"
        and L\<delta>: "P \<union> Expand f Q \<turnstile> \<delta> \<Rightarrow>(l) map Tm u"
        and Lzs: "P \<union> Expand f Q \<turnstile> zs \<Rightarrow>(k) map Tm t"
        and n: "n = Suc (m + l + k)"
        and w: "w = v @ u @ t" by force
      from n have mn: "m < n" and ln: "l < n" and kn: "k < n" by auto
      with less.IH L\<delta> Lys Lzs
      have u: "u \<in> Lang_of (P \<union> Q) \<delta>"
        and v: "v \<in> Lang_of (P \<union> Q) ys"
        and t: "t \<in> Lang_of (P \<union> Q) zs" by auto
      show ?thesis
      proof (cases "(A,\<delta>) \<in> P")
        case True
        have "Lang_of (P \<union> Q) \<delta> \<subseteq> Lang (P \<union> Q) A"
          apply (rule Lang_of_prod_subset)
          using True by simp
        with u v t
        show ?thesis by (auto simp: xs w Lang_of_append Lang_of_Nt)
      next
        case False
        with A\<delta> obtain \<alpha> where AQ: "(A,\<alpha>) \<in> Q" and \<delta>: "\<delta> \<in> f \<alpha>" by (auto simp: Expand_def)
        from L\<delta>[unfolded \<delta>] less.IH[of l] n
        have "u \<in> Lang_of (P \<union> Q) \<delta>" by auto
        with \<delta> have "u \<in> Lang_of_set (P \<union> Q) (f \<alpha>)"
          by (auto simp: Lang_of_def)
        also have "\<dots> = Lang_of (P \<union> Q) \<alpha>"
          apply (subst Expand_syms_ops_Lang_of)
          using f AQ L by auto
        also have "\<dots> \<subseteq> Lang (P \<union> Q) A"
          apply (rule Lang_of_prod_subset)
          using AQ by auto
        finally have u: "u \<in> Lang (P \<union> Q) A" by auto
        with v t
        show ?thesis by (simp add: xs w Lang_of_append Lang_of_Nt)
      qed
    qed
  qed
  then show "P \<union> Expand f Q \<turnstile> xs \<Rightarrow>* map Tm w \<Longrightarrow> P \<union> Q \<turnstile> xs \<Rightarrow>* map Tm w" for xs w
    by (auto simp: rtranclp_power Lang_of_iff_derives)
next
  have "P \<union> Q \<turnstile> xs \<Rightarrow>(n) map Tm w \<Longrightarrow> w \<in> Lang_of (P \<union> Expand f Q) xs" for xs w n
  proof (induction n arbitrary: xs w rule: less_induct)
    case (less n)
    show ?case
    proof (cases "\<exists>A. Nt A \<in> set xs")
      case False
      with less.prems have "xs = map Tm w"
        by (metis (no_types, lifting) deriven_from_TmsD destTm.cases ex_map_conv)
      then show ?thesis by (auto simp: Lang_of_map_Tm)
    next
      case True
      then obtain ys zs A where xs: "xs = ys @ Nt A # zs" by (metis split_list) 
      from less.prems[unfolded this deriven_Nt_map_Tm]
      obtain \<alpha> m l k v u t where A\<alpha>: "(A,\<alpha>) \<in> P \<union> Q"
        and Rys: "P \<union> Q \<turnstile> ys \<Rightarrow>(m) map Tm v"
        and R\<alpha>: "P \<union> Q \<turnstile> \<alpha> \<Rightarrow>(l) map Tm u"
        and Rzs: "P \<union> Q \<turnstile> zs \<Rightarrow>(k) map Tm t"
        and n: "n = Suc (m + l + k)"
        and w: "w = v @ u @ t" by force
      from n have mn: "m < n" and ln: "l < n" and kn: "k < n" by auto
      with R\<alpha> Rys Rzs
      have u: "u \<in> Lang_of (P \<union> Expand f Q) \<alpha>"
        and v: "v \<in> Lang_of (P \<union> Expand f Q) ys"
        and t: "t \<in> Lang_of (P \<union> Expand f Q) zs" by (auto simp: less.IH)
      show ?thesis
      proof (cases "(A,\<alpha>) \<in> P")
        case True
        then have "(A,\<alpha>) \<in> P \<union> Expand f Q" by simp
        from Lang_of_prod_subset[OF this] u
        have "u \<in> Lang (P \<union> Expand f Q) A" by auto
        with v w t
        show ?thesis by (auto simp: xs w Lang_of_append Lang_of_Nt)
      next
        case False
        with A\<alpha> have A\<alpha>Q: "(A,\<alpha>) \<in> Q" by simp
        with f have f\<alpha>: "f \<alpha> \<in> Expand_syms_ops P L \<alpha>" by auto
        from L Lhss_Expand[of f Q]
        have Lhss: "Lhss (Expand f Q) \<subseteq> L" by auto
        from L A\<alpha>Q have Rhss: "f \<alpha> \<subseteq> Rhss (Expand f Q) A"
          by (auto simp: Rhss_def Expand_def)
        from u Expand_syms_ops_Lang_of[OF f\<alpha> Lhss]
        have "u \<in> Lang_of_set (P \<union> Expand f Q) (f \<alpha>)" by auto
        also have "\<dots> \<subseteq> Lang (P \<union> Expand f Q) A" using Rhss
          by (auto simp flip: Lang_of_set_Rhss simp: Rhss_Un)
        finally have "u \<in> \<dots>".
        with v t show ?thesis by (simp add: xs w Lang_of_append Lang_of_Nt)
      qed
    qed
  qed
  then show "P \<union> Q \<turnstile> xs \<Rightarrow>* map Tm w \<Longrightarrow> P \<union> Expand f Q \<turnstile> xs \<Rightarrow>* map Tm w" for xs w
    by (auto simp: rtranclp_power Lang_of_iff_derives)
qed

lemma Lang_Expand_left:
  assumes f: "\<forall>(A,\<alpha>) \<in> Q. f \<alpha> \<in> Expand_syms_ops P L \<alpha>" and L: "Lhss Q \<subseteq> L"
  shows "Lang (Expand f Q \<union> P) = Lang (Q \<union> P)"
  using Lang_Expand[OF f L] by (simp add: ac_simps)

subsubsection \<open>Instance: Expanding all nonterminals\<close>

definition Expand_all_sym :: "('n,'t) Prods \<Rightarrow> 'n set \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'t) syms set" where
"Expand_all_sym P L x = (case x of Nt A \<Rightarrow> if A \<in> L then {[x]} else Rhss P A | _ \<Rightarrow> {[x]})"

lemma Expand_all_sym_ops: "Expand_all_sym P L x \<in> Expand_sym_ops P L x"
  by (auto simp: Expand_all_sym_def Expand_sym_ops_simps split: sym.splits)

fun Expand_all_syms where
  "Expand_all_syms P L [] = {[]}"
| "Expand_all_syms P L (x#xs) = Expand_all_sym P L x @@ Expand_all_syms P L xs"

lemma Expand_all_syms_ops: "Expand_all_syms P L xs \<in> Expand_syms_ops P L xs"
  by (induction xs, simp, force simp: Expand_all_sym_ops)

abbreviation Expand_all where
"Expand_all P L Q \<equiv> Expand (Expand_all_syms P L) Q"

lemma Lang_Expand_all:
  assumes "Lhss Q \<subseteq> L"
  shows "Lang (Expand_all P L Q \<union> P) = Lang (Q \<union> P)"
  apply (rule Lang_Expand_left[OF _ assms])
  by (simp add: Expand_all_syms_ops)

end