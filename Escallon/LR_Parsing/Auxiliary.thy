theory Auxiliary
  imports Context_Free_Grammar.Context_Free_Grammar Finite_Automata_HF.Finite_Automata_HF
begin 

section \<open>Lists\<close>

lemma index_gt_left_imp_right:
  assumes "length xs < m" "m < length (xs@y#ys)"
        shows "(xs@y#ys)!m \<in> set ys"
proof -
  have "(xs@y#ys)!m = (y#ys)!(m-length xs)" 
    using assms(1) by (meson le_eq_less_or_eq nth_append_right)
  also have "... = ys!(m-length xs-1)" 
    using assms(1) by simp
  finally show ?thesis 
    by (metis One_nat_def Suc_pred add_diff_inverse_nat add_less_cancel_left assms length_Cons
        length_append less_Suc_eq not_less_eq nth_mem zero_less_diff)
qed

lemma list_app_last_is_next_hd:
  assumes "w = u@v@y"
    "w = xs@a#y"
    "v \<noteq> []"
  shows "last v = a"
  using assms 
  by (metis append.assoc append_Cons append_Nil append_same_eq last_append last_snoc)

lemma x_notin_tl_imp_eq:
  assumes "ws @ x # xs = ys @ x # zs"
  "x \<notin> set xs" "x \<notin> set zs"
shows "ws = ys \<and> xs = zs"
  using assms proof (induction xs arbitrary: zs rule: rev_induct)
  case Nil
  have "zs = []"
    by (metis Nil.prems(1,3) last_ConsL last_ConsR last_appendR last_in_set list.simps(3))
  then show ?case using Nil(1) by blast
next
  case (snoc a xs)
  obtain a' zs' where zs_snoc: "zs = zs' @ [a']"
  proof -
    have "\<exists>a zs'. zs = zs' @ [a]"
      by (metis snoc.prems(1) snoc.prems(2) rev_exhaust last_in_set last.simps 
          last_appendR list.distinct(1))
    thus thesis using that by blast
  qed
  with snoc have "ws = ys \<and> xs = zs'" by force
  then show ?case using zs_snoc snoc by blast
qed

lemma list_of_subset:
  assumes "A \<noteq> {}"
  obtains xs where "set xs \<subseteq> A" "length xs = n"
proof -
  from assms obtain a where in_A: "a \<in> A" by blast
  let ?xs = "replicate n a"
  from in_A have "set ?xs \<subseteq> A" by fastforce
  moreover have "length ?xs = n" by simp
  ultimately show thesis using that by blast
qed

lemma list_eq_less_imp_substring:
  assumes "as @ bs = xs @ ys" "length as < length xs"
  obtains as' where "xs = as @ as'"
  using assms by (metis append_eq_append_conv2 length_append not_add_less1)

lemma take_diff:
  "take n xs = take n ys \<Longrightarrow> take (n-m) xs = take (n-m) ys"
proof (induction n arbitrary: xs ys)
  case 0
  then show ?case by simp
next
  case (Suc n)
  hence Nil_iff: "xs = [] = (ys = [])" by fastforce
  then show ?case proof (cases xs)
    case Nil
    then show ?thesis using Nil_iff by blast
  next
    case (Cons a as)
    with Nil_iff obtain b bs where ys_def: "ys = b#bs" using list.exhaust 
      by auto
    show ?thesis using Suc unfolding ys_def Cons 
      by (metis One_nat_def Suc_diff_diff diff_zero list.inject take_Cons' take_Suc_Cons)
  qed
qed

lemma list_app_eq_nempty_cases[consumes 1, case_names left right]:
  assumes "as @ bs = xs @ y # ys"
  obtains 
    xs' where "as = xs @ y # xs'" "ys = xs' @ bs" |
    bs' where "xs = as @ bs'" "bs = bs' @ y # ys"
using assms proof (induction as arbitrary: xs thesis)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  show ?case 
    by (cases xs) (use Cons in auto)
qed

lemma last_of_Cons_idx_len_tl:
  "x = last (y # xs) \<Longrightarrow> x = (y # xs) ! (length xs)"
  by (induction xs rule: rev_induct) auto

section \<open>Syms (generalize to all list types?)\<close>

lemma syms_split_last_eq_imp_tl_eq:
  assumes "\<alpha> @ Nt A # map Tm w = \<beta> @ Nt A # \<gamma> @ map Tm v"
    "Nt A \<notin> set \<gamma>"
  obtains u where "\<gamma> = map Tm u" "w = u@v"
  using assms proof (induction w arbitrary: thesis v \<gamma> rule: rev_induct)
  case Nil
  from Nil(2) have A_last: "last (\<beta> @ Nt A # \<gamma> @ map Tm v) = Nt A" 
    by (simp add: snoc_eq_iff_butlast)
  have "\<gamma> @ map Tm v = []" 
    by (metis A_last Nil.prems(3) append.right_neutral isNt_simps(1,2) last_ConsR last_appendR last_in_set
        last_map list.distinct(1) list.map_disc_iff)
  then show ?case using Nil by auto
next
  case (snoc a w)
  from snoc(3) have butlast_eq: "\<alpha> @ Nt A # map Tm w = \<beta> @ Nt A # butlast (\<gamma> @ map Tm v)"
  proof -
    have "\<gamma> @ map Tm v \<noteq> []"
      by standard (use snoc(3) in auto)
    then obtain \<delta> b where "\<gamma> @ map Tm v = \<delta> @ [b]" using rev_exhaust by meson
    with snoc(3) show ?thesis by force
  qed
  let ?\<delta> = "butlast (\<gamma> @ map Tm v)"
  obtain \<delta> v' where \<delta>v'_def: "\<delta>@map Tm v' = ?\<delta>" by fast
  note \<delta>v'_eq = butlast_eq[unfolded this[symmetric]]
  from \<delta>v'_def snoc(4) have "Nt A \<notin> set \<delta>" 
  proof -
    from \<delta>v'_def have "set \<delta> \<subseteq> set ?\<delta>" 
      by (metis Un_iff set_append subsetI) 
    also have "... \<subseteq> set (\<gamma> @ map Tm v)" 
      by (meson in_set_butlastD subsetI)
    finally show ?thesis using snoc(4) by auto
  qed
  from snoc(1)[OF _ \<delta>v'_eq this] obtain u where "\<delta> = map Tm u" "w = u @ v'" by blast
  then show thesis using snoc(2,3) \<delta>v'_def \<delta>v'_eq append_same_eq
    by (smt (verit, ccfv_threshold) list.inject map_Tm_inject_iff map_eq_append_conv
        same_append_eq)
qed

lemma syms_decomp_rightmost:
  assumes "\<alpha> @ Nt A # map Tm w = \<beta> @ \<gamma> @ \<delta> @ map Tm x"
    "Nt A \<in> set \<gamma>" "Nt A \<notin> set \<delta>"
  obtains \<eta> u v where "\<gamma> = \<eta> @ Nt A # map Tm u" "\<delta> = map Tm v"  "w = u@v@x"
proof -
  from split_list_last[OF assms(2)] obtain \<zeta> \<theta> where \<gamma>_decomp: "\<gamma> = \<zeta> @ Nt A # \<theta>" "Nt A \<notin> set \<theta>" 
    by blast
  with assms(1) have "\<alpha> @ Nt A # map Tm w = \<beta> @ \<zeta> @ Nt A # \<theta> @ \<delta> @ map Tm x" by simp
  moreover from \<gamma>_decomp(2) assms(3) have "Nt A \<notin> set (\<theta>@\<delta>)" by simp
  ultimately obtain y where y_defs: "\<theta>@\<delta> = map Tm y" "w = y @ x" 
    using syms_split_last_eq_imp_tl_eq[of \<alpha> A _ "\<beta>@\<zeta>" "\<theta>@\<delta>" _] by auto
  then obtain u v where "\<theta> = map Tm u" "\<delta> = map Tm v" "w = u@v@x" 
    using append_eq_map_conv y_defs by (metis append.assoc)
  then show thesis using that \<gamma>_decomp 
    by blast
qed

lemma syms_decomp_rightmost2:
  assumes "\<alpha> @ Nt A # map Tm w = \<beta> @ \<gamma> @ map Tm x"
    "Nt A \<in> set \<gamma>"
  obtains \<delta> u where "\<gamma> = \<delta> @ Nt A # map Tm u" "w = u@x"
proof -
  from assms(1) have 1: "\<alpha> @ Nt A # map Tm w = \<beta> @ \<gamma> @ [] @ map Tm x" by simp
  obtain \<delta> u v where "\<gamma> = \<delta> @ Nt A # map Tm u" "[] = map Tm v" "w = u@v@x"
    using syms_decomp_rightmost[OF 1 assms(2) _] by auto
  then show thesis using that by blast
qed

lemma no_Nts_imp_Tms:
  assumes "\<nexists>A. Nt A \<in> set \<alpha>"
  obtains w where "\<alpha> = map Tm w"
  using assms by (metis ex_map_conv sym.exhaust)

lemma Tms_iff_no_Nts:
  "(\<exists>w. \<alpha> = map Tm w) \<longleftrightarrow> (\<nexists>A. Nt A \<in> set \<alpha>)"
  by (rule iffI) (use sym.exhaust in force, use no_Nts_imp_Tms in blast)

lemma Tms_iff_no_Nt:
  "(\<exists>w. \<alpha> = map Tm w) \<longleftrightarrow> (\<nexists>\<beta> A \<gamma>. \<alpha> = \<beta> @ Nt A # \<gamma>)"
  using Tms_iff_no_Nts by (metis in_set_conv_decomp)

text \<open>Same as @{thm non_word_has_last_Nt}, except with Cons instead of \<open>@\<close>.}\<close>
lemma syms_split_rightmost:
  assumes "\<exists>A. Nt A \<in> set \<alpha>"
  obtains \<beta> A u where "\<alpha> = \<beta> @ Nt A # map Tm u"
  using assms non_word_has_last_Nt in_Nts_syms by fastforce

lemma rightmost_eq_tl_lt_imp_substring:
  assumes "\<alpha> @ Nt X # map Tm w = \<alpha>' @ \<gamma> @ map Tm v"
  obtains u where "w = u @ v"
  using assms that by (cases "Nt X \<in> set \<gamma>")
    ((meson syms_decomp_rightmost2),
   (metis Tms_iff_no_Nts Un_iff append.assoc append_Nil in_set_conv_decomp 
     set_append syms_decomp_rightmost[of \<alpha> X w "[]" \<alpha>' \<gamma> v]))

lemma syms_split_tl:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
  obtains \<beta>' where "\<beta> = \<beta>' @ map Tm v"
proof -
  consider (Tms) u where "\<beta> = map Tm u" | (rightmost) \<beta>' Y u where "\<beta> = \<beta>' @ Nt Y # map Tm u"
    by (meson Tms_iff_no_Nts syms_split_rightmost)
  then show thesis
  proof cases
    case Tms
    then show ?thesis using rightmost_eq_tl_lt_imp_substring[OF assms[unfolded Tms]] that 
      by fastforce
  next
    case rightmost
    with assms[unfolded this] show ?thesis 
      using rightmost_eq_tl_lt_imp_substring[of "\<alpha> @ Nt X # \<beta>'" Y u] 
      by (metis append.assoc append_Cons map_append that)
  qed
qed

lemma syms_split_leq:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
    "length \<alpha>' \<le> length \<alpha>"
  obtains \<alpha>'' \<beta>'  where "\<alpha> = \<alpha>' @ \<alpha>''" "\<gamma> = \<alpha>'' @ Nt X # \<beta>'" "\<beta> = \<beta>' @ map Tm v"
using assms proof (induction \<alpha>' arbitrary: \<alpha> thesis)
  case Nil
  then show ?case using Nil(1)[of \<alpha>] syms_split_tl[OF Nil(2)] 
    by (smt (verit, ccfv_threshold) Cons_eq_appendI append_assoc append_same_eq self_append_conv2) 
next
  case (Cons a \<alpha>')
  note Cons_\<alpha>' = this
  show ?case 
    by (cases \<alpha>) (use Cons in auto)
qed

lemma syms_split_gt:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
    "length \<alpha>' > length \<alpha>"
  obtains \<alpha>'' where "\<alpha>' = \<alpha> @ Nt X # \<alpha>''" "\<beta> = \<alpha>'' @ \<gamma> @ map Tm v"
using assms proof (induction \<alpha> arbitrary: \<alpha>' thesis)
  case Nil
  then show ?case using Nil(1)[of "[]"] 
    by (metis (no_types, lifting) append_eq_Cons_conv length_greater_0_conv list.size(3))
next
  case (Cons a \<alpha>)
  show ?case 
    by (cases \<alpha>') (use Cons in auto)
qed

lemma syms_cases [case_names Tms Nt]:
  assumes "\<And>w. \<alpha> = map Tm w \<Longrightarrow> P"
    "\<And>\<beta> A \<gamma>. \<alpha> = \<beta> @ Nt A # \<gamma> \<Longrightarrow> P"
  shows P 
  using assms syms_split_rightmost by (metis Tms_iff_no_Nts)

lemma syms_rm_cases [case_names Tms Nt]:
  assumes "\<And>w. \<alpha> = map Tm w \<Longrightarrow> P"
    "\<And>\<beta> A w. \<alpha> = \<beta> @ Nt A # map Tm w \<Longrightarrow> P"
  shows P
  using assms non_word_has_last_Nt by (cases \<alpha> rule: syms_cases) 
    (blast, meson in_set_conv_decomp syms_split_rightmost)

lemma syms_lm_cases [case_names Tms Nt]:
  assumes "\<And>w. \<alpha> = map Tm w \<Longrightarrow> P"
    "\<And>w A \<beta>. \<alpha> = map Tm w @ Nt A # \<beta> \<Longrightarrow> P"
  shows P
  using assms by (cases \<alpha> rule: syms_cases) 
    (blast, metis Nts_syms_empty_iff non_word_has_first_Nt)

lemma nonword_eq_append_map_Tm_cases:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
  obtains \<alpha>'' \<beta>'  where "\<alpha> = \<alpha>' @ \<alpha>''" "\<gamma> = \<alpha>'' @ Nt X # \<beta>'" "\<beta> = \<beta>' @ map Tm v" |
              \<alpha>'' where "\<alpha>' = \<alpha> @ Nt X # \<alpha>''" "\<beta> = \<alpha>'' @ \<gamma> @ map Tm v"
  by (cases "length \<alpha>' \<le> length \<alpha>")  
    (meson assms that syms_split_leq syms_split_gt not_le_imp_less)+

lemma rm_eq_append_cases[case_names left right]:
  assumes "\<alpha> @ Nt X # map Tm w = \<beta> @ \<gamma>"
  obtains u v where "\<beta> = \<alpha> @ Nt X # map Tm u" "\<gamma> = map Tm v" "w = u @ v" |
          \<delta> where "\<alpha> = \<beta> @ \<delta>" "\<delta> @ Nt X # map Tm w = \<gamma>"
proof (cases "Nt X \<in> set \<gamma>")
  case True
  with syms_decomp_rightmost[of \<alpha> X w \<beta> \<gamma> "[]" "[]"]
  show ?thesis using assms using that(2) by force
next
  case False
  with assms have "Nt X \<in> set \<beta>" 
    by (metis in_set_conv_decomp Un_iff set_append)
  with syms_decomp_rightmost[of \<alpha> X w "[]" \<beta> \<gamma> "[]"]
  show ?thesis using False that(1) Cons_eq_appendI assms by force
qed

lemma eq_tl_lt_imp_substring:
  assumes "\<alpha> @ map Tm x = \<beta> @ map Tm y"
    "length x \<le> length y"
  obtains \<gamma> x' where "x' @ x = y" "\<gamma> @ map Tm x' = \<alpha>"
using assms proof (induction y arbitrary: \<alpha> x thesis rule: rev_induct)
  case (snoc a y)
  then show ?case by (cases x rule: rev_cases) auto
qed simp

lemma eq_hd_lt_imp_substring:
  assumes "\<alpha> @ \<gamma> = \<beta> @ \<delta>"
    "length \<alpha> \<le> length \<beta>"
  obtains \<gamma>' where "\<alpha> @ \<gamma>' = \<beta>"  "\<gamma>' @ \<delta> = \<gamma>"
  using assms proof (induction \<beta> arbitrary: \<alpha> \<gamma> thesis)
  case (Cons X \<beta>)
  show ?case proof (cases \<alpha>)
    case Nil
    then show ?thesis using Cons.prems unfolding Nil 
      by (metis append_self_conv2)
  qed (use Cons in auto)
qed simp 

lemma substring_app_cases[consumes 2, case_names prefix in_suffix]:
  assumes "\<alpha> @ map Tm u = \<beta> @ \<gamma> @ map Tm v"
    "length \<alpha> \<le> length (\<beta> @ \<gamma>)"
  obtains u' v' where "\<beta> = \<alpha> @ map Tm u'" "\<gamma> = map Tm v'" "u = u' @ v' @ v" |
    \<gamma>' u' where "\<alpha> = \<beta> @ \<gamma>'" "\<gamma> = \<gamma>' @ map Tm u'" "u = u' @ v"
proof (cases "length \<alpha> \<le> length \<beta>")
  case True
  with assms(1) obtain \<alpha>' where "\<beta> = \<alpha> @ \<alpha>'" "\<alpha>' @ \<gamma> @ map Tm v = map Tm u" 
    using eq_hd_lt_imp_substring[of \<alpha> "map Tm u" \<beta> "\<gamma> @ map Tm v"] by metis
  moreover from this(2) obtain u' v' where "\<alpha>' = map Tm u' \<and> \<gamma> = map Tm v'" 
    by (meson append_eq_map_conv)
  ultimately show ?thesis using that(1) 
    by (metis map_Tm_inject_iff map_append)
next
  case False
  with assms(1) obtain \<beta>' where "\<alpha> = \<beta> @ \<beta>'" "\<beta>' @ map Tm u = \<gamma> @ map Tm v"
    using eq_hd_lt_imp_substring[of \<beta> "\<gamma> @ map Tm v" \<alpha> "map Tm u"] by force
  moreover with assms(2) obtain \<gamma>' u' where "u = u' @ v" "\<gamma> = \<gamma>' @ map Tm u'"
    by (smt (verit, ccfv_SIG) add_diff_cancel_right' diff_add_inverse diff_commute diff_diff_left
        diff_is_0_eq eq_tl_lt_imp_substring length_append length_map)
  ultimately show ?thesis using that(2) by auto
qed


lemma app_eq_rm_cases:
  assumes "\<gamma> @ \<delta> = \<alpha> @ \<beta> @ map Tm w"
  obtains u v where "\<gamma> = \<alpha> @ \<beta> @ map Tm u" "\<delta> = map Tm v" "w = u @ v" |
    \<delta>' where "\<delta> = \<delta>' @ map Tm w" "\<gamma> @ \<delta>' = \<alpha> @ \<beta>" 
  using assms proof (induction "\<gamma> @ \<delta>" arbitrary: \<gamma> \<delta> \<alpha> \<beta> w thesis rule: rev_induct)
  case (snoc X \<zeta>)
  note X_snoc = this
  show ?case proof (cases w rule: rev_cases)
    case (snoc u a)
    note a_snoc = this
    show ?thesis proof (cases \<delta> rule: rev_cases)
      case Nil
      then show ?thesis using a_snoc X_snoc by force
    next
      case (snoc \<eta> Y)
      note X_snoc(1)[of \<gamma> \<eta> \<alpha> \<beta> u]
      then show ?thesis
        using snoc X_snoc(2-) a_snoc by cases force+
    qed
  qed (use snoc in simp)
qed simp

lemma rms_app_eq_tl_cases:
  assumes "\<alpha> @ \<beta> @ map Tm u = \<gamma> @ \<delta> @ map Tm v"
  obtains \<zeta> x where "v = x @ u" "\<zeta> @ map Tm x = \<alpha> @ \<beta>" |
    \<zeta> x where "u = x @ v" "\<zeta> @ map Tm x = \<gamma> @ \<delta>"
  using that by (cases rule: le_cases[of "length u" "length v"]) 
    (metis assms append_assoc  eq_tl_lt_imp_substring)+

lemma right_sententials_eq_impossible:
  assumes "\<beta> @ Nt A # map Tm u = \<beta>' @ Nt A' # map Tm u'" (is "?w = ?w'")
    "length \<beta> < length \<beta>'" (is "?n < ?m")
  shows False
proof -
  have inds: "?w!?n = Nt A" "?w'!?m = Nt A'" by auto 
  with assms obtain a where "?w!?m = Tm a"
    using index_gt_left_imp_right[of \<beta> ?m "Nt A" "map Tm u", OF assms(2)] by auto
  then show False using inds(2) assms(1) by simp
qed

lemma rm_eq_imp_eq:
  assumes "\<beta> @ Nt A # map Tm u = \<beta>' @ Nt A' # map Tm u'"
  shows "\<beta> = \<beta>'" "A = A'" "u = u'"
proof -
  show "u = u'"
  proof (rule ccontr)
    assume neq: "u \<noteq> u'"
    then show False
    proof (cases "length u = length u'")
      case False
      with assms have "length \<beta> \<noteq> length \<beta>'" by fastforce
      then consider "length \<beta> < length \<beta>'" | "length \<beta>' < length \<beta>" by linarith
      then show ?thesis
        using right_sententials_eq_impossible assms assms[symmetric] 
        by cases fast+
    qed (use assms neq in auto)
  qed
  with assms show "\<beta> = \<beta>'" "A = A'" by auto
qed

section \<open>Rightmost derivations\<close>

lemma deriver_imp_in_Prods:
  assumes "P \<turnstile> \<gamma> @ Nt A#map Tm w \<Rightarrow>r \<gamma>@\<alpha>@map Tm w"
  shows "(A, \<alpha>) \<in> P"
  using deriver.cases[OF assms]
  by (metis append_eq_append_conv rm_eq_imp_eq)

lemma deriver_imp_handle:
  assumes "P \<turnstile> \<beta> @ Nt A#map Tm u \<Rightarrow>r \<gamma> @ Nt X#map Tm v"
  obtains \<alpha> where "\<beta>@\<alpha>@map Tm u = \<gamma> @ Nt X#map Tm v"
    "(A, \<alpha>) \<in> P" 
proof -
  from deriver.cases[OF assms] obtain A' \<alpha>' \<beta>' u' where
    "\<beta> @ Nt A # map Tm u = \<beta>' @ Nt A' # map Tm u'"
    "\<gamma> @ Nt X # map Tm v = \<beta>' @ \<alpha>' @ map Tm u'"
    "(A', \<alpha>') \<in> P" by metis
  with rm_eq_imp_eq[OF this(1)] show thesis using that by simp
qed 

lemma deriver_imp_handle_Tms:
  assumes "P \<turnstile> map Tm u @ Nt A#map Tm x \<Rightarrow>r map Tm w"
  obtains v where "w = u @ v @ x" "(A, map Tm v) \<in> P"
proof -
  from deriver.cases[OF assms] obtain u' A' x' \<alpha> where eqs:
    "map Tm u @ Nt A # map Tm x = u' @ Nt A' # map Tm x'"
    "map Tm w = u' @ \<alpha> @ map Tm x'" 
    "(A', \<alpha>) \<in> P" by metis
  moreover note x_eq = rm_eq_imp_eq[OF this(1)]
  moreover obtain v where "\<alpha> = map Tm v" using eqs(2) 
    by (metis map_eq_append_conv)
  ultimately show thesis using that map_Tm_inject_iff by fastforce
qed


lemma derives_Nts_subset_preserved:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"
    "Nts_syms \<alpha> \<subseteq> Nts P"
  shows "Nts_syms \<beta> \<subseteq> Nts P"
  using assms proof induction
  case base
  then show ?case .
next
  case (step y z)
  from step(3)[OF step(4)] step(2) show ?case 
    by (smt (verit, ccfv_threshold) Nts_Lhss_Rhs_Nts Un_iff derive_Nts_syms_subset subset_eq)
qed



lemma derivers_append_map_Tm:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@map Tm v \<Rightarrow>r* u @ map Tm v"
  using assms by (simp add: derivern_append_map_Tm rtranclp_power)


lemma derivers_prepend:
  assumes "P \<turnstile> \<beta> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@\<beta> \<Rightarrow>r* \<alpha> @ u"
  using assms derivern_prepend rtranclp_power by (smt (verit))+

lemma deriver_cases[consumes 1, case_names rightmost Tms]:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r \<beta>"
  obtains \<gamma> A u \<gamma>' B v where "\<alpha> = \<gamma> @ Nt A # map Tm u" "\<beta> = \<gamma>' @ Nt B # map Tm v" |
          \<gamma> A u v where "\<alpha> = \<gamma> @ Nt A # map Tm u" "\<beta> = map Tm v"
proof -
  from assms obtain \<gamma> A u \<delta> where \<alpha>\<beta>_defs: "\<alpha> = \<gamma> @ Nt A # map Tm u" "\<beta> = \<gamma> @ \<delta> @ map Tm u"
    using deriver.cases by meson
  consider "\<nexists>B. Nt B \<in> set \<delta>" | B where "Nt B \<in> set \<delta>" by blast
  then show thesis
  proof cases
    case 1
    show ?thesis 
      by (meson \<alpha>\<beta>_defs(1) syms_split_rightmost Tms_iff_no_Nts that(1,2)) 
  next
    case 2
    then show ?thesis using syms_split_rightmost \<alpha>\<beta>_defs 
      by (metis Tms_iff_no_Nts that(1,2))
  qed
qed

lemma derivers_tl_substring:
  assumes "P \<turnstile> \<alpha> @ Nt A # map Tm v \<Rightarrow>r* \<beta> @ Nt B # map Tm w"
  obtains u where "w = u@v"
  using assms proof (induction "\<beta> @ Nt B # map Tm w" arbitrary: \<beta> B w thesis)
  case base
  then show ?case using rm_eq_imp_eq[OF base(1)] by blast
next
  case (step y \<beta> B w)
  then obtain \<gamma> C u where y_def: "y = \<gamma> @ Nt C # map Tm u" 
    by (metis deriver_cases)
  with step(3) obtain x where u_decomp: "u = x@v" by blast
  from step(2) obtain \<delta> where eq: "\<beta> @ Nt B # map Tm w = \<gamma> @ \<delta> @ map Tm u" 
    unfolding y_def using deriver_imp_handle by metis
  consider "Nt B \<in> set \<delta>" | "Nt B \<notin> set \<delta>" "Nt B \<in> set \<gamma>"
  proof (cases "Nt B \<in> set \<delta>")
    case False
    then show ?thesis using eq that 
      by (metis Un_iff ex_map_conv in_set_conv_decomp set_append sym.distinct(1))
  qed (use that in simp)
  then show ?case
    using eq u_decomp step by cases 
      ((metis append.assoc syms_decomp_rightmost2),
        (metis append.assoc append_Nil syms_decomp_rightmost[of \<beta> B _ "[]" \<gamma> \<delta>]))
qed

lemma deriver_rightmost_cases[consumes 1, case_names prod prefix]:
  assumes "P \<turnstile> \<alpha> @ Nt A # map Tm u \<Rightarrow>r \<beta> @ Nt B # map Tm w"
  obtains \<gamma> v where "\<beta> @ Nt B # map Tm w = \<alpha> @ \<gamma> @ Nt B # map Tm v @ map Tm u" |
          \<delta> v x where "\<alpha> = \<delta> @ Nt B # map Tm x" "\<beta> @ Nt B # map Tm w = \<alpha> @ map Tm (v@u)"
proof -
  from assms obtain \<gamma> where deriv: "\<beta> @ Nt B # map Tm w = \<alpha> @ \<gamma> @ map Tm u" "(A, \<gamma>) \<in> P" 
    by (metis deriver_imp_handle)
  then consider (Tms) x where "\<gamma> = map Tm x" | (Nt) \<delta> C \<zeta> where "\<gamma> = \<delta> @ Nt C # \<zeta>" 
    by (metis split_list Tms_iff_no_Nts)
  then show ?thesis 
  proof cases
    case Tms
    with deriv have "\<beta> @ Nt B # map Tm w = \<alpha> @ map Tm (x@u)" by auto
    moreover from this obtain \<delta> v where "\<alpha> = \<delta> @ Nt B # map Tm v" 
      by (metis Nts_syms_append Nts_syms_map_Tm append.right_neutral append_Nil in_Nts_syms 
          in_set_conv_decomp list.simps(8) syms_decomp_rightmost2)
    ultimately show ?thesis using deriv that by blast
  next
    case Nt
    obtain \<eta> D y where "Nt C # \<zeta> = \<eta> @ Nt D # map Tm y" 
        by (meson list.set_intros(1) syms_split_rightmost)
   moreover from this have "B = D" using deriv Nt rm_eq_imp_eq[of \<beta> B w "\<alpha> @ \<delta> @ \<eta>" D "y@u"]
     by simp
   ultimately show ?thesis using Nt that deriv by (metis append.assoc append_Cons)
  qed
qed

lemma derivers_induct[consumes 1, case_names base step]:
  assumes "P \<turnstile> xs \<Rightarrow>r* ys"
  and "Q xs"
  and "\<And>u A v w. \<lbrakk> P \<turnstile> xs \<Rightarrow>r* u @ Nt A #  map Tm v; Q (u @ Nt A # map Tm v); (A,w) \<in> P \<rbrakk> 
      \<Longrightarrow> Q (u @ w @ map Tm v)"
  shows "Q ys"
using assms
proof (induction rule: rtranclp_induct)
  case base
  from this(1) show ?case .
next
  case (step y z)
  from deriver.cases[OF step(2)] step(1,3-) show ?case by metis
qed

lemma converse_derivers_induct[consumes 1, case_names base step]:
  assumes "P \<turnstile> xs \<Rightarrow>r* ys"
  and "Q ys"
  and "\<And>A \<alpha> u v. \<lbrakk>(A, \<alpha>) \<in> P; P \<turnstile> u @ \<alpha> @ map Tm v \<Rightarrow>r* ys; Q (u @ \<alpha> @ map Tm v)\<rbrakk> 
    \<Longrightarrow> Q (u @ Nt A # map Tm v)"
shows "Q xs"
  using assms proof (induction rule: converse_rtranclp_induct)
  case base
  from this(1) show ?case .
next
  case (step y z)
  from deriver.cases[OF step(1)] step(2-) show ?case by metis
qed


lemma derivern_induct[consumes 1, case_names 0 Suc]:
  assumes "P \<turnstile> xs \<Rightarrow>r(n) ys"
  and "Q 0 xs"
  and "\<And>n u A v w. \<lbrakk> P \<turnstile> xs \<Rightarrow>r(n) u @ Nt A#map Tm v; Q n (u @ Nt A#map Tm v); (A,w) \<in> P \<rbrakk> 
    \<Longrightarrow> Q (Suc n) (u @ w @ map Tm v)"
  shows "Q n ys"
using assms(1) proof (induction n arbitrary: ys)
  case 0
  thus ?case using assms(2) by auto
next
  case (Suc n)
  from relpowp_Suc_E[OF Suc.prems]
  obtain xs' where n: "P \<turnstile> xs \<Rightarrow>r(n) xs'" and 1: "P \<turnstile> xs' \<Rightarrow>r ys" by auto
  from deriver.cases[OF 1] obtain u A v w where "xs' = u @ Nt A # map Tm v" "(A,w) \<in> P" "ys = u @ w @ map Tm v"
    by metis
  with Suc.IH[OF n] assms(3) n
  show ?case by blast
qed

lemma derivels_empty_imp_no_Tms:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>l* []"
    "\<alpha> \<noteq> []"
  obtains X \<beta> where "\<alpha> = Nt X # \<beta>"
proof -
  from assms obtain \<beta> where "P \<turnstile> \<alpha> \<Rightarrow>l \<beta>" "P \<turnstile> \<beta> \<Rightarrow>l* []" 
    by (metis converse_rtranclpE)
  with derivel.cases obtain u X \<gamma> where "\<alpha> = map Tm u @ Nt X # \<gamma>" by meson
  moreover from this have "map Tm u = []" using assms 
    by (simp add: derivels_map_Tm_append)
  ultimately show thesis using that by blast
qed

lemma derives_decomp_less:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>(Suc n) map Tm w"
  obtains \<gamma>\<^sub>1 i u X j v \<gamma>\<^sub>2 k x where
    "\<alpha> = \<gamma>\<^sub>1 @ Nt X # \<gamma>\<^sub>2"
    "P \<turnstile> \<gamma>\<^sub>1 \<Rightarrow>(i) map Tm u" "P \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v" "P \<turnstile> \<gamma>\<^sub>2 \<Rightarrow>(k) map Tm x" "w = u @ v @ x"
    "i + j + k = Suc n" "j > 0"
proof -
  from assms obtain \<gamma>\<^sub>1 X \<gamma>\<^sub>2 where "\<alpha> = \<gamma>\<^sub>1 @ Nt X # \<gamma>\<^sub>2" 
    by (smt (verit, ccfv_SIG) deriven_Suc_iff)
  moreover with deriven_appendD[of _ _ \<gamma>\<^sub>1 "Nt X # \<gamma>\<^sub>2" "map Tm w"] assms obtain i u jk vx where
    "Suc n = i + jk" "P \<turnstile> \<gamma>\<^sub>1 \<Rightarrow>(i) map Tm u" "P \<turnstile> Nt X # \<gamma>\<^sub>2 \<Rightarrow>(jk) map Tm vx"
    "w = u @ vx" using deriven_append_map_Tm by blast
  moreover from this(3) deriven_appendD[of _ _ "[Nt X]" \<gamma>\<^sub>2 "map Tm vx"] obtain j k v x where
    "j + k = jk" "P \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v" "P \<turnstile> \<gamma>\<^sub>2 \<Rightarrow>(k) map Tm x" 
    "vx = v @ x"
    by (metis (no_types, lifting) append_Cons append_Nil deriven_append_map_Tm)
  ultimately show thesis using that by fastforce
qed


lemma derive_word_imp_single_Nt:
  assumes "P \<turnstile> \<alpha> \<Rightarrow> map Tm w"
  obtains u v X x where 
    "\<alpha> = map Tm u @ Nt X # map Tm x" "P \<turnstile> [Nt X] \<Rightarrow> map Tm v" "w = u @ v @ x"
proof -
  from assms have "P \<turnstile> \<alpha> \<Rightarrow>(Suc 0) map Tm w" by auto
  from derives_decomp_less[OF this] show thesis using that 
    by (metis (no_types, lifting) add_is_0 not_less_zero one_is_add relpowp_0_E
        relpowp_Suc_0) 
qed

lemma derivern_singleton_imp_prod:
  assumes "P \<turnstile> [Nt X] \<Rightarrow>(n) map Tm w"
  obtains \<alpha> m where "n = Suc m" "P \<turnstile> [Nt X] \<Rightarrow> \<alpha>"
    "P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w"
  using assms by (cases n) (force, metis relpowp_Suc_D2)

lemma app_derivers_app:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* map Tm u"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  shows "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* map Tm (u@v)"
  using assms derivers_iff_derives by (metis derives_append_map_Tm)

lemma derivers_singleton_imp_produced:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # \<beta>"
  obtains m \<alpha>' B v \<alpha>'' \<beta>' where
    "m < Suc n"
    "P \<turnstile> [Nt A] \<Rightarrow>r(m) \<alpha>' @ Nt B # map Tm v"
    "P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm v"
    "\<alpha> = \<alpha>' @ \<alpha>''"
    "P \<turnstile> \<beta>' @ map Tm v \<Rightarrow>r* \<beta>"
  using assms proof (induction "Suc n" arbitrary: n \<alpha> X \<beta> thesis rule: less_induct)
  case less
  show ?case 
  proof (cases n)
    case 0
    then show ?thesis using less(2)[of 0 "[]" A "[]" \<alpha> \<beta>] less(3) by auto
  next
    case (Suc m)
    note Suc_m = this
    from less(3) obtain \<alpha>' B v where n_steps: "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha>' @ Nt B # map Tm v"
      "P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha> @ Nt X # \<beta>" 
      by (smt (verit) deriver.cases relpowp_Suc_E)
    then obtain \<gamma> where B_prod: "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v" "(B, \<gamma>) \<in> P"
      by (metis deriver_imp_handle in_set_conv_decomp syms_split_rightmost)
    then show thesis proof (cases rule: nonword_eq_append_map_Tm_cases)
      case (1 \<alpha>'' \<beta>')
      then show ?thesis using less(2)[OF _ n_steps(1), of \<alpha>'' \<beta>'] B_prod n_steps(2) by fastforce
    next
      case (2 \<alpha>'')
      with n_steps have "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha> @ Nt X # \<alpha>'' @ Nt B # map Tm v" by simp
      with less(1)[of _ X \<alpha> "\<alpha>'' @ Nt B # map Tm v"] obtain k \<delta> C w \<zeta> \<beta>' where k_steps:
        "k < Suc m" "P \<turnstile> [Nt A] \<Rightarrow>r(k) \<delta> @ Nt C # map Tm w"
        "P \<turnstile> \<delta> @ Nt C # map Tm w \<Rightarrow>r \<delta> @ \<zeta> @ Nt X # \<beta>' @ map Tm w" "\<alpha> = \<delta> @ \<zeta>"
        "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<alpha>'' @ Nt B # map Tm v" using Suc by blast
      from this(5) \<open>\<beta> = \<alpha>'' @ \<gamma> @ map Tm v\<close> B_prod(2) have derivers_\<beta>: "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<beta>" 
        using 2 by (meson deriver.intros rtranclp.simps)
      show ?thesis using less(2)[OF _ k_steps(2-4) derivers_\<beta>] Suc_m k_steps(1) by linarith    
    qed
  qed
qed

lemma deriven_leq:
  assumes "Prods G \<turnstile> \<alpha> @ \<beta> @ \<gamma> \<Rightarrow>(n) map Tm w"
  obtains m v where "Prods G \<turnstile> \<beta> \<Rightarrow>(m) map Tm v" "m \<le> n"
  using assms by (metis add_leD1 deriven_append_map_Tm le_add2)

lemma derivern_leq:
  assumes "Prods G \<turnstile> \<alpha> @ \<beta> @ \<gamma> \<Rightarrow>r(n) map Tm w"
  obtains m v where "Prods G \<turnstile> \<beta> \<Rightarrow>r(m) map Tm v" "m \<le> n"
  using assms derivern_iff_deriven deriven_leq by meson


lemma derivern_imp_last_step:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r(Suc n) map Tm w"
  obtains u v x X where "P \<turnstile> \<alpha> \<Rightarrow>r(n) map Tm u @ Nt X # map Tm x"
    "P \<turnstile> map Tm u @ Nt X # map Tm x \<Rightarrow>r map Tm (u @ v @ x)" "w = u @ v @ x"
  using assms proof (induction n arbitrary: \<alpha> thesis)
  case 0
  hence "P \<turnstile> \<alpha> \<Rightarrow>r map Tm w" by auto
  then show ?case using 0(2) deriver.cases 
    by (smt (verit, ccfv_threshold) "0.prems"(1) derive_word_imp_single_Nt deriver_imp_derive
        relpowp_Suc_E)
next
  case (Suc n)
  then obtain \<beta> where "P \<turnstile> \<alpha> \<Rightarrow>r \<beta>" "P \<turnstile> \<beta> \<Rightarrow>r(Suc n) map Tm w" 
    by (metis relpowp_Suc_D2)
  with Suc.IH[OF _ this(2)] show ?case using Suc.prems(1) 
    by (metis (no_types, opaque_lifting) relpowp_Suc_I2)
qed

lemma derivers_last_step_single_Nt:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>" "P \<turnstile> \<beta> \<Rightarrow>r map Tm w"
  obtains u v x X where "\<beta> = map Tm u @ Nt X # map Tm x"
    "(X, map Tm v) \<in> P" "w = u @ v @ x"
  using assms deriver_imp_handle_Tms by (metis (no_types, lifting) derive_word_imp_single_Nt deriver_imp_derive)

lemma derivern_appendD:
  assumes "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r(n) \<gamma>"
  obtains \<delta> \<zeta> m k where "m + k = n" "P \<turnstile> \<alpha> \<Rightarrow>r(m) \<delta>" "P \<turnstile> \<beta> \<Rightarrow>r(k) \<zeta>" "\<gamma> = \<delta> @ \<zeta>"
  using assms proof (induction n arbitrary: \<alpha> \<beta> thesis)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain \<eta> where stepn: "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r \<eta>" "P \<turnstile> \<eta> \<Rightarrow>r(n) \<gamma>" by (metis relpowp_Suc_D2)
  consider (Tms) v where "\<beta> = map Tm v" | (rightmost) \<beta>' A w where "\<beta> = \<beta>' @ Nt A # map Tm w"
    by (metis destTm.cases ex_map_conv syms_split_rightmost)
  then show ?case proof cases
    case Tms
    with stepn obtain \<alpha>' A \<alpha>'' u where "\<alpha> = \<alpha>' @ Nt A # map Tm u" 
      "\<eta> = \<alpha>' @ \<alpha>'' @ map Tm (u@v)" 
      by (smt (verit, ccfv_threshold) append.assoc deriver.simps deriver_append_map_Tm
          map_append)
    from Suc.IH[of "\<alpha>' @ \<alpha>''" "map Tm (u@v)"] stepn[unfolded this(2)] 
     show ?thesis  
       by (metis Suc.prems Tms add.right_neutral derivern_append_map_Tm relpowp_0_I)
  next
    case rightmost
    with stepn(1) obtain \<alpha>' where step: "(A, \<alpha>') \<in> P" "\<eta> = \<alpha> @ \<beta>' @ \<alpha>' @ map Tm w" 
      by (smt (verit, ccfv_threshold) append.assoc rm_eq_imp_eq deriver.cases)
    from Suc.IH[of \<alpha> "\<beta>' @ \<alpha>' @ map Tm w"] stepn[unfolded this] obtain m k \<delta> \<zeta> where ih:
      "m + k = n" "P \<turnstile> \<alpha> \<Rightarrow>r(m) \<delta>" "P \<turnstile> \<beta>' @ \<alpha>' @ map Tm w \<Rightarrow>r(k) \<zeta>" "\<gamma> = \<delta> @ \<zeta>" by blast
    with step rightmost have "P \<turnstile> \<beta> \<Rightarrow>r(Suc k) \<zeta>" 
      using deriver.intros by (meson relpowp_Suc_I2)
    with ih show ?thesis using Suc.prems(1) by force
  qed
qed

lemma derives_map_Tm_rm_cases[case_names Tms Nt]:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
  obtains "\<alpha> = map Tm w" | 
    n u v x X where "P \<turnstile> \<alpha> \<Rightarrow>r(n) map Tm u @ Nt X # map Tm x"
    "P \<turnstile> map Tm u @ Nt X # map Tm x \<Rightarrow>r map Tm (u @ v @ x)" "w = u @ v @ x"
proof -
  from assms obtain n where derivern: "P \<turnstile> \<alpha> \<Rightarrow>r(n) map Tm w"
    using derivers_iff_derives  by (metis rtranclp_power)
  show thesis by (cases n) 
      (use that derivern in simp, use that derivern derivern_imp_last_step in meson)
qed

lemma deriver_prepend:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r \<beta>"
  shows "P \<turnstile> \<gamma> @ \<alpha> \<Rightarrow>r \<gamma> @ \<beta>"
  using assms proof cases
  case (1 A \<alpha> u v)
  then show ?thesis using deriver.intros[OF 1(3), of "\<gamma> @ u" v] by auto
qed

lemma deriver_prefix_indep:
  assumes "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r \<alpha> @ \<gamma>"
    "\<beta> = \<delta> @ Nt A # map Tm w"
  shows "P \<turnstile> \<alpha>' @ \<beta> \<Rightarrow>r \<alpha>' @ \<gamma>"
  using assms proof cases
  case (1 A \<zeta> \<delta> w)
  from this(1)[symmetric] show ?thesis proof (cases rule: rm_eq_append_cases)
    case (left u v)
    from this(2) show ?thesis using assms(2) 
      by (metis Tms_iff_no_Nts in_set_conv_decomp)
  next
    case (right \<eta>)
    with 1 have "P \<turnstile> \<beta> \<Rightarrow>r \<gamma>" 
      using deriver.intros by fastforce
    from this[THEN deriver_prepend] show ?thesis by presburger
  qed
qed

lemma derivers_appendD:
  "(P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma>) = 
    ((\<exists>\<beta>'. P \<turnstile> \<beta> \<Rightarrow>r* \<beta>' \<and> \<gamma> = \<alpha> @ \<beta>') \<or> (\<exists>\<alpha>' v. P \<turnstile> \<alpha> \<Rightarrow>r* \<alpha>' \<and> P \<turnstile> \<beta> \<Rightarrow>r* map Tm v \<and> \<gamma> = \<alpha>' @ map Tm v))" 
  (is "_ = ?EX")
proof
  show "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma> \<Longrightarrow> ?EX"
  proof (induction "\<alpha> @ \<beta>" arbitrary: \<alpha> \<beta> rule: converse_rtranclp_induct)
    case (step z)
      show ?case proof (cases \<beta> rule: syms_rm_cases)
        case (Tms w)
        then show ?thesis using step(3)[of _ "map Tm w"] 
          by (metis (no_types, lifting) derivern_append_map_Tm rtranclp.simps rtranclp_power 
              rtranclp_trans step.hyps(1,2))
      next
        case (Nt \<beta>' A w)
        with step obtain \<delta> where z_app: "P \<turnstile> \<beta> \<Rightarrow>r \<beta>' @ \<delta> @ map Tm w"  "z = \<alpha> @ \<beta>' @ \<delta> @ map Tm w"   
          by (smt (verit, best) append.assoc deriver.cases deriver.intros rm_eq_imp_eq)
        from step(3)[OF this(2)] consider 
          \<beta>'' where "P \<turnstile> \<beta>' @ \<delta> @ map Tm w \<Rightarrow>r* \<beta>''" "\<gamma> = \<alpha> @ \<beta>''" |
          \<alpha>'' v where "P \<turnstile> \<alpha>  \<Rightarrow>r* \<alpha>''" "P \<turnstile> \<beta>' @ \<delta> @ map Tm w \<Rightarrow>r* map Tm v"  "\<gamma> = \<alpha>'' @ map Tm v"  
          using derivers_imp_derives derives_map_Tm_iff by blast
        thus ?thesis using z_app by cases fastforce+
      qed
    qed simp
next
  assume ?EX
  then show "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma>" by standard 
      (use derivers_prepend in blast, metis derivers_prepend derivers_append_map_Tm rtranclp_trans)
qed

lemma derivers_append_cases [consumes 1, case_names suffix prefix]:
  assumes "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* \<gamma>"
  obtains \<beta>' where "P \<turnstile> \<beta> \<Rightarrow>r* \<beta>'" "\<gamma> = \<alpha> @ \<beta>'" |
    \<alpha>' v where "P \<turnstile> \<alpha> \<Rightarrow>r* \<alpha>'" "P \<turnstile> \<beta> \<Rightarrow>r* map Tm v" "\<gamma> = \<alpha>' @ map Tm v"
  using derivers_appendD[THEN iffD1, OF assms] by blast

section \<open>NFAs\<close>

context nfa begin
lemma Power_nextl_eq_nfa_nextl [simp]:
  "(dfa.nextl Power_dfa (dfa.init Power_dfa) u) = nextl (init M) u"
proof (induct u rule: List.rev_induct)
  case Nil show ?case
    using hinsert_def by (simp add: dfa.nextl.simps(1) dfa_Power)
next
  case (snoc x u) then show ?case
    using init finite_nextl nextl_state [THEN subsetD]
    by (simp add: dfa.nextl_snoc dfa_Power)
qed

lemma in_states_imp_in_epsclo:
  assumes "q \<in> nfa.states M" "q \<in> Q"
  shows "q \<in> epsclo Q"
  unfolding epsclo_def using assms by blast



subsection \<open>NFA Configurations and Steps\<close>

type_synonym ('b,'c) config = "'b \<times> 'c list"

inductive step :: "('s,'a) config \<Rightarrow> ('s,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
step_nxt[intro]:  "q \<in> nfa.nxt M p a \<Longrightarrow> (p,a#u) \<turnstile> (q,u)" |
step_eps[intro]:  "(p,q) \<in> nfa.eps M \<Longrightarrow> (p,w) \<turnstile> (q,w)"

inductive_cases step_nxtE[elim]: "(q,a#u) \<turnstile> (r,u)"
inductive_cases step_epsE[elim]: "(q,w) \<turnstile> (r,w)"

lemma step_equal_or_Cons:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "u = v \<or> (\<exists>a. u = a#v)"
  using assms by cases auto

lemma step_len_dec:
  assumes "(p,u) \<turnstile> (q,v)"
  shows "length u \<ge> length v" 
  using step_equal_or_Cons[OF assms] by fastforce

abbreviation stepn  (\<open>_ \<turnstile>'(_') _\<close> 55) where
  "c0 \<turnstile>(n) c1 \<equiv> (step ^^ n) c0 c1"

abbreviation steps (infix \<open>\<turnstile>*\<close> 55) where
  "steps \<equiv> (step \<^sup>*\<^sup>*)"

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by (induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct)
  (use step_len_dec surj_pair le_trans in fastforce)+

lemma nxt_indep:
  assumes "(p, a # u) \<turnstile> (q, u)"
  shows "(p, a # v) \<turnstile> (q, v)"
  using assms by auto

lemma eps_indep:
  assumes "(p, u) \<turnstile> (q, u)"
  shows "(p, v) \<turnstile> (q, v)"
  using assms by blast

lemma step_imp_nempty_or_eq:
  assumes "(p, u) \<turnstile> (q, v)"
  shows "u \<noteq> [] \<or> u = v"
  using assms by cases auto

lemma stepn_append:
  assumes "(p, u@v) \<turnstile>(n) (q, v)"
  shows "(p, u@w) \<turnstile>(n) (q, w)"
  using assms proof (induction n arbitrary: p u q)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain r x where n_steps: "(p, u@v) \<turnstile> (r, x)" "(r, x) \<turnstile>(n) (q, v)" 
    by (metis eq_fst_iff relpowp_Suc_D2)
  from this(1) show ?case 
  proof cases
    case (step_nxt a)
    then obtain y where u_decomp: "u = a # y" "x = y @ v" using n_steps 
      by (metis append_eq_Cons_conv impossible_Cons relpowp_imp_rtranclp steps_len_dec)
    hence "(p, u @ w) \<turnstile> (r, y @ w)" by (auto simp: step_nxt(2))
    also note Suc.IH[OF n_steps(2)[unfolded u_decomp(2)]]
    finally show ?thesis .
  next
    case step_eps
    with Suc.IH n_steps(2) have "(r, u @ w) \<turnstile>(n) (q, w)" by blast
    then show ?thesis using eps_indep[OF n_steps(1)[unfolded step_eps(1)], of "u @ w"] 
      by (meson relpowp_Suc_I2)
  qed
qed

lemma steps_append:
  "(p, u @ v) \<turnstile>* (q, v) \<Longrightarrow> (p, u @ w) \<turnstile>* (q, w)"
  using stepn_append[THEN relpowp_imp_rtranclp] rtranclp_imp_relpowp by metis

lemma in_epsclo_imp_reachable:
  assumes "q \<in> epsclo Q"
  obtains p where "p \<in> Q" "(p, w) \<turnstile>* (q, w)"
proof -
  from assms obtain p where "p \<in> Q" "(p, q) \<in> (nfa.eps M)\<^sup>*"
    unfolding epsclo_def by blast
  from this(2) show thesis
    using that by (induction arbitrary: thesis) 
      (use \<open>p \<in> Q\<close> in simp, metis step_eps rtranclp.simps)
qed 

lemma in_nextl_imp_reaches:
  assumes "q \<in> nextl Q w"
  obtains p where "p \<in> Q" "(p, w) \<turnstile>* (q, [])"
  using assms proof (induction w arbitrary: Q thesis)
  case Nil
  hence "q \<in> epsclo Q" by auto
  then show ?case using Nil(1) in_epsclo_imp_reachable by blast
next
  case (Cons a w) 
  then obtain p where p_defs: "p \<in> (\<Union>q \<in> epsclo Q. nfa.nxt M q a)" "(p, w) \<turnstile>* (q, [])"
    using nextl.simps(2) by metis
  then obtain r where r_defs: "r \<in> epsclo Q" "p \<in> nfa.nxt M r a" by blast
  with in_epsclo_imp_reachable obtain s where "s \<in> Q" "(s, a#w) \<turnstile>* (r, a#w)" by blast
  note this(2)
  also from r_defs have "(r, a#w) \<turnstile> (p, w)" by blast
  also note p_defs(2)
  finally show ?case using \<open>s \<in> Q\<close> Cons by fast
qed

lemma reachable_imp_in_nextl:
  assumes "p \<in> nfa.states M"
    "nfa.eps M \<subseteq> nfa.states M \<times> nfa.states M"
    "(p, w) \<turnstile>* (q, [])"
  shows "q \<in> nextl {p} w"
  using assms(3,1) proof (induction rule: converse_rtranclp_induct2)
  case refl
  then show ?case using epsclo_def by simp
next
  case (step p u r v)
  from step(1) show ?case
  proof cases
    case (step_nxt a)
    with nfa.nxt[OF nfa_axioms step(4)] step have q_in_nextl_r: "q \<in> nextl {r} v" 
      by blast                                            
    have "nextl {p} u = nextl (\<Union>q\<in>epsclo {p}. nfa.nxt M q a) v"    
      using step_nxt(1) nextl.simps(2) by blast
    with step_nxt have "nextl {r} v \<subseteq> nextl {p} u" 
      by (metis (mono_tags, lifting) Int_insert_left_if1 UN_I empty_subsetI insert_subset nextl_mono
          nfa.epsclo_increasing nfa_axioms step.prems)
    then show ?thesis using q_in_nextl_r by blast 
  next
    case step_eps
    hence r_subst_p: "epsclo {r} \<subseteq> epsclo {p}"
      unfolding epsclo_def by auto
    from step_eps step(3) assms have q_in_nextl_r: "q \<in> nextl {r} u" by blast
    also have "... = nextl (epsclo {r}) u" by simp
    also from r_subst_p have "... \<subseteq> nextl (epsclo {p}) u" 
      using nextl_mono by presburger
    also have "... = nextl {p} u" by simp
    finally show ?thesis .
  qed
qed

lemma eps_subst_states_imp_nextl_eq_reachable:
  assumes "nfa.eps M \<subseteq> nfa.states M \<times> nfa.states M"
  shows "i \<in> nextl (nfa.init M) w = (\<exists>q \<in> nfa.init M. (q, w) \<turnstile>* (i, []))"
proof
  show "i \<in> nextl (nfa.init M) w \<Longrightarrow> \<exists>q\<in>nfa.init M. (q, w) \<turnstile>* (i, [])"
    using in_nextl_imp_reaches by metis
next
  show "\<exists>q\<in>nfa.init M. (q, w) \<turnstile>* (i, []) \<Longrightarrow> i \<in> nextl (nfa.init M) w"
    using reachable_imp_in_nextl[OF _ assms] 
    by (metis Set.set_insert empty_subsetI insert_subset nextl_mono nfa.init nfa_axioms)
qed


lemma eps_subst_states_imp_language_eq_init_final_reachable:
  assumes "nfa.eps M \<subseteq> nfa.states M \<times> nfa.states M"
  shows "language = {w. \<exists>q\<^sub>0 \<in> nfa.init M. \<exists>f \<in> nfa.final M. (q\<^sub>0, w) \<turnstile>* (f, [])}"
  (is "_ = ?r")
  using eps_subst_states_imp_nextl_eq_reachable[OF assms] unfolding language_def
  by blast

end

section \<open>Others\<close>

lemma derives_non_word_imp_non_word:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>* \<beta> @ Nt X # \<gamma>"
  shows "Nts_syms \<alpha> \<noteq> {}"
proof 
  assume "Nts_syms \<alpha> = {}"
  then obtain w where "\<alpha> = map Tm w" using Nts_syms_empty_iff by blast
  with assms have "\<beta> @ Nt X # \<gamma> = map Tm w" 
    by (simp add: derives_map_Tm_iff)
  thus False by (metis Tms_iff_no_Nts in_set_conv_decomp)
qed

lemma prod_substring_imp_Nts_subset:
  "(A, \<alpha> @ \<beta> @ \<gamma>) \<in> P \<Longrightarrow> Nts_syms \<beta> \<subseteq> Nts P"
  unfolding Nts_def by fastforce

lemma finite_lists_length_eq_set:
  assumes "finite A" "finite B"
  shows "finite {xs|xs n. set xs \<subseteq> A \<and> length xs = n \<and> n \<in> B}"
proof -
  have "{xs|xs n. set xs \<subseteq> A \<and> length xs = n \<and> n \<in> B} = 
    (\<Union>n \<in> B. {xs|xs \<alpha>. set xs \<subseteq> A \<and> length xs = n})" by auto
  with assms finite_lists_length_eq show ?thesis by auto
qed

lemma less_induct_Suc[case_names 0 Suc]:
  assumes "P 0"
    "\<And>n. (\<And>m. m < Suc n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)"
  shows "P n"
  using assms proof (induction n rule: less_induct)
  case (less n)
  show ?case 
  proof (cases n)
    case (Suc m)
    then show ?thesis using less by blast
  qed (use less in simp)
qed

lemma stepcnt_cases [consumes 1, case_names refl step]:
  assumes "r\<^sup>*\<^sup>* a b"
    "a = b \<Longrightarrow> P"
    "\<And>n. (r ^^ Suc n) a b \<Longrightarrow> P"
  shows P
  using assms(1) by cases (use assms(2-) rtranclp_imp_relpowp in fastforce)+

end
