theory Auxiliary
  imports Context_Free_Grammar.Context_Free_Grammar Finite_Automata_HF.Finite_Automata_HF
begin 

section \<open>Lists\<close>

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

corollary take_diff:
  "take n xs = take n ys \<Longrightarrow> take (n-m) xs = take (n-m) ys"
by (meson diff_le_self take_cong_le)

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
  using assms by(auto simp: append_eq_iffs)

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

text \<open>Same as @{thm non_word_has_last_Nt}, except with Cons instead of \<open>@\<close>.\<close>
lemma syms_split_rightmost:
  assumes "Nt A \<in> set \<alpha>"
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

section \<open>Rightmost derivations\<close>

lemma deriver_imp_handle:
  assumes "P \<turnstile> \<beta> @ Nt A#map Tm u \<Rightarrow>r \<gamma> @ Nt X#map Tm v"
  obtains \<alpha> where "\<beta>@\<alpha>@map Tm u = \<gamma> @ Nt X#map Tm v"
    "(A, \<alpha>) \<in> P" 
  using deriver.cases[OF assms] Nt_map_Tm_eq_Nt_map_TmD
  by metis

lemma deriver_imp_handle_Tms:
  assumes "P \<turnstile> map Tm u @ Nt A#map Tm x \<Rightarrow>r map Tm w"
  obtains v where "w = u @ v @ x" "(A, map Tm v) \<in> P"
proof -
  from deriver.cases[OF assms] obtain u' A' x' \<alpha> where eqs:
    "map Tm u @ Nt A # map Tm x = u' @ Nt A' # map Tm x'"
    "map Tm w = u' @ \<alpha> @ map Tm x'" 
    "(A', \<alpha>) \<in> P" by metis
  moreover note x_eq = Nt_map_Tm_eq_Nt_map_TmD[OF this(1)]
  moreover obtain v where "\<alpha> = map Tm v" using eqs(2) 
    by (metis map_eq_append_conv)
  ultimately show thesis using that map_Tm_inject_iff by fastforce
qed

lemma derivers_append_map_Tm:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@map Tm v \<Rightarrow>r* u @ map Tm v"
  by (meson assms derivern_append_map_Tm rtranclp_power)

lemma derivers_prepend:
  assumes "P \<turnstile> \<beta> \<Rightarrow>r* u"
  shows "P \<turnstile> \<alpha>@\<beta> \<Rightarrow>r* \<alpha> @ u"
  using assms derivern_prepend rtranclp_power by metis

lemma deriver_imp_in_Prods:
  assumes "P \<turnstile> \<gamma> @ Nt A#map Tm w \<Rightarrow>r \<gamma>@\<alpha>@map Tm w"
  shows "(A, \<alpha>) \<in> P"
  using deriver.cases[OF assms]
  by (metis append_eq_append_conv Nt_map_Tm_eq_Nt_map_TmD)

lemma deriven_decomp_less:
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

lemma derivern_singleton_imp_produced:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # \<beta>"
  obtains m \<alpha>' B v \<alpha>'' \<beta>' where
    "m < Suc n"
    "P \<turnstile> [Nt A] \<Rightarrow>r(m) \<alpha>' @ Nt B # map Tm v"
    "P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm v"
    "\<alpha> = \<alpha>' @ \<alpha>''"
    "P \<turnstile> \<beta>' @ map Tm v \<Rightarrow>r* \<beta>"
  using assms proof (induction "Suc n" arbitrary: n \<alpha> \<beta> thesis rule: less_induct)
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
      with less(1)[of _ \<alpha> "\<alpha>'' @ Nt B # map Tm v"] obtain k \<delta> C w \<zeta> \<beta>' where k_steps:
        "k < Suc m" "P \<turnstile> [Nt A] \<Rightarrow>r(k) \<delta> @ Nt C # map Tm w"
        "P \<turnstile> \<delta> @ Nt C # map Tm w \<Rightarrow>r \<delta> @ \<zeta> @ Nt X # \<beta>' @ map Tm w" "\<alpha> = \<delta> @ \<zeta>"
        "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<alpha>'' @ Nt B # map Tm v" using Suc by blast
      from this(5) \<open>\<beta> = \<alpha>'' @ \<gamma> @ map Tm v\<close> B_prod(2) have derivers_\<beta>: "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<beta>" 
        using 2 by (meson deriver.intros rtranclp.simps)
      show ?thesis using less(2)[OF _ k_steps(2-4) derivers_\<beta>] Suc_m k_steps(1) by linarith    
    qed
  qed
qed

lemma derivern_imp_last_step:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r(Suc n) map Tm w"
  obtains u v x X where "P \<turnstile> \<alpha> \<Rightarrow>r(n) map Tm u @ Nt X # map Tm x"
    "P \<turnstile> map Tm u @ Nt X # map Tm x \<Rightarrow>r map Tm (u @ v @ x)" "w = u @ v @ x"
  using assms proof (induction n arbitrary: \<alpha> thesis)
  case 0
  hence "P \<turnstile> \<alpha> \<Rightarrow>r map Tm w" by auto
  then show ?case using 0(2) deriver.cases 
    by (smt (verit, ccfv_threshold) "0.prems"(1) derive_map_TmD deriver_imp_derive
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
  using assms deriver_imp_handle_Tms by (metis (no_types, lifting) derive_map_TmD deriver_imp_derive)

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
  by (metis assms derivern_prepend relpowp_Suc_0)

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
          by (smt (verit, best) append.assoc deriver.cases deriver.intros Nt_map_Tm_eq_Nt_map_TmD)
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

lemma derivers_leftmost_derivers_last_step:
  assumes "P \<turnstile> Nt A # \<alpha> \<Rightarrow>r* \<beta>"
    "P \<turnstile> \<beta> \<Rightarrow>r map Tm w"
  obtains \<gamma> u v where "P \<turnstile> [Nt A] \<Rightarrow>r* \<gamma>" "P \<turnstile> \<gamma> \<Rightarrow>r map Tm u"
    "\<beta> = \<gamma> @ map Tm v" "P \<turnstile> \<alpha> \<Rightarrow>r* map Tm v" "w = u @ v"
proof -
  from assms have "P \<turnstile> [Nt A] @ \<alpha> \<Rightarrow>r* \<beta>" by simp
  then show thesis proof (cases rule: derivers_append_cases)
    case (suffix \<alpha>')
    from assms(2) show thesis unfolding suffix proof (cases, goal_cases deriver)
      case (deriver A' \<gamma> u' v')
      hence eqs [simp]: "u' = []" "A' = A" "map Tm v' = \<alpha>'"  
      proof -
        from deriver have "u' = [] \<and> A' = A \<and> map Tm v' = \<alpha>'" 
          by (metis Tms_iff_no_Nt append_Cons append_Nil list.inject neq_Nil_conv sym.inject(1))
        thus "u' = []" "A' = A" "map Tm v' = \<alpha>'"  by blast+
      qed
      moreover from deriver obtain u where "\<gamma> = map Tm u" "P \<turnstile> [Nt A] \<Rightarrow>r map Tm u"
        unfolding eqs by (metis append_eq_map_conv deriver_singleton)
      ultimately show ?thesis using that[of "[Nt A]" u v'] suffix deriver 
        by (metis append_Cons append_Nil map_Tm_Nt_eq_map_Tm_Nt map_append rtranclp.rtrancl_refl)
    qed 
  next
    case (prefix \<gamma> v)
    from assms(2) obtain u where "P \<turnstile> \<gamma> \<Rightarrow>r map Tm u" "w = u @ v"
      unfolding prefix(3) by (smt (verit, ccfv_threshold) append_eq_map_conv deriver_append_map_Tm
          map_Tm_inject_iff)
    with prefix show thesis using that by blast
  qed
qed

lemma S_deriven_Suc_imp_all_nts_in_Nts:
  assumes "A \<in> Nts_syms \<alpha>"
    "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc n) \<alpha>" 
  shows "A \<in> Nts (Prods G)"
  using assms(2,1) proof (induction n arbitrary: \<alpha>)
  case 0
  hence "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow> \<alpha>" by auto
  then show ?case 
    using 0 Cons_eq_append_conv unfolding Nts_def 
    by cases (auto simp: Cons_eq_append_conv)
next
  case (Suc n)
  then obtain \<alpha>' where step_Suc: "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc n) \<alpha>'" "Prods G \<turnstile> \<alpha>' \<Rightarrow> \<alpha>"
    by auto
  then consider 
    B \<beta> \<gamma> \<delta> where "\<alpha>' = \<gamma> @ [Nt B] @ \<delta>" "\<alpha> = \<gamma> @ \<beta> @ \<delta>" "(B, \<beta>) \<in> Prods G" "A \<in> Nts_syms \<beta>" |
    B \<beta> \<gamma> \<delta> where "\<alpha>' = \<gamma> @ [Nt B] @ \<delta>" "\<alpha> = \<gamma> @ \<beta> @ \<delta>" "(B, \<beta>) \<in> Prods G" "A \<notin> Nts_syms \<beta>"
    by (meson derive.cases)
  then show ?case 
    using Suc step_Suc unfolding Nts_def Nts_syms_def by cases auto
qed

section \<open>NFAs\<close>

context nfa begin
lemma Power_nextl_eq_nfa_nextl [simp]:(*TODO mv?*)
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

lemma steps_substring:
  "(p, w) \<turnstile>* (q, v) \<Longrightarrow> \<exists>u. w = u@v"
proof (induction "(q, v)" arbitrary: q v rule: rtranclp_induct)
  case (step y)
  from this(2) show ?case 
    using step by cases auto
qed auto

lemma steps_len_dec:
  "(p,u) \<turnstile>* (q,v) \<Longrightarrow> length u \<ge> length v" 
  by (induction "(p,u)" "(q,v)" arbitrary: q v rule: rtranclp.induct)
  (use step_len_dec surj_pair le_trans in fastforce)+

lemma eps_indep:
  assumes "(p, u) \<turnstile> (q, u)"
  shows "(p, v) \<turnstile> (q, v)"
  using assms by blast

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

lemma stepcnt_cases [consumes 1, case_names refl step]:
  assumes "r\<^sup>*\<^sup>* a b"
    "a = b \<Longrightarrow> P"
    "\<And>n. (r ^^ Suc n) a b \<Longrightarrow> P"
  shows P
  using assms(1) by cases (use assms(2-) rtranclp_imp_relpowp in fastforce)+

end
