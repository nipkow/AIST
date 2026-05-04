theory Auxiliary
  imports Context_Free_Grammar.Context_Free_Grammar 
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

corollary syms_decomp_rightmost:
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

corollary syms_decomp_rightmost2:
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

lemma syms_split_rightmost:
  assumes "\<exists>A. Nt A \<in> set \<alpha>"
  obtains \<beta> A u where "\<alpha> = \<beta> @ Nt A # map Tm u"
  using assms proof (induction "length \<alpha>" arbitrary: \<alpha> thesis rule: less_induct)
  case less
  then obtain X \<beta> where \<alpha>_def: "\<alpha> = X#\<beta>" 
    by (metis list.set_cases)
  show ?case 
  proof (cases "\<exists>A. Nt A \<in> set \<beta>")
    case True
    show thesis using less(1)[OF _ _ True] less(2) unfolding \<alpha>_def 
      by (metis Cons_eq_appendI length_Cons lessI)
  next
    case False
    show ?thesis using no_Nts_imp_Tms[OF False] less(2)[of "[]"] less(3) False 
      unfolding \<alpha>_def by force
  qed
qed


section \<open>Rightmost derivations\<close>

lemma right_derivs_eq_impossible:
  assumes "\<beta> @ Nt A # map Tm u = \<beta>' @ Nt A' # map Tm u'" (is "?w = ?w'")
    "length \<beta> < length \<beta>'" (is "?n < ?m")
  shows False
proof -
  have inds: "?w!?n = Nt A" "?w'!?m = Nt A'" by auto 
  with assms obtain a where "?w!?m = Tm a"
    using index_gt_left_imp_right[of \<beta> ?m "Nt A" "map Tm u", OF assms(2)] by auto
  then show False using inds(2) assms(1) by simp
qed

lemma right_derivs_eq_imp_eq_tl:
  assumes "\<beta> @ Nt A # map Tm u = \<beta>' @ Nt A' # map Tm u'"
  shows "u = u'"
proof (rule ccontr)
  assume neq: "u \<noteq> u'"
  then show False
  proof (cases "length u = length u'")
    case False
    with assms have "length \<beta> \<noteq> length \<beta>'" by fastforce
    then consider "length \<beta> < length \<beta>'" | "length \<beta>' < length \<beta>" by linarith
    then show ?thesis
      using right_derivs_eq_impossible assms assms[symmetric] 
      by cases fast+
  qed (use assms neq in auto)
qed

lemma deriver_imp_in_Prods:
  assumes "P \<turnstile> \<gamma> @ Nt A#map Tm w \<Rightarrow>r \<gamma>@\<alpha>@map Tm w"
  shows "(A, \<alpha>) \<in> P"
  using deriver.cases[OF assms]
  by (metis append_eq_append_conv length_Cons list.inject right_derivs_eq_imp_eq_tl
      sym.inject(1))

lemma deriver_imp_handle:
  assumes "P \<turnstile> \<beta> @ Nt A#map Tm u \<Rightarrow>r \<gamma> @ Nt X#map Tm v"
  obtains \<alpha> where "\<beta>@\<alpha>@map Tm u = \<gamma> @ Nt X#map Tm v"
    "(A, \<alpha>) \<in> P" 
proof -
  from deriver.cases[OF assms] obtain A' \<alpha>' \<beta>' u' where
    "\<beta> @ Nt A # map Tm u = \<beta>' @ Nt A' # map Tm u'"
    "\<gamma> @ Nt X # map Tm v = \<beta>' @ \<alpha>' @ map Tm u'"
    "(A', \<alpha>') \<in> P" by metis
  with right_derivs_eq_imp_eq_tl[OF this(1)] show thesis using that by simp
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

lemma deriver_cases[consumes 1, case_names rightmost Tms_only]:
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
  then show ?case using right_derivs_eq_imp_eq_tl[OF base(1)] by blast
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
   moreover from this have "B = D" using deriv Nt right_derivs_eq_imp_eq_tl[of \<beta> B w "\<alpha> @ \<delta> @ \<eta>" D "y@u"]
     by simp
   ultimately show ?thesis using Nt that deriv by (metis append.assoc append_Cons)
  qed
qed

lemma derivern_last_step:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r(Suc n) map Tm w"
  obtains u A v where "P \<turnstile> \<alpha> \<Rightarrow>r(n) map Tm u@Nt A#map Tm v" "P \<turnstile> map Tm u@Nt A#map Tm v \<Rightarrow>r map Tm w"
  using assms proof (induction n arbitrary: \<alpha> thesis w)
  case 0
  hence "P \<turnstile> \<alpha> \<Rightarrow>r map Tm w" by auto
  then obtain x A \<beta> v where "\<alpha> = x@Nt A#map Tm v" "x@\<beta>@map Tm v = map Tm w" 
    using deriver.cases by metis
  then show ?case using 0 
    by (smt (verit, best) map_eq_append_conv relpowp_0_E relpowp_Suc_E)
next
  case (Suc n)
  from Suc(3) obtain \<beta> where "P \<turnstile> \<alpha> \<Rightarrow>r \<beta>" "P \<turnstile> \<beta> \<Rightarrow>r(Suc n) map Tm w" 
    by (metis relpowp_Suc_D2)
  then show ?case using Suc by (metis relpowp_Suc_I2)
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


lemma derive_decomp:
  assumes "P \<turnstile> \<alpha> \<Rightarrow> map Tm w"
  obtains u v X x where 
    "\<alpha> = map Tm u @ Nt X # map Tm x" "P \<turnstile> [Nt X] \<Rightarrow> map Tm v" "w = u @ v @ x"
proof -
  from assms have "P \<turnstile> \<alpha> \<Rightarrow>(Suc 0) map Tm w" by auto
  from derives_decomp_less[OF this] show thesis using that 
    by (metis (no_types, lifting) ext add_is_0 not_less_zero one_is_add relpowp_0_E
        relpowp_Suc_0) 
qed

(* If needed can be trivially extended to obtain m where 
    n = Suc m and P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w still holds *)
lemma derivern_singleton_imp_prod:
  assumes "P \<turnstile> [Nt X] \<Rightarrow>(n) map Tm w"
  obtains \<alpha> m where "P \<turnstile> [Nt X] \<Rightarrow> \<alpha>"
    "P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w" "m < n"
  using assms by (cases n) (force, metis lessI relpowp_Suc_D2)

section \<open>Others\<close>

end
