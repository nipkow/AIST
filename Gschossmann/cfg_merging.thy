theory cfg_merging
  imports "../CFG"
begin

(*
  This theory provides lemmas relevant when combining
  the productions of two grammars with disjoint
  sets of nonterminals.
*)




(* helper for deriven_nts_prods_subset *)
lemma derivel_nts_prods_subset:
  assumes "P \<turnstile> u \<Rightarrow>l v"
  shows "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms u"
proof
  fix x
  assume asm: "x \<in> nts_of_syms v"

  from assms obtain A w u1 u2
      where "(A,w) \<in> P"
        and u: "u = map Tm u1 @ Nt A # u2"
        and v: "v = map Tm u1 @ w @ u2"
    unfolding derivel_iff by fast

  then show "x \<in> Nts P \<union> nts_of_syms u"
  proof (cases "x \<in> nts_of_syms w")
    case True
    with \<open>(A, w) \<in> P\<close> show ?thesis unfolding Nts_def by auto
  next
    case False
    with asm v have "x \<in> nts_of_syms (map Tm u1 @ u2)"
      by simp
    with u have "x \<in> nts_of_syms u" unfolding nts_of_syms_def by simp
    then show "x \<in> Nts P \<union> nts_of_syms u" by simp
  qed
qed



(* helper for deriven_nts_prods_subset *)
lemma derive_nts_prods_subset:
  assumes "P \<turnstile> u \<Rightarrow> v"
  shows "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms u"
proof
  fix x
  assume asm: "x \<in> nts_of_syms v"

  from assms(1) obtain A w u1 u2
      where "(A,w) \<in> P"
        and u: "u = u1 @ Nt A # u2"
        and v: "v = u1 @ w @ u2"
    unfolding derive_iff by fast

  then show "x \<in> Nts P \<union> nts_of_syms u"
  proof (cases "x \<in> nts_of_syms w")
    case True
    with \<open>(A, w) \<in> P\<close> show ?thesis unfolding Nts_def by auto
  next
    case False
    with asm v have "x \<in> nts_of_syms (u1 @ u2)"
      by simp
    with u have "x \<in> nts_of_syms u" unfolding nts_of_syms_def by simp
    then show "x \<in> Nts P \<union> nts_of_syms u" by simp
  qed
qed


(* any derived word can only contain nonterminals that are part of
   either part of the grammar's nonterminals or contained in the
   word it is derived from *)
lemma deriveln_nts_prods_subset:
  assumes deriv: "P \<turnstile> u \<Rightarrow>l(n) v"
  shows "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms u"
proof -
  from assms show ?thesis
  proof (induction n arbitrary: v)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then obtain v' where parts: "P \<turnstile> u \<Rightarrow>l(n) v' \<and> P \<turnstile> v' \<Rightarrow>l v"
      by (meson relpowp_Suc_E)
    with Suc have "nts_of_syms v' \<subseteq> Nts P \<union> nts_of_syms u" by fast
    moreover from parts have "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms v'"
      using derivel_nts_prods_subset by blast
    ultimately show "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms u" by fast 
  qed
qed



(* any derived word can only contain nonterminals that are part of
   either part of the grammar's nonterminals or contained in the
   word it is derived from *)
lemma deriven_nts_prods_subset:
  assumes deriv: "P \<turnstile> u \<Rightarrow>(n) v"
  shows "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms u"
proof -
  from assms show ?thesis
  proof (induction n arbitrary: v)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then obtain v' where parts: "P \<turnstile> u \<Rightarrow>(n) v' \<and> P \<turnstile> v' \<Rightarrow> v"
      by (meson relpowp_Suc_E)
    with Suc have "nts_of_syms v' \<subseteq> Nts P \<union> nts_of_syms u" by fast
    moreover from parts have "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms v'"
      using derive_nts_prods_subset by blast
    ultimately show "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms u" by fast 
  qed
qed











(* helper for append_unreachable_productions_derivels *)
lemma append_unreachable_productions_derivel:
  assumes "old \<union> new \<turnstile> u \<Rightarrow>l v"
      and "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<inter> Lhss new = {}"
    shows "old \<turnstile> u \<Rightarrow>l v \<and> nts_of_syms v \<inter> Lhss new = {}"
proof -
  from assms(1) obtain A w u' v' where
        A_w: "(A, w)\<in>(old \<union> new)"
      and u: "u = map Tm u' @ Nt A # v'"
      and v: "v = map Tm u' @ w @ v'"
    unfolding derivel_iff by fast
  then have "(A,w) \<in> old \<or> (A,w) \<in> new" by simp
  then show ?thesis
  proof (elim disjE)
    assume "(A, w) \<in> old"
    with u v have "(A, w) \<in> old"
        and u: "u = map Tm u' @ Nt A # v'"
        and v: "v = map Tm u' @ w @ v'" by auto
    then have "old \<turnstile> u \<Rightarrow>l v" using derivel.intros by fastforce
    moreover have "nts_of_syms v \<inter> Lhss new = {}"
    proof -
      from v have "nts_of_syms v = nts_of_syms (map Tm u') \<union> nts_of_syms w \<union> nts_of_syms v'"
        unfolding nts_of_syms_def by auto
      moreover from \<open>(A, w) \<in> old\<close> have "nts_of_syms w \<subseteq> Nts old"
        unfolding nts_of_syms_def Nts_def by auto
      with assms have "nts_of_syms w \<inter> Lhss new = {}"
        by fast
      moreover from u assms have "nts_of_syms (map Tm u') \<inter> Lhss new = {}"
        by auto
      moreover from u assms have "nts_of_syms v' \<inter> Lhss new = {}"
        unfolding nts_of_syms_def by auto
      ultimately show ?thesis
        by blast
    qed
    ultimately show ?thesis by fast
  next
    assume "(A, w) \<in> new"
    with assms(3) u have "nts_of_syms (map Tm u' @ [Nt A] @ v') \<inter> Lhss new = {}" by simp
    then have "nts_of_syms [Nt A] \<inter> Lhss new = {}"
      unfolding nts_of_syms_def by auto
    then have "A \<notin> Lhss new" unfolding nts_of_syms_def by auto
    with \<open>(A, w) \<in> new\<close> have False unfolding Lhss_def by auto
    then show ?thesis by fast
  qed
qed



(* helper for append_unreachable_productions_derives *)
lemma append_unreachable_productions_derive:
  assumes "old \<union> new \<turnstile> u \<Rightarrow> v"
      and "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<inter> Lhss new = {}"
    shows "old \<turnstile> u \<Rightarrow> v \<and> nts_of_syms v \<inter> Lhss new = {}"
proof -
  from assms(1) obtain A w u' v' where
        A_w: "(A, w)\<in>(old \<union> new)"
      and u: "u = u' @ Nt A # v'"
      and v: "v = u' @ w @ v'"
    unfolding derive_iff by fast
  then have "(A,w) \<in> old \<or> (A,w) \<in> new" by simp
  then show ?thesis
  proof (elim disjE)
    assume "(A, w) \<in> old"
    with u v have "(A, w) \<in> old"
        and u: "u = u' @ Nt A # v'"
        and v: "v = u' @ w @ v'" by auto
    then have "old \<turnstile> u \<Rightarrow> v" using derive.intros by fastforce
    moreover have "nts_of_syms v \<inter> Lhss new = {}"
    proof -
      from v have "nts_of_syms v = nts_of_syms u' \<union> nts_of_syms w \<union> nts_of_syms v'"
        unfolding nts_of_syms_def by auto
      moreover from \<open>(A, w) \<in> old\<close> have "nts_of_syms w \<subseteq> Nts old"
        unfolding nts_of_syms_def Nts_def by auto
      with assms have "nts_of_syms w \<inter> Lhss new = {}"
        by fast
      moreover from u assms have "nts_of_syms u' \<inter> Lhss new = {}"
        unfolding nts_of_syms_def by auto
      moreover from u assms have "nts_of_syms v' \<inter> Lhss new = {}"
        unfolding nts_of_syms_def by auto
      ultimately show ?thesis
        by blast
    qed
    ultimately show ?thesis by fast
  next
    assume "(A, w) \<in> new"
    with assms(3) u have "nts_of_syms (u' @ [Nt A] @ v') \<inter> Lhss new = {}" by simp
    then have "nts_of_syms [Nt A] \<inter> Lhss new = {}"
      unfolding nts_of_syms_def by auto
    then have "A \<notin> Lhss new" unfolding nts_of_syms_def by auto
    with \<open>(A, w) \<in> new\<close> have False unfolding Lhss_def by auto
    then show ?thesis by fast
  qed
qed



lemma append_unreachable_productions_deriveln:
  assumes "old \<union> new \<turnstile> u \<Rightarrow>l(n) v"
      and "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<inter> Lhss new = {}"
    shows "old \<turnstile> u \<Rightarrow>l(n) v \<and> nts_of_syms v \<inter> Lhss new = {}"
proof -
  from assms show "old \<turnstile> u \<Rightarrow>l(n) v \<and> nts_of_syms v \<inter> Lhss new = {}"
  proof (induction n arbitrary: v)
    case 0
    then show ?case by simp
  next
    case (Suc n')
    then obtain v' where split: "old \<union> new \<turnstile> u \<Rightarrow>l(n') v' \<and> old \<union> new \<turnstile> v' \<Rightarrow>l v"
      by (meson relpowp_Suc_E)
    with Suc have "old \<turnstile> u \<Rightarrow>l(n') v' \<and> nts_of_syms v' \<inter> Lhss new = {}"
      by fast
    with Suc show ?case using append_unreachable_productions_derivel
      by (metis split relpowp_Suc_I)
  qed
qed


(* If two grammars with disjoint sets of nonterminals are merged, 
   then words derived in the merged grammar 
   from words which only contain nonterminals of one grammar
   can also be derived in the other grammar.
 *)
lemma append_unreachable_productions_deriven:
  assumes "old \<union> new \<turnstile> u \<Rightarrow>(n) v"
      and "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<inter> Lhss new = {}"
    shows "old \<turnstile> u \<Rightarrow>(n) v \<and> nts_of_syms v \<inter> Lhss new = {}"
proof -
  from assms show "old \<turnstile> u \<Rightarrow>(n) v \<and> nts_of_syms v \<inter> Lhss new = {}"
  proof (induction n arbitrary: v)
    case 0
    then show ?case by simp
  next
    case (Suc n')
    then obtain v' where split: "old \<union> new \<turnstile> u \<Rightarrow>(n') v' \<and> old \<union> new \<turnstile> v' \<Rightarrow> v"
      by (meson relpowp_Suc_E)
    with Suc have "old \<turnstile> u \<Rightarrow>(n') v' \<and> nts_of_syms v' \<inter> Lhss new = {}"
      by fast
    with Suc show ?case using append_unreachable_productions_derive
      by (metis split relpowp_Suc_I)
  qed
qed


lemma append_unreachable_productions_derivel_iff:
  assumes "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<subseteq> Nts old"
    shows "old \<turnstile> u \<Rightarrow>l v \<longleftrightarrow> old \<union> new \<turnstile> u \<Rightarrow>l v"
proof
  assume "old \<turnstile> u \<Rightarrow>l v"
  then show "old \<union> new \<turnstile> u \<Rightarrow>l v" by (simp add: Un_derivel)
next
  assume "old \<union> new \<turnstile> u \<Rightarrow>l v"
  with assms show "old \<turnstile> u \<Rightarrow>l v"
    using append_unreachable_productions_derivel by fast
qed

lemma append_unreachable_productions_derive_iff:
  assumes "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<subseteq> Nts old"
    shows "old \<turnstile> u \<Rightarrow> v \<longleftrightarrow> old \<union> new \<turnstile> u \<Rightarrow> v"
proof
  assume "old \<turnstile> u \<Rightarrow> v"
  then show "old \<union> new \<turnstile> u \<Rightarrow> v" by (simp add: Un_derive)
next
  assume "old \<union> new \<turnstile> u \<Rightarrow> v"
  with assms show "old \<turnstile> u \<Rightarrow> v"
    using append_unreachable_productions_derive by fast
qed


lemma append_unreachable_productions_deriveln_iff:
  assumes "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<inter> Lhss new = {}"
    shows "old \<turnstile> u \<Rightarrow>l(n) v \<longleftrightarrow> old \<union> new \<turnstile> u \<Rightarrow>l(n) v"
proof
  assume "old \<turnstile> u \<Rightarrow>l(n) v"
  then show "old \<union> new \<turnstile> u \<Rightarrow>l(n) v"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n')
    then have "\<exists>v'. old \<turnstile> u \<Rightarrow>l(n') v' \<and> old \<turnstile> v' \<Rightarrow>l v"
      by (meson relpowp_Suc_E)
    then show ?case using Un_derivel
      by (metis Suc.prems relpowp_mono)
  qed
next
  assume "old \<union> new \<turnstile> u \<Rightarrow>l(n) v"
  then show "old \<turnstile> u \<Rightarrow>l(n) v"
    using assms by (simp only: append_unreachable_productions_deriveln)
qed


lemma append_unreachable_productions_deriven_iff:
  assumes "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<inter> Lhss new = {}"
    shows "old \<turnstile> u \<Rightarrow>(n) v \<longleftrightarrow> old \<union> new \<turnstile> u \<Rightarrow>(n) v"
proof
  assume "old \<turnstile> u \<Rightarrow>(n) v"
  then show "old \<union> new \<turnstile> u \<Rightarrow>(n) v"
  proof (induction n)
    case 0
    then show ?case by simp
  next
    case (Suc n')
    then have "\<exists>v'. old \<turnstile> u \<Rightarrow>(n') v' \<and> old \<turnstile> v' \<Rightarrow> v"
      by (meson relpowp_Suc_E)
    then show ?case using Un_derive
      by (metis Suc.prems relpowp_mono)
  qed
next
  assume "old \<union> new \<turnstile> u \<Rightarrow>(n) v"
  then show "old \<turnstile> u \<Rightarrow>(n) v"
    using assms by (simp only: append_unreachable_productions_deriven)
qed




(* If two grammars with disjoint sets of nonterminals are merged, 
   then the language described by that grammar is that of the
   grammar which contains the start symbol.
 *)
lemma append_unreachable_productions_L:
  assumes "Nts old \<inter> Lhss new = {}"
  and "S \<notin> Lhss new"
shows "Lang old S = Lang (old \<union> new) S"
proof (cases "S \<in> Lhss old")
  case True
  with assms have "S \<notin> Lhss new" by fast

  then have "nts_of_syms [Nt S] \<inter> Lhss new = {}" unfolding nts_of_syms_def Lhss_def
    by simp
  from assms(1) this have "\<And>n v. (old \<turnstile> [Nt S] \<Rightarrow>(n) v) = (old \<union> new \<turnstile> [Nt S] \<Rightarrow>(n) v)"
    by (rule append_unreachable_productions_deriven_iff)
  then show ?thesis unfolding Lang_def
    by (simp add: rtranclp_power)
next
  case False
  then have "Lang old S = {}"
    by (simp add: Lang_empty_if_notin_Lhss)
  moreover from False assms(2) have "S \<notin> Lhss (old \<union> new)" unfolding Lhss_def by auto
  then have "Lang (old \<union> new) S = {}"
    by (simp add: Lang_empty_if_notin_Lhss) 
  ultimately show ?thesis by fast
qed


end