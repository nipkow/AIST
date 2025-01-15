theory DFA_rlin2
imports
  Right_Linear "$AFP/Regular-Sets/Regular_Set"
begin

definition nxt_rlin2 :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2 P A a = {B. (A, [Tm a, Nt B]) \<in> P}"

definition nxt_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2_set P M a = (\<Union>A\<in>M. nxt_rlin2 P A a)"

definition nxts_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't list \<Rightarrow> 'n set" where
"nxts_rlin2_set P = foldl (nxt_rlin2_set P)"

lemma map_Tm_single_nt:
  assumes "map Tm w @ [Tm a, Nt A] = u1 @ [Nt B] @ u2"
  shows "u1 = map Tm (w @ [a]) \<and> u2 = []"
proof -
  from assms have *: "map Tm (w @ [a]) @ [Nt A] = u1 @ [Nt B] @ u2" by simp
  have 1: "Nt B \<notin> set (map Tm (w @ [a]))" by auto
  have 2: "Nt B \<in> set (u1 @ [Nt B] @ u2)" by simp
  from * 1 2 have "Nt B \<in> set ([Nt A])"
    by (metis list.set_intros(1) rotate1.simps(2) set_ConsD set_rotate1 sym.inject(1))
  hence "[Nt B] = [Nt A]" by simp
  with 1 * show ?thesis
    by (metis append_Cons append_Cons_eq_iff append_self_conv emptyE empty_set)
qed

lemma nxts_to_mult_derive:
  "B \<in> nxts_rlin2_set P M w \<Longrightarrow> (\<exists>A\<in>M. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B])"
unfolding nxts_rlin2_set_def proof (induction w arbitrary: B rule: rev_induct)
  case Nil
  hence 1: "B \<in> M" by simp
  have 2: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm [] @ [Nt B]" by simp
  from 1 2 show ?case by blast
next
  case (snoc x xs)
  from snoc.prems have "\<exists>C. C \<in> foldl (nxt_rlin2_set P) M xs \<and> (C, [Tm x, Nt B]) \<in> P"
    unfolding nxt_rlin2_set_def nxt_rlin2_def by auto
  then obtain C where C_xs: "C \<in> foldl (nxt_rlin2_set P) M xs" and C_prod: "(C, [Tm x, Nt B]) \<in> P" by blast
  from C_xs obtain A where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Nt C]" and A_in: "A \<in> M" 
    using snoc.IH[of C] by auto
  from C_prod have "P \<turnstile> [Nt C] \<Rightarrow> [Tm x, Nt B]"
    using derive_singleton[of P "Nt C" "[Tm x, Nt B]"] by blast
  hence "P \<turnstile> map Tm xs @ [Nt C] \<Rightarrow> map Tm xs @ [Tm x, Nt B]"
    using derive_prepend[of P "[Nt C]" "[Tm x, Nt B]" "map Tm xs"] by simp
  hence C_der: "P \<turnstile> map Tm xs @ [Nt C] \<Rightarrow> map Tm (xs @ [x]) @ [Nt B]" by simp
  from A_der C_der have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm (xs @ [x]) @ [Nt B]" by simp
  with A_in show ?case by blast
qed

lemma rlin2_derive:
  assumes "P \<turnstile> v1 \<Rightarrow>* v2" 
      and "v1 = [Nt A]"
      and "v2 = u1 @ [Nt B] @ u2" 
      and "rlin2 P"
    shows "\<exists>w. u1 = map Tm w \<and> u2 = []"
using assms proof (induction arbitrary: u1 B u2 rule: rtrancl_derive_induct)
  case base
  then show ?case
    by (simp add: append_eq_Cons_conv)
next
  case (step u C v w)
  from step.prems(1) step.prems(3) have "\<exists>w. u = map Tm w \<and> v = []" 
    using step.IH[of u C v] by simp
  then obtain wh where u_def: "u = map Tm wh" by blast
  have v_eps: "v = []"
    using \<open>\<exists>w. u = map Tm w \<and> v = []\<close> by simp
  from step.hyps(2) step.prems(3) have w_cases: "w = [] \<or> (\<exists>d D. w = [Tm d, Nt D])"
    unfolding rlin2_def by auto
  then show ?case proof cases
    assume "w=[]"
    with v_eps step.prems(2) have "u = u1 @ [Nt B] @ u2" by simp
    with u_def show ?thesis by simp (metis ex_map_conv in_set_conv_decomp sym.distinct(1))
  next
    assume "\<not>w=[]"
    then obtain d D where "w = [Tm d, Nt D]" 
      using w_cases by blast
    with u_def v_eps step.prems(2) have "u1 = map Tm (wh @ [d]) \<and> u2 = []"
      using map_Tm_single_nt[of wh d D u1 B u2] by simp
    thus ?thesis by blast
  qed
qed

lemma rlin2_introduce_tm:
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Tm x, Nt B]"
    shows "\<exists>C. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt C] \<and> (C,[Tm x, Nt B]) \<in> P"
proof -
  from assms(2) have "\<exists>v. P \<turnstile> [Nt A] \<Rightarrow>* v \<and> P \<turnstile> v \<Rightarrow> map Tm w @ [Tm x, Nt B]"
    using rtranclp.cases by fastforce
  then obtain v where v_star: "P \<turnstile> [Nt A] \<Rightarrow>* v" and v_step: "P \<turnstile> v \<Rightarrow> map Tm w @ [Tm x, Nt B]" by blast
  from v_step have "\<exists>u1 u2 C \<alpha>. v = u1 @ [Nt C] @ u2 \<and> map Tm w @ [Tm x, Nt B] = u1 @ \<alpha> @ u2 \<and> (C,\<alpha>) \<in> P"
    using derive.cases by fastforce
  then obtain u1 u2 C \<alpha> where v_def: "v = u1 @ [Nt C] @ u2" and w_def: "map Tm w @ [Tm x, Nt B] = u1 @ \<alpha> @ u2" 
                          and C_prod: "(C,\<alpha>) \<in> P" by blast
  from assms(1) v_star v_def have u2_eps: "u2 = []"
    using rlin2_derive[of P "[Nt A]"] by simp
  from assms(1) v_star v_def obtain wa where u1_def: "u1 = map Tm wa"
    using rlin2_derive[of P "[Nt A]" "u1 @ [Nt C] @ u2" A u1] by auto
  from w_def u2_eps u1_def have "map Tm w @ [Tm x, Nt B] = map Tm wa @ \<alpha>" by simp
  then have "map Tm (w @ [x]) @ [Nt B] = map Tm wa @ \<alpha>" by simp
  then have "\<alpha> \<noteq> []" 
    by (metis append.assoc append.right_neutral list.distinct(1) map_Tm_single_nt)
  with assms(1) C_prod obtain d D where "\<alpha> = [Tm d, Nt D]"
    using rlin2_def by fastforce
  from w_def u2_eps have x_d: "x = d" 
    using \<open>\<alpha> = [Tm d, Nt D]\<close> by simp
  from w_def u2_eps have B_D: "B = D"
    using \<open>\<alpha> = [Tm d, Nt D]\<close> by simp
  from x_d B_D have alpha_def: "\<alpha> = [Tm x, Nt B]"
    using \<open>\<alpha> = [Tm d, Nt D]\<close> by simp
  from w_def u2_eps alpha_def have "map Tm w = u1" by simp
  with u1_def have w_eq_wa: "w = wa"
    by (metis list.inj_map_strong sym.inject(2))
  from v_def u1_def w_eq_wa u2_eps have "v = map Tm w @ [Nt C]" by simp
  with v_star have 1: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt C]" by simp
  from C_prod alpha_def have 2: "(C,[Tm x, Nt B]) \<in> P" by simp
  from 1 2 show ?thesis by auto
qed

lemma rlin2_nts_derive_eq: 
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]"
    shows "A = B"
proof -
  from assms(2) have star_cases: "[Nt A] = [Nt B] \<or> (\<exists>w. P \<turnstile> [Nt A] \<Rightarrow> w \<and> P \<turnstile> w \<Rightarrow>* [Nt B])"
    using converse_rtranclpE by force
  show ?thesis proof cases
    assume "\<not>[Nt A] = [Nt B]"
    then obtain w where w_step: "P \<turnstile> [Nt A] \<Rightarrow> w" and w_star: "P \<turnstile> w \<Rightarrow>* [Nt B]"
      using star_cases by auto
    from assms(1) w_step have w_cases: "w = [] \<or> (\<exists>a C. w = [Tm a, Nt C])"
      unfolding rlin2_def using derive_singleton[of P "Nt A" w] by auto
    show ?thesis proof cases
      assume "w = []"
      with w_star show ?thesis by simp
    next
      assume "\<not>w = []"
      with w_cases obtain a C where "w = [Tm a, Nt C]" by blast
      with w_star show ?thesis
        using derives_T_Cons[of P a "[Nt C]" "[Nt B]"] by simp
    qed
  qed simp
qed

lemma mult_derive_to_nxts:
  assumes "rlin2 P"
  shows "(\<exists>A\<in>M. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B]) \<Longrightarrow> B \<in> nxts_rlin2_set P M w"
unfolding nxts_rlin2_set_def using assms proof (induction w arbitrary: B rule: rev_induct)
  case Nil
  then obtain A where A_unit: "P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]" and A_in: "A \<in> M" by auto
  from A_unit Nil.prems(2) have "A = B"
    using rlin2_nts_derive_eq[of P A B] by simp
  with A_in show ?case by simp
next
  case (snoc x xs)
  from snoc.prems(1) obtain A where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm (xs @ [x]) @ [Nt B]" 
                                and A_in: "A \<in> M" by blast
  from A_der have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Tm x,Nt B]" by simp
  with snoc.prems(2) obtain C where C_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Nt C]"
                                and C_prods: "(C,[Tm x, Nt B]) \<in> P" using rlin2_introduce_tm[of P A xs x B] by fast
  from A_in C_der snoc.prems(2) have "C \<in> foldl (nxt_rlin2_set P) M xs"
    using snoc.IH[of C] by auto
  with C_prods show ?case
    unfolding nxt_rlin2_set_def nxt_rlin2_def by auto
qed

lemma rlin2_tms_eps:
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
    shows "\<exists>B. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B] \<and> (B,[]) \<in> P"
proof -
  from assms(2) have "\<exists>v. P \<turnstile> [Nt A] \<Rightarrow>* v \<and> P \<turnstile> v \<Rightarrow> map Tm w"
    using rtranclp.cases by force
  then obtain v where v_star: "P \<turnstile> [Nt A] \<Rightarrow>* v" and v_step: "P \<turnstile> v \<Rightarrow> map Tm w" by blast
  from v_step have "\<exists>u1 u2 C \<alpha>. v = u1 @ [Nt C] @ u2 \<and> map Tm w = u1 @ \<alpha> @ u2 \<and> (C,\<alpha>) \<in> P"
    using derive.cases by fastforce
  then obtain u1 u2 C \<alpha> where v_def: "v = u1 @ [Nt C] @ u2" and w_def: "map Tm w = u1 @ \<alpha> @ u2" and C_prod: "(C,\<alpha>) \<in> P" by blast
  have "\<nexists>A. Nt A \<in> set (map Tm w)" by auto
  with w_def have "\<nexists>A. Nt A \<in> set \<alpha>" 
    by (metis Un_iff set_append)
  then have "\<nexists>a A. \<alpha> = [Tm a, Nt A]" by auto
  with assms(1) C_prod have alpha_eps: "\<alpha> = []"
    using rlin2_def by force
  from v_star assms(1) v_def have u2_eps: "u2 = []"
    using rlin2_derive[of P "[Nt A]"] by simp
  from w_def alpha_eps u2_eps have u1_def: "u1 = map Tm w" by simp
  from v_star v_def u1_def u2_eps have 1: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt C]" by simp
  from alpha_eps C_prod have 2: "(C,[]) \<in> P"  by simp
  from 1 2 show ?thesis by auto
qed

definition "accepted P A w = (\<exists>Z \<in> nxts_rlin2_set P {A} w. (Z,[]) \<in> P)"

theorem accepted_if_Lang:
  assumes "rlin2 P"
      and "w \<in> Lang P A"
    shows "accepted P A w"
proof -
  from assms obtain B where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B]" and B_in: "(B,[]) \<in> P" 
    unfolding Lang_def using rlin2_tms_eps[of P A w] by auto
  from A_der have "B \<in> nxts_rlin2_set P {A} w" 
    using mult_derive_to_nxts[OF assms(1)] by auto
  with B_in show ?thesis 
    unfolding accepted_def by blast
qed

theorem Lang_if_accepted: 
  assumes "accepted P A w"
    shows "w \<in> Lang P A"
proof -
  from assms obtain Z where Z_nxts: "Z \<in> nxts_rlin2_set P {A} w" and Z_eps: "(Z,[]) \<in> P"
    unfolding accepted_def by blast
  from Z_nxts obtain B where B_der: "P \<turnstile> [Nt B] \<Rightarrow>* map Tm w @ [Nt Z]" and B_in: "B \<in> {A}"
    using nxts_to_mult_derive by fast
  from B_in have A_eq_B: "A = B" by simp
  from Z_eps have "P \<turnstile> [Nt Z] \<Rightarrow> []" 
    using derive_singleton[of P "Nt Z" "[]"] by simp
  hence "P \<turnstile> map Tm w @ [Nt Z] \<Rightarrow> map Tm w"
    using derive_prepend[of P "[Nt Z]" "[]" "map Tm w"] by simp
  with B_der A_eq_B have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w" by simp
  thus ?thesis 
    unfolding Lang_def by blast
qed

theorem Lang_iff_accepted_if_rlin2:
assumes "rlin2 P"
shows "w \<in> Lang P A \<longleftrightarrow> accepted P A w"
  using accepted_if_Lang[OF assms] Lang_if_accepted by fast

end