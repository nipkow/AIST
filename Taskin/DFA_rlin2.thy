theory DFA_rlin2
imports
  Right_Linear
begin

definition nxt_rlin2 :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2 P A a = {B. (A, [Tm a, Nt B]) \<in> P}"

definition nxt_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't \<Rightarrow> 'n set" where
"nxt_rlin2_set P M a = (\<Union>A\<in>M. nxt_rlin2 P A a)"

definition nxts_rlin2_set :: "('n,'t)Prods \<Rightarrow> 'n set \<Rightarrow> 't list \<Rightarrow> 'n set" where
"nxts_rlin2_set P = foldl (nxt_rlin2_set P)"

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

lemma rlin2_nts_eq: 
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

lemma rlin2_intro_tm:
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Tm x, Nt B]"
    shows "\<exists>C. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt C] \<and> (C,[Tm x, Nt B]) \<in> P"
  sorry

lemma mult_derive_to_nxts:
  assumes "rlin2 P"
  shows "(\<exists>A\<in>M. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B]) \<Longrightarrow> B \<in> nxts_rlin2_set P M w"
unfolding nxts_rlin2_set_def using assms proof (induction w arbitrary: B rule: rev_induct)
  case Nil
  then obtain A where A_unit: "P \<turnstile> [Nt A] \<Rightarrow>* [Nt B]" and A_in: "A \<in> M" by auto
  from A_unit Nil.prems(2) have "A = B"
    using rlin2_nts_eq[of P A B] by simp
  with A_in show ?case by simp
next
  case (snoc x xs)
  from snoc.prems(1) obtain A where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm (xs @ [x]) @ [Nt B]" 
                                and A_in: "A \<in> M" by blast
  from A_der have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Tm x,Nt B]" by simp
  with snoc.prems(2) obtain C where C_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm xs @ [Nt C]"
                                and C_prods: "(C,[Tm x, Nt B]) \<in> P" using rlin2_intro_tm by fast
  from A_in C_der snoc.prems(2) have "C \<in> foldl (nxt_rlin2_set P) M xs"
    using snoc.IH[of C] by auto
  with C_prods show ?case
    unfolding nxt_rlin2_set_def nxt_rlin2_def by auto
qed

lemma rlin2_tms_eps:
  assumes "rlin2 P"
      and "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
    shows "\<exists>B. P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B] \<and> (B,[]) \<in> P"
  sorry

theorem accepted_if_Lang:
assumes "rlin2 P"
shows "w \<in> Lang P A \<Longrightarrow> A \<in> M \<Longrightarrow> \<exists>Z \<in> nxts_rlin2_set P M w. (Z,[]) \<in> P"
proof -
  assume w_lang: "w \<in> Lang P A" and A_in: "A \<in> M"
  from assms w_lang obtain B where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt B]" and B_in: "(B,[]) \<in> P" 
    unfolding Lang_def using rlin2_tms_eps by fast
  from A_in A_der have "B \<in> nxts_rlin2_set P M w" 
    using mult_derive_to_nxts[OF assms] by auto
  with B_in show ?thesis by blast
qed

theorem Lang_if_accepted: "Z \<in> nxts_rlin2_set P M w \<Longrightarrow> (Z,[]) \<in> P \<Longrightarrow> \<exists>A\<in>M. w \<in> Lang P A"
proof -
  assume Z_nxts: "Z \<in> nxts_rlin2_set P M w" and Z_eps: "(Z,[]) \<in> P"
  from Z_nxts obtain A where A_der: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w @ [Nt Z]" and A_in: "A \<in> M"
    using nxts_to_mult_derive by fast
  from Z_eps have "P \<turnstile> [Nt Z] \<Rightarrow> []" 
    using derive_singleton[of P "Nt Z" "[]"] by simp
  hence "P \<turnstile> map Tm w @ [Nt Z] \<Rightarrow> map Tm w"
    using derive_prepend[of P "[Nt Z]" "[]" "map Tm w"] by simp
  with A_der have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w" by simp
  with A_in show ?thesis 
    unfolding Lang_def by blast
qed

theorem Lang_if_accepted_if_rlin2:
assumes "rlin2 P"
shows "w \<in> Lang P A \<longleftrightarrow> (\<exists>Z \<in> nxts_rlin2_set P {A} w. (Z,[]) \<in> P)"
using accepted_if_Lang[OF assms] Lang_if_accepted
by (metis singleton_iff)

end