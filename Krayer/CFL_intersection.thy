(* Authors: Felix Krayer, Tobias Nipkow *)

section "CFL Not Closed Under Intersection"

theory CFL_intersection
imports
  "$AFP/List_Power/List_Power"
  "../CFL"
  "../Stimpfle/CNF"
  "../AFP/CFG_Renaming"
begin

declare count_list_pow_list[simp]

section "CFL intersection is not closed"

section "auxiliaries"

abbreviation Lang_concat :: "'t list set \<Rightarrow> 't list set \<Rightarrow> 't list set" where
  "Lang_concat L1 L2 \<equiv> {word. \<exists>w1 \<in> L1. \<exists>w2 \<in> L2. word = w1 @ w2}"

lemma deriven_same_repl:
  assumes "(A, u' @ [Nt A] @ v') \<in> P"
  shows "P \<turnstile> u @ [Nt A] @ v \<Rightarrow>(n) u @ (u'^^n) @ [Nt A] @ (v'^^n) @ v"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "P \<turnstile> u @ (u'^^n) @ [Nt A] @ (v'^^n) @ v \<Rightarrow> u @ (u'^^n) @ u' @ [Nt A] @ v' @ (v'^^n) @ v" 
    using assms derive.intros[of _ _ _ "u @ (u'^^n)" "(v'^^n) @ v"] by fastforce 
  then have "P \<turnstile> u @ (u'^^n) @ [Nt A] @ (v'^^n) @ v \<Rightarrow> u @ (u'^^(Suc n)) @ [Nt A] @ (v'^^(Suc n)) @ v"
    by (metis append.assoc pow_list_Suc2 pow_list_comm) 
  then show ?case using Suc by auto
qed

(*this is just a consequence of CFG.deriven_start1 *) 
thm CFG.deriven_start1
lemma derives_start1: 
  assumes "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
  shows "\<exists>\<alpha>. P \<turnstile> \<alpha> \<Rightarrow>* (map Tm w) \<and> (A,\<alpha>) \<in> P"
proof -
  from assms obtain n where "P \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w" using rtranclp_imp_relpowp by fast
  then obtain \<alpha> m where "n = Suc m \<and> P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w \<and> (A, \<alpha>) \<in> P" using deriven_start1 by fast
  then have "P \<turnstile> \<alpha> \<Rightarrow>* map Tm w \<and> (A, \<alpha>) \<in> P" by (auto simp add: relpowp_imp_rtranclp) 
  then show ?thesis by auto
qed  

subsection "Mapping over Nts + lemmas"

lemma notin_range_imp_notin_map:
  assumes "x \<notin> range f"
  shows "Nt x \<notin> set (rename_syms f w)"
  by (metis assms ex_map_conv rangeI rename_sym.elims sym.inject(1) sym.simps(4))


subsubsection "Equivalences after mapping a injective function over all Nts"

lemma map_derives_imp_map:
  assumes "rename_Prods f P \<turnstile> rename_syms f u \<Rightarrow>* fv"
  shows "\<exists>v. fv = rename_syms f v"
  using assms
proof(induction rule: derives_induct)
  case base
  then show ?case by auto
next
  case (step u A v w)
  then obtain A' where A'_src: "rename_syms f [Nt A'] = [Nt A]" by auto
  from step obtain drvW where "rename_syms f drvW = u @ [Nt A] @ v" by auto
  then have uAv_split: "u @ rename_syms f [Nt A'] @ v = rename_syms f drvW" using A'_src by simp
  from uAv_split obtain u' where u'_src: "rename_syms f u' = u" by (metis map_eq_append_conv)
  from uAv_split obtain v' where v'_src: "rename_syms f v' = v" by (metis map_eq_append_conv)
  from step obtain w' where "rename_syms f w' = w" by auto
  then have "u @ w @ v = rename_syms f (u' @ w' @ v')" using u'_src v'_src by auto
  then show ?case by fast
qed

section "main proof"

lemma an_CFL: "CFL TYPE('n) (\<Union>n. {[a]^^n})" (is "CFL _ ?L")
proof  -
  obtain P X where P_def: "(P::('n, 'a) Prods) = {(X, [Tm a, Nt X]), (X, [])}" by simp
  have "Lang P X = ?L" 
  proof
    show "Lang P X \<subseteq> ?L" 
    proof
      fix w
      assume "w \<in> Lang P X"
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using CFG.Lang_def by fastforce
      then have "\<exists>n. map Tm w = ([Tm a]^^n) @ [Nt X] \<or> (map Tm w::('n, 'a)syms) = ([Tm a]^^n)"
      proof(induction rule: derives_induct)
        case base
        then show ?case by (auto simp: pow_list_single_Nil_iff)
      next
        case (step u A v w')
        then have "A=X" using P_def by auto
        have "P \<turnstile> u @ [Nt X] @ v \<Rightarrow> u @ w' @ v" using \<open>A=X\<close> derive.intros step by fast
        obtain n where n_src: "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X] \<or> u @ [Nt X] @ v = ([Tm a]^^n)" 
          using \<open>A=X\<close> step by auto 
        have notin: "Nt X \<notin> set ([Tm a]^^n)" by (simp add: pow_list_single)
        then have "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X]" 
          using n_src append_Cons in_set_conv_decomp by metis
        then have uv_eq: "u = ([Tm a]^^n) \<and> v = []" 
          using notin n_src Cons_eq_appendI append_Cons_eq_iff append_Nil in_set_insert insert_Nil snoc_eq_iff_butlast by metis
        have "w' = [Tm a, Nt X] \<or> w' = []" using step(2) P_def by auto
        then show ?case
        proof
          assume "w' = [Tm a, Nt X]"
          then have "u @ w' @ v = ([Tm a]^^(Suc n)) @ [Nt X]" using uv_eq by (simp add: pow_list_comm)
          then show ?case by blast
        next
          assume "w' = []"
          then show ?case using uv_eq by blast
        qed
      qed
      then obtain n' where n'_src: "(map Tm w) = ([Tm a]^^n') @ [Nt X] \<or> ((map Tm w)::('n, 'a)syms) = ([Tm a]^^n')" by auto
      have "Nt X \<notin> set (map Tm w)" by auto
      then have "((map Tm w)::('n, 'a)syms) = ([Tm a]^^n')" using n'_src by fastforce
      have "map Tm ([a]^^n') = ([Tm a]^^n')" by (simp add: map_concat)
      then have "w = [a]^^n'" using \<open>map Tm w = ([Tm a]^^n')\<close> by (metis list.inj_map_strong sym.inject(2))
      then show "w \<in> ?L" by auto
    qed
  next
    show "?L \<subseteq> Lang P X" 
    proof
      fix w
      assume "w \<in> ?L"
      then obtain n where n_src: "w = [a]^^n" by blast
      (*"X \<Rightarrow>* a^n"*)
      have Xa: "P \<turnstile> [Nt X] \<Rightarrow>(n) ([Tm a]^^n) @ [Nt X]"
        using P_def deriven_same_repl[of "X" "[Tm a]" "[]" _ _ "[]" ] by (simp add: pow_list_Nil)
      have X\<epsilon>: "P \<turnstile> ([Tm a]^^n) @ [Nt X] \<Rightarrow> ([Tm a]^^n)" using P_def derive.intros[of "X" "[]" _ "[Tm a]^^n" "[]"] by auto
      have "([Tm a]^^n) = map Tm w" using n_src by auto
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Xa X\<epsilon> relpowp_imp_rtranclp
        by (smt (verit, best) rtranclp.simps) 
      then show "w \<in> Lang P X" using CFG.Lang_def by fastforce
    qed
  qed
  then show ?thesis unfolding CFL_def P_def by blast
qed

lemma anbn_CFL: "CFL TYPE('n) (\<Union>n. {[a]^^n @ [b]^^n})" (is "CFL _ ?L")
proof  -
  obtain P X where P_def: "(P::('n, 'a) Prods) = {(X, [Tm a, Nt X, Tm b]), (X, [])}" by simp
  let ?G = "Cfg P X"
  have "Lang P X = ?L" 
  proof
    show "Lang P X \<subseteq> ?L" proof
      fix w
      assume "w \<in> Lang P X"
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using CFG.Lang_def by fastforce
      then have "\<exists>n. map Tm w = ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n) \<or> (map Tm w::('n, 'a)syms) = ([Tm a]^^n) @ ([Tm b]^^n)"
      proof(induction rule: derives_induct)
        case base
        have "[Nt X] = ([Tm a]^^0) @ [Nt X] @ ([Tm b]^^0)" by auto
        then show ?case by fast
      next
        case (step u A v w')
        then have "A=X" using P_def by auto
        have "P \<turnstile> u @ [Nt X] @ v \<Rightarrow> u @ w' @ v" using \<open>A=X\<close> derive.intros step by fast
        obtain n where n_src: "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n) \<or> u @ [Nt X] @ v = ([Tm a]^^n) @ ([Tm b]^^n)" 
          using \<open>A=X\<close> step by auto
        have notin2: "Nt X \<notin> set ([Tm a]^^n) \<and> Nt X \<notin> set ([Tm b]^^n)"
          by (simp add: pow_list_single)
        then have notin: "Nt X \<notin> set (([Tm a]^^n) @ ([Tm b]^^n))" by simp
        then have uv_split: "u @ [Nt X] @ v = ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n)" 
          by (metis n_src append_Cons in_set_conv_decomp)
        have u_eq: "u = ([Tm a]^^n)"
          by (metis (no_types, lifting) uv_split notin2 Cons_eq_appendI append_Cons_eq_iff eq_Nil_appendI) 
        then have v_eq: "v = ([Tm b]^^n)" 
           by (metis (no_types, lifting) uv_split notin2 Cons_eq_appendI append_Cons_eq_iff eq_Nil_appendI)
        have "w' = [Tm a, Nt X, Tm b] \<or> w' = []" using step(2) P_def by auto
        then show ?case
        proof
          assume "w' = [Tm a, Nt X, Tm b]"
          then have "u @ w' @ v = ([Tm a]^^n) @ [Tm a, Nt X, Tm b] @ ([Tm b]^^n)" using u_eq v_eq by simp
          then have "u @ w' @ v = ([Tm a]^^(Suc n)) @ [Nt X] @ ([Tm b]^^(Suc n)) "
            by (simp add: pow_list_comm)
          then show ?case by blast
        next
          assume "w' = []"
          then show ?case using u_eq v_eq by blast
        qed
      qed
      then obtain n' where n'_src: "(map Tm w) = ([Tm a]^^n') @ [Nt X] @ ([Tm b]^^n') \<or> ((map Tm w)::('n, 'a)syms) = ([Tm a]^^n') @ ([Tm b]^^n')" by auto
      have "Nt X \<notin> set (map Tm w)" by auto
      then have w_ab: "((map Tm w)::('n, 'a)syms) = ([Tm a]^^n') @ ([Tm b]^^n')" using n'_src by fastforce
      have map_a: "([Tm a]^^n') = map Tm ([a]^^n')" by (simp add: map_concat)
      have map_b: "([Tm b]^^n') = map Tm ([b]^^n')" by (simp add: map_concat)
      from w_ab map_a map_b have "((map Tm w)::('n, 'a)syms) = map Tm ([a]^^n') @  map Tm ([b]^^n')" by metis
      then have "((map Tm w)::('n, 'a)syms) = map Tm (([a]^^n') @ ([b]^^n'))" by simp
      then have "w = [a]^^n' @ [b]^^n'" by (metis list.inj_map_strong sym.inject(2))
      then show "w \<in> ?L" by auto
    qed
  next
    show "?L \<subseteq> Lang P X" 
    proof
      fix w
      assume "w \<in> ?L"
      then obtain n where n_src: "w = [a]^^n @ [b]^^n" by blast
      (*"X \<Rightarrow>* a^nb^n"*)
      have Xa: "P \<turnstile> [Nt X] \<Rightarrow>(n) ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n)"
        using P_def deriven_same_repl[of "X" "[Tm a]" "[Tm b]" _ _ "[]" "[]"] by simp
      have X\<epsilon>: "P \<turnstile> ([Tm a]^^n) @ [Nt X] @ ([Tm b]^^n) \<Rightarrow> ([Tm a]^^n) @ ([Tm b]^^n)" 
        using P_def derive.intros[of "X" "[]" _ "[Tm a]^^n" "[Tm b]^^n"] by auto
      have "[Tm a]^^n @ [Tm b]^^n = map Tm ([a]^^n) @ (map Tm ([b]^^n))" by simp
      then have "([Tm a]^^n) @ ([Tm b]^^n) = map Tm w" using n_src by simp
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Xa X\<epsilon> relpowp_imp_rtranclp
        by (smt (verit, best) rtranclp.simps) 
      then show "w \<in> Lang P X" using CFG.Lang_def by fastforce
    qed
  qed
  then show ?thesis unfolding CFL_def P_def by blast
qed

lemma concat_closed: 
  assumes "CFL TYPE('n) L1"
  and "CFL TYPE('m) L2"
  and "Lconcat = {word. \<exists>w1 \<in> L1. \<exists>w2 \<in> L2. word = w1 @ w2}"
shows "CFL TYPE(('n option \<times> 'm option)) Lconcat"
proof -
  obtain P1 S1 where L1_def: "L1 = Lang P1 (S1::'n)" "finite P1"
    using assms(1) CFL_def[of L1] by auto 
  obtain P2 S2 where L2_def: "L2 = Lang P2 (S2::'m)" "finite P2"
    using assms(2) CFL_def[of L2] by auto
  let ?f1 = "(\<lambda>A. (Some A, None))"
  let ?f2 = "(\<lambda>A. (None, Some A))"
  let ?P1r = "rename_Prods ?f1 P1"
  let ?P2r = "rename_Prods ?f2 P2"
  let ?P = "{((None, None), [Nt (Some S1, None), Nt (None, Some S2)])} \<union> ?P1r \<union> ?P2r"
  let ?S = "(None, None)"
  have "inj ?f1" by (simp add: inj_on_def) 
  then have L1r_def: "L1 = Lang ?P1r (Some S1, None)" 
    using L1_def Lang_rename_Prods[of ?f1 P1] inj_on_def by blast
  have "inj ?f2" by (simp add: inj_on_def) 
  then have L2r_def: "L2 = Lang ?P2r ((None, Some S2))" 
    using L2_def Lang_rename_Prods[of ?f2 P2] inj_on_def by blast

  have "Lang ?P ?S = Lconcat"
  proof
    show "Lang ?P ?S \<subseteq> Lconcat" 
    proof
      fix w
      assume "w \<in> Lang ?P ?S"
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w" using CFG.Lang_def by fastforce
      then obtain \<alpha> where "?P \<turnstile> \<alpha> \<Rightarrow>* map Tm w \<and> ((None, None), \<alpha>) \<in> ?P" using derives_start1 by fast
      then have dervs: "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>* map Tm w" by auto
      then obtain n where "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) map Tm w" using rtranclp_imp_relpowp by fast
      then obtain Tmw where Tmw_src: "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) Tmw \<and> map Tm w = Tmw" by blast
      then have "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) Tmw" by simp
      then have "\<exists>n1 w1 n2 w2. n = n1 + n2 \<and> ?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>(n1) w1 \<and> ?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>(n2) w2 \<and> Tmw = w1@w2"
      proof(induction n arbitrary: Tmw)
        case (0 w')
        then show ?case by simp
      next
        case (Suc n w')
        then obtain im where im_src: "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) im \<and> ?P \<turnstile> im \<Rightarrow> w'" by auto
        then obtain n1 w1 n2 w2 where nw_src: "n = n1 + n2 \<and> ?P1r \<turnstile> rename_syms ?f1 [Nt S1] \<Rightarrow>(n1) w1 \<and>
           ?P2r \<turnstile> rename_syms ?f2 [Nt S2] \<Rightarrow>(n2) w2 \<and> im = w1 @ w2" using Suc by fastforce
        obtain w1o where w1o_src: "w1 = rename_syms ?f1 w1o" using nw_src map_derives_imp_map relpowp_imp_rtranclp by meson
        obtain w2o where w2o_src: "w2 = rename_syms ?f2 w2o" using nw_src map_derives_imp_map relpowp_imp_rtranclp by meson
        have "(None, None) \<notin> range ?f1 \<and> (None, None) \<notin> range ?f2" by blast
        then have "Nt (None, None) \<notin> set w1 \<and> Nt (None, None) \<notin> set w2" 
          using notin_range_imp_notin_map w1o_src w2o_src by metis
        then have notin_im: "Nt (None, None) \<notin> set im" using nw_src by simp
        have "{((None, None), [Nt (Some S1, None), Nt (None, Some S2)])} \<turnstile> im \<Rightarrow> w' \<or> ?P1r \<turnstile> im \<Rightarrow> w' \<or> ?P2r \<turnstile> im \<Rightarrow> w'"
          using Un_derive im_src by blast
        then have "?P1r \<turnstile> im \<Rightarrow> w' \<or> ?P2r \<turnstile> im \<Rightarrow> w'" using notin_im derive.cases by fastforce
        then have "?P1r \<turnstile> w1@w2 \<Rightarrow> w' \<or> ?P2r \<turnstile> w1@w2 \<Rightarrow> w'" using nw_src by fast
        then show ?case
        proof
          assume "?P1r \<turnstile> w1@w2 \<Rightarrow> w'"
          then obtain A w u1 u2 where Awu_src: "(A, w) \<in> ?P1r \<and> w1 @ w2 = u1 @ Nt A # u2 \<and> w' = u1 @ w @ u2" 
            using derive_iff[of ?P1r "w1 @ w2" w'] case_prodE by blast
          then have pre_split: "w1 @ w2 = u1 @ [Nt A] @ u2" by simp
          then have in_either: "set w1 \<union> set w2 = set (u1 @ [Nt A] @ u2)" using set_append by metis
          from Awu_src have "A \<notin> range ?f2" by auto
          then have notin_2: "Nt A \<notin> set w2" using notin_range_imp_notin_map w2o_src by fast
          then obtain Au21 where Au21_src: "[Nt A] @ u2 = Au21@w2" using pre_split
            by (smt (verit, ccfv_SIG) append_Cons append_eq_append_conv2 in_set_conv_decomp) 
          then have "hd Au21 = Nt A" using notin_2
            by (metis append_Cons hd_append list.sel(1) list.set_sel(1))
          then obtain u21 where u21_src: "u21 = tl Au21 \<and> u2 = u21@w2" using Au21_src
            by (metis Cons_eq_appendI list.sel(3) list.set_intros(1) notin_2 self_append_conv2 tl_append2)
          then have cond4: "w' = u1 @ w @ u21 @ w2" using Awu_src by simp
          have "w1 = u1 @ [Nt A] @ u21" using u21_src pre_split by simp
          then have "?P1r \<turnstile> w1 \<Rightarrow> u1 @ w @ u21" using Awu_src derive.intros by metis
          then have cond2: "?P1r \<turnstile> rename_syms ?f1 [Nt S1] \<Rightarrow>(Suc n1) u1 @ w @ u21" using nw_src by auto
          have "Suc n = Suc n1 + n2" using nw_src by simp  
          then show ?case using cond4 cond2 nw_src by fastforce
        next
          assume "?P2r \<turnstile> w1@w2 \<Rightarrow> w'"
          then obtain A w u1 u2 where Awu_src: "(A, w) \<in> ?P2r \<and> w1 @ w2 = u1 @ Nt A # u2 \<and> w' = u1 @ w @ u2" 
            using derive_iff[of ?P2r "w1@w2" w'] case_prodE by blast
          then have pre_split: "w1 @ w2 = u1 @ [Nt A] @ u2" by simp
          then have in_either: "set w1 \<union> set w2 = set (u1 @ [Nt A] @ u2)" using set_append by metis
          from Awu_src have "A \<notin> range ?f1" by auto
          then have notin_1: "Nt A \<notin> set w1" using notin_range_imp_notin_map w1o_src by fast
          then have rev_notin_1: "Nt A \<notin> set (rev w1)" by simp
          have rev_pre_split: "rev w2 @ rev w1 = rev u2 @ rev [Nt A] @ rev u1" using pre_split
            by (metis append_assoc rev_append) 
          then have rev_pre_split: "rev w2 @ rev w1 = rev u2 @ [Nt A] @ rev u1" by simp
          (*there has to be a better way than reversing the list, but otherwise this proof step does not work*)
          (*this part of the proof is wanky anyways. It feels really hard reasoning about lists when knowing that something is or is not an element of the list *)
          obtain u12Ar where u12Ar_src: "[Nt A] @ rev u1 = u12Ar @ rev w1" using rev_notin_1 rev_pre_split 
            by (smt (verit, ccfv_SIG) append_Cons append_eq_append_conv2 in_set_conv_decomp) 
          then have "hd u12Ar = Nt A" using rev_notin_1
            by (metis append_Cons hd_append list.sel(1) list.set_sel(1))
          then obtain u12r where "u12r = tl u12Ar \<and> rev u1 = u12r @ rev w1" using u12Ar_src
            by (metis Cons_eq_appendI list.sel(3) list.set_intros(1) rev_notin_1 self_append_conv2 tl_append2)
          then have u12_src: "u1 = w1 @ rev u12r"
            by (simp add: rev_eq_append_conv) 
          then have cond4: "w' = w1 @ (rev u12r) @ w @ u2" using Awu_src by simp
          have "w2 = rev u12r @ [Nt A] @ u2" using u12_src pre_split by simp
          then have "?P2r \<turnstile> w2 \<Rightarrow> rev u12r @ w @ u2" using Awu_src derive.intros by metis
          then have cond2: "?P2r \<turnstile> rename_syms ?f2 [Nt S2] \<Rightarrow>(Suc n2) rev u12r @ w @ u2" using nw_src by auto
          have "Suc n = n1 + Suc n2" using nw_src by simp  
          then show ?case using cond4 cond2 nw_src by fastforce
        qed
      qed
      then obtain n1 n2 w1 w2 where nw_src: "n = n1 + n2 \<and> ?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>(n1) w1 \<and> ?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>(n2) w2 \<and> Tmw = w1@w2" by fast
      from nw_src have "map Tm w = w1@w2" using Tmw_src by auto
      then obtain w1' w2' where w12'_src: "((map Tm w1')::('n option \<times> 'm option, 'a)syms) = w1 \<and> 
        ((map Tm w2')::('n option \<times> 'm option, 'a)syms) = w2 \<and> w1'@w2' = w"
        by (metis append_eq_map_conv) 
      from w12'_src have "?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* ((map Tm w1')::('n option \<times> 'm option, 'a)syms)" using nw_src relpowp_imp_rtranclp by fast
      then have "w1' \<in> L1" using CFG.Lang_def by (metis L1r_def mem_Collect_eq)
      from w12'_src have "?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* ((map Tm w2')::('n option \<times> 'm option, 'a)syms)" using nw_src relpowp_imp_rtranclp by fast
      then have "w2' \<in> L2" using CFG.Lang_def by (metis L2r_def mem_Collect_eq)
      show "w \<in> Lconcat" using \<open>w1' \<in> L1\<close> \<open>w2' \<in> L2\<close> w12'_src assms(3) by blast
    qed
  next
    show "Lconcat \<subseteq> Lang ?P ?S" 
    proof
      fix w
      assume "w \<in> Lconcat"
      then obtain w1 w2 where w12_src: "(w1 \<in> L1) \<and> (w2 \<in> L2) \<and> w = w1 @ w2" using assms by blast
      have P1r_sub: "?P1r \<subseteq> ?P" by auto
      from w12_src have "?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* map Tm w1" using L1r_def CFG.Lang_def by fast
      then have der_w1: "?P \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* map Tm w1" using derives_mono[OF P1r_sub] by blast
      have P2r_sub: "?P2r \<subseteq> ?P" by auto 
      from w12_src have "?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* map Tm w2" using L2r_def CFG.Lang_def by fast
      then have der_w2: "?P \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* map Tm w2" using  derives_mono[OF P2r_sub] by blast
      have "?P \<turnstile> [Nt (None, None)] \<Rightarrow> [Nt (Some S1, None), Nt (None, Some S2)]" 
        using derive.intros[of "(None, None)" "[Nt (Some S1, None), Nt (None, Some S2)]" ?P "[]"] by auto
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w1 @ [Nt (None, Some S2)]" 
        using derives_append[of ?P "[Nt (Some S1, None)]" "map Tm w1" "[Nt (None, Some S2)]"] der_w1 by simp
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w1 @ map Tm w2"
        using derives_prepend[of ?P "[Nt (None, Some S2)]" "map Tm w2" "map Tm w1"] der_w2 by simp
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w" using w12_src by simp
      then show "w \<in> Lang ?P ?S" using CFG.Lang_def by fastforce
    qed
  qed
  moreover have "finite ?P" using \<open>finite P1\<close> \<open>finite P2\<close> by auto
  ultimately show ?thesis unfolding CFL_def by blast
qed

section "formalize goal"

lemma anbncn_not_CFL: 
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"  "L = {word. \<exists>n. word = [a]^^n @ [b]^^n @ [c]^^n}"
  shows "\<not>(\<exists>P S. Lang P S = L \<and> finite P)"
  sorry
(* proven in ../Philipp/anbncn.thy*)


(*this seems very tedious and unnecessary, there is likely a better way to do this*)
lemma intersection_anbncn: 
  assumes "a\<noteq>b" 
  and "b\<noteq>c" 
  and "c\<noteq>a"
  and "(\<exists>x y z. w = [a]^^x@[b]^^y@[c]^^z \<and> x = y)"
  and "(\<exists>x y z. w = [a]^^x@[b]^^y@[c]^^z \<and> y = z)"
  shows "(\<exists>x y z. w = [a]^^x@[b]^^y@[c]^^z \<and> x = y \<and> y = z)"
proof -
  obtain x1 y1 z1 where src1: "w = [a]^^x1@[b]^^y1@[c]^^z1 \<and> x1 = y1" using assms by blast
  obtain x2 y2 z2 where src2: "w = [a]^^x2@[b]^^y2@[c]^^z2 \<and> y2 = z2" using assms by blast
  have "[a]^^x1@[b]^^y1@[c]^^z1 = [a]^^x2@[b]^^y2@[c]^^z2" using src1 src2 by simp
  have cx1: "count_list w a = x1" using src1 assms by (simp)
  have cx2: "count_list w a = x2" using src2 assms by (simp)
  from cx1 cx2 have eqx: "x1 = x2" by simp

  have cy1: "count_list w b = y1" using assms src1 by (simp)
  have cy2: "count_list w b = y2" using assms src2 by simp
  from cy1 cy2 have eqy: "y1 = y2" by simp

  have cz1: "count_list w c = z1" using assms src1 by simp
  have cz2: "count_list w c = z2" using assms src2 by simp
  from cz1 cz2 have eqz: "z1 = z2" by simp

  have "w = [a]^^x1@[b]^^y1@[c]^^z1 \<and> x1 = y1 \<and> y1 = z1" using eqx eqy eqz src1 src2 by blast
  then show ?thesis by blast
qed

lemma intersection_not_closed:
  fixes a b c :: 't
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows "\<exists>L1 L2 :: 't list set.
    CFL TYPE('a option \<times> 'a option) L1 \<and> CFL TYPE('b option \<times> 'b option) L2
 \<and> (\<nexists>(P::('x,'t)Prods) S. Lang P S = L1 \<inter> L2 \<and> finite P)"
proof -
  let ?anbn = "\<Union>n. {[a]^^n @ [b]^^n}"
  let ?cm = "\<Union>n. {[c]^^n}"
  let ?an = "\<Union>n. {[a]^^n}"
  let ?bmcm = "\<Union>n. {[b]^^n @ [c]^^n}"
  let ?anbncm = "\<Union>n. \<Union>m. {[a]^^n @ [b]^^n @ [c]^^m}"
  let ?anbmcm = "\<Union>n. \<Union>m. {[a]^^n @ [b]^^m @ [c]^^m}"
  have anbn: "CFL TYPE('a) ?anbn" by(rule anbn_CFL)
  have cm: "CFL TYPE('a) ?cm" by(rule an_CFL)
  have an: "CFL TYPE('b) ?an" by(rule an_CFL)
  have bmcm: "CFL TYPE('b) ?bmcm" by(rule anbn_CFL)
  have "?anbncm = (Lang_concat ?anbn ?cm)" by auto
  then have anbncm: "CFL TYPE('a option \<times> 'a option) ?anbncm" using anbn cm concat_closed by blast
  have "?anbmcm = (Lang_concat ?an ?bmcm)" by auto
  then have anbmcm: "CFL TYPE('b option \<times> 'b option) ?anbmcm" using an bmcm concat_closed by blast
  have "?anbncm \<inter> ?anbmcm = {word. \<exists>n. word = [a]^^n@[b]^^n@[c]^^n}" 
    using assms intersection_anbncn by fast
  then have "CFL TYPE('a option \<times> 'a option) ?anbncm \<and> 
        CFL TYPE('b option \<times> 'b option) ?anbmcm \<and> 
        (\<nexists>P::('x,'t)Prods.\<exists>S. Lang P S = ?anbncm \<inter> ?anbmcm \<and> finite P)" 
    using assms anbncn_not_CFL[of a b c, where 'b = 'x] anbncm anbmcm by auto
  then show ?thesis by auto
qed
unused_thms
end