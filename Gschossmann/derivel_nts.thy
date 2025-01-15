theory derivel_nts
  imports "../Stimpfle/CNF" util "../Taskin/detProds" cfg_util
begin


(*
  Some lemmas about the connection between left derivations and nonterminals
 *)


definition "left_tms_then_nts ss \<equiv> \<exists>tms nts. ss = map Tm tms @ map Nt nts"
definition "num_tms ss \<equiv> length (filter (\<lambda>s. \<exists>t. s = Tm t) ss)"


(* A single leftmost derivation in a CNF grammar starting at a sequence of 
   terminals followed by nonterminals can only generate a sequence of terminals
   followed by a sequence of nonterminals
 *)
lemma CNF_derivl_tms_nts:
  assumes derivl: "P \<turnstile> u \<Rightarrow>l v"
  and cnf: "CNF P"
  and invariant: "left_tms_then_nts u"
  shows "left_tms_then_nts v"
proof -
  from derivl obtain A w u1 u2
    where in_P: "(A,w) \<in> P"
      and u: "u = map Tm u1 @ Nt A # u2"
      and v: "v = map Tm u1 @ w @ u2"
    by (auto simp add: derivel_iff)

  from invariant obtain utms unts where usplit: "u = map Tm utms @ map Nt unts"
    unfolding left_tms_then_nts_def by auto

  from usplit u have "map Tm u1 @ Nt A # u2 = map Tm utms @ map Nt unts" by simp
  moreover have "Nt A \<notin> set (map Tm utms)"
    by force
  ultimately have "Nt A # u2 = map Nt unts" using append_sets_disjoint_middle
    by (smt (verit, best) disjoint_iff_not_equal if_set_map sym.distinct(1))
  then obtain u2nts where u2nts: "map Nt u2nts = u2"
    by blast

  from cnf in_P have "(\<exists>B C. w = [Nt B, Nt C]) \<or> (\<exists>t. w = [Tm t])" unfolding CNF_def by auto
  then show ?thesis
  proof (elim disjE)
    assume "\<exists>B C. w = [Nt B, Nt C]"
    then obtain B C where " w = [Nt B, Nt C]" by blast
    with v u2nts have "v = map Tm u1 @ [Nt B, Nt C] @ map Nt u2nts" by auto
    then have "v = map Tm u1 @ map Nt ([B, C] @ u2nts)" by auto
    then show ?thesis unfolding left_tms_then_nts_def by blast
  next
    assume "\<exists>t. w = [Tm t]"
    then obtain t where "w = [Tm t]" by blast
    with v u2nts have "v = map Tm u1 @ [Tm t] @ map Nt u2nts" by auto
    then have "v = map Tm (u1 @ [t]) @ map Nt u2nts" by auto
    then show ?thesis unfolding left_tms_then_nts_def by blast
  qed
qed


(* Helper for CNF_derivls_tms_nts *)
lemma CNF_derivln_tms_nts:
  assumes derivln: "P \<turnstile> u \<Rightarrow>l(n) v"
  and cnf: "CNF P"
  and invariant: "left_tms_then_nts u"
  shows "left_tms_then_nts v"
proof -
  from derivln have "left_tms_then_nts u \<Longrightarrow> left_tms_then_nts v"
  proof (induction n arbitrary: u v)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then obtain y where uy: "P \<turnstile> u \<Rightarrow>l y" and yv: "P \<turnstile> y \<Rightarrow>l(n) v"
      by (metis relpowp_Suc_D2)
    with Suc show ?case using CNF_derivl_tms_nts cnf by blast
  qed
  with invariant show ?thesis by simp
qed


(* A leftmost derivation in a CNF grammar starting at a sequence of 
   terminals followed by nonterminals can only generate a sequence of terminals
   followed by a sequence of nonterminals
 *)
lemma CNF_derivls_tms_nts:
  assumes derivls: "ps \<turnstile> u \<Rightarrow>l* v"
  and cnf: "CNF ps"
  and invariant: "left_tms_then_nts u"
  shows "left_tms_then_nts v"
proof -
  from derivls obtain n where "ps \<turnstile> u \<Rightarrow>l(n) v"
    using rtranclp_imp_relpowp by fast
  from this cnf invariant show "left_tms_then_nts v" by (rule CNF_derivln_tms_nts)
qed

(* In each single leftmost derivation in a CNF grammar either none or one nonterminal is added *)
lemma CNF_deriv_tms_nts_mono:
  assumes deriv: "P \<turnstile> u \<Rightarrow> v"
  and cnf: "CNF P"
  shows "num_tms v = num_tms u \<or> num_tms v = Suc (num_tms u)"
proof -
  from deriv obtain A w u1 u2
    where in_P: "(A,w) \<in> P"
      and u: "u = u1 @ Nt A # u2"
      and v: "v = u1 @ w @ u2"
    by (smt (verit, ccfv_threshold) append_Cons append_Nil derive.cases)
    
  from u have num_tms_u: "num_tms u = num_tms u1 + num_tms u2" unfolding num_tms_def by auto
  from v have num_tms_v: "num_tms v = num_tms u1 + num_tms w + num_tms u2" unfolding num_tms_def by auto

  from cnf in_P have "(\<exists>B C. w = [Nt B, Nt C]) \<or> (\<exists>t. w = [Tm t])" unfolding CNF_def by auto
  then show ?thesis
  proof (elim disjE)
    assume "\<exists>B C. w = [Nt B, Nt C]"
    then obtain B C where "w = [Nt B, Nt C]" by blast
    then have "num_tms w = 0" unfolding num_tms_def by auto
    with num_tms_u num_tms_v have "num_tms v = num_tms u" by auto
    then show ?thesis by simp
  next
    assume "\<exists>t. w = [Tm t]"
    then obtain t where "w = [Tm t]" by blast
    then have "num_tms w = 1" unfolding num_tms_def by auto
    with num_tms_u num_tms_v have "num_tms v = Suc (num_tms u)" by auto
    then show ?thesis by simp
  qed
qed


(* For each leftmost derivation in a CNF grammar starting at a sequence of nonterminals
   which results in a (nonempty) sequence of terminals,
   there is a first step which introduces the leftmost terminal.
 *)
lemma CNF_derivln_first_tm:
  assumes derivln: "P \<turnstile> map Nt u \<Rightarrow>l(n) Tm t # v"
  and cnf: "CNF P"
shows "\<exists>ns. P \<turnstile> map Nt u \<Rightarrow>l* Tm t # map Nt ns  \<and>  P \<turnstile> Tm t # map Nt ns \<Rightarrow>l* Tm t # v" (is ?P)
proof -
  from derivln show "?P"
  proof (induction n arbitrary: u v)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then obtain y where uy: "P \<turnstile> map Nt u \<Rightarrow>l y" and yv: "P \<turnstile> y \<Rightarrow>l(n) Tm t # v"
      by (metis relpowp_Suc_D2)

    from uy have "P \<turnstile> map Nt u \<Rightarrow> y" by (rule derivel_imp_derive)
    from this cnf have "num_tms y = num_tms (map Nt u) \<or> num_tms y = Suc (num_tms (map Nt u))"
      using CNF_deriv_tms_nts_mono[where P=P and u="map Nt u" and v=y]
      by (simp add: num_tms_def)

    moreover have "num_tms (map Nt u) = 0" unfolding num_tms_def by simp
    ultimately have num_tms_variants: "num_tms y = 0 \<or> num_tms y = Suc 0"
      by metis

    have "left_tms_then_nts (map Nt u)" unfolding left_tms_then_nts_def by auto
    with uy cnf thm CNF_derivls_tms_nts have "left_tms_then_nts y" using CNF_derivls_tms_nts by auto
    then obtain tms nts where tms_nts: "y = map Tm tms @ map Nt nts" unfolding left_tms_then_nts_def by blast
    then have num_tms_y: "num_tms y = length tms" unfolding num_tms_def by auto

    from num_tms_variants show ?case
    proof (elim disjE)
      assume "num_tms y = 0"
      with num_tms_y have "length tms = 0" by simp
      with tms_nts have y_nts: "y = map Nt nts" by auto
      with yv have "P \<turnstile> map Nt nts \<Rightarrow>l(n) Tm t # v" by simp
      with Suc(1) obtain nts' where "P \<turnstile> map Nt nts \<Rightarrow>l* Tm t # map Nt nts' \<and> P \<turnstile> Tm t # map Nt nts' \<Rightarrow>l* Tm t # v"
        by blast
      with uy have "P \<turnstile> map Nt u \<Rightarrow>l* Tm t # map Nt nts' \<and> P \<turnstile> Tm t # map Nt nts' \<Rightarrow>l* Tm t # v"
        using y_nts by force
      then show "\<exists>ns. P \<turnstile> map Nt u \<Rightarrow>l* Tm t # map Nt ns \<and> P \<turnstile> Tm t # map Nt ns \<Rightarrow>l* Tm t # v" by auto
    next
      assume "num_tms y = Suc 0"
      with num_tms_y have "length tms = Suc 0" by simp
      then have "\<exists>t'. tms = [t']"
        by (simp add: length_Suc_conv) 
      then obtain t' where "map Tm tms = [Tm t']" by auto
      with tms_nts have y_nts: "y = Tm t' # map Nt nts" by auto

      have t_t: "t' = t"
        by (metis deriveln_Tm_Cons list.inject sym.inject(2) y_nts yv)

      from uy y_nts t_t have "P \<turnstile> map Nt u \<Rightarrow>l Tm t # map Nt nts" by auto
      then have "P \<turnstile> map Nt u \<Rightarrow>l* Tm t # map Nt nts" by auto
      moreover
      from yv y_nts t_t have "P \<turnstile> Tm t # map Nt nts \<Rightarrow>l(n) Tm t # v" by auto
      then have "P \<turnstile> Tm t # map Nt nts \<Rightarrow>l* Tm t # v"
        by (simp add: relpowp_imp_rtranclp) 
      ultimately show "\<exists>ns. P \<turnstile> map Nt u \<Rightarrow>l* Tm t # map Nt ns \<and> P \<turnstile> Tm t # map Nt ns \<Rightarrow>l* Tm t # v"
        by auto
    qed
  qed
qed

(* stronger version of derivel_iff for derivations starting from nonterminals *)
lemma derivel_iff_map_Nt: "R \<turnstile> map Nt u \<Rightarrow>l v \<longleftrightarrow>
 (\<exists> (A,w) \<in> R. \<exists>u1 u2. map Nt u = Nt A # map Nt u2 \<and> v = w @ map Nt u2)"
proof -
  have "R \<turnstile> map Nt u \<Rightarrow>l v \<longleftrightarrow> (\<exists> (A,w) \<in> R. \<exists>u1 u2. map Nt u = map Tm u1 @ Nt A # u2 \<and> v = map Tm u1 @ w @ u2)"
    by (rule derivel_iff)
  moreover have "(\<exists> (A,w) \<in> R. \<exists>u1 u2. map Nt u = map Tm u1 @ Nt A # u2 \<and> v = map Tm u1 @ w @ u2) \<longleftrightarrow>
                 (\<exists> (A,w) \<in> R. \<exists>u2. map Nt u = Nt A # u2 \<and> v = w @ u2)"
  proof
    assume "(\<exists> (A,w) \<in> R. \<exists>u1 u2. map Nt u = map Tm u1 @ Nt A # u2 \<and> v = map Tm u1 @ w @ u2)"
    then obtain A w u1 u2 where
        "(A,w) \<in> R" 
        "map Nt u = map Tm u1 @ Nt A # u2"
        "v = map Tm u1 @ w @ u2"
      by fast
    moreover from this have "u1 = []"
      by (metis Nil_is_map_conv append_is_Nil_conv hd_append2 hd_map sym.simps(4))
    ultimately show "(\<exists> (A,w) \<in> R. \<exists>u2. map Nt u = Nt A # u2 \<and> v = w @ u2)" by auto
  next
    assume "(\<exists> (A,w) \<in> R. \<exists>u2. map Nt u = Nt A # u2 \<and> v = w @ u2)"
    then have "(\<exists> (A,w) \<in> R. \<exists>u2. map Nt u = map Tm [] @ Nt A # u2 \<and> v = map Tm [] @ w @ u2)" by auto
    then show "(\<exists> (A,w) \<in> R. \<exists>u1 u2. map Nt u = map Tm u1 @ Nt A # u2 \<and> v = map Tm u1 @ w @ u2)" by blast
  qed

  moreover have "(\<exists> (A,w) \<in> R. \<exists>u2. map Nt u = Nt A # u2 \<and> v = w @ u2) \<longleftrightarrow>
                 (\<exists> (A,w) \<in> R. \<exists>u2. map Nt u = Nt A # map Nt u2 \<and> v = w @ map Nt u2)" (is "?l \<longleftrightarrow> ?r")
  proof
    assume "?l"
    then obtain A w u2 where
        "(A,w) \<in> R" 
        "map Nt u = Nt A # u2"
        "v = w @ u2"
      by force
    moreover from this have "\<exists>u2'. u2 = map Nt u2'"
      by blast
    ultimately show "?r"
      by fastforce
  next
    assume "?r"
    then show "?l"
      by (smt (verit, best) case_prodE list.inj_map_strong list.simps(9) old.prod.case slemma4_2_0)
  qed
  ultimately show ?thesis by auto
qed

(* like CNF_derivln_first_tm, but also yields the situation directly before first step
   and the lengths of the derivation fragments
 *)
lemma CNF_derivln_first_tm_strong:
  assumes derivln: "P \<turnstile> map Nt u \<Rightarrow>l(n) Tm t # v"
  and cnf: "CNF P"
shows "\<exists>T ns n1 n2. P \<turnstile> map Nt u \<Rightarrow>l(n1) Nt T # map Nt ns \<and>
                    P \<turnstile> Nt T # map Nt ns \<Rightarrow>l Tm t # map Nt ns \<and>
                    P \<turnstile> Tm t # map Nt ns \<Rightarrow>l(n2) Tm t # v \<and>
                    n1 + 1 + n2 = n" (is ?P)
proof -
  from derivln show "?P"
  proof (induction n arbitrary: u v rule: nat_induct_with_1)
    case 0
    then show ?case by auto
  next
    case 1
    then have "P \<turnstile> map Nt u \<Rightarrow>l Tm t # v" by auto
    then have "\<exists>(A, w)\<in>P. \<exists>u2. map Nt u = Nt A # map Nt u2 \<and> Tm t # v = w @ map Nt u2"
    using derivel_iff_map_Nt[where R=P and u="u" and v="Tm t # v"] by auto
    then obtain A w u2 where
        "(A, w)\<in>P" and
        "map Nt u = Nt A # map Nt u2" and
        v: "Tm t # v = w @ map Nt u2"
      by force

    then have u: "map Nt u = Nt A # map Nt u2" (* ? ? *)
      by (smt (verit, ccfv_threshold) \<open>\<And>thesis. (\<And>A w u2. \<lbrakk>(A, w) \<in> P; map Nt u = Nt A # map Nt u2; Tm t # v = w @ map Nt u2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> list.inj_map_strong list.simps(1) map_eq_Cons_D sym.inject(1)) 

    from \<open>(A, w)\<in>P\<close> cnf have "(\<exists>B C. w = [Nt B, Nt C]) \<or> (\<exists>t. w = [Tm t])" unfolding CNF_def by auto
    then show ?case
    proof (elim disjE)
      assume "\<exists>B C. w = [Nt B, Nt C]"
      then obtain B C where "w = [Nt B, Nt C]" by fast
      with \<open>Tm t # v = w @ map Nt u2\<close> have False by simp
      then show ?thesis by fast
    next
      assume "\<exists>t. w = [Tm t]"
      then obtain t' where "w = [Tm t']" by fast
      with v have w: "w = [Tm t]" by auto

      from 1 have "P \<turnstile> map Nt u \<Rightarrow>l Tm t # v" by auto
      with u have "P \<turnstile> map Nt u \<Rightarrow>l(0) Nt A # map Nt u2" by simp

      moreover from v w have "v = map Nt u2" by simp
      with 1 have "P \<turnstile> map Nt u \<Rightarrow>l(1) Tm t # map Nt u2" by auto
      with u have "P \<turnstile> Nt A # map Nt u2 \<Rightarrow>l(1) Tm t # map Nt u2"
        by metis
      then have "P \<turnstile> Nt A # map Nt u2 \<Rightarrow>l Tm t # map Nt u2" by auto

      moreover from v w have "P \<turnstile> Tm t # map Nt u2 \<Rightarrow>l(0) Tm t # v" by auto

      ultimately have
        "P \<turnstile> map Nt u \<Rightarrow>l(0) Nt A # map Nt u2"
        "P \<turnstile> Nt A # map Nt u2 \<Rightarrow>l Tm t # map Nt u2"
        "P \<turnstile> Tm t # map Nt u2 \<Rightarrow>l(0) Tm t # v"
        "(0::nat) + 1 + 0 = 1" by auto

      then show ?thesis
        by blast
    qed
  next
    case (Suc m)
    with Suc obtain y where uy: "P \<turnstile> map Nt u \<Rightarrow>l y" and yv: "P \<turnstile> y \<Rightarrow>l(m) Tm t # v"
      by (metis relpowp_Suc_D2)

    from uy have "P \<turnstile> map Nt u \<Rightarrow> y" by (rule derivel_imp_derive)
    from this cnf have "num_tms y = num_tms (map Nt u) \<or> num_tms y = Suc (num_tms (map Nt u))"
      using CNF_deriv_tms_nts_mono[where P=P and u="map Nt u" and v=y]
      by (simp add: num_tms_def)

    moreover have "num_tms (map Nt u) = 0" unfolding num_tms_def by simp
    ultimately have num_tms_variants: "num_tms y = 0 \<or> num_tms y = Suc 0"
      by metis

    have "left_tms_then_nts (map Nt u)" unfolding left_tms_then_nts_def by auto
    with uy cnf thm CNF_derivls_tms_nts have "left_tms_then_nts y" using CNF_derivls_tms_nts by auto
    then obtain tms nts where tms_nts: "y = map Tm tms @ map Nt nts" unfolding left_tms_then_nts_def by blast
    then have num_tms_y: "num_tms y = length tms" unfolding num_tms_def by auto

    from num_tms_variants show ?case
    proof (elim disjE)
      assume "num_tms y = 0"
      with num_tms_y have "length tms = 0" by simp
      with tms_nts have y_nts: "y = map Nt nts" by auto
      with yv have "P \<turnstile> map Nt nts \<Rightarrow>l(m) Tm t # v" by simp
      with Suc obtain T' nts' n1' n2'
        where "P \<turnstile> map Nt nts \<Rightarrow>l(n1') Nt T' # map Nt nts'"
          and "P \<turnstile> Nt T' # map Nt nts' \<Rightarrow>l Tm t # map Nt nts'"
          and "P \<turnstile> Tm t # map Nt nts' \<Rightarrow>l(n2') Tm t # v"
          and "n1' + 1 + n2' = m"
        by blast
      then show ?thesis
        by (smt (verit, best) add_Suc relpowp_Suc_I2 uy y_nts)
    next
      assume "num_tms y = Suc 0"
      with num_tms_y have "length tms = Suc 0" by simp
      then have "\<exists>t'. tms = [t']"
        by (simp add: length_Suc_conv) 
      then obtain t' where "map Tm tms = [Tm t']" by auto
      with tms_nts have y_nts: "y = Tm t' # map Nt nts" by auto

      have t_t: "t' = t"
        by (metis deriveln_Tm_Cons list.inject sym.inject(2) y_nts yv)

      from uy y_nts t_t have "P \<turnstile> map Nt u \<Rightarrow>l Tm t # map Nt nts" by auto
      then have single_step: "P \<turnstile> map Nt u \<Rightarrow>l(1) Tm t # map Nt nts" by auto
      have "\<exists>T' ns' n1' n2'.
              P \<turnstile> map Nt u \<Rightarrow>l(n1') Nt T' # map Nt ns' \<and>
              P \<turnstile> Nt T' # map Nt ns' \<Rightarrow>l Tm t # map Nt ns' \<and>
              P \<turnstile> Tm t # map Nt ns' \<Rightarrow>l(n2') Tm t # map Nt nts \<and>
              n1' + 1 + n2' = 1"
        using single_step Suc(1)[where u=u and v="map Nt nts"]
        by fast
      then obtain T' ns' n1' n2' where
          "P \<turnstile> map Nt u \<Rightarrow>l(n1') Nt T' # map Nt ns'"
          "P \<turnstile> Nt T' # map Nt ns' \<Rightarrow>l Tm t # map Nt ns'"
          "P \<turnstile> Tm t # map Nt ns' \<Rightarrow>l(n2') Tm t # map Nt nts"
          "n1' + 1 + n2' = 1"
        by fast

      moreover
      from yv y_nts t_t have "P \<turnstile> Tm t # map Nt nts \<Rightarrow>l(m) Tm t # v"
        by (simp add: relpowp_imp_rtranclp)
      with \<open>P \<turnstile> Tm t # map Nt ns' \<Rightarrow>l(n2') Tm t # map Nt nts\<close> have
          "P \<turnstile> Tm t # map Nt nts \<Rightarrow>l(m) Tm t # v"
        by force

      ultimately have
          "P \<turnstile> map Nt u \<Rightarrow>l(0) Nt T' # map Nt ns'"
          "P \<turnstile> Nt T' # map Nt ns' \<Rightarrow>l Tm t # map Nt ns'"
          "P \<turnstile> Tm t # map Nt ns' \<Rightarrow>l(m) Tm t # v"
        by auto
      then show ?thesis by force
    qed
  qed
qed


lemma CNF_derivls_first_tm:
  assumes derivls: "P \<turnstile> map Nt u \<Rightarrow>l* Tm t # v"
  and cnf: "CNF P"
  shows "\<exists>ns. P \<turnstile> map Nt u \<Rightarrow>l* Tm t # map Nt ns  \<and>  P \<turnstile> Tm t # map Nt ns \<Rightarrow>l* Tm t # v"
proof -
  from derivls obtain n where "P \<turnstile> map Nt u \<Rightarrow>l(n) Tm t # v"
    using rtranclp_imp_relpowp by fast
  from this cnf show ?thesis
    by (rule CNF_derivln_first_tm)
qed


end