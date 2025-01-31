theory cfg_util
  imports "../CFG" "../Stimpfle/CNF"
begin

(*
  Some utility lemmas about grammars that did not fit into other files.
  The sorries are only relevant for parts of the GNF proof, that are not in use (anymore).
 *)

(* derives/deriven implies derivel if the result is a word consisting of terminals *)
lemma deriven_imp_derivels: "P \<turnstile> u \<Rightarrow>(n) (map Tm v) \<Longrightarrow> P \<turnstile> u \<Rightarrow>l* (map Tm v)"
proof (induction arbitrary: u v rule: nat_induct)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "\<exists>u'. P \<turnstile> u \<Rightarrow> u' \<and> P \<turnstile> u' \<Rightarrow>(n) map Tm v"
    by (simp add: relpowp_Suc_D2)
  then have "\<exists>u'. P \<turnstile> u \<Rightarrow> u'" by auto

  then have "\<exists>tms nt ss. (map Tm tms) @ [Nt nt] @ ss = u"
    (* TODO: write a (faster) proof by hand*)
    by (metis Cons_eq_append_conv Suc.prems append_self_conv2 derivel.cases deriveln_iff_deriven nat.distinct(1) relpowp_E2) 
  then show ?case
    by (metis Suc.prems deriveln_iff_deriven rtranclp_power)
qed

(* derives/deriven implies derivel if the result is a word consisting of terminals *)
lemma derives_tms_imp_derivels: "P \<turnstile> u \<Rightarrow>* (map Tm v) \<Longrightarrow> P \<turnstile> u \<Rightarrow>l* (map Tm v)"
proof -
  assume "P \<turnstile> u \<Rightarrow>* (map Tm v)"
  then have "\<exists>n. P \<turnstile> u \<Rightarrow>(n) (map Tm v)"
    by (simp add: rtranclp_power)
  then obtain n where "P \<turnstile> u \<Rightarrow>(n) (map Tm v)" by auto
  then show "P \<turnstile> u \<Rightarrow>l* (map Tm v)" using deriven_imp_derivels by auto
qed



lemma nts_of_syms_map_Nt: "nts_of_syms (map Nt ns) = set ns"
  unfolding map_def nts_of_syms_def by auto

(* derivations cannot remove or introduce nonterminals which are not in the productions *)
lemma derive_nts_in_prod_invariant: "P \<turnstile> u \<Rightarrow>* v \<Longrightarrow> nts_of_syms u \<subseteq> Nts P \<longleftrightarrow> nts_of_syms v \<subseteq> Nts P"
  sorry

(* derivations cannot remove or introduce terminals which are not in the productions *)
lemma derive_tms_in_prod_invariant: "P \<turnstile> u \<Rightarrow>* v \<Longrightarrow> tms_of_syms u \<subseteq> Tms P \<longleftrightarrow> tms_of_syms v \<subseteq> Tms P"
  sorry

(* words consisting of terminals cannot be derived from nonterminals not in the productions *)
(* currently unused *)
lemma derive_map_Tm_nts_in_prod_invariant:
  assumes "P \<turnstile> u \<Rightarrow>* map Tm v"
  shows "nts_of_syms u \<subseteq> Nts P"
proof -
  have "nts_of_syms (map Tm v) = {}" unfolding nts_of_syms_def by auto
  then have "nts_of_syms (map Tm v) \<subseteq> Nts P" by auto
  from assms this show "nts_of_syms u \<subseteq> Nts P" using derive_nts_in_prod_invariant by fast
qed








lemma derivel_not_elim_tm:
  assumes "P \<turnstile> xs \<Rightarrow>l map Nt ys"
  shows "\<exists>xs'. xs = map Nt xs'"
proof -
  from assms obtain A w u1 u2 where
         A_w: "(A, w)\<in>P"
      and xs: "xs = map Tm u1 @ Nt A # u2"
      and ys: "map Nt ys = map Tm u1 @ w @ u2"
    unfolding derivel_iff by fast

  from ys have u1: "u1 = []"
    by (metis Nil_is_append_conv Nil_is_map_conv hd_append list.map_sel(1) sym.simps(4))
  moreover from ys obtain u2' where "u2 = map Nt u2'"
    by (metis append_eq_map_conv)

  ultimately have "xs = map Nt (A # u2')"
    by (simp add: xs)
  then show ?thesis by blast
qed

lemma deriveln_not_elim_tm:
  assumes "P \<turnstile> xs \<Rightarrow>l(n) map Nt ys"
  shows "\<exists>xs'. xs = map Nt xs'"
using assms
proof (induction n arbitrary: xs)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then obtain z where "P \<turnstile> xs \<Rightarrow>l z" and "P \<turnstile> z \<Rightarrow>l(n) map Nt ys"
    using relpowp_Suc_E2 by metis
  with Suc show ?case using derivel_not_elim_tm
    by blast
qed


lemma derivel_nts_suffix:
  assumes "P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l map Nt Ys"
  shows "\<exists>Ys'. Ys' @ Xs = Ys \<and> P \<turnstile> [Nt X] \<Rightarrow>l map Nt Ys'"
proof -
  from assms obtain A w u1 u2 where
           A_w: "(A, w)\<in>P"
      and X_Xs: "Nt X # map Nt Xs = map Tm u1 @ Nt A # u2"
      and Ys: "map Nt Ys = map Tm u1 @ w @ u2"
    unfolding derivel_iff by fast

  from X_Xs have u1: "u1 = []"
    by (metis (no_types, opaque_lifting) Cons_eq_append_conv list.map_disc_iff map_eq_Cons_D sym.distinct(1))
  moreover from u1 X_Xs obtain u2' where u2':"u2 = map Nt u2'"
    by auto
  moreover note X_Xs
  ultimately have "Nt X # map Nt Xs = map Nt (A # u2')"
    by (smt (verit, best) append_self_conv2 list.inj_map_strong list.simps(9) map_is_Nil_conv slemma4_2_0)
  then have "map Nt (X # Xs) = map Nt (A # u2')" by simp
  then have "X # Xs = A # u2'"
    by (metis list.inj_map_strong sym.inject(1))
  then have "X = A" and "Xs = u2'" by auto

  from u1 Ys obtain w' where "w = map Nt w'"
    by (metis append_eq_map_conv)

  with Ys have "map Nt Ys = map Tm u1 @ map Nt w' @ u2"
    by simp
  with u1 have "map Nt Ys = map Tm [] @ map Nt w' @ u2"
    by simp
  then have "map Nt Ys = map Nt w' @ u2"
    by simp
  with u2' have "map Nt Ys = map Nt w' @ map Nt u2'"
    by (metis list.inj_map_strong map_append sym.inject(1))
  with \<open>Xs = u2'\<close> have "map Nt Ys = map Nt w' @ map Nt Xs"
    by simp
  then have "w' @ Xs = Ys"
    by (metis list.inj_map_strong map_append sym.inject(1))

  moreover from A_w have "P \<turnstile> [Nt A] \<Rightarrow>l w"
    by (simp add: derivel_Nt_Cons)
  with A_w have "P \<turnstile> [Nt X] \<Rightarrow>l w"
    using \<open>X = A\<close> by blast
  with A_w \<open>w = map Nt w'\<close> have "P \<turnstile> [Nt X] \<Rightarrow>l map Nt w'"
    by blast

  ultimately have "w' @ Xs = Ys \<and> P \<turnstile> [Nt X] \<Rightarrow>l map Nt w'"
    by simp
  then show ?thesis by fast
qed





lemma Eps_free_derivels_Nil: "Eps_free R \<Longrightarrow> R \<turnstile> l \<Rightarrow>l* [] \<longleftrightarrow> l = []"
  by (meson Eps_free_derives_Nil derivels_from_empty derivels_imp_derives)


lemma CNF_Eps_free: "CNF P \<Longrightarrow> Eps_free P"
  unfolding CNF_def Eps_free_def by blast


lemma deriveln_nts_suffix:
  assumes "P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l(n) map Nt Ys"
  assumes "Eps_free P"
  shows "\<exists>Ys'. Ys' @ Xs = Ys \<and> P \<turnstile> [Nt X] \<Rightarrow>l(n) map Nt Ys'"
using assms
proof (induction n arbitrary: Ys)
  case 0
  then have "Nt X # map Nt Xs = map Nt Ys"
    by (smt (verit, best) list.inj_map_strong map_eq_Cons_conv relpowp.simps(1) sym.inject(1))
  
  with 0 have "[X] @ Xs = Ys \<and> P \<turnstile> [Nt X] \<Rightarrow>l* map Nt [X]"
    by (smt (verit, ccfv_SIG) append_Cons append_Nil list.inj_map_strong list.simps(8) map_eq_Cons_conv rtranclp.rtrancl_refl sym.inject(1))
  then show ?case
    by auto
next
  case (Suc n)

  then obtain z where "P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l(n) z" and "P \<turnstile> z \<Rightarrow>l map Nt Ys"
    using relpowp_Suc_E by metis

  from \<open>P \<turnstile> z \<Rightarrow>l map Nt Ys\<close> obtain xs' where "z = map Nt xs'"
    using derivel_not_elim_tm by blast
  with \<open>P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l(n) z\<close> have "P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l(n) map Nt xs'"
    by simp
  with Suc(1) assms(2) obtain Ys'1 where IH: "Ys'1 @ Xs = xs' \<and> P \<turnstile> [Nt X] \<Rightarrow>l(n) map Nt Ys'1"
    by fast

  from \<open>z = map Nt xs'\<close> \<open>P \<turnstile> z \<Rightarrow>l map Nt Ys\<close> have "P \<turnstile> map Nt xs' \<Rightarrow>l map Nt Ys"
    by fast

  show ?case
  proof (cases xs')
    case Nil
    with \<open>P \<turnstile> map Nt xs' \<Rightarrow>l map Nt Ys\<close> have "P \<turnstile> [] \<Rightarrow>l map Nt Ys" by simp
    then have False by simp
    then show ?thesis by fast
  next
    case (Cons xs'1 xs's)
    with \<open>P \<turnstile> map Nt xs' \<Rightarrow>l map Nt Ys\<close> have "P \<turnstile> Nt xs'1 # map Nt xs's \<Rightarrow>l map Nt Ys"
      by simp
    then obtain Ys'2 where step: "Ys'2 @ xs's = Ys" "P \<turnstile> [Nt xs'1] \<Rightarrow>l map Nt Ys'2"
      using derivel_nts_suffix by fast
    
    show ?thesis
    proof (cases "Ys'1")
      case Nil
      with IH Cons have "P \<turnstile> [Nt X] \<Rightarrow>l(n) map Nt []"
        by auto
      then have False using Eps_free_derivels_Nil
        by (metis assms(2) list.discI map_is_Nil_conv relpowp_imp_rtranclp) 
      then show ?thesis by (rule FalseE)
    next
      case innerCons: (Cons Ys'1_1 Ys'1s)
      with IH Cons have "Ys'1_1 = xs'1"
        by auto

      with IH innerCons have IH_new: "xs'1 # Ys'1s @ Xs = xs' \<and> P \<turnstile> [Nt X] \<Rightarrow>l(n) Nt xs'1 # map Nt Ys'1s"
        by simp
      with Cons step(1) have "Ys'2 @ Ys'1s @ Xs = Ys"
        by blast

      moreover from IH_new \<open>P \<turnstile> [Nt xs'1] \<Rightarrow>l map Nt Ys'2\<close> have "P \<turnstile> [Nt X] \<Rightarrow>l(Suc n) map Nt Ys'2 @ map Nt Ys'1s"
        using derivel_append relpowp_Suc_I by fastforce
      then have "P \<turnstile> [Nt X] \<Rightarrow>l(Suc n) map Nt (Ys'2 @ Ys'1s)"
        by simp 

      ultimately show ?thesis
        by auto
    qed
  qed
qed







end