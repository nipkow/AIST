theory cfg_util
  imports "../CFG"
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
(* currently only used in a failed attempt to prove existence of GNF grammar *)
lemma derive_map_Tm_nts_in_prod_invariant:
  assumes "P \<turnstile> u \<Rightarrow>* map Tm v"
  shows "nts_of_syms u \<subseteq> Nts P"
proof -
  have "nts_of_syms (map Tm v) = {}" unfolding nts_of_syms_def by auto
  then have "nts_of_syms (map Tm v) \<subseteq> Nts P" by auto
  from assms this show "nts_of_syms u \<subseteq> Nts P" using derive_nts_in_prod_invariant by fast
qed


end