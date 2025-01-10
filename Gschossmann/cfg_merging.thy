theory cfg_merging
  imports "../CFG"
begin

(*
  This theory provides lemmas relevant when combining
  the productions of two grammars with disjoint
  sets of nonterminals.

  The theory is nearly complete: I could not prove one fact that seems
  to be identical to another, already proven fact at first, but is
  actually different in some subtle that the display does not show. 
*)


(* any derived word can only contain nonterminals that are part of
   either part of the grammar's nonterminals or contained in the
   word it is derived from *)
lemma nts_prods_subset:
  assumes deriv: "P \<turnstile> u \<Rightarrow>* v"
  shows "nts_of_syms v \<subseteq> Nts P \<union> nts_of_syms u"
proof
  fix x
  assume asm: "x \<in> nts_of_syms v"
  show "x \<in> Nts P \<union> nts_of_syms u"
  proof
    assume "x \<notin> nts_of_syms u"
    from deriv this show "x \<in> Nts P"
    proof (induction rule: derives_induct')
      case base
      with asm show ?case by simp
    next
      case (step pre A post a)
      then show ?case
      proof (cases "x \<in> nts_of_syms a")
        case True
        with \<open>(A, a) \<in> P\<close> show ?thesis unfolding Nts_def by auto
      next
        case False
        with step(4) have "x \<notin> nts_of_syms (pre @ post)"
          by (metis UnCI UnE nts_of_syms_append)
        with False have  "x \<notin> nts_of_syms (pre @ a @ post)"
          by simp
        with step(3) show "x \<in> Nts P" by simp
      qed
    qed
  qed
qed


(* If two grammars with disjoint sets of nonterminals are merged, 
   then words derived from words which only contain nonterminals
   of one grammar can also contain only such nonterminals.
 *)
lemma append_unreachable_productions_derive:
  assumes "old \<union> new \<turnstile> u \<Rightarrow>* v"
      and "Nts old \<inter> Lhss new = {}"
      and "nts_of_syms u \<subseteq> Nts old"
    shows "nts_of_syms v \<subseteq> Nts old"
proof -
  from assms show "nts_of_syms v \<subseteq> Nts old"
  proof (induction rule: derives_induct')
    case base
    then show ?case by auto
  next
    case (step u' A v' w)

    from \<open>(A, w) \<in> old \<union> new\<close> have "(A,w) \<in> old \<or> (A,w) \<in> new" by simp
    then show ?case
    proof (elim disjE)
      assume "(A, w) \<in> old"
      then have "nts_of_syms w \<subseteq> Nts old" unfolding nts_of_syms_def Nts_def by fast
      with step(5) have "nts_of_syms (u' @ w @ v') \<subseteq> Nts old" unfolding nts_of_syms_def by auto
      with step(4) step(3) show "nts_of_syms v \<subseteq> Nts old" by fast
    next
      assume "(A, w) \<in> new"

      from \<open>nts_of_syms (u' @ [Nt A] @ v') \<subseteq> Nts old\<close> have "nts_of_syms [Nt A] \<subseteq> Nts old"
        unfolding nts_of_syms_def by auto
      then have "A \<in> Nts old" unfolding nts_of_syms_def by simp
      then have "A \<notin> Lhss new" using \<open>Nts old \<inter> Lhss new = {}\<close> by auto
      with \<open>(A, w) \<in> new\<close> have False unfolding Lhss_def by auto
      then show "nts_of_syms v \<subseteq> Nts old" by fast
    qed
  qed
qed


(* If two grammars with disjoint sets of nonterminals are merged, 
   then the language described by that grammar is that of the
   grammar which contains the start symbol.
 *)
lemma append_unreachable_productions_L:
  assumes "Nts old \<inter> Lhss new = {}"
  and "S \<notin> Lhss new"
  shows "Lang old S = Lang (old \<union> new) S"
proof
  show "Lang old S \<subseteq> Lang (old \<union> new) S"
  proof
    fix x
    assume "x \<in> Lang old S"
    then have "old \<turnstile> [Nt S] \<Rightarrow>* map Tm x" unfolding Lang_def by simp
    then have "old \<union> new \<turnstile> [Nt S] \<Rightarrow>* map Tm x"
      by (metis (no_types, opaque_lifting) Un_derive mono_rtranclp)
    then show "x \<in> Lang (old \<union> new) S" unfolding Lang_def by simp
  qed
next
  show "Lang (old \<union> new) S \<subseteq> Lang old S"
  proof
    fix x
    assume "x \<in> Lang (old \<union> new) S"
    then have "old \<union> new \<turnstile> [Nt S] \<Rightarrow>* map Tm x" unfolding Lang_def by simp
    then have "old \<turnstile> [Nt S] \<Rightarrow>* map Tm x"
    proof (induction)
      case base
      then show ?case by simp
    next
      case (step y z)
      from step(2) have derivations: "old \<turnstile> y \<Rightarrow> z \<or> new \<turnstile> y \<Rightarrow> z" by (simp only: Un_derive)
      show ?case
      proof (cases "old \<turnstile> y \<Rightarrow> z")
        case True
        then show ?thesis
          using step.IH by simp 
      next
        case False
        with derivations have "new \<turnstile> y \<Rightarrow> z" by simp
        then have "(\<exists> (A,w) \<in> new. \<exists>u1 u2. y = u1 @ Nt A # u2 \<and> z = u1 @ w @ u2)" by (simp only: derive_iff)
        then obtain A w u1 u2 where y_A: "(A,w) \<in> new \<and> y = u1 @ Nt A # u2 \<and> z = u1 @ w @ u2" by fast
        then have A_new: "A \<in> Lhss new" unfolding Lhss_def by auto

        from \<open>old \<turnstile> [Nt S] \<Rightarrow>* y\<close> have "nts_of_syms y \<subseteq> Nts old \<union> nts_of_syms [Nt S]"
          using nts_prods_subset sorry (* ? ? *)
      (*
        from nts_prods_subset[where u="[Nt S]" and v=y and P=old]
        have x: "old \<turnstile> [Nt S] \<Rightarrow>* y \<Longrightarrow> nts_of_syms y \<subseteq> Nts old \<union> nts_of_syms [Nt S]" by simp
  
        print_statement nts_prods_subset[where u="[Nt S]" and v=y and P=old]
        print_statement x
      *)

        then have "nts_of_syms y \<subseteq> Nts old \<union> {S}" unfolding nts_of_syms_def by simp
        moreover from y_A have "A \<in> nts_of_syms y" unfolding nts_of_syms_def by simp
        ultimately have "A \<in> Nts old \<union> {S}" by auto
        with A_new assms have False by auto
        then show ?thesis by simp
      qed
    qed
    then show " x \<in> Lang old S" unfolding Lang_def by simp
  qed
qed


end