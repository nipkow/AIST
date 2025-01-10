theory GNF
  imports cfg_renaming cfg_merging util derivel_nts cfg_util map_tms
begin


abbreviation "gnf_rhs rhs \<equiv> (\<exists>t nts. rhs = Tm t # map Nt nts)"

definition GNF :: "('n, 't) Prods \<Rightarrow> bool" where
  "GNF P \<equiv> (\<forall>(A,\<alpha>) \<in> P. gnf_rhs \<alpha>)"

abbreviation gnf :: "('n, 't) cfg \<Rightarrow> bool" where
  "gnf G \<equiv> GNF (set (prods G))"

definition "R P (A::'n) (a::'t) = {\<beta>. P \<turnstile> [Nt A] \<Rightarrow>l* ((Tm a) # map Nt \<beta>)}"

(* properties that G_A,a has *)
definition "G_props (A::'n) (a::'t) G G0 = (L G = R (set (prods G0)) A a \<and> rlin2 (set (prods G)))"

lemma exists_rlin_G_for_R: "cnf G0 \<Longrightarrow> (\<And>A a. (\<exists>G. G_props A a G G0))"
  (* 
      They Grammar {A' \<longrightarrow> B'C | A \<longrightarrow> BC @ P} \<union> {A' \<longrightarrow> \<epsilon> | A \<longrightarrow> a \<in> P}
      produces the language  R (set (prods G0)) A a
      see Kozen. Automata and Computability pp Lecture 21 (about GNF)

      TODO: specify the grammar, show that it is regular

      apply a lemma which shows that for a regular language there is a grammar
      stronly right linear grammar (that means rlin2 G is true)
   *)
  sorry

datatype ('n, 't) renamed = Original 'n | Renamed 'n 't nat

definition "removed_from_G2 P = (\<exists>X B Y. (X, [Nt (Original B), Nt Y]) = P)"

definition "original_sym s \<equiv> (\<exists>nt. s = Nt (Original nt)) \<or> (\<exists>tm. s = Tm tm)"
abbreviation "original_syms ss \<equiv> \<forall>s \<in> (set ss). original_sym s"  


(*  TODO: once, the core of the proof is done,
    identify dependencies between facts and extract `have`s into lemmas *)
theorem gnf_exists:
  shows "\<forall>G::('n::infinite,'t) cfg. \<exists>G0::('n,'t) cfg. (gnf G0) \<and> (L G0 = L G - {[]})"
proof -
  fix G

  (* obtain a grammar for L G that is in CNF *)
  have "\<forall>G::('n::infinite,'t) cfg. \<exists>G0::('n,'t) cfg. (cnf G0) \<and> (L G0 = L G - {[]})"
    by (rule cnf_exists)
  then obtain "G0" where cnf: "(cnf (G0::('n,'t) cfg))"
                and cnf_L_eq: "(L G0 = L (G::('n::infinite,'t) cfg) - {[]})"
    by auto

  (* witness function for G_A,a. The grammars adhere to G_props *)
  obtain witness where func: "(\<And>A a. (\<exists>G. (witness:: 'n \<Rightarrow> 't \<Rightarrow> (nat,'n) cfg) A a = G \<and> G_props A a G G0))"
    by (meson exists_rlin_G_for_R cnf)

  (* Derive a witness function for G_A,a
     that renames the nonterminals to ensure that these are disjoint *)
  obtain renamed_wittness where renamed_wittness_def: "renamed_wittness = (\<lambda> A a. (rename_cfg (Renamed A a)) (witness A a))" by simp
  
  (* Grammars returned by renamed_wittness also adhere to G_props *)
  then have "(\<And>A a. (\<exists>G. renamed_wittness A a = G \<and> G_props A a G G0))"
    by (smt (verit) G_props_def cfg_rename_L cfg_rename_rlin2 func injI renamed.inject(2))

  (* The nonterminals of different grammars returned by renamed_wittness are disjoint.
     This fact is currently not yet used, but will later be relevant. *)
  have "\<And>A a B b. (A \<noteq> B \<or> a \<noteq> b) \<Longrightarrow> ((nts (prods (renamed_wittness A a)) \<inter> nts (prods (renamed_wittness B b)) = {}))"
  proof
    fix A a B b
    assume assm: "((A::'n) \<noteq> B \<or> (a::'t) \<noteq> b)"
    let ?f = "Renamed A a" and ?g = "Renamed B b"
    from assm have "range (?f) \<inter> range (?g) = {}" by blast
    then have "\<And>ps1 ps2. nts (map (rename_prod ?f) ps1) \<inter> nts (map (rename_prod ?g) ps2) = {}" by (rule rename_prods_disjoint)
    then show "nts (prods (renamed_wittness A a)) \<inter> nts (prods (renamed_wittness B b)) \<subseteq> {}"
      by (metis (no_types, lifting) cfg.collapse cfg.sel(1) renamed_wittness_def rename_cfg.simps subset_empty)
  qed simp

  (* construction of G1 from G0:
     First rename the nonterminals in G0 to distinguish them from the new ones:
       \<rightarrow> yields grammar G0R
     Then create the union of the productions of each G_A,a and replace all
     terminals in G_A,a with the corresponding nonterminals of G0R
       \<rightarrow> yields productions ?G1_new_prods
     The productions of G1 are the union of ?G1_new_prods with the productions of G0R *)
  obtain G0R where G0R_def: "(G0R::(('n,'t) renamed,'t) cfg) = rename_cfg Original G0" by fast
  obtain G_union where G_union_def: "(G_union::(('n,'t) renamed,'n) Prods) = 
      (\<Union>A\<in>(nts (prods G0)). (\<Union> a\<in>(tms (prods G0)). set(prods (renamed_wittness A a))))"
    by fast
  let ?G1_new_prods = "map_tms_Prods Original G_union"
  let ?G0R_prods = "set (prods G0R)"
  let ?G1_prods = "?G0R_prods \<union> ?G1_new_prods"

  (* G0R is still in CNF *)
  from cnf have "cnf G0R" unfolding G0R_def by (rule cfg_rename_cnf_dir1)
  then have "CNF ?G0R_prods" by simp

  (* show that G0R and G1 yield the same language *)
  have "Nts ?G0R_prods \<inter> Lhss ?G1_new_prods = {}"
  proof -
    have "\<And>A a. Nts ?G0R_prods \<inter> Nts (set (prods (renamed_wittness A a))) = {}"
    proof
      fix A a
      have f_g_disjoint: "range Original \<inter> range (Renamed (A::'n) (a::'t)) = {}" by blast
      let ?f = "Original" and ?g = "Renamed A a"
      from f_g_disjoint have 
          "\<And>ps1 ps2. nts (map (rename_prod ?f) ps1) \<inter> nts (map (rename_prod ?g) ps2) = {}"
        by (rule rename_prods_disjoint)
      then show "nts (prods G0R) \<inter> nts (prods (renamed_wittness A a)) \<subseteq> {}"
        by (metis G0R_def prods_rename_cfg_rename_prods renamed_wittness_def subset_empty)
    qed simp
    then have "\<And>A a. Nts ?G0R_prods \<inter> Lhss (set (prods (renamed_wittness A a))) = {}"
      by (meson disjoint_iff fresh_Lhss)
    then have "Nts ?G0R_prods \<inter> Lhss G_union = {}"
      unfolding G_union_def Lhss_def by blast
    then show ?thesis using map_tms_Prods_Lhss unfolding G_union_def
      by fast 
  qed
  moreover have "\<And>S A a. (Original S) \<notin> Nts (set (prods (renamed_wittness A a)))"
  proof -
    fix S A a
    have "\<And>ps. Nts (set (rename_prods (Renamed (A::'n) (a::'t)) ps)) = (Renamed A a) ` nts ps"
      using nts_rename_prod by simp
    moreover have "\<And>ps. (Original S) \<notin> (Renamed A a) ` nts ps"
      by blast
    ultimately show "(Original S) \<notin> Nts (set (prods (renamed_wittness A a)))"
      unfolding renamed_wittness_def by (metis prods_rename_cfg_rename_prods)
  qed
  then have "\<And>S. (Original S) \<notin> Nts G_union"
    unfolding G_union_def renamed_wittness_def using nts_rename_prod
    unfolding Nts_def by simp
  then have "\<And>S. (Original S) \<notin> Lhss G_union"
    unfolding Nts_def Lhss_def by fast
  then have "\<And>S. (Original S) \<notin> Lhss ?G1_new_prods"
    using map_tms_Prods_Lhss by fast
  ultimately have "Lang (?G0R_prods) (Original (start G0)) = Lang (?G0R_prods \<union> ?G1_new_prods) (Original (start G0))"
    by (rule append_unreachable_productions_L)

  (* continue by showing that G0R and G0 yield the same language *)
  moreover have "Lang (?G0R_prods) (Original (start G0)) = L G0R"
    by (metis \<open>G0R = rename_cfg Original G0\<close> cfg.exhaust_sel cfg.sel(2) rename_cfg.simps) 
  moreover have "L G0R = L (rename_cfg Original G0)"
    using G0R_def
    by (metis (mono_tags, opaque_lifting) cfg_rename_L inj_def renamed.inject(1))

  (* ultimately, G1 yields the same language as G0 *)
  moreover have "L (rename_cfg Original G0) = L G0"
    by (metis cfg_rename_L injI renamed.inject(1))
  ultimately have "Lang (?G1_prods) (Original (start G0)) = L G0" by auto

  (* construction of G2 from G1:
      replace all productions of the form A \<rightarrow> BY (where B is a nonterminal in G0R)
      with all possible productions A \<rightarrow> b<S_B,b>Y, where S_B,b is the start symbol
      of the renamed grammar G_B,b
   *)
  obtain G2_new_prods where G2_new_prods_def: 
      "G2_new_prods = {(A,a'). \<exists>B b Y. 
        a' = [Tm b, Nt (start (renamed_wittness B b)),Nt Y] \<and>
        (A, [Nt (Original B), Nt Y]) \<in> (?G0R_prods \<union> ?G1_new_prods)}"
    by simp
  obtain G2_retained_prods where G2_retained_prods_def:
    "G2_retained_prods = {P \<in> (?G0R_prods \<union> ?G1_new_prods). \<not> removed_from_G2 P}"
    by simp
  let ?G2_prods = "G2_retained_prods \<union> G2_new_prods"

  note \<open>\<And>S. Original S \<notin> Lhss ?G1_new_prods\<close> 
  then have G1_prods_Original: "\<And>A w. (A,w) \<in> ?G1_prods \<Longrightarrow> (\<exists>nt. A = Original nt) \<Longrightarrow> (A,w) \<in> ?G0R_prods"
    unfolding Lhss_def by blast

  (*
    First part of the proof of equivalence of G1 and G2:
      Show by induction on the length of the leftmost derivation, that for each
      sequence of nonterminals (that originate from G0R), G1 and G2 produce the
      same sequences of terminals.
   *)
  have "\<And>ss x. (?G1_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x)) \<Longrightarrow>
                (?G2_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x))"
  proof -
    fix ss x
    have "(?G1_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x)) \<Longrightarrow>
          (?G2_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x))"
    proof -
      let ?ntss = "map (Nt o Original) ss"
      assume "(?G1_prods \<turnstile> ?ntss \<Rightarrow>* (map Tm x))"
      (* there must be a leftmost derivation *)
      from this(1) have "(?G1_prods \<turnstile> ?ntss \<Rightarrow>l* (map Tm x))" by (rule derives_tms_imp_derivels)
      (* obtain the length of that derivation *)
      then have "\<exists>n. (?G1_prods \<turnstile> ?ntss \<Rightarrow>l(n) (map Tm x))"
        by (rule rtranclp_imp_relpowp)
      then obtain n where "?G1_prods \<turnstile> ?ntss \<Rightarrow>l(n) (map Tm x)" by auto

      (* Beginning of the actual induction proof:
         Shows: If there is a leftmost derivation in G1 of length \<le> n
           from any sequence of nonterminals contained in G0R to the terminal word x
           then there must also be a derivation in G2
       *)
      fix sss
      have "\<And>m. ?G1_prods \<turnstile> map (Nt o Original) sss \<Rightarrow>l(m) (map Tm x) \<Longrightarrow> m \<le> n \<Longrightarrow> 
                 ?G2_prods \<turnstile> map (Nt o Original) sss \<Rightarrow>* (map Tm x)"
      proof (induction n arbitrary: sss)
        case 0
        (* trivial, since both sides of the derivation must be [] then *)
        then show ?case by simp
      next
        case (Suc n)

        (*
          Proof idea for this case:
            Due to lemma append_unreachable_productions_derive
            sequences of derivations in G1 starting from original nonterminals can never
            lead to sentinential words containing nonterminals that only G2 contains.
            
            Thus, if there is a leftmost derivation in G1, then the same derivation also is
            possible in G0.
            We can obtain such a derivation and then obtain the first step where
            a terminal is introduced at the left end.
              For that there is lemma CNF_derivln_first_tm_strong

            Due to the construction, when the first terminal a is introduced,
            also the start symbol S_A,a is generated. 
            This is the first time, the derivations in G1 and G2 are different.
              

            Thus, the sentinential from in the G1 derivation has the following form:
              Tm a # [Nt A] @ map Nt nts
            And in G2:
              Tm a # Nt (start (renamed_wittness A a)) @ map Nt nts
                note: `(start (renamed_wittness A a))` the expression for `S_A,a`
              
            We know, that for all derivations
              G1_prods \<turnstile> [Nt A] \<Rightarrow> y
            which lead to terminals, there is a corresponding derivation G2 \<turnstile> [S_A,a] \<Rightarrow> y,
            due to the construction.

            Due to the induction hypothesis, we know
              G1_prods \<turnstile> [map Nt nts] \<Rightarrow>* nts' \<Longrightarrow> G2_prods \<turnstile> [map Nt nts] \<Rightarrow>* nts'


            It may be required to generalize the induction, so that not only (map Tm x) are derived,
            but sequences of (at least one) terminals followed by nonterminals
         *)




        (* Most part of the remaining part of the "proof" is leftover from a previous,
           failed attempt. Nevertheless, some facts may be helpful.
         *)
(*
        from this(2) have "?G0R_prods \<union> ?G1_new_prods \<turnstile> map (Nt \<circ> Original) sss \<Rightarrow>l(m) map Tm x" by force
        then have "?G0R_prods \<union> ?G1_new_prods \<turnstile> map (Nt \<circ> Original) sss \<Rightarrow>l* map Tm x"
          by (simp add: relpowp_imp_rtranclp)
        then have "?G0R_prods \<union> ?G1_new_prods \<turnstile> map (Nt \<circ> Original) sss \<Rightarrow>* map Tm x"
          by (simp add: derivels_iff_derives)
        moreover note \<open>Nts ?G0R_prods \<inter> Lhss ?G1_new_prods = {}\<close>
  
        from \<open>?G0R_prods \<union> ?G1_new_prods \<turnstile> map (Nt \<circ> Original) sss \<Rightarrow>* map Tm x\<close> 
        have "nts_of_syms (map (Nt \<circ> Original) sss) \<subseteq> Nts (?G0R_prods \<union> ?G1_new_prods)"
          by (metis derive_map_Tm_nts_in_prod_invariant list.map_comp nts_of_syms_map_Nt)
        then have "nts_of_syms (map (Nt \<circ> Original) sss) \<subseteq> Lhss (?G0R_prods)"
          unfolding nts_of_syms_def sorry
        moreover have "nts_of_syms (map (Nt \<circ> Original) sss) = set (map (Original) sss)"
          using nts_of_syms_map_Nt by (metis list.map_comp)
  
        ultimately have "nts_of_syms (map (Nt \<circ> Original) sss) \<subseteq> Nts (?G0R_prods)"
          by simp
  
        ultimately have "nts_of_syms (map Tm x) \<subseteq> Nts ?G0R_prods"
          using append_unreachable_productions_derive by blast 
  
        with Suc show ?case
        proof (cases m)
          case 0
          with Suc show ?thesis by simp
        next
          let ?ntsss = "map (Nt o Original) sss"
          case innerSuc: (Suc mn)
          with Suc(2) have "?G1_prods \<turnstile> ?ntsss \<Rightarrow>l(Suc mn) map Tm x"
            by blast
  
          thm CNF_derivln_first_tm_strong
  
  
          then have "\<exists>y. (?G1_prods \<turnstile> ?ntsss \<Rightarrow>l y \<and> ?G1_prods \<turnstile> y \<Rightarrow>l(mn) (map Tm x))"
            by (rule relpowp_Suc_D2)
          then obtain y where "?G1_prods \<turnstile> ?ntsss \<Rightarrow>l y" and first_g1: "?G1_prods \<turnstile> y \<Rightarrow>l(mn) (map Tm x)" by auto
  
  
          from first_g1 innerSuc Suc have first: "?G2_prods \<turnstile> y \<Rightarrow>* map Tm x" by auto
  
  
          note \<open>?G1_prods \<turnstile> ss \<Rightarrow>l y\<close>
          then have "(\<exists> (A,w) \<in> ?G1_prods. \<exists>u1 u2. ss = map Tm u1 @ Nt A # u2 \<and> y = map Tm u1 @ w @ u2)"
            using derivel_iff
            by blast 
          then obtain A w u1 u2 where "(A,w) \<in> ?G1_prods" and ss: "ss = map Tm u1 @ Nt A # u2" and y: "y = map Tm u1 @ w @ u2" by auto
  
          have "?G2_prods \<turnstile> [Nt A] @ u2 \<Rightarrow>* w @ u2"
          proof (cases A)
            case (Original nt)
            with \<open>(A,w) \<in> ?G1_prods\<close> have "(A,w) \<in> ?G0R_prods" using G1_prods_Original by auto
            with \<open>CNF ?G0R_prods\<close> have "(\<exists>B C. w = [Nt B, Nt C]) \<or> (\<exists>t. w = [Tm t])"
              unfolding CNF_def by fast
            then show ?thesis
            proof (elim disjE)
              assume "(\<exists>B C. w = [Nt B, Nt C])"
              then obtain B C where "w = [Nt B, Nt C]" by auto
              show ?thesis sorry
            next
              assume "(\<exists>t. w = [Tm t])"
              then obtain t where "w = [Tm t]" by auto
              then have "\<not> removed_from_G2 (A,w)"
                by (simp add: removed_from_G2_def)
              then have "(A,w) \<in> G2_retained_prods"
                unfolding G2_retained_prods_def removed_from_G2_def
                using \<open>(A, w) \<in> ?G1_prods\<close> G1_prods_def by blast
              then have "(A,w) \<in> ?G2_prods" unfolding ?G2_prods_def by simp
              then have "?G2_prods \<turnstile> [Nt A] \<Rightarrow> w"
                using derive_singleton by blast
              then have "?G2_prods \<turnstile> [Nt A] @ u2 \<Rightarrow> w @ u2"
                using derive_append_decomp by blast
              then show ?thesis by simp
            qed
  
            (* TODO: case distinction between different possible cases of w *)
  
          next
            (* due to \<open>original ss\<close>, this is case not possible *)
            case (Renamed AA aa num)
            with ss Suc(4) show ?thesis unfolding original_sym_def by auto
          qed
          then have "?G2_prods \<turnstile> Nt A # u2 \<Rightarrow>* w @ u2"
            by (metis append.left_neutral append_Cons derives_append)
          then have "?G2_prods \<turnstile> map Tm u1 @ Nt A # u2 \<Rightarrow>* map Tm u1 @ w @ u2"
            using derives_prepend by blast 
          with ss y have second: "?G2_prods \<turnstile> ss \<Rightarrow>* y" by simp
  
          from first second show ?thesis by auto
        qed
      qed
      moreover note original
      ultimately show "?G2_prods \<turnstile> ss \<Rightarrow>* map Tm x" by simp
*)


  show ?thesis sorry
qed




end