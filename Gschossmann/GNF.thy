theory GNF
  imports cfg_renaming cfg_merging util derivel_nts cfg_util map_tms
begin

(*
  STATE OF THE PROOF

  tldr: The construction is nearly complete, but its proof is missing since the
        main lemma G0_G2 is broken. Utility lemmas in other files should be OK.

  Complete:
    - various lemmas about:
      - renaming of nonterminals (cfg_renaming.thy)
      - replacing all terminals with corresponding nonterminals (map_tms.thy)
      - merging CFGs with disjoint sets of nonterminals (cfg_merging.thy)
      - leftmost derivations and nonterminals (derivel_nts.thy)
    - The construction of a grammar G2 nearly in GNF from a grammar in CNF
      - G2 still contains epsilon productions

  Incomplete / missing / skipped parts:
    - The proof that the constructed grammar yields the same language as the original grammar
      - This proof is split into two directions, G0_G2 and G2_G0.
        - While G0_G2 is present, it relies on a skipped proof that is actually not provable.
          Thus, the proof for G0_G2 below is basically useless.
        - G2_G0 is missing.
    - The proof, that G2 is actually in GNF (but with epsilon productions) is missing
    - The proof relies on the (unproved) lemma that there is always a strongly right linear
      grammar for all languages R_A,a
    - The removal of the epsilon productions is not described and the proof that it does not
      introduce unit productions is missing.
 *)


(* CNF.thy? *)
definition some_cnf :: "('n::infinite,'t) cfg \<Rightarrow> ('n,'t) cfg" where
  "some_cnf G = (SOME G'. (cnf G') \<and> (L G' = L G - {[]}))"

(* CNF.thy? *)
lemma some_cnf_cnf: "cnf (some_cnf (G::('n::infinite,'t) cfg)) \<and> L (some_cnf G) = L G - {[]}"
proof -
  from cnf_exists have "\<exists>(G'::('n::infinite,'t) cfg). cnf G' \<and> L G' = L G - {[]}" by blast
  then show ?thesis unfolding some_cnf_def by (rule someI_ex)
qed


abbreviation "gnf_rhs rhs \<equiv> (\<exists>t nts. rhs = Tm t # map Nt nts)"

definition GNF :: "('n, 't) Prods \<Rightarrow> bool" where
  "GNF P \<equiv> (\<forall>(A,\<alpha>) \<in> P. gnf_rhs \<alpha>)"

abbreviation gnf :: "('n, 't) cfg \<Rightarrow> bool" where
  "gnf G \<equiv> GNF (set (prods G))"




(* construction *)

datatype ('n, 't) renamed = Original 'n | Renamed 'n 't nat



definition G0 :: "('n::infinite,'t) cfg \<Rightarrow> ('n::infinite,'t) cfg" where
  "G0 G = some_cnf G"

definition G0_prods :: "('n::infinite,'t) cfg \<Rightarrow> ('n,'t) Prods" where
  "G0_prods G = set (prods (G0 G))"

definition G0_start :: "('n::infinite,'t) cfg \<Rightarrow> 'n" where
  "G0_start G = start (some_cnf G)"

definition G0R_prods :: "('n::infinite,'t) cfg \<Rightarrow> (('n,'t) renamed,'t) Prods" where
  "G0R_prods G = rename_Prods Original (G0_prods G)"

definition G0R_start :: "('n::infinite,'t) cfg \<Rightarrow> ('n,'t) renamed" where
  "G0R_start G = Original (G0_start G)"


definition "R_func P (A::'n) (a::'t) = {\<beta>. P \<turnstile> [Nt A] \<Rightarrow>l* ((Tm a) # map Nt \<beta>)}"

(* properties that G_A,a has *)
definition G_props :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> ('a,'n) cfg \<Rightarrow> bool" where 
  "G_props G A a G' = (L G' = R_func (set (prods (G0 G))) A a \<and> rlin2 (set (prods G')))"

(* properties that G_A,a has *)
definition G_Props :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> ('a,'n) Cfg \<Rightarrow> bool" where 
  "G_Props G A a G' = (Lang (Prods G') (Start G') = R_func (set (prods (G0 G))) A a \<and> rlin2 (Prods G'))"

definition R_grammar :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> (nat,'n) cfg" where
  "R_grammar G A a = (SOME G'. G_props G A a G')"

definition R_grammar_prods :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> (nat,'n) Prods" where
  "R_grammar_prods G A a = set (prods (R_grammar G A a))"

definition R_grammar_start :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> nat" where
  "R_grammar_start G A a = start (R_grammar G A a)"

definition renamed_R_grammar_prods :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> (('n,'t) renamed,'n) Prods" where
  "renamed_R_grammar_prods G A a = rename_Prods (Renamed A a) (R_grammar_prods G A a)"

definition renamed_R_grammar_start :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> ('n,'t) renamed" where
  "renamed_R_grammar_start G A a = Renamed A a (R_grammar_start G A a)"


definition renamed_R_grammar :: "('n::infinite,'t) cfg \<Rightarrow> 'n \<Rightarrow> 't \<Rightarrow> (('n, 't) renamed, 'n) Cfg" where
  "renamed_R_grammar G A a = Cfg (renamed_R_grammar_prods G A a) (renamed_R_grammar_start G A a)"


definition G_union :: "('n::infinite,'t) cfg \<Rightarrow> (('n,'t) renamed,'n) Prods" where
  "G_union G = (\<Union>A. (\<Union> a. renamed_R_grammar_prods G A a))"

definition G1_new_prods :: "('n::infinite,'t) cfg \<Rightarrow> (('n,'t) renamed,'t) Prods" where
  "G1_new_prods G = map_tms_Prods Original (G_union G)"

definition G1_prods :: "('n::infinite,'t) cfg \<Rightarrow> (('n,'t) renamed,'t) Prods" where
  "G1_prods G = (G0R_prods G) \<union> (G1_new_prods G)"

definition G2_new_prods :: "('n::infinite,'t) cfg \<Rightarrow> (('n,'t) renamed,'t) Prods" where
  "G2_new_prods G = {(A,a'). \<exists>B b Y.
        a' = [Tm b, Nt (renamed_R_grammar_start G B b), Nt Y] \<and>
        (A, [Nt (Original B), Nt Y]) \<in> (G1_prods G)}"

definition G2_retained_prods :: "('n::infinite,'t) cfg \<Rightarrow> (('n,'t) renamed,'t) Prods" where
  "G2_retained_prods G = {P. P \<in> (G1_prods G) \<and> (\<nexists>X B Y. (X, [Nt (Original B), Nt Y]) = P)}"

definition G2_prods :: "('n::infinite,'t) cfg \<Rightarrow> (('n,'t) renamed,'t) Prods" where
  "G2_prods G = (G2_retained_prods G) \<union> (G2_new_prods G)"



(* proof *)

lemma inj_Original: "inj Original"
  unfolding inj_def by blast


lemma exists_G_for_R: "(\<And>A a. (\<exists>G'. G_props G A a G'))"
  (* 
      The Grammar {A' \<longrightarrow> B'C | A \<longrightarrow> BC @ P} \<union> {A' \<longrightarrow> \<epsilon> | A \<longrightarrow> a \<in> P}
      produces the language  R (set (prods G0)) A a
      see Kozen. Automata and Computability pp Lecture 21 (about GNF)

      TODO: specify the grammar, show that it is regular

      apply a lemma which shows that for a regular language there is a grammar
      stronly right linear grammar (that means rlin2 G is true)
   *)
  sorry


(* R_grammar actually satisfies G_props *)
lemma R_grammar_G_props:
  shows "G_props G A a (R_grammar G A a)"
proof -
  have "\<exists>G'. G_props G A a G'" using exists_G_for_R by fast
  then show "G_props G A a (R_grammar G A a)"
    unfolding R_grammar_def G_props_def by (rule someI_ex)
qed


(* renaming of R_grammar preserves its language *)
lemma renamed_R_grammar_Lang_unchanged:
      "Lang (R_grammar_prods G A a) (start (R_grammar G A a)) =
       Lang (renamed_R_grammar_prods G A a) (renamed_R_grammar_start G A a)"
proof -
  let ?P = "(R_grammar_prods G A a)"
  let ?f = "(Renamed A a)"
  have "inj ?f"
    by (meson injI renamed.inject(2))
  then have "\<And>a b. ?P \<turnstile> a \<Rightarrow>* b \<longleftrightarrow> rename_Prods ?f ?P \<turnstile> (rename_syms ?f a) \<Rightarrow>* (rename_syms ?f b)"
    by (rule rename_Prods_derives_iff)
  moreover have "[Nt (?f (R_grammar_start G A a))] = rename_syms ?f [Nt (start (R_grammar G A a))]"
    unfolding R_grammar_start_def by auto
  ultimately show ?thesis unfolding Lang_def renamed_R_grammar_prods_def renamed_R_grammar_start_def
    by (metis map_Tm_rename_syms)
qed


(* renaming of R_grammar preserves its strong right linearity *)
lemma renamed_R_grammar_rlin2: 
    shows "rlin2 (renamed_R_grammar_prods G A a)"
proof -
  from R_grammar_G_props have "rlin2 (R_grammar_prods G A a)"
    unfolding G_props_def R_grammar_prods_def by fast
  then show ?thesis unfolding renamed_R_grammar_prods_def
    by (rule prods_rename_rlin2)
qed


(* Grammars returned by renamed_wittness also adhere to G_props *)
lemma renamed_R_G_Props: "G_Props G A a (renamed_R_grammar G A a)"
  unfolding G_props_def G_Props_def renamed_R_grammar_def
  using renamed_R_grammar_Lang_unchanged renamed_R_grammar_rlin2
  by (metis Cfg.sel(1) Cfg.sel(2) G_props_def R_grammar_G_props R_grammar_prods_def)

(* G0 is in GNF *)
lemma G0_prods_CNF: "CNF (G0_prods G)"
  unfolding G0_prods_def G0_def using some_cnf_cnf by blast




(* The sets of nonterminals of renamed G0 and renamed R_grammar are disjoint *)
lemma Nts_G0R_R_grammar_disjoint: "Nts (G0R_prods G) \<inter> Nts (renamed_R_grammar_prods G A a) = {}"
proof -
  let ?f = "Original" and ?g = "Renamed A a"
  have f_g_disjoint: "range Original \<inter> range (Renamed A a) = {}" by blast
  then have "\<And>ps1 ps2. nts (map (rename_prod ?f) ps1) \<inter> nts (map (rename_prod ?g) ps2) = {}"
    by (simp add: disjoint_iff_not_equal nts_rename_Prods)
  then show ?thesis
    by (simp add: G0R_prods_def f_g_disjoint rename_prods_disjoint renamed_R_grammar_prods_def)
qed


(* The set of nonterminals of renamed G0 and the set of left hand sides of G1 are disjoint *)
lemma Nts_G0R_Lhss_G1: "Nts (G0R_prods G) \<inter> Lhss (G1_new_prods G) = {}"
proof -
  from Nts_G0R_R_grammar_disjoint have "\<And>A a. Nts (G0R_prods G) \<inter> Lhss (renamed_R_grammar_prods G A a) = {}"
    by (meson disjoint_iff fresh_Lhss)
  then have "Nts (G0R_prods G) \<inter> Lhss (G_union G) = {}"
    unfolding G_union_def Lhss_def by blast
  then show ?thesis using map_tms_Prods_Lhss unfolding G_union_def G1_new_prods_def
    by fast
qed

(* The set of nonterminals of renamed_R_grammar cannot contain Original nonterminals *)
lemma Original_not_in_Nts_renamed_R_grammar_prods: "Original S \<notin> Nts (renamed_R_grammar_prods G A a)"
  by (simp add: image_iff nts_rename_Prods renamed_R_grammar_prods_def)


(* The set of nonterminals of G_union cannot contain Original nonterminals *)
lemma Original_not_in_Nts_G_union: "Original S \<notin> Nts (G_union G)"
  using Original_not_in_Nts_renamed_R_grammar_prods nts_rename_Prods
  unfolding G_union_def renamed_R_grammar_prods_def Nts_def
  by fast


(* The set of left hand sides of G_union cannot contain Original nonterminals *)
lemma Original_not_in_Lhss_G_union: "Original S \<notin> Lhss (G_union G)"
  by (simp add: Original_not_in_Nts_G_union fresh_Lhss)


(* There is a leftmmost derivation (to a sequence of terminals)
   in G0 iff there is a leftmost derivation in G1 *)
lemma G0R_deriveln_iff_G1:
      "(G0R_prods G \<turnstile> map (Nt o Original) u \<Rightarrow>l(n) map Tm v) =
                (G1_prods G \<turnstile> map (Nt o Original) u \<Rightarrow>l(n) map Tm v)"
proof -
  have "nts_of_syms (map (Nt o Original) u) \<inter> Lhss (G1_new_prods G) = {}"
    unfolding nts_of_syms_def Lhss_def G1_new_prods_def using Lhss_def Original_not_in_Lhss_G_union 
    by fastforce
  with Nts_G0R_Lhss_G1 show ?thesis
    unfolding G1_prods_def using append_unreachable_productions_deriveln_iff by fast
qed






(* first direction: Each word contained in the CNF grammar is also
   contained in the constructed nearly-GNF grammar
*)
lemma G0_G2:
   assumes assm: "(G0_prods G \<turnstile> (map Nt ss) \<Rightarrow>* map Tm x)"
    shows "(G2_prods G \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* map Tm x)"
proof -
  (* there must be a leftmost derivation *)
  from assm have "(G0_prods G \<turnstile> map Nt ss \<Rightarrow>l* (map Tm x))"
    by (rule derives_tms_imp_derivels)

  (* obtain the length of that derivation *)
  then have "\<exists>n. (G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(n) (map Tm x))"
    by (rule rtranclp_imp_relpowp)
  then obtain n where "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(n) (map Tm x)" by auto

  (* Beginning of the actual induction proof:
     Shows: If there is a leftmost derivation in G1 of length \<le> n
       from any sequence of nonterminals contained in G0R to the terminal word x
       then there must also be a derivation in G2
   *)

  moreover have "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(n) (map Tm x) \<Longrightarrow> 
                   G2_prods G \<turnstile> map (Nt o Original) ss \<Rightarrow>* (map Tm x)"
  proof (induction n arbitrary: ss x rule: nat_induct_leq)
    (* trivial, since both sides of the derivation must be [] *)
    case 0
    then have "map Nt ss = map Tm x"
      by simp
    then have "ss = []"
      by (metis list.map_sel(1) map_is_Nil_conv sym.distinct(1))
    moreover from 0 this have "x = []"
      by simp
    ultimately show ?case by simp
  next
    case (Leq n')
    show ?case
    proof (cases "x = []")
      (* There are no epsilon productions in CNF.
         Thus, the empty word can only be derived if ss = [], in which case n would
         have to be zero
       *)
      case True
      with G0_prods_CNF Leq(2) have "map Nt ss = []"
        using CNF_Eps_free Eps_free_derivels_Nil by (metis list.map_disc_iff relpowp_imp_rtranclp)
      with Leq have False
        by auto
      then show ?thesis by fast
    next
      case False
      then obtain x1 xs where x1_xs: "x = x1 # xs"
        by (meson neq_Nil_conv)
      with Leq(2) have "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(Suc n') Tm x1 # map Tm xs"
        by simp
      then have "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(Suc n') Tm x1 # map Tm xs"
        by simp

      (* obtain the derivation step, in which the first terminal is produced *)

      moreover note G0_prods_CNF
      ultimately obtain T ns n1 n2 where
         step1: "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(n1) Nt T # map Nt ns" and
         step2: "G0_prods G \<turnstile> Nt T # map Nt ns \<Rightarrow>l Tm x1 # map Nt ns" and
         step3: "G0_prods G \<turnstile> Tm x1 # map Nt ns \<Rightarrow>l(n2) Tm x1 # map Tm xs" and
         sum: "n1 + 1 + n2 = Suc n'" using 
            CNF_derivln_first_tm_strong[where 
                    P="G0_prods G"
                and u="ss"
                and n="Suc n'"
                and t="x1"
                and v="map Tm xs"]
        by blast


      (* show that there is an equivalent derivation in G2 for step1 followed by step2 *)
      have "G2_prods G \<turnstile>map (Nt \<circ> Original) ss \<Rightarrow>* Tm x1 # map (Nt \<circ> Original) ns"
      proof (cases n1)
        case 0
        (* if step1 is a derivation of length 0, then step1 and step2 together is only one derivation,
           which is also possible in G2, since it only requires "(Original T, [Tm x1]) \<in> G2_prods G"
         *)

        have "(T, [Tm x1]) \<in> G0_prods G"
        proof -
          from step2 obtain A w u1 u2 where
                 A_w: "(A, w)\<in>G0_prods G"
              and xs: "Nt T # map Nt ns = map Tm u1 @ Nt A # u2"
              and ys: "Tm x1 # map Nt ns = map Tm u1 @ w @ u2"
            unfolding derivel_iff by fast

          (* TODO: this is a pattern used more often, it could be refactored into its own lemma *)
          then have u1: "u1 = []"
            by (metis Nil_is_map_conv hd_append list.sel(1) sym.simps(4))
          with xs have "T = A"
            by auto
          from xs u1 have "map Nt ns = u2"
            by simp
          with u1 ys have "w = [Tm x1]"
            by simp
          from A_w \<open>T = A\<close> \<open>w = [Tm x1]\<close> show "(T, [Tm x1]) \<in> G0_prods G"
            by blast
        qed
        then have "(Original T, [Tm x1]) \<in> G0R_prods G"
          unfolding G0R_prods_def by force
        then have "(Original T, [Tm x1]) \<in> G1_prods G"
          unfolding G1_prods_def by blast
        then have "(Original T, [Tm x1]) \<in> G2_retained_prods G"
          unfolding G2_retained_prods_def by simp
        then have "(Original T, [Tm x1]) \<in> G2_prods G"
          unfolding G2_prods_def by blast
        then have "G2_prods G \<turnstile> Nt (Original T) # map Nt (map Original ns) \<Rightarrow>l Tm x1 # map Nt (map Original ns)"
          by (simp add: derivel_Nt_Cons)

        moreover from 0 step1 have "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(0) Nt T # map Nt ns"
          try by blast
        then have "map Nt (map Original ss) = Nt (Original T) # map Nt (map Original ns)"
          using relpowp_0_E by (smt (verit, best) Cons_eq_map_conv list.inj_map_strong sym.inject(1)) 
      
        then show ?thesis
          by (metis calculation derivels_imp_derives map_map r_into_rtranclp)
      next
        case (Suc n1')
        (* get the first derivation step within step1 *)
        with step1 have "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l(Suc n1') Nt T # map Nt ns" by simp
        then obtain middle where 
                  step1A: "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l middle"
              and step1B: "G0_prods G \<turnstile> middle \<Rightarrow>l(n1') Nt T # map Nt ns"
          using relpowp_Suc_E2 by metis

        then obtain middle_nts where middle_nts: "middle = map Nt middle_nts"
          by (metis deriveln_not_elim_tm list.simps(9))

        with step1B have middle_nts_not_Nil: "middle_nts \<noteq> []"
          by auto

        with step1A have "ss \<noteq> []"
          by auto

        from middle_nts_not_Nil obtain middle_nts1 middle_ntss where middle_nts1: "middle_nts = middle_nts1 # middle_ntss"
          using list.exhaust_sel by blast

        with middle_nts step1B have "G0_prods G \<turnstile> Nt middle_nts1 # map Nt middle_ntss \<Rightarrow>l(n1') map Nt (T # ns)"
          by simp

        moreover from G0_prods_CNF have "Eps_free (G0_prods G)"
          by (rule CNF_Eps_free)

        ultimately obtain Ys' where Ys': "Ys' @ middle_ntss = T # ns \<and> G0_prods G \<turnstile> [Nt middle_nts1] \<Rightarrow>l(n1') map Nt Ys'"
          using deriveln_nts_suffix by fast

        then have "Ys' \<noteq> []"
          (* TODO: make nicer *)
          by (metis Eps_free_derivels_Nil \<open>Eps_free (G0_prods G)\<close> length_0_conv length_map not_Cons_self2 relpowp_imp_rtranclp)

        with Ys' obtain Ys's where Ys's: "Ys' = T # Ys's"
          by (meson append_eq_Cons_conv)

        with Ys' have "G0_prods G \<turnstile> [Nt middle_nts1] \<Rightarrow>l(n1') map Nt (T # Ys's)"
          by blast
        then have "G0_prods G \<turnstile> [Nt middle_nts1] \<Rightarrow>l(n1') Nt T # map Nt (Ys's)"
          by simp

        moreover from step2 have "(T, [Tm x1]) \<in> G0_prods G"
          by (simp add: derivel_Nt_Cons)
        then have "G0_prods G \<turnstile> Nt T # map Nt Ys's \<Rightarrow>l Tm x1 # map Nt Ys's"
          by (simp add: derivel_Nt_Cons)
        ultimately have "G0_prods G \<turnstile> [Nt middle_nts1] \<Rightarrow>l(Suc n1') Tm x1 # map Nt (Ys's)"
          by auto
        then have "G0_prods G \<turnstile> [Nt middle_nts1] \<Rightarrow>l* Tm x1 # map Nt (Ys's)"
          by (rule relpowp_imp_rtranclp)
        then have "G0R_prods G \<turnstile> rename_syms Original [Nt middle_nts1] \<Rightarrow>l* rename_syms Original (Tm x1 # map Nt (Ys's))"
          unfolding G0R_prods_def by (rule rename_Prods_derivels_dir1)
        then have "G0R_prods G \<turnstile> [Nt (Original middle_nts1)] \<Rightarrow>l* Tm x1 # map Nt (map Original Ys's)"
          by (metis (no_types, lifting) map_Nt_rename_syms list.map_disc_iff map_eq_Cons_conv rename_sym.simps(2))
        then have "G0R_prods G \<turnstile> rename_syms Original [Nt middle_nts1] \<Rightarrow>l* Tm x1 # map Nt (map Original Ys's)"
          by simp
        then have "G0R_prods G \<turnstile> rename_syms Original [Nt middle_nts1] \<Rightarrow>l* Tm x1 # rename_syms Original (map Nt Ys's)"
          by (simp only: map_Nt_rename_syms)
        then have "G0R_prods G \<turnstile> rename_syms Original [Nt middle_nts1] \<Rightarrow>l* rename_syms Original (Tm x1 # map Nt Ys's)"
          by simp
        then have "rename_Prods Original (G0_prods G)
                    \<turnstile> rename_syms Original [Nt middle_nts1]
                    \<Rightarrow>l* rename_syms Original (Tm x1 # map Nt Ys's)"
          unfolding G0R_prods_def
          by (metis rename_Prods_derivels_iff inj_Original)

        then have "G0_prods G \<turnstile> [Nt middle_nts1] \<Rightarrow>l* (Tm x1 # map Nt Ys's)"
          using rename_Prods_derivels_iff inj_Original
          by blast

        moreover have "G_Props G middle_nts1 x1 (renamed_R_grammar G middle_nts1 x1)"
          using renamed_R_G_Props by fast
        ultimately have "renamed_R_grammar_prods G middle_nts1 x1
                          \<turnstile> [Nt (renamed_R_grammar_start G middle_nts1 x1)]
                          \<Rightarrow>* map Tm Ys's"
          unfolding R_func_def G_Props_def Lang_def G0_prods_def renamed_R_grammar_def by auto

        then have "G_union G \<turnstile> [Nt (renamed_R_grammar_start G middle_nts1 x1)] \<Rightarrow>* map Tm Ys's"
          unfolding G_union_def by (smt (verit, ccfv_threshold) UnionI image_iff iso_tuple_UNIV_I psubRtcDeriv)

        then have "G1_new_prods G \<turnstile> [Nt (renamed_R_grammar_start G middle_nts1 x1)] \<Rightarrow>* map Nt (map Original Ys's)"
          using map_tms_Prods_derives[where P="G_union G"
                                        and a="[renamed_R_grammar_start G middle_nts1 x1]"
                                        and b="Ys's"
                                        and f=Original]
          unfolding G1_new_prods_def by (simp)

        then have "G1_prods G \<turnstile> [Nt (renamed_R_grammar_start G middle_nts1 x1)] \<Rightarrow>* map Nt (map Original Ys's)"
          unfolding G1_prods_def by (simp add: psubRtcDeriv)

        then have "G2_retained_prods G \<turnstile> [Nt (renamed_R_grammar_start G middle_nts1 x1)] \<Rightarrow>* map Nt (map Original Ys's)"
          sorry (*  
                  This is actually not provable since G2 does not anymore contain productions, which
                    do not yield terminals.
                 *)

        then have "G2_prods G \<turnstile> [Nt (renamed_R_grammar_start G middle_nts1 x1)] \<Rightarrow>* map Nt (map Original Ys's)"
          unfolding G2_prods_def by (metis Un_iff psubRtcDeriv)




        from step1A middle_nts middle_nts1 have "G0_prods G \<turnstile> map Nt ss \<Rightarrow>l Nt middle_nts1 # map Nt middle_ntss"
          by simp

        moreover from this have "ss \<noteq> []"
          by auto
        then obtain ss1 sss where "ss = ss1 # sss"
          by (meson list.exhaust)

        ultimately have "G0_prods G \<turnstile> Nt ss1 # map Nt sss \<Rightarrow>l Nt middle_nts1 # map Nt middle_ntss"
          by simp
        then have "G0_prods G \<turnstile> Nt ss1 # map Nt sss \<Rightarrow>l map Nt (middle_nts1 # middle_ntss)"
          by simp

        then obtain prefix where "prefix @ sss = middle_nts1 # middle_ntss"
                                 "G0_prods G \<turnstile> [Nt ss1] \<Rightarrow>l map Nt prefix"
          using derivel_nts_suffix by fast
        then have "(ss1, map Nt prefix) \<in> G0_prods G"
          by (simp add: derivel_Nt_Cons)

        note \<open>G0_prods G \<turnstile> Nt ss1 # map Nt sss \<Rightarrow>l map Nt (middle_nts1 # middle_ntss)\<close>
        then obtain middle_ntss1 middle_ntsss
          where "middle_ntss = middle_ntss1 # middle_ntsss"
            and "[middle_nts1, middle_ntss1] = prefix"
          using \<open>G0_prods G \<turnstile> [Nt ss1] \<Rightarrow>l map Nt prefix\<close> 
          \<open>G0_prods G \<turnstile> [Nt ss1] \<Rightarrow>l map Nt prefix\<close>
        sorry (* can be obtained due to CNF *)

        moreover from \<open>(ss1, map Nt prefix) \<in> G0_prods G\<close>
        have "(Original ss1, map Nt (map Original prefix)) \<in> G0R_prods G"
          unfolding G0R_prods_def by force
        ultimately have "(Original ss1, [Nt (Original middle_nts1), Nt (Original middle_ntss1)]) \<in> G1_prods G"
          unfolding G1_prods_def by auto

        then have "(Original ss1, [Tm x1, Nt (renamed_R_grammar_start G middle_nts1 x1), Nt (Original middle_ntss1)]) \<in> G2_new_prods G"
          unfolding G2_new_prods_def by blast

        then have "G2_prods G \<turnstile> Nt (Original ss1) # map Nt (map Original sss)
                                \<Rightarrow>* [Tm x1, Nt (renamed_R_grammar_start G middle_nts1 x1), Nt (Original middle_ntss1)] @ map Nt (map Original sss)"
          unfolding G2_prods_def by (simp add: derivel_Nt_Cons derivel_imp_derive r_into_rtranclp)

        moreover from \<open>G2_prods G \<turnstile> [Nt (renamed_R_grammar_start G middle_nts1 x1)] \<Rightarrow>* map Nt (map Original Ys's)\<close>
        have "G2_prods G \<turnstile> [Tm x1, Nt (renamed_R_grammar_start G middle_nts1 x1)] \<Rightarrow>* Tm x1 # map Nt (map Original Ys's)"
          by (rule derives_Cons)
        then have "G2_prods G \<turnstile> [Tm x1, Nt (renamed_R_grammar_start G middle_nts1 x1), Nt (Original middle_ntss1)] \<Rightarrow>* Tm x1 # map Nt ((map Original Ys's)) @ [Nt (Original middle_ntss1)]"
          by (metis append.left_neutral append_Cons derives_append)
        then have "G2_prods G \<turnstile> [Tm x1, Nt (renamed_R_grammar_start G middle_nts1 x1), Nt (Original middle_ntss1)] @ map Nt (map Original sss) \<Rightarrow>* Tm x1 # map Nt ((map Original Ys's)) @ [Nt (Original middle_ntss1)] @ map Nt (map Original sss)"
           by (metis Cons_eq_appendI append_assoc derives_append)

        ultimately have "G2_prods G \<turnstile> Nt (Original ss1) # map Nt (map Original sss)
                                \<Rightarrow>* Tm x1 # map Nt (map Original Ys's) @ Nt (Original middle_ntss1) # map Nt (map Original sss)"
          by simp
        then have "G2_prods G \<turnstile> Nt (Original ss1) # map Nt (map Original sss)
                                \<Rightarrow>* Tm x1 # map Nt (map Original Ys's @ (Original middle_ntss1) # map Original sss)"
          by simp
        with \<open>ss = ss1 # sss\<close> have "G2_prods G \<turnstile> map Nt (map Original ss)
                                \<Rightarrow>* Tm x1 # map Nt (map Original Ys's @ (Original middle_ntss1) # map Original sss)"
          by simp

        moreover have "map Original Ys's @ (Original middle_ntss1) # (map Original sss) = map Original ns"
          using Ys' Ys's \<open>[middle_nts1, middle_ntss1] = prefix\<close> \<open>prefix @ sss = middle_nts1 # middle_ntss\<close> by force
        ultimately have "G2_prods G \<turnstile> map (Nt \<circ> Original) ss \<Rightarrow>* Tm x1 # map Nt (map Original ns)"
          by (metis map_map)
        then have "G2_prods G \<turnstile> map (Nt \<circ> Original) ss \<Rightarrow>* Tm x1 # map (Nt \<circ> Original) ns"
          by simp
        then show ?thesis by simp
      qed

      (* show that there is an equivalent derivation in G2 for step3 *)
      moreover have "G2_prods G \<turnstile> Tm x1 # map (Nt \<circ> Original) ns \<Rightarrow>* map Tm x"
      proof -
        from step3 have "G0_prods G \<turnstile> map Nt ns \<Rightarrow>l(n2) map Tm xs"
          by (simp add: deriveln_Tm_Cons)
        then have "G0R_prods G \<turnstile> rename_syms Original (map Nt ns) \<Rightarrow>l(n2) rename_syms Original (map Tm xs)"
          unfolding G0R_prods_def by (rule rename_Prods_deriveln_dir1)
        then have "G0R_prods G \<turnstile> map Nt (map Original ns) \<Rightarrow>l(n2) map Tm xs"
          using map_Nt_rename_syms map_Tm_rename_syms by metis
        then have  "G1_prods G \<turnstile> map Nt (map Original ns) \<Rightarrow>l(n2) map Tm xs"
          using G0R_deriveln_iff_G1 by auto
        moreover from sum have "n2 \<le> n'" by auto
        moreover note Leq.IH
        ultimately have "G2_prods G \<turnstile> map (Nt \<circ> Original) ns \<Rightarrow>* map Tm xs"
          using \<open>G0_prods G \<turnstile> map Nt ns \<Rightarrow>l(n2) map Tm xs\<close> by blast
        then have "G2_prods G \<turnstile> Tm x1 # map (Nt \<circ> Original) ns \<Rightarrow>* Tm x1 # map Tm xs"
          by (rule derives_Cons)
        then show "G2_prods G \<turnstile> Tm x1 # map (Nt \<circ> Original) ns \<Rightarrow>* map Tm x"
          using x1_xs by simp
      qed

      ultimately show ?thesis
        by (rule rtranclp_trans)
    qed
  qed

  ultimately show "(G2_prods G \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* map Tm x)" by fast
qed


(* first direction: Each word contained in the nearly-GNF grammar is also
   contained in the constructed CNF grammar
*)
lemma G2_G0:
   assumes assm: "(G2_prods G \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* map Tm x)"
    shows "(G0_prods G \<turnstile> (map Nt ss) \<Rightarrow>* map Tm x)"
  sorry


lemma G0_iff_G2: "(G0_prods G \<turnstile> (map Nt ss) \<Rightarrow>* map Tm x) \<longleftrightarrow> (G2_prods G \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* map Tm x)"
  using G0_G2 G2_G0 by blast

(* main theorem *)
theorem gnf_exists:
  shows "\<forall>G::('n::infinite,'t) cfg. \<exists>G0::('n,'t) cfg. (gnf G0) \<and> (L G0 = L G - {[]})"
proof -
  fix G::"('n::infinite,'t) cfg"
  have "\<And>ss x. (G0_prods G \<turnstile> (map Nt ss) \<Rightarrow>* map Tm x) \<longleftrightarrow> (G2_prods G \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* map Tm x)"
    using G0_iff_G2 by blast

  have "Lang (G0_prods G) (G0_start G) = Lang (G2_prods G) (Original (G0_start G))"
  proof (unfold Lang_def, rule Collect_eqI, standard)
    fix x
    assume "G0_prods G \<turnstile> [Nt (G0_start G)] \<Rightarrow>* map Tm x"
    then show "G2_prods G \<turnstile> [Nt (Original (G0_start G))] \<Rightarrow>* map Tm x"
      using G0_G2
      by (metis (no_types, lifting) Nil_is_map_conv comp_apply list.simps(9)) 
  next
    fix x
    assume "G2_prods G \<turnstile> [Nt (Original (G0_start G))] \<Rightarrow>* map Tm x"
    then show "G0_prods G \<turnstile> [Nt (G0_start G)] \<Rightarrow>* map Tm x" 
      using G2_G0
      by (metis (no_types, lifting) Nil_is_map_conv comp_apply list.simps(9)) 
  qed

  (* G2 is not yet in GNF, since it can contain epsilon-productions *)
  (* TODO: prove, that eliminating epsilon-productions does not yield unit productions
      and thus yields a grammar equivalent to G in GNF
   *)

  show ?thesis sorry
qed


(* convenience function to obtain a GNF grammar *)
definition some_gnf :: "('n::infinite,'t) cfg \<Rightarrow> ('n,'t) cfg" where
  "some_gnf G = (SOME G'. (gnf G') \<and> (L G' = L G - {[]}))"

(* proof for the convenience function *)
lemma some_gnf_gnf: "gnf (some_gnf (G::('n::infinite,'t) cfg)) \<and> L (some_gnf G) = L G - {[]}"
proof -
  from gnf_exists have "\<exists>(G'::('n::infinite,'t) cfg). gnf G' \<and> L G' = L G - {[]}" by blast
  then show ?thesis unfolding some_gnf_def by (rule someI_ex)
qed







(* another idea that might be the base of a proof for G0_G2.
   Maybe joining the induction hypotheses of G0_G2 and G0_G2_try2 via \<and>
   could yield an induction that is better provable.
 *)
lemma G0_G2_try2: "ns \<in> R_func (set (prods (G0 G))) A a
      \<Longrightarrow> (G0_prods G) \<turnstile> map (Nt) ns \<Rightarrow>* map Tm ts
      \<Longrightarrow> length ts = n
      \<Longrightarrow> (G2_prods G) \<turnstile> [Nt (renamed_R_grammar_start G A a)] \<Rightarrow> map Tm ts"
proof (induction n arbitrary: A a ns ts)
  case 0
  then have "ts = []" by simp
  moreover from G0_prods_CNF have "Eps_free (G0_prods G)"
    using CNF_Eps_free by blast
  with \<open>ts = []\<close> 0 have "ns = []" unfolding CNF_def
    by (simp add: Eps_free_derives_Nil)
  have "Lang (renamed_R_grammar_prods G A a) (renamed_R_grammar_start G A a) = R_func (set (prods (G0 G))) A a"
    by (metis Cfg.sel(1) Cfg.sel(2) G_Props_def renamed_R_G_Props renamed_R_grammar_def)
  with 0 \<open>ns = []\<close> have "[] \<in> Lang (renamed_R_grammar_prods G A a) (renamed_R_grammar_start G A a)" by simp
  with renamed_R_grammar_rlin2 have "((renamed_R_grammar_start G A a), []) \<in> (renamed_R_grammar_prods G A a)"
    unfolding rlin2_def sorry (*since R_grammar is strongly right linear, it can only produce empty words directly,
                                since all other productions add terminals*)
  then have "((renamed_R_grammar_start G A a), []) \<in> (G_union G)"
    unfolding G_union_def by blast
  then have "((renamed_R_grammar_start G A a), []) \<in> (G1_new_prods G)"
    unfolding G1_new_prods_def by force
  then have "((renamed_R_grammar_start G A a), []) \<in> (G1_prods G)"
    unfolding G1_prods_def by blast
  then have "((renamed_R_grammar_start G A a), []) \<in> (G2_retained_prods G)"
    unfolding G2_retained_prods_def by blast
  then have "((renamed_R_grammar_start G A a), []) \<in> (G2_prods G)"
    unfolding G2_prods_def by blast
  then show ?case
    using "0.prems"(3) derive_singleton by auto

(* TODO: another base case for n=1 has to be manually proven*)

next
  case (Suc n)
  then show ?case sorry

  (* get the first leftmost derivation step *)
  (* since G0 is in CNF, either one terminal or two nonterminals are produced *)
  (* if two nonterminals are produced: then ts can be split into two non-empty terminal sequences.
     Also, on the G2_side, there has to be a production, in which the first terminal is replaced by
      [Tm b, Nt T_b,B] where b is the first character of ts.
     For the first nonterminal, the induction hypothesis of G0_G2_try2 can be used.
     For the second nonterminal a stronger induction hypothesis may be needed which also
      includes the induction hypothesis of G0_G2.
   *)

qed



end