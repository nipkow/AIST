theory GNF
  imports cfg_renaming cfg_merging util derivel_nts cfg_util map_tms cnf_induct
begin


(* currently, only one direction is proven (apart from a few sorries for small proofs) *)
(* The core of the proof needs plenty of garbage collection and redesign *)
(* Especially, it would be easier to show the equivalence of G0 and G2 directly, without G1,
   which saves a lot of tinkering with Original / Renamed
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



lemma map_rename_syms: "map Nt (map f xs) = rename_syms f (map Nt xs)"
  by simp


definition "R_func P (A::'n) (a::'t) = {\<beta>. P \<turnstile> [Nt A] \<Rightarrow>l* ((Tm a) # map Nt \<beta>)}"

(* properties that G_A,a has *)
definition "G_props (A::'n) (a::'t) G0 G = (L G = R_func (set (prods G0)) A a \<and> rlin2 (set (prods G)))"

lemma exists_G_for_R: "cnf G0 \<Longrightarrow> (\<And>A a. (\<exists>G. G_props A a G0 G))"
  (* 
      The Grammar {A' \<longrightarrow> B'C | A \<longrightarrow> BC @ P} \<union> {A' \<longrightarrow> \<epsilon> | A \<longrightarrow> a \<in> P}
      produces the language  R (set (prods G0)) A a
      see Kozen. Automata and Computability pp Lecture 21 (about GNF)

      TODO: specify the grammar, show that it is regular

      apply a lemma which shows that for a regular language there is a grammar
      stronly right linear grammar (that means rlin2 G is true)
   *)
  sorry




definition "some_G_for_R (A::'n) (a::'t) G0 \<equiv> 
  SOME G. G_props A a G0 G"

lemma some_G_for_R_props:
  assumes "cnf G0"
    shows "G_props A a G0 (some_G_for_R A a G0)"
proof -
  from assms have "\<exists>G. G_props A a G0 G" using exists_G_for_R by fast
  then show "G_props A a G0 (some_G_for_R A a G0)"
    unfolding some_G_for_R_def G_props_def by (rule someI_ex)
qed

lemma some_G_for_R_Lang: "cnf G0 \<Longrightarrow> L (some_G_for_R A a G0) = R_func (set (prods G0)) A a"
  using some_G_for_R_props unfolding G_props_def by fast

lemma some_G_for_R_rlin2: "cnf G0 \<Longrightarrow> rlin2 (set (prods (some_G_for_R A a G0)))"
  using some_G_for_R_props unfolding G_props_def by fast



datatype ('n, 't) renamed = Original 'n | Renamed 'n 't nat

lemma inj_Original: "inj Original"
  unfolding inj_def by blast

definition "removed_from_G2 P = (\<exists>X B Y. (X, [Nt (Original B), Nt Y]) = P)"

definition "original_sym s \<equiv> (\<exists>nt. s = Nt (Original nt)) \<or> (\<exists>tm. s = Tm tm)"
abbreviation "original_syms ss \<equiv> \<forall>s \<in> (set ss). original_sym s"  



lemma derivel_not_elim_tm:
  assumes "P \<turnstile> xs \<Rightarrow>l map Nt ys"
  shows "\<exists>xs'. xs = map Nt xs'"
proof -
  from assms have "(\<exists>(A, w)\<in>P. \<exists>u1 u2. xs = map Tm u1 @ Nt A # u2 \<and> map Nt ys = map Tm u1 @ w @ u2)"
    by (simp only: derivel_iff)
  then obtain A w u1 u2 where
         A_w: "(A, w)\<in>P"
      and xs: "xs = map Tm u1 @ Nt A # u2"
      and ys: "map Nt ys = map Tm u1 @ w @ u2"
    by fast

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
  from \<open>P \<turnstile> Nt X # map Nt Xs \<Rightarrow>l map Nt Ys\<close> have
      "\<exists>(A, w)\<in>P. \<exists>u1 u2. Nt X # map Nt Xs = map Tm u1 @ Nt A # u2 \<and> map Nt Ys = map Tm u1 @ w @ u2"
    by (simp only: derivel_iff)
  then obtain A w u1 u2 where
           A_w: "(A, w)\<in>P"
      and X_Xs: "Nt X # map Nt Xs = map Tm u1 @ Nt A # u2"
      and Ys: "map Nt Ys = map Tm u1 @ w @ u2"
    by fast

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
    by auto

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
        using derivel_append by fastforce
      then have "P \<turnstile> [Nt X] \<Rightarrow>l(Suc n) map Nt (Ys'2 @ Ys'1s)"
        by simp 

      ultimately show ?thesis
        by auto
    qed
  qed
qed






(*  TODO: once, the core of the proof is done,
    identify dependencies between facts and extract `have`s into lemmas *)
theorem gnf_exists:
  shows "\<forall>G::('n::infinite,'t) cfg. \<exists>G0::('n,'t) cfg. (gnf G0) \<and> (L G0 = L G - {[]})"
proof -
  fix G

  (* obtain a grammar for L G that is in CNF *)
  obtain G0 where G0_def: "G0 = some_cnf (G::('n::infinite,'t) cfg)" by fast
  then have cnf: "(cnf (G0::('n,'t) cfg))"
        and cnf_L_eq: "(L G0 = L (G::('n::infinite,'t) cfg) - {[]})"
    using some_cnf_cnf by fast+

  (* witness function for G_A,a. The grammars adhere to G_props *)
  obtain witness where witness: "(\<And>A a. (let G = (witness:: 'n \<Rightarrow> 't \<Rightarrow> (nat,'n) cfg) A a in G_props A a G0 G))"
    by (meson exists_G_for_R cnf)

  (* Derive a witness function for G_A,a
     that renames the nonterminals to ensure that these are disjoint *)
  obtain renamed_wittness where renamed_wittness_def: "renamed_wittness = (\<lambda> A a. (rename_cfg (Renamed A a)) (witness A a))" by simp
  
  (* Grammars returned by renamed_wittness also adhere to G_props *)
  then have renamed_wittness_G_props: "(\<And>A a. (let G = renamed_wittness A a in G_props A a G0 G))"
    by (smt (verit) G_props_def cfg_rename_L cfg_rename_rlin2 witness injI renamed.inject(2))

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
      (\<Union>A. (\<Union> a. set(prods (renamed_wittness A a))))"
    by fast
  let ?G1_new_prods = "map_tms_Prods Original G_union"
  let ?G0R_prods = "set (prods G0R)"
  let ?G1_prods = "?G0R_prods \<union> ?G1_new_prods"
  (* TODO: skip G1 *)

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



  have G0R_deriveln_iff_G1:
      "\<And>u n v. (?G0R_prods \<turnstile> map (Nt o Original) u \<Rightarrow>l(n) map Tm v) =
                (?G1_prods \<turnstile> map (Nt o Original) u \<Rightarrow>l(n) map Tm v)"
  proof -
    fix u n v
    note \<open>Nts ?G0R_prods \<inter> Lhss ?G1_new_prods = {}\<close>
    moreover have "nts_of_syms (map (Nt o Original) u) \<inter> Lhss ?G1_new_prods = {}"
      unfolding nts_of_syms_def Lhss_def using Lhss_def \<open>\<And>S. Original S \<notin> Lhss G_union\<close> by fastforce
    ultimately show "(?G0R_prods \<turnstile> map (Nt o Original) u \<Rightarrow>l(n) map Tm v) =
                     (?G1_prods \<turnstile> map (Nt o Original) u \<Rightarrow>l(n) map Tm v)"
      using append_unreachable_productions_deriveln_iff by blast
  qed

  then have G0R_derivels_iff_G1:
      "\<And>u v. (?G0R_prods \<turnstile> map (Nt o Original) u \<Rightarrow>l* map Tm v) =
                (?G1_prods \<turnstile> map (Nt o Original) u \<Rightarrow>l* map Tm v)"
    by (simp add: rtranclp_power)


  (* first direction *)
  have G1_G2: "\<And>ss x. (?G1_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* map Tm x) \<Longrightarrow>
                      (?G2_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* map Tm x)"
  proof -
    fix ss x
    assume assm: "(?G1_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x))"
    let ?ntss = "map (Nt o Original) ss"

    (* there must be a leftmost derivation *)
    from assm have "(?G1_prods \<turnstile> ?ntss \<Rightarrow>l* (map Tm x))"
      by (rule derives_tms_imp_derivels)

    (* obtain the length of that derivation *)
    then have "\<exists>n. (?G1_prods \<turnstile> ?ntss \<Rightarrow>l(n) (map Tm x))"
      by (rule rtranclp_imp_relpowp)
    then obtain n where "?G1_prods \<turnstile> ?ntss \<Rightarrow>l(n) (map Tm x)" by auto

    (* unused

    (* Beginning of the actual induction proof:
       Shows: If there is a leftmost derivation in G1 of length \<le> n
         from any sequence of nonterminals contained in G0R to the terminal word x
         then there must also be a derivation in G2
     *)
    moreover have "?G1_prods \<turnstile> map (Nt o Original) ss \<Rightarrow>l* (map Tm x) \<Longrightarrow> 
                   ?G2_prods \<turnstile> map (Nt o Original) ss \<Rightarrow>* (map Tm x)"
    proof -
      assume "?G1_prods \<turnstile> map (Nt o Original) ss \<Rightarrow>l* (map Tm x)"
      then have "?G0R_prods \<turnstile> map (Nt o Original) ss \<Rightarrow>l* map Tm x"
        using G0R_derivels_iff_G1 by fast

      moreover note \<open>CNF ?G0R_prods\<close>
      ultimately show "?G2_prods \<turnstile> map (Nt o Original) ss \<Rightarrow>* (map Tm x)"
      proof (induction rule: cnf_derivels_induct)
        case base
        then show ?case by simp
      next
        case (step_nt_nt u A v B C)
        then show ?case sorry 
      next
        case (step_tm u A v t)
        then show ?case sorry  (* productions of this type are still contained *)
      qed
    qed

    *)


    (* Beginning of the actual induction proof:
       Shows: If there is a leftmost derivation in G1 of length \<le> n
         from any sequence of nonterminals contained in G0R to the terminal word x
         then there must also be a derivation in G2
     *)
    moreover have "?G1_prods \<turnstile> map (Nt o Original) ss \<Rightarrow>l(n) (map Tm x) \<Longrightarrow> 
                   ?G2_prods \<turnstile> map (Nt o Original) ss \<Rightarrow>* (map Tm x)"
    proof (induction n arbitrary: ss x rule: nat_induct_leq)
      case 0
      (* trivial, since both sides of the derivation must be [] *)
      then show ?case by simp
    next
      case (Leq n')
      let ?ntsss = "map (Nt o Original) ss"
      from Leq have in_G0R: "?G0R_prods \<turnstile> ?ntsss \<Rightarrow>l(Suc n') map Tm x"
        using G0R_deriveln_iff_G1 by blast

      show ?case
      proof (cases "x = []")
        (* There are no epsilon productions in CNF.
           Thus, the empty word can only be derived if ss = [], in which case n would
           have to be zero
         *)
        case True
        with \<open>cnf G0R\<close> Leq(2) have "map (Nt \<circ> Original) ss = []"
          using CNF_Eps_free Eps_free_derivels_Nil by (metis in_G0R list.map_disc_iff relpowp_imp_rtranclp)
        with Leq have False
          by auto
        then show ?thesis by fast
      next
        case False
        then obtain x1 xs where x1_xs: "x = x1 # xs"
          by (meson neq_Nil_conv)
        with \<open>?G0R_prods \<turnstile> ?ntsss \<Rightarrow>l(Suc n') map Tm x\<close> have "?G0R_prods \<turnstile> ?ntsss \<Rightarrow>l(Suc n') Tm x1 # map Tm xs"
          by simp
        then have "?G0R_prods \<turnstile> map Nt (map Original ss) \<Rightarrow>l(Suc n') Tm x1 # map Tm xs"
          by simp

        moreover note \<open>CNF ?G0R_prods\<close>
        ultimately obtain T ns n1 n2 where
           step1: "?G0R_prods \<turnstile> map Nt (map Original ss) \<Rightarrow>l(n1) Nt T # map Nt ns" and
           step2: "?G0R_prods \<turnstile> Nt T # map Nt ns \<Rightarrow>l Tm x1 # map Nt ns" and
           step3: "?G0R_prods \<turnstile> Tm x1 # map Nt ns \<Rightarrow>l(n2) Tm x1 # map Tm xs" and
           sum: "n1 + 1 + n2 = Suc n'" using 
              CNF_derivln_first_tm_strong[where 
                      P="?G0R_prods"
                  and u="(map Original ss)"
                  and n="Suc n'"
                  and t="x1"
                  and v="map Tm xs"]
          by blast

        then obtain T' where T': "T = Original T'"
          (* provable since T is a result of a derivation in ?G0R_prods starting from Original nonterminals*)
          sorry

        then obtain ns' where ns': "ns = map Original ns'"
          (* provable since ns is a result of a derivation in ?G0R_prods starting from Original nonterminals*)
          sorry


        have "?G2_prods \<turnstile>map (Nt \<circ> Original) ss \<Rightarrow>* Tm x1 # map (Nt \<circ> Original) ns'"
        proof (cases n1)
          case 0

        (*
          from step2 have "(T, [Tm x1]) \<in> ?G0R_prods"
            by (smt (verit, best) Cons_eq_append_conv append_self_conv2 derivel.simps list.inject not_Cons_self2 sym.distinct(1) sym.inject(1))
        *)

          have "(T, [Tm x1]) \<in> ?G0R_prods"
          proof -
            from step2 have "(\<exists>(A, w)\<in>?G0R_prods. \<exists>u1 u2. 
                Nt T # map Nt ns = map Tm u1 @ Nt A # u2 \<and> 
                Tm x1 # map Nt ns = map Tm u1 @ w @ u2)"
              by (simp only: derivel_iff)
            then obtain A w u1 u2 where
                   A_w: "(A, w)\<in>?G0R_prods"
                and xs: "Nt T # map Nt ns = map Tm u1 @ Nt A # u2"
                and ys: "Tm x1 # map Nt ns = map Tm u1 @ w @ u2"
              by fast
  
            (* TODO: this is a pattern used more often, it could be refactored into its own lemma *)
            then have u1: "u1 = []"
              by (metis Nil_is_map_conv hd_append list.sel(1) sym.simps(4))
            with xs have "T = A"
              by auto
            from xs u1 have "map Nt ns = u2"
              by simp
            with u1 ys have "w = [Tm x1]"
              by simp
            from A_w \<open>T = A\<close> \<open>w = [Tm x1]\<close> show "(T, [Tm x1]) \<in> ?G0R_prods"
              by blast
          qed
          then have "(T, [Tm x1]) \<in> ?G1_prods"
            by blast
          then have "(T, [Tm x1]) \<in> G2_retained_prods"
            unfolding G2_retained_prods_def removed_from_G2_def by simp
          then have "(T, [Tm x1]) \<in> ?G2_prods"
            by blast
          then have "?G2_prods \<turnstile> Nt T # map Nt ns \<Rightarrow>l Tm x1 # map Nt ns"
            by (simp add: derivel_Nt_Cons)

          moreover from 0 step1 have "set (prods G0R) \<turnstile> map Nt (map Original ss) \<Rightarrow>l(0) Nt T # map Nt ns"
            by blast
          then have "map Nt (map Original ss) = Nt T # map Nt ns"
            using relpowp_0_E by (smt (verit, best) Cons_eq_map_conv list.inj_map_strong sym.inject(1)) 
        
          then show ?thesis
            by (metis calculation derivels_imp_derives map_map ns' r_into_rtranclp)
        next
          case (Suc n1')
          with step1 have "?G0R_prods \<turnstile> map Nt (map Original ss) \<Rightarrow>l(Suc n1') Nt T # map Nt ns" by simp
          then obtain middle where 
                    step1A: "?G0R_prods \<turnstile> map Nt (map Original ss) \<Rightarrow>l middle"
                and step1B: "?G0R_prods \<turnstile> middle \<Rightarrow>l(n1') Nt T # map Nt ns"
            using relpowp_Suc_E2 by metis

          then obtain middle_nts where middle_nts: "middle = map Nt middle_nts"
            by (metis deriveln_not_elim_tm list.simps(9))

          with step1B have middle_nts_not_Nil: "middle_nts \<noteq> []"
            by auto

          with step1A have "ss \<noteq> []"
            by auto

          from middle_nts_not_Nil obtain middle_nts1 middle_ntss where middle_nts1: "middle_nts = middle_nts1 # middle_ntss"
            using list.exhaust_sel by blast

          with middle_nts step1B have "?G0R_prods \<turnstile> Nt middle_nts1 # map Nt middle_ntss \<Rightarrow>l(n1') map Nt (T # ns)"
            by simp

          moreover from \<open>CNF ?G0R_prods\<close> have "Eps_free ?G0R_prods"
            by (rule CNF_Eps_free)

          ultimately obtain Ys' where Ys': "Ys' @ middle_ntss = T # ns \<and> ?G0R_prods \<turnstile> [Nt middle_nts1] \<Rightarrow>l(n1') map Nt Ys'"
            using deriveln_nts_suffix by fast
  
          then have "Ys' \<noteq> []"
            (* TODO: make nicer *)
            by (metis Eps_free_derivels_Nil \<open>Eps_free (set (prods G0R))\<close> length_0_conv length_map not_Cons_self2 relpowp_imp_rtranclp)

          with Ys' obtain Ys's where Ys's: "Ys' = T # Ys's"
            by (meson append_eq_Cons_conv)

          with Ys' have "?G0R_prods \<turnstile> [Nt middle_nts1] \<Rightarrow>l(n1') map Nt (T # Ys's)"
            by blast
          then have "?G0R_prods \<turnstile> [Nt middle_nts1] \<Rightarrow>l(n1') Nt T # map Nt (Ys's)"
            by simp

          moreover from step2 have "(T, [Tm x1]) \<in> ?G0R_prods"
            by (simp add: derivel_Nt_Cons)
          then have "?G0R_prods \<turnstile> Nt T # map Nt Ys's \<Rightarrow>l Tm x1 # map Nt Ys's"
            by (simp add: derivel_Nt_Cons)
          ultimately have "?G0R_prods \<turnstile> [Nt middle_nts1] \<Rightarrow>l(Suc n1') Tm x1 # map Nt (Ys's)"
            by auto
          then have "?G0R_prods \<turnstile> [Nt middle_nts1] \<Rightarrow>l* Tm x1 # map Nt (Ys's)"
            by (rule relpowp_imp_rtranclp)

          obtain Ys's' where Ys's': "Ys's = map Original Ys's'"
            sorry (* provable since ?G0R_prods only contains original nonterminals *)

          from middle_nts step1A have "\<exists>middle_nts'. middle_nts = map Original middle_nts'"
            sorry (* provable since ?G0R_prods only contains original nonterminals *)

          then obtain middle_nts1' where middle_nts1': "middle_nts1 = Original middle_nts1'"
            using middle_nts1 by blast

          with \<open>?G0R_prods \<turnstile> [Nt middle_nts1] \<Rightarrow>l* Tm x1 # map Nt (Ys's)\<close> Ys's'
          have "?G0R_prods \<turnstile> [Nt (Original middle_nts1')] \<Rightarrow>l* Tm x1 # map Nt (map Original Ys's')"
            by simp
          then have "?G0R_prods \<turnstile> rename_syms Original [Nt middle_nts1'] \<Rightarrow>l* Tm x1 # map Nt (map Original Ys's')"
            by simp
          then have "?G0R_prods \<turnstile> rename_syms Original [Nt middle_nts1'] \<Rightarrow>l* Tm x1 # rename_syms Original (map Nt Ys's')"
            by (simp only: map_rename_syms)
          then have "?G0R_prods \<turnstile> rename_syms Original [Nt middle_nts1'] \<Rightarrow>l* rename_syms Original (Tm x1 # map Nt Ys's')"
            by simp
          then have "set (rename_prods Original (prods (G0)))
                      \<turnstile> rename_syms Original [Nt middle_nts1']
                      \<Rightarrow>l* rename_syms Original (Tm x1 # map Nt Ys's')"
            unfolding G0R_def
            by (metis cfg_rename_derivels_iff inj_Original prods_rename_cfg_rename_prods)

          then have "set (prods (G0)) \<turnstile> [Nt middle_nts1'] \<Rightarrow>l* (Tm x1 # map Nt Ys's')"
            using cfg_rename_derivels_iff inj_Original
            by blast

          then have "Ys's' \<in> R_func (set (prods G0)) middle_nts1' x1"
            unfolding R_func_def by blast
          moreover have "G_props middle_nts1' x1 G0 (renamed_wittness middle_nts1' x1)"
            using renamed_wittness_G_props by auto
          ultimately have "set (prods (renamed_wittness middle_nts1' x1))
                            \<turnstile> [Nt (start (renamed_wittness middle_nts1' x1))]
                            \<Rightarrow>* map Tm Ys's'"
            unfolding R_func_def G_props_def Lang_def by auto

          then have "G_union \<turnstile> [Nt (start (renamed_wittness middle_nts1' x1))] \<Rightarrow>* map Tm Ys's'"
            unfolding G_union_def by (smt (verit, ccfv_threshold) UnionI image_iff iso_tuple_UNIV_I psubRtcDeriv)

          then have "?G1_new_prods \<turnstile> [Nt (start (renamed_wittness middle_nts1' x1))] \<Rightarrow>* map Nt (map Original Ys's')"
            using map_tms_Prods_derivel[where P=G_union
                                          and a="[start (renamed_wittness middle_nts1' x1)]"
                                          and b="Ys's'"
                                          and f=Original]
            by simp

          then have "?G1_prods \<turnstile> [Nt (start (renamed_wittness middle_nts1' x1))] \<Rightarrow>* map Nt (map Original Ys's')"
            by (metis Un_iff psubRtcDeriv)

          then have "G2_retained_prods \<turnstile> [Nt (start (renamed_wittness middle_nts1' x1))] \<Rightarrow>* map Nt (map Original Ys's')"
            sorry (*  no production used for this derivation has an Original nonterminal on its left hand side
                      \<rightarrow> thus none of these productions has been removed
                      rather difficult to prove, probably it is easier to not use define a G1 at all
                   *)

          then have "?G2_prods \<turnstile> [Nt (start (renamed_wittness middle_nts1' x1))] \<Rightarrow>* map Nt (map Original Ys's')"
            by (metis Un_iff psubRtcDeriv)




          from step1A middle_nts middle_nts1 have "?G0R_prods \<turnstile> map Nt (map Original ss) \<Rightarrow>l Nt middle_nts1 # map Nt middle_ntss"
            by simp

          moreover from this have "ss \<noteq> []"
            by auto
          then obtain ss1 sss where "ss = ss1 # sss"
            by (meson list.exhaust)

          ultimately have "?G0R_prods \<turnstile> Nt (Original ss1) # map Nt (map Original sss) \<Rightarrow>l Nt middle_nts1 # map Nt middle_ntss"
            by simp
          then have "?G0R_prods \<turnstile> Nt (Original ss1) # map Nt (map Original sss) \<Rightarrow>l map Nt (middle_nts1 # middle_ntss)"
            by simp

          then obtain prefix where "prefix @ map Original sss = middle_nts1 # middle_ntss"
                                   "?G0R_prods \<turnstile> [Nt (Original ss1)] \<Rightarrow>l map Nt prefix"
            using derivel_nts_suffix by fast
          then have "(Original ss1, map Nt prefix) \<in> ?G0R_prods"
            by (simp add: derivel_Nt_Cons)

          note \<open>?G0R_prods \<turnstile> Nt (Original ss1) # map Nt (map Original sss) \<Rightarrow>l map Nt (middle_nts1 # middle_ntss)\<close>
          then obtain middle_ntss1 middle_ntsss
            where "middle_ntss = middle_ntss1 # middle_ntsss"
              and "[Original middle_nts1', middle_ntss1] = prefix"
            sorry (* can be obtained due to CNF *)

          with \<open>(Original ss1, map Nt prefix) \<in> ?G0R_prods\<close> have "(Original ss1, [Nt (Original middle_nts1'), Nt middle_ntss1]) \<in> ?G1_prods"
            by auto

          then have "(Original ss1, [Tm x1, Nt (start (renamed_wittness middle_nts1' x1)), Nt middle_ntss1]) \<in> G2_new_prods"
            unfolding G2_new_prods_def by blast

          then have "?G2_prods \<turnstile> Nt (Original ss1) # map Nt (map Original sss)
                                  \<Rightarrow>* [Tm x1, Nt (start (renamed_wittness middle_nts1' x1)), Nt middle_ntss1] @ map Nt (map Original sss)"
            by (simp add: derivel_Nt_Cons derivel_imp_derive r_into_rtranclp)

          moreover from \<open>?G2_prods \<turnstile> [Nt (start (renamed_wittness middle_nts1' x1))] \<Rightarrow>* map Nt (map Original Ys's')\<close>
          have "?G2_prods \<turnstile> [Tm x1, Nt (start (renamed_wittness middle_nts1' x1))] \<Rightarrow>* Tm x1 # map Nt (map Original Ys's')"
            by (rule derives_Cons)
          then have "?G2_prods \<turnstile> [Tm x1, Nt (start (renamed_wittness middle_nts1' x1)), Nt middle_ntss1] \<Rightarrow>* Tm x1 # map Nt ((map Original Ys's')) @ [Nt middle_ntss1]"
            by (metis append.left_neutral append_Cons derives_append)
          then have "?G2_prods \<turnstile> [Tm x1, Nt (start (renamed_wittness middle_nts1' x1)), Nt middle_ntss1] @ map Nt (map Original sss) \<Rightarrow>* Tm x1 # map Nt ((map Original Ys's')) @ [Nt middle_ntss1] @ map Nt (map Original sss)"
             by (metis Cons_eq_appendI append_assoc derives_append)

          ultimately have "?G2_prods \<turnstile> Nt (Original ss1) # map Nt (map Original sss)
                                  \<Rightarrow>* Tm x1 # map Nt (map Original Ys's') @ Nt middle_ntss1 # map Nt (map Original sss)"
            by simp 

          with Ys's' have "?G2_prods \<turnstile> Nt (Original ss1) # map Nt (map Original sss)
                                  \<Rightarrow>* Tm x1 # map Nt Ys's @ Nt middle_ntss1 # map Nt (map Original sss)"
            by simp
          then have "?G2_prods \<turnstile> Nt (Original ss1) # map Nt (map Original sss)
                                  \<Rightarrow>* Tm x1 # map Nt (Ys's @ middle_ntss1 # map Original sss)"
            by simp
          with \<open>ss = ss1 # sss\<close> have "?G2_prods \<turnstile> map Nt (map Original ss)
                                  \<Rightarrow>* Tm x1 # map Nt (Ys's @ middle_ntss1 # map Original sss)"
            by simp

          moreover have "Ys's @ middle_ntss1 # (map Original sss) = map Original ns'"
            using Ys' Ys's \<open>[Original middle_nts1', middle_ntss1] = prefix\<close> \<open>prefix @ map Original sss = middle_nts1 # middle_ntss\<close> ns' by force
          ultimately have "?G2_prods \<turnstile> map (Nt \<circ> Original) ss \<Rightarrow>* Tm x1 # map Nt (map Original ns')"
            by simp
          then have "?G2_prods \<turnstile> map (Nt \<circ> Original) ss \<Rightarrow>* Tm x1 # map (Nt \<circ> Original) ns'"
            by simp
          then show ?thesis by simp
        qed

        moreover have "?G2_prods \<turnstile> Tm x1 # map (Nt \<circ> Original) ns' \<Rightarrow>* map Tm x"
        proof -
          from step3 have "?G0R_prods \<turnstile> map Nt ns \<Rightarrow>l(n2) map Tm xs"
            by (simp add: deriveln_Tm_Cons)
          with \<open>ns = map Original ns'\<close> have "?G0R_prods \<turnstile> map (Nt o Original) ns' \<Rightarrow>l(n2) map Tm xs"
            by simp
          then have  "?G1_prods \<turnstile> map (Nt o Original) ns' \<Rightarrow>l(n2) map Tm xs"
            using G0R_deriveln_iff_G1 by blast
          moreover from sum have "n2 \<le> n'" by auto
          moreover note Leq.IH
          ultimately have "?G2_prods \<turnstile> map (Nt \<circ> Original) ns' \<Rightarrow>* map Tm xs"
            by fast
          then have "?G2_prods \<turnstile> Tm x1 # map (Nt \<circ> Original) ns' \<Rightarrow>* Tm x1 # map Tm xs"
            by (rule derives_Cons)
          then show "?G2_prods \<turnstile> Tm x1 # map (Nt \<circ> Original) ns' \<Rightarrow>* map Tm x"
            using x1_xs by simp
        qed

        ultimately show ?thesis
          by (rule rtranclp_trans)
      qed
    qed

    ultimately show "(?G2_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x))" by fast
  qed


  (* second direction *)
  have G2_G1: "\<And>ss x. (?G2_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x)) \<Longrightarrow>
                (?G1_prods \<turnstile> (map (Nt o Original) ss) \<Rightarrow>* (map Tm x))"
    sorry

  

  have "Lang ?G1_prods (Original (start G0)) = Lang ?G2_prods (Original (start G0))"
    unfolding Lang_def apply(rule Collect_eqI)
  proof
    fix x
    assume "?G1_prods \<turnstile> [Nt (Original (start G0))] \<Rightarrow>* map Tm x"
    then show "?G2_prods \<turnstile> [Nt (Original (start G0))] \<Rightarrow>* map Tm x"
      using G1_G2
      by (metis (no_types, lifting) Nil_is_map_conv comp_apply list.simps(9)) 
  next
    fix x
    assume "?G2_prods \<turnstile> [Nt (Original (start G0))] \<Rightarrow>* map Tm x"
    then show "?G1_prods \<turnstile> [Nt (Original (start G0))] \<Rightarrow>* map Tm x" 
      using G2_G1
      by (metis (no_types, lifting) Nil_is_map_conv comp_apply list.simps(9)) 
  qed


  (* G2 is not yet in GNF, since it can contain epsilon-productions *)
  (* TODO: prove, that eliminating epsilon-productions does not yield unit productions *)

  show ?thesis sorry
qed


lemma "(x = y) \<Longrightarrow> (\<And>e. ((e \<in> x) \<longleftrightarrow> (e \<in> y)))"  using [[simp_trace]] by simp

end