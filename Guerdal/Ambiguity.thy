
section \<open>Ambiguity in Context-Free Grammars\<close>

theory Ambiguity
  imports 
    Main 
    Context_Free_Grammar.Parse_Tree
begin

subsection "Definition of an Ambiguous Grammar"

text "A CFG is ambiguous, if there exists a word for which there is two leftmost derivations (or different parse tree, which we do not model, because 
      the proof of inherent ambiguity uses the definition through leftmost derivations)."

abbreviation ambiguous :: "('n, 't) Cfg \<Rightarrow> bool" 
  where 
    "ambiguous G \<equiv> \<not> unambiguous (Prods G) (Start G)" 


subsection "Showing that distinct subsets of productions deriving a word implies ambiguity"

text "If a subset of productions form a parse tree, the superset also forms the same tree."
lemma subset_tree:
  fixes P_subs P :: "('n, 't) Prods" and t :: "('n, 't) ptree" 
  assumes "parse_tree P_subs t" "P_subs \<subseteq> P"
  shows "parse_tree P t"
  using assms by (induction t; auto)

text "If there exists two distinct subsets of productions of a grammar deriving same word, then the 
     grammar is ambiguous."
lemma prod_subsets_imp_ambig:
  fixes G :: "('n, 't) Cfg"
  assumes "\<exists>w P1 P2. P1 \<subseteq> Prods G \<and> P2 \<subseteq> Prods G \<and> P1 \<inter> P2 = {} \<and>
          P1 \<turnstile> [Nt (Start G)] \<Rightarrow>+ map Tm w \<and> P2 \<turnstile> [Nt (Start G)] \<Rightarrow>+ map Tm w"
  shows "ambiguous G"
proof - 
  from assms obtain w P1 P2 where 
      p1_subst: "P1 \<subseteq> Prods G" and p2_subst: "P2 \<subseteq> Prods G" and
      conj: "P1 \<inter> P2 = {}" and
      p1_deriv: "P1 \<turnstile> [Nt (Start G)] \<Rightarrow>+ map Tm w" and p2_deriv: "P2 \<turnstile> [Nt (Start G)] \<Rightarrow>+ map Tm w" 
    by blast
  then obtain n m 
    where p1_deriven: "P1 \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc n) map Tm w" 
    and   p2_deriven: "P2 \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc m) map Tm w" 
    using deriven_Nt_map_TmD rtranclp_power tranclp_into_rtranclp by metis

  then obtain t1 t2 where 
      pt_1: "parse_tree P1 t1" and size1: "size_pt t1 = Suc n" and fr1: "fringe t1 = map Tm w" and root1: "root t1 = Nt (Start G)" 
  and pt_2: "parse_tree P2 t2" and size2: "size_pt t2 = Suc m" and fr2: "fringe t2 = map Tm w" and root2: "root t2 = Nt (Start G)" 
    using parse_tree_if_deriven[OF p1_deriven] parse_tree_if_deriven[OF p2_deriven] by blast


  then have ptP1: "parse_tree (Prods G) t1" and ptP2: "parse_tree (Prods G) t2"
    using subset_tree[OF pt_1 p1_subst] subset_tree[OF pt_2 p2_subst] by auto
  then have v_pt_1: "valid_parse_tree (Prods G) (Start G) (map Tm w) t1" and v_pt_2: "valid_parse_tree (Prods G) (Start G) (map Tm w) t2"
    using ptP1 size1 fr1 root1 ptP2 size2 fr2 root2 unfolding valid_parse_tree_def by auto

  have "P1 \<noteq> P2" using conj deriven_Nt_Cons_map_Tm p2_deriven by force 

  then have uneq: "t1 \<noteq> t2" 
    by (metis conj disjoint_iff nat.distinct(1) parse_tree.simps(2) pt_1 pt_2 size1 size_pt.elims)

  have w_in_L: "w \<in> Lang (Prods G) (Start G)" 
    unfolding Lang_def using tranclp_into_rtranclp[OF p1_deriv] p1_subst 
    by (simp add: derives_mono)

  have "\<not> unambiguous (Prods G) (Start G)" 
  proof (rule ccontr)
    assume "\<not>?thesis"
    then have ambig: "\<And>w t1 t2. w \<in> Lang (Prods G) (Start G) \<Longrightarrow> valid_parse_tree (Prods G) (Start G) (map Tm w) t1 \<Longrightarrow> valid_parse_tree (Prods G) (Start G) (map Tm w) t2 \<Longrightarrow> t1 = t2"
      unfolding unambiguous_def by blast
    have "t1 = t2" using ambig[OF w_in_L v_pt_1 v_pt_2] by simp
    thus False using uneq by simp
  qed
  then show ?thesis by auto
qed    



abbreviation inherently_ambiguous_type :: "('n itself) \<Rightarrow> 't list set \<Rightarrow> bool" where
  "inherently_ambiguous_type TYPE('n) L \<equiv> \<forall>(G :: ('n, 't) Cfg). LangS G = L \<longrightarrow> ambiguous G"

abbreviation inherently_ambiguous :: "'t list set \<Rightarrow> bool" where
  "inherently_ambiguous L \<equiv> inherently_ambiguous_type TYPE(nat) L"

end