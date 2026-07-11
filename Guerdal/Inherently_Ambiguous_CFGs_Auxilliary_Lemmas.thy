theory Inherently_Ambiguous_CFGs_Auxilliary_Lemmas
  imports 
    Main 
    Ambiguity
begin

section "Lemma 4.5"
text "The first preliminary lemma of the proof is the Lemma 4.5. Informally explained if we build a set \<open>S={(n,m) | n \<in> N_i,m \<in> M_i}\<close> through finite partitions \<open>N_i\<close> \<open>M_i\<close>
     where each pair \<open>(n,m)\<close> of distinct integers is in the set \<open>(n,m)\<in>S\<close>, then there *all but some finite set* of \<open>n\<close> will be inside the set \<open>(n,n) \<in> S\<close>.
     Our formalization of the lemma does not use the set \<open>S\<close>, and argues over the property \<open>n \<in> N_i,m \<in> M_i\<close> for all \<open>i\<close>."
lemma lemma_45:
  fixes r :: nat
    and N :: "nat \<Rightarrow> nat set"
    and M :: "nat \<Rightarrow> nat set"
  assumes "r \<ge> 1"
  and cover: "\<And>n m. n \<noteq> m \<Longrightarrow> (\<exists>i\<in>{1..r}. n \<in> N i \<and> m \<in> M i)"
  shows "finite {n. \<not> (\<exists>i\<in>{1..r}. n \<in> N i \<and> n \<in> M i)}"
  proof (rule ccontr)
    let ?J = "{n. \<not> (\<exists>i\<in>{1..r}. n \<in> N i \<and> n \<in> M i)}"
    let ?J_before = "\<lambda>i. {n.\<not> (\<exists>j\<in>{1..i}. n \<in> N j \<and> n \<in> M j)}"
    let ?J_indexN =  "\<lambda>i. {n. n \<notin> N i}"
    let ?J_indexM =  "\<lambda>i. {n. n \<notin> M i}"

    text "We use a contradiction proof, assuming there is an infinite set of \<open>n\<close> s.t. \<open>(n,n) \<notin> S\<close>. "
    assume assm: "infinite ?J"
    then have brother: "\<And>i n. i\<in>{1..r} \<Longrightarrow>  n \<in> ?J \<Longrightarrow>  n \<notin> N i \<or> n \<notin> M i" using cover odd_nonzero by force

    text "We try here to show the construction of \<open>J_1,...,J_r\<close> shown in the proof. For a downwards induction, we switch the indexes: \<open>i=1\<close> means we are looking at
         \<open>J_r\<close>, i.e., for each index \<open>i\<close>, we look at \<open>J_{r-i+1}\<close>. In this case, we start the induction with \<open>i=0\<close>. This is a special case: the third ocondition will
         simplify to \<open>True\<close>, and hence, an infinite subset of \<open>J\<close> is enough. Then, we say \<open>J_{r+1}=?J\<close>. This works, since the construction of \<open>J_r\<close> from \<open>J\<close> in the 
         proof is the same as the construction of any \<open>J_i\<close> from \<open>J_{i+1}\<close>. We do not have to duplicate our efforts."
    have "\<And>i. i \<le> r \<Longrightarrow> \<exists>Ji. Ji \<subseteq> ?J \<and> infinite Ji \<and> (\<forall>n\<in>Ji. \<forall>m\<in>Ji. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{r - i + 1..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" 
    proof - 
      fix i
      assume iless: "i \<le> r"
      then show "\<exists>Ji. Ji \<subseteq> ?J \<and> infinite Ji \<and> (\<forall>n\<in>Ji. \<forall>m\<in>Ji. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{r - i + 1..r}. \<not>(n \<in> N j \<and> m \<in> M j)))"
      proof (induct i)
        case 0 
        text "We show that \<open>J\<close> is an infinite subset of \<open>J\<close>, trivially."
        then show ?case using assm by auto
      next
        case (Suc i)
        then obtain Ji where ji: "Ji \<subseteq> ?J" "infinite Ji" "(\<forall>n\<in>Ji. \<forall>m\<in>Ji. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{r - i + 1..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" by auto
        let ?i = "r - Suc i + 1" (* Make indexing more readable *)
        have union_ranges:  "{?i..r} \<subseteq> {r-i+1..r} \<union> {?i}" using iless by auto 
        from ji have "(Ji \<inter> ?J_indexN ?i) \<union> (Ji \<inter> ?J_indexM ?i) = (Ji \<inter> (?J_indexN ?i \<union>  ?J_indexM ?i))" by auto
        have "Ji \<subseteq> ?J_indexN ?i \<union> ?J_indexM ?i" 
        proof 
            fix x 
            assume "x \<in> Ji"
            then have xinJ: "x \<in> ?J" using ji(1) by auto 
            moreover have "?i \<le> r" using assms by linarith
            moreover have "1 \<le> ?i" by auto
            ultimately have le: "x \<notin> N ?i \<or> x \<notin> M ?i"
              using atLeastAtMost_iff xinJ by blast
            thus "x \<in> ?J_indexN ?i \<union> ?J_indexM ?i" by auto
        qed
        then have "Ji = (Ji \<inter> ?J_indexN ?i) \<union> (Ji \<inter> ?J_indexM ?i)" by auto
        text "Here, we use the fact that the union of two sets is infinite, then one of the sets is also infinite."
        then have infinite: "infinite (Ji \<inter> ?J_indexN ?i) \<or> infinite (Ji \<inter> ?J_indexM ?i)" 
           using ji(2) Finite_Set.infinite_Un
           by metis
         moreover have "(Ji \<inter> ?J_indexN ?i) \<subseteq> Ji" using ji(1) by blast
         moreover have "(Ji \<inter> ?J_indexM ?i) \<subseteq> Ji" using ji(1) by blast
         moreover have "(\<forall>n\<in>(Ji \<inter> ?J_indexN ?i). \<forall>m\<in>(Ji \<inter> ?J_indexN ?i). n \<noteq> m \<longrightarrow> (\<forall>j\<in>{?i..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" using union_ranges ji(3) by blast
         moreover have "(\<forall>n\<in>(Ji \<inter> ?J_indexM ?i). \<forall>m\<in>(Ji \<inter> ?J_indexM ?i). n \<noteq> m \<longrightarrow> (\<forall>j\<in>{?i..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" using union_ranges ji(3) by blast
         ultimately have "\<exists>Ji'. Ji' \<subseteq> Ji \<and> infinite Ji' \<and> (\<forall>n\<in>Ji'. \<forall>m\<in>Ji'. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{?i..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" using ji by blast
         then have "\<exists>Ji'. Ji' \<subseteq> ?J \<and> infinite Ji' \<and> (\<forall>n\<in>Ji'. \<forall>m\<in>Ji'. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{?i..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" using ji(1) by auto
         then show ?case by auto 
       qed
    qed
    then have "\<exists>Ji. Ji \<subseteq> ?J \<and> infinite Ji \<and> (\<forall>n\<in>Ji. \<forall>m\<in>Ji. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{r-r + 1..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" using assms(2) by blast
    then have "\<exists>Ji. Ji \<subseteq> ?J \<and> infinite Ji \<and> (\<forall>n\<in>Ji. \<forall>m\<in>Ji. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{1..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" using assms(2) by simp
    then obtain J1 where j1: "J1 \<subseteq> ?J" "infinite J1" "(\<forall>n\<in>J1. \<forall>m\<in>J1. n \<noteq> m \<longrightarrow> (\<forall>j\<in>{1..r}. \<not>(n \<in> N j \<and> m \<in> M j)))" by blast
    have "\<exists>B. finite B \<and> card B = 2 \<and> B \<subseteq> J1" using infinite_arbitrarily_large j1(2) by auto
    then obtain B where b: "finite B" "card B = 2" "B \<subseteq> J1" by blast
    then have "\<exists>n \<in> B. \<exists>m \<in> B. n \<noteq> m" by (auto iff: card_2_iff')
    then obtain n m where n_m: "n \<in> B" "m \<in> B" "n \<noteq> m" by blast
    then have "n \<in> J1 \<and> m \<in> J1" using b(3) by auto
    then have "(\<forall>j\<in>{1..r}. \<not>(n \<in> N j \<and> m \<in> M j))" using n_m j1 by fast 
    thus "False" using cover n_m(3) by blast
  qed



section "Lemma 4.6"
text "Our second preliminary lemma is the Lemma 4.6. This lemma will provide us a construction for CFGs s.t. the resulting grammar has no
      useless symbols or productions, and for all but the starting symbol \<open>S\<close>, we have \<open>A \<Rightarrow>* xAy\<close> where \<open>xy \<noteq> \<epsilon>\<close>. The construction also 
      preserves (un)ambiguity"

text "This construction uses previous constructions from the book, "



lemma productives_when_derive_tms:
  fixes P :: "('n, 't) Prods" and S A :: "'n" 
  assumes "useful P S A"
  shows "\<exists>\<alpha> \<beta> w. (P \<turnstile> [Nt S] \<Rightarrow>* \<alpha> @ [Nt A] @ \<beta> \<and> P \<turnstile> [Nt A] \<Rightarrow>* map Tm w)"
proof -
  from assms obtain \<beta> w where beta_w_obtain: "P \<turnstile> [Nt S] \<Rightarrow>* \<beta> " "P \<turnstile> \<beta> \<Rightarrow>* map Tm w" "Nt A \<in> set \<beta>" unfolding useful_def by blast
  then have aa: "\<exists>\<alpha> \<gamma>. \<beta> = \<alpha> @ [Nt A] @ \<gamma>" 
    by (simp add: split_list)
  then obtain \<alpha> \<gamma> where "\<beta> = \<alpha> @ [Nt A] @ \<gamma>" by blast
  then have "P \<turnstile> [Nt S] \<Rightarrow>* \<alpha> @ [Nt A] @ \<gamma> \<and> P \<turnstile> \<alpha> @ [Nt A] @ \<gamma> \<Rightarrow>* map Tm w" using beta_w_obtain by auto
  then obtain aa where aa_obtain: "P \<turnstile> [Nt A] \<Rightarrow>* map Tm aa" using derives_append_map_Tm by blast
  thus ?thesis using beta_w_obtain aa by fast
qed
 

lemma lemma46: (*added finiteness here because CFL condition only allowed to say that there exists one finite grammar, but not necessarily ours*)
  fixes G :: "('n, 't) Cfg"
  assumes "\<not>ambiguous G"
  shows "\<exists>G'. LangS G = LangS G' \<and> \<not>ambiguous G' \<and> finite (Prods G')
         \<and> (\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X) 
          \<and> (\<forall>X.  X \<noteq> (Start G') \<and> X \<in> Nts (Prods G') \<longrightarrow> (\<exists>\<alpha> \<beta>. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm \<alpha> @ [Nt X] @ map Tm \<beta> \<and> \<alpha> @ \<beta> \<noteq> []))"
proof - 
  show ?thesis sorry
qed















end