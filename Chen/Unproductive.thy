theory Unproductive
imports
  Closure
  Epsilon
  "../CFG"
begin

hide_const (open) Topological_Spaces.closed

text \<open>Unproductive Symbol Elimination\<close>

(* I think we might prefer the inductive set definition, because we may want to
use productive.induct at some point, although I'm not 100% sure *)
inductive_set productive :: "('n,'t)Prods \<Rightarrow> 'n set" for P where
"\<lbrakk> (A,\<alpha>) \<in> P; \<And>B. B \<in> nts_of_syms \<alpha> \<Longrightarrow> B \<in> productive P \<rbrakk> \<Longrightarrow> A \<in> productive P"

definition "rm_unproductive P = {(A,\<alpha>) \<in> P. ({A} \<union> nts_of_syms \<alpha>) \<subseteq> productive P}"


theorem "Lang (rm_unproductive P) A = Lang P A"
  proof
    have "rm_unproductive P \<subseteq> P"
      unfolding rm_unproductive_def by auto
    then show "Lang (rm_unproductive P) A \<subseteq> Lang P A"
      using Lang_mono by metis
  next
    show "Lang P A \<subseteq> Lang (rm_unproductive P) A"
      proof (cases)
        assume "A \<in> productive P"
        have "\<And> w. w \<in> Lang P A \<Longrightarrow> w \<in> Lang (rm_unproductive P) A"
          proof -
            fix w
            assume "w \<in> Lang P A"
            then have "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
              unfolding Lang_def by simp

            (* should follow from A \<in> productive P, but I couldn't figure it out *)
            then have "rm_unproductive P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
              using \<open>A \<in> productive P\<close>
              proof (induction rule: derives_induct)
                case base
                then show ?case by simp
              next
                case (step u A' v w')
                then show ?case 
                sorry
              qed

            then show "w \<in> Lang (rm_unproductive P) A"
            by (simp add: Lang_def)
          qed
        then show ?thesis
          by auto
      next
        assume "A \<notin> productive P"
        have "Lang P A = {}"
        proof (rule ccontr)
          assume "Lang P A \<noteq> {}"
          then obtain w where "P \<turnstile> [Nt A] \<Rightarrow>* w" and "nts_of_syms w = {}"
            unfolding Lang_def nts_of_syms_def by fastforce

          (* should follow frow A \<notin> productive P, although I'm not sure if the 
          current attempt at proving it is particularly fruitful*)
          moreover have "nts_of_syms w \<noteq> {}"
            using \<open>P \<turnstile> [Nt A] \<Rightarrow>* w\<close> unfolding nts_of_syms_def 
            proof (induction)
              case base
              then show ?case by simp
            next
              case (step y z)
              then obtain \<alpha> \<beta> \<gamma> A' where "y = \<alpha> @ [Nt A'] @ \<gamma>" and "z = \<alpha> @ \<beta> @ \<gamma>"
                by (meson derive.cases)
              (* should be easily proved with an additional lemma*)
              then have "A' \<notin> productive P"
              using \<open>A \<notin> productive P\<close> step.hyps sorry
              (* I feel like this should follow from the previous statement,
              but I wasn't able to prove it *)
              then show ?case
                sorry
            qed

          ultimately show False
            by simp

        qed
        then show ?thesis
          by auto
    qed
qed
end