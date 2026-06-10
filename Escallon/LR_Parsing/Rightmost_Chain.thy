theory Rightmost_Chain
  imports Extended_Cfg
begin

inductive rm_chain :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) syms \<Rightarrow> ('a, 'b) item list \<Rightarrow> ('a, 'b) syms 
                            \<Rightarrow> bool" 
   (\<open>_ \<Turnstile> _ \<Rightarrow>r* _ \<Rightarrow>r* _\<close> 30) for P where
refl[intro]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [] \<Rightarrow>r* \<alpha>" |

step[intro]:  "\<lbrakk>P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v; 
    P \<turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r \<alpha> @ \<alpha>' @ Nt Y # \<beta> @ map Tm v; P \<turnstile> \<beta> \<Rightarrow>r* map Tm u\<rbrakk>
    \<Longrightarrow> P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [X \<rightarrow> \<alpha>' . Nt Y # \<beta>]#\<rho> \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v"

lemma rm_chain_imp_eq_or_rsentential:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta>"
  shows "(\<alpha> = \<beta> \<and> \<rho> = []) \<or> (\<exists>\<gamma> X v. \<beta> = \<gamma> @ Nt X # map Tm v)"
  using assms by cases (simp, metis append.assoc map_append)

lemma rm_chain_rsentential_imp_rsentential:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 @ Nt X # map Tm u \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta>"
  obtains \<gamma> X v where "\<beta> = \<gamma> @ Nt X # map Tm v"
  using assms that by cases (blast, metis append.assoc map_append)

lemma rm_chain_Tms_impossible[simp]:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> x#xs . map Tm u]#\<rho> \<Rightarrow>r* \<beta>"
  shows False
  using assms by cases auto

lemma rm_chain_imp_Nt_hd[elim]:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> \<alpha>' . \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"
  obtains B \<beta>' where "\<beta> = Nt B # \<beta>'"
  using assms by cases auto

inductive_cases rm_chain_reflE[elim]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [] \<Rightarrow>r* \<beta>"
inductive_cases rm_chain_stepE[elim]: "P \<Turnstile> \<alpha> \<Rightarrow>r* [A \<rightarrow> \<alpha>' . Nt B # \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"

lemma rm_chain_imp_prod:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . \<beta>]#\<rho> \<Rightarrow>r* \<gamma>"
  shows "(A, \<alpha>@\<beta>) \<in> P"
  using assms syms_split_rightmost by cases (simp add: deriver_imp_in_Prods)


lemma rm_chain_imp_prods:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  shows "\<forall>i \<in> set \<rho>. prod_of_item i \<in> P"
  using assms by induction (use rm_chain_imp_prod in fastforce)+

lemma rm_chain_singleton_imp_eq:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . Nt C # \<beta>]#\<rho> \<Rightarrow>r* \<gamma> @ Nt B # map Tm w"
  shows "C = B \<and> (\<exists>u v. w = u @ v \<and> P \<turnstile> \<beta> \<Rightarrow>r* map Tm u)"
  using assms proof cases
  case (step \<alpha>' v u)
  with right_sententials_eq_imp_tl_eq[of _ _ _ "\<alpha>' @ \<alpha>" C] have "w = u @ v"
    by fastforce
  moreover with step have "C = B" by simp
  ultimately show ?thesis using step by blast 
qed

lemma derive_singleton_imp_singleton_chain:
  assumes "P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "P \<Turnstile> [Nt A] \<Rightarrow>r* [[A \<rightarrow> [] . [Nt B]]] \<Rightarrow>r* [Nt B]"
  using assms rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" "[]" B "[]" "[]"]
    by (simp add: derive_singleton deriver_singleton rm_chain.refl)



lemma rm_chain_imp_hd_prod_rightmost:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma> @ Nt B # map Tm w"
  obtains A \<alpha> \<beta> "is" u v where "\<rho> = [A \<rightarrow> \<alpha> . Nt B # \<beta>] # is"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u" "w = u @ v" | "\<alpha>\<^sub>0 = \<gamma> @ Nt B # map Tm w" "\<rho> = []"
using assms proof cases
  case (step \<rho> \<alpha> X v \<alpha>' Y \<beta> u)
  moreover with right_sententials_eq_imp_tl_eq[of _ _ _ "\<alpha> @ \<alpha>'"] have "w = u@v" by simp
  moreover from this have "B = Y" using step(2) by simp
  ultimately show ?thesis using that by blast
qed argo

lemma rm_chain_second_produces_hd:
  assumes "Prods G' \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . Nt B # \<beta>] # i # \<rho> \<Rightarrow>r* \<gamma>"
  obtains X \<alpha>' \<beta>' where "i = [X \<rightarrow> \<alpha>' . Nt A # \<beta>']"
  using assms proof cases
  case (step \<alpha> v u)
  from rm_chain_imp_hd_prod_rightmost[OF step(2)] show ?thesis using that
    by fastforce
qed

lemma rm_chain_Cons_imp_prod_rightmost:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . Nt B # \<beta>] # \<rho> \<Rightarrow>r* \<gamma>"
  obtains \<delta> u v w where "\<gamma> = \<delta> @ Nt B # map Tm w"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u" "w = u @ v"
proof -
  note rm_chain_imp_eq_or_rsentential[OF assms]
  then show thesis
  proof
    assume "\<exists>\<gamma>' X v. \<gamma> = \<gamma>' @ Nt X # map Tm v"
    then obtain \<gamma>' X v where \<gamma>_rm: "\<gamma> = \<gamma>' @ Nt X # map Tm v" by blast
    from rm_chain_imp_hd_prod_rightmost[OF assms[unfolded this]] show thesis
      using that \<gamma>_rm by (cases, auto)
  qed simp
qed

lemma rm_chain_imp_derivers:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta>"
  shows "P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>"
  using assms proof induction
  case (step \<alpha>\<^sub>0 \<rho> \<alpha> X v \<alpha>' Y \<beta> u)
  from step(3) derivers_append_map_Tm[OF step(3)] have
    "P \<turnstile>  \<alpha> @ \<alpha>' @ Nt Y # \<beta> @ map Tm v \<Rightarrow>r*  \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v"
    by (metis append_Cons append_Nil derivers_prepend)
  then show ?case using step by simp
qed simp


lemma rm_chain_append:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* \<sigma> \<Rightarrow>r* \<beta>"
    "P \<Turnstile> \<beta> \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  shows "P \<Turnstile> \<alpha> \<Rightarrow>r* \<rho>@\<sigma> \<Rightarrow>r* \<gamma>"
  using assms(2,1) by induction auto

lemma rm_chain_decomp:
  assumes "P \<Turnstile> \<alpha> \<Rightarrow>r* \<rho>@\<sigma> \<Rightarrow>r* \<gamma>"
  obtains \<beta> where 
    "P \<Turnstile> \<alpha> \<Rightarrow>r* \<sigma> \<Rightarrow>r* \<beta>"
    "P \<Turnstile> \<beta> \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  using assms proof (induction \<rho> arbitrary: \<gamma>)
  case (Cons a \<rho>)
  then show ?case 
    by (smt (verit, del_insts) append.simps(2) list.distinct(1) list.simps(1) rm_chain.simps)
qed auto


lemma rm_chain_snoc:
  assumes "P \<Turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r* \<rho> @ [[X \<rightarrow> \<alpha>' . Nt Y # \<beta>]] \<Rightarrow>r* \<gamma>"
  obtains u where "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u" 
    "P \<Turnstile> \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v \<Rightarrow>r* \<rho> \<Rightarrow>r* \<gamma>"
  using assms 
  by (smt (verit, best) append_same_eq right_sententials_eq_imp_tl_eq rm_chain_decomp rm_chain_reflE
      rm_chain_stepE)

lemma rm_chain_substring:
  assumes "P \<Turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta> @ Nt Y # map Tm w"
  obtains u where "w = u @ v"
  using assms proof (induction "\<alpha> @ Nt X # map Tm v" \<rho> "\<beta> @ Nt Y # map Tm w" arbitrary: \<beta> Y w)
  case refl
  then show ?case using right_sententials_eq_imp_tl_eq[OF refl(1)] by simp
next
  case (step \<rho> \<alpha>' X v \<gamma> Y' \<beta>' u)
  then show ?case 
    by (meson assms derivers_tl_substring rm_chain_imp_derivers that)
qed 

lemma rm_chain_singleton_left_is_hist:
  assumes "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v"
  shows "\<alpha> = hist \<rho>"
  using assms proof (induction \<rho> arbitrary: \<alpha> X v)
  case Nil
  hence "[Nt A] = \<alpha> @ Nt X # map Tm v" by auto
  then show ?case by (simp add: Cons_eq_append_conv)
next
  case (Cons i \<rho>)
  from this(2) show ?case 
  proof cases
    case (step \<alpha>' X' w \<gamma> Y \<beta> x)
    then show ?thesis using Cons.IH[OF step(3)] 
      by (metis (no_types, lifting) Cons.prems append_assoc append_same_eq hist_Cons history_unfold
          map_append right_sententials_eq_imp_tl_eq rm_chain_singleton_imp_eq)
  qed
qed

lemma prod_imp_rm_chain_step:
  assumes "Prods G \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v"
    "(X, \<alpha>' @ Nt A # \<beta>) \<in> Prods G"
    "reduced G"
  obtains u where "Prods G \<turnstile> \<beta> \<Rightarrow>r* map Tm u"
    "Prods G \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [X \<rightarrow> \<alpha>' . Nt A # \<beta>] # \<rho> \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt A # map Tm (u@v)"
proof -
  from assms have "Prods G \<turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r \<alpha> @ \<alpha>' @ Nt A # \<beta> @ map Tm v" 
    using deriver.intros by fastforce
  moreover from assms(2-) obtain u where "Prods G \<turnstile> \<beta> \<Rightarrow>r* map Tm u"
    using reduced_imp_prod_substring_derives_Tms derivers_iff_derives 
    by (metis append.assoc append.right_neutral append_Cons append_Nil)
  ultimately show ?thesis using assms(1) rm_chain.step that by fastforce
qed

lemma derivern_Suc_singleton_imp_rm_chain:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v"
  obtains B \<alpha>' \<beta> \<rho> where "P \<Turnstile> [Nt A] \<Rightarrow>r* [B \<rightarrow> \<alpha>' . Nt X # \<beta>] # \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v"
  using assms(1) proof (induction "Suc n" arbitrary: \<alpha> X v n thesis rule: less_induct)
  case (less n)
  show ?case 
  proof (cases n)
    case 0
    then show ?thesis using rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" \<alpha> X] less 
      by force
  next
    case (Suc m)
    note Suc_m = this
    with less obtain \<beta> B u \<gamma> where Suc_steps: "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<beta> @ Nt B # map Tm u"
      "\<beta> @ \<gamma> @ map Tm u = \<alpha> @ Nt X # map Tm v" "P \<turnstile> \<beta> @ Nt B # map Tm u \<Rightarrow>r \<beta> @ \<gamma> @ map Tm u"
      using deriver.cases by (smt (verit, del_insts) relpowp_Suc_E)
    with less(1)[OF _ this(1)] Suc obtain \<rho> where last_chain_step: 
      "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta> @ Nt B # map Tm u" using less.hyps by blast
    show ?thesis
    proof (cases "Nt X \<in> set \<gamma>")
      case True
      from Suc_steps(2) obtain \<delta> w where"\<gamma> = \<delta> @ Nt X # map Tm w" "w @ u = v" 
      by (metis True syms_decomp_rightmost2)
      with Suc Suc_steps less show thesis using last_chain_step by fastforce
    next
      case False
      with Suc_steps(2) have X_in_\<beta>: "Nt X \<in> set \<beta>" 
        by (metis Nts_syms_append Nts_syms_map_Tm Un_iff empty_iff in_Nts_syms list.set_intros(1))
      from syms_decomp_rightmost[OF _ X_in_\<beta> False, of \<alpha> v "[]" u] obtain \<delta> y z where
        \<beta>\<gamma>_decomp: "\<beta> = \<delta> @ Nt X # map Tm y" "\<gamma> = map Tm z" "v = y @ z @ u"
        using Suc_steps(2) by auto
      hence B_deriver: "P \<turnstile> [Nt B] \<Rightarrow>r map Tm z" using deriver_singleton 
        deriver_imp_in_Prods[OF Suc_steps(3)] by fast
      from \<beta>\<gamma>_decomp derivers_singleton_imp_produced[of m P A \<delta> X "map Tm y @ Nt B # map Tm u"] 
        Suc_steps(1) Suc
      obtain k \<alpha>' C w \<alpha>'' \<beta>' where k_steps:
        "P \<turnstile> [Nt A] \<Rightarrow>r(k) \<alpha>' @ Nt C # map Tm w"
        "P \<turnstile> \<alpha>' @ Nt C # map Tm w \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm w"
        "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm y @ Nt B # map Tm u"
        "\<delta> = \<alpha>' @ \<alpha>''" "k < Suc m" 
        by (smt (verit, ccfv_SIG) Cons_eq_appendI append_assoc)
      with \<beta>\<gamma>_decomp Suc_steps(2-) B_deriver have suffix_derivers_v:
          "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm v"
        using deriver.intros deriver_singleton 
          by (metis (mono_tags, lifting) map_append rtranclp.simps)
      show ?thesis 
      proof (cases k)
        case 0
        with k_steps(1) have eqs: "\<alpha>' = [] \<and> A = C \<and> w = []" 
          by (metis append1_eq_conv eq_Nil_appendI map_is_Nil_conv relpowp_0_E right_sententials_eq_imp_tl_eq
              sym.inject(1)) 
        moreover with k_steps(3) have "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm v" using eqs suffix_derivers_v by simp
        ultimately show ?thesis using less(2) rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" \<alpha>'' X \<beta>']
          0 k_steps 
          by (metis Suc_steps(2) \<beta>\<gamma>_decomp append.assoc append.right_neutral append_Cons append_Nil
              list.simps(8) map_append rm_chain.refl)
      next
        case (Suc j)
        from less(1)[OF _ _ k_steps(1)[unfolded Suc]] obtain \<rho> where \<rho>_def:
          "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha>' @ Nt C # map Tm w" using k_steps(5)[unfolded Suc] Suc_m
          by auto
        moreover from suffix_derivers_v obtain u' where "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm u'" "u' @ w = v"
          by (metis converse_rtranclpE derivers_iff_derives derives_append_map_Tm map_Tm_inject_iff
              not_derive_map_Tm)
        moreover from \<beta>\<gamma>_decomp Suc_steps(2) have "\<alpha> = \<delta>" by force
        ultimately show ?thesis using less(2) rm_chain.step[OF \<rho>_def k_steps(2)] 
          k_steps(4) by fastforce
      qed
    qed
  qed
qed

end 
