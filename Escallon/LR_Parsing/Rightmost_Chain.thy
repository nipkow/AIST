theory Rightmost_Chain
  imports 
    Extended_Cfg 
    Item_Pushdown_Automata
begin

inductive rm_chain :: "('a, 'b) Prods \<Rightarrow> ('a, 'b) syms \<Rightarrow> ('a, 'b) item list \<Rightarrow> ('a, 'b) syms 
                            \<Rightarrow> bool" 
   (\<open>_ \<turnstile> _ \<midarrow>_\<rightarrow>r* _\<close> 30) for P where
refl[intro]: "P \<turnstile> \<alpha> \<midarrow>[]\<rightarrow>r* \<alpha>" |

step[intro]:  "\<lbrakk>P \<turnstile> \<alpha>\<^sub>0 \<midarrow>\<rho>\<rightarrow>r* \<alpha> @ Nt X # map Tm v; 
    P \<turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r \<alpha> @ \<alpha>' @ Nt Y # \<beta> @ map Tm v; P \<turnstile> \<beta> \<Rightarrow>r* map Tm u\<rbrakk>
    \<Longrightarrow> P \<turnstile> \<alpha>\<^sub>0 \<midarrow>[X \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>]#\<rho>\<rightarrow>r* \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v"

inductive_cases rm_chain_reflE[elim]: "P \<turnstile> \<alpha> \<midarrow>[]\<rightarrow>r* \<beta>"
inductive_cases rm_chain_stepE[elim]: "P \<turnstile> \<alpha> \<midarrow>[A \<rightarrow> \<alpha>' \<cdot> Nt B # \<beta>]#\<rho>\<rightarrow>r* \<gamma>"

lemma rm_chain_imp_prod:
  assumes "P \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> \<beta>]#\<rho>\<rightarrow>r* \<gamma>"
  shows "(A, \<alpha>@\<beta>) \<in> P"
  using assms syms_split_rightmost by cases (simp add: deriver_imp_in_Prods)

lemma rm_chain_singleton_imp_eq:
  assumes "P \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> Nt C # \<beta>]#\<rho>\<rightarrow>r* \<gamma> @ Nt B # map Tm w"
  shows "C = B \<and> (\<exists>u v. w = u @ v \<and> P \<turnstile> \<beta> \<Rightarrow>r* map Tm u)"
  using assms proof cases
  case (step \<alpha>' v u)
  with Nt_map_Tm_eq_Nt_map_TmD[of _ _ _ "\<alpha>' @ \<alpha>" C] have "w = u @ v"
    by fastforce
  moreover with step have "C = B" by simp
  ultimately show ?thesis using step by blast 
qed

lemma derive_singleton_imp_singleton_chain:
  assumes "P \<turnstile> [Nt A] \<Rightarrow> [Nt B]"
  shows "P \<turnstile> [Nt A] \<midarrow>[[A \<rightarrow> [] \<cdot> [Nt B]]]\<rightarrow>r* [Nt B]"
  using assms rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" "[]" B "[]" "[]"]
    by (simp add: derive_singleton deriver_singleton rm_chain.refl)

lemma rm_chain_second_produces_hd:
  assumes "Prods G' \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> Nt B # \<beta>] # i # \<rho>\<rightarrow>r* \<gamma>"
  obtains X \<alpha>' \<beta>' where "i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']"
  using assms proof cases
  case (step \<alpha>' v u)
  from step(2) show ?thesis
    using step that by cases (metis rm_chain_singleton_imp_eq)
qed

lemma rm_chain_Cons_imp_prod_rightmost:
  assumes "P \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> Nt B # \<beta>] # \<rho>\<rightarrow>r* \<gamma>"
  obtains \<delta> u v w where "\<gamma> = \<delta> @ Nt B # map Tm w"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm u" "w = u @ v"
  using assms by cases (metis that append.assoc map_append)

lemma rm_chain_imp_derivers:
  assumes "P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>"
  shows "P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>"
  using assms proof induction
  case (step \<alpha>\<^sub>0 \<rho> \<alpha> X v \<alpha>' Y \<beta> u)
  from step(3) derivers_append_map_Tm[OF step(3)] have
    "P \<turnstile>  \<alpha> @ \<alpha>' @ Nt Y # \<beta> @ map Tm v \<Rightarrow>r*  \<alpha> @ \<alpha>' @ Nt Y # map Tm u @ map Tm v"
    by (metis append_Cons append_Nil derivers_prepend)
  then show ?case using step by simp
qed simp

lemma (in Extended_Cfg) rm_chain_S'_Cons_imp_neq:
  assumes "Prods G' \<turnstile> [Nt S'] \<midarrow>i # \<rho>\<rightarrow>r* \<alpha>"
  shows "[Nt S'] \<noteq> \<alpha>"
  using assms proof cases
  case (step \<alpha>' X v \<alpha>'' Y \<beta> u)
  obtain n where derivern_\<alpha>: "Prods G' \<turnstile> \<alpha>' @ \<alpha>'' @ Nt Y # \<beta> @ map Tm v \<Rightarrow>r(n) \<alpha>"
    using step(5)[THEN derivers_prepend, of "\<alpha>' @ \<alpha>'' @ [Nt Y]", 
      THEN derivers_append_map_Tm, of v] step(2) rtranclp_imp_relpowp by fastforce
  from step rm_chain_imp_derivers obtain m where  "Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(m) \<alpha>' @ Nt X # map Tm v" 
    using rtranclp_imp_relpowp by metis
  also note step(4)
  also note derivern_\<alpha>
  finally show ?thesis using G'_deriven_Suc_imp_no_S' derivern_imp_deriven 
    by (metis add_Suc in_Nts_syms list.set_intros(1))
qed

lemma prod_imp_rm_chain_step:
  assumes "Prods G \<turnstile> \<alpha>\<^sub>0 \<midarrow>\<rho>\<rightarrow>r* \<alpha> @ Nt X # map Tm v"
    "(X, \<alpha>' @ Nt A # \<beta>) \<in> Prods G"
    "reduced G"
  obtains u where "Prods G \<turnstile> \<beta> \<Rightarrow>r* map Tm u"
    "Prods G \<turnstile> \<alpha>\<^sub>0 \<midarrow>[X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>] # \<rho>\<rightarrow>r* \<alpha> @ \<alpha>' @ Nt A # map Tm (u@v)"
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
  obtains B \<alpha>' \<beta> \<rho> where "P \<turnstile> [Nt A] \<midarrow>[B \<rightarrow> \<alpha>' \<cdot> Nt X # \<beta>] # \<rho>\<rightarrow>r* \<alpha> @ Nt X # map Tm v"
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
      "P \<turnstile> [Nt A] \<midarrow>\<rho>\<rightarrow>r* \<beta> @ Nt B # map Tm u" using less.hyps by blast
    show ?thesis
    proof (cases "X \<in> Nts_syms \<gamma>")
      case True
      from Suc_steps(2) obtain \<delta> w where"\<gamma> = \<delta> @ Nt X # map Tm w" "w @ u = v" 
        using True syms_decomp_rightmost2 by (metis in_Nts_syms)
      with Suc Suc_steps less show thesis using last_chain_step by fastforce
    next
      case False
      with Suc_steps(2) have X_in_\<beta>: "Nt X \<in> set \<beta>" 
        by (metis Nts_syms_append Nts_syms_map_Tm Un_iff empty_iff in_Nts_syms list.set_intros(1))
      from syms_decomp_rightmost[OF _ X_in_\<beta> _, of \<alpha> v "[]" \<gamma> u] obtain \<delta> y z where
        \<beta>\<gamma>_decomp: "\<beta> = \<delta> @ Nt X # map Tm y" "\<gamma> = map Tm z" "v = y @ z @ u"
        using Suc_steps(2) in_Nts_syms by (metis False self_append_conv2)
      hence B_deriver: "P \<turnstile> [Nt B] \<Rightarrow>r map Tm z" using deriver_singleton 
        deriver_imp_in_Prods[OF Suc_steps(3)] by fast
      from \<beta>\<gamma>_decomp derivern_singleton_imp_produced[of m P A \<delta> X "map Tm y @ Nt B # map Tm u"] 
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
          by (metis eq_Nil_appendI map_is_Nil_conv relpowp_0_E Nt_map_Tm_eq_Nt_map_TmD) 
        moreover with k_steps(3) have "P \<turnstile> \<beta>' \<Rightarrow>r* map Tm v" using eqs suffix_derivers_v by simp
        ultimately show ?thesis using less(2) rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" \<alpha>'' X \<beta>']
          0 k_steps \<beta>\<gamma>_decomp
          by (metis Suc_steps(2) append.assoc append.right_neutral append_Cons append_Nil
              list.simps(8) map_append rm_chain.refl)
      next
        case (Suc j)
        from less(1)[OF _ _ k_steps(1)[unfolded Suc]] obtain \<rho> where \<rho>_def:
          "P \<turnstile> [Nt A] \<midarrow>\<rho>\<rightarrow>r* \<alpha>' @ Nt C # map Tm w" using k_steps(5)[unfolded Suc] Suc_m
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

context Extended_Cfg
begin

interpretation I: ipda G IPDA
  by unfold_locales simp

corollary ipda_IPDA:
  "ipda G IPDA"
  by (fact I.ipda_axioms)

notation I.step (infix \<open>\<turnstile>I\<close> 55)
notation I.steps (infix \<open>\<turnstile>I*\<close> 55)
notation I.stepn ( \<open>_ \<turnstile>I'(_') _\<close> 55)


lemma ipda_reaches_final_imp_rm_chain:
  assumes "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])"
  obtains "\<rho> = []" |
    \<sigma> X \<alpha>' \<beta>' \<gamma> where "\<rho> = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'] # \<sigma>" "Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<gamma>"
  using assms proof (induction "([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w)" arbitrary: A \<alpha> \<beta> \<rho> w thesis
                      rule: converse_rtranclp_induct)
  case (step z)
  from I.step_imp_in_It this(1) have A_in_It: "[A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> It G'" 
    using I.step_imp_not_Nil by (smt (verit, ccfv_SIG) I.step_cases)
  from step(1) obtain B \<gamma> \<delta> \<tau> v where z\<tau>_def:
    "z = ([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v)" using prod.exhaust 
    by (metis I.step_imp_not_Nil item.exhaust list.exhaust)
  note step(3)[OF this] 
  then show thesis
  proof (cases, goal_cases Nil chain)
    case Nil
    with z\<tau>_def have z_B_init: "z = ([[B \<rightarrow> \<gamma> \<cdot> \<delta>]], v)" by blast
    with step(2) I.reaches_final_imp_last_is_init_or_final consider 
      "[B \<rightarrow> \<gamma> \<cdot> \<delta>] = init IPDA" |
      "[B \<rightarrow> \<gamma> \<cdot> \<delta>] = I.final_state" by fastforce
    then show thesis
    proof cases
      case 2
      note step(1)[unfolded z_B_init this] 
      with I.step_reaches_final_imp_S[of _ _ _ \<rho> "[]"] show ?thesis using step(5) G'_derive_S 
          derive_singleton_imp_singleton_chain 
        by (metis I.init_ipda append.right_neutral item.inject list.inject)
    qed (use step(1) in cases, use z_B_init in auto)
  next
    case (chain X \<alpha>' \<beta>' \<sigma> \<zeta>)
    from step(1)[unfolded z\<tau>_def] show ?thesis proof cases
      case (reduce Y \<eta> X' \<theta> \<iota> \<upsilon> x)
      hence BA_in_prods: "(B, \<theta> @ Nt A # \<delta>) \<in> Prods G'"
        using step(1) z\<tau>_def I.step_imp_in_Prods by force 
      from rm_chain_Cons_imp_prod_rightmost chain obtain \<zeta>' u where \<zeta>_rm: "\<zeta> = \<zeta>' @ Nt B # map Tm u"
        by meson
      note chain(2)[unfolded chain(1) this]
      from prod_imp_rm_chain_step[OF this BA_in_prods G'_reduced] step.prems(2) reduce chain(1)
      show thesis by fastforce       
    next
      case (expand Y \<eta> X' \<theta> \<iota> \<upsilon> x)
      show ?thesis
      proof (cases \<rho>)
        case (Cons i \<xi>)
        from Cons expand have Ai\<xi>: "\<tau> = [A \<rightarrow> \<theta> \<cdot> Nt B # \<iota>] # i # \<xi>"  by auto
        from rm_chain_second_produces_hd[OF chain(2)[unfolded this]] obtain Z \<gamma>' \<delta>' where
          "\<rho> = [Z \<rightarrow> \<gamma>' \<cdot> Nt A # \<delta>'] # \<xi>" using Cons expand by auto
        moreover from chain(2) obtain \<zeta>' where "Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<zeta>'"
          unfolding Ai\<xi> by cases (auto simp: Cons)
        ultimately show thesis using step.prems(2) by blast
      qed (rule step.prems(1))
    qed (use step(5) chain in fastforce)
  qed
qed simp

end
end
