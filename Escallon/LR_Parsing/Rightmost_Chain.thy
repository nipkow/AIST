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


lemma rm_chain_singleton_imp_eq:
  assumes "P \<Turnstile> \<alpha>\<^sub>0 \<Rightarrow>r* [A \<rightarrow> \<alpha> . Nt C # \<beta>]#\<rho> \<Rightarrow>r* \<gamma> @ Nt B # map Tm w"
  shows "C = B \<and> (\<exists>u v. w = u @ v \<and> P \<turnstile> \<beta> \<Rightarrow>r* map Tm u)"
  using assms proof cases
  case (step \<alpha>' v u)
  with right_derivs_eq_imp_eq_tl[of _ _ _ "\<alpha>' @ \<alpha>" C] have "w = u @ v"
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
  moreover with right_derivs_eq_imp_eq_tl[of _ _ _ "\<alpha> @ \<alpha>'"] have "w = u@v" by simp
  moreover from this have "B = Y" using step(2) by simp
  ultimately show ?thesis using that by blast
qed argo



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

lemma app_derivers_app:
  assumes "P \<turnstile> \<alpha> \<Rightarrow>r* map Tm u"
    "P \<turnstile> \<beta> \<Rightarrow>r* map Tm v"
  shows "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>r* map Tm (u@v)"
  using assms derivers_iff_derives by (metis derives_append_map_Tm)

lemma syms_append_cases[consumes 1, case_names left right]:
  assumes "\<alpha> @ Nt X # map Tm w = \<beta> @ \<gamma>"
  obtains u v where "\<beta> = \<alpha> @ Nt X # map Tm u" "\<gamma> = map Tm v" "w = u @ v" |
          \<delta> where "\<alpha> = \<beta> @ \<delta>" "\<delta> @ Nt X # map Tm w = \<gamma>"
proof (cases "Nt X \<in> set \<gamma>")
  case True
  with syms_decomp_rightmost[of \<alpha> X w \<beta> \<gamma> "[]" "[]"]
  show ?thesis using assms using that(2) by force
next
  case False
  with assms have "Nt X \<in> set \<beta>" 
    by (metis in_set_conv_decomp Un_iff set_append)
  with syms_decomp_rightmost[of \<alpha> X w "[]" \<beta> \<gamma> "[]"]
  show ?thesis using False that(1) Cons_eq_appendI assms by force
qed


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
  by (smt (verit, best) append_same_eq right_derivs_eq_imp_eq_tl rm_chain_decomp rm_chain_reflE
      rm_chain_stepE)

lemma rm_chain_substring:
  assumes "P \<Turnstile> \<alpha> @ Nt X # map Tm v \<Rightarrow>r* \<rho> \<Rightarrow>r* \<beta> @ Nt Y # map Tm w"
  obtains u where "w = u @ v"
  using assms proof (induction "\<alpha> @ Nt X # map Tm v" \<rho> "\<beta> @ Nt Y # map Tm w" arbitrary: \<beta> Y w)
  case refl
  then show ?case using right_derivs_eq_imp_eq_tl[OF refl(1)] by simp
next
  case (step \<rho> \<alpha>' X v \<gamma> Y' \<beta>' u)
  then show ?case 
    by (meson assms derivers_tl_substring rm_chain_imp_derivers that)
qed

lemma rightmost_eq_imp_tl_substring:
  assumes "\<alpha> @ Nt X # map Tm w = \<alpha>' @ \<gamma> @ map Tm v"
  obtains u where "w = u @ v"
  using assms that by (cases "Nt X \<in> set \<gamma>")
    ((meson syms_decomp_rightmost2),
   (metis Tms_iff_no_Nts Un_iff append.assoc append_Nil in_set_conv_decomp 
     set_append syms_decomp_rightmost[of \<alpha> X w "[]" \<alpha>' \<gamma> v]))

lemma syms_split_tl:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
  obtains \<beta>' where "\<beta> = \<beta>' @ map Tm v"
proof -
  consider (Tms) u where "\<beta> = map Tm u" | (rightmost) \<beta>' Y u where "\<beta> = \<beta>' @ Nt Y # map Tm u"
    by (meson Tms_iff_no_Nts syms_split_rightmost)
  then show thesis
  proof cases
    case Tms
    then show ?thesis using rightmost_eq_imp_tl_substring[OF assms[unfolded Tms]] that 
      by fastforce
  next
    case rightmost
    with assms[unfolded this] show ?thesis 
      using rightmost_eq_imp_tl_substring[of "\<alpha> @ Nt X # \<beta>'" Y u] 
      by (metis append.assoc append_Cons map_append that)
  qed
qed

lemma syms_split_leq:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
    "length \<alpha>' \<le> length \<alpha>"
  obtains \<alpha>'' \<beta>'  where "\<alpha> = \<alpha>' @ \<alpha>''" "\<gamma> = \<alpha>'' @ Nt X # \<beta>'" "\<beta> = \<beta>' @ map Tm v"
using assms proof (induction \<alpha>' arbitrary: \<alpha> thesis)
  case Nil
  then show ?case using Nil(1)[of \<alpha>] syms_split_tl[OF Nil(2)] 
    by (smt (verit, ccfv_threshold) Cons_eq_appendI append_assoc append_same_eq self_append_conv2) 
next
  case (Cons a \<alpha>')
  note Cons_\<alpha>' = this
  show ?case 
    by (cases \<alpha>) (use Cons in auto)
qed

lemma syms_split_gt:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
    "length \<alpha>' > length \<alpha>"
  obtains \<alpha>'' where "\<alpha>' = \<alpha> @ Nt X # \<alpha>''" "\<beta> = \<alpha>'' @ \<gamma> @ map Tm v"
using assms proof (induction \<alpha> arbitrary: \<alpha>' thesis)
  case Nil
  then show ?case using Nil(1)[of "[]"] 
    by (metis (no_types, lifting) append_eq_Cons_conv length_greater_0_conv list.size(3))
next
  case (Cons a \<alpha>)
  show ?case 
    by (cases \<alpha>') (use Cons in auto)
qed



lemma syms_split_cases:
  assumes "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v"
  obtains \<alpha>'' \<beta>'  where "\<alpha> = \<alpha>' @ \<alpha>''" "\<gamma> = \<alpha>'' @ Nt X # \<beta>'" "\<beta> = \<beta>' @ map Tm v" |
              \<alpha>'' where "\<alpha>' = \<alpha> @ Nt X # \<alpha>''" "\<beta> = \<alpha>'' @ \<gamma> @ map Tm v"
  by (cases "length \<alpha>' \<le> length \<alpha>")  
    (meson assms that syms_split_leq syms_split_gt not_le_imp_less)+ 

lemma derivers_singleton_imp_produced:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # \<beta>"
  obtains m \<alpha>' B v \<alpha>'' \<beta>' where
    "m < Suc n"
    "P \<turnstile> [Nt A] \<Rightarrow>r(m) \<alpha>' @ Nt B # map Tm v"
    "P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm v"
    "\<alpha> = \<alpha>' @ \<alpha>''"
    "P \<turnstile> \<beta>' @ map Tm v \<Rightarrow>r* \<beta>"
  using assms proof (induction "Suc n" arbitrary: n \<alpha> X \<beta> thesis rule: less_induct)
  case less
  show ?case 
  proof (cases n)
    case 0
    then show ?thesis using less(2)[of 0 "[]" A "[]" \<alpha> \<beta>] less(3) by auto
  next
    case (Suc m)
    note Suc_m = this
    from less(3) obtain \<alpha>' B v where n_steps: "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha>' @ Nt B # map Tm v"
      "P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha> @ Nt X # \<beta>" 
      by (smt (verit) deriver.cases relpowp_Suc_E)
    then obtain \<gamma> where B_prod: "\<alpha> @ Nt X # \<beta> = \<alpha>' @ \<gamma> @ map Tm v" "(B, \<gamma>) \<in> P"
      by (metis deriver_imp_handle in_set_conv_decomp syms_split_rightmost)
    then show thesis proof (cases rule: syms_split_cases)
      case (1 \<alpha>'' \<beta>')
      then show ?thesis using less(2)[OF _ n_steps(1), of \<alpha>'' \<beta>'] B_prod n_steps(2) by fastforce
    next
      case (2 \<alpha>'')
      with n_steps have "P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha> @ Nt X # \<alpha>'' @ Nt B # map Tm v" by simp
      with less(1)[of _ X \<alpha> "\<alpha>'' @ Nt B # map Tm v"] obtain k \<delta> C w \<zeta> \<beta>' where k_steps:
        "k < Suc m" "P \<turnstile> [Nt A] \<Rightarrow>r(k) \<delta> @ Nt C # map Tm w"
        "P \<turnstile> \<delta> @ Nt C # map Tm w \<Rightarrow>r \<delta> @ \<zeta> @ Nt X # \<beta>' @ map Tm w" "\<alpha> = \<delta> @ \<zeta>"
        "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<alpha>'' @ Nt B # map Tm v" using Suc by blast
      from this(5) \<open>\<beta> = \<alpha>'' @ \<gamma> @ map Tm v\<close> B_prod(2) have derivers_\<beta>: "P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* \<beta>" 
        using 2 by (meson deriver.intros rtranclp.simps)
      show ?thesis using less(2)[OF _ k_steps(2-4) derivers_\<beta>] Suc_m k_steps(1) by linarith    
    qed
  qed
qed

lemma derivers_singleton_imp_rm_chain:
  assumes "P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v"
    "P = Prods J"
    "reduced J"
    "LangS J \<noteq> {}"
    "A \<in> Nts P"
  obtains \<rho> where "P \<Turnstile> [Nt A] \<Rightarrow>r* \<rho> \<Rightarrow>r* \<alpha> @ Nt X # map Tm v"
  using assms(1) proof (induction "Suc n" arbitrary: \<alpha> X v n thesis rule: less_induct)
  case (less n)
  show ?case 
  proof (cases n)
    case 0
    then show ?thesis using rm_chain.step[of P "[Nt A]" "[]" "[]" A "[]" \<alpha> X] less by auto
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
          by (metis append1_eq_conv eq_Nil_appendI map_is_Nil_conv relpowp_0_E right_derivs_eq_imp_eq_tl
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