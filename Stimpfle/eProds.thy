theory eProds
  imports CFG
begin

(* AFP-Definition *)
inductive nullable :: "('n,'t)cfg \<Rightarrow> ('n,'t)symbol \<Rightarrow> bool"
for g where
  NullableSym:
  "\<lbrakk> (x, gamma) \<in> set (prods g); \<forall>s \<in> set gamma. nullable g s \<rbrakk>
  \<Longrightarrow> nullable g (NT x)"

abbreviation "nullables G w \<equiv> (\<forall>s \<in> set w. nullable G s)"

code_pred nullable .

lemma nullables_if: "G \<turnstile> u \<Rightarrow>* v \<Longrightarrow> u=[a] \<Longrightarrow> nullables G v \<Longrightarrow> nullables G u"
proof(induction arbitrary: a rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl u v w)
  from \<open>G \<turnstile> v \<Rightarrow> w\<close> \<open>nullables G w\<close> have "nullables G v"
    by (smt (verit, del_insts) Un_iff nullable.simps self_append_conv2 set_ConsD set_append
        step1.cases)
  thus ?case
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by blast
qed

corollary nullable_if: "G \<turnstile> [a] \<Rightarrow>* [] \<Longrightarrow> nullable G a"
using nullables_if[of G "[a]" "[]" a] by simp

lemma nullable: "nullable G a \<Longrightarrow> G \<turnstile> [a] \<Rightarrow>* []"
proof (induction  rule: nullable.induct)
  case (NullableSym x gamma)
    hence "G \<turnstile> [NT x] \<Rightarrow>* gamma" 
      using deriv1_if_valid_prod by fastforce
  also have "G \<turnstile> gamma \<Rightarrow>* []" sorry
  finally show ?case .
qed

(*
thm nullable_nullable_gamma.inducts
thm nullable_nullable_gamma.induct
thm nullable_nullable_gamma.intros
thm nullable.cases
thm nullable_gamma.cases
thm nullable_nullable_gamma.NullableSym
thm nullable_nullable_gamma.NullableNil
thm nullable_nullable_gamma.NullableCons

lemma nullable_not2: "(G \<turnstile> [a] \<Rightarrow>* []) \<Longrightarrow> nullable G a" (G \<turnstile> r \<Rightarrow>* []) \<Longrightarrow> nullable_gamma G r"
proof (induction  rule: nullable_nullable_gamma.inducts)
*)

fun munge0 :: "('n, 't) cfg \<Rightarrow> ('n, 't) rhs \<Rightarrow> ('n, 't) rhs list" where
  "munge0 G [] = [[]]" |
  "munge0 G (s#sl) = (
    if nullable G s then ((map ((#) s) (munge0 G sl)) @ munge0 G sl) 
    else (map ((#) s) (munge0 G sl)))"

thm munge0.induct

definition munge :: "('n, 't) cfg \<Rightarrow> ('n \<times> ('n, 't) symbol list) list \<Rightarrow> ('n \<times> ('n, 't) symbol list) set" where
"munge G P = {(l,r'). \<exists>r. (l,r) \<in> set P \<and> r' \<in> set (munge0 G r) \<and> (r' \<noteq> [])}"

definition "negr G G' = ((set (prods G') = munge G (prods G)) \<and> (start G' = start G))"

(* auxiliary function to prove finiteness *)
definition munge_fun :: "('n, 't) cfg \<Rightarrow> 'n \<times> ('n, 't) symbol list \<Rightarrow> ('n \<times> ('n, 't) symbol list) set" where 
  "munge_fun G p = {(l',r'). l' = fst p \<and> r' \<in> set (munge0 G (snd p)) \<and> (r' \<noteq> [])}"

lemma munge_fun_eq: "munge G P = \<Union>((munge_fun G) ` (set P))"
proof 
  show "munge G P \<subseteq> (\<Union> (munge_fun G ` set P))" 
   unfolding munge_def munge_fun_def by auto
next
  show "\<Union>((munge_fun G) ` (set P)) \<subseteq> munge G P"
  proof 
    fix x
    assume "x \<in> \<Union>((munge_fun G) ` (set P))"
    obtain l r' where "x = (l,r')" by fastforce
    hence "(l,r') \<in> \<Union>((munge_fun G) ` (set P))" 
      using \<open>x \<in> \<Union>((munge_fun G) ` (set P))\<close> by simp
    hence 1: "\<exists>r. r' \<in> set (munge0 G r) \<and> (r' \<noteq> []) \<and> (l,r) \<in> (set P)" 
      using munge_fun_def by fastforce
    from this  obtain r where "r' \<in> set (munge0 G r) \<and> (l,r) \<in> (set P)" 
      by blast
    thus "x \<in> munge G P" unfolding munge_fun_def munge_def
      using 1 \<open>x = (l, r')\<close> by blast 
  qed
qed

lemma finitenegrProds: "finite (munge G P)" 
proof -
  have "\<forall>p \<in> set P. finite (munge_fun G p)"
    unfolding munge_fun_def by auto
  hence "finite (\<Union>((munge_fun G) ` (set P)))"
    using finite_UN by auto
  thus ?thesis using munge_fun_eq by metis
qed

lemma negr_exists: "\<forall>G. \<exists>G'. negr G G'" 
  unfolding negr_def by (metis cfg.sel finite_list finitenegrProds)

lemma eq_snegr: "negr G G' \<Longrightarrow> (start G = start G')"
  by (simp add: negr_def)

definition "no_rhs G l1 l2 = (l2 \<in> set (munge0 G l1))"

definition "no_prod G p1 p2 = ((fst p1 = fst p2) \<and> snd p2 \<in> set (munge0 G (snd p1)))"

lemma no_rhs_nullable: 
  assumes "no_rhs G r []"
  shows "nullables G r"
  using assms unfolding no_rhs_def 
proof (induction rule: munge0.induct)
  case (1 G)
  then show ?case by (simp)
next
  case (2 G s sl)
  then show ?case
    by (smt (verit, ccfv_threshold) Un_iff imageE list.set_map list.simps(3) munge0.simps(2) set_ConsD
        set_append) 
qed

lemma negr_r1: "(r' \<in> set (munge0 G r) \<Longrightarrow> G \<turnstile> r \<Rightarrow>* r')"
proof (induction r arbitrary: r')
  case (Cons a r)
  then show ?case 
  proof (cases "nullable G a")
    case True
    obtain e where "e \<in> set (munge0 G r) \<and> (r' = (a#e) \<or> r' = e)" (is "?e")
      using Cons.prems True by auto
    hence 1: "G \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by blast
    hence 2: "G \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using \<open>?e\<close> deriv_prepend by blast
    have "G \<turnstile> [a] \<Rightarrow>* []" 
      using True nullable(1) by blast
    hence "G \<turnstile> [a]@r \<Rightarrow>* r" 
      using deriv_apppend by fastforce
    thus ?thesis 
      using 1 2 \<open>?e\<close> by force 
  next
    case False
    obtain e where "e \<in> set (munge0 G r) \<and> (r' = (a#e))" (is "?e")
      using Cons.prems False by auto
    hence "G \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by simp
    hence "G \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using deriv_prepend by blast
    thus ?thesis
      using \<open>?e\<close> by simp
  qed
qed simp

lemma negr_r2: 
  assumes "negr G G'"
    and "G' \<turnstile> u \<Rightarrow> v"
  shows "G \<turnstile> u \<Rightarrow>* v"
  using assms 
proof -
  obtain A \<alpha> r1 r2 where "(A, \<alpha>) \<in> set (prods G') \<and> u = r1 @ [NT A] @ r2 \<and> v = r1 @ \<alpha> @ r2" (is "?A")
    using assms step1.cases by meson
  hence 1: "(A, \<alpha>) \<in> {(l,r'). \<exists>r. (l,r) \<in> set (prods G) \<and> r' \<in> set (munge0 G r) \<and> (r' \<noteq> [])}"
    using assms(1) unfolding negr_def munge_def by simp
  obtain r where "(A, r) \<in> set (prods G) \<and> \<alpha> \<in> set (munge0 G r)" (is "?r")
    using 1 by blast
  hence "G \<turnstile> r \<Rightarrow>* \<alpha>" 
    using negr_r1 by blast
  hence 2: "G \<turnstile> r1 @ r @ r2 \<Rightarrow>* r1 @ \<alpha> @ r2"
    using \<open>?r\<close> deriv_prepend deriv_apppend by blast
  hence "G \<turnstile> r1 @ [NT A] @ r2 \<Rightarrow> r1 @ r @ r2" 
    using \<open>?r\<close> step1.simps by blast
  thus ?thesis 
    using 2 by (simp add: \<open>?A\<close>)
qed

lemma negr_r3:
  assumes "negr G G'"
    and "G' \<turnstile> u \<Rightarrow>* v"
  shows "G \<turnstile> u \<Rightarrow>* v"
  using assms by (smt (verit, del_insts) negr_r2 rtranclp.rtrancl_refl rtranclp_induct rtranclp_trans)

lemma negr_r4:
  assumes "(l,r) \<in> set (prods G)"
    and "negr G G'"
    and "r' \<in> set (munge0 G r) \<and> (r' \<noteq> [])"
  shows "(l,r') \<in> set (prods G')"
  using assms by (smt (verit) case_prod_conv mem_Collect_eq munge_def negr_def)

lemma negr_r5: "r \<in> set (munge0 G r)" 
  by (induction r) auto

lemma negr_r6: 
  assumes "(l,r) \<in> set (prods G)"
    and "r' \<noteq> []"
    and "no_rhs G r r'"
    and "negr G G'"
  shows "(l,r') \<in> set (prods G')"
  using assms negr_r4 unfolding no_rhs_def by fast

lemma negr_r7: 
  assumes "negr G G'"
    and "G \<turnstile> [NT A] \<Rightarrow> v"
    and "no_rhs G v v' \<and> (v' \<noteq> [])"
  shows "G' \<turnstile> [NT A] \<Rightarrow> v'"
proof -
  have "(A,v) \<in> set (prods G)" 
    using assms(2) valid_prod_if_deriv1 by fast
  hence "(A,v') \<in> set (prods G')" 
    using assms negr_r6 conjE by fastforce
  thus ?thesis 
    using deriv1_if_valid_prod by fast
qed

lemma negr_r8:
  assumes "negr G G'"
    and "G \<turnstile> [NT A] \<Rightarrow> v"
    and "no_rhs G v v' \<and> (v' \<noteq> [])"
  shows "G' \<turnstile> [NT A] \<Rightarrow>* v'"
  using assms negr_r7 by fast

(* lemma negr_r9 & negr_r10 \<Longrightarrow> nullable_rev 

lemma negr_r9:
  assumes "\<not>nullable_gamma G r"
    and "G \<turnstile> r \<Rightarrow>* r'"
  shows "r' \<noteq> []"
  using assms apply (induction r arbitrary: r') apply auto 
  apply (simp add: NullableNil) sorry
*)
  
lemma negr_r11:
  assumes "sf \<in> set (munge0 G s) \<and> (sf \<noteq> [])"
    and "negr G G'"
  shows "\<exists>l. ((l,s) \<in> set (prods G) \<longrightarrow> (l,sf) \<in> set (prods G'))"
  using assms by (meson negr_r4)

lemma negr_r12a: 
  assumes "no_rhs G r1 r1'"
    and "no_rhs G r2 r2'"
  shows "no_rhs G (r1@r2) (r1'@r2')"
  using assms unfolding no_rhs_def 
  apply (induction r1 arbitrary: r1' r2 r2' rule: munge0.induct) by auto

lemma negr_r12b:
  assumes "no_rhs G r1 r1'"
    and "no_rhs G r2 r2'"
    and "no_rhs G r3 r3'"
  shows "no_rhs G (r1@r2@r3) (r1'@r2'@r3')"
  using assms unfolding no_rhs_def 
  apply (induction r1 arbitrary: r1' r2 r2' r3 r3' rule: munge0.induct) 
   apply auto 
  using negr_r12a no_rhs_def by blast

lemma negr_r13:
  assumes "no_rhs G r r'"
  shows "(\<exists>r1 r2 r1' r2'. (r=r1@r2) \<and> (r'=r1'@r2') \<and> no_rhs G r1 r1' \<and> no_rhs G r2 r2')"
  using assms unfolding no_rhs_def 
  apply (induction r arbitrary: r' rule: munge0.induct) 
   apply auto 
  by fastforce

lemma negr_r14:
  assumes "no_rhs G (r1@r2) r'"
  shows "(\<exists>r1' r2'. (r'=r1'@r2') \<and> no_rhs G r1 r1' \<and> no_rhs G r2 r2')"
  using assms unfolding no_rhs_def 
  apply (induction r1 arbitrary: r2 r' rule: munge0.induct) 
   apply auto 
  by (metis append_Cons imageI)+    


lemma negr_r15:
  assumes "G \<turnstile> r \<Rightarrow>* rf"
    and "negr G G'"
    and "r = [s]"
    and "no_rhs G rf rf' \<and> (rf' \<noteq> [])"
  shows "G' \<turnstile> r \<Rightarrow>* rf'"
  using assms
proof (induction arbitrary: rf')
  case base
  then show ?case 
  proof (cases "nullables G r")
    case True
    then show ?thesis 
      by (smt (verit, del_insts) Un_iff append.left_neutral base.prems(2) base.prems(3) concat.simps(1) concat.simps(2) concat_eq_Nil_conv munge0.simps(1) munge0.simps(2) negr_r1 no_rhs_def set_append) 
  next
    case False
    then show ?thesis
      by (metis (no_types, lifting) base.prems(1,2,3) empty_iff empty_set munge0.simps(1,2) negr_r1 negr_r3
          no_rhs_def nullable nullable_if set_ConsD)
  qed
next
  case (step b c)
  then show ?case 
  proof (cases "b = []")
    case True
    then show ?thesis 
      using step Derivation1_from_empty by blast 
  next
    case False
    obtain r1 rhs r2 lhs where "b = (r1@[NT lhs]@r2) \<and> c = (r1@rhs@r2) \<and> (lhs, rhs) \<in> set (prods G)" (is "?bc")
      using False step by (meson step1.cases)
    from this obtain r1' rhs' r2' where 
      "(rf' = (r1'@rhs'@r2')) \<and> no_rhs G r1 r1' \<and> no_rhs G rhs rhs' \<and> no_rhs G r2 r2'" (is "?rf'")
      using step negr_r14 by metis
    then show ?thesis 
    proof (cases "rhs' = []")
      case True
        hence "rf' = r1'@r2'" 
          using \<open>?rf'\<close> by simp 
        have "no_rhs G rhs []"
          using True \<open>?rf'\<close> by simp
        hence "nullables G rhs"
          using no_rhs_nullable by blast
        hence "no_rhs G [NT lhs] []" 
          unfolding no_rhs_def using \<open>?bc\<close> NullableSym by fastforce
        hence "no_rhs G (r1@[NT lhs]@r2) (r1'@r2')"
          using negr_r12b[of G r1 r1' "[NT lhs]" "[]" r2 r2'] \<open>?rf'\<close> by simp
        then show ?thesis 
          using \<open>?bc\<close> \<open>rf' = r1' @ r2'\<close> step by blast
    next
      case False
        have "no_rhs G (r1@[NT lhs]@r2) (r1'@[NT lhs]@r2')"
          using negr_r12b[of G r1 r1' \<open>[NT lhs]\<close> \<open>[NT lhs]\<close> r2 r2'] negr_r5[of \<open>[NT lhs]\<close> G] no_rhs_def \<open>?rf'\<close> by blast
        hence 1: "G' \<turnstile> [s] \<Rightarrow>* (r1'@[NT lhs]@r2')" 
          using \<open>?bc\<close> step by blast
        have "G \<turnstile> [NT lhs] \<Rightarrow> rhs" 
          using \<open>?bc\<close> step(2) deriv1_if_valid_prod[of lhs rhs G] by simp
        hence "G' \<turnstile> [NT lhs] \<Rightarrow> rhs'"
          using negr_r7[of G G' lhs rhs rhs'] False step \<open>?rf'\<close> by blast
        hence "G' \<turnstile> (r1'@[NT lhs]@r2') \<Rightarrow> (r1'@rhs'@r2')" 
          using step1_apppend step1_prepend by blast
        thus ?thesis using 1
        by (simp add: \<open>?rf'\<close> step.prems(2))
    qed
  qed
qed

theorem negr_eq_if_noe:
  assumes "negr G G'"
    and "[] \<notin> L G"
  shows "L G = L G'"
proof 
  show "L G \<subseteq> L G'"
  proof 
    fix x
    assume "x \<in> L G"
    have "\<forall>x. G \<turnstile> [NT (start G)] \<Rightarrow>* x \<longrightarrow> x \<noteq> []"
      using assms L_def isWord_def by fastforce
    hence 1: "no_rhs G x x" 
      unfolding no_rhs_def using negr_r5 by auto
    have "start G' = start G"
      using assms(1) negr_def by blast
    hence "G' \<turnstile> [NT (start G')] \<Rightarrow>* x"
      using negr_r15[of G "[NT (start G')]" x G' x] using 1 assms L_def \<open>x \<in> L G\<close> by auto
    thus "x \<in> L G'"
      using L_def \<open>x \<in> L G\<close> by auto
  qed
next
  show "L G' \<subseteq> L G"
  proof
    fix x'
    assume "x' \<in> L G'"
    show "x' \<in> L G" using assms
      by (metis (no_types, lifting) CollectD CollectI L_def \<open>x' \<in> L G'\<close> eq_snegr negr_r3)
  qed
qed

(* correctness *)
lemma negr_correct:
  assumes "negr G G'"
  shows "\<nexists>p. p \<in> set (prods G') \<and> snd p = []"
  using assms unfolding negr_def munge_def by simp

lemma negr_correct2:
  assumes "negr G G'"
  shows "[] \<notin> L G'"
  using assms unfolding negr_def L_def munge_def isWord_def 
  by (smt (verit, best) append_is_Nil_conv case_prod_conv list.distinct(1) mem_Collect_eq rtranclp.simps step1.cases)

lemma negr_correct3:
  assumes "negr G G'"
  shows "L G' = L G - {[]}"
sorry

(*
lemma negr_correct3:
  assumes "negr G G'"
    and "L \<G> = L G - {[]}"
  shows "L \<G> = L G'"
  using assms unfolding negr_def L_def munge_def isWord_def sorry
*)

end