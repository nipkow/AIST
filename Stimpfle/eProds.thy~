theory eProds
  imports "../CFG"
begin

(* AFP-Definition *)
inductive nullable :: "('n,'t) cfg \<Rightarrow> ('n,'t) sym \<Rightarrow> bool"
for g where
  NullableSym:
  "\<lbrakk> (x, gamma) \<in> prodS g; \<forall>s \<in> set gamma. nullable g s \<rbrakk>
  \<Longrightarrow> nullable g (Nt x)"

abbreviation "nullables G w \<equiv> (\<forall>s \<in> set w. nullable G s)"

code_pred nullable .

lemma nullables_if: "(prodS G) \<turnstile> u \<Rightarrow>* v \<Longrightarrow> u=[a] \<Longrightarrow> nullables G v \<Longrightarrow> nullables G u"
proof(induction arbitrary: a rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl u v w)
  from \<open>(prodS G) \<turnstile> v \<Rightarrow> w\<close> \<open>nullables G w\<close> have "nullables G v"
    by (smt (verit, del_insts) Un_iff nullable.simps self_append_conv2 set_ConsD set_append
        derive.cases)
  thus ?case
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by blast
qed

corollary nullable_if: "(prodS G) \<turnstile> [a] \<Rightarrow>* [] \<Longrightarrow> nullable G a"
  using nullables_if[of G "[a]" "[]" a] by simp

lemma nullable: "nullable G a \<Longrightarrow> (prodS G) \<turnstile> [a] \<Rightarrow>* []"
proof (induction  rule: nullable.induct)
  case (NullableSym x gamma)
    hence "(prodS G) \<turnstile> [Nt x] \<Rightarrow>* gamma" 
      using derive_singleton by blast
  also have "(prodS G) \<turnstile> gamma \<Rightarrow>* []" sorry (* TODO *)
  finally show ?case .
qed

fun munge0 :: "('n, 't) cfg \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms list" where
  "munge0 G [] = [[]]" |
  "munge0 G (s#sl) = (
    if nullable G s then ((map ((#) s) (munge0 G sl)) @ munge0 G sl) 
    else (map ((#) s) (munge0 G sl)))"

thm munge0.induct

definition munge :: "('n, 't) cfg \<Rightarrow> ('n \<times> ('n, 't) syms) set \<Rightarrow> ('n \<times> ('n, 't) syms) set" where
"munge G P = {(l,r'). \<exists>r. (l,r) \<in> P \<and> r' \<in> set (munge0 G r) \<and> (r' \<noteq> [])}"

definition "negr G G' = ((prodS G' = munge G (prodS G)) \<and> (start G' = start G))"

(* Why do I not need this anymore? 
(* auxiliary function to prove finiteness *)
definition munge_fun :: "('n, 't) cfg \<Rightarrow> 'n \<times> ('n, 't) syms \<Rightarrow> ('n \<times> ('n, 't) syms) set" where 
  "munge_fun G p = {(l',r'). l' = fst p \<and> r' \<in> set (munge0 G (snd p)) \<and> (r' \<noteq> [])}"

lemma munge_fun_eq: "munge G P = \<Union>((munge_fun G) ` P)"
proof 
  show "munge G P \<subseteq> (\<Union> (munge_fun G ` P))" 
   unfolding munge_def munge_fun_def by auto
next
  show "\<Union>((munge_fun G) ` P) \<subseteq> munge G P"
     fix x
    assume "x \<in> \<Union>((munge_fun G) ` P)"
    obtain l r' where "x = (l,r')" by fastforce
    hence "(l,r') \<in> \<Union>((munge_fun G) ` P)" 
      using \<open>x \<in> \<Union>((munge_fun G) ` P)\<close> by simp
    hence 1: "\<exists>r. r' \<in> set (munge0 G r) \<and> (r' \<noteq> []) \<and> (l,r) \<in> P" 
      using munge_fun_def by fastforce
    from this  obtain r where "r' \<in> set (munge0 G r) \<and> (l,r) \<in> P" 
      by blast
    thus "x \<in> munge G P" unfolding munge_fun_def munge_def
      using 1 \<open>x = (l, r')\<close> by blast 
  qed
qed

(* Had to add the assms, because CFG.thy changed prodS to a set*)
lemma finitenegrProds: 
  assumes "finite P"  
  shows "finite (munge G P)" 
proof -
  have "\<forall>p \<in> P. finite (munge_fun G p)"
    unfolding munge_fun_def by auto
  hence "finite (\<Union>((munge_fun G) ` P))"
    using finite_UN assms by simp
  thus ?thesis using munge_fun_eq by metis
qed
*)

lemma negr_exists: "\<forall>G. \<exists>G'. negr G G'" 
  unfolding negr_def by (metis cfg.sel)

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

lemma negr_r1: "(r' \<in> set (munge0 G r) \<Longrightarrow> (prodS G) \<turnstile> r \<Rightarrow>* r')"
proof (induction r arbitrary: r')
  case (Cons a r)
  then show ?case 
  proof (cases "nullable G a")
    case True
    obtain e where "e \<in> set (munge0 G r) \<and> (r' = (a#e) \<or> r' = e)" (is "?e")
      using Cons.prems True by auto
    hence 1: "(prodS G) \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by blast
    hence 2: "(prodS G) \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using \<open>?e\<close> derives_prepend by blast
    have "(prodS G) \<turnstile> [a] \<Rightarrow>* []" 
      using True nullable(1) by blast
    hence "(prodS G) \<turnstile> [a]@r \<Rightarrow>* r" 
      using derives_append by fastforce
    thus ?thesis 
      using 1 2 \<open>?e\<close> by force 
  next
    case False
    obtain e where "e \<in> set (munge0 G r) \<and> (r' = (a#e))" (is "?e")
      using Cons.prems False by auto
    hence "(prodS G) \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by simp
    hence "(prodS G) \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using derives_prepend by blast
    thus ?thesis
      using \<open>?e\<close> by simp
  qed
qed simp

lemma negr_r2: 
  assumes "negr G G'"
    and "prodS G' \<turnstile> u \<Rightarrow> v"
  shows "prodS G \<turnstile> u \<Rightarrow>* v"
  using assms 
proof -
  obtain A \<alpha> r1 r2 where "(A, \<alpha>) \<in> prodS G' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2" (is "?A")
    using assms derive.cases by meson
  hence 1: "(A, \<alpha>) \<in> {(l,r'). \<exists>r. (l,r) \<in> prodS G \<and> r' \<in> set (munge0 G r) \<and> (r' \<noteq> [])}"
    using assms(1) unfolding negr_def munge_def by simp
  obtain r where "(A, r) \<in> prodS G \<and> \<alpha> \<in> set (munge0 G r)" (is "?r")
    using 1 by blast
  hence "prodS G \<turnstile> r \<Rightarrow>* \<alpha>" 
    using negr_r1 by blast
  hence 2: "prodS G \<turnstile> r1 @ r @ r2 \<Rightarrow>* r1 @ \<alpha> @ r2"
    using \<open>?r\<close> derives_prepend derives_append by blast
  hence "prodS G \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ r @ r2" 
    using \<open>?r\<close> derive.simps by fast
  thus ?thesis 
    using 2 by (simp add: \<open>?A\<close>)
qed

lemma negr_r3:
  assumes "negr G G'"
    and "prodS G' \<turnstile> u \<Rightarrow>* v"
  shows "prodS G \<turnstile> u \<Rightarrow>* v"
  using assms by (smt (verit, del_insts) negr_r2 rtranclp.rtrancl_refl rtranclp_induct rtranclp_trans)

lemma negr_r4:
  assumes "(l,r) \<in> prodS G"
    and "negr G G'"
    and "r' \<in> set (munge0 G r) \<and> (r' \<noteq> [])"
  shows "(l,r') \<in> prodS G'"
  using assms by (smt (verit) case_prod_conv mem_Collect_eq munge_def negr_def)

lemma negr_r5: "r \<in> set (munge0 G r)" 
  by (induction r) auto

lemma negr_r6: 
  assumes "(l,r) \<in> prodS G"
    and "r' \<noteq> []"
    and "no_rhs G r r'"
    and "negr G G'"
  shows "(l,r') \<in> prodS G'"
  using assms negr_r4 unfolding no_rhs_def by fast

lemma negr_r7: 
  assumes "negr G G'"
    and "prodS G \<turnstile> [Nt A] \<Rightarrow> v"
    and "no_rhs G v v' \<and> (v' \<noteq> [])"
  shows "prodS G' \<turnstile> [Nt A] \<Rightarrow> v'"
proof -
  have "(A,v) \<in> prodS G" 
    using assms(2) by (simp add: derive_singleton)
  hence "(A,v') \<in> prodS G'" 
    using assms negr_r6 conjE by fastforce
  thus ?thesis 
    using derive_singleton by fast
qed

lemma negr_r8:
  assumes "negr G G'"
    and "prodS G \<turnstile> [Nt A] \<Rightarrow> v"
    and "no_rhs G v v' \<and> (v' \<noteq> [])"
  shows "prodS G' \<turnstile> [Nt A] \<Rightarrow>* v'"
  using assms negr_r7 by fast

lemma negr_r11:
  assumes "sf \<in> set (munge0 G s) \<and> (sf \<noteq> [])"
    and "negr G G'"
  shows "\<exists>l. ((l,s) \<in> prodS G \<longrightarrow> (l,sf) \<in> prodS G')"
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
  assumes "prodS G \<turnstile> r \<Rightarrow>* rf"
    and "negr G G'"
    and "r = [s]"
    and "no_rhs G rf rf' \<and> (rf' \<noteq> [])"
  shows "prodS G' \<turnstile> r \<Rightarrow>* rf'"
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
      using step derive_from_empty by blast
  next
    case False
    obtain r1 rhs r2 lhs where "b = (r1@[Nt lhs]@r2) \<and> c = (r1@rhs@r2) \<and> (lhs, rhs) \<in> prodS G" (is "?bc")
      using False step by (meson derive.cases)
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
        hence "no_rhs G [Nt lhs] []" 
          unfolding no_rhs_def using \<open>?bc\<close> NullableSym by fastforce
        hence "no_rhs G (r1@[Nt lhs]@r2) (r1'@r2')"
          using negr_r12b[of G r1 r1' "[Nt lhs]" "[]" r2 r2'] \<open>?rf'\<close> by simp
        then show ?thesis 
          using \<open>?bc\<close> \<open>rf' = r1' @ r2'\<close> step by blast
    next
      case False
        have "no_rhs G (r1@[Nt lhs]@r2) (r1'@[Nt lhs]@r2')"
          using negr_r12b[of G r1 r1' \<open>[Nt lhs]\<close> \<open>[Nt lhs]\<close> r2 r2'] negr_r5[of \<open>[Nt lhs]\<close> G] no_rhs_def \<open>?rf'\<close> by blast
        hence 1: "prodS G' \<turnstile> [s] \<Rightarrow>* (r1'@[Nt lhs]@r2')" 
          using \<open>?bc\<close> step by blast
        have "prodS G \<turnstile> [Nt lhs] \<Rightarrow> rhs" 
          using \<open>?bc\<close> step(2) derive_singleton by blast
        hence "prodS G' \<turnstile> [Nt lhs] \<Rightarrow> rhs'"
          using negr_r7[of G G' lhs rhs rhs'] False step \<open>?rf'\<close> by blast
        hence "prodS G' \<turnstile> (r1'@[Nt lhs]@r2') \<Rightarrow> (r1'@rhs'@r2')" 
          using derive_append derive_prepend by blast
        thus ?thesis using 1
        by (simp add: \<open>?rf'\<close> step.prems(2))
    qed
  qed
qed

definition "isWord w \<longleftrightarrow> (\<nexists>A. Nt A \<in> set w)"   
definition "L G = {w. prodS G \<turnstile> [Nt (start G)] \<Rightarrow>* w \<and> isWord w}"

theorem negr_eq_if_noe:
  assumes "negr G G'"
    and "[] \<notin> L G"
  shows "L G = L G'"
proof 
  show "L G \<subseteq> L G'"
  proof 
    fix x
    assume "x \<in> L G"
    have "\<forall>x. prodS G \<turnstile> [Nt (start G)] \<Rightarrow>* x \<longrightarrow> x \<noteq> []"
      using assms L_def isWord_def by fastforce
    hence 1: "no_rhs G x x" 
      unfolding no_rhs_def using negr_r5 by auto
    have "start G' = start G"
      using assms(1) negr_def by blast
    hence "prodS G' \<turnstile> [Nt (start G')] \<Rightarrow>* x"
      using 1 assms L_def \<open>x \<in> L G\<close> by (metis (no_types, lifting) CollectD negr_r15)
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
  shows "\<nexists>p. p \<in> prodS G' \<and> snd p = []"
  using assms unfolding negr_def munge_def by simp

lemma negr_correct2:
  assumes "negr G G'"
  shows "[] \<notin> L G'"
  using assms unfolding negr_def L_def munge_def isWord_def 
  by (smt (verit, ccfv_threshold) CollectD append_is_Nil_conv case_prod_conv derive.cases not_Cons_self2 rtranclp.cases)

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