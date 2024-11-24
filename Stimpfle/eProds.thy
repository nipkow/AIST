theory eProds
  imports "../CFG"
begin

inductive nullable :: "('n,'t) prods \<Rightarrow> ('n,'t) sym \<Rightarrow> bool"
for P where
  NullableSym:
  "\<lbrakk> (x, gamma) \<in> set P; \<forall>s \<in> set gamma. nullable P s \<rbrakk>
  \<Longrightarrow> nullable P (Nt x)"

abbreviation "nullables P w \<equiv> (\<forall>s \<in> set w. nullable P s)"

lemma nullables_if: 
  assumes "set P \<turnstile> u \<Rightarrow>* v" 
    and "u=[a]" "nullables P v"
  shows "nullables P u"
  using assms
proof(induction arbitrary: a rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl u v w)
  from \<open>set P \<turnstile> v \<Rightarrow> w\<close> \<open>nullables P w\<close> have "nullables P v"
    by (smt (verit, del_insts) Un_iff nullable.simps self_append_conv2 set_ConsD set_append
        derive.cases)
  thus ?case
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by blast
qed

corollary nullable_if: "set P \<turnstile> [a] \<Rightarrow>* [] \<Longrightarrow> nullable P a"
  using nullables_if[of P "[a]" "[]" a] by simp

lemma nullable_aux: "\<forall>s\<in>set gamma. nullable P s \<and> set P \<turnstile> [s] \<Rightarrow>* [] \<Longrightarrow> set P \<turnstile> gamma \<Rightarrow>* []"
proof (induction gamma)
  case (Cons a list)
  hence "set P \<turnstile> list \<Rightarrow>* []"
    by simp
  moreover have "set P \<turnstile> [a] \<Rightarrow>* []"
    using Cons by simp
  ultimately show ?case 
    using derives_Cons[of \<open>set P\<close> list \<open>[]\<close> \<open>a\<close>] by simp
qed simp

lemma nullable: "nullable P a \<Longrightarrow> set P \<turnstile> [a] \<Rightarrow>* []"
proof (induction rule: nullable.induct)
  case (NullableSym x gamma)
    hence "set P \<turnstile> [Nt x] \<Rightarrow>* gamma" 
      using derive_singleton by blast
    also have "set P \<turnstile> gamma \<Rightarrow>* []" 
      using NullableSym nullable_aux by blast
  finally show ?case .
qed

fun munge0 :: "('n, 't) prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms list" where
  "munge0 P [] = [[]]" |
  "munge0 P (s#sl) = (
    if nullable P s then ((map ((#) s) (munge0 P sl)) @ munge0 P sl) 
    else (map ((#) s) (munge0 P sl)))"

definition munge :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
"munge P = {(l,r'). \<exists>r. (l,r) \<in> set P \<and> r' \<in> set (munge0 P r) \<and> (r' \<noteq> [])}"

definition nepr :: "('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> bool" where 
  "nepr P P' = (set P' = munge P)"

(* auxiliary function to prove finiteness *)
definition munge_fun :: "('n, 't) prods \<Rightarrow> ('n, 't) prod \<Rightarrow> ('n, 't) Prods" where 
  "munge_fun P p = {(l',r'). l' = fst p \<and> r' \<in> set (munge0 P (snd p)) \<and> (r' \<noteq> [])}"

lemma munge_fun_eq: "munge P = \<Union>((munge_fun P) ` set P)"
proof 
  show "munge P \<subseteq> (\<Union> (munge_fun P ` set P))" 
   unfolding munge_def munge_fun_def by auto
next
  show "\<Union>((munge_fun P) ` set P) \<subseteq> munge P"
  proof
    fix x
    assume "x \<in> \<Union>((munge_fun P) ` set P)"
    obtain l r' where "x = (l,r')" by fastforce
    hence "(l,r') \<in> \<Union>((munge_fun P) ` set P)" 
      using \<open>x \<in> \<Union>((munge_fun P) ` set P)\<close> by simp
    hence 1: "\<exists>r. r' \<in> set (munge0 P r) \<and> (r' \<noteq> []) \<and> (l,r) \<in> set P" 
      using munge_fun_def by fastforce
    from this  obtain r where "r' \<in> set (munge0 P r) \<and> (l,r) \<in> set P" 
      by blast
    thus "x \<in> munge P" unfolding munge_fun_def munge_def
      using 1 \<open>x = (l, r')\<close> by blast 
  qed
qed

lemma finiteneprProds: "finite (munge P)" 
proof -
  have "\<forall>p \<in> set P. finite (munge_fun P p)"
    unfolding munge_fun_def by auto
  hence "finite (\<Union>((munge_fun P) ` set P))"
    using finite_UN by simp
  thus ?thesis using munge_fun_eq by metis
qed

lemma nepr_exists: "\<forall>P. \<exists>P'. nepr P P'"
  unfolding nepr_def by (simp add: finite_list finiteneprProds)


definition no_rhs :: "('n, 't) prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms \<Rightarrow> bool" where
  "no_rhs P l1 l2 = (l2 \<in> set (munge0 P l1))"

lemma no_rhs_nullable: 
  assumes "no_rhs P r []"
  shows "nullables P r"
  using assms unfolding no_rhs_def 
proof (induction rule: munge0.induct)
  case (1 P)
  then show ?case by (simp)
next
  case (2 P s sl)
  then show ?case
    by (smt (verit, ccfv_threshold) Un_iff imageE list.set_map list.simps(3) munge0.simps(2) set_ConsD
        set_append) 
qed

lemma nepr_r1: "(r' \<in> set (munge0 P r) \<Longrightarrow> set P \<turnstile> r \<Rightarrow>* r')"
proof (induction r arbitrary: r')
  case (Cons a r)
  then show ?case 
  proof (cases "nullable P a")
    case True
    obtain e where "e \<in> set (munge0 P r) \<and> (r' = (a#e) \<or> r' = e)" (is "?e")
      using Cons.prems True by auto
    hence 1: "set P \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by blast
    hence 2: "set P \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using \<open>?e\<close> derives_prepend by blast
    have "set P \<turnstile> [a] \<Rightarrow>* []" 
      using True nullable(1) by blast
    hence "set P \<turnstile> [a]@r \<Rightarrow>* r" 
      using derives_append by fastforce
    thus ?thesis 
      using 1 2 \<open>?e\<close> by force 
  next
    case False
    obtain e where "e \<in> set (munge0 P r) \<and> (r' = (a#e))" (is "?e")
      using Cons.prems False by auto
    hence "set P \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by simp
    hence "set P \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using derives_prepend by blast
    thus ?thesis
      using \<open>?e\<close> by simp
  qed
qed simp

lemma nepr_r2: 
  assumes "nepr P P'"
    and "set P' \<turnstile> u \<Rightarrow> v"
  shows "set P \<turnstile> u \<Rightarrow>* v"
  using assms 
proof -
  obtain A \<alpha> r1 r2 where "(A, \<alpha>) \<in> set P' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2" (is "?A")
    using assms derive.cases by meson
  hence 1: "(A, \<alpha>) \<in> {(l,r'). \<exists>r. (l,r) \<in> set P \<and> r' \<in> set (munge0 P r) \<and> (r' \<noteq> [])}"
    using assms(1) unfolding nepr_def munge_def by simp
  obtain r where "(A, r) \<in> set P \<and> \<alpha> \<in> set (munge0 P r)" (is "?r")
    using 1 by blast
  hence "set P \<turnstile> r \<Rightarrow>* \<alpha>" 
    using nepr_r1 by blast
  hence 2: "set P \<turnstile> r1 @ r @ r2 \<Rightarrow>* r1 @ \<alpha> @ r2"
    using \<open>?r\<close> derives_prepend derives_append by blast
  hence "set P \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ r @ r2" 
    using \<open>?r\<close> derive.simps by fast
  thus ?thesis 
    using 2 by (simp add: \<open>?A\<close>)
qed

lemma nepr_r3:
  assumes "nepr P P'"
    and "set P' \<turnstile> u \<Rightarrow>* v"
  shows "set P \<turnstile> u \<Rightarrow>* v"
  using assms by (smt (verit, del_insts) nepr_r2 rtranclp.rtrancl_refl rtranclp_induct rtranclp_trans)

lemma nepr_r4:
  assumes "(l,r) \<in> set P"
    and "nepr P P'"
    and "r' \<in> set (munge0 P r) \<and> (r' \<noteq> [])"
  shows "(l,r') \<in> set P'"
  using assms by (smt (verit) case_prod_conv mem_Collect_eq munge_def nepr_def)

lemma nepr_r5: "r \<in> set (munge0 P r)" 
  by (induction r) auto

lemma nepr_r6: 
  assumes "(l,r) \<in> set P"
    and "r' \<noteq> []"
    and "no_rhs P r r'"
    and "nepr P P'"
  shows "(l,r') \<in> set P'"
  using assms nepr_r4 unfolding no_rhs_def by fast

lemma nepr_r7: 
  assumes "nepr P P'"
    and "set P \<turnstile> [Nt A] \<Rightarrow> v"
    and "no_rhs P v v' \<and> (v' \<noteq> [])"
  shows "set P' \<turnstile> [Nt A] \<Rightarrow> v'"
proof -
  have "(A,v) \<in> set P" 
    using assms(2) by (simp add: derive_singleton)
  hence "(A,v') \<in> set P'" 
    using assms nepr_r6 conjE by fastforce
  thus ?thesis 
    using derive_singleton by fast
qed

lemma nepr_r8:
  assumes "nepr P P'"
    and "set P \<turnstile> [Nt A] \<Rightarrow> v"
    and "no_rhs P v v' \<and> (v' \<noteq> [])"
  shows "set P' \<turnstile> [Nt A] \<Rightarrow>* v'"
  using assms nepr_r7 by fast

lemma nepr_r12a: 
  assumes "no_rhs P r1 r1'"
    and "no_rhs P r2 r2'"
  shows "no_rhs P (r1@r2) (r1'@r2')"
  using assms unfolding no_rhs_def 
  apply (induction r1 arbitrary: r1' r2 r2' rule: munge0.induct) by auto

lemma nepr_r12b:
  assumes "no_rhs P r1 r1'"
    and "no_rhs P r2 r2'"
    and "no_rhs P r3 r3'"
  shows "no_rhs P (r1@r2@r3) (r1'@r2'@r3')"
  using assms unfolding no_rhs_def 
  apply (induction r1 arbitrary: r1' r2 r2' r3 r3' rule: munge0.induct) 
   apply auto 
  using nepr_r12a no_rhs_def by blast

lemma nepr_r13:
  assumes "no_rhs P r r'"
  shows "(\<exists>r1 r2 r1' r2'. (r=r1@r2) \<and> (r'=r1'@r2') \<and> no_rhs P r1 r1' \<and> no_rhs P r2 r2')"
  using assms unfolding no_rhs_def 
  apply (induction r arbitrary: r' rule: munge0.induct) 
   apply auto 
  by fastforce

lemma nepr_r14:
  assumes "no_rhs P (r1@r2) r'"
  shows "(\<exists>r1' r2'. (r'=r1'@r2') \<and> no_rhs P r1 r1' \<and> no_rhs P r2 r2')"
  using assms unfolding no_rhs_def 
  apply (induction r1 arbitrary: r2 r' rule: munge0.induct) 
   apply auto 
  by (metis append_Cons imageI)+    


lemma nepr_r15:
  assumes "set P \<turnstile> r \<Rightarrow>* rf"
    and "nepr P P'"
    and "r = [S]"
    and "no_rhs P rf rf' \<and> (rf' \<noteq> [])"
  shows "set P' \<turnstile> r \<Rightarrow>* rf'"
  using assms
proof (induction arbitrary: rf')
  case base
  then show ?case 
  proof (cases "nullables P r")
    case True
    then show ?thesis 
      by (smt (verit, del_insts) Un_iff append.left_neutral base.prems(2) base.prems(3) concat.simps(1) concat.simps(2) concat_eq_Nil_conv munge0.simps(1) munge0.simps(2) nepr_r1 no_rhs_def set_append) 
  next
    case False
    then show ?thesis
      by (metis (no_types, lifting) base.prems(1,2,3) empty_iff empty_set munge0.simps(1,2) nepr_r1 nepr_r3
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
    obtain r1 rhs r2 lhs where "b = (r1@[Nt lhs]@r2) \<and> c = (r1@rhs@r2) \<and> (lhs, rhs) \<in> set P" (is "?bc")
      using False step by (meson derive.cases)
    from this obtain r1' rhs' r2' where 
      "(rf' = (r1'@rhs'@r2')) \<and> no_rhs P r1 r1' \<and> no_rhs P rhs rhs' \<and> no_rhs P r2 r2'" (is "?rf'")
      using step nepr_r14 by metis
    then show ?thesis 
    proof (cases "rhs' = []")
      case True
        hence "rf' = r1'@r2'" 
          using \<open>?rf'\<close> by simp 
        have "no_rhs P rhs []"
          using True \<open>?rf'\<close> by simp
        hence "nullables P rhs"
          using no_rhs_nullable by blast
        hence "no_rhs P [Nt lhs] []" 
          unfolding no_rhs_def using \<open>?bc\<close> NullableSym by fastforce
        hence "no_rhs P (r1@[Nt lhs]@r2) (r1'@r2')"
          using nepr_r12b[of P r1 r1' "[Nt lhs]" "[]" r2 r2'] \<open>?rf'\<close> by simp
        then show ?thesis 
          using \<open>?bc\<close> \<open>rf' = r1' @ r2'\<close> step by blast
    next
      case False
        have "no_rhs P (r1@[Nt lhs]@r2) (r1'@[Nt lhs]@r2')"
          using nepr_r12b[of P r1 r1' \<open>[Nt lhs]\<close> \<open>[Nt lhs]\<close> r2 r2'] nepr_r5[of \<open>[Nt lhs]\<close> P] no_rhs_def \<open>?rf'\<close> by blast
        hence 1: "set P' \<turnstile> [S] \<Rightarrow>* (r1'@[Nt lhs]@r2')" 
          using \<open>?bc\<close> step by blast
        have "set P \<turnstile> [Nt lhs] \<Rightarrow> rhs" 
          using \<open>?bc\<close> step(2) derive_singleton by blast
        hence "set P' \<turnstile> [Nt lhs] \<Rightarrow> rhs'"
          using nepr_r7[of P P' lhs rhs rhs'] False step \<open>?rf'\<close> by blast
        hence "set P' \<turnstile> (r1'@[Nt lhs]@r2') \<Rightarrow> (r1'@rhs'@r2')" 
          using derive_append derive_prepend by blast
        thus ?thesis using 1
        by (simp add: \<open>?rf'\<close> step.prems(2))
    qed
  qed
qed

(* Proof that Aditis definition of L G is the same as Lang (Prods G) (Start G). This part has become obsolete *)
definition "isWord w \<longleftrightarrow> (\<nexists>A. Nt A \<in> set w)"   
definition "L G = {w. Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* w \<and> isWord w}"

lemma L_eq_Lang1: "(map Tm) ` Lang (Prods G) (Start G) \<subseteq> L G"
proof -
  have "\<forall>w \<in> Lang (Prods G) (Start G). isWord (map Tm w)"
    unfolding isWord_def by auto
  moreover have "\<forall>w \<in> Lang (Prods G) (Start G). (Prods G) \<turnstile> [Nt (Start G)] \<Rightarrow>* (map Tm w)"
    unfolding Lang_def by simp
  ultimately show ?thesis
    using L_def by blast
qed

lemma L_eq_Lang2: "L G \<subseteq> (map Tm) ` Lang (Prods G) (Start G)"
proof 
  fix w
  assume "w \<in> L G"
  hence 1: "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* w \<and> isWord w"
    using L_def by blast
  obtain w' where "w = map Tm w'"
    by (metis 1 ex_map_conv isWord_def sym.exhaust)
  hence "w' \<in> {w'. Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* map Tm w'}"
    using 1 by blast
  hence "w \<in> (map Tm) ` {w'. Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* map Tm w'}"
    using \<open>w = map Tm w'\<close> by blast
  thus "w \<in> (map Tm) ` Lang (Prods G) (Start G)"
    by (simp add: Lang_def)
qed

lemma L_eq_Lang: "L G = (map Tm) ` Lang (Prods G) (Start G)"
  using L_eq_Lang1 L_eq_Lang2 by blast

lemma L_Lang: "L G = L G' \<longleftrightarrow> Lang (Prods G) (Start G) = Lang (Prods G') (Start G')"
  using L_eq_Lang by (metis (mono_tags, lifting) Collect_cong L_def Lang_def image_eqI mem_Collect_eq)

theorem nepr_eq_if_noe:
  assumes "nepr P P'"
    and "[] \<notin> lang P S"
  shows "lang P S = lang P' S"
proof 
  show "lang P S \<subseteq> lang P' S"
  proof 
    fix x
    assume "x \<in> lang P S"
    have "\<forall>x. set P \<turnstile> [Nt S] \<Rightarrow>* x \<longrightarrow> x \<noteq> []" (is "?x")
      using assms Lang_def by fastforce
    hence 1: "no_rhs P (map Tm x) (map Tm x)" 
      unfolding no_rhs_def using nepr_r5 by auto
    hence "set P' \<turnstile> [Nt S] \<Rightarrow>* (map Tm x)"
      using 1 assms \<open>x \<in> lang P S\<close> by (smt (verit, best) Lang_def \<open>?x\<close> mem_Collect_eq nepr_r15)
    thus "x \<in> lang P' S"
      using Lang_def \<open>x \<in> lang P S\<close> by fast 
  qed
next
  show "lang P' S \<subseteq> lang P S"
  proof
    fix x'
    assume "x' \<in> lang P' S"
    show "x' \<in> lang P S" 
      using assms by (metis Lang_def \<open>x' \<in> lang P' S\<close> mem_Collect_eq nepr_r3)
  qed
qed

(* correctness *)
lemma noe_Prods_nepr:
  assumes "nepr P P'"
  shows "\<nexists>p. p \<in> set P' \<and> snd p = []"
  using assms unfolding nepr_def munge_def by simp

lemma noe_lang_nepr:
  assumes "nepr P P'"
  shows "[] \<notin> lang P' S"
proof (rule ccontr)
  assume "\<not>([] \<notin> lang P' S)"
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* map Tm []"
    using Lang_def by fast
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* []"
    by simp
  hence "\<exists>A. set P' \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, []) \<in> set P'"
    by (smt (verit, best) append.left_neutral append_is_Nil_conv append_self_conv derive.cases list.distinct(1) rtranclp.cases)
  thus False 
    using assms unfolding nepr_def munge_def by blast 
qed

theorem nepr_lang_eq:
  assumes "nepr P P'"
  shows "lang P' S = lang P S - {[]}"
proof 
  show "lang P' S \<subseteq> lang P S - {[]}"
  proof 
    fix w
    assume "w \<in> lang P' S"
    hence "w \<in> lang P' S - {[]}"
      using assms noe_lang_nepr by fastforce
    thus "w \<in> lang P S - {[]}"
      using assms by (simp add: Lang_def nepr_r3)
  qed
next
  show "lang P S - {[]} \<subseteq> lang P' S"
  proof 
    fix w
    assume "w \<in> lang P S - {[]}"
    hence 1: "(map Tm w) \<noteq> []" 
      by simp
    have 2: "set P \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using \<open>w \<in> lang P S - {[]}\<close> Lang_def by fast
    have "no_rhs P (map Tm w) (map Tm w)"
      using \<open>w \<in> lang P S - {[]}\<close> nepr_r5 no_rhs_def by blast
    hence "set P' \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using 1 2 nepr_r15[of P \<open>[Nt S]\<close> \<open>map Tm w\<close> P' \<open>Nt S\<close> \<open>map Tm w\<close>] assms by simp
    thus "w \<in> lang P' S"
      by (simp add: Lang_def)
  qed
qed

end