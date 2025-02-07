theory eProds
  imports "../CFG"
begin

inductive nullable :: "('n,'t) prods \<Rightarrow> ('n,'t) sym \<Rightarrow> bool"
for P where
  NullableSym:
  "\<lbrakk> (A, w) \<in> set P; \<forall>s \<in> set w. nullable P s\<rbrakk>
  \<Longrightarrow> nullable P (Nt A)"

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
  from \<open>set P \<turnstile> v \<Rightarrow> w\<close> obtain A \<alpha> l r where "v = l @ [Nt A] @ r \<and> w = l @ \<alpha> @ r \<and> (A, \<alpha>) \<in> set P" (is "?A\<alpha>")
    by (auto simp: derive.simps)
  from this \<open>nullables P w\<close> have "nullables P \<alpha> \<and> nullables P l \<and> nullables P r"
    by simp
  hence "nullables P [Nt A]"
    using \<open>?A\<alpha>\<close> nullable.simps by auto
  from this \<open>nullables P \<alpha> \<and> nullables P l \<and> nullables P r\<close> have "nullables P v"
    using \<open>?A\<alpha>\<close> by auto
  thus ?case
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by blast
qed

lemma nullable_if: "set P \<turnstile> [a] \<Rightarrow>* [] \<Longrightarrow> nullable P a"
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

lemma if_nullable: "nullable P a \<Longrightarrow> set P \<turnstile> [a] \<Rightarrow>* []"
proof (induction rule: nullable.induct)
  case (NullableSym x gamma)
    hence "set P \<turnstile> [Nt x] \<Rightarrow>* gamma" 
      using derive_singleton by blast
    also have "set P \<turnstile> gamma \<Rightarrow>* []" 
      using NullableSym nullable_aux by blast
  finally show ?case .
qed

corollary nullable_iff: "nullable P a \<longleftrightarrow> set P \<turnstile> [a] \<Rightarrow>* []"
  by (auto simp: nullable_if if_nullable)

fun eps_closure :: "('n, 't) prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms list" where
  "eps_closure P [] = [[]]" |
  "eps_closure P (s#sl) = (
    if nullable P s then (map ((#) s) (eps_closure P sl)) @ eps_closure P sl 
    else map ((#) s) (eps_closure P sl))"

definition eps_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
"eps_elim P \<equiv> {(l,r'). \<exists>r. (l,r) \<in> set P \<and> r' \<in> set (eps_closure P r) \<and> (r' \<noteq> [])}"

definition \<N> :: "('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> bool" where 
  "\<N> P P' \<equiv> set P' = eps_elim P"

(* auxiliary function to prove finiteness *)
definition eps_elim_fun :: "('n, 't) prods \<Rightarrow> ('n, 't) prod \<Rightarrow> ('n, 't) Prods" where 
  "eps_elim_fun P p = {(l',r'). l' = fst p \<and> r' \<in> set (eps_closure P (snd p)) \<and> (r' \<noteq> [])}"

lemma eps_elim_fun_eq: "eps_elim P = \<Union>((eps_elim_fun P) ` set P)"
proof 
  show "eps_elim P \<subseteq> (\<Union> (eps_elim_fun P ` set P))" 
   unfolding eps_elim_def eps_elim_fun_def by auto
next
  show "\<Union>((eps_elim_fun P) ` set P) \<subseteq> eps_elim P"
  proof
    fix x
    assume "x \<in> \<Union>((eps_elim_fun P) ` set P)"
    obtain l r' where "x = (l,r')" by fastforce
    hence "(l,r') \<in> \<Union>((eps_elim_fun P) ` set P)" 
      using \<open>x \<in> \<Union>((eps_elim_fun P) ` set P)\<close> by simp
    hence 1: "\<exists>r. r' \<in> set (eps_closure P r) \<and> (r' \<noteq> []) \<and> (l,r) \<in> set P" 
      using eps_elim_fun_def by fastforce
    from this  obtain r where "r' \<in> set (eps_closure P r) \<and> (l,r) \<in> set P" 
      by blast
    thus "x \<in> eps_elim P" unfolding eps_elim_fun_def eps_elim_def
      using 1 \<open>x = (l, r')\<close> by blast 
  qed
qed

lemma finite_eps_elim: "finite (eps_elim P)" 
proof -
  have "\<forall>p \<in> set P. finite (eps_elim_fun P p)"
    unfolding eps_elim_fun_def by auto
  hence "finite (\<Union>((eps_elim_fun P) ` set P))"
    using finite_UN by simp
  thus ?thesis using eps_elim_fun_eq by metis
qed

lemma \<N>_exists: "\<forall>P. \<exists>P'. \<N> P P'"
  unfolding \<N>_def by (simp add: finite_list finite_eps_elim)

lemma eps_closure_nullable:  "[] \<in> set (eps_closure P r) \<Longrightarrow> nullables P r"
proof (induction r)
  case Nil
  then show ?case by simp
next
  case (Cons a r)
  hence "nullable P a"
    using image_iff[of \<open>[]\<close> \<open>eps_closure P\<close> \<open>{a#r}\<close>] by auto
  then show ?case 
    using Cons Un_iff by auto
qed

lemma \<N>_r1: "r' \<in> set (eps_closure P r) \<Longrightarrow> set P \<turnstile> r \<Rightarrow>* r'"
proof (induction r arbitrary: r')
  case (Cons a r)
  then show ?case 
  proof (cases "nullable P a")
    case True
    obtain e where "e \<in> set (eps_closure P r) \<and> (r' = (a#e) \<or> r' = e)" (is "?e")
      using Cons.prems True by auto
    hence 1: "set P \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by blast
    hence 2: "set P \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using \<open>?e\<close> derives_prepend by blast
    have "set P \<turnstile> [a] \<Rightarrow>* []" 
      using True if_nullable by blast
    hence "set P \<turnstile> [a]@r \<Rightarrow>* r" 
      using derives_append by fastforce
    thus ?thesis 
      using 1 2 \<open>?e\<close> by force 
  next
    case False
    obtain e where "e \<in> set (eps_closure P r) \<and> (r' = (a#e))" (is "?e")
      using Cons.prems False by auto
    hence "set P \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by simp
    hence "set P \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using derives_prepend by blast
    thus ?thesis
      using \<open>?e\<close> by simp
  qed
qed simp

lemma \<N>_r2: 
  assumes "set P' \<turnstile> u \<Rightarrow> v"
    and "\<N> P P'" 
  shows "set P \<turnstile> u \<Rightarrow>* v"
  using assms 
proof -
  obtain A \<alpha> r1 r2 where "(A, \<alpha>) \<in> set P' \<and> u = r1 @ [Nt A] @ r2 \<and> v = r1 @ \<alpha> @ r2" (is "?A")
    using assms derive.cases by meson
  hence 1: "(A, \<alpha>) \<in> {(l,r'). \<exists>r. (l,r) \<in> set P \<and> r' \<in> set (eps_closure P r) \<and> (r' \<noteq> [])}"
    using assms(2) unfolding \<N>_def eps_elim_def by simp
  obtain r where "(A, r) \<in> set P \<and> \<alpha> \<in> set (eps_closure P r)" (is "?r")
    using 1 by blast
  hence "set P \<turnstile> r \<Rightarrow>* \<alpha>" 
    using \<N>_r1 by blast
  hence 2: "set P \<turnstile> r1 @ r @ r2 \<Rightarrow>* r1 @ \<alpha> @ r2"
    using \<open>?r\<close> derives_prepend derives_append by blast
  hence "set P \<turnstile> r1 @ [Nt A] @ r2 \<Rightarrow> r1 @ r @ r2" 
    using \<open>?r\<close> derive.simps by fast
  thus ?thesis 
    using 2 by (simp add: \<open>?A\<close>)
qed

lemma \<N>_r3:
  assumes "set P' \<turnstile> u \<Rightarrow>* v"
    and "\<N> P P'" 
  shows "set P \<turnstile> u \<Rightarrow>* v"
  using assms by (induction v rule: rtranclp_induct) (auto simp: \<N>_r2 rtranclp_trans)

lemma \<N>_r4:
  assumes "(l,r) \<in> set P"
    and "\<N> P P'"
    and "r' \<in> set (eps_closure P r) \<and> (r' \<noteq> [])"
  shows "(l,r') \<in> set P'"
  using assms unfolding \<N>_def eps_elim_def by blast

lemma \<N>_r5: "r \<in> set (eps_closure P r)" 
  by (induction r) auto

lemma \<N>_r6: 
  assumes "(l,r) \<in> set P"
    and "r' \<noteq> []"
    and "r' \<in> set (eps_closure P r)"
    and "\<N> P P'"
  shows "(l,r') \<in> set P'"
  using assms \<N>_r4 by fast

lemma \<N>_r7: 
  assumes "\<N> P P'"
    and "set P \<turnstile> [Nt A] \<Rightarrow> v"
    and "v' \<in> set (eps_closure P v) \<and> (v' \<noteq> [])"
  shows "set P' \<turnstile> [Nt A] \<Rightarrow> v'"
proof -
  have "(A,v) \<in> set P" 
    using assms(2) by (simp add: derive_singleton)
  hence "(A,v') \<in> set P'" 
    using assms \<N>_r6 conjE by fastforce
  thus ?thesis 
    using derive_singleton by fast
qed

lemma \<N>_r12a: 
  assumes "r1' \<in> set (eps_closure P r1)"
    and "r2' \<in> set (eps_closure P r2)"
  shows "(r1'@r2') \<in> set (eps_closure P (r1@r2))"
  using assms by (induction r1 arbitrary: r1' r2 r2' rule: eps_closure.induct) auto

lemma \<N>_r12b:
  assumes "r1' \<in> set (eps_closure P r1)"
    and "r2' \<in> set (eps_closure P r2)"
    and "r3' \<in> set (eps_closure P r3)"
  shows "(r1'@r2'@r3') \<in> set (eps_closure P (r1@r2@r3))"
  using assms 
  by (induction r1 arbitrary: r1' r2 r2' r3 r3' rule: eps_closure.induct) (auto simp: \<N>_r12a)

lemma \<N>_r14:
  assumes "r' \<in> set (eps_closure P (r1@r2))"
  shows "\<exists>r1' r2'. (r'=r1'@r2') \<and> r1' \<in> set (eps_closure P r1) \<and> r2' \<in> set (eps_closure P r2)"
  using assms
  apply (induction r1 arbitrary: r2 r' rule: eps_closure.induct) 
   apply auto
  by (metis append_Cons imageI)+    

lemma \<N>_r15:
  assumes "set P \<turnstile> [S] \<Rightarrow>* rf"
    and "\<N> P P'"
    and "rf' \<in> set (eps_closure P rf) \<and> (rf' \<noteq> [])"
  shows "set P' \<turnstile> [S] \<Rightarrow>* rf'"
  using assms
proof (induction arbitrary: rf')
  case base
  then show ?case 
    by (cases "nullable P S") auto
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
      using False step by (auto simp: derive.simps)
    from this obtain r1' rhs' r2' where 
      "(rf' = (r1'@rhs'@r2')) \<and> r1' \<in> set (eps_closure P r1) \<and> rhs' \<in> set (eps_closure P rhs) \<and> r2' \<in> set (eps_closure P r2)" (is "?rf'")
      using step \<N>_r14 by metis
    then show ?thesis 
    proof (cases "rhs' = []")
      case True
        hence "rf' = r1'@r2'" 
          using \<open>?rf'\<close> by simp 
        have "[] \<in> set (eps_closure P rhs)"
          using True \<open>?rf'\<close> by simp
        hence "nullables P rhs"
          using eps_closure_nullable by blast
        hence "[] \<in> set (eps_closure P [Nt lhs])" 
          using \<open>?bc\<close> NullableSym by fastforce
        hence "(r1'@r2') \<in> set (eps_closure P (r1@[Nt lhs]@r2))"
          using \<N>_r12b[of r1' P r1 \<open>[]\<close> \<open>[Nt lhs]\<close> r2' r2] \<open>?rf'\<close> by simp
        then show ?thesis 
          using \<open>?bc\<close> \<open>rf' = r1' @ r2'\<close> step by blast
    next
      case False
        have "(r1'@[Nt lhs]@r2') \<in> set (eps_closure P (r1@[Nt lhs]@r2)) "
          using \<N>_r12b[of r1' P r1 \<open>[Nt lhs]\<close> \<open>[Nt lhs]\<close> r2' r2] \<N>_r5[of \<open>[Nt lhs]\<close> P] \<open>?rf'\<close> by blast
        hence 1: "set P' \<turnstile> [S] \<Rightarrow>* (r1'@[Nt lhs]@r2')" 
          using \<open>?bc\<close> step by blast
        have "set P \<turnstile> [Nt lhs] \<Rightarrow> rhs" 
          using \<open>?bc\<close> step(2) derive_singleton by blast
        hence "set P' \<turnstile> [Nt lhs] \<Rightarrow> rhs'"
          using \<N>_r7[of P P' lhs rhs rhs'] False step \<open>?rf'\<close> by blast
        hence "set P' \<turnstile> (r1'@[Nt lhs]@r2') \<Rightarrow> (r1'@rhs'@r2')" 
          using derive_append derive_prepend by blast
        thus ?thesis using 1
        by (simp add: \<open>?rf'\<close> step.prems(2))
    qed
  qed
qed

theorem \<N>_eq_if_noe:
  assumes "\<N> P P'"
    and "[] \<notin> lang P S"
  shows "lang P S = lang P' S"
proof 
  show "lang P S \<subseteq> lang P' S"
  proof 
    fix x
    assume "x \<in> lang P S"
    have "\<forall>x. set P \<turnstile> [Nt S] \<Rightarrow>* x \<longrightarrow> x \<noteq> []" (is "?x")
      using assms Lang_def by fastforce
    hence "(map Tm x) \<in> set (eps_closure P (map Tm x))" 
      using \<N>_r5 by auto
    hence "set P' \<turnstile> [Nt S] \<Rightarrow>* (map Tm x)"
      using assms \<open>x \<in> lang P S\<close> Lang_def \<N>_r15[of P \<open>Nt S\<close> \<open>map Tm x\<close>] by fast
    thus "x \<in> lang P' S"
      using Lang_def \<open>x \<in> lang P S\<close> by fast 
  qed
next
  show "lang P' S \<subseteq> lang P S"
  proof
    fix x'
    assume "x' \<in> lang P' S"
    show "x' \<in> lang P S" 
      using assms Lang_def \<open>x' \<in> lang P' S\<close> \<N>_r3[of P' \<open>[Nt S]\<close> \<open>map Tm x'\<close> P] by fast
  qed
qed

(* correctness *)
lemma noe_lang_\<N>_aux: 
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* w" "w = []"  
  shows "\<exists>A. P \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, w) \<in> P"
  using assms by (induction w rule: rtranclp_induct) (auto simp: derive.simps)

lemma noe_lang_\<N>:
  assumes "\<N> P P'"
  shows "[] \<notin> lang P' S"
proof (rule ccontr)
  assume "\<not>([] \<notin> lang P' S)"
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* map Tm []"
    using Lang_def by fast
  hence "set P' \<turnstile> [Nt S] \<Rightarrow>* []"
    by simp
  hence "\<exists>A. set P' \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, []) \<in> set P'"
    using noe_lang_\<N>_aux[of \<open>set P'\<close>] by blast
  thus False 
    using assms unfolding \<N>_def eps_elim_def by blast 
qed

theorem \<N>_lang_eq: "\<N> P P' \<Longrightarrow> lang P' S = lang P S - {[]}"
proof 
  assume "\<N> P P'"
  show "lang P' S \<subseteq> lang P S - {[]}"
  proof 
    fix w
    assume "w \<in> lang P' S"
    hence "w \<in> lang P' S - {[]}"
      using noe_lang_\<N>[of P] \<open>\<N> P P'\<close> by simp
    thus "w \<in> lang P S - {[]}"
      using \<open>\<N> P P'\<close> by (auto simp: Lang_def \<N>_r3)
  qed
next
  assume "\<N> P P'"
  show "lang P S - {[]} \<subseteq> lang P' S"
  proof 
    fix w
    assume "w \<in> lang P S - {[]}"
    hence 1: "(map Tm w) \<noteq> []" 
      by simp
    have 2: "set P \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using \<open>w \<in> lang P S - {[]}\<close> Lang_def by fast
    have "(map Tm w) \<in> set (eps_closure P (map Tm w)) "
      using \<open>w \<in> lang P S - {[]}\<close> \<N>_r5 by blast
    hence "set P' \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using 1 2 \<N>_r15[of P] \<open>\<N> P P'\<close> by simp
    thus "w \<in> lang P' S"
      by (simp add: Lang_def)
  qed
qed

end