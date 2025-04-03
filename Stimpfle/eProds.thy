(*
Author: August Martin Stimpfle
Based on HOL4 theories by Aditi Barthwal
*)

theory eProds
  imports "../CFG"
begin

inductive nullable :: "('n,'t) prods \<Rightarrow> ('n,'t) sym \<Rightarrow> bool"
for ps where
  NullableSym:
  "\<lbrakk> (A, w) \<in> set ps; \<forall>s \<in> set w. nullable ps s\<rbrakk>
  \<Longrightarrow> nullable ps (Nt A)"

abbreviation "nullables ps w \<equiv> (\<forall>s \<in> set w. nullable ps s)"

lemma nullables_if: 
  assumes "set ps \<turnstile> u \<Rightarrow>* v" 
    and "u=[a]" "nullables ps v"
  shows "nullables ps u"
  using assms
proof(induction arbitrary: a rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl u v w)
  from \<open>set ps \<turnstile> v \<Rightarrow> w\<close> obtain A \<alpha> l r where A\<alpha>: "v = l @ [Nt A] @ r \<and> w = l @ \<alpha> @ r \<and> (A, \<alpha>) \<in> set ps"
    by (auto simp: derive.simps)
  from this \<open>nullables ps w\<close> have "nullables ps \<alpha> \<and> nullables ps l \<and> nullables ps r"
    by simp
  hence "nullables ps [Nt A]"
    using A\<alpha> nullable.simps by auto
  from this \<open>nullables ps \<alpha> \<and> nullables ps l \<and> nullables ps r\<close> have "nullables ps v"
    using A\<alpha> by auto
  thus ?case
    using rtrancl_into_rtrancl.IH rtrancl_into_rtrancl.prems(1) by blast
qed

lemma nullable_if: "set ps \<turnstile> [a] \<Rightarrow>* [] \<Longrightarrow> nullable ps a"
  using nullables_if[of ps "[a]" "[]" a] by simp

lemma nullable_aux: "\<forall>s\<in>set gamma. nullable ps s \<and> set ps \<turnstile> [s] \<Rightarrow>* [] \<Longrightarrow> set ps \<turnstile> gamma \<Rightarrow>* []"
proof (induction gamma)
  case (Cons a list)
  hence "set ps \<turnstile> list \<Rightarrow>* []"
    by simp
  moreover have "set ps \<turnstile> [a] \<Rightarrow>* []"
    using Cons by simp
  ultimately show ?case 
    using derives_Cons[of \<open>set ps\<close> list \<open>[]\<close> \<open>a\<close>] by simp
qed simp

lemma if_nullable: "nullable ps a \<Longrightarrow> set ps \<turnstile> [a] \<Rightarrow>* []"
proof (induction rule: nullable.induct)
  case (NullableSym x gamma)
    hence "set ps \<turnstile> [Nt x] \<Rightarrow>* gamma" 
      using derive_singleton by blast
    also have "set ps \<turnstile> gamma \<Rightarrow>* []" 
      using NullableSym nullable_aux by blast
  finally show ?case .
qed

corollary nullable_iff: "nullable ps a \<longleftrightarrow> set ps \<turnstile> [a] \<Rightarrow>* []"
  by (auto simp: nullable_if if_nullable)

fun eps_closure :: "('n, 't) prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms list" where
  "eps_closure ps [] = [[]]" |
  "eps_closure ps (s#sl) = (
    if nullable ps s then (map ((#) s) (eps_closure ps sl)) @ eps_closure ps sl 
    else map ((#) s) (eps_closure ps sl))"

definition eps_elim :: "('n, 't) prods \<Rightarrow> ('n, 't) Prods" where
"eps_elim ps \<equiv> {(l,r'). \<exists>r. (l,r) \<in> set ps \<and> r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> [])}"

definition \<N> :: "('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> bool" where 
  "\<N> ps ps'\<equiv> set ps'= eps_elim ps"

(* auxiliary function to prove finiteness *)
definition eps_elim_fun :: "('n, 't) prods \<Rightarrow> ('n, 't) prod \<Rightarrow> ('n, 't) Prods" where 
  "eps_elim_fun ps p = {(l',r'). l' = fst p \<and> r' \<in> set (eps_closure ps (snd p)) \<and> (r' \<noteq> [])}"

lemma eps_elim_fun_eq: "eps_elim ps = \<Union>((eps_elim_fun ps) ` set ps)"
proof 
  show "eps_elim ps \<subseteq> (\<Union> (eps_elim_fun ps ` set ps))" 
   unfolding eps_elim_def eps_elim_fun_def by auto
next
  show "\<Union>((eps_elim_fun ps) ` set ps) \<subseteq> eps_elim ps"
  proof
    fix x
    assume "x \<in> \<Union>((eps_elim_fun ps) ` set ps)"
    obtain l r' where "x = (l,r')" by fastforce
    hence "(l,r') \<in> \<Union>((eps_elim_fun ps) ` set ps)" 
      using \<open>x \<in> \<Union>((eps_elim_fun ps) ` set ps)\<close> by simp
    hence 1: "\<exists>r. r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> []) \<and> (l,r) \<in> set ps" 
      using eps_elim_fun_def by fastforce
    from this  obtain r where "r' \<in> set (eps_closure ps r) \<and> (l,r) \<in> set ps" 
      by blast
    thus "x \<in> eps_elim ps" unfolding eps_elim_fun_def eps_elim_def
      using 1 \<open>x = (l, r')\<close> by blast 
  qed
qed

lemma finite_eps_elim: "finite (eps_elim ps)" 
proof -
  have "\<forall>p \<in> set ps. finite (eps_elim_fun ps p)"
    unfolding eps_elim_fun_def by auto
  hence "finite (\<Union>((eps_elim_fun ps) ` set ps))"
    using finite_UN by simp
  thus ?thesis using eps_elim_fun_eq by metis
qed

lemma \<N>_exists: "\<forall>ps. \<exists>ps'. \<N> ps ps'"
  unfolding \<N>_def by (simp add: finite_list finite_eps_elim)

lemma eps_closure_nullable:  "[] \<in> set (eps_closure ps w) \<Longrightarrow> nullables ps w"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a r)
  hence "nullable ps a"
    using image_iff[of \<open>[]\<close> \<open>eps_closure ps\<close> \<open>{a#r}\<close>] by auto
  then show ?case 
    using Cons Un_iff by auto
qed

lemma \<N>_1: "r' \<in> set (eps_closure ps r) \<Longrightarrow> set ps \<turnstile> r \<Rightarrow>* r'"
proof (induction r arbitrary: r')
  case (Cons a r)
  then show ?case 
  proof (cases "nullable ps a")
    case True
    obtain e where e: "e \<in> set (eps_closure ps r) \<and> (r' = (a#e) \<or> r' = e)"
      using Cons.prems True by auto
    hence 1: "set ps \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by blast
    hence 2: "set ps \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using e derives_prepend by blast
    have "set ps \<turnstile> [a] \<Rightarrow>* []" 
      using True if_nullable by blast
    hence "set ps \<turnstile> [a]@r \<Rightarrow>* r" 
      using derives_append by fastforce
    thus ?thesis 
      using 1 2 e by force 
  next
    case False
    obtain e where e: "e \<in> set (eps_closure ps r) \<and> (r' = (a#e))"
      using Cons.prems False by auto
    hence "set ps \<turnstile> r \<Rightarrow>* e" 
      using Cons.IH by simp
    hence "set ps \<turnstile> [a]@r \<Rightarrow>* [a]@e" 
      using derives_prepend by blast
    thus ?thesis
      using e by simp
  qed
qed simp

lemma \<N>_r2: 
  assumes "set ps' \<turnstile> u \<Rightarrow> v" and "\<N> ps ps'" 
  shows "set ps \<turnstile> u \<Rightarrow>* v"
  using assms 
proof -
  obtain A \<alpha> x y where A: "(A, \<alpha>) \<in> set ps'\<and> u = x @ [Nt A] @ y \<and> v = x @ \<alpha> @ y"
    using assms derive.cases by meson
  hence 1: "(A, \<alpha>) \<in> {(l,r'). \<exists>r. (l,r) \<in> set ps \<and> r' \<in> set (eps_closure ps r) \<and> (r' \<noteq> [])}"
    using assms(2) unfolding \<N>_def eps_elim_def by simp
  obtain r where r: "(A, r) \<in> set ps \<and> \<alpha> \<in> set (eps_closure ps r)"
    using 1 by blast
  hence "set ps \<turnstile> r \<Rightarrow>* \<alpha>" 
    using \<N>_1 by blast
  hence 2: "set ps \<turnstile> x @ r @ y \<Rightarrow>* x @ \<alpha> @ y"
    using r derives_prepend derives_append by blast
  hence "set ps \<turnstile> x @ [Nt A] @ y \<Rightarrow> x @ r @ y" 
    using r derive.simps by fast
  thus ?thesis 
    using 2 by (simp add: A)
qed

lemma \<N>_r3:
  assumes "set ps' \<turnstile> u \<Rightarrow>* v" and "\<N> ps ps'" 
  shows "set ps \<turnstile> u \<Rightarrow>* v"
    using assms by (induction v rule: rtranclp_induct) (auto simp: \<N>_r2 rtranclp_trans)

lemma \<N>_r5: "r \<in> set (eps_closure ps r)" 
  by (induction r) auto

lemma \<N>_r4:
  assumes "(l,r) \<in> set ps"
    and "\<N> ps ps'"
    and "(r' \<noteq> [])" 
    and "r' \<in> set (eps_closure ps r)"
  shows "(l,r') \<in> set ps'"
  using assms unfolding \<N>_def eps_elim_def by blast

lemma \<N>_r7: 
  assumes "\<N> ps ps'"
    and "set ps \<turnstile> [Nt A] \<Rightarrow> v"
    and "v' \<in> set (eps_closure ps v) \<and> (v' \<noteq> [])"
  shows "set ps' \<turnstile> [Nt A] \<Rightarrow> v'"
proof -
  have "(A,v) \<in> set ps" 
    using assms(2) by (simp add: derive_singleton)
  hence "(A,v') \<in> set ps'" 
    using assms \<N>_r4 conjE by fastforce
  thus ?thesis 
    using derive_singleton by fast
qed

lemma \<N>_r12a: 
  assumes "x' \<in> set (eps_closure ps x)"
    and "y' \<in> set (eps_closure ps y)"
  shows "(x'@y') \<in> set (eps_closure ps (x@y))"
  using assms by (induction x arbitrary: x' y y' rule: eps_closure.induct) auto

lemma \<N>_r12b:
  assumes "x' \<in> set (eps_closure ps x)"
    and "y' \<in> set (eps_closure ps y)"
    and "z' \<in> set (eps_closure ps z)"
  shows "(x'@y'@z') \<in> set (eps_closure ps (x@y@z))"
  using assms 
  by (induction x arbitrary: x' y y' z z' rule: eps_closure.induct) (auto simp: \<N>_r12a)

lemma \<N>_r14:
  assumes "r' \<in> set (eps_closure ps (x@y))"
  shows "\<exists>x' y'. (r'=x'@y') \<and> x' \<in> set (eps_closure ps x) \<and> y' \<in> set (eps_closure ps y)"
  using assms
  apply (induction x arbitrary: y r' rule: eps_closure.induct) 
   apply auto
  by (metis append_Cons imageI)+ 

lemma \<N>_r15:
  assumes "set ps \<turnstile> [Nt S] \<Rightarrow>* u"
    and "\<N> ps ps'"
    and "v \<in> set (eps_closure ps u) \<and> (v \<noteq> [])"
  shows "set ps' \<turnstile> [Nt S] \<Rightarrow>* v"
  using assms
proof (induction u arbitrary: v rule: derives_induct)
  case base
  then show ?case
    by (cases "nullable ps (Nt S)") auto
next
  case (step x A y w)
  then obtain x' w' y' where 
    v: "(v = (x'@w'@y')) \<and> x' \<in> set (eps_closure ps x) \<and> w' \<in> set (eps_closure ps w) \<and> y' \<in> set (eps_closure ps y)"
    using step \<N>_r14 by metis
  then show ?case
  proof (cases "w' = []")
    case True
      hence "v = x'@y'" 
        using v by simp 
      have "[] \<in> set (eps_closure ps w)"
        using True v by simp
      hence "nullables ps w"
        using eps_closure_nullable by blast
      hence "[] \<in> set (eps_closure ps [Nt A])" 
        using step(2) NullableSym by fastforce
      hence "(x'@y') \<in> set (eps_closure ps (x@[Nt A]@y))"
        using \<N>_r12b[of x' ps x \<open>[]\<close> \<open>[Nt A]\<close> y' y] v by simp
      then show ?thesis 
        using \<open>v = x' @ y'\<close> step by blast
  next
    case False
      have "(x'@[Nt A]@y') \<in> set (eps_closure ps (x@[Nt A]@y)) "
        using \<N>_r12b[of x' ps x \<open>[Nt A]\<close> \<open>[Nt A]\<close> y' y] \<N>_r5[of \<open>[Nt A]\<close> ps] v by blast
      hence 1: "set ps' \<turnstile> [Nt S] \<Rightarrow>* (x'@[Nt A]@y')" 
        using step by blast
      have "set ps \<turnstile> [Nt A] \<Rightarrow> w" 
        using step(2) derive_singleton by blast
      hence "set ps' \<turnstile> [Nt A] \<Rightarrow> w'"
        using \<N>_r7[of ps ps' A w w'] False step v by blast
      hence "set ps' \<turnstile> (x'@[Nt A]@y') \<Rightarrow> (x'@w'@y')" 
        using derive_append derive_prepend by blast
      thus ?thesis using 1
      by (simp add: v step.prems(2))
  qed
qed

theorem \<N>_eq_if_noe:
  assumes "\<N> ps ps'"
    and "[] \<notin> lang ps S"
  shows "lang ps S = lang ps' S"
proof 
  show "lang ps S \<subseteq> lang ps' S"
  proof 
    fix x
    assume "x \<in> lang ps S"
    have "\<forall>x. set ps \<turnstile> [Nt S] \<Rightarrow>* x \<longrightarrow> x \<noteq> []"
      using assms Lang_def by fastforce
    hence "(map Tm x) \<in> set (eps_closure ps (map Tm x))" 
      using \<N>_r5 by auto
    hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* (map Tm x)"
      using assms \<open>x \<in> lang ps S\<close> Lang_def \<N>_r15[of ps S \<open>map Tm x\<close>] by fast
    thus "x \<in> lang ps' S"
      using Lang_def \<open>x \<in> lang ps S\<close> by fast 
  qed
next
  show "lang ps' S \<subseteq> lang ps S"
  proof
    fix x'
    assume "x' \<in> lang ps' S"
    show "x' \<in> lang ps S" 
      using assms Lang_def \<open>x' \<in> lang ps' S\<close> \<N>_r3[of ps' \<open>[Nt S]\<close> \<open>map Tm x'\<close> ps] by fast
  qed
qed

(* correctness *)
lemma noe_lang_\<N>_aux: 
  assumes "ps \<turnstile> [Nt S] \<Rightarrow>* w" "w = []"  
  shows "\<exists>A. ps \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, w) \<in> ps"
  using assms by (induction w rule: rtranclp_induct) (auto simp: derive.simps)

lemma noe_lang_\<N>: "\<N> ps ps' \<Longrightarrow> [] \<notin> lang ps' S"
proof (rule ccontr)
  assume "\<N> ps ps'" "\<not>([] \<notin> lang ps' S)"
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* map Tm []"
    using Lang_def by fast
  hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* []"
    by simp
  hence "\<exists>A. set ps' \<turnstile> [Nt S] \<Rightarrow>* [Nt A] \<and> (A, []) \<in> set ps'"
    using noe_lang_\<N>_aux[of \<open>set ps'\<close>] by blast
  thus False 
    using \<open>\<N> ps ps'\<close> unfolding \<N>_def eps_elim_def by blast
qed

theorem \<N>_lang_eq: "\<N> ps ps'\<Longrightarrow> lang ps' S = lang ps S - {[]}"
proof 
  assume "\<N> ps ps'"
  show "lang ps' S \<subseteq> lang ps S - {[]}"
  proof 
    fix w
    assume "w \<in> lang ps' S"
    hence "w \<in> lang ps' S - {[]}"
      using noe_lang_\<N>[of ps] \<open>\<N> ps ps'\<close> by simp
    thus "w \<in> lang ps S - {[]}"
      using \<open>\<N> ps ps'\<close> by (auto simp: Lang_def \<N>_r3)
  qed
next
  assume "\<N> ps ps'"
  show "lang ps S - {[]} \<subseteq> lang ps' S"
  proof 
    fix w
    assume "w \<in> lang ps S - {[]}"
    hence 1: "(map Tm w) \<noteq> []" 
      by simp
    have 2: "set ps \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using \<open>w \<in> lang ps S - {[]}\<close> Lang_def by fast
    have "(map Tm w) \<in> set (eps_closure ps (map Tm w)) "
      using \<open>w \<in> lang ps S - {[]}\<close> \<N>_r5 by blast
    hence "set ps' \<turnstile> [Nt S] \<Rightarrow>* (map Tm w)"
      using 1 2 \<N>_r15[of ps] \<open>\<N> ps ps'\<close> by simp
    thus "w \<in> lang ps' S"
      by (simp add: Lang_def)
  qed
qed

end