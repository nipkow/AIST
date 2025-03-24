theory PumpingLemma
  imports "../CFG" CNF
begin

(* earliest version is due to Thomas Ammer *)
abbreviation repl :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<^sup>*/_")
  where "xs\<^sup>*n \<equiv> concat (replicate n xs)"

lemma repl_append: "(x\<^sup>*(Suc i)) = (x\<^sup>*i) @ x"
  by (induction i) simp_all

(* paths for Prods in CNF form *)
(* prods \<Rightarrow> Start Nt \<Rightarrow> path \<Rightarrow> word  (path = Nt list, word = Tm list) *)
inductive path :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool" 
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>'\<langle>_'\<rangle>/ _))" [50, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> Ps \<Longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>[A]\<rangle> [a]" |
left:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> Ps \<and> (Ps \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<and> (Ps \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v)\<rbrakk> \<Longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#p\<rangle> (w@v)" |
right:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> Ps \<and> (Ps \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<and> (Ps \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v)\<rbrakk> \<Longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#q\<rangle> (w@v)"

(* rules for derivations of words if the grammar is in cnf, resembles binary syntax trees *)
inductive cnf_derives :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_/ \<Rightarrow>cnf/ _))" [50, 0, 50] 50) where
step:  "(A, [Tm a]) \<in> Ps \<Longrightarrow> Ps \<turnstile> A \<Rightarrow>cnf [a]"|
trans:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> Ps \<and> Ps \<turnstile> B \<Rightarrow>cnf w \<and> Ps \<turnstile> C \<Rightarrow>cnf v\<rbrakk> \<Longrightarrow> Ps \<turnstile> A \<Rightarrow>cnf (w@v)"

lemma path_if_cnf_derives: "Ps \<turnstile> S \<Rightarrow>cnf w \<Longrightarrow> \<exists>p. Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  by (induction rule: cnf_derives.induct) (auto intro: path.intros)

lemma cnf_derives_if_path: "Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> Ps \<turnstile> S \<Rightarrow>cnf w"
  by (induction rule: path.induct) (auto intro: cnf_derives.intros)

corollary cnf_path: "Ps \<turnstile> S \<Rightarrow>cnf w \<longleftrightarrow> (\<exists>p. Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w)"
  using path_if_cnf_derives[of Ps] cnf_derives_if_path[of Ps] by blast

lemma cnf_der: 
  assumes "Ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w" "CNF Ps" 
  shows "Ps \<turnstile> S \<Rightarrow>cnf w"
using assms proof (induction w arbitrary: S rule: length_induct)
  case (1 w)
  have "Eps_free Ps"
    using assms(2) CNF_eq by blast
  hence "\<not>(Ps \<turnstile> [Nt S] \<Rightarrow>* [])"
    by (simp add: Eps_free_derives_Nil)
  hence 2: "length w \<noteq> 0" 
    using 1 by auto
  thus ?case
  proof (cases "length w \<le> 1")
    case True
    hence "length w = 1"
      using 2 by linarith
    then obtain t where "w = [t]"
      using length_Suc_conv[of w 0] by auto 
    hence "(S, [Tm t]) \<in> Ps"
      using 1 assms(2) cnf_single_derive[of Ps S t] by simp
    thus ?thesis
      by (simp add: \<open>w = _\<close> cnf_derives.intros(1))
  next
    case False 
    obtain A B u v where ABuv: "(S, [Nt A, Nt B]) \<in> Ps \<and> Ps \<turnstile> [Nt A] \<Rightarrow>* map Tm u \<and> Ps \<turnstile> [Nt B] \<Rightarrow>* map Tm v \<and> u@v = w \<and> u \<noteq> [] \<and> v \<noteq> []"
      using False assms(2) 1 cnf_word[of Ps S w] by auto
    have "length u < length w \<and> length v < length w"
      using ABuv by auto
    hence "cnf_derives Ps A u \<and> cnf_derives Ps B v"
      using 1 ABuv by blast
    thus ?thesis
      using ABuv cnf_derives.intros(2)[of S A B Ps u v] by blast
  qed
qed

lemma der_cnf:
  assumes "Ps \<turnstile> S \<Rightarrow>cnf w" "CNF Ps"
  shows "Ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
using assms proof (induction rule: cnf_derives.induct)
  case (step A a Ps)
  then show ?case 
    by (simp add: derive_singleton r_into_rtranclp)
next
  case (trans A B C Ps w v)
  hence "Ps \<turnstile> [Nt A] \<Rightarrow> [Nt B, Nt C]"
    by (simp add: derive_singleton)
  moreover have "Ps \<turnstile> [Nt B] \<Rightarrow>* map Tm w \<and> Ps \<turnstile> [Nt C] \<Rightarrow>* map Tm v"
    using trans by blast
  ultimately show ?case 
    using derives_append_decomp[of Ps \<open>[Nt B]\<close> \<open>[Nt C]\<close> \<open>map Tm (w @ v)\<close>] by auto
qed

corollary cnf_der_eq: "CNF Ps \<Longrightarrow> (Ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w \<longleftrightarrow> Ps \<turnstile> S \<Rightarrow>cnf w)"
  using cnf_der[of Ps S w] der_cnf[of Ps S w] by blast

lemma path_if_derives: 
  assumes "Ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w" "CNF Ps" 
  shows "\<exists>p. Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  using assms cnf_der[of Ps S w] path_if_cnf_derives[of Ps S w] by blast

lemma derives_if_path:
  assumes "Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w" "CNF Ps"
  shows "Ps \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
  using assms der_cnf[of Ps S w] cnf_derives_if_path[of Ps S p w] by blast

(* longest path, similar to path, the difference is that lpath always chooses the longest path in a syntax tree *)
inductive lpath :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool" 
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>'\<llangle>_'\<rrangle>/ _))" [50, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> Ps \<Longrightarrow> Ps \<turnstile> A \<Rightarrow>\<llangle>[A]\<rrangle> [a]" |
nonTerminals:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> Ps \<and> (Ps \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> w) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>q\<rrangle> v)\<rbrakk> \<Longrightarrow> 
                Ps \<turnstile> A \<Rightarrow>\<llangle>A#(if length p \<ge> length q then p else q)\<rrangle> (w@v)" 

lemma path_lpath: "Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>p'. (Ps \<turnstile> S \<Rightarrow>\<llangle>p'\<rrangle> w) \<and> length p' \<ge> length p"
  by (induction rule: path.induct) (auto intro: lpath.intros)

lemma lpath_path: "(Ps \<turnstile> S \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  by (induction rule: lpath.induct) (auto intro: path.intros)

(*Property of the a binary tree: Since the tree is a binary tree, word lengths are always \<le> 2^(longest path-1).
However, this version is easier to use/proof and suffices *)
lemma lpath_length: "(Ps \<turnstile> S \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> length w \<le> 2^length p"
proof (induction rule: lpath.induct)
  case (terminal A a Ps)
  then show ?case by simp
next
  case (nonTerminals A B C Ps p w q v)
  then show ?case 
  proof (cases "length p \<ge> length q")
    case True
    hence "length v \<le> 2^length p"
      using nonTerminals order_subst1[of \<open>length v\<close> \<open>\<lambda>x. 2^x\<close> \<open>length q\<close> \<open>length p\<close>] by simp
    hence "length w +length v \<le> 2*2^length p"
      by (simp add: nonTerminals.IH(1) add_le_mono mult_2)
    then show ?thesis
      by (simp add: True)
  next
    case False
    hence "length w \<le> 2^length q"
      using nonTerminals order_subst1[of \<open>length w\<close> \<open>\<lambda>x. 2^x\<close> \<open>length p\<close> \<open>length q\<close>] by simp 
    hence "length w +length v \<le> 2*2^length q"
      by (simp add: nonTerminals.IH add_le_mono mult_2)
    then show ?thesis
      by (simp add: False)
  qed
qed

lemma step_decomp:
  assumes "Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p\<rangle> w" " length p \<ge> 1" 
  shows "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> Ps \<and> w =a@b \<and>
        (((Ps \<turnstile> B \<Rightarrow>\<langle>p\<rangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<langle>p'\<rangle> b)) \<or> ((Ps \<turnstile> B \<Rightarrow>\<langle>p'\<rangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<langle>p\<rangle> b)))"
  using assms by (cases) fastforce+

lemma steplp_decomp:
  assumes "Ps \<turnstile> A \<Rightarrow>\<llangle>[A]@p\<rrangle> w" " length p \<ge> 1" 
  shows "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> Ps \<and> w =a@b \<and>
      (((Ps \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length p \<ge> length p') \<or>
      ((Ps \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p\<rrangle> b) \<and> length p \<ge> length p'))"
  using assms by (cases) fastforce+

lemma path_first_step: "Ps \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>q. p = [A]@q "
  by (induction rule: path.induct) simp_all

lemma no_empty: "Ps \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> length w > 0"
  by (induction rule: path.induct) simp_all

lemma substitution: 
  assumes "Ps \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p2\<rangle> z"
  shows "\<exists>v w x. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> z = v@w@x \<and>
        (\<forall>w' p'. ((Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@w'@x)) \<and>
        (length p1 > 0 \<longrightarrow> length (v@x) > 0)"
using assms proof (induction p1 arbitrary: Ps A z)
  case Nil
  hence "\<forall>w' p'. ((Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> z) \<and> z = []@z@[] \<and>
        ((Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>[]@[X]@p'\<rangle> ([]@w'@[])) \<and>
        (length [] > 0 \<longrightarrow> length ([]@[]) > 0))"
    using path_first_step[of Ps A] by auto
  then show ?case 
    by blast
next
  case (Cons A p1 Ps Y)
  hence 0: "A = Y"
    using path_first_step[of Ps Y] by fastforce 
  have "length (p1@[X]@p2) \<ge> 1"
    by simp
  hence "\<exists>B C a b q. (A, [Nt B, Nt C]) \<in> Ps \<and> a@b = z \<and> 
        (((Ps \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> Ps \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b) \<or> ((Ps \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p2\<rangle> a) \<and> Ps \<turnstile> C \<Rightarrow>\<langle>q\<rangle> b))"
    using Cons.prems path_first_step step_decomp by fastforce
  then obtain B C a b q where BC: "(A, [Nt B, Nt C]) \<in> Ps \<and> a@b = z \<and> 
        (((Ps \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> Ps \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b) \<or> ((Ps \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p2\<rangle> a) \<and> Ps \<turnstile> C \<Rightarrow>\<langle>q\<rangle> b))"
    by blast
  then show ?case
  proof (cases "((Ps \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> Ps \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b)")
    case True
    then obtain v w x where vwx: "(Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> b = v@w@x \<and> 
          (\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@w'@x))"
      using Cons.IH by blast
    hence 1: "\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (a@v@w'@x)"
      using BC by (auto intro: path.intros(3))
    obtain v' where "v' = a@v"
      by simp
    hence "length (v'@x) > 0"
      using True no_empty by fast
    hence "(Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> z = v'@w@x \<and> (\<forall>w' p'.
          (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v'@w'@x)) \<and>
          (length (A#p1) > 0 \<longrightarrow> length (v'@x) >0)"
      using vwx 1 BC \<open>v' = _\<close> by simp
    thus ?thesis
      using 0 by auto
  next
    case False
    then obtain v w x where vwx: "(Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> a = v@w@x \<and> 
          (\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@w'@x))"
      using Cons.IH BC by blast
    hence 1: "\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@w'@x@b)"
      using BC left[of A B C Ps] by fastforce
    hence "(Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> z = v@w@x@b \<and> (\<forall>w' p'.
          (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@w'@x@b)) \<and>
          (length (A#p1) > 0 \<longrightarrow> length (a@v@x) >0)"
      using vwx BC no_empty by fastforce
    moreover have "length (v@x@b) > 0"
      using no_empty BC by fast
    ultimately show ?thesis
    using 0 by auto
  qed
qed

lemma substitution_lp: 
  assumes "Ps \<turnstile> A \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> z"
  shows "\<exists>v w x. ((Ps \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> z = v@w@x \<and>
        (\<forall>w' p'. ((Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@w'@x)))"
using assms proof (induction p1 arbitrary: Ps A z)
  case Nil
  hence "\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>[]@[X]@p'\<rangle> ([]@w'@[])"
    using path_first_step lpath_path by fastforce
  moreover have "(Ps \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> z) \<and> z = []@z@[]"
    using Nil lpath.cases[of Ps A \<open>[X] @ p2\<close> z] by auto
  ultimately show ?case 
    by blast
next
  case (Cons A p1 Ps Y)
  hence 0: "A = Y"
    using path_first_step[of Ps Y] lpath_path by fastforce 
  have "length (p1@[X]@p2) \<ge> 1"
    by simp
  hence "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> Ps \<and> z = a@b \<and> 
        (((Ps \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p') \<or> 
        ((Ps \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p'))"
    using steplp_decomp[of Ps A \<open>p1@[X]@p2\<close> z] 0 Cons by simp
  then obtain B C p' a b where BC: "(A, [Nt B, Nt C]) \<in> Ps \<and> z = a@b \<and> 
        (((Ps \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p') \<or> 
        ((Ps \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p'))"
    by blast
  then show ?case
  proof (cases "(Ps \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p'")
    case True
    then obtain v w x where vwx: "(Ps \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> a = v@w@x \<and> 
          (\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@w'@x))"
      using Cons.IH by blast
    hence "(Ps \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> z = v@w@x@b \<and>
       (\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@w'@x@b))"
      using BC lpath_path[of Ps] path.intros(2)[of A B C Ps] by fastforce
    then show ?thesis
      using 0 by auto
  next
    case False
    hence "((Ps \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (Ps \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p')"
      using BC by blast
    then obtain v w x where vwx: "(Ps \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> b = v@w@x \<and> 
          (\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@w'@x))"
      using Cons.IH by blast
    then obtain v' where "v' = a@v"
      by simp
    hence "(Ps \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> z = v'@w@x \<and>
       (\<forall>w' p'. (Ps \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v'@w'@x))"
      using BC lpath_path[of Ps] path.intros(3)[of A B C Ps] vwx by fastforce
    then show ?thesis
      using 0 by auto
  qed
qed

lemma path_nts: "Ps \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> set p \<subseteq> Nts Ps"
  unfolding Nts_def by (induction rule: path.induct) auto

lemma finite_Nts: "finite (Prods G) \<Longrightarrow> finite (Nts (Prods G))"
proof -
  assume "finite (Prods G)"
  have "\<forall>w A. finite (nts_syms w) \<and> finite {A}"
    using finite_nts_syms by blast
  hence "\<forall>w A. finite (nts_syms w \<union> {A})"
    using finite_Un by simp
  thus "finite (Nts (Prods G))"
    unfolding Nts_def using \<open>finite (Prods G)\<close> by auto
qed

lemma finite_nts: "finite (nts (prods G))"
proof -
  have "\<forall>w A. finite (nts_syms w) \<and> finite {A}"
    using finite_nts_syms by blast
  hence "\<forall>w A. finite (nts_syms w \<union> {A})"
    using finite_Un by simp
  thus ?thesis
    unfolding Nts_def by auto
qed

lemma card_split: "card (set xs) < length xs \<Longrightarrow> (\<exists>a l m r. xs = l@[a]@m@[a]@r)"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case 
  proof(cases "x \<in> set xs")
    case True
    then obtain m r where "xs = m@[x]@r" 
      using split_list by fastforce
    hence "x#xs = []@[x]@m@[x]@r" 
      by simp
    then show ?thesis by blast
  next
    case False
    hence "card (set xs) < length xs" 
      using Cons by auto
    then obtain a l m r where "xs = l@[a]@m@[a]@r"
      using Cons.IH by blast
    then obtain l' where "l' = x#l \<and> x#xs = l'@[a]@m@[a]@r"
      by simp
    thus ?thesis
      by blast
  qed
qed

lemma inner_aux: 
  assumes "\<forall>w' p'. (Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p3\<rangle> w) \<and> ((Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> w') \<longrightarrow>
          (Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p2@[A]@p'\<rangle> (v@w'@x)))"
  shows "Ps \<turnstile> A \<Rightarrow>\<langle>(([A]@p2)\<^sup>*(Suc i)) @ [A]@p3\<rangle> ((v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i)))"
  using assms proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  hence 1: "Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p2@ (([A] @ p2)\<^sup>*i) @ [A]@p3\<rangle> (v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i))"
    by simp
  hence "Ps \<turnstile> A \<Rightarrow>\<langle>[A] @ p2 @ [A] @ p2@ (([A] @ p2)\<^sup>*i) @ [A]@p3\<rangle> v @ (v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i)) @ x"
    using assms by fastforce
  thus ?case 
    using repl_append[of \<open>Suc i\<close> x] by simp
qed

lemma inner_pumping: 
  assumes "cnf g"
    and "m = card (nts (prods g))"
    and "z \<in> langS g"
    and "length z \<ge> 2^(m+1)"
  shows "\<exists>u v w x y . z = u@v@w@x@y \<and> length (v@w@x) \<le> 2^(m+1) \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> langS g)"
proof -
  obtain S Ps where SPs: "S = start g \<and> Ps = set (prods g)"
    by simp
  then obtain p' where p': "Ps \<turnstile> S \<Rightarrow>\<langle>p'\<rangle> z"
    using assms Lang_def[of Ps S] path_if_derives[of Ps S] by blast
  then obtain lp where lp: "Ps \<turnstile> S \<Rightarrow>\<llangle>lp\<rrangle> z"
    using path_lpath[of Ps] by blast
  hence 1: "set lp \<subseteq> Nts Ps"
    using lpath_path[of Ps] path_nts[of Ps] by blast
  have "length lp > m"
  proof -
    have "(2^(m+1)::nat) \<le> 2^length lp"
      using lp lpath_length[of Ps S lp z] assms(4) le_trans by blast
    hence "m+1 \<le> length lp" 
      using power_le_imp_le_exp[of 2 \<open>m+1\<close> \<open>length lp\<close>] by auto
    thus ?thesis
      by simp
  qed
  then obtain l p where p: "lp = l@p \<and> length p = m+1"
    using less_Suc_eq by (induction lp) fastforce+
  hence "set l \<subseteq> Nts Ps \<and> set p \<subseteq> Nts Ps \<and> finite (Nts Ps)"
    using 1 finite_nts[of g] assms(1) SPs by auto
  hence "card (set p) < length p"
    using p assms(2) card_mono[of \<open>Nts Ps\<close> \<open>set p\<close>] SPs by simp
  then obtain A p1 p2 p3 where "p = p1@[A]@p2@[A]@p3"
    using card_split by blast
  then obtain u vwx y where uy: "((Ps \<turnstile> A \<Rightarrow>\<llangle>[A]@p2@[A]@p3\<rrangle> vwx) \<and> z = u@vwx@y \<and>
        (\<forall>w' p'. ((Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> S \<Rightarrow>\<langle>l@p1@[A]@p'\<rangle> u@w'@y)))"
    using substitution_lp[of Ps S \<open>l@p1\<close> A \<open>p2@[A]@p3\<close> z] lp p by auto
  hence "length vwx \<le> 2^(m+1)"
    using \<open>p = _\<close> p lpath_length[of Ps A \<open>[A] @ p2 @ [A] @ p3\<close> vwx] order_subst1 by fastforce
  then obtain v w x where vwx: "(Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p3\<rangle> w) \<and> vwx = v@w@x \<and>
        (\<forall>w' p'. ((Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> w') \<longrightarrow> Ps \<turnstile> A \<Rightarrow>\<langle>[A]@p2@[A]@p'\<rangle> v@w'@x)) \<and>
        (length ([A]@p2) > 0 \<longrightarrow> length (v@x) > 0)"
    using substitution[of Ps A \<open>[A]@p2\<close> A p3 vwx] uy lpath_path[of Ps A] by auto
  have "\<forall>i \<ge> 0. Ps \<turnstile> S \<Rightarrow>\<langle>l@p1@ (([A]@p2)\<^sup>*i) @[A]@p3\<rangle> (u@(v\<^sup>*i)@w@(x\<^sup>*i)@y)"
  proof 
    fix i
    have "\<forall>i. Ps \<turnstile> A \<Rightarrow>\<langle>repl ([A]@p2) (Suc i) @ [A]@p3\<rangle> (repl v (Suc i) @ w @ repl x (Suc i))"
      using vwx inner_aux[of Ps A] by blast
    hence "\<forall>i \<ge> 0. Ps \<turnstile> S \<Rightarrow>\<langle>l@p1@(([A]@p2)\<^sup>*(Suc i)) @[A]@p3\<rangle> (u@ (v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i)) @y)"
      using uy by fastforce
    moreover have "Ps \<turnstile> S \<Rightarrow>\<langle>l@p1@(([A]@p2)\<^sup>*0) @[A]@p3\<rangle> (u@ (v\<^sup>*0) @ w @ (x\<^sup>*0) @y)"
      using vwx uy by auto
    ultimately show "i \<ge> 0 \<longrightarrow> Ps \<turnstile> S \<Rightarrow>\<langle>l@p1@ (([A]@p2)\<^sup>*i) @[A]@p3\<rangle> (u@(v\<^sup>*i)@w@(x\<^sup>*i)@y)"
      by (induction i) simp_all
  qed
  hence "\<forall>i \<ge> 0. (u@(v\<^sup>*i)@w@(x\<^sup>*i)@y) \<in> langS g"
    unfolding Lang_def using assms(1) assms(2) SPs derives_if_path[of Ps S] by blast
  hence "z = u@v@w@x@y \<and> length (v@w@x) \<le> 2^(m+1) \<and> 1 \<le> length (v@x) \<and> (\<forall> i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@ y \<in> langS g)"
    using vwx uy \<open>length vwx \<le> 2 ^ (m + 1)\<close> by (simp add: Suc_leI)
  then show ?thesis
    by blast
qed

theorem pumping_lemma:
  assumes "cnf g"
  shows "\<exists>n. \<forall>z \<in> langS g. length z \<ge> n \<longrightarrow>
     (\<exists>u v w x y. z = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> langS g))"
  using assms inner_pumping[of g \<open>card (nts (prods g))\<close>] by blast

end