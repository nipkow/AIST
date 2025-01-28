theory PumpingLemma
  imports "../CFG" CNF
begin

(* some ideas for derivation trees *)
datatype ('n, 't) dtree =
  Leaf ("nonTerminal": 'n) ("terminal": 't) ("(\<langle>_,/ _,\<rangle>)") |
  Node ("nonTerminal": 'n) "('n, 't) dtree" "('n, 't) dtree" ("(1\<langle>_,/ _,/ _\<rangle>)")

fun dheight :: "('n, 't) dtree \<Rightarrow> nat" where 
  "dheight (Leaf N t) = 1" |
  "dheight (Node N l r) = Suc (max (dheight l) (dheight r))"

(* implementation of Thomas Ammer *)
abbreviation repl :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<^sup>*/_")
  where "xs\<^sup>*n \<equiv> concat (replicate n xs)"

lemma repl_append: "(x\<^sup>*(Suc i)) = (x\<^sup>*i) @ x"
  by (induction i) simp_all

(* paths for Prods in CNF form *)
(* prods \<Rightarrow> Start Nt \<Rightarrow> path \<Rightarrow> word  (path = Nt list, word = Tm list) *)
inductive path :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool" 
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>'\<langle>_'\<rangle>/ _))" [50, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[A]\<rangle> [a]" |
left:  "(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<Longrightarrow> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v) \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p\<rangle> (w@v)" |
right:  "(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<Longrightarrow> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v) \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#q\<rangle> (w@v)"

(* rules for derivations of words if the grammar is in cnf *)
inductive cnf_derives :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_/ \<Rightarrow>cnf/ _))" [50, 0, 50] 50) where
step:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>cnf [a]"|
trans:  "(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> P \<turnstile> B \<Rightarrow>cnf w \<Longrightarrow> P \<turnstile> C \<Rightarrow>cnf v \<Longrightarrow> P \<turnstile> A \<Rightarrow>cnf (w@v)"

lemma path_if_cnf_derives:
  "P \<turnstile> S \<Rightarrow>cnf w \<Longrightarrow> \<exists>p. P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  apply (induction rule: cnf_derives.induct) by (auto intro: path.intros)

lemma cnf_derives_if_path:
  "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> P \<turnstile> S \<Rightarrow>cnf w"
  apply (induction rule: path.induct) by (auto intro: cnf_derives.intros)

lemma cnf_der: 
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w" "CNF P" 
  shows "P \<turnstile> S \<Rightarrow>cnf w"
using assms proof (induction w arbitrary: S rule: length_induct)
  case (1 w)
  have "Eps_free P"
    using assms(2) CNF_eq by blast
  hence "\<not>(P \<turnstile> [Nt S] \<Rightarrow>* [])"
    by (simp add: Eps_free_derives_Nil)
  hence 2: "length w \<noteq> 0" 
    using 1 by auto
  thus ?case
  proof (cases "length w \<le> 1")
    case True
    hence "length w = 1"
      using 2 by linarith
    then obtain t where "w = [t]" (is "?t")
      using length_Suc_conv[of w 0] by auto 
    hence "(S, [Tm t]) \<in> P"
      using 1 assms(2) cnf_single_derive[of P S t] by simp
    thus ?thesis
      by (simp add: \<open>?t\<close> cnf_derives.intros(1))
  next
    case False 
    obtain A B u v where "(S, [Nt A, Nt B]) \<in> P \<and> P \<turnstile> [Nt A] \<Rightarrow>* map Tm u \<and> P \<turnstile> [Nt B] \<Rightarrow>* map Tm v \<and> u@v = w \<and> u \<noteq> [] \<and> v \<noteq> []" (is "?ABuv")
      using False assms(2) 1 cnf_word[of P S w] by auto
    have "length u < length w \<and> length v < length w"
      using \<open>?ABuv\<close> by auto
    hence "cnf_derives P A u \<and> cnf_derives P B v"
      using 1 \<open>?ABuv\<close> by blast
    thus ?thesis
      using \<open>?ABuv\<close> cnf_derives.intros(2)[of S A B P u v] by blast
  qed
qed

lemma der_cnf:
  assumes "P \<turnstile> S \<Rightarrow>cnf w" "CNF P"
  shows "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
using assms proof (induction rule: cnf_derives.induct)
  case (step A a P)
  then show ?case 
    by (simp add: derive_singleton r_into_rtranclp)
next
  case (trans A B C P w v)
  hence "P \<turnstile> [Nt A] \<Rightarrow> [Nt B, Nt C]"
    by (simp add: derive_singleton)
  moreover have "P \<turnstile> [Nt B] \<Rightarrow>* map Tm w \<and> P \<turnstile> [Nt C] \<Rightarrow>* map Tm v"
    using trans by blast
  ultimately show ?case 
    using derives_append_decomp[of P \<open>[Nt B]\<close> \<open>[Nt C]\<close> \<open>map Tm (w @ v)\<close>] by auto
qed

corollary cnf_der_eq: "CNF P \<Longrightarrow> (P \<turnstile> [Nt S] \<Rightarrow>* map Tm w \<longleftrightarrow> P \<turnstile> S \<Rightarrow>cnf w)"
  using cnf_der[of P S w] der_cnf[of P S w] by blast

lemma path_if_derives: 
  assumes "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w" "CNF P" 
  shows "\<exists>p. P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  using assms cnf_der[of P S w] path_if_cnf_derives[of P S w] by blast

lemma derives_if_path:
  assumes "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w" "CNF P"
  shows "P \<turnstile> [Nt S] \<Rightarrow>* map Tm w"
  using assms der_cnf[of P S w] cnf_derives_if_path[of P S p w] by blast

(* longest path, similar to path, the difference is that lpath always chooses the longest path in a derivation tree *)
inductive lpath :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool" 
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>'\<llangle>_'\<rrangle>/ _))" [50, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<llangle>[A]\<rrangle> [a]" |
nonTerminals:  "(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> (P \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> (P \<turnstile> C \<Rightarrow>\<llangle>q\<rrangle> v) \<Longrightarrow> 
                P \<turnstile> A \<Rightarrow>\<llangle>A#(if length p \<ge> length q then p else q)\<rrangle> (w@v)" 

lemma path_lpath: "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>p'. (P \<turnstile> S \<Rightarrow>\<llangle>p'\<rrangle> w) \<and> length p' \<ge> length p"
  by (induction rule: path.induct) (auto intro: lpath.intros)

lemma lpath_path: "(P \<turnstile> S \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  by (induction rule: lpath.induct) (auto intro: path.intros)

(*Property of the derivation tree: Since the tree is a binary tree, word lengths are always \<le> 2^longest path*)
lemma lpath_length: "(P \<turnstile> S \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> length w \<le> 2^length p"
proof (induction rule: lpath.induct)
  case (terminal A a P)
  then show ?case by simp
next
  case (nonTerminals A B C P p w q v)
  then show ?case 
  proof (cases "length p \<ge> length q")
    case True
    hence "length v \<le> 2^length p"
      using nonTerminals(5) order_subst1[of \<open>length v\<close> \<open>\<lambda>x. 2^x\<close> \<open>length q\<close> \<open>length p\<close>] by simp
    hence "length w +length v \<le> 2*2^length p"
      by (simp add: nonTerminals.IH(1) add_le_mono mult_2)
    then show ?thesis
      by (simp add: True)
  next
    case False
    hence "length w \<le> 2^length q"
      using nonTerminals(4) order_subst1[of \<open>length w\<close> \<open>\<lambda>x. 2^x\<close> \<open>length p\<close> \<open>length q\<close>] by simp 
    hence "length w +length v \<le> 2*2^length q"
      by (simp add: nonTerminals.IH(2) add_le_mono mult_2)
    then show ?thesis
      by (simp add: False)
  qed
qed

(*auxiliary lemma: if A\<rightarrow>*wv using a#p and length a#p \<ge> 1 then the derivation can be decomposed:
there exist B C where B\<rightarrow>*w and C\<rightarrow>*v and A\<rightarrow>BC and one of both derivation uses the path p. *)
lemma step_decomp:
  assumes "P \<turnstile> A \<Rightarrow>\<langle>[A]@p\<rangle> w" " length p \<ge> 1" 
  shows "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> P \<and> w =a@b \<and>
        (((P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<langle>p'\<rangle> b)) \<or> ((P \<turnstile> B \<Rightarrow>\<langle>p'\<rangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<langle>p\<rangle> b)))"
  using assms by (cases) fastforce+

lemma steplp_decomp:
  assumes "P \<turnstile> A \<Rightarrow>\<llangle>[A]@p\<rrangle> w" " length p \<ge> 1" 
  shows "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> P \<and> w =a@b \<and>
      (((P \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length p \<ge> length p') \<or>
      ((P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p\<rrangle> b) \<and> length p \<ge> length p'))"
  using assms by (cases) fastforce+

(* some helper lemmas *)
lemma path_first_step: "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>q. p = [A]@q "
  by (induction rule: path.induct) simp_all

lemma no_empty: "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> length w > 0"
  by (induction rule: path.induct) simp_all

(*if A\<rightarrow>*z using p1Xp2 then z can be decomposed into v w x where X\<rightarrow>*w and if X\<rightarrow>*w' then A\<rightarrow>*vw'x.
v and x are universal, i.e. they are independent from arbitrary w'.
If the front part p1 is not empty then v or x is not empty.*)
lemma substitution: 
  assumes "P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p2\<rangle> z"
  shows "\<exists>v w x. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> z = v@w@x \<and>
        (\<forall>subst p'. ((P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@subst@x)) \<and>
        (length p1 > 0 \<longrightarrow> length (v@x) > 0)"
using assms proof (induction p1 arbitrary: P A z X p2)
  case Nil
  hence "\<forall>subst p'. ((P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> z) \<and> z = []@z@[] \<and>
        ((P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[]@[X]@p'\<rangle> ([]@subst@[])) \<and>
        (length [] > 0 \<longrightarrow> length ([]@[]) > 0))"
    using path_first_step[of P A] by auto
  then show ?case 
    by blast
next
  case (Cons A p1 P Y)
  hence 0: "A = Y"
    using path_first_step[of P Y] by fastforce 
  have "length (p1@[X]@p2) \<ge> 1"
    by simp
  hence "\<exists>B C a b q. (A, [Nt B, Nt C]) \<in> P \<and> a@b = z \<and> 
        (((P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b) \<or> ((P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p2\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> b))"
    using Cons.prems path_first_step step_decomp by fastforce
  then obtain B C a b q where "(A, [Nt B, Nt C]) \<in> P \<and> a@b = z \<and> 
        (((P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b) \<or> ((P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p2\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> b))" (is "?BC")
    by blast
  then show ?case
  proof (cases "((P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b)")
    case True
    then obtain v w x where "(P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> b = v@w@x \<and> 
          (\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@subst@x))" (is "?vwx")
      using Cons.IH by blast
    hence 1: "\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (a@v@subst@x)"
      using \<open>?BC\<close> by (auto intro: path.intros(3))
    obtain v' where "v' = a@v" (is "?v'")
      by simp
    hence "length (v'@x) > 0"
      using True no_empty by fast
    hence "(P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> z = v'@w@x \<and> (\<forall>subst p'.
          (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v'@subst@x)) \<and>
          (length (A#p1) > 0 \<longrightarrow> length (v'@x) >0)"
      using \<open>?vwx\<close> 1 \<open>?BC\<close> \<open>?v'\<close> by simp
    thus ?thesis
      using 0 by auto
  next
    case False
    then obtain v w x where "(P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> a = v@w@x \<and> 
          (\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@subst@x))" (is "?vwx")
      using Cons.IH \<open>?BC\<close> by blast
    hence 1: "\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@subst@x@b)"
      using \<open>?BC\<close> left[of A B C P] by fastforce
    hence "(P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> z = v@w@x@b \<and> (\<forall>subst p'.
          (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@subst@x@b)) \<and>
          (length (A#p1) > 0 \<longrightarrow> length (a@v@x) >0)"
      using \<open>?vwx\<close> \<open>?BC\<close> no_empty by fastforce
    moreover have "length (v@x@b) > 0"
      using no_empty \<open>?BC\<close> by fast
    ultimately show ?thesis
    using 0 by auto
  qed
qed

(* Same for longest path. the longest path of w is interesting in case of reasoning about length w *)
lemma substitution_lp: 
  assumes "P \<turnstile> A \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> z"
  shows "\<exists>v w x. ((P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> z = v@w@x \<and>
        (\<forall>subst p'. ((P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@subst@x)))"
using assms proof (induction p1 arbitrary: P A z X p2)
  case Nil
  hence "\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[]@[X]@p'\<rangle> ([]@subst@[])"
    using path_first_step lpath_path by fastforce
  moreover have "(P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> z) \<and> z = []@z@[]"
    using Nil lpath.cases[of P A \<open>[X] @ p2\<close> z] by auto
  ultimately show ?case 
    by blast
next
  case (Cons A p1 P Y)
  hence 0: "A = Y"
    using path_first_step[of P Y] lpath_path by fastforce 
  have "length (p1@[X]@p2) \<ge> 1"
    by simp
  hence "\<exists>B C p' a b. (A, [Nt B, Nt C]) \<in> P \<and> z = a@b \<and> 
        (((P \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p') \<or> 
        ((P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p'))"
    using steplp_decomp[of P A \<open>p1@[X]@p2\<close> z] 0 Cons by simp
  then obtain B C p' a b where "(A, [Nt B, Nt C]) \<in> P \<and> z = a@b \<and> 
        (((P \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p') \<or> 
        ((P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p'))" (is "?BC")
    by blast
  then show ?case
  proof (cases "(P \<turnstile> B \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p'\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p'")
    case True
    then obtain v w x where "(P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> a = v@w@x \<and> 
          (\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@subst@x))" (is "?vwx")
      using Cons.IH by blast
    hence "(P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> z = v@w@x@b \<and>
       (\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v@subst@x@b))"
      using \<open>?BC\<close> lpath_path[of P] path.intros(2)[of A B C P] by fastforce
    then show ?thesis
      using 0 by auto
  next
    case False
    hence "((P \<turnstile> B \<Rightarrow>\<llangle>p'\<rrangle> a) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>p1@[X]@p2\<rrangle> b) \<and> length (p1@[X]@p2) \<ge> length p')"
      using \<open>?BC\<close> by blast
    then obtain v w x where "(P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> b = v@w@x \<and> 
          (\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p'\<rangle> (v@subst@x))" (is "?vwx")
      using Cons.IH by blast
    then obtain v' where "v' = a@v" (is "?v'")
      by simp
    hence "(P \<turnstile> X \<Rightarrow>\<llangle>[X]@p2\<rrangle> w) \<and> z = v'@w@x \<and>
       (\<forall>subst p'. (P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p1@[X]@p'\<rangle> (v'@subst@x))"
      using \<open>?BC\<close> lpath_path[of P] path.intros(3)[of A B C P] \<open>?vwx\<close> by fastforce
    then show ?thesis
      using 0 by auto
  qed
qed

lemma path_nts: "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> set p \<subseteq> Nts P"
  unfolding Nts_def by (induction rule: path.induct) auto

lemma finite_nts: "finite (nts (prods G))"
proof -
  have "\<forall>w A. finite (nts_of_syms w) \<and> finite {A}"
    using finite_nts_of_syms by blast
  hence "\<forall>w A. finite (nts_of_syms w \<union> {A})"
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
  assumes "\<forall>subst p'. (P \<turnstile> A \<Rightarrow>\<langle>[A]@p3\<rangle> w) \<and> ((P \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> subst) \<longrightarrow>
          (P \<turnstile> A \<Rightarrow>\<langle>[A]@p2@[A]@p'\<rangle> (v@subst@x)))"
  shows "P \<turnstile> A \<Rightarrow>\<langle>(([A]@p2)\<^sup>*(Suc i)) @ [A]@p3\<rangle> ((v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i)))"
  using assms proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  hence 1: "P \<turnstile> A \<Rightarrow>\<langle>[A]@p2@ (([A] @ p2)\<^sup>*i) @ [A]@p3\<rangle> (v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i))"
    by simp
  hence "P \<turnstile> A \<Rightarrow>\<langle>[A] @ p2 @ [A] @ p2@ (([A] @ p2)\<^sup>*i) @ [A]@p3\<rangle> v @ (v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i)) @ x"
    using assms by fastforce
  thus ?case 
    using repl_append[of \<open>Suc i\<close> x] by simp
qed

lemma inner_pumping: 
  assumes "cnf G"
    and "m = card (nts (prods G))"
    and "z \<in> L G"
    and "length z \<ge> 2^(m+1)"
  shows "\<exists>u v w x y . z = u@v@w@x@y \<and> length (v@w@x) \<le> 2^(m+1) \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G)"
proof -
  obtain S P where "S = start G \<and> P = set (prods G)" (is "?SP")
    by simp
  then obtain p' where "P \<turnstile> S \<Rightarrow>\<langle>p'\<rangle> z" (is "?p'")
    using assms Lang_def[of P S] path_if_derives[of P S] by blast
  then obtain pg where "P \<turnstile> S \<Rightarrow>\<llangle>pg\<rrangle> z" (is "?pg")
    using path_lpath[of P] by blast
  hence 1: "set pg \<subseteq> Nts P"
    using lpath_path[of P] path_nts[of P] by blast
  have "length pg > m"
  proof -
    have "(2^(m+1)::nat) \<le> 2^length pg"
      using \<open>?pg\<close> lpath_length[of P S pg z] assms(4) le_trans by blast
    hence "m+1 \<le> length pg" 
      using power_le_imp_le_exp[of 2 \<open>m+1\<close> \<open>length pg\<close>] by auto
    thus ?thesis
      by simp
  qed
  then obtain g p where "pg = g@p \<and> length p = m+1" (is "?gp")
    using less_Suc_eq by (induction pg) fastforce+
  hence "set g \<subseteq> Nts P \<and> set p \<subseteq> Nts P \<and> finite (Nts P)"
    using 1 finite_nts[of G] assms(1) \<open>?SP\<close> by auto
  hence "card (set p) < length p"
    using \<open>?gp\<close> assms(2) card_mono[of \<open>Nts P\<close> \<open>set p\<close>] \<open>?SP\<close> by simp
  then obtain A p1 p2 p3 where "p = p1@[A]@p2@[A]@p3" (is "?Ap")
    using card_split by blast
  then obtain u vwx y where "((P \<turnstile> A \<Rightarrow>\<llangle>[A]@p2@[A]@p3\<rrangle> vwx) \<and> z = u@vwx@y \<and>
        (\<forall>subst p'. ((P \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> S \<Rightarrow>\<langle>g@p1@[A]@p'\<rangle> u@subst@y)))" (is "?uy")
    using substitution_lp[of P S \<open>g@p1\<close> A \<open>p2@[A]@p3\<close> z] \<open>?pg\<close> \<open>?gp\<close> by auto
  hence "length vwx \<le> 2^(m+1)"
    using \<open>?Ap\<close> \<open>?gp\<close> lpath_length[of P A \<open>[A] @ p2 @ [A] @ p3\<close> vwx] order_subst1 by fastforce
  then obtain v w x where "(P \<turnstile> A \<Rightarrow>\<langle>[A]@p3\<rangle> w) \<and> vwx = v@w@x \<and>
        (\<forall>subst p'. ((P \<turnstile> A \<Rightarrow>\<langle>[A]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[A]@p2@[A]@p'\<rangle> v@subst@x)) \<and>
        (length ([A]@p2) > 0 \<longrightarrow> length (v@x) > 0)" (is "?vwx")
    using substitution[of P A \<open>[A]@p2\<close> A p3 vwx] \<open>?uy\<close> lpath_path[of P A] by auto
  have "\<forall>i \<ge> 0. P \<turnstile> S \<Rightarrow>\<langle>g@p1@ (([A]@p2)\<^sup>*i) @[A]@p3\<rangle> (u@(v\<^sup>*i)@w@(x\<^sup>*i)@y)"
  proof 
    fix i
    have "\<forall>i. P \<turnstile> A \<Rightarrow>\<langle>repl ([A]@p2) (Suc i) @ [A]@p3\<rangle> (repl v (Suc i) @ w @ repl x (Suc i))"
      using \<open>?vwx\<close> inner_aux[of P A] by blast
    hence "\<forall>i \<ge> 0. P \<turnstile> S \<Rightarrow>\<langle>g@p1@(([A]@p2)\<^sup>*(Suc i)) @[A]@p3\<rangle> (u@ (v\<^sup>*(Suc i)) @ w @ (x\<^sup>*(Suc i)) @y)"
      using \<open>?uy\<close> by fastforce
    moreover have "P \<turnstile> S \<Rightarrow>\<langle>g@p1@(([A]@p2)\<^sup>*0) @[A]@p3\<rangle> (u@ (v\<^sup>*0) @ w @ (x\<^sup>*0) @y)"
      using \<open>?vwx\<close> \<open>?uy\<close> by auto
    ultimately show "i \<ge> 0 \<longrightarrow> P \<turnstile> S \<Rightarrow>\<langle>g@p1@ (([A]@p2)\<^sup>*i) @[A]@p3\<rangle> (u@(v\<^sup>*i)@w@(x\<^sup>*i)@y)"
      by (induction i) simp_all
  qed
  hence "\<forall>i \<ge> 0. (u@(v\<^sup>*i)@w@(x\<^sup>*i)@y) \<in> L G"
    unfolding Lang_def using assms(1) assms(2) \<open>?SP\<close> derives_if_path[of P S] by blast
  hence "z = u@v@w@x@y \<and> length (v@w@x) \<le> 2^(m+1) \<and> 1 \<le> length (v@x) \<and> (\<forall> i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@ y \<in> L G)"
    using \<open>?vwx\<close> \<open>?uy\<close> \<open>length vwx \<le> 2 ^ (m + 1)\<close> by (simp add: Suc_leI)
  then show ?thesis
    by blast
qed

theorem pumping_lemma:
  assumes "cnf G"
  shows "\<exists>n. \<forall>z \<in> L G. length z \<ge> n \<longrightarrow>
     (\<exists>u v w x y. z = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G))"
  using assms inner_pumping[of G \<open>card (nts (prods G))\<close>] by blast

end