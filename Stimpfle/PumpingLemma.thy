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

lemma repl_length: "length (xs\<^sup>*n) = length (xs) * n"
  by (induction n) auto

(* paths for Prods in CNF form *)
(* prods \<Rightarrow> Start Nt \<Rightarrow> word \<Rightarrow> path *)
inductive path :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool" 
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>'\<langle>_'\<rangle>/ _))" [50, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[A]\<rangle> [a]" |
left:  "(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<Longrightarrow> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v) \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p\<rangle> (w@v)" |
right:  "(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<Longrightarrow> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v) \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#q\<rangle> (w@v)"

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
    from this obtain t where "w = [t]" (is "?t")
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

(* longest path *)
inductive lpath :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> bool" 
   ("(2_ \<turnstile>/ (_/ \<Rightarrow>'\<llangle>_'\<rrangle>/ _))" [50, 0, 50] 50) where
terminal:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<llangle>[A]\<rrangle> [a]" |
nonTerminals:  "(A, [Nt B, Nt C]) \<in> P \<Longrightarrow> (P \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> (P \<turnstile> C \<Rightarrow>\<llangle>q\<rrangle> v) \<Longrightarrow> 
                P \<turnstile> A \<Rightarrow>\<llangle>A#(if length p \<ge> length q then p else q)\<rrangle> (w@v)" 

lemma path_lpath: "P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>p'. (P \<turnstile> S \<Rightarrow>\<llangle>p'\<rrangle> w) \<and> length p' \<ge> length p"
  by (induction rule: path.induct) (auto intro: lpath.intros)

lemma lpath_path: "(P \<turnstile> S \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> P \<turnstile> S \<Rightarrow>\<langle>p\<rangle> w"
  by (induction rule: lpath.induct) (auto intro: path.intros)

(*Property of the derivation tree: 
Since the tree is a binary tree, word lengths are always \<le> 2^longest path*)
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

(*first Nonterminal in the path is root node*)
lemma path_first_step: "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>q. p = [A]@q "
  by (induction rule: path.induct) simp_all

lemma no_empty: "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> length w > 0"
  by (induction rule: path.induct) simp_all

(*if A\<rightarrow>*z using p1Xp2 then z can be decomposed into v w x where X\<rightarrow>*w and if X\<rightarrow>*w' then A\<rightarrow>*vw'x.
v and x are universal, i.e. they are independent from arbitrary w'.
If the front part p1 is not empty then v or x is not empty.*)
lemma substitution: 
  assumes "P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p2\<rangle> z"
  shows "\<exists>v w x. ((P \<turnstile> X \<Rightarrow>\<langle>[X]@p2\<rangle> w) \<and> z = v@w@x \<and>
        (\<forall>subst p'. ((P \<turnstile> X \<Rightarrow>\<langle>[X]@p'\<rangle> subst) \<longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>p1@[X]@p'\<rangle> v@subst@x)) \<and>
        (length p1 > 0 \<longrightarrow> length (v@x) > 0))"
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
  from this obtain B C a b q where ttree: "(A, [Nt B, Nt C]) \<in> P \<and> a@b = z \<and> 
        (((P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b) \<or> ((P \<turnstile> B \<Rightarrow>\<langle>p1@[X]@p2\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> b))"
    by blast
  then show ?case
  proof (cases "((P \<turnstile> B \<Rightarrow>\<langle>q\<rangle> a) \<and> P \<turnstile> C \<Rightarrow>\<langle>p1@[X]@p2\<rangle> b)")
    case True
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed


(* towards pumping lemma *)
lemma inner_pumping: 
  assumes "cnf G"
    and "m = card (nts (prods G))"
    and "z \<in> L G"
    and "length z \<ge> 2^(m+1)"
  shows "\<exists>u v w x y . z = u@v@w@x@y \<and> length (v@w@x) \<le> 2^(m+1) \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G)"
  sorry

theorem pumping_lemma:
  assumes "cnf G"
  shows "\<exists>n. \<forall>z \<in> L G. length z \<ge> n \<longrightarrow>
     (\<exists>u v w x y. z = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G))"
 using assms inner_pumping[of G \<open>card (nts (prods G))\<close>] by blast

end