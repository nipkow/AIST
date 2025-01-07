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
step:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>[A]\<rangle> [a]" |
left:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<and> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v)\<rbrakk> \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#p\<rangle> (w@v)" |
right:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> (P \<turnstile> B \<Rightarrow>\<langle>p\<rangle> w) \<and> (P \<turnstile> C \<Rightarrow>\<langle>q\<rangle> v)\<rbrakk> \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>A#q\<rangle> (w@v)"

inductive cnf_derives :: "('n, 't) Prods \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> bool"
  ("(2_ \<turnstile>/ (_/ \<Rightarrow>cnf/ _))" [50, 0, 50] 50) where
step:  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>cnf [a]"|
trans:  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> P \<turnstile> B \<Rightarrow>cnf w \<and> P \<turnstile> C \<Rightarrow>cnf v\<rbrakk> \<Longrightarrow> P \<turnstile> A \<Rightarrow>cnf (w@v)"

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
  "(A, [Tm a]) \<in> P \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<llangle>[A]\<rrangle> [a]" |
  "\<lbrakk>(A, [Nt B, Nt C]) \<in> P \<and> (P \<turnstile> B \<Rightarrow>\<llangle>p\<rrangle> w) \<and> (P \<turnstile> C \<Rightarrow>\<llangle>q\<rrangle> v)\<rbrakk> \<Longrightarrow> 
    P \<turnstile> A \<Rightarrow>\<llangle>A#(if length p \<ge> length q then p else q)\<rrangle> (w@v)" 

lemma path_lpath: "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w \<Longrightarrow> \<exists>p'. (P \<turnstile> A \<Rightarrow>\<llangle>p'\<rrangle> w) \<and> length p' \<ge> length p"
  by (induction rule: path.induct) (auto intro: lpath.intros)

lemma lpath_path: "(P \<turnstile> A \<Rightarrow>\<llangle>p\<rrangle> w) \<Longrightarrow> P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w"
  by (induction rule: lpath.induct) (auto intro: path.intros)

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