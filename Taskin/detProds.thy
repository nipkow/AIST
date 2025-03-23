theory detProds
imports "../CFG"
begin

text 
\<open>We call a non-terminal \<open>A\<close> deterministic if the grammar contains a single production of \<open>A\<close> and the form of this production is 
 \<open>(A,w)\<close>. In this case we could replace every occurrence of \<open>A\<close> with \<open>w\<close> on the right-hand sides of the productions and the 
 language of the grammar would be preserved\<close>

text 
\<open>\<open>substW xs y ys\<close> replaces every occurrence of the element \<open>y\<close> with the list of elements \<open>ys\<close> in the given list \<open>xs\<close>\<close>

definition "substW y ys xs = concat (map (\<lambda>x. if x=y then ys else [x]) xs)"

lemma substW_simps[simp]:
  "substW y ys[]  = []"
  "substW y ys (x#xs) = (if x = y then ys @ substW y ys xs else x # substW y ys xs)"
unfolding substW_def by auto

subsection \<open>Properties of \<open>substW\<close>\<close>

lemma substW_split: "substW y ys (xs @ xs') = substW y ys xs @ substW y ys xs'"
unfolding substW_def by auto

lemma substW_skip: "y \<notin> set xs \<Longrightarrow> substW y ys xs = xs"
unfolding substW_def by (induction xs) auto

lemma substW_len: "length (substW y [y'] xs) = length xs"
unfolding substW_def by (induction xs) auto

lemma substW_rev: "y' \<notin> set xs \<Longrightarrow> substW y' [y] (substW y [y'] xs) = xs"
unfolding substW_def by (induction xs) auto

lemma substW_der:
  "(B,v) \<in> P \<Longrightarrow> P \<turnstile> u \<Rightarrow>* substW (Nt B) v u"
unfolding substW_def
proof (induction u)
  case Nil
  then show ?case by simp
next
  case (Cons a u)
  then show ?case
    by (auto simp add: derives_Cons_rule derives_prepend derives_Cons)
qed

text
\<open>\<open>substP ps s u\<close> replaces every occurrence of the symbol \<open>s\<close> with the list of symbols \<open>u\<close> on the right-hand sides of the production list \<open>ps\<close>\<close>

definition substP :: "('n, 't) sym \<Rightarrow>  ('n, 't) syms \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
  "substP s u ps = map (\<lambda>(A,v). (A, substW s u v)) ps"

subsection \<open>Properties of \<open>substP\<close>\<close>

lemma substP_split: "substP s u (ps @ ps') = substP s u ps @ substP s u ps'"
  by (simp add: substP_def)

lemma substP_skip1: "s \<notin> set v \<Longrightarrow> substP s u ((A,v) # ps) = (A,v) # substP s u ps"
  by (auto simp add: substW_skip substP_def)

lemma substP_skip2: "s \<notin> syms ps \<Longrightarrow> substP s u ps = ps"
  by (induction ps) (auto simp add: substP_def substW_skip)

lemma substP_rev: "Nt B \<notin> syms ps \<Longrightarrow> substP (Nt B) [s] (substP s [Nt B] ps) = ps"
proof (induction ps)
  case Nil
  then show ?case
    by (simp add: substP_def)
next
  case (Cons a ps)
  let ?A = "fst a" let ?u = "snd a" let ?substs = "substW s [Nt B]"
  have "substP (Nt B) [s] (substP s [Nt B] (a # ps)) = substP (Nt B) [s] (map (\<lambda>(A,v). (A, ?substs v)) (a#ps))"
    by (simp add: substP_def)
  also have "... = substP (Nt B) [s] ((?A, ?substs ?u) # map (\<lambda>(A,v). (A, ?substs v)) ps)"
    by (simp add: case_prod_unfold)
  also have "... = map ((\<lambda>(A,v). (A, substW (Nt B) [s] v))) ((?A, ?substs ?u) # map (\<lambda>(A,v). (A, ?substs v)) ps)"
    by (simp add: substP_def)
  also have "... = (?A, substW (Nt B) [s] (?substs ?u)) # substP (Nt B) [s] (substP s [Nt B] ps)"
    by (simp add: substP_def)
  also from Cons have "... = (?A, substW (Nt B) [s] (?substs ?u)) # ps"
    using set_subset_Cons unfolding Syms_def by auto
  also from Cons.prems have "... = (?A, ?u) # ps"
    using substW_rev unfolding Syms_def by force
  also have "... = a # ps" by simp
  finally show ?case .
qed

lemma substP_lhss:
  "lhss ps = lhss (substP s u ps)"
by (auto simp add: Lhss_def substP_def)

lemma if_set_map:
  "x' \<in> set (map f l) \<Longrightarrow> (\<exists>x. x \<in> set l \<and> f x = x')"
  by auto

lemma substP_der:
  "(A,u) \<in> set (substP (Nt B) v ps) \<Longrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
proof -
  assume "(A,u) \<in> set (substP (Nt B) v ps)"
  then have "\<exists>u'. (A,u') \<in> set ps \<and> u = substW (Nt B) v u'" 
    using if_set_map by (smt (verit, del_insts) Pair_inject case_prod_conv old.prod.exhaust substP_def)
  then obtain u' where u'_def: "(A,u') \<in> set ps \<and> u = substW (Nt B) v u'" by blast
  then have path1: "set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u'"
    by (simp add: derive_singleton r_into_rtranclp)
  have "set ((B,v) # ps) \<turnstile> u' \<Rightarrow>* substW (Nt B) v u'"
    using substW_der by (metis list.set_intros(1))
  with u'_def have path2: "set ((B,v) # ps) \<turnstile> u' \<Rightarrow>* u" by simp
  from path1 path2 show ?thesis by simp
qed

text
\<open>In order to prove that the elimination of deterministic non-terminals preserves the language, we prove that a word can be derived if and
 only if the word can be derived after the procedure of elimination. We first show the simpler implication, namely that the list of symbols
 \<open>u\<close> can be derived before the procedure, if \<open>u\<close> can be derived after the procedure\<close>

lemma if_part:
  "set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* u \<Longrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
proof (induction rule: derives_induct)
  case (step u A v w)
  then show ?case 
    by simp (metis (no_types, lifting) derives_append derives_prepend list.simps(15) rtranclp_trans step.IH substP_der)
qed simp

text
\<open>For the other implication we first show that the list of symbols \<open>u\<close>, where the occurrences of the non-terminal \<open>B\<close> is replaced by the 
 list of symbols \<open>v\<close>, can be derived in the transformed production set if \<open>u\<close> can be derived in the original set of productions extended with
 the production \<open>(B,v)\<close>, under the following assumptions:\<close>

lemma substPW_der:
  assumes prem: "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u"
      and A_B_noteq: "A \<noteq> B"
      and B_notin_dom: "B \<notin> lhss ps"
      and B_notin_v: "Nt B \<notin> set v"
    shows "set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* substW (Nt B) v u"
using assms(1) proof (induction rule: derives_induct)
  case base
  then show ?case using assms(2) by simp
next
  case (step s B' w v')
  then show ?case
  proof (cases "B = B'")
    case True
    then have "v = v'" 
      using B_notin_dom step.hyps unfolding Lhss_def by auto
    then have "substW (Nt B) v (s @ [Nt B'] @ w) = substW (Nt B) v (s @ v' @ w)" 
      using step.prems B_notin_v True by (simp add: substW_skip substW_split)
    then show ?thesis
      using step.IH by argo
  next
    case False
    then have "(B',v') \<in> set ps"
      using step by auto
    then have "(B', substW (Nt B) v v') \<in> set (substP (Nt B) v ps)"
      by (metis (no_types, lifting) list.set_map pair_imageI substP_def)
    with rtrancl_into_rtrancl show ?thesis
      by (smt (verit, ccfv_threshold) False step.IH step.prems derive.simps rtranclp.simps substW_simps substW_split sym.inject(1))
  qed
qed

text
\<open>With the assumption that the non-terminal \<open>B\<close> is not in the list of symbols \<open>u\<close>, \<open>substW u (Nt B) v\<close> reduces to \<open>u\<close>\<close>

lemma only_if_part: 
  assumes "set ((B,v)#ps) \<turnstile> [Nt A] \<Rightarrow>* u"
      and A_B_noteq: "A \<noteq> B"
      and B_notin_dom: "B \<notin> lhss ps"
      and B_notin_v: "Nt B \<notin> set v"
      and B_notin_u: "Nt B \<notin> set u"
    shows "set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* u"
  by (metis assms substW_skip substPW_der)

text
\<open>Combining the two implications gives us the desired property of language preservation\<close>

lemma substP_lang: 
  assumes "B \<notin> lhss ps" and
          "Nt B \<notin> set v" and
          "Nt B \<notin> set u" and
          "A \<noteq> B"
        shows "set (substP (Nt B) v ps) \<turnstile> [Nt A] \<Rightarrow>* u \<longleftrightarrow> set ((B,v) # ps) \<turnstile> [Nt A] \<Rightarrow>* u"
  using assms if_part only_if_part by metis

end