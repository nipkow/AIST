theory Binarize
imports "../CFG" detProds
begin

(* FFPI *)
lemma funpow_fix: fixes f :: "'a \<Rightarrow> 'a" and m :: "'a \<Rightarrow> nat"
assumes "\<And>x. m(f x) < m x \<or> f x = x"
shows "f((f ^^ m x) x) = (f ^^ m x) x"
proof -
 have "n + m ((f^^n) x) \<le> m x \<or> f((f^^n) x) = (f^^n) x" for n
 proof(induction n)
   case 0
   then show ?case by simp
 next
   case (Suc n)
   then show ?case
   proof
     assume a1: "n + m ((f ^^ n) x) \<le> m x"
     then show ?thesis
     proof (cases "m ((f ^^ Suc n) x) < m ((f ^^ n) x)")
       case True
       then show ?thesis using a1 by auto
     next
       case False
       with assms have "(f ^^ Suc n) x = (f ^^ n) x" by auto
       then show ?thesis by simp
     qed
   next
     assume "f ((f ^^ n) x) = (f ^^ n) x"
     then show ?thesis by simp
   qed
 qed
  from this[of "m x"] show ?thesis using assms[of "(f ^^ m x) x"] by auto
qed

fun binarize1 :: "('n :: infinite, 't) prods \<Rightarrow> ('n, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize1 ps' [] = []"
| "binarize1 ps' ((A, []) # ps) = (A, []) # binarize1 ps' ps"
| "binarize1 ps' ((A, [s0]) # ps) = (A,[s0]) # binarize1 ps' ps"
| "binarize1 ps' ((A, [s0,s1]) # ps) = (A, [s0,s1]) # binarize1 ps' ps"
| "binarize1 ps' ((A, s0 # u) # ps) = (let B = fresh ps' in (A,[s0, Nt B]) # (B, u) # ps)"

definition binarize' :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize' ps = binarize1 ps ps"

fun count :: "('n::infinite, 't) prods \<Rightarrow> nat" where
  "count [] = 0"
| "count ((A,u) # ps) = (if length u \<le> 2 then count ps else length u + count ps)"

definition binarize :: "('n::infinite, 't) prods \<Rightarrow> ('n, 't) prods" where
  "binarize ps = (binarize' ^^ (count ps)) ps"

(* does not do what binarize does? *)
definition trans2Nt :: "'n::infinite \<Rightarrow> 'n \<Rightarrow> 'n \<Rightarrow> ('n,'t) prods \<Rightarrow> ('n,'t) prods \<Rightarrow> bool" where
      "trans2Nt A B\<^sub>1 B\<^sub>2 P P' \<equiv> (
    \<exists>l r p s. (l,r) \<in> set P \<and> (r = p@[Nt B\<^sub>1,Nt B\<^sub>2]@s)
    \<and> (p \<noteq> [] \<or> s \<noteq> []) \<and> (A = fresh P)
    \<and> (P' = ((removeAll (l,r) P) @ [(A, [Nt B\<^sub>1,Nt B\<^sub>2]), (l, p@[Nt A]@s)])))"

lemma count_dec1:
  assumes "binarize1 ps' ps \<noteq> ps" 
  shows "count ps > count (binarize1 ps' ps)"
using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by simp
next
  case (3 ps' A s0 ps)
  then show ?case by simp
next
  case (4 ps' A s0 s1 ps)
  then show ?case by simp
next
  case (5 ps' A s0 v vb vc ps)
  then have "count (binarize1 ps' ((A, s0 # v # vb # vc) # ps)) = 
             count ((A,[s0, Nt (fresh ps')]) # (fresh ps', v # vb # vc) # ps)" by (metis binarize1.simps(5))
  also have "... = count ((fresh ps', v # vb # vc) # ps)" by simp
  also have "... < count ((fresh ps', s0 # v # vb # vc) # ps)" by simp
  also have "... = count ((A, s0 # v # vb # vc) # ps)" by simp
  finally show ?case by simp
qed

lemma count_dec:
  assumes "binarize' ps \<noteq> ps" 
  shows "count ps > count (binarize' ps)"
  using count_dec1 binarize'_def assms by metis

lemma binarize_ffpi:
  "binarize'((binarize' ^^ count x) x) = (binarize' ^^ count x) x"
proof -
  have "\<And>x. count(binarize' x) < count x \<or> binarize' x = x"
    using count_dec by blast
  then show ?thesis using funpow_fix by metis
qed

lemma binarize_binary1: 
  assumes "ps = binarize1 ps' ps"
  shows "(A,w) \<in> set(binarize1 ps' ps) \<Longrightarrow> length w \<le> 2"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A s0 ps)
  then show ?case by auto
next
  case (4 ps' A s0 s1 ps)
  then show ?case by auto
next
  case (5 ps' A s0 v vb vc ps)
  then have "(A,[s0, Nt (fresh ps')]) # (fresh ps', v # vb # vc) # ps = binarize1 ps' ((A, s0 # v # vb # vc) # ps)"
    by (metis binarize1.simps(5))
  also from 5 have "... = (A, s0 # v # vb # vc) # ps"
    by argo
  finally have "(A,[s0, Nt (fresh ps')]) # (fresh ps', v # vb # vc) # ps = (A, s0 # v # vb # vc) # ps"
    by blast
  then show ?case
    by simp
qed

lemma binarize_binary':
  assumes "ps = binarize' ps"
  shows "(A,w) \<in> set(binarize' ps) \<Longrightarrow> length w \<le> 2"
  using assms binarize_binary1 binarize'_def by metis

lemma length_binarize: "(A,w) \<in> set(binarize ps) \<Longrightarrow> length w \<le> 2"
  unfolding binarize_def using binarize_ffpi binarize_binary' by metis

lemma binarize1_cases:
  "binarize1 ps' ps = ps \<or> (\<exists>A ps'' B u s. set ps = {(A, s#u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A,[s,Nt B]),(B,u)} \<union> set ps'' \<and> Nt B \<notin> syms ps')"
proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' C ps)
  then show ?case
  proof (cases "binarize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
      using 2 by blast
    from defs have wit: "set ((C, []) # ps) = {(A, s # u)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit2: "set (binarize1 ps' ((C, []) # ps)) = {(A, [s, Nt B]), (B, u)} \<union> set ((C, []) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (3 ps' C s0 ps)
  then show ?case proof (cases "binarize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
      using 3 by blast
    from defs have wit: "set ((C, [s0]) # ps) = {(A, s # u)} \<union> set ((C, [s0]) # ps'')" by simp
    from defs have wit2: "set (binarize1 ps' ((C, [s0]) # ps)) = {(A, [s, Nt B]), (B, u)} \<union> set ((C, [s0]) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (4 ps' C s0 s1 ps)
  then show ?case  proof (cases "binarize1 ps' ps = ps")
    case True
    then show ?thesis by simp
  next
    case False
    then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps' ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> syms ps'"
      using 4 by blast
    from defs have wit: "set ((C, [s0,s1]) # ps) = {(A, s # u)} \<union> set ((C, [s0,s1]) # ps'')" by simp
    from defs have wit2: "set (binarize1 ps' ((C, [s0,s1]) # ps)) = {(A, [s, Nt B]), (B, u)} \<union> set ((C, [s0,s1]) # ps'')" by simp
    from defs have wit3: "Nt B \<notin> syms ps'" by simp
    from wit wit2 wit3 show ?thesis by blast
  qed
next
  case (5 ps' C s0 v vb vc ps)
  then show ?case
    by simp (metis fresh fresh_syms list.simps(15))
qed

lemma binarize_der1:
  assumes "N \<in> lhss ps"
  shows "set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize1 ps ps) \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
 proof (cases "binarize1 ps ps = ps")
  case True
  then show ?thesis by simp
next
  case False
  then obtain A ps'' B u s where defs: "set ps = {(A, s # u)} \<union> set ps'' \<and> set (binarize1 ps ps) = {(A, [s, Nt B]), (B, u)} \<union> set ps'' \<and> Nt B \<notin> syms ps"
    by (meson binarize1_cases)
  from defs have a_not_b: "A \<noteq> B" using syms_not_eq by fast
  from defs assms have a1: "N \<noteq> B" using syms_dom_not_eq by fastforce
  from defs have a2: "Nt B \<notin> set (map Tm x)" by auto
  from defs have a3: "Nt B \<notin> set u" using syms_not_set by fastforce
  from defs have "set ps = set ((A, s # u) # ps'')" by simp
  with defs a_not_b have a4: "B \<notin> lhss ((A, [s, Nt B]) # ps'')" using syms_dom by fastforce
  from defs have notB: "Nt B \<notin> syms ps''" by fastforce
  then have 1: "set ps = set (substP ((A, [s, Nt B]) # ps'') (Nt B) u)" proof -
    from defs have "set ps = {(A, s # u)} \<union> set ps''" by simp
    also have "... = set ((A, s#u) # ps'')" by simp
    also have "... = set ([(A, s#u)] @ ps'')" by simp
    also from defs have "... = set ([(A,substW [s, Nt B] (Nt B) u)] @ ps'')" using syms_set by fastforce
    also have "... = set ((substP [(A, [s, Nt B])] (Nt B) u) @ ps'')" by (simp add: substP_def)
    also have "... = set ((substP [(A, [s, Nt B])] (Nt B) u) @ substP ps'' (Nt B) u)" using notB by (simp add: substP_skip2)
    also have "... = set (substP ((A, [s, Nt B]) # ps'') (Nt B) u)" by (simp add: substP_def)
    finally show ?thesis by simp
  qed
  from defs have 2: "set (binarize1 ps ps) = set ((A, [s, Nt B]) # (B, u) # ps'')" by auto
  with 1 2 a1 a2 a3 a4 show ?thesis using substP_lang
    by (smt (verit) insert_commute list.simps(15))
qed

lemma binarize_der':
  assumes "N \<in> lhss ps"
  shows "set ps \<turnstile> [Nt N] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize' ps) \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
  unfolding binarize'_def by (simp add: assms binarize_der1)

lemma dom_binarize1:
  "lhss ps \<subseteq> lhss (binarize1 ps' ps)"
proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A s0 ps)
  then show ?case by auto
next
  case (4 ps' A s0 s1 ps)
  then show ?case by auto
next
  case (5 ps' A s0 v vb vc ps)
  then show ?case
    by (auto simp: Let_def)
qed

lemma dom_binarize':
  "lhss ps \<subseteq> lhss (binarize' ps)"
  by (simp add: binarize'_def dom_binarize1)

lemma dom_binarize'':
  "lhss ps \<subseteq> lhss ((binarize'^^n) ps)"
  apply (induction n)
   apply simp
  using dom_binarize' by auto

lemma binarize_der'': 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((binarize'^^n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
using assms proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "A \<in> lhss ((binarize' ^^ n) ps)"
    using assms dom_binarize'' by blast
  then have "set ((binarize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize' ((binarize' ^^ n) ps)) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    using binarize_der' by blast
  then have "set ((binarize' ^^ n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set ((binarize' ^^ Suc n) ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
    by simp
  with Suc show ?case by blast
qed

lemma binarize_der: 
  assumes "A \<in> lhss ps"
  shows "set ps \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<longleftrightarrow> set (binarize ps) \<turnstile> [Nt A] \<Rightarrow>* map Tm x"
  by (simp add: assms binarize_def binarize_der'')

lemma lang_binarize': 
  assumes "N \<in> lhss ps"
  shows "lang ps N = lang (binarize ps) N"
  by (meson Lang_eqI_derives assms binarize_der)

(* Extending assumption from domain to arbitrary non-terminal *)

lemma dom_der:
  assumes "N \<notin> Lhss P"
  shows "\<nexists>x. P \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
proof 
  from assms have nol: "\<nexists>u. (N,u) \<in> P" by (simp add: dom_set)
  assume "\<exists>x. P \<turnstile> [Nt N] \<Rightarrow>* map Tm x"
  then obtain x where x_def: "P \<turnstile> [Nt N] \<Rightarrow>* map Tm x" by blast
  then show False proof (induction rule: rtranclp.induct)
    case (rtrancl_refl a)
    with nol x_def show ?case
      by (meson deriven_start1 rtranclp_power)
  next
    case (rtrancl_into_rtrancl a b c)
    with nol x_def show ?case by blast
  qed
qed

lemma dom_lang:
  assumes "N \<notin> Lhss P"
  shows "Lang P N = {}"
  using dom_der Lang_def assms by fastforce

lemma binarize_syms1:
  assumes  "Nt N \<in> syms ps"
    shows  "Nt N \<in> syms (binarize1 ps' ps)"
using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by auto
next
  case (3 ps' A s0 ps)
  then show ?case by auto
next
  case (4 ps' A s0 s1 ps)
  then show ?case by auto
next
  case (5 ps' A s0 v vb vc ps)
  then show ?case
    by simp (metis (no_types, opaque_lifting) list.set_intros(1) list.set_intros(2) syms_inv)
qed

lemma binarize_dom1:
  assumes "N \<notin> lhss ps"
      and "N \<in> nts ps'"
    shows "N \<notin> lhss (binarize1 ps' ps)"
  using assms proof (induction ps' ps rule: binarize1.induct)
  case (1 ps')
  then show ?case by simp
next
  case (2 ps' A ps)
  then show ?case by simp
next
  case (3 ps' A s0 ps)
  then show ?case by simp
next
  case (4 ps' A s0 s1 ps)
  then show ?case by simp
next
  case (5 ps' A s0 v vb vc ps)
  then show ?case
    by (auto simp add: Let_def fresh)
qed

lemma binarize_syms_dom1:
  assumes "N \<notin> lhss ps"
      and "N \<in> nts ps"
    shows "N \<notin> lhss (binarize1 ps ps) \<and> N \<in> nts (binarize1 ps ps)"
  using assms binarize_syms1 binarize_dom1 Nts_syms_equI by metis

lemma binarize_syms_dom':
  assumes "N \<notin> lhss ps"
      and "N \<in> nts ps"
    shows "N \<notin> lhss (binarize' ps) \<and> N \<in> nts (binarize' ps)"
  unfolding binarize'_def by (simp add: assms binarize_syms_dom1)

lemma binarize_syms_dom'':
  assumes "N \<notin> lhss ps"
      and "N \<in> nts ps"
    shows "N \<notin> lhss ((binarize'^^n) ps) \<and> N \<in> nts ((binarize'^^n) ps)"
  using assms by (induction n) (auto simp add: binarize_syms_dom')

lemma binarize_syms_dom:
   assumes "N \<notin> lhss ps"
      and  "N \<in> nts ps"
    shows "N \<notin> lhss (binarize ps) \<and> N \<in> nts (binarize ps)"
  unfolding binarize_def using assms binarize_syms_dom'' by blast

lemma lang_binarize: 
  assumes "N \<in> nts ps"
  shows "lang ps N = lang (binarize ps) N"
proof (cases "N \<in> lhss ps")
  case True
  then show ?thesis
    using lang_binarize' by blast
next
  case False
  then show ?thesis
    using assms binarize_syms_dom dom_lang by metis
qed

end