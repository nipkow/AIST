theory Finite_Automata_Not_HF
imports Main HereditarilyFinite.Ordinal "$AFP/Finite_Automata_HF/Finite_Automata_HF"
begin


text\<open>This file contains a version of the dfa and nfa definition from Finite_Automata_Hf 
but with \<open>'b set\<close> as states set, instead of forcing \<open>hf set\<close>. 
It is intended to be used for easier constructions of explicitly given languages,
not for abstract constructions such as the intersection of 2 automaton languages.
The locale below adds a converter from this dfa to the hf version dfa, to show that regularity also
holds for the language of this dfa.

Todo: add converter for nfa.
TODO: rename locales.\<close>


text\<open>First, the record for DFAs\<close>
record ('a, 'b) dfa' = states :: "'b set"
                init   :: "'b"
                final  :: "'b set"
                nxt    :: "'b \<Rightarrow> 'a \<Rightarrow> 'b"

locale dfa' =
  fixes M :: "('a, 'b) dfa'"
  assumes init [simp]: "init M \<in> states M"
      and final:       "final M \<subseteq> states M"
      and nxt:         "\<And>q x. q \<in> states M \<Longrightarrow> nxt M q x \<in> states M"
      and finite:      "finite (states M)"

begin

lemma finite_final [simp]: "finite (final M)"
  using final finite_subset finite by blast

text\<open>Transition function for a given starting state and word.\<close>
primrec nextl :: "['b, 'a list] \<Rightarrow> 'b" where
    "nextl q []     = q"
  | "nextl q (x#xs) = nextl (nxt M q x) xs"

definition language :: "'a list set"  where
  "language \<equiv> {xs. nextl (init M) xs \<in> final M}"





text\<open>The left language WRT a state q is the set of words that lead to q.\<close>
definition left_lang :: "'b \<Rightarrow> 'a list set"  where
  "left_lang q \<equiv> {u. nextl (init M) u = q}"

text\<open>Part of Prop 1 of
  Jean-Marc Champarnaud, A. Khorsi and T. Paranthoën,
  Split and join for minimizing: Brzozowski's algorithm,
  Prague Stringology Conference 2002\<close>
lemma left_lang_disjoint:
  "q1 \<noteq> q2 \<Longrightarrow> left_lang q1 \<inter> left_lang q2 = {}"
  unfolding left_lang_def by auto

text\<open>The right language WRT a state q is the set of words that go from q to F.\<close>
definition right_lang :: "'b \<Rightarrow> 'a list set"  where
  "right_lang q \<equiv> {u. nextl q u \<in> final M}"

lemma language_eq_right_lang: "language = right_lang (init M)"
  using language_def right_lang_def by auto

lemma nextl_app: "nextl q (xs@ys) = nextl (nextl q xs) ys"
  by (induct xs arbitrary: q) auto

lemma nextl_snoc [simp]: "nextl q (xs@[x]) = nxt M (nextl q xs) x"
  by (simp add: nextl_app)

lemma nextl_state: "q \<in> states M \<Longrightarrow> nextl q xs \<in> states M"
  by (induct xs arbitrary: q) (auto simp: nxt)

lemma nextl_init_state [simp]: "nextl (init M) xs \<in> states M"
  by (simp add: nextl_state)














end



lemma embed_finite_to_hf:
fixes B::\<open>'b set\<close>
assumes \<open>finite B\<close>
shows \<open>\<exists>(f:: 'b \<Rightarrow> hf).  inj_on f B  \<close>
proof-
from \<open>finite B\<close> obtain f_inv1::\<open>nat \<Rightarrow> 'b\<close> and n::nat where \<open>B = f_inv1 ` {i. i < n} \<and> inj_on f_inv1 {i. i < n}\<close>  using finite_imp_nat_seg_image_inj_on by fastforce
then obtain f1::\<open>'b \<Rightarrow> nat\<close> where \<open>(\<forall>x \<in> B. f_inv1 (f1 x) = x) \<and> (\<forall>x \<in> (f1 ` B). f1 (f_inv1 x) = x)\<close> by (metis (lifting) f_the_inv_into_f the_inv_into_f_f the_inv_into_onto)
then have \<open>inj_on (ord_of o f1) B\<close> by (metis comp_inj_on inj_on_def inj_ord_of)
then show ?thesis by blast
qed





locale embed_dfa = 
fixes M' :: \<open>('a, 'b) dfa'\<close>
and f:: \<open>'b \<Rightarrow> hf\<close>

assumes dfa'_M': \<open>dfa' M'\<close>
and \<open>inj_on f (states M')\<close>

begin




abbreviation f_inv where 
\<open>f_inv \<equiv> the_inv_into (states M') f\<close>

abbreviation hf_M' where
\<open>hf_M' \<equiv>  \<lparr>dfa.states = f ` (states M'),
                init  = f (init M'),
                final = f ` (final M'),
                nxt   = \<lambda>q x. f( nxt M' (f_inv q) x) \<rparr>\<close>

lemma f_f_inv[simp]: \<open>h \<in> dfa.states hf_M' \<Longrightarrow> f (f_inv h) = h\<close> by (metis dfa.select_convs(1) embed_dfa_axioms embed_dfa_def f_the_inv_into_f)
lemma f_in[intro]: \<open>q \<in> dfa'.states M' \<Longrightarrow> f q \<in> dfa.states hf_M'\<close> by simp
lemma f_in_final[intro]:\<open>q \<in> dfa'.final M' \<Longrightarrow> f q \<in> dfa.final hf_M'\<close> by simp
lemma f_f__inv_init[simp]: \<open>f( f_inv( dfa.init hf_M' ) ) = dfa.init hf_M'\<close> by (simp add: dfa'.init dfa'_M')

lemma f_inv_f[simp]: \<open>q \<in> dfa'.states M' \<Longrightarrow> f_inv (f q) = q\<close> by (meson embed_dfa_axioms embed_dfa_def the_inv_into_f_f)
lemma f_inv_in[intro]: \<open>h \<in> dfa.states hf_M' \<Longrightarrow> f_inv h \<in> dfa'.states M'\<close> by fastforce
lemma f_inv_in_final[intro]: \<open>h \<in> dfa.final hf_M' \<Longrightarrow> f_inv h \<in> dfa'.final M'\<close> using dfa'_M' dfa'_def by fastforce
lemma f_inv_f_init[simp]: \<open>f_inv( f( dfa'.init M' ) ) = dfa'.init M'\<close> by (simp add: dfa'.init dfa'_M')


lemma dfa_hf_M': \<open>dfa hf_M'\<close>
proof(standard, goal_cases)
  case 1
  then show ?case using dfa'.init dfa'_M' by auto
next
  case 2
  then show ?case apply simp using dfa'.final dfa'_M' by blast
next
  case (3 q x)
  then show ?case by (simp add: dfa'.nxt dfa'_M' f_inv_in)
next
  case 4
  then show ?case using dfa'_M' dfa'_def by auto
qed


interpretation M': dfa' M'
  by (fact dfa'_M')

interpretation hf_M': dfa hf_M'
  by (fact dfa_hf_M')


lemma nxt_M'_f_inv: \<open>h \<in> dfa.states hf_M' \<Longrightarrow> dfa'.nxt M' (f_inv h) x = f_inv (dfa.nxt hf_M' h x)\<close> by (simp add: dfa'.nxt dfa'_M' f_inv_in)

lemma nxt_hf_M'_f:\<open>q \<in> dfa'.states M' \<Longrightarrow> dfa.nxt hf_M' (f q) x = f (dfa'.nxt M' q x)\<close> by auto


lemma nextl_M'_f_inv: \<open>h \<in> dfa.states hf_M' \<Longrightarrow> M'.nextl  (f_inv h) xs = f_inv (hf_M'.nextl h xs)\<close>
proof(induction xs arbitrary: h)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have \<open>M'.nextl (dfa'.nxt M' (f_inv h) a) xs = f_inv (hf_M'.nextl (f (dfa'.nxt M' (f_inv h) a)) xs)\<close> using f_f_inv hf_M'.nxt nxt_M'_f_inv by presburger
  then show ?case by simp
qed 


lemma nextl_hf_M'_f: \<open>q \<in> dfa'.states M' \<Longrightarrow> hf_M'.nextl (f q) xs = f (M'.nextl q xs)\<close>
proof(induction xs arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have \<open>hf_M'.nextl (f (dfa'.nxt M' q a)) xs = f (M'.nextl (dfa'.nxt M' q a) xs)\<close> using M'.nxt by blast
  then show ?case by (simp add: Cons.prems)
qed 


lemma M'_lang_eq_hf_M'_lang: \<open>M'.language = hf_M'.language\<close>
unfolding M'.language_def hf_M'.language_def by (metis M'.init dfa.select_convs(2) f_in_final f_inv_f_init f_inv_in_final hf_M'.init nextl_M'_f_inv nextl_hf_M'_f)


end



corollary ex_hf_M:
fixes M' :: \<open>('a, 'b) dfa'\<close>
assumes dfa'_M': \<open>dfa' M'\<close>
shows \<open>\<exists>hf_M'. dfa hf_M' \<and> dfa'.language M' = dfa.language hf_M'\<close> 
proof-
  interpret M': dfa' M' using dfa'_M' by simp
  have \<open>finite (dfa'.states M')\<close> by (simp add: M'.finite) 

  with embed_finite_to_hf[of \<open>dfa'.states M'\<close>] obtain f::\<open>'b \<Rightarrow> hf\<close> where inj_on: \<open>inj_on f (dfa'.states M')\<close> by blast

  then interpret embed_dfa: embed_dfa M' f apply unfold_locales by blast

  have \<open>M'.language = dfa.language local.embed_dfa.hf_M'\<close> using embed_dfa.M'_lang_eq_hf_M'_lang by blast
  moreover have \<open>dfa local.embed_dfa.hf_M'\<close> using local.embed_dfa.dfa_hf_M' by blast

  ultimately show ?thesis by blast
qed


corollary
fixes M' :: \<open>('a, 'b) dfa'\<close>
assumes dfa'_M': \<open>dfa' M'\<close>
shows \<open>regular (dfa'.language M')\<close> using ex_hf_M using dfa'_M' regular_def by fastforce










end
