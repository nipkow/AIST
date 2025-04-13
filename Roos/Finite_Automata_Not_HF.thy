theory Finite_Automata_Not_HF
  imports Main HereditarilyFinite.Ordinal "$AFP/Finite_Automata_HF/Finite_Automata_HF"
begin


text\<open>This file contains a version of the dfa and nfa definition from Finite_Automata_Hf 
but with \<open>'b set\<close> as states set, instead of forcing \<open>hf set\<close>. 
It is intended to be used for easier constructions of explicitly given languages,
not for abstract constructions such as the intersection of 2 automaton languages.
The locale below adds a converter from this dfa to the hf version dfa, to show that regularity also
holds for the language of this dfa.\<close>

section\<open>Deterministic Finite Automata\<close>

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



lemma embed_finite_set_into_hf:
  fixes B::\<open>'b set\<close>
  assumes \<open>finite B\<close>
  shows \<open>\<exists>(f:: 'b \<Rightarrow> hf).  inj_on f B  \<close>
proof-
  from \<open>finite B\<close> obtain f_inv1::\<open>nat \<Rightarrow> 'b\<close> and n::nat where \<open>B = f_inv1 ` {i. i < n} \<and> inj_on f_inv1 {i. i < n}\<close>  using finite_imp_nat_seg_image_inj_on by fastforce
  then obtain f1::\<open>'b \<Rightarrow> nat\<close> where \<open>(\<forall>x \<in> B. f_inv1 (f1 x) = x) \<and> (\<forall>x \<in> (f1 ` B). f1 (f_inv1 x) = x)\<close> by (metis (lifting) f_the_inv_into_f the_inv_into_f_f the_inv_into_onto)
  then have \<open>inj_on (ord_of o f1) B\<close> by (metis comp_inj_on inj_on_def inj_ord_of)
  then show ?thesis by blast
qed





locale construct_equiv_dfa = 
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

lemma f_f_inv[simp]: \<open>h \<in> dfa.states hf_M' \<Longrightarrow> f (f_inv h) = h\<close> by (metis dfa.select_convs(1) construct_equiv_dfa_axioms construct_equiv_dfa_def f_the_inv_into_f)
lemma f_in[intro]: \<open>q \<in> dfa'.states M' \<Longrightarrow> f q \<in> dfa.states hf_M'\<close> by simp
lemma f_in_final[intro]:\<open>q \<in> dfa'.final M' \<Longrightarrow> f q \<in> dfa.final hf_M'\<close> by simp
lemma f_f__inv_init[simp]: \<open>f( f_inv( dfa.init hf_M' ) ) = dfa.init hf_M'\<close> by (simp add: dfa'.init dfa'_M')

lemma f_inv_f[simp]: \<open>q \<in> dfa'.states M' \<Longrightarrow> f_inv (f q) = q\<close> by (meson construct_equiv_dfa_axioms construct_equiv_dfa_def the_inv_into_f_f)
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

  with embed_finite_set_into_hf[of \<open>dfa'.states M'\<close>] obtain f::\<open>'b \<Rightarrow> hf\<close> where inj_on: \<open>inj_on f (dfa'.states M')\<close> by blast

  then interpret construct_equiv_dfa: construct_equiv_dfa M' f apply unfold_locales by blast

  have \<open>M'.language = dfa.language local.construct_equiv_dfa.hf_M'\<close> using construct_equiv_dfa.M'_lang_eq_hf_M'_lang by blast
  moreover have \<open>dfa local.construct_equiv_dfa.hf_M'\<close> using local.construct_equiv_dfa.dfa_hf_M' by blast

  ultimately show ?thesis by blast
qed

text\<open>Now we have the result, that our dfas also produce regular languages.\<close>
corollary dfa'_imp_regular:
  fixes M' :: \<open>('a, 'b) dfa'\<close>
  assumes dfa'_M': \<open>dfa' M'\<close> "dfa'.language M' = L"
  shows \<open>regular L\<close> using ex_hf_M using dfa'_M'(1,2) regular_def by fastforce






































section\<open>Non-Deterministic Finite Automata\<close>

text\<open>These NFAs may include epsilon-transitions and multiple start states.\<close>

subsection\<open>Basic Definitions\<close>

record ('a, 'b) nfa' = states :: "'b set"
                init   :: "'b set"
                final  :: "'b set"
                nxt    :: "'b \<Rightarrow> 'a \<Rightarrow> 'b set"
                eps    :: "('b * 'b) set"

locale nfa' =
  fixes M :: "('a, 'b) nfa'"
  assumes init: "init M \<subseteq> states M"
      and final: "final M \<subseteq> states M"
      and nxt:   "\<And>q x. q \<in> states M \<Longrightarrow> nxt M q x \<subseteq> states M"
      and finite: "finite (states M)"
begin

lemma subset_states_finite [intro,simp]: "Q \<subseteq> states M \<Longrightarrow> finite Q"
  by (simp add: finite_subset finite)

definition epsclo :: "'b set \<Rightarrow> 'b set" where
  "epsclo Q \<equiv> states M \<inter> (\<Union>q\<in>Q. {q'. (q,q') \<in> (eps M)\<^sup>*})"

lemma epsclo_eq_Image: "epsclo Q = states M \<inter> (eps M)\<^sup>* `` Q"
  by (auto simp: epsclo_def)

lemma epsclo_empty [simp]: "epsclo {} = {}"
  by (auto simp: epsclo_def)

lemma epsclo_idem [simp]: "epsclo (epsclo Q) = epsclo Q"
  by (auto simp: epsclo_def)

lemma epsclo_increasing: "Q \<inter> states M \<subseteq> epsclo Q"
  by (auto simp: epsclo_def)

lemma epsclo_Un [simp]: "epsclo (Q1 \<union> Q2) = epsclo Q1 \<union> epsclo Q2"
  by (auto simp: epsclo_def)

lemma epsclo_UN [simp]: "epsclo (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. epsclo (B x))"
  by (auto simp: epsclo_def)

lemma epsclo_subset [simp]: "epsclo Q \<subseteq> states M"
  by (auto simp: epsclo_def)

lemma epsclo_trivial [simp]: "eps M \<subseteq> Q \<times> Q \<Longrightarrow> epsclo Q = states M \<inter> Q"
  by (auto simp: epsclo_def elim: rtranclE)

lemma epsclo_mono: "Q' \<subseteq> Q \<Longrightarrow> epsclo Q' \<subseteq> epsclo Q"
  by (auto simp: epsclo_def)

lemma finite_epsclo [simp]: "finite (epsclo Q)"
  using epsclo_subset finite_subset finite by blast

lemma finite_final: "finite (final M)"
  using final finite_subset finite by blast

lemma finite_nxt: "q \<in> states M \<Longrightarrow> finite (nxt M q x)"
  by (metis finite_subset finite nxt)

text\<open>Transition function for a given starting state and word.\<close>
primrec nextl :: "['b set, 'a list] \<Rightarrow> 'b set" where
    "nextl Q []     = epsclo Q"
  | "nextl Q (x#xs) = nextl (\<Union>q \<in> epsclo Q. nxt M q x) xs"

definition language :: "'a list set"  where
  "language \<equiv> {xs. nextl (init M) xs \<inter> final M \<noteq> {}}"

text\<open>The right language WRT a state q is the set of words that go from q to F.\<close>
definition right_lang :: "'b \<Rightarrow> 'a list set"  where
  "right_lang q \<equiv> {u. nextl {q} u \<inter> final M \<noteq> {}}"

lemma nextl_epsclo [simp]: "nextl (epsclo Q) xs = nextl Q xs"
  by (induct xs) auto

lemma epsclo_nextl [simp]: "epsclo (nextl Q xs) = nextl Q xs"
  by (induct xs arbitrary: Q) auto

lemma nextl_app: "nextl Q (xs@ys) = nextl (nextl Q xs) ys"
  by (induct xs arbitrary: Q) auto

lemma nextl_snoc [simp]: "nextl Q (xs@[x]) = (\<Union>q \<in> nextl Q xs. epsclo (nxt M q x))"
  by (simp add: nextl_app)

lemma nextl_state: "nextl Q xs \<subseteq> states M"
  by (induct xs arbitrary: Q) auto

lemma nextl_mono: "Q' \<subseteq> Q \<Longrightarrow> nextl Q' u \<subseteq> nextl Q u"
  by (induct u rule: rev_induct) (auto simp: epsclo_mono)

lemma nextl_eps: "q \<in> nextl Q u \<Longrightarrow> (q,q') \<in> eps M \<Longrightarrow> q' \<in> states M \<Longrightarrow> q' \<in> nextl Q u"
  using rtrancl_into_rtrancl epsclo_nextl epsclo_eq_Image by fastforce

lemma finite_nextl: "finite (nextl Q u)"
  by (induct u rule: List.rev_induct) auto

lemma nextl_empty [simp]: "nextl {} xs = {}"
  by (induct xs) auto

lemma nextl_Un: "nextl (Q1 \<union> Q2) xs = nextl Q1 xs \<union> nextl Q2 xs"
  by (induct xs arbitrary: Q1 Q2) auto

lemma nextl_UN: "nextl (\<Union>i\<in>I. f i) xs = (\<Union>i\<in>I. nextl (f i) xs)"
  by (induct xs arbitrary: f) auto

subsection\<open>The Powerset Construction\<close>

definition Power_dfa' :: "('a, 'b set) dfa'" where
  "Power_dfa' = \<lparr>dfa'.states = {(epsclo q) | q. q \<in> Pow (states M)},
                     init  = (epsclo (init M)),
                     final = {(epsclo Q) | Q. Q \<subseteq> states M \<and> Q \<inter> final M \<noteq> {}},
                     nxt   = \<lambda>Q x. (\<Union>q \<in> epsclo Q. epsclo (nxt M q x))\<rparr>"

lemma states_Power_dfa' [simp]: "dfa'.states Power_dfa' = epsclo ` Pow (states M)"
  by (auto simp add: Power_dfa'_def)

lemma init_Power_dfa' [simp]: "dfa'.init Power_dfa' = (epsclo (nfa'.init M))"
  by (simp add: Power_dfa'_def)

lemma final_Power_dfa [simp]: "dfa'.final Power_dfa' = {(epsclo Q) | Q. Q \<subseteq> states M \<and> Q \<inter> final M \<noteq> {}}"
  by (simp add: Power_dfa'_def)

lemma nxt_Power_dfa [simp]: "dfa'.nxt Power_dfa' = (\<lambda>Q x. (\<Union>q \<in> epsclo Q. epsclo (nxt M q x)))"
  by (simp add: Power_dfa'_def)

interpretation Power: dfa' Power_dfa'
proof unfold_locales
  show "dfa'.init Power_dfa' \<in> dfa'.states Power_dfa'"
    by (force simp add: init)
next
  show "dfa'.final Power_dfa' \<subseteq> dfa'.states Power_dfa'"
    by auto
next
  fix q a
  show "q \<in> dfa'.states Power_dfa' \<Longrightarrow> dfa'.nxt Power_dfa' q a \<in> dfa'.states Power_dfa'"
    apply (auto simp: nxt)
    by (smt (verit, ccfv_SIG) Pow_iff Sup.SUP_cong epsclo_UN epsclo_subset image_iff nfa'.epsclo_idem nfa'_axioms)
next
  show "finite (dfa'.states Power_dfa')"
    by (force simp: finite)
qed

corollary dfa_Power: "dfa' Power_dfa'"
  by unfold_locales

lemma nextl_Power_dfa':
     "qs \<in> dfa'.states Power_dfa'
     \<Longrightarrow> dfa'.nextl Power_dfa' qs u = (\<Union>q \<in> qs. nextl {q} u)"
  apply (induct u rule: List.rev_induct)
  apply (auto simp: finite_nextl inj_on_HF [THEN inj_on_eq_iff])
  apply (metis Int_empty_left Int_insert_left_if1 epsclo_increasing epsclo_subset subsetD singletonI)
  apply (metis contra_subsetD empty_subsetI epsclo_idem epsclo_mono insert_subset)
  done

text\<open>Part of Prop 4 of Jean-Marc Champarnaud, A. Khorsi and T. Paranthoën (2002)\<close>
lemma Power_right_lang:
     "qs \<in> dfa'.states Power_dfa' \<Longrightarrow> Power.right_lang qs = (\<Union>q \<in> qs. right_lang q)"
using epsclo_increasing
apply (auto simp: Power.right_lang_def right_lang_def nextl_Power_dfa'
                  inj_on_HF [THEN inj_on_eq_iff] finite_nextl, blast)
apply (rename_tac Q u q1 q2)
apply (drule_tac x="(\<Union>x\<in>epsclo Q. nextl {x} u)" in spec)
apply auto
using nextl_state apply blast
done


text\<open>The Power DFA accepts the same language as the NFA.\<close>
theorem Power_language [simp]: "Power.language = language"
proof -
  { fix u
    have "(Power.nextl (dfa'.init Power_dfa') u) = (nextl (init M) u)"
    proof (induct u rule: List.rev_induct)
      case Nil show ?case
        using Power.nextl.simps
        by (auto simp: hinsert_def)
    next
      case (snoc x u) then show ?case
        by (simp add: init finite_nextl nextl_state [THEN subsetD])
    qed
    then have "u \<in> Power.language \<longleftrightarrow> u \<in> language"
      apply (auto simp add: Power.language_def language_def disjoint_iff_not_equal)
      apply (metis Int_iff finite_nextl hfset_HF nextl.simps(1) epsclo_increasing subsetCE)
      apply (metis epsclo_nextl nextl_state)
      done
  }
  then show ?thesis
    by blast
qed

text\<open>Every language accepted by a NFA is also accepted by a DFA.\<close>
corollary imp_regular: "regular language"
  using Power_language dfa_Power regular_def using dfa'_imp_regular by blast

end

text\<open>As above, outside the locale\<close>
corollary nfa'_imp_regular:
  assumes "nfa' M" "nfa'.language M = L"
    shows "regular L"
using assms nfa'.imp_regular by blast











end
