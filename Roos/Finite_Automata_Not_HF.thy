(* Author: Moritz Roos *)

theory Finite_Automata_Not_HF
  imports Finite_Automata_HF.Finite_Automata_HF
begin


text\<open>This file contains a version of the dfa and nfa definition from 
Lawrence C. Paulson's \<open>Finite_Automata_Hf\<close> but with \<open>'b set\<close> as states set, 
instead of forcing \<open>hf set\<close>. 
It is intended to be used for easier constructions of explicitly given languages,
not for abstract constructions such as the intersection of 2 automaton languages.
The locale below adds a converter from this dfa/nfa to the hf version dfa/nfa, 
to show that regularity also holds for the language of this dfa/nfa.\<close>

lemma embed_finite_set_into_hf:
  fixes B::\<open>'b set\<close>
  assumes \<open>finite B\<close>
  shows \<open>\<exists>(f:: 'b \<Rightarrow> hf).  inj_on f B  \<close>
by (meson assms comp_inj_on finite_imp_inj_to_nat_seg inj_ord_of)

section\<open>Deterministic Finite Automata\<close>

text\<open>First, the record for DFAs\<close>
record ('a, 'b) dfa' =
  states :: "'b set"
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

lemma nextl_app: "nextl q (xs@ys) = nextl (nextl q xs) ys"
  by (induct xs arbitrary: q) auto

lemma nextl_snoc [simp]: "nextl q (xs@[x]) = nxt M (nextl q xs) x"
  by (simp add: nextl_app)

lemma nextl_state: "q \<in> states M \<Longrightarrow> nextl q xs \<in> states M"
  by (induct xs arbitrary: q) (auto simp: nxt)

lemma nextl_init_state [simp]: "nextl (init M) xs \<in> states M"
  by (simp add: nextl_state)

definition f :: "'b \<Rightarrow> hf" where
"f = (SOME f. inj_on f (states M))"

lemma f_inj_on: "inj_on f (states M)"
unfolding f_def using embed_finite_set_into_hf[OF finite]
by (metis someI_ex)

abbreviation f_inv :: "hf \<Rightarrow> 'b" where 
  \<open>f_inv \<equiv> the_inv_into (states M) f\<close>

abbreviation f_M :: "'a dfa" where
  \<open>f_M \<equiv>  \<lparr>dfa.states = f ` (states M),
            init  = f (init M),
            final = f ` (final M),
            nxt   = \<lambda>q x. f( nxt M (f_inv q) x) \<rparr>\<close>

lemma f_f_inv[simp]: \<open>h \<in> dfa.states f_M \<Longrightarrow> f (f_inv h) = h\<close>
  by (simp add: f_inj_on f_the_inv_into_f)

lemma f_in[intro]: \<open>q \<in> dfa'.states M \<Longrightarrow> f q \<in> dfa.states f_M\<close> 
  by simp

lemma f_in_final[intro]:\<open>q \<in> dfa'.final M \<Longrightarrow> f q \<in> dfa.final f_M\<close> 
  by simp

lemma f_f__inv_init[simp]: \<open>f( f_inv( dfa.init f_M) ) = dfa.init f_M\<close> 
  by (simp add: dfa'.init)

lemma f_inv_f[simp]: \<open>q \<in> dfa'.states M \<Longrightarrow> f_inv (f q) = q\<close> 
  by (meson f_inj_on the_inv_into_f_f)

lemma f_inv_in[intro]: \<open>h \<in> dfa.states f_M \<Longrightarrow> f_inv h \<in> dfa'.states M\<close> 
  by fastforce

lemma f_inv_in_final[intro]: \<open>h \<in> dfa.final f_M \<Longrightarrow> f_inv h \<in> dfa'.final M\<close>
  using final by auto 

lemma f_inv_f_init[simp]: \<open>f_inv( f( dfa'.init M) ) = dfa'.init M\<close> 
  by (simp add: dfa'.init)


interpretation f_M: dfa f_M
proof(standard, goal_cases)
  case 1
  then show ?case using dfa'.init by auto
next
  case 2
  then show ?case by (simp add: final image_mono)
next
  case (3 q x)
  then show ?case by (simp add: nxt f_inv_in)
next
  case 4
  then show ?case by (simp add: finite)
qed


lemma nxt_M_f_inv: \<open>h \<in> dfa.states f_M \<Longrightarrow> dfa'.nxt M (f_inv h) x = f_inv (dfa.nxt f_M h x)\<close> 
  by (simp add: nxt f_inv_in)

lemma nxt_f_M_f:\<open>q \<in> dfa'.states M \<Longrightarrow> dfa.nxt f_M (f q) x = f (dfa'.nxt M q x)\<close> 
  by auto

lemma nextl_M_f_inv: \<open>h \<in> dfa.states f_M \<Longrightarrow> nextl  (f_inv h) xs = f_inv (f_M.nextl h xs)\<close>
proof(induction xs arbitrary: h)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have \<open>nextl (dfa'.nxt M (f_inv h) a) xs = f_inv (f_M.nextl (f (dfa'.nxt M (f_inv h) a)) xs)\<close> 
    using f_f_inv f_M.nxt nxt_M_f_inv by presburger
  then show ?case by simp
qed 

lemma nextl_f_M_f: \<open>q \<in> dfa'.states M \<Longrightarrow> f_M.nextl (f q) xs = f (nextl q xs)\<close>
proof(induction xs arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then have \<open>f_M.nextl (f (dfa'.nxt M q a)) xs = f (nextl (dfa'.nxt M q a) xs)\<close> 
    using nxt by blast
  then show ?case by (simp add: Cons.prems)
qed 


lemma M'_lang_eq_f_M'_lang: \<open>language = f_M.language\<close>
  unfolding language_def f_M.language_def
  by (metis dfa.select_convs(2) f_M.init f_in_final f_inv_f_init f_inv_in_final init nextl_M_f_inv
      nextl_f_M_f)

corollary ex_hf_M:
  \<open>\<exists>f_M. dfa f_M \<and> dfa'.language M = dfa.language f_M\<close>
using M'_lang_eq_f_M'_lang f_M.dfa_axioms by blast

text\<open>Now we have the result, that our dfas also produce regular languages.\<close>
corollary dfa'_imp_regular:
  assumes "dfa'.language M = L"
  shows \<open>regular L\<close> 
  using ex_hf_M assms unfolding regular_def by blast

end

section\<open>Non-Deterministic Finite Automata\<close>
(* Currently unused *)

text\<open>These NFAs may include epsilon-transitions and multiple start states.\<close>

subsection\<open>Basic Definitions\<close>

record ('a, 'b) nfa' =
  states :: "'b set"
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
    then have "u \<in> Power.language \<longleftrightarrow> u \<in> language" using epsclo_increasing nextl_state
      by (fastforce simp add: Power.language_def language_def disjoint_iff_not_equal)
  }
  then show ?thesis
    by blast
qed

text\<open>Every language accepted by a NFA is also accepted by a DFA.\<close>
corollary imp_regular: "regular language"
  using Power_language dfa_Power regular_def using Power.dfa'_imp_regular by blast

end

text\<open>As above, outside the locale\<close>
corollary nfa'_imp_regular:
  assumes "nfa' M" "nfa'.language M = L"
  shows "regular L"
  using assms nfa'.imp_regular by blast

end
