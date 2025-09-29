chapter ‹Alternating Finite Automata using the Hereditarily Finite Sets› 

theory Alternating_Finite_Automata_HF
  imports Main Finite_Automata_HF.Finite_Automata_HF 
begin

text‹This theory formalizes alternating finite automata (AFA) based on hereditarily
finite sets. The main result is that every AFA can be converted into an NFA.
Our formalization is based on positive boolean formulas rather than functions,
following the textbook Automatentheory und Logik by Hofmann and Lange.

The theory starts with positive boolean formulas (type ‹'a and_or_exp›). The
main body of the theory is concerned with AFAs and their translation to NFAs.›

section‹Positive Boolean formulas and the related modeling relation›
datatype 'a and_or_exp =
  Var 'a 
  | And "'a and_or_exp" "'a and_or_exp" 
  | Or "'a and_or_exp" "'a and_or_exp" 
  | MT

inductive models :: "hf set ⇒ hf and_or_exp ⇒ bool" where
  "q ∈ Q ⟹ models Q (Var q)"
| "models Q q1 ∨ models Q q2 ⟹ models Q (Or q1 q2)"
| "models Q q1 ∧ models Q q2 ⟹ models Q (And q1 q2)"

subsection‹Some lemmas about models›
lemma anding1 : "models qs a ⟹ models qs b ⟹ models qs (And a b)"
  using models.intros(3) by blast

lemma anding2 : "models qs (And a b) ⟹ models qs a"
  using models.cases by fastforce

lemma anding3 : "models qs (And a b) ⟹ models qs b"
  using models.cases by fastforce

lemma modelinc: "models qs a ⟹ qs ⊆ qs' ⟹ models qs' a"
proof (induction rule: models.induct)
  case (1 q Q)
  then show ?case using models.intros by auto
next
  case (2 Q q1 q2)
  then show ?case using models.intros by auto
next
  case (3 Q q1 q2)
  then show ?case using models.intros by auto
qed

lemma mod_has: "models qs a ⟹ qs ≠ {}"
proof (induction rule: models.induct)
  case (1 q Q)
  then show ?case by auto
next
  case (2 Q q1 q2)
  then show ?case by auto
next
  case (3 Q q1 q2)
  then show ?case by auto
qed
  

lemma mod_has': "∄ab. models {} ab"
  using mod_has by blast

text‹Returns set of variables used in the given and or expression›
fun elems :: "'a and_or_exp ⇒ 'a set" where
  "elems MT = {}"
| "elems (Var a) = {a}"
| "elems (And q1 q2) = ((elems q1) ∪ (elems q2))"
| "elems (Or q1 q2) = ((elems q1) ∪ (elems q2))"


section‹hf lemmas›
lemma althf: "HF ` (hfset ` X) = X"
  using image_iff by fastforce

lemma chainhf: "∀x∈q. finite x ⟹ hfset ` HF ` q = q"
  by force


section‹Alternating Finite Automata›

record 'a afa = states :: "hf set"
                init   :: "hf"
                final  :: "hf set"
                nxt    :: "hf ⇒ 'a ⇒ hf and_or_exp"
locale afa =
fixes M :: "'a afa"
  assumes init: "init M ∈ states M"
      and final: "final M ⊆ states M"
      and nxt:   "⋀q x. q ∈ states M ⟹ elems (nxt M q x) ⊆ states M"
      and finite: "finite (states M)"
begin

text‹Returns whether starting from a node, a (rest)word is accepted›
fun A :: "'a list ⇒ hf ⇒ bool" where
  "A [] q = (q ∈ final M)"
| "A (a#w) q = ((q ∈ states M) ∧ (models {q' ∈ states M. A w q'} (nxt M q a)))"

text‹The language of the afa›
definition lang :: "'a list set" where
  "lang ≡ {as. A as (init M)}"

text‹Verifies that a set of states are a valid set of children for a given node and character›
text‹It also verifies whether the given nodes are valid›
fun valid_children :: "hf ⇒ hf set ⇒ 'a ⇒ bool" where
  "valid_children q qs a = ((qs ⊆ states M) ∧ (q ∈ states M) ∧ (models qs (nxt M q a)))"


text‹Equivalent to A (Returns whether a respective accepting tree exists)›
text‹It takes a layer wise recursive approach on the tree, 
  verifying the existence of a valid set of children which can each be root to an accepting tree for the rest word›
fun acc_i :: "'a list ⇒ hf ⇒ bool" where
  "acc_i [] q = (q ∈ final M)"
| "acc_i (a#as) q = (∃qs. (valid_children q qs a) ∧ (∀q' ∈ qs. acc_i as q'))"


text‹Equivalence of acc_i and A›
lemma acc_i_A_eq: "acc_i as q = A as q"
proof (induction rule: acc_i.induct)
  case (1 q)
  then show ?case by simp
next
  case (2 a as q)
  then show ?case proof (cases "acc_i (a#as) q")
    case t1: True
    have h1: "(∃qs. (valid_children q qs a) ∧ (∀q' ∈ qs. acc_i as q'))"
      using t1 by force
    then obtain qs where o1: "(valid_children q qs a) ∧ (∀q' ∈ qs. acc_i as q')" by auto
    then have h2: "(∀q' ∈ qs. A as q')"
      using "2" by blast
    then have h3: "qs ⊆ {q' ∈ states M. A as q'}"
      using o1 by auto
    then have h4: "models {q' ∈ states M. A as q'} (nxt M q a)"
      using modelinc o1 valid_children.simps by blast
    then show ?thesis
      using t1 by auto
  next
    case f1: False
    then show ?thesis proof (cases "A (a#as) q")
      case True
      then have h11: "(valid_children q {q' ∈ states M. A as q'} a) ∧ (∀q' ∈ {q' ∈ states M. A as q'}. acc_i as q')"
        using "2" by auto
      then show ?thesis
        using acc_i.simps(2) f1 by blast
    next
      case False
      then show ?thesis
        using f1 by blast
    qed 
  qed
   
qed



text‹Returns the conjunction of all (nxt M x a) for all xs in a list›
fun anded :: "hf list ⇒ 'a ⇒ hf and_or_exp" where
  "anded [] a = MT"
| "anded [x] a = nxt M x a"
| "anded (x#xs) a = And (nxt M x a) (anded xs a)"

subsection‹An equivalency about anded›
lemma andingeq1: "(∀q ∈ set (p#qs). models qs' (nxt M q a)) ⟹ models qs' (anded (p#qs) a)"
proof (induction qs)
  case Nil
  then show ?case by simp
next
  case (Cons a qs)
  then show ?case by (metis anded.elims anding1 anding3 list.discI list.inject
      list.set_intros(1,2) set_ConsD)
qed
  

lemma andingeq2: "models qs' (anded (p#qs) a) ⟹ (∀q ∈ set (p#qs). models qs' (nxt M q a))"
proof (induction qs)
  case Nil
  then show ?case by simp
next
  case (Cons a qs)
  then show ?case
    by (metis anded.simps(2,3) anding2 anding3 list.set_intros(2) models.intros(3) neq_Nil_conv
        set_ConsD)
qed 

text‹Verifies whether a set of states (qs') is a valid next level for another set of states (qs)›
text‹It is used to define an equivalent language(langalt) to lang›
fun nxt_lvl_set_valid :: "hf set ⇒ hf set ⇒ 'a ⇒ bool" where
  "nxt_lvl_set_valid qs qs' a = ((qs ≠ {}) ∧ (qs ⊆ states M) ∧ (qs' ⊆ states M) ∧ (∃qsl. ((set qsl = qs) ∧ (distinct qsl) ∧ models qs' (anded qsl a))))"


text‹Verifies whether a (rest)word will be accepted from a given level using nxt_lvl_set_valid›
fun acc_i_set :: "'a list ⇒ hf set ⇒ bool" where
   "acc_i_set [] qs = (qs ⊆ (final M))"
|  "acc_i_set (a#as) qs = (∃qs'. (nxt_lvl_set_valid qs qs' a) ∧ (acc_i_set as qs'))"


text‹An equivalent function to nxt_lvl_set_valid helping to prove equivalence of langalt (defined later) and lang›
fun nxt_lvl_set_valid' :: "hf set ⇒ hf set ⇒ 'a ⇒ bool" where
  "nxt_lvl_set_valid' qs qs' a = ((qs ≠ {}) ∧ (qs ⊆ states M) ∧ (qs' ⊆ states M) ∧ (∀q ∈ qs. models qs' (nxt M q a)))"


text‹Like acc_i_set but using nxt_lvl_set_valid' instead of nxt_lvl_set_valid›
fun acc_i_set' :: "'a list ⇒ hf set ⇒ bool" where
   "acc_i_set' [] qs = (qs ⊆ (final M))"
|  "acc_i_set' (a#as) qs = (∃qs'. (nxt_lvl_set_valid' qs qs' a) ∧ (acc_i_set' as qs'))"


subsection‹Equivalence of nxt_lvl_set_valid and nxt_lvl_set_valid'›
lemma eq_nlsv1: "nxt_lvl_set_valid qs qs' a ⟹ nxt_lvl_set_valid' qs qs' a"
proof -
  assume A: "nxt_lvl_set_valid qs qs' a"
  have h1: "⋀xqs xqs' xa. (finite xqs ⟹ xqs ≠ {} ⟹ (∃qsl. ((set qsl = xqs) ∧ (distinct qsl) ∧ models xqs' (anded qsl xa))) ⟹ (∀q ∈ xqs. models xqs' (nxt M q xa)))"
    by (metis andingeq2 empty_set remdups_adj.cases)
  show ?thesis using A h1 by auto
qed


lemma eq_nlsv2: "nxt_lvl_set_valid' qs qs' a ⟹ nxt_lvl_set_valid qs qs' a"
  by (metis anded.elims andingeq1 finite_distinct_list finite_subset
      local.finite nxt_lvl_set_valid'.elims(1) nxt_lvl_set_valid.elims(1)
      set_empty)

subsection‹Equivalence of acc_i_set and acc_i_set'›
lemma eq_ais1: "acc_i_set as q ⟹ acc_i_set' as q"
proof (induction rule: acc_i_set.induct)
  case (1 qs)
  then show ?case by simp
next
  case (2 a as qs)
  then show ?case using acc_i_set'.simps(2) acc_i_set.simps(2) eq_nlsv1 by blast
qed
  

lemma eq_ais2: "acc_i_set' as q ⟹ acc_i_set as q"
proof (induction rule: acc_i_set'.induct)
  case (1 qs)
  then show ?case by simp
next
  case (2 a as qs)
  then show ?case using acc_i_set'.simps(2) acc_i_set.simps(2) eq_nlsv2 by blast
qed
  


subsection‹Relations between acc_i and acc_i_set'›
lemma aiais1: "qs ≠ {} ⟹ (∀q ∈ qs. acc_i as q) ⟹ acc_i_set' as qs"
proof -
  assume A: "qs ≠ {}" and B: "(∀q ∈ qs. acc_i as q)"
  show ?thesis using A B proof (induction rule: acc_i_set'.induct)
    case (1 qs)
    then show ?case by auto
  next
    case (2 a as qs)
    then have h3: "∀q ∈ qs. ∃xqs. ((valid_children q xqs a) ∧ (∀q' ∈ xqs. acc_i as q'))"
      using B by simp
    let ?xs = "{q'∈(states M). acc_i as q'}"
    have inc_vc: "⋀xqs xqs' xq xa. (xqs ⊆ xqs' ⟹ xqs' ⊆ states M ⟹ valid_children xq xqs xa ⟹ valid_children xq xqs' xa)"
      by (meson modelinc valid_children.elims(2,3))
    have h4: "∀q ∈ qs. (valid_children q ?xs a)"
    proof (intro ballI)
      fix q
      assume "q ∈ qs"
      then have H1: "∃xqs. ((valid_children q xqs a) ∧ (∀q' ∈ xqs. acc_i as q'))" using h3 by simp
      then obtain xqs where O1: "((valid_children q xqs a) ∧ (∀q' ∈ xqs. acc_i as q'))" by blast
      then have H2: "xqs ⊆ ?xs" by auto
      show "(valid_children q ?xs a)"
        using H2 O1 inc_vc by blast
    qed

    have hr: "nxt_lvl_set_valid' qs ?xs a"
      using "2.prems"(1) h4 by force

    then have "?xs ≠ {}"
      using mod_has by fastforce
    then have "acc_i_set' as ?xs"
      using "2.IH" by force
    then show ?case
      using acc_i_set'.simps(2) hr by blast
  qed
qed
  
lemma aiais2: "acc_i_set' as qs ⟹ (∀q ∈ qs. acc_i as q)"
proof (induction rule: acc_i_set'.induct)
  case (1 qs)
  then show ?case by fastforce
next
  case (2 a as qs)
  then show ?case by fastforce
qed



text‹Returns possible options for the next level given the possible options for some level of the tree›
fun nxt_lvl_set_opt_ext :: "hf set set ⇒ 'a ⇒ hf set set" where
  "nxt_lvl_set_opt_ext qss a = {qs'. ∃qs∈qss. nxt_lvl_set_valid qs qs' a}"

subsection‹Some lemmas about nxt_lvl_set_opt_ext›
lemma no_mt: "{} ∉ (nxt_lvl_set_opt_ext qss a)"
  using mod_has' by fastforce

lemma cond_fin: "finite qs ⟹ finite (nxt_lvl_set_opt_ext qs a)"
  using local.finite by auto

lemma elemfin': "∀y∈(nxt_lvl_set_opt_ext qs a). finite y"
  using local.finite rev_finite_subset by auto

lemma elemfin: "x ∈ (nxt_lvl_set_opt_ext qss a) ⟹ finite x"
  using elemfin' by blast


text‹Set of all possible leaf sets for a valid run›
definition acc_set :: "hf set set" where
  "acc_set ≡ {Q. Q ⊆ final M}"

text‹An equivalent to acc_i_set using nxt_lvl_set_opt_ext and acc_set›
fun acc_i_set_sim :: "'a list ⇒ hf set ⇒ bool" where
   "acc_i_set_sim [] qs = (qs ∈ acc_set)"
|  "acc_i_set_sim (a#as) qs = (∃qs' ∈ (nxt_lvl_set_opt_ext {qs} a). (acc_i_set_sim as qs'))"

subsection‹Equivalence of acc_i_set_sim and acc_i_set›
lemma aiss_eq1: "acc_i_set_sim as qs ⟹ acc_i_set as qs"
proof (induction rule: acc_i_set_sim.induct)
  case (1 qs)
  then show ?case by (simp add: acc_set_def)
next
  case (2 a as qs)
  have h1: "(∃qs' ∈ (nxt_lvl_set_opt_ext {qs} a). (acc_i_set_sim as qs'))"
    using "2.prems" acc_i_set_sim.simps(2) by blast
  then obtain qs' where o1: "qs' ∈ (nxt_lvl_set_opt_ext {qs} a) ∧ (acc_i_set_sim as qs')" by blast
  then show ?case using 2(1)[of qs'] by auto
qed

lemma aiss_eq2: "acc_i_set as qs ⟹ acc_i_set_sim as qs"
proof (induction rule: acc_i_set.induct)
  case (1 qs)
  then show ?case by (simp add: afa.acc_set_def afa_axioms)
next
  case (2 a as qs)
  then show ?case by auto
qed


text‹Returns possible options for the level reached after processing a word from given options for starting level›
fun nxt_lvl_set_opt_ext_l :: "hf set set ⇒ 'a list ⇒ hf set set" where
  "nxt_lvl_set_opt_ext_l qss [] = qss"  
| "nxt_lvl_set_opt_ext_l qss (a#as) = nxt_lvl_set_opt_ext_l (nxt_lvl_set_opt_ext qss a) as"


text‹Helper lemma about nxt_lvl_set_opt_ext_l›
lemma elem_fin: "x ∈ nxt_lvl_set_opt_ext_l qs xs ⟹ (∀y∈qs. finite y) ⟹ finite x"
proof (induction rule: nxt_lvl_set_opt_ext_l.induct)
  case (1 qss)
  then show ?case by simp
next
  case (2 qss a as)
  then show ?case by (metis elemfin nxt_lvl_set_opt_ext_l.simps(2))
qed
  
subsection‹Relations between nxt_lvl_set_opt_ext_l and acc_i_set_sim or acc_i_set›

lemma helper1: "∃x ∈ (nxt_lvl_set_opt_ext_l qss as). (x ∈ acc_set) ⟹ ∃qs ∈ qss. acc_i_set_sim as qs"
proof (induction rule: nxt_lvl_set_opt_ext_l.induct)
  case (1 qss)
  then show ?case by simp
next
  case (2 qss a as)
  then have H1: "∃qs'∈nxt_lvl_set_opt_ext qss a. acc_i_set_sim as qs'" by simp
  then obtain qs' where O1: "qs'∈nxt_lvl_set_opt_ext qss a ∧ acc_i_set_sim as qs'" by blast
  then have H2: "∃qs∈qss. nxt_lvl_set_valid qs qs' a" by simp
  then obtain qs where O2: "qs∈qss ∧ nxt_lvl_set_valid qs qs' a" by blast
  have H3: "qs'∈nxt_lvl_set_opt_ext {qs} a"
    using O2 by auto 
  show ?case using H3 O1 O2 acc_i_set_sim.simps(2) by blast
qed


lemma helper2: "qs ∈ qss ⟹ acc_i_set_sim as qs ⟹ ∃x ∈ (nxt_lvl_set_opt_ext_l qss as). (x ∈ acc_set)"
proof (induction arbitrary: qss rule: acc_i_set_sim.induct)
  case (1 qs)
  then show ?case by fastforce
next
  case (2 a as qs)
  have h1: "(∃qs' ∈ (nxt_lvl_set_opt_ext {qs} a). (acc_i_set_sim as qs'))"
    using "2.prems"(2) acc_i_set_sim.simps(2) by blast
  then obtain qs' where o1: "(qs' ∈ (nxt_lvl_set_opt_ext {qs} a) ∧ (acc_i_set_sim as qs'))" by blast
  then have h2: "qs' ∈ (nxt_lvl_set_opt_ext qss a)"
    using "2.prems"(1) by fastforce
  then show ?case 
    using 2(1)[of qs' "(nxt_lvl_set_opt_ext qss a)"] o1 h2 by simp 
qed

lemma langeq2_helper: "nxt_lvl_set_opt_ext_l {{afa.init M}} as ∩ acc_set ≠ {} ⟹ acc_i_set as {afa.init M}"
  using aiss_eq1 helper1 by blast

lemma langeq1_helper: "acc_i_set as {afa.init M} ⟹ nxt_lvl_set_opt_ext_l {{afa.init M}} as ∩ acc_set ≠ {}"
  by (simp add: aiss_eq2 helper2 disjoint_iff_not_equal)


text‹An equivalent definition for lang›
definition langalt :: "'a list set" where
  "langalt ≡ {as. (nxt_lvl_set_opt_ext_l {{init M}} as) ∩ (acc_set) ≠ {}}"


subsection‹Equivalence of lang and langalt›
lemma langeq1: "lang ⊆ langalt"
  unfolding lang_def langalt_def
  by (simp add: Collect_mono_iff aiais1 eq_ais2 langeq1_helper acc_i_A_eq)

lemma langeq2: "langalt ⊆ lang"
  unfolding lang_def langalt_def using langeq2_helper aiais2 eq_ais1 acc_i_A_eq by blast

subsection‹The Powerset Construction›

definition Power_nfa :: "'a nfa" where 
  "Power_nfa = ⦇nfa.states = {HF Q | Q. Q ∈ Pow (states M)},
                     init  = {HF {init M}},
                     final = {HF Q | Q. Q ⊆ final M},
                     nxt   = (λQ x. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset Q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))}),
                     eps = {}⦈"


interpretation Power: nfa Power_nfa
proof unfold_locales
  show "nfa.init Power_nfa ⊆ nfa.states Power_nfa"
    using Power_nfa_def init by auto
next 
  show "nfa.final Power_nfa ⊆ nfa.states Power_nfa"
    using Power_nfa_def final by force
next
  show "⋀q x. q ∈ nfa.states Power_nfa ⟹
           nfa.nxt Power_nfa q x ⊆ nfa.states Power_nfa"
    using Power_nfa_def by auto
next
  show "finite (nfa.states Power_nfa)"
    unfolding Power_nfa_def using finite by simp
qed

subsection‹Helper lemmas on Power_nfa›
lemma neps: "q ⊆ nfa.states Power_nfa ⟹ Power.epsclo q = q"
  using Power.epsclo_trivial Power_nfa_def by auto

lemma nfa_init: "(HF {}) ∉ (nfa.init Power_nfa)"
  using Power_nfa_def hmem_HF_iff by fastforce


text‹Works similar to Power.nextl, defined to help prove equivalence of Power.language and langalt›
fun lnextl' :: "hf set ⇒ 'a list ⇒ hf set" where
  "lnextl' Q []     = Q"
| "lnextl' Q (x#xs) = lnextl' (⋃q ∈ Q. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))}) xs"


text‹Relationship of lnextl' and Power.nextl›
lemma nextl_cond_eq: "q ⊆ nfa.states Power_nfa ⟹ lnextl' q as = Power.nextl q as"
proof (induction as arbitrary: q)
  case Nil
  then show ?case by (simp add: neps)
next
  case (Cons a as)
  have h1: "(⋃q∈q. {HF Q' |Q'.
                 Q' ⊆ afa.states M ∧
                 (∃Qsl. set Qsl = hfset q ∧
                        distinct Qsl ∧ models Q' (anded Qsl a))})
                = (⋃q∈q. nfa.nxt Power_nfa q a)" by (simp add: Power_nfa_def)
  have h2: "(⋃q∈Power.epsclo q. nfa.nxt Power_nfa q a) ⊆ nfa.states Power_nfa"
    using Cons.prems Power.nxt neps by auto
  have h3: "lnextl'
     (⋃q∈q. {HF Q' |Q'.
              Q' ⊆ afa.states M ∧
              (∃Qsl. set Qsl = hfset q ∧ distinct Qsl ∧ models Q' (anded Qsl a))})
     as =
    Power.nextl (⋃q∈Power.epsclo q. nfa.nxt Power_nfa q a) as"
    using h1 Cons.IH(1)[OF h2]
    by (simp add: Cons.prems afa.neps afa_axioms)
  show ?case using h3 by simp
qed


subsection‹Relationships between lnextl' and nxt_lvl_set_opt_ext_l›

text‹A helper lemma›
lemma cond_eq_helper: "(HF {}) ∉ Q ⟹ Q ⊆ (nfa.states Power_nfa) ⟹ hfset ` (⋃q ∈ Q. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})
    = nxt_lvl_set_opt_ext (hfset ` Q) x"
proof -
  assume X: "(HF {}) ∉ Q" and Y: "Q ⊆ (nfa.states Power_nfa)"
  have hpll1: "hfset ` (⋃q ∈ Q. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})
            =
              {qs'. ∃qs∈ (hfset ` Q). ((qs ≠ {}) ∧ (qs ⊆ states M) ∧ (qs' ⊆ states M) ∧ (∃qsl. ((set qsl = qs) ∧ (distinct qsl) ∧ models qs' (anded qsl x))))}"
  proof -
    have hpll16: "(⋃qs ∈ Q. {qs'. ((hfset qs ≠ {}) ∧ (hfset qs ⊆ states M) ∧ (qs' ⊆ states M) ∧ (∃qsl. ((set qsl = hfset qs) ∧ (distinct qsl) ∧ models qs' (anded qsl x))))})
      = (⋃qs ∈ Q. {qs'. ((qs' ⊆ states M) ∧ (∃qsl. ((set qsl = hfset qs) ∧ (distinct qsl) ∧ models qs' (anded qsl x))))})" 
      proof -
        have h1: "⋀qs. (qs ∈ Q ⟹ (hfset qs ≠ {}))" using X by (metis HF_hfset)
        have h2: "⋀qs. (qs ∈ Q ⟹ hfset qs ⊆ states M)"
          proof -
            fix qs
            show "(qs ∈ Q ⟹ hfset qs ⊆ states M)"
              proof -
                assume a2: "qs ∈ Q"
                show ?thesis
                  using Power_nfa_def Y a2 hfset_HF local.finite mem_Collect_eq nfa.select_convs(1)
                    rev_finite_subset by force
              qed
          qed
          show ?thesis using h1 h2 X Y by simp
      qed
      have hpll11: "hfset ` (⋃q ∈ Q. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})
                = (⋃q ∈ Q. hfset ` {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})"
        by auto
      have hpll12: "(⋃q ∈ Q. hfset ` {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})
                = (⋃q ∈ Q. {hfset (HF Q') | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})"
        by auto
      have hpll13: "(⋃q ∈ Q. {hfset (HF Q') | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})
                = (⋃q ∈ Q. {Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})"
        proof -
          have "⋀q. ({hfset (HF Q') | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))}
              = {Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl x))))})"
            by (metis finite_subset hfset_HF local.finite)
          then show ?thesis by simp
        qed
        have hpll14: "{qs'. ∃qs∈ (hfset ` Q). ((qs ≠ {}) ∧ (qs ⊆ states M) ∧ (qs' ⊆ states M) ∧ (∃qsl. ((set qsl = qs) ∧ (distinct qsl) ∧ models qs' (anded qsl x))))}
              =
              (⋃qs ∈ (hfset ` Q). {qs'. ((qs ≠ {}) ∧ (qs ⊆ states M) ∧ (qs' ⊆ states M) ∧ (∃qsl. ((set qsl = qs) ∧ (distinct qsl) ∧ models qs' (anded qsl x))))})"
          by blast
        show ?thesis using hpll16 hpll14 hpll13 hpll12 hpll11 X Y by auto
      qed
      show ?thesis using hpll1 X Y by simp
    qed

lemma cond_eq1: "(HF {}) ∉ qs ⟹ qs ⊆ nfa.states Power_nfa ⟹ x ∈ lnextl' qs as ⟹ hfset x ∈ (nxt_lvl_set_opt_ext_l (hfset ` qs) as)"
proof (induction as arbitrary: qs x)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case 
  proof -
    assume A: "(⋀qs x.
        HF {} ∉ qs ⟹
        qs ⊆ nfa.states Power_nfa ⟹
        x ∈ lnextl' qs as ⟹ hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` qs) as)"
      and B: "HF {} ∉ qs" and C: "qs ⊆ nfa.states Power_nfa" and D: "x ∈ lnextl' qs (a # as)"
    
    have h1: "HF {} ∉ HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)"
      using no_mt[of "(hfset ` qs)" a] elemfin' cond_fin
      by (metis Zero_hf_def chainhf hfset_0 image_eqI)
    have h21: "∀x∈(nxt_lvl_set_opt_ext (hfset ` qs) a). x ⊆ states M"
      by auto
    then have h2: "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)) ⊆ (nfa.states Power_nfa)"
      using Power_nfa_def by auto
    have h3: "HF {} ∉ HF ` nxt_lvl_set_opt_ext (hfset ` qs) a ⟹
  HF ` nxt_lvl_set_opt_ext (hfset ` qs) a ⊆ nfa.states Power_nfa ⟹
  x ∈ lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as ⟹
  hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using A[of "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a))" x] by blast
    have h4: "x ∈ (lnextl' (⋃q ∈ qs. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl a))))}) as)"
      using Cons.prems(3) lnextl'.simps(2) by blast
    have h5: "(HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) =
              (⋃q ∈ qs. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl a))))})"
      using cond_eq_helper[OF B C] althf
      by (metis (lifting)) 
    have h6: "x ∈ lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using h4 h5 by presburger
    show ?thesis using h3[OF h1 h2 h6]
      by (metis (no_types, lifting) B C cond_eq_helper althf nxt_lvl_set_opt_ext_l.simps(2))
  qed
qed


lemma cond_eq2: "(HF {}) ∉ qs ⟹ qs ⊆ nfa.states Power_nfa ⟹ hfset x ∈ (nxt_lvl_set_opt_ext_l (hfset ` qs) as) ⟹ x ∈ lnextl' qs as"
proof (induction as arbitrary: qs x)
  case Nil
  then show ?case
    using HF_hfset
    by (metis image_iff lnextl'.simps(1) nxt_lvl_set_opt_ext_l.simps(1))
next
  case (Cons a as)
  then show ?case
  proof -
    assume A: "(⋀qs x.
        HF {} ∉ qs ⟹
        qs ⊆ nfa.states Power_nfa ⟹
        hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` qs) as ⟹ x ∈ lnextl' qs as)" and
    B: "HF {} ∉ qs" and C: "qs ⊆ nfa.states Power_nfa" and D: "hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` qs) (a # as)"
    have h1: "HF {} ∉ HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)"
      using no_mt[of "(hfset ` qs)" a] elemfin' cond_fin 
      by (metis Zero_hf_def chainhf hfset_0 image_eqI)
    have h21: "∀x∈(nxt_lvl_set_opt_ext (hfset ` qs) a). x ⊆ states M"
      by auto
    then have h2: "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)) ⊆ (nfa.states Power_nfa)"
      using Power_nfa_def by auto
    have h3: "HF {} ∉ HF ` nxt_lvl_set_opt_ext (hfset ` qs) a ⟹
  HF ` nxt_lvl_set_opt_ext (hfset ` qs) a ⊆ nfa.states Power_nfa ⟹
  hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as
  ⟹ x ∈ lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using A[of "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a))" x] by blast
    have h4: "hfset x ∈ nxt_lvl_set_opt_ext_l (nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using D nxt_lvl_set_opt_ext_l.simps(2) by blast
    have h5: "(HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) =
              (⋃q ∈ qs. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl a))))})"
      using cond_eq_helper[OF B C] althf
      by (metis (lifting))
    have h6: "hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` (⋃q ∈ qs. {HF Q' | Q'. ((Q' ⊆ (states M)) ∧ (∃Qsl. ((set Qsl = hfset q) ∧ (distinct Qsl) ∧ models Q' (anded Qsl a))))})) as"
      using B C h4 cond_eq_helper by presburger
    have h7: "hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using h6 h5 by argo
    show ?thesis using h3[OF h1 h2 h7] h5 by fastforce
  qed
qed



subsection‹Some helper lemmas›

lemma langs_innerset_eq_help1: "(HF {}) ∉ qs ⟹ qs ⊆ nfa.states Power_nfa ⟹ x ∈ (nxt_lvl_set_opt_ext_l (hfset ` qs) as) ⟹ HF x ∈ lnextl' qs as"
  by (simp add: cond_eq2 elem_fin)


lemma langs_innerset_eq_help2: "x ∈ nxt_lvl_set_opt_ext_l {{afa.init M}} xs ⟹ x ∈ hfset ` (lnextl' (nfa.init Power_nfa) xs)"
proof -
  assume A: "x ∈ nxt_lvl_set_opt_ext_l {{afa.init M}} xs"
  have llc3z: "⋀y. (hfset y ∈ nxt_lvl_set_opt_ext_l {{afa.init M}} xs ⟹ y ∈ (lnextl' (nfa.init Power_nfa) xs))"
    using Power.init Power_nfa_def cond_eq2 nfa_init by auto
  have h1: "HF x ∈ lnextl' (nfa.init Power_nfa) xs" using langs_innerset_eq_help1[OF nfa_init] A
    by (simp add: elem_fin llc3z)
  show ?thesis using h1 A afa.elem_fin afa_axioms hfset_HF by blast
qed


lemma langs_secondset_eq: "hfset ` (nfa.final Power_nfa) = {Q. Q ⊆ afa.final M}"
proof -
  have hpfin121': "⋀Q. (Q ⊆ afa.final M ⟹ finite Q)"
    by (meson final finite_subset local.finite)
  have hpfin12: "hfset ` HF ` {Q. Q ⊆ afa.final M} = {Q. Q ⊆ afa.final M}"
    by (simp add: chainhf hpfin121')
  have h1: "hfset ` {HF Q |Q. Q ⊆ afa.final M} = {Q. Q ⊆ afa.final M}"
    using Set.setcompr_eq_image hpfin12 by metis
  show ?thesis by (simp add: Power_nfa_def h1)
qed

lemma langs_innerset_eq: "nxt_lvl_set_opt_ext_l {{afa.init M}} xs = hfset ` (Power.nextl (nfa.init Power_nfa) xs)"
proof -
  have llc2: "hfset ` (lnextl' (nfa.init Power_nfa) xs) ⊆ nxt_lvl_set_opt_ext_l {{afa.init M}} xs"
    using cond_eq1[OF nfa_init]
    using Power.init Power_nfa_def by auto
  have llc3'': "nxt_lvl_set_opt_ext_l {{afa.init M}} xs ⊆ hfset ` (lnextl' (nfa.init Power_nfa) xs)"
    using langs_innerset_eq_help1[OF nfa_init]
    using langs_innerset_eq_help2 by blast
  show ?thesis using Power.init nextl_cond_eq set_eq_subset llc2 llc3'' subset_antisym by metis
qed




text‹The main theorem›
text‹Power_nfa accepts the same language as the afa.›
theorem Power_language: "Power.language = lang"
proof -
  have fin: "Power.language ⊆ langalt"
    unfolding Power.language_def langalt_def acc_set_def using langs_innerset_eq langs_secondset_eq by fast
  have finr: "langalt ⊆ Power.language"
    proof -
      have hpfinr: "⋀as. (nxt_lvl_set_opt_ext_l {{afa.init M}} as ∩ {Q. Q ⊆ afa.final M} =
                   hfset ` (Power.nextl (nfa.init Power_nfa) as ∩ nfa.final Power_nfa))"
        using langs_innerset_eq langs_secondset_eq HF_hfset
          by (metis image_Int inj_on_def)
      show ?thesis unfolding Power.language_def langalt_def acc_set_def
        by (simp add: hpfinr)
    qed
  show ?thesis using fin finr langeq1 langeq2 by order
qed

end

end
