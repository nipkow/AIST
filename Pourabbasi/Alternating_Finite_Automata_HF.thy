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

section‹Positive Boolean formulas and their semantics:›

datatype 'a and_or_exp =
  Var 'a 
  | And "'a and_or_exp" "'a and_or_exp" 
  | Or "'a and_or_exp" "'a and_or_exp" 
  | MT

fun models :: "hf set ⇒ hf and_or_exp ⇒ bool" where
"models Q (Var q) ⟷ (q ∈ Q)" |
"models Q (Or q1 q2) ⟷ models Q q1 ∨ models Q q2" |
"models Q (And q1 q2) ⟷ models Q q1 ∧ models Q q2" |
"models Q MT ⟷ False"

lemma modelinc: "models Q a ⟹ Q ⊆ Q' ⟹ models Q' a"
by (induction a) auto

lemma mod_has: "models Q a ⟹ Q ≠ {}"
by (induction a) auto

lemma mod_has': "∄ab. models {} ab"
  using mod_has by blast

text‹Returns set of variables used in the given and or expression›
fun vars :: "'a and_or_exp ⇒ 'a set" where
  "vars MT = {}"
| "vars (Var a) = {a}"
| "vars (And q1 q2) = ((vars q1) ∪ (vars q2))"
| "vars (Or q1 q2) = ((vars q1) ∪ (vars q2))"


lemma mod_lim: "models Q aox = models (Q ∩ (vars aox)) aox"
proof (induction aox)
  case (Var x)
  then show ?case by simp
next
  case (And aox1 aox2)
  then show ?case
    by (metis (no_types, lifting) Int_lower1 Un_upper1 boolean_algebra.conj_disj_distrib
        vars.simps(3) modelinc models.simps(3) sup.cobounded2)
next
  case (Or aox1 aox2)
  then show ?case
    by (metis distrib_inf_le vars.simps(4) inf.cobounded1 le_sup_iff modelinc
        models.simps(2))
next
  case MT
  then show ?case by simp
qed


section‹HF lemmas›
lemma althf: "HF ` (hfset ` X) = X"
  using image_iff by fastforce

lemma chainhf: "∀x∈q. finite x ⟹ hfset ` HF ` q = q"
  by force


section‹Alternating Finite Automata (AFA)›

record 'a afa = states :: "hf set"
                init   :: "hf"
                final  :: "hf set"
                nxt    :: "hf ⇒ 'a ⇒ hf and_or_exp"
locale afa =
fixes M :: "'a afa"
  assumes init: "init M ∈ states M"
      and final: "final M ⊆ states M"
      and nxt:   "⋀q x. q ∈ states M ⟹ vars (nxt M q x) ⊆ states M"
      and finite: "finite (states M)"
begin

(* see Chandra, Kozen and Stockmeyer *)
fun H :: "'a list ⇒ hf ⇒ hf set ⇒ bool" where
"H [] p = (λQ. p ∈ Q)" |
"H (a#w) p = (λQ. models {q. H w q Q} (nxt M p a))"

text‹Returns whether starting from a node, a word is accepted›
fun acc :: "'a list ⇒ hf ⇒ bool" where
  "acc [] q = (q ∈ final M)"
| "acc (a#w) q = ((q ∈ states M) ∧ models {q' ∈ states M. acc w q'} (nxt M q a))"

lemma Heq_hp: "p ∈ states M ⟹ models {q. H w q Q} (nxt M p a) = models {q ∈ states M. H w q Q} (nxt M p a)"
proof -
  assume A: "p ∈ states M"
  have h1: "{q ∈ states M. H w q Q} = ({q. H w q Q}∩(states M))"
    by blast
  have h2: "models {q. H w q Q} (nxt M p a) = models ({q. H w q Q}∩(states M)) (nxt M p a)"
    using A nxt mod_lim inf.absorb_iff2 inf_assoc by metis
  show ?thesis using h1 h2 by simp
qed

lemma Heq: "q ∈ states M ⟹ (H as q (final M)) = acc as q"
proof (induction arbitrary: q rule: H.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 a w p)
  show ?case using Heq_hp[OF "2.prems"]
    by (metis (no_types, lifting) "2.IH" "2.prems" Collect_cong H.simps(2)
         local.acc.simps(2))
qed

definition Hlang :: "'a list set" where
  "Hlang ≡ {as. H as (init M) (final M)}"

text‹The language of an AFA›
definition lang :: "'a list set" where
  "lang ≡ {as. acc as (init M)}"

lemma Hlangeq: "Hlang = lang"
  using Hlang_def Heq init local.lang_def by auto

text‹Verifies that a set of states are a valid set of children for a given node and character›
text‹It also verifies whether the given nodes are valid›
fun valid_children :: "hf ⇒ hf set ⇒ 'a ⇒ bool" where
  "valid_children q Q a = ((Q ⊆ states M) ∧ (q ∈ states M) ∧ (models Q (nxt M q a)))"


text‹Equivalent to ‹acc› (Returns whether a respective accepting tree exists)›
text‹It takes a layer wise recursive approach on the tree, 
  verifying the existence of a valid set of children which can each be root to an accepting tree for the rest word›
fun acc_i :: "'a list ⇒ hf ⇒ bool" where
  "acc_i [] q = (q ∈ final M)"
| "acc_i (a#as) q = (∃Q. (valid_children q Q a) ∧ (∀q' ∈ Q. acc_i as q'))"


text‹Equivalence of ‹acc_i› and ‹acc››
lemma acc_i_acc_eq: "acc_i as q = acc as q"
proof (induction rule: acc_i.induct)
  case (1 q)
  then show ?case by simp
next
  case (2 a as q)
  then show ?case proof (cases "acc_i (a#as) q")
    case t1: True
    have h1: "(∃Q. (valid_children q Q a) ∧ (∀q' ∈ Q. acc_i as q'))"
      using t1 by force
    then obtain Q where o1: "(valid_children q Q a) ∧ (∀q' ∈ Q. acc_i as q')" by auto
    then have h2: "(∀q' ∈ Q. acc as q')"
      using "2" by blast
    then have h3: "Q ⊆ {q' ∈ states M. acc as q'}"
      using o1 by auto
    then have h4: "models {q' ∈ states M. acc as q'} (nxt M q a)"
      using modelinc o1 valid_children.simps by blast
    then show ?thesis
      using t1 by auto
  next
    case f1: False
    then show ?thesis proof (cases "acc (a#as) q")
      case True
      then have h11: "(valid_children q {q' ∈ states M. acc as q'} a) ∧ (∀q' ∈ {q' ∈ states M. acc as q'}. acc_i as q')"
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


text‹Returns the conjunction of all ‹nxt M x a› for all ‹x› in a list›
fun anded :: "hf list ⇒ 'a ⇒ hf and_or_exp" where
  "anded [] a = MT"
| "anded [x] a = nxt M x a"
| "anded (x#xs) a = And (nxt M x a) (anded xs a)"

lemma models_anded: "qs ≠ [] ⟹ models Q' (anded qs a) ⟷ (∀q ∈ set qs. models Q' (nxt M q a))"
proof (induction qs)
  case Nil
  then show ?case by simp
next
  case (Cons a qs)
  then show ?case by(cases qs) auto
qed 

abbreviation "ex_same_nxt_list Q Q' a ≡ (∃qs. set qs = Q ∧ distinct qs ∧ models Q' (anded qs a))"

text‹Verifies whether a set of states ‹qs'› is a valid next level for another set of states ‹qs›.
It is used to define an equivalent language‹langalt› to ‹lang››
fun nxt_lvl_set_valid :: "hf set ⇒ hf set ⇒ 'a ⇒ bool" where
  "nxt_lvl_set_valid Q Q' a = (Q ≠ {} ∧ Q ⊆ states M ∧ Q' ⊆ states M ∧ ex_same_nxt_list Q Q' a)"


text‹Verifies whether a word will be accepted from a given level using ‹nxt_lvl_set_valid››
fun acc_i_set :: "'a list ⇒ hf set ⇒ bool" where
   "acc_i_set [] Q = (Q ⊆ (final M))"
|  "acc_i_set (a#as) Q = (∃Q'. nxt_lvl_set_valid Q Q' a ∧ acc_i_set as Q')"


text‹An equivalent function to ‹nxt_lvl_set_valid›
helping to prove equivalence of ‹langalt› (defined later) and ‹lang››
fun nxt_lvl_set_valid' :: "hf set ⇒ hf set ⇒ 'a ⇒ bool" where
  "nxt_lvl_set_valid' Q Q' a = (Q ≠ {} ∧ Q ⊆ states M ∧ Q' ⊆ states M ∧ (∀q ∈ Q. models Q' (nxt M q a)))"


text‹Like ‹acc_i_set› but using ‹nxt_lvl_set_valid'› instead of ‹nxt_lvl_set_valid››
fun acc_i_set' :: "'a list ⇒ hf set ⇒ bool" where
   "acc_i_set' [] Q = (Q ⊆ (final M))"
|  "acc_i_set' (a#as) Q = (∃Q'. nxt_lvl_set_valid' Q Q' a ∧ acc_i_set' as Q')"


subsection‹Equivalence of ‹acc_i_set› and ‹acc_i_set'››

lemma eq_ais1: "acc_i_set as q ⟹ acc_i_set' as q"
proof (induction rule: acc_i_set.induct)
  case (1 Q)
  then show ?case by simp
next
  case (2 a as Q)
  then show ?case using models_anded by auto
qed
  
lemma eq_ais2: "acc_i_set' as q ⟹ acc_i_set as q"
proof (induction rule: acc_i_set'.induct)
  case (1 Q)
  then show ?case by simp
next
  case (2 a as Q)
  then show ?case
      by (simp) (metis empty_set finite_distinct_list finite_subset local.finite models_anded)
qed
  

subsection‹Relations between ‹acc_i› and ‹acc_i_set'››

lemma acc_i_set_if_acc_i: "Q ≠ {} ⟹ ∀q ∈ Q. acc_i as q ⟹ acc_i_set' as Q"
proof (induction as arbitrary: Q)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  then have h3: "∀q ∈ Q. ∃Q'. valid_children q Q' a ∧ (∀q' ∈ Q'. acc_i as q')"
    using Cons.prems(2) by simp
  let ?xs = "{q' ∈ states M. acc_i as q'}"
  have inc_vc: "⋀Q Q' q a. (Q ⊆ Q' ⟹ Q' ⊆ states M ⟹ valid_children q Q a ⟹ valid_children q Q' a)"
    by (meson modelinc valid_children.elims(2,3))
  have h4: "valid_children q ?xs a" if asm: "q ∈ Q" for q
  proof -
    have H1: "∃Q. valid_children q Q a ∧ (∀q' ∈ Q. acc_i as q')" using asm h3 by simp
    then obtain Q where O1: "valid_children q Q a ∧ (∀q' ∈ Q. acc_i as q')" by blast
    then have H2: "Q ⊆ ?xs" by auto
    show ?thesis using H2 O1 inc_vc by blast
  qed

  have hr: "nxt_lvl_set_valid' Q ?xs a"
    using Cons.prems(1) h4 by force

  then have "?xs ≠ {}"
    using mod_has by fastforce
  then have "acc_i_set' as ?xs"
    using Cons.IH by force
  then show ?case
    using acc_i_set'.simps(2) hr by blast
qed
  
lemma acc_i_if_acc_i_set: "acc_i_set' as Q ⟹ (∀q ∈ Q. acc_i as q)"
proof (induction rule: acc_i_set'.induct)
  case (1 Q)
  then show ?case by fastforce
next
  case (2 a as Q)
  then show ?case by fastforce
qed



text‹Returns possible options for the next level given the possible options for some level of the tree›
fun nxt_lvl_set_opt_ext :: "hf set set ⇒ 'a ⇒ hf set set" where
  "nxt_lvl_set_opt_ext QQ a = {Q'. ∃Q∈QQ. nxt_lvl_set_valid Q Q' a}"

subsection‹Some lemmas about ‹nxt_lvl_set_opt_ext››
lemma no_mt: "{} ∉ (nxt_lvl_set_opt_ext QQ a)"
  using mod_has' by fastforce

lemma cond_fin: "finite Q ⟹ finite (nxt_lvl_set_opt_ext Q a)"
  using local.finite by auto

lemma elemfin': "∀y∈(nxt_lvl_set_opt_ext Q a). finite y"
  using local.finite rev_finite_subset by auto

lemma elemfin: "x ∈ (nxt_lvl_set_opt_ext QQ a) ⟹ finite x"
  using elemfin' by blast


text‹An equivalent to ‹acc_i_set› using ‹nxt_lvl_set_opt_ext› and ‹acc_set››
fun acc_i_set_sim :: "'a list ⇒ hf set ⇒ bool" where
   "acc_i_set_sim [] Q = (Q ⊆ final M)"
|  "acc_i_set_sim (a#as) Q = (∃Q' ∈ nxt_lvl_set_opt_ext {Q} a. acc_i_set_sim as Q')"

subsection‹Equivalence of ‹acc_i_set_sim› and ‹acc_i_set››
lemma aiss_eq1: "acc_i_set_sim as Q ⟹ acc_i_set as Q"
proof (induction rule: acc_i_set_sim.induct)
  case (1 Q)
  then show ?case by (simp)
next
  case (2 a as Q)
  have h1: "(∃Q' ∈ (nxt_lvl_set_opt_ext {Q} a). (acc_i_set_sim as Q'))"
    using "2.prems" acc_i_set_sim.simps(2) by blast
  then obtain Q' where o1: "Q' ∈ nxt_lvl_set_opt_ext {Q} a ∧ acc_i_set_sim as Q'" by blast
  then show ?case using 2(1)[of Q'] by auto
qed

lemma aiss_eq2: "acc_i_set as Q ⟹ acc_i_set_sim as Q"
proof (induction rule: acc_i_set.induct)
  case (1 Q)
  then show ?case by (simp)
next
  case (2 a as Q)
  then show ?case by auto
qed


text‹Returns possible options for the level reached after processing a word from given options for starting level›
fun nxt_lvl_set_opt_ext_l :: "hf set set ⇒ 'a list ⇒ hf set set" where
  "nxt_lvl_set_opt_ext_l QQ [] = QQ"  
| "nxt_lvl_set_opt_ext_l QQ (a#as) = nxt_lvl_set_opt_ext_l (nxt_lvl_set_opt_ext QQ a) as"


text‹Helper lemma about ‹nxt_lvl_set_opt_ext_l››
lemma elem_fin: "x ∈ nxt_lvl_set_opt_ext_l Q xs ⟹ (∀y∈Q. finite y) ⟹ finite x"
proof (induction rule: nxt_lvl_set_opt_ext_l.induct)
  case (1 QQ)
  then show ?case by simp
next
  case (2 QQ a as)
  then show ?case by (metis elemfin nxt_lvl_set_opt_ext_l.simps(2))
qed
  
subsection‹Relations between ‹nxt_lvl_set_opt_ext_l› and ‹acc_i_set_sim› or ‹acc_i_set››

lemma helper1: "∃x ∈ (nxt_lvl_set_opt_ext_l QQ as). x ⊆ final M ⟹ ∃Q ∈ QQ. acc_i_set_sim as Q"
proof (induction rule: nxt_lvl_set_opt_ext_l.induct)
  case (1 QQ)
  then show ?case by simp
next
  case (2 QQ a as)
  then have H1: "∃Q'∈nxt_lvl_set_opt_ext QQ a. acc_i_set_sim as Q'" by simp
  then obtain Q' where O1: "Q'∈nxt_lvl_set_opt_ext QQ a ∧ acc_i_set_sim as Q'" by blast
  then have H2: "∃Q∈QQ. nxt_lvl_set_valid Q Q' a" by simp
  then obtain Q where O2: "Q∈QQ ∧ nxt_lvl_set_valid Q Q' a" by blast
  have H3: "Q'∈nxt_lvl_set_opt_ext {Q} a"
    using O2 by auto 
  show ?case using H3 O1 O2 acc_i_set_sim.simps(2) by blast
qed


lemma helper2: "Q ∈ QQ ⟹ acc_i_set_sim as Q ⟹ ∃x ∈ nxt_lvl_set_opt_ext_l QQ as. x ⊆ final M"
proof (induction as arbitrary: QQ Q)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  have h1: "(∃Q' ∈ (nxt_lvl_set_opt_ext {Q} a). (acc_i_set_sim as Q'))"
    using Cons.prems(2) acc_i_set_sim.simps(2) by blast
  then obtain Q' where o1: "Q' ∈ nxt_lvl_set_opt_ext {Q} a ∧ acc_i_set_sim as Q'" by blast
  then have h2: "Q' ∈ nxt_lvl_set_opt_ext QQ a"
    using Cons.prems(1) by fastforce
  then show ?case 
    using Cons(1)[of Q' "nxt_lvl_set_opt_ext QQ a"] o1 h2 by simp 
qed

lemma langeq2_helper: "nxt_lvl_set_opt_ext_l {{init M}} as ∩ Pow(final M) ≠ {} ⟹ acc_i_set as {init M}"
  using aiss_eq1 helper1 by blast

lemma langeq1_helper: "acc_i_set as {init M} ⟹ nxt_lvl_set_opt_ext_l {{init M}} as ∩ Pow(final M) ≠ {}"
  by (simp add: aiss_eq2 helper2 disjoint_iff_not_equal)


text‹An equivalent definition for lang›
definition langalt :: "'a list set" where
  "langalt ≡ {as. nxt_lvl_set_opt_ext_l {{init M}} as ∩ Pow(final M) ≠ {}}"


subsection‹‹langalt = lang››

lemma langeq1: "lang ⊆ langalt"
  unfolding lang_def langalt_def
  by (simp add: Collect_mono_iff acc_i_set_if_acc_i eq_ais2 langeq1_helper acc_i_acc_eq)

lemma langeq2: "langalt ⊆ lang"
  unfolding lang_def langalt_def using langeq2_helper acc_i_if_acc_i_set eq_ais1 acc_i_acc_eq by blast

subsection‹The Powerset Construction›

definition Power_nfa :: "'a nfa" where 
  "Power_nfa = ⦇nfa.states = HF ` Pow (states M),
                     init  = {HF {init M}},
                     final = HF ` Pow(final M),
                     nxt   = (λQ x. HF ` {Q'. Q' ⊆ (states M) ∧ ex_same_nxt_list (hfset Q) Q' x}),
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

subsection‹Helper lemmas for ‹Power_nfa››
lemma neps: "q ⊆ nfa.states Power_nfa ⟹ Power.epsclo q = q"
  using Power.epsclo_trivial Power_nfa_def by auto

lemma nfa_init: "HF {} ∉ (nfa.init Power_nfa)"
  using Power_nfa_def hmem_HF_iff by fastforce


text‹Works similar to Power.nextl, defined to help prove equivalence of Power.language and langalt›
fun lnextl' :: "hf set ⇒ 'a list ⇒ hf set" where
  "lnextl' Q []     = Q"
| "lnextl' Q (x#xs) = lnextl' (⋃q ∈ Q. HF ` {Q'. Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' x}) xs"


text‹Relationship of lnextl' and Power.nextl›
lemma nextl_cond_eq: "q ⊆ nfa.states Power_nfa ⟹ lnextl' q as = Power.nextl q as"
proof (induction as arbitrary: q)
  case Nil
  then show ?case by (simp add: neps)
next
  case (Cons a as)
  have h1: "(⋃q∈q. HF ` {Q'.
                 Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' a})
                = (⋃q∈q. nfa.nxt Power_nfa q a)" by (auto simp add: Power_nfa_def)
  have h2: "(⋃q∈Power.epsclo q. nfa.nxt Power_nfa q a) ⊆ nfa.states Power_nfa"
    using Cons.prems Power.nxt neps by auto
  have h3: "lnextl'
     (⋃q∈q. HF ` {Q'. Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' a})
     as =
    Power.nextl (⋃q∈Power.epsclo q. nfa.nxt Power_nfa q a) as"
    using h1 Cons.IH(1)[OF h2]
    by (simp add: Cons.prems neps afa_axioms)
  show ?case using h3 by simp
qed


subsection‹Relationships between ‹lnextl'› and ‹nxt_lvl_set_opt_ext_l››

text‹A helper lemma›
lemma cond_eq_helper:
  assumes "HF {} ∉ Q" "Q ⊆ nfa.states Power_nfa"
  shows "hfset ` (⋃q ∈ Q. HF ` {Q'. Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' x})
    = nxt_lvl_set_opt_ext (hfset ` Q) x"
proof -
  let ?P' = "λQ' q. Q' ⊆ states M ∧ ex_same_nxt_list q Q' x"
  let ?P = "λQ' q. ?P' Q' (hfset q)"
  let ?PQ = "λq. {Q'. ?P Q' q}"
  have hpll1: "hfset ` (⋃q ∈ Q. HF ` ?PQ q) =
              {Q'. ∃Q∈ (hfset ` Q). Q ≠ {} ∧ Q ⊆ states M ∧ ?P' Q' Q}"
  proof -
    have hpll16: "(⋃q ∈ Q. {Q'. hfset q ≠ {} ∧ hfset q ⊆ states M ∧ ?P Q' q})
      = (⋃q ∈ Q. ?PQ q)" 
    proof -
      have h1: "⋀q. q ∈ Q ⟹ hfset q ≠ {}" using assms(1) by (metis HF_hfset)
      have h2: "⋀q. q ∈ Q ⟹ hfset q ⊆ states M"
            using assms(2) hfset_HF local.finite mem_Collect_eq nfa.select_convs(1)
                  rev_finite_subset unfolding Power_nfa_def Pow_def by force
      show ?thesis using h1 h2 assms by simp
    qed
    have hpll11: "hfset ` (⋃q ∈ Q. HF ` ?PQ q) = (⋃q ∈ Q. {hfset (HF Q') | Q'. ?P Q' q})"
      by auto
    have hpll13: "(⋃q ∈ Q. {hfset (HF Q') | Q'. ?P Q' q}) = (⋃q ∈ Q. ?PQ q)"
    proof -
      have "⋀q. {hfset (HF Q') | Q'. ?P Q' q} = ?PQ q"
        by (metis finite_subset hfset_HF local.finite)
      then show ?thesis by simp
    qed
    have hpll14: "{Q'. ∃H∈ hfset ` Q. H ≠ {} ∧ H ⊆ states M ∧ ?P' Q' H}
            =
            (⋃H ∈ hfset ` Q. {Q'. H ≠ {} ∧ H ⊆ states M ∧ ?P' Q' H})"
      by blast
    show ?thesis using hpll16 hpll14 hpll13 hpll11 assms by auto
  qed
  show ?thesis using hpll1 assms by simp
qed

lemma cond_eq1: "HF {} ∉ Q ⟹ Q ⊆ nfa.states Power_nfa ⟹ x ∈ lnextl' Q as ⟹ hfset x ∈ (nxt_lvl_set_opt_ext_l (hfset ` Q) as)"
proof (induction as arbitrary: Q x)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have h1: "HF {} ∉ HF ` (nxt_lvl_set_opt_ext (hfset ` Q) a)"
    using no_mt[of "(hfset ` Q)" a] elemfin' cond_fin
    by (metis Zero_hf_def chainhf hfset_0 image_eqI)
  have h21: "∀x∈(nxt_lvl_set_opt_ext (hfset ` Q) a). x ⊆ states M"
    by auto
  then have h2: "(HF ` (nxt_lvl_set_opt_ext (hfset ` Q) a)) ⊆ (nfa.states Power_nfa)"
    using Power_nfa_def by auto
  have h3: "HF {} ∉ HF ` nxt_lvl_set_opt_ext (hfset ` Q) a ⟹
  HF ` nxt_lvl_set_opt_ext (hfset ` Q) a ⊆ nfa.states Power_nfa ⟹
  x ∈ lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) as ⟹
  hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) as"
    using Cons.IH[of "(HF ` (nxt_lvl_set_opt_ext (hfset ` Q) a))" x] by blast
  have h4: "x ∈ (lnextl' (⋃q ∈ Q. HF ` {Q'. Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' a}) as)"
    using Cons.prems(3) lnextl'.simps(2) by blast
  have h5: "(HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) =
            (⋃q ∈ Q. HF ` {Q'. Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' a})"
    using cond_eq_helper[OF Cons.prems(1,2)] althf
    by (metis (lifting)) 
  have h6: "x ∈ lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) as"
    using h4 h5 by presburger
  show ?case using h3[OF h1 h2 h6]
    by (metis (no_types, lifting) Cons.prems(1,2) cond_eq_helper althf nxt_lvl_set_opt_ext_l.simps(2))
qed


lemma cond_eq2: "HF {} ∉ Q ⟹ Q ⊆ nfa.states Power_nfa ⟹ hfset x ∈ (nxt_lvl_set_opt_ext_l (hfset ` Q) as) ⟹ x ∈ lnextl' Q as"
proof (induction as arbitrary: Q x)
  case Nil
  then show ?case
    using HF_hfset
    by (metis image_iff lnextl'.simps(1) nxt_lvl_set_opt_ext_l.simps(1))
next
  case (Cons a as)
  have h1: "HF {} ∉ HF ` (nxt_lvl_set_opt_ext (hfset ` Q) a)"
    using no_mt[of "(hfset ` Q)" a] elemfin' cond_fin 
    by (metis Zero_hf_def chainhf hfset_0 image_eqI)
  have h21: "∀x∈(nxt_lvl_set_opt_ext (hfset ` Q) a). x ⊆ states M"
    by auto
  then have h2: "(HF ` (nxt_lvl_set_opt_ext (hfset ` Q) a)) ⊆ (nfa.states Power_nfa)"
    using Power_nfa_def by auto
  have h3: "HF {} ∉ HF ` nxt_lvl_set_opt_ext (hfset ` Q) a ⟹
  HF ` nxt_lvl_set_opt_ext (hfset ` Q) a ⊆ nfa.states Power_nfa ⟹
  hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) as
  ⟹ x ∈ lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) as"
    using Cons.IH[of "HF ` (nxt_lvl_set_opt_ext (hfset ` Q) a)" x] by blast
  have h4: "hfset x ∈ nxt_lvl_set_opt_ext_l (nxt_lvl_set_opt_ext (hfset ` Q) a) as"
    using Cons.prems(3) nxt_lvl_set_opt_ext_l.simps(2) by blast
  have h5: "(HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) =
            (⋃q ∈ Q. HF ` {Q'. Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' a})"
    using cond_eq_helper[OF Cons.prems(1,2)] althf
    by (metis (lifting))
  have h6: "hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` (⋃q ∈ Q. HF ` {Q'. Q' ⊆ states M ∧ ex_same_nxt_list (hfset q) Q' a})) as"
    using Cons.prems(1,2) h4 cond_eq_helper by presburger
  have h7: "hfset x ∈ nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` Q) a) as"
    using h6 h5 by argo
  show ?case using h3[OF h1 h2 h7] h5 by fastforce
qed


subsection‹Some helper lemmas›

lemma langs_innerset_eq_help:
  assumes "x ∈ nxt_lvl_set_opt_ext_l {{init M}} xs"
  shows "x ∈ hfset ` lnextl' (nfa.init Power_nfa) xs"
proof -
  have llc3z: "⋀y. (hfset y ∈ nxt_lvl_set_opt_ext_l {{init M}} xs ⟹ y ∈ (lnextl' (nfa.init Power_nfa) xs))"
    using Power.init Power_nfa_def cond_eq2 nfa_init by auto
  have h1: "HF x ∈ lnextl' (nfa.init Power_nfa) xs"
    using assms elem_fin llc3z by auto
  show ?thesis using h1 assms elem_fin afa_axioms hfset_HF by blast
qed


lemma langs_secondset_eq: "hfset ` nfa.final Power_nfa = Pow(final M)"
unfolding Power_nfa_def  nfa.select_convs(3)
by (metis (mono_tags, lifting) Pow_iff chainhf final finite_subset finite)

lemma langs_innerset_eq:
  "nxt_lvl_set_opt_ext_l {{init M}} xs = hfset ` Power.nextl (nfa.init Power_nfa) xs"
proof -
  have llc2: "hfset ` lnextl' (nfa.init Power_nfa) xs ⊆ nxt_lvl_set_opt_ext_l {{init M}} xs"
    using cond_eq1[OF nfa_init]
    using Power.init Power_nfa_def by auto
  have llc3'': "nxt_lvl_set_opt_ext_l {{init M}} xs ⊆ hfset ` (lnextl' (nfa.init Power_nfa) xs)"
    using langs_innerset_eq_help by blast
  show ?thesis using Power.init nextl_cond_eq set_eq_subset llc2 llc3'' subset_antisym by metis
qed


text‹The main theorem: ‹Power_nfa› accepts the same language as the AFA.›
theorem Power_language: "Power.language = lang"
proof -
  have fin: "Power.language ⊆ langalt"
    unfolding Power.language_def langalt_def using langs_innerset_eq langs_secondset_eq by fast
  have finr: "langalt ⊆ Power.language"
    proof -
      have hpfinr: "⋀as. nxt_lvl_set_opt_ext_l {{init M}} as ∩ Pow(final M) =
                   hfset ` (Power.nextl (nfa.init Power_nfa) as ∩ nfa.final Power_nfa)"
        using langs_innerset_eq langs_secondset_eq HF_hfset
          by (metis image_Int inj_on_def)
      show ?thesis unfolding Power.language_def langalt_def
        by (simp add: hpfinr)
    qed
  show ?thesis using fin finr langeq1 langeq2 by order
qed

end

end
