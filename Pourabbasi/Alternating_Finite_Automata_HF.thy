chapter \<open>Alternating Finite Automata using the Hereditarily Finite Sets\<close> 

theory Alternating_Finite_Automata_HF
  imports Main Finite_Automata_HF.Finite_Automata_HF 
begin

text\<open>This theory formalizes alternating finite automata (AFA) based on hereditarily
finite sets. The main result is that every AFA can be converted into an NFA.
Our formalization is based on positive boolean formulas rather than functions,
following the textbook Automatentheory und Logik by Hofmann and Lange.

The theory starts with positive boolean formulas (type \<open>'a and_or_exp\<close>). The
main body of the theory is concerned with AFAs and their translation to NFAs.\<close>

section\<open>Positive Boolean formulas and the related modeling relation\<close>
datatype 'a and_or_exp =
  Var 'a 
  | And "'a and_or_exp" "'a and_or_exp" 
  | Or "'a and_or_exp" "'a and_or_exp" 
  | MT

fun models :: "hf set \<Rightarrow> hf and_or_exp \<Rightarrow> bool" where
"models Q (Var q) \<longleftrightarrow> (q \<in> Q)" |
"models Q (Or q1 q2) \<longleftrightarrow> models Q q1 \<or> models Q q2" |
"models Q (And q1 q2) \<longleftrightarrow> models Q q1 \<and> models Q q2" |
"models Q MT \<longleftrightarrow> False"

lemma modelinc: "models qs a \<Longrightarrow> qs \<subseteq> qs' \<Longrightarrow> models qs' a"
by (induction a) auto

lemma mod_has: "models qs a \<Longrightarrow> qs \<noteq> {}"
by (induction a) auto

lemma mod_has': "\<nexists>ab. models {} ab"
  using mod_has by blast

text\<open>Returns set of variables used in the given and or expression\<close>
fun elems :: "'a and_or_exp \<Rightarrow> 'a set" where
  "elems MT = {}"
| "elems (Var a) = {a}"
| "elems (And q1 q2) = ((elems q1) \<union> (elems q2))"
| "elems (Or q1 q2) = ((elems q1) \<union> (elems q2))"


section\<open>hf lemmas\<close>
lemma althf: "HF ` (hfset ` X) = X"
  using image_iff by fastforce

lemma chainhf: "\<forall>x\<in>q. finite x \<Longrightarrow> hfset ` HF ` q = q"
  by force


section\<open>Alternating Finite Automata\<close>

record 'a afa = states :: "hf set"
                init   :: "hf"
                final  :: "hf set"
                nxt    :: "hf \<Rightarrow> 'a \<Rightarrow> hf and_or_exp"
locale afa =
fixes M :: "'a afa"
  assumes init: "init M \<in> states M"
      and final: "final M \<subseteq> states M"
      and nxt:   "\<And>q x. q \<in> states M \<Longrightarrow> elems (nxt M q x) \<subseteq> states M"
      and finite: "finite (states M)"
begin

text\<open>Returns whether starting from a node, a (rest)word is accepted\<close>
fun A :: "'a list \<Rightarrow> hf \<Rightarrow> bool" where
  "A [] q = (q \<in> final M)"
| "A (a#w) q = ((q \<in> states M) \<and> (models {q' \<in> states M. A w q'} (nxt M q a)))"

text\<open>The language of the afa\<close>
definition lang :: "'a list set" where
  "lang \<equiv> {as. A as (init M)}"

text\<open>Verifies that a set of states are a valid set of children for a given node and character\<close>
text\<open>It also verifies whether the given nodes are valid\<close>
fun valid_children :: "hf \<Rightarrow> hf set \<Rightarrow> 'a \<Rightarrow> bool" where
  "valid_children q qs a = ((qs \<subseteq> states M) \<and> (q \<in> states M) \<and> (models qs (nxt M q a)))"


text\<open>Equivalent to A (Returns whether a respective accepting tree exists)\<close>
text\<open>It takes a layer wise recursive approach on the tree, 
  verifying the existence of a valid set of children which can each be root to an accepting tree for the rest word\<close>
fun acc_i :: "'a list \<Rightarrow> hf \<Rightarrow> bool" where
  "acc_i [] q = (q \<in> final M)"
| "acc_i (a#as) q = (\<exists>qs. (valid_children q qs a) \<and> (\<forall>q' \<in> qs. acc_i as q'))"


text\<open>Equivalence of acc_i and A\<close>
lemma acc_i_A_eq: "acc_i as q = A as q"
proof (induction rule: acc_i.induct)
  case (1 q)
  then show ?case by simp
next
  case (2 a as q)
  then show ?case proof (cases "acc_i (a#as) q")
    case t1: True
    have h1: "(\<exists>qs. (valid_children q qs a) \<and> (\<forall>q' \<in> qs. acc_i as q'))"
      using t1 by force
    then obtain qs where o1: "(valid_children q qs a) \<and> (\<forall>q' \<in> qs. acc_i as q')" by auto
    then have h2: "(\<forall>q' \<in> qs. A as q')"
      using "2" by blast
    then have h3: "qs \<subseteq> {q' \<in> states M. A as q'}"
      using o1 by auto
    then have h4: "models {q' \<in> states M. A as q'} (nxt M q a)"
      using modelinc o1 valid_children.simps by blast
    then show ?thesis
      using t1 by auto
  next
    case f1: False
    then show ?thesis proof (cases "A (a#as) q")
      case True
      then have h11: "(valid_children q {q' \<in> states M. A as q'} a) \<and> (\<forall>q' \<in> {q' \<in> states M. A as q'}. acc_i as q')"
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



text\<open>Returns the conjunction of all (nxt M x a) for all xs in a list\<close>
fun anded :: "hf list \<Rightarrow> 'a \<Rightarrow> hf and_or_exp" where
  "anded [] a = MT"
| "anded [x] a = nxt M x a"
| "anded (x#xs) a = And (nxt M x a) (anded xs a)"

lemma models_anded: "qs \<noteq> [] \<Longrightarrow> models qs' (anded (qs) a) \<longleftrightarrow> (\<forall>q \<in> set (qs). models qs' (nxt M q a))"
proof (induction qs)
  case Nil
  then show ?case by simp
next
  case (Cons a qs)
  then show ?case by(cases qs) auto
qed 

text\<open>Verifies whether a set of states (qs') is a valid next level for another set of states (qs)\<close>
text\<open>It is used to define an equivalent language(langalt) to lang\<close>
fun nxt_lvl_set_valid :: "hf set \<Rightarrow> hf set \<Rightarrow> 'a \<Rightarrow> bool" where
  "nxt_lvl_set_valid qs qs' a = ((qs \<noteq> {}) \<and> (qs \<subseteq> states M) \<and> (qs' \<subseteq> states M) \<and> (\<exists>qsl. ((set qsl = qs) \<and> (distinct qsl) \<and> models qs' (anded qsl a))))"


text\<open>Verifies whether a (rest)word will be accepted from a given level using nxt_lvl_set_valid\<close>
fun acc_i_set :: "'a list \<Rightarrow> hf set \<Rightarrow> bool" where
   "acc_i_set [] qs = (qs \<subseteq> (final M))"
|  "acc_i_set (a#as) qs = (\<exists>qs'. (nxt_lvl_set_valid qs qs' a) \<and> (acc_i_set as qs'))"


text\<open>An equivalent function to nxt_lvl_set_valid helping to prove equivalence of langalt (defined later) and lang\<close>
fun nxt_lvl_set_valid' :: "hf set \<Rightarrow> hf set \<Rightarrow> 'a \<Rightarrow> bool" where
  "nxt_lvl_set_valid' qs qs' a = ((qs \<noteq> {}) \<and> (qs \<subseteq> states M) \<and> (qs' \<subseteq> states M) \<and> (\<forall>q \<in> qs. models qs' (nxt M q a)))"


text\<open>Like acc_i_set but using nxt_lvl_set_valid' instead of nxt_lvl_set_valid\<close>
fun acc_i_set' :: "'a list \<Rightarrow> hf set \<Rightarrow> bool" where
   "acc_i_set' [] qs = (qs \<subseteq> (final M))"
|  "acc_i_set' (a#as) qs = (\<exists>qs'. (nxt_lvl_set_valid' qs qs' a) \<and> (acc_i_set' as qs'))"


subsection\<open>Equivalence of acc_i_set and acc_i_set'\<close>

lemma eq_ais1: "acc_i_set as q \<Longrightarrow> acc_i_set' as q"
proof (induction rule: acc_i_set.induct)
  case (1 qs)
  then show ?case by simp
next
  case (2 a as qs)
  then show ?case using models_anded by auto
qed
  
lemma eq_ais2: "acc_i_set' as q \<Longrightarrow> acc_i_set as q"
proof (induction rule: acc_i_set'.induct)
  case (1 qs)
  then show ?case by simp
next
  case (2 a as qs)
  then show ?case
      by (simp) (metis empty_set finite_distinct_list finite_subset local.finite models_anded)
qed
  

subsection\<open>Relations between acc_i and acc_i_set'\<close>

lemma aiais1: "qs \<noteq> {} \<Longrightarrow> (\<forall>q \<in> qs. acc_i as q) \<Longrightarrow> acc_i_set' as qs"
proof -
  assume A: "qs \<noteq> {}" and B: "(\<forall>q \<in> qs. acc_i as q)"
  show ?thesis using A B proof (induction rule: acc_i_set'.induct)
    case (1 qs)
    then show ?case by auto
  next
    case (2 a as qs)
    then have h3: "\<forall>q \<in> qs. \<exists>xqs. ((valid_children q xqs a) \<and> (\<forall>q' \<in> xqs. acc_i as q'))"
      using B by simp
    let ?xs = "{q'\<in>(states M). acc_i as q'}"
    have inc_vc: "\<And>xqs xqs' xq xa. (xqs \<subseteq> xqs' \<Longrightarrow> xqs' \<subseteq> states M \<Longrightarrow> valid_children xq xqs xa \<Longrightarrow> valid_children xq xqs' xa)"
      by (meson modelinc valid_children.elims(2,3))
    have h4: "\<forall>q \<in> qs. (valid_children q ?xs a)"
    proof (intro ballI)
      fix q
      assume "q \<in> qs"
      then have H1: "\<exists>xqs. ((valid_children q xqs a) \<and> (\<forall>q' \<in> xqs. acc_i as q'))" using h3 by simp
      then obtain xqs where O1: "((valid_children q xqs a) \<and> (\<forall>q' \<in> xqs. acc_i as q'))" by blast
      then have H2: "xqs \<subseteq> ?xs" by auto
      show "(valid_children q ?xs a)"
        using H2 O1 inc_vc by blast
    qed

    have hr: "nxt_lvl_set_valid' qs ?xs a"
      using "2.prems"(1) h4 by force

    then have "?xs \<noteq> {}"
      using mod_has by fastforce
    then have "acc_i_set' as ?xs"
      using "2.IH" by force
    then show ?case
      using acc_i_set'.simps(2) hr by blast
  qed
qed
  
lemma aiais2: "acc_i_set' as qs \<Longrightarrow> (\<forall>q \<in> qs. acc_i as q)"
proof (induction rule: acc_i_set'.induct)
  case (1 qs)
  then show ?case by fastforce
next
  case (2 a as qs)
  then show ?case by fastforce
qed



text\<open>Returns possible options for the next level given the possible options for some level of the tree\<close>
fun nxt_lvl_set_opt_ext :: "hf set set \<Rightarrow> 'a \<Rightarrow> hf set set" where
  "nxt_lvl_set_opt_ext qss a = {qs'. \<exists>qs\<in>qss. nxt_lvl_set_valid qs qs' a}"

subsection\<open>Some lemmas about nxt_lvl_set_opt_ext\<close>
lemma no_mt: "{} \<notin> (nxt_lvl_set_opt_ext qss a)"
  using mod_has' by fastforce

lemma cond_fin: "finite qs \<Longrightarrow> finite (nxt_lvl_set_opt_ext qs a)"
  using local.finite by auto

lemma elemfin': "\<forall>y\<in>(nxt_lvl_set_opt_ext qs a). finite y"
  using local.finite rev_finite_subset by auto

lemma elemfin: "x \<in> (nxt_lvl_set_opt_ext qss a) \<Longrightarrow> finite x"
  using elemfin' by blast


text\<open>An equivalent to acc_i_set using nxt_lvl_set_opt_ext and acc_set\<close>
fun acc_i_set_sim :: "'a list \<Rightarrow> hf set \<Rightarrow> bool" where
   "acc_i_set_sim [] qs = (qs \<subseteq> final M)"
|  "acc_i_set_sim (a#as) qs = (\<exists>qs' \<in> (nxt_lvl_set_opt_ext {qs} a). (acc_i_set_sim as qs'))"

subsection\<open>Equivalence of acc_i_set_sim and acc_i_set\<close>
lemma aiss_eq1: "acc_i_set_sim as qs \<Longrightarrow> acc_i_set as qs"
proof (induction rule: acc_i_set_sim.induct)
  case (1 qs)
  then show ?case by (simp)
next
  case (2 a as qs)
  have h1: "(\<exists>qs' \<in> (nxt_lvl_set_opt_ext {qs} a). (acc_i_set_sim as qs'))"
    using "2.prems" acc_i_set_sim.simps(2) by blast
  then obtain qs' where o1: "qs' \<in> (nxt_lvl_set_opt_ext {qs} a) \<and> (acc_i_set_sim as qs')" by blast
  then show ?case using 2(1)[of qs'] by auto
qed

lemma aiss_eq2: "acc_i_set as qs \<Longrightarrow> acc_i_set_sim as qs"
proof (induction rule: acc_i_set.induct)
  case (1 qs)
  then show ?case by (simp)
next
  case (2 a as qs)
  then show ?case by auto
qed


text\<open>Returns possible options for the level reached after processing a word from given options for starting level\<close>
fun nxt_lvl_set_opt_ext_l :: "hf set set \<Rightarrow> 'a list \<Rightarrow> hf set set" where
  "nxt_lvl_set_opt_ext_l qss [] = qss"  
| "nxt_lvl_set_opt_ext_l qss (a#as) = nxt_lvl_set_opt_ext_l (nxt_lvl_set_opt_ext qss a) as"


text\<open>Helper lemma about nxt_lvl_set_opt_ext_l\<close>
lemma elem_fin: "x \<in> nxt_lvl_set_opt_ext_l qs xs \<Longrightarrow> (\<forall>y\<in>qs. finite y) \<Longrightarrow> finite x"
proof (induction rule: nxt_lvl_set_opt_ext_l.induct)
  case (1 qss)
  then show ?case by simp
next
  case (2 qss a as)
  then show ?case by (metis elemfin nxt_lvl_set_opt_ext_l.simps(2))
qed
  
subsection\<open>Relations between nxt_lvl_set_opt_ext_l and acc_i_set_sim or acc_i_set\<close>

lemma helper1: "\<exists>x \<in> (nxt_lvl_set_opt_ext_l qss as). x \<subseteq> final M \<Longrightarrow> \<exists>qs \<in> qss. acc_i_set_sim as qs"
proof (induction rule: nxt_lvl_set_opt_ext_l.induct)
  case (1 qss)
  then show ?case by simp
next
  case (2 qss a as)
  then have H1: "\<exists>qs'\<in>nxt_lvl_set_opt_ext qss a. acc_i_set_sim as qs'" by simp
  then obtain qs' where O1: "qs'\<in>nxt_lvl_set_opt_ext qss a \<and> acc_i_set_sim as qs'" by blast
  then have H2: "\<exists>qs\<in>qss. nxt_lvl_set_valid qs qs' a" by simp
  then obtain qs where O2: "qs\<in>qss \<and> nxt_lvl_set_valid qs qs' a" by blast
  have H3: "qs'\<in>nxt_lvl_set_opt_ext {qs} a"
    using O2 by auto 
  show ?case using H3 O1 O2 acc_i_set_sim.simps(2) by blast
qed


lemma helper2: "qs \<in> qss \<Longrightarrow> acc_i_set_sim as qs \<Longrightarrow> \<exists>x \<in> (nxt_lvl_set_opt_ext_l qss as). x \<subseteq> final M"
proof (induction as arbitrary: qss qs)
  case Nil
  then show ?case by auto
next
  case (Cons a as)
  have h1: "(\<exists>qs' \<in> (nxt_lvl_set_opt_ext {qs} a). (acc_i_set_sim as qs'))"
    using Cons.prems(2) acc_i_set_sim.simps(2) by blast
  then obtain qs' where o1: "(qs' \<in> (nxt_lvl_set_opt_ext {qs} a) \<and> (acc_i_set_sim as qs'))" by blast
  then have h2: "qs' \<in> (nxt_lvl_set_opt_ext qss a)"
    using Cons.prems(1) by fastforce
  then show ?case 
    using Cons(1)[of qs' "(nxt_lvl_set_opt_ext qss a)"] o1 h2 by simp 
qed

lemma langeq2_helper: "nxt_lvl_set_opt_ext_l {{init M}} as \<inter> Pow(final M) \<noteq> {} \<Longrightarrow> acc_i_set as {init M}"
  using aiss_eq1 helper1 by blast

lemma langeq1_helper: "acc_i_set as {init M} \<Longrightarrow> nxt_lvl_set_opt_ext_l {{init M}} as \<inter> Pow(final M) \<noteq> {}"
  by (simp add: aiss_eq2 helper2 disjoint_iff_not_equal)


text\<open>An equivalent definition for lang\<close>
definition langalt :: "'a list set" where
  "langalt \<equiv> {as. (nxt_lvl_set_opt_ext_l {{init M}} as) \<inter> Pow(final M) \<noteq> {}}"


subsection\<open>Equivalence of lang and langalt\<close>
lemma langeq1: "lang \<subseteq> langalt"
  unfolding lang_def langalt_def
  by (simp add: Collect_mono_iff aiais1 eq_ais2 langeq1_helper acc_i_A_eq)

lemma langeq2: "langalt \<subseteq> lang"
  unfolding lang_def langalt_def using langeq2_helper aiais2 eq_ais1 acc_i_A_eq by blast

subsection\<open>The Powerset Construction\<close>

definition Power_nfa :: "'a nfa" where 
  "Power_nfa = \<lparr>nfa.states = {HF Q | Q. Q \<in> Pow (states M)},
                     init  = {HF {init M}},
                     final = {HF Q | Q. Q \<subseteq> final M},
                     nxt   = (\<lambda>Q x. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset Q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))}),
                     eps = {}\<rparr>"


interpretation Power: nfa Power_nfa
proof unfold_locales
  show "nfa.init Power_nfa \<subseteq> nfa.states Power_nfa"
    using Power_nfa_def init by auto
next 
  show "nfa.final Power_nfa \<subseteq> nfa.states Power_nfa"
    using Power_nfa_def final by force
next
  show "\<And>q x. q \<in> nfa.states Power_nfa \<Longrightarrow>
           nfa.nxt Power_nfa q x \<subseteq> nfa.states Power_nfa"
    using Power_nfa_def by auto
next
  show "finite (nfa.states Power_nfa)"
    unfolding Power_nfa_def using finite by simp
qed

subsection\<open>Helper lemmas on Power_nfa\<close>
lemma neps: "q \<subseteq> nfa.states Power_nfa \<Longrightarrow> Power.epsclo q = q"
  using Power.epsclo_trivial Power_nfa_def by auto

lemma nfa_init: "(HF {}) \<notin> (nfa.init Power_nfa)"
  using Power_nfa_def hmem_HF_iff by fastforce


text\<open>Works similar to Power.nextl, defined to help prove equivalence of Power.language and langalt\<close>
fun lnextl' :: "hf set \<Rightarrow> 'a list \<Rightarrow> hf set" where
  "lnextl' Q []     = Q"
| "lnextl' Q (x#xs) = lnextl' (\<Union>q \<in> Q. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))}) xs"


text\<open>Relationship of lnextl' and Power.nextl\<close>
lemma nextl_cond_eq: "q \<subseteq> nfa.states Power_nfa \<Longrightarrow> lnextl' q as = Power.nextl q as"
proof (induction as arbitrary: q)
  case Nil
  then show ?case by (simp add: neps)
next
  case (Cons a as)
  have h1: "(\<Union>q\<in>q. {HF Q' |Q'.
                 Q' \<subseteq> states M \<and>
                 (\<exists>Qsl. set Qsl = hfset q \<and>
                        distinct Qsl \<and> models Q' (anded Qsl a))})
                = (\<Union>q\<in>q. nfa.nxt Power_nfa q a)" by (simp add: Power_nfa_def)
  have h2: "(\<Union>q\<in>Power.epsclo q. nfa.nxt Power_nfa q a) \<subseteq> nfa.states Power_nfa"
    using Cons.prems Power.nxt neps by auto
  have h3: "lnextl'
     (\<Union>q\<in>q. {HF Q' |Q'.
              Q' \<subseteq> states M \<and>
              (\<exists>Qsl. set Qsl = hfset q \<and> distinct Qsl \<and> models Q' (anded Qsl a))})
     as =
    Power.nextl (\<Union>q\<in>Power.epsclo q. nfa.nxt Power_nfa q a) as"
    using h1 Cons.IH(1)[OF h2]
    by (simp add: Cons.prems neps afa_axioms)
  show ?case using h3 by simp
qed


subsection\<open>Relationships between lnextl' and nxt_lvl_set_opt_ext_l\<close>

text\<open>A helper lemma\<close>
lemma cond_eq_helper: "(HF {}) \<notin> Q \<Longrightarrow> Q \<subseteq> (nfa.states Power_nfa) \<Longrightarrow> hfset ` (\<Union>q \<in> Q. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})
    = nxt_lvl_set_opt_ext (hfset ` Q) x"
proof -
  assume X: "(HF {}) \<notin> Q" and Y: "Q \<subseteq> (nfa.states Power_nfa)"
  have hpll1: "hfset ` (\<Union>q \<in> Q. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})
            =
              {qs'. \<exists>qs\<in> (hfset ` Q). ((qs \<noteq> {}) \<and> (qs \<subseteq> states M) \<and> (qs' \<subseteq> states M) \<and> (\<exists>qsl. ((set qsl = qs) \<and> (distinct qsl) \<and> models qs' (anded qsl x))))}"
  proof -
    have hpll16: "(\<Union>qs \<in> Q. {qs'. ((hfset qs \<noteq> {}) \<and> (hfset qs \<subseteq> states M) \<and> (qs' \<subseteq> states M) \<and> (\<exists>qsl. ((set qsl = hfset qs) \<and> (distinct qsl) \<and> models qs' (anded qsl x))))})
      = (\<Union>qs \<in> Q. {qs'. ((qs' \<subseteq> states M) \<and> (\<exists>qsl. ((set qsl = hfset qs) \<and> (distinct qsl) \<and> models qs' (anded qsl x))))})" 
      proof -
        have h1: "\<And>qs. (qs \<in> Q \<Longrightarrow> (hfset qs \<noteq> {}))" using X by (metis HF_hfset)
        have h2: "\<And>qs. (qs \<in> Q \<Longrightarrow> hfset qs \<subseteq> states M)"
          proof -
            fix qs
            show "(qs \<in> Q \<Longrightarrow> hfset qs \<subseteq> states M)"
              proof -
                assume a2: "qs \<in> Q"
                show ?thesis
                  using Power_nfa_def Y a2 hfset_HF local.finite mem_Collect_eq nfa.select_convs(1)
                    rev_finite_subset by force
              qed
          qed
          show ?thesis using h1 h2 X Y by simp
      qed
      have hpll11: "hfset ` (\<Union>q \<in> Q. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})
                = (\<Union>q \<in> Q. hfset ` {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})"
        by auto
      have hpll12: "(\<Union>q \<in> Q. hfset ` {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})
                = (\<Union>q \<in> Q. {hfset (HF Q') | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})"
        by auto
      have hpll13: "(\<Union>q \<in> Q. {hfset (HF Q') | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})
                = (\<Union>q \<in> Q. {Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})"
        proof -
          have "\<And>q. ({hfset (HF Q') | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))}
              = {Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl x))))})"
            by (metis finite_subset hfset_HF local.finite)
          then show ?thesis by simp
        qed
        have hpll14: "{qs'. \<exists>qs\<in> (hfset ` Q). ((qs \<noteq> {}) \<and> (qs \<subseteq> states M) \<and> (qs' \<subseteq> states M) \<and> (\<exists>qsl. ((set qsl = qs) \<and> (distinct qsl) \<and> models qs' (anded qsl x))))}
              =
              (\<Union>qs \<in> (hfset ` Q). {qs'. ((qs \<noteq> {}) \<and> (qs \<subseteq> states M) \<and> (qs' \<subseteq> states M) \<and> (\<exists>qsl. ((set qsl = qs) \<and> (distinct qsl) \<and> models qs' (anded qsl x))))})"
          by blast
        show ?thesis using hpll16 hpll14 hpll13 hpll12 hpll11 X Y by auto
      qed
      show ?thesis using hpll1 X Y by simp
    qed

lemma cond_eq1: "(HF {}) \<notin> qs \<Longrightarrow> qs \<subseteq> nfa.states Power_nfa \<Longrightarrow> x \<in> lnextl' qs as \<Longrightarrow> hfset x \<in> (nxt_lvl_set_opt_ext_l (hfset ` qs) as)"
proof (induction as arbitrary: qs x)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case 
  proof -
    assume A: "(\<And>qs x.
        HF {} \<notin> qs \<Longrightarrow>
        qs \<subseteq> nfa.states Power_nfa \<Longrightarrow>
        x \<in> lnextl' qs as \<Longrightarrow> hfset x \<in> nxt_lvl_set_opt_ext_l (hfset ` qs) as)"
      and B: "HF {} \<notin> qs" and C: "qs \<subseteq> nfa.states Power_nfa" and D: "x \<in> lnextl' qs (a # as)"
    
    have h1: "HF {} \<notin> HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)"
      using no_mt[of "(hfset ` qs)" a] elemfin' cond_fin
      by (metis Zero_hf_def chainhf hfset_0 image_eqI)
    have h21: "\<forall>x\<in>(nxt_lvl_set_opt_ext (hfset ` qs) a). x \<subseteq> states M"
      by auto
    then have h2: "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)) \<subseteq> (nfa.states Power_nfa)"
      using Power_nfa_def by auto
    have h3: "HF {} \<notin> HF ` nxt_lvl_set_opt_ext (hfset ` qs) a \<Longrightarrow>
  HF ` nxt_lvl_set_opt_ext (hfset ` qs) a \<subseteq> nfa.states Power_nfa \<Longrightarrow>
  x \<in> lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as \<Longrightarrow>
  hfset x \<in> nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using A[of "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a))" x] by blast
    have h4: "x \<in> (lnextl' (\<Union>q \<in> qs. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl a))))}) as)"
      using Cons.prems(3) lnextl'.simps(2) by blast
    have h5: "(HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) =
              (\<Union>q \<in> qs. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl a))))})"
      using cond_eq_helper[OF B C] althf
      by (metis (lifting)) 
    have h6: "x \<in> lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using h4 h5 by presburger
    show ?thesis using h3[OF h1 h2 h6]
      by (metis (no_types, lifting) B C cond_eq_helper althf nxt_lvl_set_opt_ext_l.simps(2))
  qed
qed


lemma cond_eq2: "(HF {}) \<notin> qs \<Longrightarrow> qs \<subseteq> nfa.states Power_nfa \<Longrightarrow> hfset x \<in> (nxt_lvl_set_opt_ext_l (hfset ` qs) as) \<Longrightarrow> x \<in> lnextl' qs as"
proof (induction as arbitrary: qs x)
  case Nil
  then show ?case
    using HF_hfset
    by (metis image_iff lnextl'.simps(1) nxt_lvl_set_opt_ext_l.simps(1))
next
  case (Cons a as)
  then show ?case
  proof -
    assume A: "(\<And>qs x.
        HF {} \<notin> qs \<Longrightarrow>
        qs \<subseteq> nfa.states Power_nfa \<Longrightarrow>
        hfset x \<in> nxt_lvl_set_opt_ext_l (hfset ` qs) as \<Longrightarrow> x \<in> lnextl' qs as)" and
    B: "HF {} \<notin> qs" and C: "qs \<subseteq> nfa.states Power_nfa" and D: "hfset x \<in> nxt_lvl_set_opt_ext_l (hfset ` qs) (a # as)"
    have h1: "HF {} \<notin> HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)"
      using no_mt[of "(hfset ` qs)" a] elemfin' cond_fin 
      by (metis Zero_hf_def chainhf hfset_0 image_eqI)
    have h21: "\<forall>x\<in>(nxt_lvl_set_opt_ext (hfset ` qs) a). x \<subseteq> states M"
      by auto
    then have h2: "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a)) \<subseteq> (nfa.states Power_nfa)"
      using Power_nfa_def by auto
    have h3: "HF {} \<notin> HF ` nxt_lvl_set_opt_ext (hfset ` qs) a \<Longrightarrow>
  HF ` nxt_lvl_set_opt_ext (hfset ` qs) a \<subseteq> nfa.states Power_nfa \<Longrightarrow>
  hfset x \<in> nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as
  \<Longrightarrow> x \<in> lnextl' (HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using A[of "(HF ` (nxt_lvl_set_opt_ext (hfset ` qs) a))" x] by blast
    have h4: "hfset x \<in> nxt_lvl_set_opt_ext_l (nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using D nxt_lvl_set_opt_ext_l.simps(2) by blast
    have h5: "(HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) =
              (\<Union>q \<in> qs. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl a))))})"
      using cond_eq_helper[OF B C] althf
      by (metis (lifting))
    have h6: "hfset x \<in> nxt_lvl_set_opt_ext_l (hfset ` (\<Union>q \<in> qs. {HF Q' | Q'. ((Q' \<subseteq> (states M)) \<and> (\<exists>Qsl. ((set Qsl = hfset q) \<and> (distinct Qsl) \<and> models Q' (anded Qsl a))))})) as"
      using B C h4 cond_eq_helper by presburger
    have h7: "hfset x \<in> nxt_lvl_set_opt_ext_l (hfset ` HF ` nxt_lvl_set_opt_ext (hfset ` qs) a) as"
      using h6 h5 by argo
    show ?thesis using h3[OF h1 h2 h7] h5 by fastforce
  qed
qed



subsection\<open>Some helper lemmas\<close>

lemma langs_innerset_eq_help1: "(HF {}) \<notin> qs \<Longrightarrow> qs \<subseteq> nfa.states Power_nfa \<Longrightarrow> x \<in> (nxt_lvl_set_opt_ext_l (hfset ` qs) as) \<Longrightarrow> HF x \<in> lnextl' qs as"
  by (simp add: cond_eq2 elem_fin)


lemma langs_innerset_eq_help2: "x \<in> nxt_lvl_set_opt_ext_l {{init M}} xs \<Longrightarrow> x \<in> hfset ` (lnextl' (nfa.init Power_nfa) xs)"
proof -
  assume A: "x \<in> nxt_lvl_set_opt_ext_l {{init M}} xs"
  have llc3z: "\<And>y. (hfset y \<in> nxt_lvl_set_opt_ext_l {{init M}} xs \<Longrightarrow> y \<in> (lnextl' (nfa.init Power_nfa) xs))"
    using Power.init Power_nfa_def cond_eq2 nfa_init by auto
  have h1: "HF x \<in> lnextl' (nfa.init Power_nfa) xs" using langs_innerset_eq_help1[OF nfa_init] A
    by (simp add: elem_fin llc3z)
  show ?thesis using h1 A elem_fin afa_axioms hfset_HF by blast
qed


lemma langs_secondset_eq: "hfset ` (nfa.final Power_nfa) = {Q. Q \<subseteq> final M}"
proof -
  have hpfin121': "\<And>Q. (Q \<subseteq> final M \<Longrightarrow> finite Q)"
    by (meson final finite_subset local.finite)
  have hpfin12: "hfset ` HF ` {Q. Q \<subseteq> final M} = {Q. Q \<subseteq> final M}"
    by (simp add: chainhf hpfin121')
  have h1: "hfset ` {HF Q |Q. Q \<subseteq> final M} = {Q. Q \<subseteq> final M}"
    using Set.setcompr_eq_image hpfin12 by metis
  show ?thesis by (simp add: Power_nfa_def h1)
qed

lemma langs_innerset_eq: "nxt_lvl_set_opt_ext_l {{init M}} xs = hfset ` (Power.nextl (nfa.init Power_nfa) xs)"
proof -
  have llc2: "hfset ` (lnextl' (nfa.init Power_nfa) xs) \<subseteq> nxt_lvl_set_opt_ext_l {{init M}} xs"
    using cond_eq1[OF nfa_init]
    using Power.init Power_nfa_def by auto
  have llc3'': "nxt_lvl_set_opt_ext_l {{init M}} xs \<subseteq> hfset ` (lnextl' (nfa.init Power_nfa) xs)"
    using langs_innerset_eq_help1[OF nfa_init]
    using langs_innerset_eq_help2 by blast
  show ?thesis using Power.init nextl_cond_eq set_eq_subset llc2 llc3'' subset_antisym by metis
qed




text\<open>The main theorem\<close>
text\<open>Power_nfa accepts the same language as the afa.\<close>
theorem Power_language: "Power.language = lang"
proof -
  have fin: "Power.language \<subseteq> langalt"
    unfolding Power.language_def langalt_def using langs_innerset_eq langs_secondset_eq by fast
  have finr: "langalt \<subseteq> Power.language"
    proof -
      have hpfinr: "\<And>as. (nxt_lvl_set_opt_ext_l {{init M}} as \<inter> Pow(final M) =
                   hfset ` (Power.nextl (nfa.init Power_nfa) as \<inter> nfa.final Power_nfa))"
        unfolding Pow_def using langs_innerset_eq langs_secondset_eq HF_hfset
          by (metis image_Int inj_on_def)
      show ?thesis unfolding Power.language_def langalt_def
        by (simp add: hpfinr)
    qed
  show ?thesis using fin finr langeq1 langeq2 by order
qed

end

end
