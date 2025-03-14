theory chomsky_schuetzenberger
  imports  "../CFG" "../CFL"
begin

text \<open>This file contains all the constructions needed for the chomsky-schuetzenberger theorem.
We follow closely Automata and Computability @1997 pp 198–200 by Dexter C. Kozen for the proof.

This theorem roughly states, that each type 2 language \<open>L\<close> can be written as 
\<open>h(R \<inter> dyck_lang(\<Gamma>))\<close> for suitable alphabet Gamma, a regular language R, and a monoid-homomorphism h.


The dyck language over some set \<open>\<Gamma>\<close> (also called bracket language) is defined as follows:  
The symbols of Gamma are thought of as opening brackets. 
For each symbol a closing bracket is added.
The dyck language over Gamma then is the language of correctly bracketed terms.

We implement this cloning of Gamma, by pairing each element \<open>g \<in> \<Gamma>\<close> either with an Element from
\<open>datatype bracket = Op | Cl\<close>, as in \<open>Cl, g\<close>.


A (very) rough proof overview of chomsky-schuetzenberger is as follows:
Take some type 2 Grammar for \<open>L\<close> with Productions \<open>P\<close>, assume it in Chomsky normal form.
From the old Productions \<open>P\<close> define new Productions \<open>P'\<close> using \<open>transform_production\<close>: 
if \<open>\<pi> = A \<rightarrow> BC\<close>  let \<open>\<pi>' = A \<rightarrow> [\<^sub>\<pi>\<^sup>1  B  ]\<^sub>p\<^sup>1  [\<^sub>\<pi>\<^sup>2  C  ]\<^sub>p\<^sup>2\<close>
elif \<open>\<pi> = A \<rightarrow> a\<close> let \<open>\<pi>' = A \<rightarrow> [\<^sub>\<pi>\<^sup>1     ]\<^sub>p\<^sup>1  [\<^sub>\<pi>\<^sup>2     ]\<^sub>p\<^sup>2\<close>
\<open>B\<close> and \<open>C\<close> on the right side, are again viewed as Nonterminals,
the brackets \<open>[\<^sub>\<pi>\<^sup>1\<close> are terminals. This means, we need a second copy of each production, 
and then pair these with brackets for the non-terminal type - 
\<open>bracket \<times> (old prod. type \<times> (type of ){1,2})\<close>

This bracketing encodes the parse tree of any old expression in the word-output, and it turns out one can recover the old word by the homomorphism \<open>h\<close>, which sends \<open>[\<^sub>\<pi>\<^sup>1\<close> to \<open>a\<close> if \<open>\<pi> = A \<rightarrow> a\<close>, and sends every other bracket to \<open>\<epsilon>\<close>.

Thus \<open>h(L') = L\<close> (*), so all we need to show is, that L' is of the form \<open>R \<inter> dyck_language \<Gamma>\<close>.

\<open>R\<^sub>A\<close> is defined via an intersection of 5 regular languages. Each of these is defined via a property of words (actually the fith one has an additional parameter, a variable of the old kind) which is chosen to be the start symbol, so \<open>R := R\<^sub>S\<close> (**).

We take the easiest \<open>\<Gamma>\<close> one can imagine with the right type: \<open>\<Gamma> = P \<times> {1,2}\<close>.

One then shows \<open>A \<rightarrow>\<^sub>G\<^sub>'\<^sup>* x \<longleftrightarrow> x \<in> R\<^sub>A \<inter> dyck_language \<Gamma>\<close>. (***) This is where the main work of the proof goes into.
Using this then for the old start symbol S gives the desired equation \<open>L' = R \<inter> dyck_language \<Gamma>\<close>
\<close>



text\<open>What is done and what is missing:

The equation in (*) should be an easy induction on the derivation - it's missing. If one looks closer we need an extended version of \<open>h\<close> that can also be applied on variables - we defined this as \<open>h_ext\<close>. We showed that this does basically the same as \<open>h\<close> on the terminals (modulo the Tm operators ...) in \<open>h_ext (map Tm x) = map Tm (h x)\<close>. Presumably one can do the induction with \<open>h_ext\<close> and then reduce this to a result for \<open>h\<close>.

The definition of what it means to be a regular language is a placeholder - it's a straight up copy of the type 2 definition. One needs to show that the intersection of regulars is regular and that the \<open>R\<^sub>A\<close> are regular. This is missing. The textbook says that regular expressions might be a good entry point for this - these are also already formalized in the AFP. Also one should check the formalization of the 5 properties again - these might be right, but i didn't spend any time on them, as they are not really used yet, they are needed for the lemma in the next paragraph. Maybe they also can be formulated with less index-bound checking.

The Lemma (***) is missing. This is the main mathematics of the proof, it involes one easy direction and one hard. This is the only part where one needs the definitions of the regular languages. In the textbook this is a (local) lemma.\<close>




declare [[names_short]]


fun strip_tm :: "('a, 'b) sym  \<Rightarrow> 'b" where 
  \<open>strip_tm (Tm t) = t\<close> | 
  \<open>strip_tm (Nt A) = undefined\<close>




definition reg :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
  "reg (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> True) " (*TODO add type 3 stuff here*)               



text\<open>A type of brackets. Will be combined with other types.\<close>
datatype bracket = Op | Cl

datatype version = One | Two



abbreviation open_bracket1 :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("[\<^sub>_\<^sup>1 ") where
  "[\<^sub>p\<^sup>1  \<equiv> (Op, (p, One))"

abbreviation close_bracket1 :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("]\<^sub>_\<^sup>1") where
  "]\<^sub>p\<^sup>1 \<equiv> (Cl, (p, One))"

abbreviation open_bracket2 :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("[\<^sub>_\<^sup>2") where
  "[\<^sub>p\<^sup>2 \<equiv> (Op, (p, Two))"

abbreviation close_bracket2 :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("]\<^sub>_\<^sup>2") where
  "]\<^sub>p\<^sup>2 \<equiv> (Cl, (p, Two))"





text\<open>definition of what it means to be a balanced string with letters of type \<open>bracket \<times> ('a)\<close> \<close>
inductive balanced :: "(bracket  \<times> ('a)) list \<Rightarrow> bool" where
  empty[intro]: "balanced []" |
  pair[intro]: "balanced xs \<Longrightarrow> balanced ((Op, g) # xs @ [(Cl, g)])" |
  concat[intro]: "balanced xs \<Longrightarrow> balanced ys \<Longrightarrow> balanced (xs @ ys)"

text\<open>The bracket language over a set R. Every element r \<in> R will get a Closing and an Opening version of itself, via pairing with the type bracket. We later need D := dyck_language ((Prods G) \<times> {1,2})\<close>

definition dyck_language :: "'a set \<Rightarrow> (bracket  \<times> ('a)) list set" where
  "dyck_language R = {w. (balanced w) \<and> (\<forall>(br,r) \<in> (set w). r \<in> R)}"

text\<open>balanced strings of brackets that may contain arbitrary interspersion of Nonterminals\<close>
inductive balanced_terminals :: "('n, bracket  \<times> ('a)) syms \<Rightarrow> bool" where
  empty[intro]: "balanced_terminals []" |
  Nt[intro]: "balanced_terminals [Nt A]" |
  pair[intro]: "balanced_terminals xs \<Longrightarrow> balanced_terminals (Tm (Op, g) # xs @ [Tm (Cl, g)])" |
  concat[intro]: "balanced_terminals xs \<Longrightarrow> balanced_terminals ys \<Longrightarrow> balanced_terminals (xs @ ys)"


lemma balanced_terminals_append_Nt[intro]: \<open>balanced_terminals xs \<Longrightarrow> balanced_terminals ([Nt A] @ xs)\<close>
proof-
assume xs_balanced: \<open>balanced_terminals xs\<close>
have \<open>balanced_terminals [Nt A]\<close> by auto
then show \<open>balanced_terminals ([Nt A] @ xs)\<close> using concat xs_balanced by blast
qed





lemma map_Tm_inject: "map Tm xs = map Tm ys \<Longrightarrow> xs = ys"
  by (induction xs arbitrary: ys; auto)


lemma split_tm_append: \<open>xs @ ys = map Tm zs \<Longrightarrow> \<exists> xs' ys'. (xs' @ ys' = zs) \<and> (xs = map Tm xs') \<and> (ys = map Tm ys')\<close>
by (metis append_eq_map_conv)


lemma balanced_imp_balanced_terminals: \<open>balanced xs \<Longrightarrow> balanced_terminals (map Tm xs)\<close>
by(induction xs rule: balanced.induct; auto)


lemma balanced_terminals_imp_balanced_for_tms: \<open>balanced_terminals (map Tm xs') \<Longrightarrow> balanced xs'\<close>
proof-
assume assm: \<open>balanced_terminals (map Tm xs':: ('a, bracket \<times> 'b) sym list)\<close>
define xs::\<open>('a, bracket \<times> 'b) sym list\<close> where \<open>xs = map Tm xs'\<close> \<comment> \<open>need to enforce the same non-terminal type for xs as for map Tm xs' ...\<close>
then have \<open>balanced_terminals xs\<close> using xs_def assm by simp

from \<open>balanced_terminals xs\<close> \<open>xs = map Tm xs'\<close> show ?thesis
proof(induction xs arbitrary: xs' rule: balanced_terminals.induct)
  case (pair xs g)
  obtain xs'' where \<open>xs = map Tm xs''\<close> and \<open>xs' = ((Op, g) # (xs'') @ [(Cl, g)])\<close> using split_tm_append local.pair.prems by blast
  then have \<open>balanced xs''\<close> by (simp add: local.pair.IH)
  then have \<open>balanced ((Op, g) # (xs'') @ [(Cl, g)])\<close> by auto
  then show ?case by (simp add: \<open>xs' = (Op, g) # xs'' @ [(Cl, g)]\<close>)
next
  case (concat xs ys)
  then show ?case by (metis chomsky_schuetzenberger.balanced.concat split_tm_append)
qed auto
qed










































































text\<open>TODO mv?\<close>
lemma list_length_1_imp_ex: \<open>length l = 1 \<Longrightarrow> \<exists>x. l = [x]\<close> apply auto by (simp add: length_Suc_conv)


lemma list_length_2_imp_ex: \<open>length l = 2 \<Longrightarrow> \<exists>x y. l = [x, y]\<close>
by(induction l; use list_length_1_imp_ex in auto)







  


















lemma balanced_terminals_split: \<open>balanced_terminals (xs@ys) \<Longrightarrow> balanced_terminals xs \<Longrightarrow> balanced_terminals ys\<close> using stk_balanced_split by auto


lemma \<open>balanced_terminals (u @ [Nt A] @ v) \<Longrightarrow> balanced_terminals w \<Longrightarrow> balanced_terminals (u @ w @ v)\<close>
proof(induction \<open>u @ [Nt A] @ v\<close> arbitrary: u v rule: balanced_terminals.induct)
  case empty
  then show ?case by simp
next
  case (Nt A)
  then have \<open>u =  []\<close> and \<open>v = []\<close> apply (simp add: Cons_eq_append_conv) by (metis (no_types, lifting) List.list.distinct(1) Nil_is_append_conv append_eq_Cons_conv local.Nt.hyps)
  then show ?case by (simp add: local.Nt.prems)
next
  case (pair xs g)

  have \<open>length u > 0 \<and> length v > 0\<close> by(rule ccontr, cases \<open>length u = 0\<close>; (use pair in auto))
  then have \<open>length u > 0\<close> and \<open>length v > 0\<close> by simp+
  then obtain u' where \<open>[Tm (Op, g)] @ u' = u\<close> by (metis Cons_eq_append_conv eq_Nil_appendI length_0_conv less_irrefl_nat local.pair.hyps(3))
  define v' where \<open> v' = take (length v -1) v\<close>
  then have \<open>take (length v -1) v @ [v ! (length v -1)] = v\<close> using \<open>0 < length v\<close> by (metis Orderings.preorder_class.order.refl Suc_diff_1 lessI take_Suc_conv_app_nth take_all)

  moreover have \<open>v ! (length v -1) = Tm (Cl, g)\<close> by (metis (no_types, lifting) List.last.simps append_is_Nil_conv calculation last_appendR local.pair.hyps(3) not_Cons_self2)
  ultimately have \<open>v' @ [Tm (Cl, g)] = v\<close> using v'_def by argo
  then have \<open>xs = u' @ [Nt A] @ v'\<close> using pair(3) using \<open>[Tm (Op, g)] @ u' = u\<close> by force
  then have \<open>balanced_terminals (u' @ w @ v')\<close> by (simp add: local.pair.hyps(2) local.pair.prems)
  then have \<open>balanced_terminals ([Tm (Op, g)] @ (u' @ w @ v') @ [Tm (Cl, g)])\<close> using chomsky_schuetzenberger.balanced_terminals.pair by force
  then show ?case using \<open>[Tm (Op, g)] @ u' = u\<close> \<open>v' @ [Tm (Cl, g)] = v\<close> by force
next
  case (concat xs ys)
  then show ?case
  proof(cases \<open>length xs \<ge> length u + 1\<close>)
    case True
    have \<open>xs @ ys = u @ [Nt A] @ v\<close> using concat by simp
    with True obtain v' where \<open>xs = (u @ [Nt A]) @ v'\<close> by (metis List.append.assoc[of u "[Nt A]" "v @ drop (Suc (length u)) xs"] List.append.assoc[of u "[Nt A] @ v" "drop (Suc (length u)) xs"] List.append.assoc[of xs ys "drop (Suc (length u)) xs"] List.append.assoc[of "[Nt A]" v "drop (Suc (length u)) xs"] Suc_eq_plus1[of "length u"] append_eq_append_conv_if[of "u @ [Nt A]" "v @ drop (Suc (length u)) xs" xs "ys @ drop (Suc (length u)) xs"] append_take_drop_id[of "Suc (length u)" xs] length_append_singleton[of u "Nt A"])
    then have \<open>balanced_terminals (u @ w @ v')\<close> using List.append.assoc local.concat.hyps(2) local.concat.prems by blast
    then show ?thesis using \<open>xs = (u @ [Nt A]) @ v'\<close> chomsky_schuetzenberger.balanced_terminals.concat local.concat.hyps(3,5) by fastforce
  next
    case False
    then show ?thesis sorry
  qed
qed















text\<open>The transformation of old productions to new productions used in the proof.\<close>
fun transform_production :: "('n, 't) prod \<Rightarrow> 
('n, bracket \<times> ('n,'t) prod \<times> version) prod" where
  \<open>  transform_production (A, [Nt B, Nt C]) =    
        (A, [ Tm (Op, ((A, [Nt B, Nt C]), One)), Nt B, Tm (Cl, ((A, [Nt B, Nt C]), One)), Tm (Op, ((A, [Nt B, Nt C]), Two)), Nt C, Tm (Cl, ((A, [Nt B, Nt C]), Two))  ])\<close> | 

\<open> transform_production (A, [Tm a])  = 
 (A, [ Tm (Op, ((A, [Tm a]),One)),       Tm (Cl, ((A, [Tm a]), One)), Tm (Op, ((A, [Tm a]), Two)),       Tm (Cl, ((A, [Tm a]), Two))  ]) \<close> | 
\<open>transform_production (A, _) = (A, [])\<close>


lemma transform_production_induct:
  \<open>\<lbrakk>\<And>B C. P ([Nt B, Nt C]); 
\<And>a. P ([Tm a]); P ([]); 
\<And>vb v vc. P (Tm vb # v # vc); 
\<And>va. P ([Nt va]); 
\<And>v vd vc. P (v # Tm vd # vc); 
\<And>v vb vd ve. P (v # vb # vd # ve)\<rbrakk> 
\<Longrightarrow> P a0\<close>
  by (metis CFG.sym.exhaust List.list.exhaust)


lemma fst_transform_production[simp]: \<open>fst (transform_production (A, w)) = A\<close>
  by(induction rule: transform_production_induct;auto)    

(* 
text\<open>The transformation of old productions to new productions used in the proof.\<close>
definition transform_production :: "('n, 't) prod \<Rightarrow> 
('n, bracket \<times> ('n,'t) prod \<times> version) prod" where
  "transform_production p = (
    case p of
      (A, [Nt B, Nt C]) \<Rightarrow> 
        (A, [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ]) | 
      (A, [Tm a]) \<Rightarrow>   
        (A, [ Tm (Op, (p,One)),       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ]) 
)"*)




text\<open>Definition of what it means to be a chomksy-form rule.\<close>
definition CNF_rule :: "('c \<times> ('c, 'b) sym list) \<Rightarrow> bool" where
  \<open>CNF_rule p \<equiv>  (\<exists>(A::'c) B C. (p = (A,[Nt B, Nt C]))) \<or> (\<exists>A a. p= (A, [Tm a]))\<close>


lemma transform_production_CNF: \<open>CNF_rule p \<Longrightarrow> (\<exists>A B C. transform_production p = (A, [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ]) ) \<or> (\<exists>A a. transform_production p = (A, [ Tm (Op, (p,One)),       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ]))\<close>
  unfolding CNF_rule_def by auto

lemma transform_production_CNF2: \<open>CNF_rule p \<Longrightarrow> transform_production p = (x, []) \<Longrightarrow> False\<close>
  unfolding CNF_rule_def by auto




lemma transform_production_induct_cnf:
  assumes \<open>CNF_rule p\<close>
    and \<open>\<And>A B C. Q (transform_production (A, [Nt B, Nt C])) (A, [Nt B, Nt C])\<close>
    and \<open>\<And>A a. Q (transform_production (A, [Tm a])) (A, [Tm a])\<close>
  shows \<open>Q (transform_production p) p\<close>
  using assms CNF_rule_def by metis





text\<open>Existence of chomsky normal form. Doesn't forbid the start symbol on the right though, so it's techinally even weaker.\<close>
lemma CNF_existence :
  assumes \<open>CFL.cfl TYPE('a) L\<close>
  shows \<open>\<exists>P S::'a. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> (* TODO start symbol not on the right side*)
  sorry

text\<open> (Directly) After each (Cl,p,1) always comes a (Op,p,2) \<close>
definition P1 :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list \<Rightarrow> bool\<close> where
  \<open>P1 P x = (\<forall>p \<in> P. \<forall> i < length x.
  x ! i = ]\<^sub>p\<^sup>1  \<longrightarrow> ( i+1 < length x \<and> x ! (i+1) = [\<^sub>p\<^sup>2 ))\<close>

text\<open>After any (Cl,pi,2) there never comes an (Op,...)\<close>
definition P2 :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list \<Rightarrow> bool\<close> where
  \<open>P2 P x = (\<forall>p \<in> P. \<forall>r. (\<forall>i j. i < length x \<and> j < length x \<and> i < j \<and> x ! i = ]\<^sub>p\<^sup>2  \<longrightarrow> x ! j \<noteq> (Op, r)))\<close>

text\<open>If pi = A\<rightarrow>BC, then after each (Op,pi,1) always comes a (Op,p,1) where B = lhs of p And after each (Op,pi,2) always comes a (Op,sigma,1) where C = lhs of sigma\<close>
definition P3 :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list \<Rightarrow> bool\<close> where
  \<open>P3 x = (\<forall>i < length x. 
       (\<exists>A B C. x ! i = (Op, ((A, [Nt B, Nt C]), One)) \<longrightarrow> 
          ((i+1) < length x \<and> (\<exists>p l. x ! (i+1) = [\<^sub>p\<^sup>1  \<and> p = (B, l)))) \<and>
       (\<exists>A B C. x ! i = (Op, ((A, [Nt B, Nt C]), Two)) \<longrightarrow> 
          ((i+1) < length x \<and> (\<exists>\<sigma> l. x ! (i+1) = (Op, (\<sigma>, One)) \<and> \<sigma> = (C, l)))))\<close>


text\<open>If pi = A\<rightarrow>a then after each (Op,pi,1) comes a (Cl,pi,1) and after each (Op,pi,2) comes a (Cl,pi,2)\<close>
definition P4 :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list \<Rightarrow> bool\<close> where
  \<open>P4 x = ((\<forall>i < length x - 1. 
        (\<exists>A a. x ! i = (Op, ((A, [Tm a]), One)) \<longrightarrow> x ! (i + 1) = (Cl, ((A, [Tm a]), One))) \<and>
        (\<exists>A a. x ! i = (Op, ((A, [Tm a]), Two)) \<longrightarrow> x ! (i + 1) = (Cl, ((A, [Tm a]), Two)))))\<close>

text\<open>For all A, if A produces x under P', then there eists some pi \<in> P with lhs A such that x begins with (Op,pi,1)\<close>
definition P5 :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> 'a \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list \<Rightarrow> bool\<close> where
  \<open>P5 P A x = (( (\<forall>w. derives (image transform_production P) [Nt A] w) \<longrightarrow> 
       (\<exists>\<pi> l. \<pi> \<in> P \<and> \<pi> = (A, l) \<and> x \<noteq> [] \<and> x ! 0 = (Op, \<pi>, One))))\<close>

text\<open>This is the regular language, where one takes the Start symbol as a parameter, and then has the searched for \<open>R := R\<^sub>A\<close>\<close>
definition Re :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> 'a \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list set\<close> where
  \<open>Re P A = {x::(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list. 
(P1 P x) \<and> (P2 P x) \<and> (P3 x) \<and> (P4 x) \<and> (P5 P A x)}\<close>


text\<open>Definition of monoid-homomorphism where multiplication is that of words.\<close>
definition hom :: \<open>('c list \<Rightarrow> 'd list) \<Rightarrow> bool\<close> where
  \<open>hom h = (\<forall>a b. h (a@b) = (h a) @ h (b))\<close>


text\<open>helper function for the definition of \<open>h\<close>\<close>
fun the_hom_helper :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) \<Rightarrow> 'b list\<close> where
  \<open>the_hom_helper (Op, ((A, [Tm a]), One)) = [a]\<close> | 
  \<open>the_hom_helper _ = []\<close> 



text\<open>helper function for the definition of the extended \<open>h_ext\<close>\<close>
fun the_hom_ext_helper :: \<open>('a, bracket \<times> ('a,'b) prod \<times> version ) sym \<Rightarrow> ('a,'b) sym list\<close> where
  \<open>the_hom_ext_helper (Tm (Op, ((A, [Tm a]), One))) = [Tm a]\<close> | 
  \<open>the_hom_ext_helper (Nt A) = [Nt A]\<close> | 
  \<open>the_hom_ext_helper _ = []\<close>



text\<open>The needed homomorphism in the proof\<close>
fun the_hom :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list \<Rightarrow> 'b list \<close> where
  \<open>the_hom l = concat (map the_hom_helper l)\<close>


text\<open>The needed homomorphism in the proof, but extended on Variables\<close>
fun the_hom_ext :: \<open>('a, bracket \<times> ('a,'b) prod \<times> version ) sym list \<Rightarrow> ('a,'b) sym list \<close> where
  \<open>the_hom_ext l = concat (map the_hom_ext_helper l)\<close>



lemma the_hom_ext_hom[simp]: \<open>the_hom_ext (l1 @ l2) = the_hom_ext l1 @ the_hom_ext l2\<close>
  by simp

lemma the_hom_ext_keep_var[simp] : \<open>the_hom_ext [(Nt A)] = [Nt A]\<close> by simp 

lemma the_hom_ext_helper_var_inj: \<open>the_hom_ext_helper r = [Nt A] \<Longrightarrow> r = Nt A\<close> 
  by(induction r rule: the_hom_ext_helper.induct;auto)

lemma the_hom_ext_var_inj: \<open>the_hom_ext [r] = [Nt A] \<Longrightarrow> r = Nt A\<close>
  using the_hom_ext_helper_var_inj by fastforce

lemma the_hom_ext_tm_inj: \<open>the_hom_ext [r] = [Tm m ]\<Longrightarrow> \<exists>x. r = Tm x\<close> by (metis CFG.sym.distinct(1) CFG.sym.exhaust List.list.inject the_hom_ext_keep_var)

lemma the_hom_ext_tms_inj: \<open>the_hom_ext w = map Tm m \<Longrightarrow> \<exists>w'. w = map Tm w'\<close> 
proof(induction w arbitrary: m)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then obtain w' where \<open>w = map Tm w'\<close> by (metis (no_types, opaque_lifting) append_Cons append_Nil map_eq_append_conv the_hom_ext_hom)
  then obtain a' where \<open>a = Tm a'\<close>
  proof -
    assume a1: "\<And>a'. a = Tm a' \<Longrightarrow> thesis"
    have f2: "\<forall>ss s. [s::('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym] @ ss = s # ss" by auto
    have "\<forall>ss s. (s::('a, 'b) sym) # ss = [s] @ ss" by simp
    then show ?thesis using f2 a1 by (metis CFG.sym.exhaust CFG.sym.simps(4) local.Cons.prems map_eq_Cons_D the_hom_ext_hom the_hom_ext_keep_var)
  qed
  then show \<open>\<exists>w'. a # w = map Tm w'\<close> by (metis List.list.simps(9) \<open>w = map Tm w'\<close>)
qed



lemma length_the_hom_ext_helper: \<open>length (the_hom_ext_helper w') \<le> 1\<close>
  apply simp
  by(induction w' rule: the_hom_ext_helper.induct;auto)

lemma length_the_hom_ext: \<open>length (the_hom_ext [x]) \<le> 1\<close>
  using length_the_hom_ext_helper by auto

lemma length_the_hom_ext_leq: \<open>length (the_hom_ext w') \<le> length w'\<close>
  using length_the_hom_ext apply(induction w';auto ) by (smt (verit) One_nat_def add_Suc add_mono gen_length_def length_code length_the_hom_ext_helper)



lemma [simp]: \<open>Nt A \<in> set (the_hom_ext [a]) \<Longrightarrow> a = Nt A\<close>
  by(induction a rule:the_hom_ext_helper.induct; auto)





lemma the_hom_ext_length_mono: \<open>k'' \<ge> k' \<Longrightarrow> length (the_hom_ext (take k'' w')) \<ge> length (the_hom_ext (take k' w'))\<close>
  using the_hom_ext_hom by (smt (verit, ccfv_threshold) Lattices.linorder_class.min.absorb_iff2 Lattices.linorder_class.min.bounded_iff append_eq_append_conv_if append_eq_conv_conj append_take_drop_id length_take nat_le_linear) 


lemma the_hom_ext_length_mono_inv: \<open>length (the_hom_ext (take k'' w')) > length (the_hom_ext (take k' w')) \<Longrightarrow> k'' > k'\<close>
  using the_hom_ext_length_mono by (metis linorder_not_le)


lemma take_append_split: \<open>k''\<ge> k' + r \<Longrightarrow> take k'' w' = (take k' w') @ diff \<Longrightarrow> take (k'+r) w' = take k' w' @ take r diff\<close> 
  by (smt (verit, ccfv_SIG) Groups.ordered_cancel_comm_monoid_diff_class.add_diff_inverse Lattices.linorder_class.min.absorb_iff2 append_eq_conv_conj length_take nat_le_linear take_add take_all_iff)


lemma letters_needed_until_produced_ex: \<open>n \<le> length (the_hom_ext w') \<Longrightarrow> \<exists>k. n = length (the_hom_ext (take k w'))\<close>
proof(induction w' arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a w')
  then show \<open>\<exists>k. n = length (the_hom_ext (take k (a # w')))\<close>
  proof(cases \<open>length (the_hom_ext [a]) = 0\<close>)
    case True
    then have \<open>the_hom_ext (a # w') = the_hom_ext w'\<close> by simp
    then show ?thesis by (metis List.append.simps(1,2) Nat.bot_nat_0.not_eq_extremum True length_greater_0_conv local.Cons.IH local.Cons.prems take_Suc_Cons the_hom_ext_hom)
  next
    case False
    then have len_a: \<open>length (the_hom_ext [a]) = 1\<close> using length_the_hom_ext using le_neq_implies_less by blast
    then have \<open>n-1 \<le> length (the_hom_ext w')\<close> using local.Cons.prems by simp
    with Cons obtain k' where k'_def: \<open>n-1 = length (the_hom_ext (take k' w'))\<close> by auto

    then have \<open>the_hom_ext (take (k' + 1) (a # w')) = the_hom_ext [a] @ the_hom_ext (take k' w')\<close> using the_hom_ext_hom by simp
    moreover have \<open>length (the_hom_ext [a] @ the_hom_ext (take k' w')) \<ge>  1 + n-1\<close> using len_a k'_def by simp

    ultimately show \<open>\<exists>k. n = length (the_hom_ext (take k (a # w')))\<close> by (metis (no_types, lifting) add_diff_assoc add_diff_cancel_left' diff_is_0_eq k'_def le_neq_implies_less len_a length_0_conv length_append less_one nat_le_linear take_eq_Nil2 the_hom_ext_hom)
  qed
qed




(* need how for one needs to go in the input to get n output tokens from the_hom_ext, implemented via LEAST *)
definition letters_needed_until_produced :: "nat \<Rightarrow> ('a, bracket \<times> ('a,'b) prod \<times> version ) sym list \<Rightarrow> nat" where
  \<open>letters_needed_until_produced n w' = (if n \<le> length (the_hom_ext w') then LEAST k. n = length (the_hom_ext (take k w')) else 0)\<close>

lemma letters_needed_until_produced_if_n[simp]: \<open>n \<le> length (the_hom_ext w') \<Longrightarrow> letters_needed_until_produced n w' = (LEAST k. n = length (the_hom_ext (take k w')))\<close> by (simp add: letters_needed_until_produced_def)

lemma letters_needed_until_produced_minimal: \<open>n \<le> length (the_hom_ext w') \<Longrightarrow> n = length (the_hom_ext (take k w')) \<Longrightarrow> letters_needed_until_produced n w' \<le> k\<close>
  unfolding letters_needed_until_produced_def by (simp add: Least_le)

lemma letters_needed_until_produced_correct: \<open>n \<le> length (the_hom_ext w') \<Longrightarrow> take n (the_hom_ext w') = the_hom_ext (take (letters_needed_until_produced n w') w')\<close>
proof-
  assume n_leq: \<open>n \<le> length (the_hom_ext w')\<close>
  define k where k_def: \<open>k = letters_needed_until_produced n w'\<close>
  have \<open>n = length (the_hom_ext (take k w'))\<close> unfolding letters_needed_until_produced_def using LeastI_ex[where P = \<open>\<lambda>k. n = length (the_hom_ext (take k w'))\<close>] letters_needed_until_produced_ex n_leq k_def by auto
  thus ?thesis by (metis append_eq_conv_conj append_take_drop_id k_def the_hom_ext_hom)
qed

lemma letters_needed_until_produced_pre: \<open>n + 1 \<le> length (the_hom_ext w') \<Longrightarrow> take n (the_hom_ext w')  = the_hom_ext (take ((letters_needed_until_produced (n+1) w') - 1) w')\<close>
proof-
  assume sucn_leq: \<open>n + 1 \<le> length (the_hom_ext w')\<close>
  then have n_leq: \<open>n \<le> length (the_hom_ext w')\<close> by simp
  define k where \<open>k = (letters_needed_until_produced (n+1) w')\<close>
  define k' where \<open>k' = (letters_needed_until_produced n w')\<close>
  then have \<open>take n (the_hom_ext w')  = the_hom_ext (take k' w')\<close> using letters_needed_until_produced_correct n_leq by blast
  then have \<open>k' \<le> k - 1\<close> by (metis (no_types, lifting) Groups.ordered_cancel_comm_monoid_diff_class.add_diff_inverse Lattices.linorder_class.min.absorb_iff2 Suc_eq_plus1 add_diff_cancel_left' diff_le_self k_def length_take letters_needed_until_produced_correct nat_le_linear not_less_eq_eq plus_1_eq_Suc sucn_leq the_hom_ext_length_mono)
  moreover have \<open>k - 1 < k\<close> by (metis Lattices.linorder_class.min.absorb_iff2 Nat.bot_nat_0.not_eq_extremum One_nat_def Suc_eq_plus1 \<open>take n (the_hom_ext w') = the_hom_ext (take k' w')\<close> calculation diff_Suc_less diff_is_0_eq diff_zero k_def length_take lessI letters_needed_until_produced_correct n_leq nat_less_le sucn_leq)
  ultimately have \<open>take n (the_hom_ext w')  = the_hom_ext (take (k-1) w')\<close> using k_def k'_def by (smt (verit, ccfv_threshold) Lattices.linorder_class.min.absorb_iff2 Suc_eq_plus1 append_eq_append_conv_if append_take_drop_id length_take letters_needed_until_produced_correct letters_needed_until_produced_minimal nat_less_le nle_le not_less_eq_eq sucn_leq the_hom_ext_hom the_hom_ext_length_mono)
  thus ?thesis using k_def by blast
qed

term \<open>([]::nat list) ! 1\<close>

lemma take_append_one[simp]: \<open>k + 1 \<le> length w' \<Longrightarrow> (take k w') @ [w' ! k] = take (Suc k) w'\<close> by (simp add: take_Suc_conv_app_nth)


lemma split_into_take: \<open>k \<le> length w' \<Longrightarrow> \<exists>r. w' = take (k) w' @ r\<close>
  by (metis append_take_drop_id)




lemma the_hom_ext_var_split: \<open>(map Tm u @ [Nt A] @ v) = the_hom_ext w' \<Longrightarrow> \<exists> u' v'. w' = map Tm u' @ [Nt A] @ v'\<close>
proof-
  define k where \<open>k = letters_needed_until_produced (length (map Tm u) + 1) w'\<close>
  define km where \<open>km = letters_needed_until_produced (length (map Tm u)) w'\<close>
  assume split: \<open>map Tm u @ [Nt A] @ v = (the_hom_ext w')\<close>
  then have \<open>length (map Tm u @ [Nt A] @ v) = length (the_hom_ext w')\<close> using split by simp
  then have length_u_leq: \<open>length (map Tm u) + 1 \<le> length (the_hom_ext w')\<close> by simp

  then have \<open>map Tm u = take (length (map Tm u)) (map Tm u @ [Nt A] @ v)\<close> by (simp add: append_eq_conv_conj)
  also have \<open>take (length (map Tm u)) (map Tm u @ [Nt A] @ v) = take (length (map Tm u)) (the_hom_ext w')\<close> using split by simp
  also have \<open>take (length (map Tm u)) (the_hom_ext w') =  the_hom_ext (take (k-1) w')\<close> using letters_needed_until_produced_pre[of \<open>length (map Tm u)\<close> \<open>w'\<close>] length_u_leq by (metis calculation k_def)
  finally have u_take: \<open>the_hom_ext (take (k-1) w') = map Tm u\<close> by simp


  then have \<open>map Tm u @ [Nt A] = take (length (map Tm u) + 1) (map Tm u @ [Nt A] @ v)\<close> by (simp add: append_eq_conv_conj)
  also have \<open>take (length (map Tm u) + 1) (map Tm u @ [Nt A] @ v) = take (length (map Tm u) + 1) (the_hom_ext w')\<close> using split by simp
  also have \<open>take (length (map Tm u) + 1) (the_hom_ext w') =  the_hom_ext (take k w')\<close>  using letters_needed_until_produced_correct[of \<open>length (map Tm u) + 1\<close> \<open>w'\<close>] length_u_leq  by (simp add: k_def)
  finally have uA_take: \<open>the_hom_ext (take k w') = map Tm u @ [Nt A]\<close> by simp

  have split2: \<open>take k w' = (take (k-1) w') @ [w' ! (k-1)]\<close> by (metis List.list.distinct(1) Suc_pred' append_self_conv gr0I less_imp_diff_less linorder_not_le take_Suc_conv_app_nth take_all uA_take u_take zero_diff)
  then have Nt: \<open>the_hom_ext ([w' ! (k-1)]) = [Nt A]\<close> using u_take uA_take the_hom_ext_hom the_hom_ext_var_inj by auto

  thus ?thesis using u_take Nt split2 
    by (metis (no_types, lifting) append_assoc append_take_drop_id the_hom_ext_tms_inj the_hom_ext_var_inj)
qed


lemma prefix_unique:
  assumes "xs @ [x] @ zs = ys @ [x] @ ws"
    and "x \<notin> set xs" and "x \<notin> set ys"
  shows "xs = ys"
proof (rule ccontr)
  assume "xs \<noteq> ys"
  from assms(1) have "length (xs @ [x] @ zs) = length (ys @ [x] @ ws)" by simp
  hence "length xs + 1 + length zs = length ys + 1 + length ws" by simp
  hence length_eq: "length xs + length zs = length ys + length ws" by simp

  show False
  proof (cases "length xs < length ys")
    case True
    then obtain k where k: "length ys = length xs + k" and "k > 0" by (metis less_imp_add_positive)

    then have \<open>x = (xs @ [x] @ ws) ! (length xs)\<close> by (metis append_Cons nth_append_length)
    also have \<open>... = (ys @ [x] @ ws) ! (length xs)\<close> using assms(1) by (metis Cons_eq_appendI nth_append_length) 
    also have \<open>... = (ys @ [x] @ ws) ! (length ys - k)\<close> by (simp add: k)
    finally have \<open>x = (ys @ [x] @ ws) ! (length ys - k)\<close> .
    then have \<open>x \<in> set ys\<close> by (metis True add_diff_cancel_right' k nth_append nth_mem)
    thus False by (simp add: assms(3))

  next
    case False

    then obtain k where k: "length xs = length ys + k" by (metis add_diff_inverse)
    then have \<open>k \<noteq> 0\<close> using \<open>xs \<noteq> ys\<close> by (metis Nat.add_0_right append_eq_append_conv assms(1))
    then have \<open>k > 0\<close> by simp

    then have \<open>x = (ys @ [x] @ ws) ! (length ys)\<close> by (metis append_Cons nth_append_length)
    also have \<open>... = (xs @ [x] @ ws) ! (length ys)\<close> using assms(1) by (metis \<open>0 < k\<close> k less_add_same_cancel1 nth_append_left)
    thus \<open>False\<close> by (metis \<open>(ys @ [x] @ ws) ! length ys = (xs @ [x] @ ws) ! length ys\<close> \<open>0 < k\<close> \<open>x = (ys @ [x] @ ws) ! length ys\<close> assms(2) in_set_conv_nth k less_add_same_cancel1 nth_append_left)

  qed
qed

lemma the_hom_ext_helper_Tm_explicit:
  "the_hom_ext_helper (Tm (a,(aa,b),ba)) =
   (if (a=Op \<and> ba=One \<and> (\<exists>r. b = [Tm r]))
    then b
    else [])"
  apply(cases a; cases ba; cases b rule: list.exhaust)
         apply auto
   apply (metis CFG.sym.exhaust chomsky_schuetzenberger.the_hom_ext_helper.simps(5))
  by (metis List.remdups_adj.cases chomsky_schuetzenberger.the_hom_ext_helper.simps(6))



lemma \<open>the_hom_ext_helper (Tm (a, (aa, b), ba)) = [] \<or> the_hom_ext_helper (Tm (a, (aa, b), ba)) = b\<close>
  using the_hom_ext_helper_Tm_explicit by metis


lemma Nt_the_hom_ext_helper: \<open>Nt A \<in> set (the_hom_ext_helper (Tm (a, (aa, b), ba))) \<Longrightarrow> False\<close>
  using the_hom_ext_helper_Tm_explicit by (metis CFG.sym.distinct(1) append_is_Nil_conv set_ConsD split_list_cycles)


lemma same_prefix:
  assumes eq:\<open>map Tm u @ [Nt A] @ v  =  (the_hom_ext (map Tm u')) @ [Nt A] @ (the_hom_ext v')\<close>
  shows \<open>(map Tm u) = (the_hom_ext (map Tm u'))\<close>
proof -
  have "Nt A \<notin> set (map Tm u)" by auto
  moreover have "Nt A \<notin> set (the_hom_ext (map Tm u'))" using Nt_the_hom_ext_helper by fastforce
  ultimately show ?thesis
    using eq prefix_unique by metis
qed




text\<open>helper for showing the next lemma\<close>
lemma helper: \<open>the_hom_ext_helper (Tm x) = map Tm (the_hom_helper x)\<close>
  apply(induction x rule: the_hom_helper.induct)
  by(auto split: list.splits sym.splits)

text\<open>Show that the extension really is an extension in some sense.\<close>
lemma h_eq_h_ext: \<open>the_hom_ext (map Tm x) = map Tm (the_hom x)\<close>
  apply(induction x)
   apply(simp)
  using helper by fastforce



lemma the_hom_helper_strip: \<open>map Tm w = (the_hom_ext_helper x') \<Longrightarrow> w = the_hom_helper (strip_tm x')\<close>
  by(induction x' rule: the_hom_ext_helper.induct; auto)

lemma concat_map_cons[simp]: \<open>concat (map f (a # w')) = f a @ concat ( map f w')\<close> by auto

lemma the_hom_helper_strip2: \<open>map Tm w = concat (map the_hom_ext_helper w') \<Longrightarrow> w = concat (map (the_hom_helper \<circ> strip_tm) w')\<close>
proof(induction w' arbitrary: w)
  case Nil
  then show ?case by simp
next
  case (Cons a w')
  then show ?case by (smt (verit, ccfv_threshold) comp_apply concat_map_cons map_eq_append_conv the_hom_helper_strip)
qed



lemma h_eq_h_ext2:
  assumes \<open>(map Tm w) = the_hom_ext w'\<close> 
  shows \<open>w = the_hom (map strip_tm w')\<close>
  using assms apply simp
  apply(induction w';auto) 
  by (smt (verit, ccfv_SIG) map_eq_append_conv the_hom_helper_strip the_hom_helper_strip2)


lemma hom_ext_inv[simp]: \<open>CNF_rule \<pi> \<Longrightarrow> the_hom_ext (snd (transform_production \<pi>)) = snd \<pi>\<close>
  apply(rule transform_production_induct_cnf )
  by auto


text\<open>rtrancl_derive_induct but for left derivation\<close>
lemma rtrancl_derivel_induct
  [consumes 1, case_names base step]:
  assumes "P \<turnstile> xs \<Rightarrow>l* ys"
    and "Q xs"
    and "\<And>u A v w. \<lbrakk> P \<turnstile> xs \<Rightarrow>l* (map Tm u @ [Nt A] @ v)
                   ; Q (map Tm u @ [Nt A] @ v)
                   ; (A,w) \<in> P \<rbrakk>
               \<Longrightarrow> Q (map Tm u @ w @ v)"
  shows "Q ys"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  from this(1) show ?case by simp
next
  case (step x y)
    \<comment> \<open>Here we know one step of derivation x \<Rightarrow>ˡ y plus xs \<Rightarrow>ˡ* x.\<close>
  from \<open>P \<turnstile> x \<Rightarrow>l y\<close> obtain A \<alpha> u v
    where \<open>x = map Tm u @ [Nt A] @ v\<close>
      and \<open>y = map Tm u @ \<alpha> @ v\<close>
      and \<open>(A, \<alpha>) \<in> P\<close>
    by (auto elim: derivel.cases)
  with step show ?case by simp
qed










section \<open>Derivation Witnesses\<close>
 (* TODO mv ? *)



  (* Record for a single derivation step *)
record ('n,'t) derivation_step =
  before :: "('n,'t) syms"       \<comment> \<open>the string before applying the step\<close>
  after :: "('n,'t) syms"        
  prod :: "('n,'t) prod"         \<comment> \<open>the production used in the step\<close>
  prefix :: "('n,'t) syms"       \<comment> \<open>in order to track where the production is used: before = prefix @ [Nt (fst prod)] @ suffix  (in a valid Derivation Sequence)\<close>
  suffix :: "('n,'t) syms"       


type_synonym ('n,'t) derivation = "('n,'t) derivation_step list"

(* The set of consistent derivations in P *)
definition DerSeqs :: "('n,'t) Prods \<Rightarrow> ('n,'t) derivation set" where
  "DerSeqs P = 
  {steps |steps.   
    (\<forall>i < length steps.
      let stepi = steps ! i in
      prod stepi \<in> P \<and>
      (i > 0 \<longrightarrow> before stepi = after (steps ! (i-1))) \<and>
      before stepi = prefix stepi @ [Nt (fst (prod stepi))] @ suffix stepi \<and>
      after stepi = prefix stepi @ snd (prod stepi) @ suffix stepi)
  }"


(* The set of derivation witnesses between u v in P *)
definition DerWits :: "('n,'t) Prods \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) derivation set" where
  "DerWits P u v = 
  {steps \<in> DerSeqs P. 
    (steps = [] \<and> u = v) \<or>  
    (steps \<noteq> [] \<and> before (hd steps) = u \<and> after (last steps) = v)}"








lemma DerSeqsI[intro]: 
  assumes \<open>\<And>i. i < length steps \<Longrightarrow> (prod (steps ! i) \<in> P) 
\<and> (i > 0 \<longrightarrow> before (steps ! i) = after (steps ! (i-1)))
\<and> (before (steps ! i) = prefix (steps ! i) @ [Nt (fst (prod (steps ! i)))] @ suffix (steps ! i)) 
\<and> (after (steps ! i) = prefix (steps ! i) @ snd (prod (steps ! i)) @ suffix (steps ! i))
\<close>
  shows \<open>steps \<in> DerSeqs P\<close> unfolding DerSeqs_def by (simp add: assms)



lemma DerSeqsD[dest]:
  assumes "steps \<in> DerSeqs P"
    and \<open>i < length steps\<close>
  shows in_prods: \<open>prod (steps ! i) \<in> P\<close> 
    and before_eq_next_after: \<open>i > 0 \<longrightarrow> before (steps ! i) = after (steps ! (i-1))\<close> 
    and before_splits: \<open>before (steps ! i) = prefix (steps ! i) @ [Nt (fst (prod (steps ! i)))] @ suffix (steps ! i)\<close> 
    and after_splits: \<open>after (steps ! i) = prefix (steps ! i) @ snd (prod (steps ! i)) @ suffix (steps ! i)\<close>
proof-
  have \<open>\<And>i. i < length steps \<Longrightarrow> (prod (steps ! i) \<in> P) 
\<and> (i > 0 \<longrightarrow> before (steps ! i) = after (steps ! (i-1)))
\<and> (before (steps ! i) = prefix (steps ! i) @ [Nt (fst (prod (steps ! i)))] @ suffix (steps ! i)) 
\<and> (after (steps ! i) = prefix (steps ! i) @ snd (prod (steps ! i)) @ suffix (steps ! i))
\<close> using assms unfolding DerSeqs_def mem_Collect_eq by meson

  then have 1:\<open>(prod (steps ! i) \<in> P) 
\<and> (i > 0 \<longrightarrow> before (steps ! i) = after (steps ! (i-1)))
\<and> (before (steps ! i) = prefix (steps ! i) @ [Nt (fst (prod (steps ! i)))] @ suffix (steps ! i)) 
\<and> (after (steps ! i) = prefix (steps ! i) @ snd (prod (steps ! i)) @ suffix (steps ! i))\<close> using assms(2) by blast

  from 1 show \<open>prod (steps ! i) \<in> P\<close> by simp
  from 1 show \<open>0 < i \<longrightarrow> before (steps ! i) = after (steps ! (i - 1))\<close> by auto
  from 1 show \<open>before (steps ! i) = prefix (steps ! i) @ [Nt (fst (prod (steps ! i)))] @ suffix (steps ! i)\<close> by simp
  from 1 show \<open>after (steps ! i) = prefix (steps ! i) @ snd (prod (steps ! i)) @ suffix (steps ! i)\<close> by simp
qed


lemma DerSeqsOneD[dest]:
  assumes "[step] \<in> DerSeqs P"
  shows in_prods_one: \<open>prod (step) \<in> P\<close> 
    and before_splits_one: \<open>before (step) = prefix (step) @ [Nt (fst (prod (step)))] @ suffix (step)\<close> 
    and after_splits_one: \<open>after (step) = prefix (step) @ snd (prod (step)) @ suffix (step)\<close>
  using DerSeqsD assms by fastforce+



lemmas DerSeqsE = DerSeqsD[elim_format]
lemmas DerSeqsOneE = DerSeqsOneD[elim_format]


(* Empty derivation is a derivation *)
lemma DerSeqs_emptyI[simp]:
  shows "[] \<in> DerSeqs P"
  by (simp add: DerSeqs_def)

(* A 1 step derivation is always a derivation *)
lemma DerSeqs_singleI[intro]:
  assumes "prod_rule \<in> P"
    and "u = prefix_str @ [Nt (fst prod_rule)] @ suffix_str"
    and "v = prefix_str @ snd prod_rule @ suffix_str"
  shows "[\<lparr>before = u, after = v, prod = prod_rule, 
          prefix = prefix_str, suffix = suffix_str\<rparr>] \<in> DerSeqs P"
  using assms by (auto simp: DerSeqs_def)





(* Extending a derivation with another one *)
lemma DerSeqs_appendI:
  assumes "steps1 \<in> DerSeqs P" "steps2 \<in> DerSeqs P"
  assumes "steps1 = [] \<or> steps2 = [] \<or> after (last steps1) = before (hd steps2)"
  shows "steps1 @ steps2 \<in> DerSeqs P"
proof (cases "steps1 = [] \<or> steps2 = []")
  case True
  then show ?thesis using assms(1,2) by fastforce
next
  case False
  then have "steps1 \<noteq> []" "steps2 \<noteq> []" by auto
  with assms(3) have connection: "after (last steps1) = before (hd steps2)" by simp

  show ?thesis
  proof (intro DerSeqsI)
    fix i
    assume i_lt: "i < length (steps1 @ steps2)"

    show "(prod ((steps1 @ steps2) ! i) \<in> P) \<and>
          (i > 0 \<longrightarrow> before ((steps1 @ steps2) ! i) = after ((steps1 @ steps2) ! (i - 1))) \<and>
          (before ((steps1 @ steps2) ! i) = prefix ((steps1 @ steps2) ! i) @ 
            [Nt (fst (prod ((steps1 @ steps2) ! i)))] @ suffix ((steps1 @ steps2) ! i)) \<and>
          (after ((steps1 @ steps2) ! i) = prefix ((steps1 @ steps2) ! i) @ 
            snd (prod ((steps1 @ steps2) ! i)) @ suffix ((steps1 @ steps2) ! i))"
    proof (cases "i < length steps1")
      case True
      then have idx: "(steps1 @ steps2) ! i = steps1 ! i" by (simp add: nth_append_left)

      from assms(1) True have properties:
        "prod (steps1 ! i) \<in> P \<and>
         (i > 0 \<longrightarrow> before (steps1 ! i) = after (steps1 ! (i - 1))) \<and>
         before (steps1 ! i) = prefix (steps1 ! i) @ [Nt (fst (prod (steps1 ! i)))] @ suffix (steps1 ! i) \<and>
         after (steps1 ! i) = prefix (steps1 ! i) @ snd (prod (steps1 ! i)) @ suffix (steps1 ! i)"
        using DerSeqsD by blast

      have consistency:
        "i > 0 \<longrightarrow> before ((steps1 @ steps2) ! i) = after ((steps1 @ steps2) ! (i - 1))"
      proof (cases "i > 0")
        case True
        then have "i - 1 < length steps1" using `i < length steps1` by auto
        then have "(steps1 @ steps2) ! (i - 1) = steps1 ! (i - 1)" by (simp add: nth_append_left)
        with idx show ?thesis using properties by argo
      qed simp

      show ?thesis using idx properties consistency by simp
    next
      case False
      with i_lt have "i \<ge> length steps1" "i < length steps1 + length steps2" by auto
      then have idx: "(steps1 @ steps2) ! i = steps2 ! (i - length steps1)" by (simp add: nth_append_right)

      from assms(2) have steps2_properties:
        "\<And>j. j < length steps2 \<Longrightarrow>
         prod (steps2 ! j) \<in> P \<and>
         (j > 0 \<longrightarrow> before (steps2 ! j) = after (steps2 ! (j - 1))) \<and>
         before (steps2 ! j) = prefix (steps2 ! j) @ [Nt (fst (prod (steps2 ! j)))] @ suffix (steps2 ! j) \<and>
         after (steps2 ! j) = prefix (steps2 ! j) @ snd (prod (steps2 ! j)) @ suffix (steps2 ! j)"
        using DerSeqsD by blast

      let ?j = "i - length steps1"
      have j_valid: "?j < length steps2" using `i < length steps1 + length steps2` by (simp add: \<open>length steps1 \<le> i\<close> less_diff_conv2)

      have consistency:
        "i > 0 \<longrightarrow> before ((steps1 @ steps2) ! i) = after ((steps1 @ steps2) ! (i - 1))"
      proof (cases "i = length steps1")
        case True
        then have "?j = 0" by simp
        have "before ((steps1 @ steps2) ! i) = before (steps2 ! 0)" using True idx by simp
        also have "... = before (hd steps2)" using `steps2 \<noteq> []` by (simp add: hd_conv_nth)
        also have "... = after (last steps1)" using connection by simp
        also have "... = after (steps1 ! (length steps1 - 1))" 
          using `steps1 \<noteq> []` by (simp add: last_conv_nth)
        also have "... = after ((steps1 @ steps2) ! (i - 1))" using True by (simp add: \<open>steps1 \<noteq> []\<close> nth_append_left)
        finally show ?thesis by simp
      next
        case False
        with `i \<ge> length steps1` have "i > length steps1" by simp
        then have "i - 1 \<ge> length steps1" by simp
        then have prev_idx: "(steps1 @ steps2) ! (i - 1) = steps2 ! (i - 1 - length steps1)" by (simp add: nth_append_right)

        have "?j > 0" using \<open>i > length steps1\<close> by simp

        have "before ((steps1 @ steps2) ! i) = before (steps2 ! ?j)" using idx by simp
        moreover have "after ((steps1 @ steps2) ! (i - 1)) = after (steps2 ! (?j - 1))" 
          using prev_idx by simp
        moreover have "before (steps2 ! ?j) = after (steps2 ! (?j - 1))"
          using steps2_properties j_valid `?j > 0` by blast
        ultimately show ?thesis by presburger

      qed

      have "prod ((steps1 @ steps2) ! i) \<in> P \<and>
            before ((steps1 @ steps2) ! i) = prefix ((steps1 @ steps2) ! i) @ 
              [Nt (fst (prod ((steps1 @ steps2) ! i)))] @ suffix ((steps1 @ steps2) ! i) \<and>
            after ((steps1 @ steps2) ! i) = prefix ((steps1 @ steps2) ! i) @ 
              snd (prod ((steps1 @ steps2) ! i)) @ suffix ((steps1 @ steps2) ! i)"
        using steps2_properties[OF j_valid] idx by auto

      then show ?thesis using consistency by simp
    qed
  qed
qed



lemma DerWitsEmptyI[intro]:
  shows "[] \<in> DerWits P u u"
  unfolding DerWits_def by simp

lemma DerWitsI[intro]:
  assumes "steps \<in> DerSeqs P"
    and \<open>steps \<noteq> []\<close>
    and \<open>before (hd steps) = u\<close>
    and \<open>after (last steps) = v\<close>
  shows "steps \<in> DerWits P u v"
  using assms unfolding DerWits_def by auto


lemma DerWitsEmptyD[dest]:
  assumes "[] \<in> DerWits P u v"
  shows "[] \<in> DerSeqs P" and \<open>u = v\<close>
  using assms unfolding DerWits_def by auto


lemma DerWitsNonemptyD[dest]:
  assumes "steps \<in> DerWits P u v" and "steps \<noteq> []"
  shows is_DerSeq: "steps \<in> DerSeqs P"  and before_hd_eq: "before (hd steps) = u" and after_last_eq: "after (last steps) = v"
  using assms unfolding DerWits_def by auto

lemma DerWitsOneD[dest]:
  assumes "[step] \<in> DerWits P u v"
  shows is_DerSeq_one: "[step] \<in> DerSeqs P"  and before_hd_eq_one: "before (step) = u" and after_last_eq_one: "after (step) = v"
  using assms unfolding DerWits_def by auto


lemmas DerWitsNonemptyE = DerWitsNonemptyD[elim_format]
lemmas DerWitsEmptyE = DerWitsEmptyD[elim_format]
lemmas DerWitsOneE = DerWitsOneD[elim_format]


lemma DerWits_singleI[intro]:
  assumes "prod_rule \<in> P"
    and "u = prefix_str @ [Nt (fst prod_rule)] @ suffix_str"
    and "v = prefix_str @ snd prod_rule @ suffix_str"
  shows "[\<lparr>before = u, after = v, prod = prod_rule, 
          prefix = prefix_str, suffix = suffix_str\<rparr>] \<in> DerWits P u v"
proof -
  have step_in_derseqs: "[\<lparr>before = u, after = v, prod = prod_rule, 
                          prefix = prefix_str, suffix = suffix_str\<rparr>] \<in> DerSeqs P" using assms by (auto simp: DerSeqs_def)

  have "before (hd [\<lparr>before = u, after = v, prod = prod_rule, 
                    prefix = prefix_str, suffix = suffix_str\<rparr>]) = u" by simp

  moreover have "after (last [\<lparr>before = u, after = v, prod = prod_rule, 
                              prefix = prefix_str, suffix = suffix_str\<rparr>]) = v" by simp

  ultimately show ?thesis
    using step_in_derseqs by (auto simp: DerWits_def)
qed












lemma DerWits_appendI:
  assumes "steps1 \<in> DerWits P u w" "steps2 \<in> DerWits P w v"
  shows "steps1 @ steps2 \<in> DerWits P u v"
proof (cases "steps1 = []")
  case True
  then have "u = w" using assms(1) by auto
  then show ?thesis using assms(2) by (simp add: True)
next
  case False
  show ?thesis
  proof (cases "steps2 = []")
    case True
    then have "w = v" using assms(2) by auto
    then show ?thesis using assms(1) by (simp add: True)
  next
    case False
    have "steps1 \<in> DerSeqs P" "steps2 \<in> DerSeqs P" 
      using assms by auto

    have "after (last steps1) = w" "before (hd steps2) = w"
      using assms(1,2) \<open>steps1 \<noteq> []\<close> \<open>steps2 \<noteq> []\<close> by auto

    have "steps1 @ steps2 \<in> DerSeqs P"
      using \<open>steps1 \<in> DerSeqs P\<close> \<open>steps2 \<in> DerSeqs P\<close> by (simp add: DerSeqs_appendI \<open>after (last steps1) = w\<close> \<open>before (hd steps2) = w\<close>)


    moreover have "before (hd (steps1 @ steps2)) = u"
      using \<open>steps1 \<noteq> []\<close> assms(1) by auto

    moreover have "after (last (steps1 @ steps2)) = v"
      using \<open>steps2 \<noteq> []\<close> assms(2) by auto

    ultimately show ?thesis using False by blast
  qed
qed





lemma take_DerSeqs:
  assumes "steps \<in> DerSeqs P" "n \<le> length steps"
  shows "take n steps \<in> DerSeqs P"
proof (intro DerSeqsI)
  fix i
  assume "i < length (take n steps)"
  then have "i < n" by simp
  also have "n \<le> length steps" using assms(2) .
  finally have "i < length steps" .

  have "prod (take n steps ! i) = prod (steps ! i)"
    using \<open>i < n\<close> by (simp )

  moreover have "before (take n steps ! i) = before (steps ! i)"
    "prefix (take n steps ! i) = prefix (steps ! i)"
    "suffix (take n steps ! i) = suffix (steps ! i)"
    "after (take n steps ! i) = after (steps ! i)"
    using \<open>i < n\<close> by (auto )

  moreover have "prod (steps ! i) \<in> P" 
    "before (steps ! i) = prefix (steps ! i) @ [Nt (fst (prod (steps ! i)))] @ suffix (steps ! i)"
    "after (steps ! i) = prefix (steps ! i) @ snd (prod (steps ! i)) @ suffix (steps ! i)"
    using \<open>i < length steps\<close> assms(1) by (auto )

  moreover have "(i > 0 \<longrightarrow> before (steps ! i) = after (steps ! (i - 1)))"
    using \<open>i < length steps\<close> assms(1) by (auto )

  ultimately show "prod (take n steps ! i) \<in> P \<and>
                 (i > 0 \<longrightarrow> before (take n steps ! i) = after (take n steps ! (i - 1))) \<and>
                 before (take n steps ! i) = prefix (take n steps ! i) @ [Nt (fst (prod (take n steps ! i)))] @ suffix (take n steps ! i) \<and>
                 after (take n steps ! i) = prefix (take n steps ! i) @ snd (prod (take n steps ! i)) @ suffix (take n steps ! i)"
    by (simp add: \<open>i < n\<close> less_imp_diff_less)

qed




lemma take_DerWits:
  assumes "steps \<in> DerWits P u v" "0 < n" "n \<le> length steps"
  shows "take n steps \<in> DerWits P u (after (last (take n steps)))"
proof -
  have steps_nonempty: "steps \<noteq> []" using assms(2,3) by auto

  have "take n steps \<in> DerSeqs P"
    using assms(1,3) take_DerSeqs by (auto simp: DerWits_def)

  have "before (hd steps) = u"
    using assms(1) steps_nonempty by auto

  have take_nonempty: "take n steps \<noteq> []" 
    using \<open>0 < n\<close> using steps_nonempty by auto

  have "before (hd (take n steps)) = before (hd steps)"
    using take_nonempty by simp

  have "take n steps \<in> DerWits P u (after (last (take n steps)))"
    using \<open>take n steps \<in> DerSeqs P\<close> \<open>before (hd (take n steps)) = before (hd steps)\<close> \<open>before (hd steps) = u\<close>
    using take_nonempty by blast

  thus ?thesis .
qed



lemma drop_DerSeqs:
  assumes "steps \<in> DerSeqs P"
  shows "drop n steps \<in> DerSeqs P"
proof(cases \<open>n < length steps\<close>)
  case True
  then have 2: \<open>n < length steps\<close> by simp
  then show ?thesis

  proof (intro DerSeqsI)
    fix i
    assume "i < length (drop n steps)"
    then have "i + n < length steps" by simp

    have "prod (drop n steps ! i) = prod (steps ! (i + n))"
      by (simp add: Groups.ab_semigroup_add_class.add.commute 2 less_or_eq_imp_le)


    moreover have "before (drop n steps ! i) = before (steps ! (i + n))"
      "prefix (drop n steps ! i) = prefix (steps ! (i + n))"
      "suffix (drop n steps ! i) = suffix (steps ! (i + n))"
      "after (drop n steps ! i) = after (steps ! (i + n))"
      by (auto simp add: Groups.ab_semigroup_add_class.add.commute 2 less_or_eq_imp_le)


    moreover have "prod (steps ! (i + n)) \<in> P" 
      "before (steps ! (i + n)) = prefix (steps ! (i + n)) @ [Nt (fst (prod (steps ! (i + n))))] @ suffix (steps ! (i + n))"
      "after (steps ! (i + n)) = prefix (steps ! (i + n)) @ snd (prod (steps ! (i + n))) @ suffix (steps ! (i + n))"
      using \<open>i + n < length steps\<close> assms(1) by (auto simp add: Groups.ab_semigroup_add_class.add.commute 2 less_or_eq_imp_le)



    moreover have "i > 0 \<longrightarrow> before (steps ! (i + n)) = after (steps ! (i + n - 1))"
      using \<open>i + n < length steps\<close> assms(1) by (simp add: before_eq_next_after)


    ultimately show "prod (drop n steps ! i) \<in> P \<and>
                 (i > 0 \<longrightarrow> before (drop n steps ! i) = after (drop n steps ! (i - 1))) \<and>
                 before (drop n steps ! i) = prefix (drop n steps ! i) @ 
                   [Nt (fst (prod (drop n steps ! i)))] @ suffix (drop n steps ! i) \<and>
                 after (drop n steps ! i) = prefix (drop n steps ! i) @ 
                   snd (prod (drop n steps ! i)) @ suffix (drop n steps ! i)"
      using Groups.ab_semigroup_add_class.add.commute \<open>i + n < length steps\<close> add_0 add_diff_assoc2 after_splits assms(1) 2 before_splits nth_drop less_iff_succ_less_eq less_or_eq_imp_le by (smt (verit)  in_prods  )
  qed
next
  case False
  then show ?thesis by simp
qed




lemma drop_DerWits:
  assumes "steps \<in> DerWits P u v" "n < length steps"
  shows "drop n steps \<in> DerWits P (before (steps ! n)) v"
proof -
  have steps_nonempty: "steps \<noteq> []" using assms(2) by auto

  have "drop n steps \<in> DerSeqs P"
    using assms(1,2) drop_DerSeqs by (auto simp: DerWits_def)

  have "after (last steps) = v"
    using assms(1) steps_nonempty by auto

  have drop_nonempty: "drop n steps \<noteq> []" 
    using assms(2) by auto

  have "before (hd (drop n steps)) = before (steps ! n)"
    using drop_nonempty assms(2) by (simp add: hd_drop_conv_nth)


  have "after (last (drop n steps)) = after (last steps)"
    using drop_nonempty by simp

  have "drop n steps \<in> DerWits P (before (steps ! n)) v"
    using \<open>drop n steps \<in> DerSeqs P\<close> \<open>before (hd (drop n steps)) = before (steps ! n)\<close> 
      \<open>after (last (drop n steps)) = after (last steps)\<close> \<open>after (last steps) = v\<close>
    using drop_nonempty by blast

  thus ?thesis .
qed






lemma append_DerWits:
  assumes "(l1 @ l2) \<in> DerWits P u v"
  shows "l1 \<in> DerWits P u (if l1 = [] then u else after (last l1))" and 
    "l2 \<in> DerWits P (if l1 = [] then u else after (last l1)) v"
proof -
  let ?steps = \<open>l1 @ l2\<close>
  let ?w = "if l1 = [] then u else after (last l1)"

  show "l1 \<in> DerWits P u ?w"
  proof (cases "l1 = []")
    case True
    then show ?thesis by auto
  next
    case False
    have "?steps \<in> DerSeqs P" using assms(1) by auto

    have "l1 \<in> DerSeqs P"
    proof (intro DerSeqsI)
      fix i
      assume "i < length l1"
      then have "i < length ?steps" using assms(1) by simp

      have "prod (l1 ! i) = prod (?steps ! i)"
        using \<open>i < length l1\<close> by (simp add: assms(1) nth_append_left)


      moreover have "before (l1 ! i) = before (?steps ! i)"
        "prefix (l1 ! i) = prefix (?steps ! i)"
        "suffix (l1 ! i) = suffix (?steps ! i)"
        "after (l1 ! i) = after (?steps ! i)"
        using \<open>i < length l1\<close> by (auto simp add: \<open>i < length l1\<close> assms(1) nth_append_left)




      moreover have "prod (?steps ! i) \<in> P"
        "before (?steps ! i) = prefix (?steps ! i) @ [Nt (fst (prod (?steps ! i)))] @ suffix (?steps ! i)"
        "after (?steps ! i) = prefix (?steps ! i) @ snd (prod (?steps ! i)) @ suffix (?steps ! i)"
        using \<open>i < length ?steps\<close> \<open>?steps \<in> DerSeqs P\<close> by auto

      moreover have "i > 0 \<longrightarrow> before (?steps ! i) = after (?steps ! (i - 1))"
        using \<open>i < length ?steps\<close> \<open>?steps \<in> DerSeqs P\<close> by auto

      ultimately show "prod (l1 ! i) \<in> P \<and>
                     (i > 0 \<longrightarrow> before (l1 ! i) = after (l1 ! (i - 1))) \<and>
                     before (l1 ! i) = prefix (l1 ! i) @ [Nt (fst (prod (l1 ! i)))] @ suffix (l1 ! i) \<and>
                     after (l1 ! i) = prefix (l1 ! i) @ snd (prod (l1 ! i)) @ suffix (l1 ! i)"
        by (simp add: \<open>i < length l1\<close> assms(1) less_imp_diff_less nth_append_left)

    qed

    moreover have "before (hd l1) = u"
      using assms False by fastforce


    ultimately show ?thesis
      using False by auto
  qed

  show "l2 \<in> DerWits P ?w v"
  proof (cases "l2 = []")
    case True
    from assms(1) have "?steps \<in> DerWits P u v" by simp
    from True assms(1) have "?steps = l1" by simp

    have "v = (if l1 = [] then u else after (last l1))"
    proof (cases "l1 = []")
      case True
      then have "?steps = []" using \<open>?steps = l1\<close> by simp
      then have "u = v" using \<open>?steps \<in> DerWits P u v\<close> by auto
      then show ?thesis using True by simp
    next
      case False
      then have "?steps \<noteq> []" using \<open>?steps = l1\<close> by simp
      then have "after (last ?steps) = v" using \<open>?steps \<in> DerWits P u v\<close> by auto
      then show ?thesis using False \<open>?steps = l1\<close> by simp
    qed

    then show ?thesis using True by auto
  next
    case False
    then have l2_not_empty: \<open>l2 \<noteq> []\<close> by simp
    have "?steps \<in> DerSeqs P" using assms(1) by auto

    have "l2 \<in> DerSeqs P"
    proof (intro DerSeqsI)
      fix i
      assume "i < length l2"
      then have "i + length l1 < length ?steps" using assms(1) by simp

      have "prod (l2 ! i) = prod (?steps ! (i + length l1))"
        using \<open>i < length l2\<close> by (metis Groups.ab_semigroup_add_class.add.commute nth_append_length_plus)


      moreover have "before (l2 ! i) = before (?steps ! (i + length l1))"
        "prefix (l2 ! i) = prefix (?steps ! (i + length l1))"
        "suffix (l2 ! i) = suffix (?steps ! (i + length l1))"
        "after (l2 ! i) = after (?steps ! (i + length l1))"
        using \<open>i < length l2\<close> by (auto simp add: assms(1) nth_append)


      moreover have "prod (?steps ! (i + length l1)) \<in> P"
        "before (?steps ! (i + length l1)) = prefix (?steps ! (i + length l1)) @ 
          [Nt (fst (prod (?steps ! (i + length l1))))] @ suffix (?steps ! (i + length l1))"
        "after (?steps ! (i + length l1)) = prefix (?steps ! (i + length l1)) @ 
          snd (prod (?steps ! (i + length l1))) @ suffix (?steps ! (i + length l1))"
        using \<open>i + length l1 < length ?steps\<close> \<open>?steps \<in> DerSeqs P\<close> apply (simp add: in_prods)
        using \<open>i + length l1 < length (l1 @ l2)\<close> \<open>l1 @ l2 \<in> DerSeqs P\<close> apply blast
        using \<open>i + length l1 < length (l1 @ l2)\<close> \<open>l1 @ l2 \<in> DerSeqs P\<close> by blast


      moreover have "i > 0 \<longrightarrow> before (l2 ! i) = after (l2 ! (i - 1))"
      proof (cases "i > 0")
        case True
        then have "i - 1 < length l2" using \<open>i < length l2\<close> by auto
        then have "(i - 1) + length l1 < length ?steps" using assms(1) by simp

        have "before (?steps ! (i + length l1)) = after (?steps ! (i + length l1 - 1))"
          using \<open>i + length l1 < length ?steps\<close> \<open>?steps \<in> DerSeqs P\<close> \<open>i > 0\<close> by blast


        have "after (l2 ! (i - 1)) = after (?steps ! (i - 1 + length l1))"
          using \<open>i - 1 < length l2\<close> by (simp add: assms(1) nth_append)


        have "i + length l1 - 1 = i - 1 + length l1" using True by auto


        then show ?thesis 
          using \<open>before (l2 ! i) = before (?steps ! (i + length l1))\<close> 
            \<open>before (?steps ! (i + length l1)) = after (?steps ! (i + length l1 - 1))\<close>
            \<open>after (l2 ! (i - 1)) = after (?steps ! (i - 1 + length l1))\<close>
          by presburger
      qed simp

      ultimately show "prod (l2 ! i) \<in> P \<and>
                     (i > 0 \<longrightarrow> before (l2 ! i) = after (l2 ! (i - 1))) \<and>
                     before (l2 ! i) = prefix (l2 ! i) @ [Nt (fst (prod (l2 ! i)))] @ suffix (l2 ! i) \<and>
                     after (l2 ! i) = prefix (l2 ! i) @ snd (prod (l2 ! i)) @ suffix (l2 ! i)"
        by auto
    qed

    have "before (hd l2) = ?w"
    proof (cases "l1 = []")
      case True
      then have "?steps = l2" using assms(1) by simp
      then have "before (hd ?steps) = u" using assms(1) False by auto
      then show ?thesis using True \<open>?steps = l2\<close> by simp
    next
      case False
      then have "length l1 > 0" by simp

      then have "hd l2 = l2 ! 0" using hd_conv_nth l2_not_empty by blast
      have "?steps ! length l1 = l2 ! 0"
      proof -
        have "length l1 < length ?steps" using False assms(1) \<open>l2 \<noteq> []\<close> by auto
        then have "?steps ! length l1 = (l1 @ l2) ! length l1" using assms(1) by simp
        also have "... = l2 ! 0" 
          by (simp add: nth_append)

        finally show ?thesis by (simp add: \<open>(l1 @ l2) ! length l1 = l2 ! 0\<close>)

      qed

      then have "before (hd l2) = before (l2 ! 0)" by (simp add: \<open>hd l2 = l2 ! 0\<close>)
      also have "... = before (?steps ! length l1)" by (simp add: \<open>?steps ! length l1 = l2 ! 0\<close>)
      finally have "before (hd l2) = before (?steps ! length l1)" .


      moreover have "before (?steps ! length l1) = after (?steps ! (length l1 - 1))"
        using \<open>length l1 > 0\<close> \<open>?steps \<in> DerSeqs P\<close> 
        by (simp add: assms(1) before_eq_next_after l2_not_empty)


      moreover have "after (?steps ! (length l1 - 1)) = after (l1 ! (length l1 - 1))"
        using \<open>length l1 > 0\<close> by (simp add: assms(1) nth_append_left)


      moreover have "after (l1 ! (length l1 - 1)) = after (last l1)"
        using \<open>length l1 > 0\<close> by (simp add: last_conv_nth)

      ultimately show ?thesis using False by simp
    qed

    moreover have "after (last l2) = v"
    proof -
      have "last l2 = last ?steps" using assms(1) False by (simp add: last_append)
      then have "after (last l2) = after (last ?steps)" by simp
      moreover have "after (last ?steps) = v" using assms(1) by (simp add: DerWits_def False assms(1))

      ultimately show ?thesis by simp
    qed

    ultimately show ?thesis using False by (simp add: DerWitsI \<open>l2 \<in> DerSeqs P\<close>)

  qed
qed


lemma append_DerWits':
  assumes "(l1 @ l2) \<in> DerWits P u v"
    and \<open>l1 \<noteq> []\<close>
    and \<open>l2 \<noteq> []\<close>
  shows "l1 \<in> DerWits P u (after (last l1))" and 
    \<open>l1 \<in> DerWits P u (before (hd l2))\<close> and
    "l2 \<in> DerWits P (after (last l1)) v" and
    "l2 \<in> DerWits P (before (hd l2)) v"

  using append_DerWits assms(1,2) 
     apply blast
    apply (metis append_DerWits(1,2) assms(1,3) before_hd_eq)
  using append_DerWits(2) assms(1,2) apply force
  using append_DerWits(2) assms(1,3) by blast






theorem DerWits_iff_derive:
  "P \<turnstile> u \<Rightarrow> v \<longleftrightarrow> (\<exists>steps \<in> DerWits P u v. length steps = 1)"
proof
  assume "P \<turnstile> u \<Rightarrow> v"
  then obtain A \<alpha> prefix suffix where
    "(A, \<alpha>) \<in> P" and "u = prefix @ [Nt A] @ suffix" and "v = prefix @ \<alpha> @ suffix"
    by (auto simp: derive_iff)

  define step where "step = \<lparr>before = u, after = v, prod = (A, \<alpha>), 
                      prefix = prefix, suffix = suffix\<rparr>"

  have "[step] \<in> DerSeqs P"
    using \<open>(A, \<alpha>) \<in> P\<close> \<open>u = prefix @ [Nt A] @ suffix\<close> \<open>v = prefix @ \<alpha> @ suffix\<close>
    by (simp add: DerSeqs_singleI step_def)

  moreover have "before (hd [step]) = u" and "after (last [step]) = v"
    by (auto simp: step_def)

  ultimately have "[step] \<in> DerWits P u v"
    by (simp add: DerWitsI)


  thus "\<exists>steps \<in> DerWits P u v. length steps = 1"
    by (metis List.list.size(3) One_nat_def length_Cons)

next
  assume "\<exists>steps \<in> DerWits P u v. length steps = 1"
  then obtain step where "[step] \<in> DerWits P u v"
    by (metis One_nat_def Suc_length_conv length_0_conv)


  then have "prod step \<in> P" and 
    "before step = prefix step @ [Nt (fst (prod step))] @ suffix step" and
    "after step = prefix step @ snd (prod step) @ suffix step" and
    "before step = u" and "after step = v"
    by (auto simp: DerWits_def DerSeqs_def)

  have "u = prefix step @ [Nt (fst (prod step))] @ suffix step"
    using \<open>before step = u\<close> \<open>before step = prefix step @ [Nt (fst (prod step))] @ suffix step\<close>
    by simp

  moreover have "v = prefix step @ snd (prod step) @ suffix step"
    using \<open>after step = v\<close> \<open>after step = prefix step @ snd (prod step) @ suffix step\<close>
    by simp

  ultimately show "P \<turnstile> u \<Rightarrow> v"
    using \<open>prod step \<in> P\<close> 
    by (metis CFG.derive.intros surjective_pairing)

qed







theorem DerWits_iff_deriven:
  "P \<turnstile> u \<Rightarrow>(n) v \<longleftrightarrow> (\<exists>steps \<in> DerWits P u v. length steps = n)"
proof
  assume "P \<turnstile> u \<Rightarrow>(n) v"
  then show "\<exists>steps \<in> DerWits P u v. length steps = n"
  proof (induction n arbitrary: v)
    case 0
    then have "u = v" by simp
    then show \<open>\<exists>steps\<in>DerWits P u v. length steps = 0\<close> by auto
  next
    case (Suc n)
    from \<open>P \<turnstile> u \<Rightarrow>(Suc n) v\<close> obtain w where "P \<turnstile> u \<Rightarrow>(n) w" "P \<turnstile> w \<Rightarrow> v"
      by (auto simp: relpowp_Suc_left)

    from Suc.IH[OF this(1)] obtain steps where "steps \<in> DerWits P u w" "length steps = n" 
      by blast

    from \<open>P \<turnstile> w \<Rightarrow> v\<close> obtain A \<alpha> prefix suffix where split_defs:
      "(A, \<alpha>) \<in> P" "w = prefix @ [Nt A] @ suffix" "v = prefix @ \<alpha> @ suffix"
      by (auto simp: derive_iff)

    define step where "step = \<lparr>before = w, after = v, prod = (A, \<alpha>), 
                        prefix = prefix, suffix = suffix\<rparr>"

    have "[step] \<in> DerSeqs P"
      using \<open>(A, \<alpha>) \<in> P\<close> \<open>w = prefix @ [Nt A] @ suffix\<close> \<open>v = prefix @ \<alpha> @ suffix\<close> by (simp add: DerSeqs_singleI step_def)


    have "[step] \<in> DerWits P w v" unfolding step_def apply(rule DerWits_singleI) using split_defs by auto 


    have "steps @ [step] \<in> DerWits P u v"
      using \<open>steps \<in> DerWits P u w\<close> \<open>[step] \<in> DerWits P w v\<close>
      by (rule DerWits_appendI)

    moreover have "length (steps @ [step]) = Suc n"
      using \<open>length steps = n\<close> by auto

    ultimately show ?case by blast
  qed
next
  assume "\<exists>steps \<in> DerWits P u v. length steps = n"
  then obtain steps where steps_def: "steps \<in> DerWits P u v" "length steps = n" by blast
  show "P \<turnstile> u \<Rightarrow>(n) v"
  proof (cases "steps = []")
    case True
    then have "n = 0" using \<open>length steps = n\<close> by auto
    moreover from True \<open>steps \<in> DerWits P u v\<close> have "u = v" by auto
    ultimately show ?thesis by auto
  next
    case False
    from steps_def show ?thesis
    proof (induction n arbitrary: u v steps)
      case 0
      then show ?case by (simp add: DerWitsEmptyD(2))
    next
      case (Suc n)
      from \<open>steps \<in> DerWits P u v\<close> False have "steps \<in> DerSeqs P" 
        by auto

      have "length steps > 0" using False by (simp add: local.Suc.prems(2))

      then obtain first_step rest where rest_def: "steps = first_step # rest"
        by (meson length_Suc_conv local.Suc.prems(2))

      then have \<open>[first_step] \<in> DerSeqs P\<close> by (metis \<open>0 < length steps\<close> \<open>steps \<in> DerSeqs P\<close> hd_drop_conv_nth less_eq_Suc_le nth_Cons_0 self_append_conv2 take0 take_DerSeqs take_hd_drop)
      have \<open>rest \<in> DerSeqs P\<close> by (metis \<open>steps = first_step # rest\<close> \<open>steps \<in> DerSeqs P\<close> drop0 drop_DerSeqs drop_Suc_Cons)

      have "before first_step = u"
        using  \<open>steps \<in> DerWits P u v\<close> \<open>steps = first_step # rest\<close> by auto

      define w where "w = after first_step"

      have "[first_step] \<in> DerWits P u w"
      proof (intro DerWitsI)
        show "[first_step] \<in> DerSeqs P" using \<open>[first_step] \<in> DerSeqs P\<close> by auto
        show "[first_step] \<noteq> []" by simp
        show "before (hd [first_step]) = u" by (simp add: \<open>before first_step = u\<close>)
        show "after (last [first_step]) = w" by (simp add: w_def)
      qed

      from DerWits_iff_derive have "P \<turnstile> u \<Rightarrow> w"
        using \<open>[first_step] \<in> DerWits P u w\<close> by (metis List.list.size(3) One_nat_def length_Cons)


      have "rest \<in> DerWits P w v" 
      proof (cases "rest = []")
        case True
        then have "w = v" using \<open>steps \<in> DerWits P u v\<close> \<open>steps = first_step # rest\<close> using w_def by fastforce
        then show ?thesis by (simp add: DerWitsEmptyI True)
      next
        case False
        then have \<open>steps = [first_step] @ rest\<close> using rest_def by simp
        then show ?thesis using append_DerWits rest_def steps_def by (metis \<open>[first_step] \<in> DerWits P u w\<close> after_last_eq local.Suc.prems(1) not_Cons_self2)
      qed

      have "length rest = n"
        using \<open>length steps = Suc n\<close> \<open>steps = first_step # rest\<close> by auto

      from Suc.IH[OF \<open>rest \<in> DerWits P w v\<close> \<open>length rest = n\<close>] 
      have "P \<turnstile> w \<Rightarrow>(n) v" .

      with \<open>P \<turnstile> u \<Rightarrow> w\<close> show "P \<turnstile> u \<Rightarrow>(Suc n) v"
        by (meson relpowp_Suc_I2)

    qed
  qed
qed







corollary derives_iff_DerWits:
  "P \<turnstile> u \<Rightarrow>* v \<longleftrightarrow> (\<exists>deriv. (deriv \<in> DerWits P u v))"
  using DerWits_iff_deriven by (metis rtranclp_power) 

(*end section derivation Witnesses*)











































lemma length_append_one: \<open>length (l1 @ [l]) = (length l1 +1)\<close> by simp






lemma transform_production_one_step:
  assumes \<open>CNF_rule (S,w)\<close>
    and \<open>(S,w) \<in> P\<close>
  shows \<open>(transform_production ` P) \<turnstile> [Nt S] \<Rightarrow> snd (transform_production (S,w))\<close>
proof-
  obtain w' where \<open>transform_production (S,w) = (S, w')\<close> by (metis fst_eqD fst_transform_production surj_pair)
  then have \<open>(S, w') \<in> transform_production ` P\<close> using assms(2) by force
  then show ?thesis by (simp add: \<open>transform_production (S, w) = (S, w')\<close> derive_singleton)
qed

lemma transform_production_one_step_bu:
  assumes \<open>CNF_rule (S,w)\<close>
    and \<open>(S,w) \<in> P\<close>
  shows \<open>(transform_production ` P) \<turnstile> [Nt S] \<Rightarrow>bu snd (transform_production (S,w))\<close>
  by (metis assms(2) bu_prod fst_transform_production image_eqI surjective_pairing)









lemma P'_balanced:
assumes \<open>(image transform_production P) \<turnstile> [Nt A] \<Rightarrow>* x\<close>
and \<open>\<forall>p \<in> P. CNF_rule p\<close>
shows \<open>balanced_terminals x\<close>
using assms proof(induction rule: derives_induct)
  case base
  then show ?case by (simp add: Nt)

next
  case (step u A v w)
  have \<open>balanced_terminals (u @ [Nt A] @ v)\<close> using local.step.IH local.step.prems by auto

  have \<open>balanced_terminals w\<close> sorry
  then show ?case 
qed

















text\<open>The chomsky-scheutzenberger theorem that we want to prove.\<close>
lemma chomsky_schuetzenberger :
  fixes L::\<open>'t list set\<close>
  assumes \<open>CFL.cfl TYPE('n) L\<close> 
  shows \<open>\<exists>(R::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set) h \<Gamma>. (reg TYPE('n) R) \<and> (L = image h (R \<inter> dyck_language \<Gamma>)) \<and> hom h\<close>
proof -
  have \<open>\<exists>P S::'n. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> using \<open>cfl TYPE('n) L\<close> CNF_existence by auto
  then obtain P and S::'n where \<open>L = Lang P S\<close> and P_CNF: \<open>(\<forall>p \<in> P. CNF_rule p)\<close> by blast

  define \<Gamma> where \<open>\<Gamma> = P \<times> {One, Two}\<close>
  define P' where \<open>P' = image transform_production P\<close>
  define L' where \<open>L' = Lang P' S\<close>
  define h where \<open>h = (the_hom::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list \<Rightarrow> 't list)\<close>
  define h_ext where \<open>h_ext = (the_hom_ext::('n, bracket \<times> ('n,'t) prod \<times> version ) sym list \<Rightarrow> ('n,'t) sym list)\<close>

  have \<open>L' \<subseteq> dyck_language \<Gamma>\<close> sorry (* This might not be needed (but it was listed in the book). Leave this for last *)

  have \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re P A)\<close> (* This is the hard part of the proof - the local lemma in the textbook *)
  proof-

    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> balanced_terminals x\<close>
    proof-
    fix A x
    assume \<open>P' \<turnstile> [Nt A] \<Rightarrow>* x\<close>
    then show \<open>balanced_terminals x\<close>
    proof(induction rule: derives_induct)
      case base
      then show ?case sorry
    next
      case (step u A v w)
      then show ?case sorry
    qed

    qed
    (*
    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> (strip_tm_kill_Nt x) \<in> (dyck_language \<Gamma>)\<close>
    proof-
    fix A x
    assume \<open>P' \<turnstile> [Nt A] \<Rightarrow>* x\<close>
    then show \<open>(map strip_tm x) \<in> (dyck_language \<Gamma>)\<close>
    proof(induction  rule: rtrancl_derive_induct)
      case base
      then show ?case sorry
    next
      case (step u A v w)
      then show ?case sorry
    qed

    qed *)




    show ?thesis sorry
  qed



  then have \<open>L' = (dyck_language \<Gamma>) \<inter> (Re P S)\<close> by (metis CFL_Lang_eq_CFG_Lang CFL_Lang_if_derives L'_def derives_if_CFL_Lang inf_absorb2 inf_commute subsetI)
  then have \<open>image h ((dyck_language \<Gamma>) \<inter> (Re P S)) =  image h L'\<close> by simp
  also have \<open>... = Lang P S\<close>
  proof(standard)
    have \<open>\<And>w'. (w'  \<in> L' \<Longrightarrow> h w' \<in> Lang P S)\<close>
    proof-
      fix w'
      assume \<open>w' \<in> L'\<close>
      with L'_def have \<open>w' \<in> Lang P' S\<close> by simp
      then have \<open>P' \<turnstile> [Nt S] \<Rightarrow>* map Tm w'\<close> by (simp add: CFL_Lang_eq_CFG_Lang derives_if_CFL_Lang)
      then obtain n where \<open>P' \<turnstile> [Nt S] \<Rightarrow>(n) map Tm w'\<close> by (metis rtranclp_power)
      then have \<open>P \<turnstile> [Nt S] \<Rightarrow>* h_ext (map Tm w')\<close> 
      proof(induction rule: deriven_induct)
        case 0
        then show ?case unfolding h_ext_def the_hom_ext.simps by simp
      next
        case (Suc n u A v x')
        from \<open>(A, x') \<in> P'\<close> obtain \<pi> where \<open>\<pi> \<in> P\<close> and transf_\<pi>_def: \<open>(transform_production \<pi>) = (A, x')\<close> using P'_def by auto
        moreover have \<open>CNF_rule \<pi>\<close> using P_CNF \<open>\<pi> \<in> P\<close> by auto
        ultimately obtain x where \<pi>_def: \<open>\<pi> = (A, x)\<close> using transform_production_CNF by (smt (verit, del_insts) CNF_rule_def Pair_inject chomsky_schuetzenberger.transform_production.simps(1,2))
        have \<open>hom h_ext\<close> unfolding hom_def h_ext_def the_hom_ext.simps by simp
        then have \<open>h_ext (u @ [Nt A] @ v) = h_ext u @ h_ext [Nt A] @ h_ext v\<close> using hom_def by (metis (no_types, lifting))
        then have \<open> P \<turnstile> [Nt S] \<Rightarrow>* h_ext u @ h_ext [Nt A] @ h_ext v\<close> using local.Suc.IH by auto
        then have \<open> P \<turnstile> [Nt S] \<Rightarrow>* h_ext u @ [Nt A] @ h_ext v\<close> unfolding h_ext_def by simp
        then have \<open> P \<turnstile> [Nt S] \<Rightarrow>* h_ext u @ x @ h_ext v\<close> using \<pi>_def \<open>\<pi> \<in> P\<close> derive.intros by (metis Transitive_Closure.rtranclp.rtrancl_into_rtrancl)

        have \<open>h_ext x' = h_ext (snd (transform_production \<pi>))\<close> by (simp add: transf_\<pi>_def)
        also have \<open>... = snd \<pi>\<close> using \<open>CNF_rule \<pi>\<close> h_ext_def hom_ext_inv by blast
        also have \<open>... = x\<close> by (simp add: \<pi>_def)
        finally have \<open>h_ext x' = x\<close> by simp

        with \<open> P \<turnstile> [Nt S] \<Rightarrow>* h_ext u @ x @ h_ext v\<close> have \<open> P \<turnstile> [Nt S] \<Rightarrow>* h_ext u @ h_ext x' @ h_ext v\<close> by simp
        then show ?case by (metis \<open>hom h_ext\<close> hom_def)
      qed
      then show \<open>h w' \<in> Lang P S\<close> using h_eq_h_ext h_ext_def by (metis CFL_Lang_eq_CFG_Lang CFL_Lang_if_derives h_def)
    qed
    then show \<open> h ` L' \<subseteq> Lang P S\<close> by (simp add: image_subsetI)

  next
    have \<open>\<And>w. (w  \<in> Lang P S \<Longrightarrow> \<exists>w' \<in> L'. w = h w')\<close> 
    proof-
      have \<open>\<And>w. (w \<in> Ders P S \<Longrightarrow> \<exists>w' \<in> Ders P' S. w = h_ext w')\<close>
      proof-
        fix w
        assume \<open>w \<in> Ders P S\<close>
        then have \<open>P \<turnstile> [Nt S] \<Rightarrow>*  w\<close> by (simp add: DersD)
        then have \<open>\<exists>derw. derw \<in> DerWits P [Nt S] w\<close> by (simp add: derives_iff_DerWits) 
        then obtain derw where \<open>derw \<in> DerWits P [Nt S] w\<close> by blast
        then have \<open>\<exists>w' derw'.  
                  (derw' \<in> DerWits P' [Nt S] w') 
              \<and>  (length derw' = length derw)
              \<and>  (\<forall>i < length derw'. 
                      (transform_production (prod (derw ! i)) = (prod (derw' ! i)))
                    \<and> ( after (derw ! i) = h_ext (after (derw' ! i)) )
                    \<and> ( before (derw ! i) = h_ext (before (derw' ! i)) )
                    \<and> ( prefix (derw ! i) = h_ext (prefix (derw' ! i)) )
                    \<and> ( suffix (derw ! i) = h_ext (suffix (derw' ! i)) )
              )\<close>
        proof(induction \<open>length derw\<close> arbitrary: w derw)
          case 0
          then show ?case by auto
        next
          case (Suc n)

          from Suc have derw_DerWits: \<open>derw \<in> DerWits P [Nt S] w\<close> by simp
          from Suc have length_derw: \<open>length derw = n + 1\<close> by simp
          from Suc have IH:\<open>\<And>w derw. \<lbrakk>n = length derw; derw \<in> DerWits P [Nt S] w\<rbrakk>
                      \<Longrightarrow> \<exists>w' derw'. derw' \<in> DerWits P' [Nt S] w' 
                      \<and> length derw' = length derw 
                      \<and> (\<forall>i<length derw'. transform_production (prod (derw ! i)) = prod (derw' ! i) 
                      \<and> after (derw ! i) = h_ext (after (derw' ! i)) 
                      \<and> before (derw ! i) = h_ext (before (derw' ! i)) 
                      \<and> prefix (derw ! i) = h_ext (prefix (derw' ! i)) 
                      \<and> suffix (derw ! i) = h_ext (suffix (derw' ! i)))\<close> by blast


          obtain derw_front derw_step where derw_split: \<open>derw = (derw_front @ [derw_step])\<close> by (metis length_Suc_conv_rev local.Suc.hyps(2))
          then have \<open>n = length derw_front\<close> using local.Suc.hyps(2) by fastforce


          then show \<open>\<exists>w' derw'. 
          derw' \<in> DerWits P' [Nt S] w' 
          \<and> length derw' = length derw 
          \<and> (\<forall>i<length derw'. 
              transform_production (prod (derw ! i)) = prod (derw' ! i) 
              \<and> after (derw ! i) = h_ext (after (derw' ! i)) 
              \<and> before (derw ! i) = h_ext (before (derw' ! i)) 
              \<and> prefix (derw ! i) = h_ext (prefix (derw' ! i)) 
              \<and> suffix (derw ! i) = h_ext (suffix (derw' ! i)) )\<close>
          proof(cases \<open>n = 0\<close>)
            case True
            then have n_eq_0: \<open>n = 0\<close> by simp
            then have \<open>derw = [derw_step]\<close> by (simp add: \<open>n = length derw_front\<close> derw_split)
            then have derw_step_DerWits: \<open>[derw_step] \<in> DerWits P [Nt S] w\<close> using derw_DerWits by auto

            then have before_split: \<open>before (derw_step) = prefix (derw_step) @ [Nt (fst (prod (derw_step)))] @ suffix (derw_step)\<close> by blast

            then have \<open>fst (prod derw_step) = S\<close> by (metis (no_types, lifting) CFG.sym.inject(1) Cons_eq_append_conv List.list.distinct(1) List.list.sel(1) Nil_is_append_conv before_hd_eq_one derw_step_DerWits)
            then have \<open>prefix (derw_step) = []\<close> by (metis Cons_eq_append_conv Nil_is_append_conv before_split before_hd_eq_one derw_step_DerWits)
            then have \<open>suffix (derw_step) = []\<close> using \<open>derw = [derw_step]\<close> before_hd_eq_one before_split derw_DerWits by auto
            then have \<open>after derw_step = snd (prod derw_step)\<close> by (metis \<open>prefix derw_step = []\<close> after_splits_one derw_step_DerWits is_DerSeq_one self_append_conv self_append_conv2)
            then have \<open>after (derw ! 0) = snd (prod derw_step)\<close> using \<open>derw = [derw_step]\<close> by auto
            have \<open>prod (derw_step) \<in> P\<close> using derw_step_DerWits by (simp add: in_prods_one is_DerSeq_one)
            then have \<open>CNF_rule (prod (derw_step))\<close> using P_CNF by simp
            define w' where \<open>w' = snd (transform_production (prod derw_step))\<close>
            define derw' where \<open>derw' = [\<lparr>before = [Nt S], after = w', prod = transform_production (prod derw_step), prefix = [], suffix = []\<rparr>]\<close>
            have derw'0: \<open>derw' ! 0 = \<lparr>before = [Nt S], after = w', prod = transform_production (prod derw_step), prefix = [], suffix = []\<rparr>\<close> using derw'_def by simp
            have \<open>derw' \<in> DerWits P' [Nt S] w'\<close> unfolding derw'_def apply(rule DerWits_singleI) 
              using P'_def \<open>derw = [derw_step]\<close> derw_DerWits apply auto[1]
               apply (metis Product_Type.prod.exhaust_sel \<open>fst (prod derw_step) = S\<close> append_Cons append_Nil fst_transform_production)
              by (simp add: w'_def)
            moreover have \<open>length derw' = length derw\<close> using derw'_def using local.Suc.hyps(2) n_eq_0 by auto

            moreover have \<open>transform_production (prod (derw ! 0)) = prod (derw' ! 0) \<close> using derw'0 by (simp add: \<open>derw = [derw_step]\<close>)
            moreover have \<open>after (derw ! 0) = h_ext (after (derw' ! 0))\<close> using derw'0 w'_def hom_ext_inv by (metis \<open>CNF_rule (prod derw_step)\<close> \<open>after (derw ! 0) = snd (prod derw_step)\<close> h_ext_def select_convs(2))
            moreover have \<open>before (derw ! 0) = h_ext (before (derw' ! 0))\<close> using derw'0 using \<open>derw = [derw_step]\<close> derw_step_DerWits h_ext_def by auto
            moreover have \<open>prefix (derw ! 0) = h_ext (prefix (derw' ! 0)) \<close> using derw'0 by (simp add: \<open>derw = [derw_step]\<close> \<open>prefix derw_step = []\<close> h_ext_def)
            moreover have \<open>suffix (derw ! 0) = h_ext (suffix (derw' ! 0))\<close> using derw'0 using \<open>derw = [derw_step]\<close> \<open>prefix derw_step = []\<close> \<open>suffix derw_step = []\<close> calculation(6) by auto
            ultimately have \<open>(\<forall>i<length derw'. 
              transform_production (prod (derw ! i)) = prod (derw' ! i) 
              \<and> after (derw ! i) = h_ext (after (derw' ! i)) 
              \<and> before (derw ! i) = h_ext (before (derw' ! i)) 
              \<and> prefix (derw ! i) = h_ext (prefix (derw' ! i)) 
              \<and> suffix (derw ! i) = h_ext (suffix (derw' ! i)) )\<close> using local.Suc.hyps(2) n_eq_0 using less_Suc0 by force
            then show ?thesis using \<open>derw' \<in> DerWits P' [Nt S] w'\<close> \<open>length derw' = length derw\<close> by blast
          next
            case False
            then have n_geq_1: \<open>n > 0\<close> by simp
            then have derw_front_not_empty: \<open>derw_front \<noteq> []\<close> by (simp add: \<open>n = length derw_front\<close>)
            then have \<open>derw_front \<in> DerWits P [Nt S] (before derw_step)\<close> using derw_split derw_DerWits append_DerWits'[of derw_front \<open>[derw_step]\<close> P \<open>[Nt S]\<close> w] by simp
            with IH[OF \<open>n = length derw_front\<close> \<open>derw_front \<in> DerWits P [Nt S] (before derw_step)\<close>]  obtain wb' derw'_front where 
              derw'_DerWits: \<open>derw'_front \<in> DerWits P' [Nt S] wb'\<close> and
              length_derw': \<open>length derw'_front = length derw_front\<close> and
              front_h_front: \<open> (\<And>i. i<length derw'_front \<Longrightarrow> 
                transform_production (prod (derw_front ! i)) = prod (derw'_front ! i) 
                \<and> after (derw_front ! i) = h_ext (after (derw'_front ! i)) 
                \<and> before (derw_front ! i) = h_ext (before (derw'_front ! i)) 
                \<and> prefix (derw_front ! i) = h_ext (prefix (derw'_front ! i)) 
                \<and> suffix (derw_front ! i) = h_ext (suffix (derw'_front ! i)))\<close> by blast

            have derw_step_DerWit: \<open>[derw_step] \<in> DerWits P (after (last derw_front)) w\<close> using derw_DerWits by (simp add: append_DerWits'(3) derw_front_not_empty derw_split)
            then have derw_step_DerSeq: \<open>[derw_step] \<in> DerSeqs P\<close> by (simp add: is_DerSeq_one)


            have last_derw'_front_index: \<open>last derw'_front = derw'_front ! (length derw'_front - 1)\<close> by (metis False List.list.size(3) \<open>n = length derw_front\<close> last_conv_nth length_derw')
            have last_derw_front_index:\<open>last derw_front = derw_front ! (length derw'_front - 1)\<close> using derw_front_not_empty last_conv_nth length_derw' by auto

            have h_after_last: \<open>h_ext (after (last derw'_front)) = after (last derw_front)\<close> using front_h_front[of \<open>(length derw'_front - 1)\<close>] by (metis \<open>n = length derw_front\<close> diff_less last_derw'_front_index last_derw_front_index length_derw' less_numeral_extra(1) n_geq_1)
            have before_ders_step_split: \<open>before derw_step = prefix derw_step @ [Nt (fst (prod derw_step))] @ suffix derw_step\<close> using before_splits_one derw_step_DerSeq by auto

            have \<open>before derw_step = prefix derw_step @ [Nt (fst (prod derw_step))] @ suffix derw_step\<close> using before_splits_one[of derw_step P] by (simp add: derw_step_DerSeq)

            then have \<open>(length (prefix derw_step)+1) \<le> (length (before derw_step))\<close> by simp
            also have \<open>... = length (after (last derw_front))\<close> using before_hd_eq_one derw_step_DerWit by auto
            also have \<open>... = length (h_ext (after (last derw'_front)))\<close> using h_after_last by simp
            finally have length_prefix_derw_step: \<open>(length (prefix derw_step)+1) \<le> length (h_ext (after (last derw'_front)))\<close> .

            (* now we have to find the right prefix *)
            define before' where \<open>before' = after (last derw'_front)\<close>
            define i_prefix' where \<open>i_prefix' = (letters_needed_until_produced (length (prefix derw_step)+1) (after (last derw'_front))) - 1\<close>
            define prefix' where \<open>prefix' = take i_prefix' (after (last derw'_front))\<close>

            have \<open>take (length (prefix derw_step)) (h_ext (after (last derw'_front))) = h_ext prefix'\<close> using prefix'_def letters_needed_until_produced_pre using h_ext_def i_prefix'_def length_prefix_derw_step by blast

            with h_after_last have \<open>h_ext prefix' = take (length (prefix derw_step)) (after (last derw_front))\<close> by simp
            also have \<open>... = take (length (prefix derw_step)) (before derw_step)\<close> using before_hd_eq_one derw_step_DerWit by auto
            also have \<open>... = (prefix derw_step)\<close> using before_ders_step_split by simp

            finally have h_ext_prefix': \<open>h_ext prefix' = prefix derw_step\<close> .


            have \<open>take (length (prefix derw_step) +1) (h_ext (after (last derw'_front))) = h_ext (take (i_prefix'+1) (after (last derw'_front)))\<close> using prefix'_def letters_needed_until_produced_correct[of \<open>length (prefix derw_step) +1\<close> \<open>after (last derw'_front)\<close>] using h_ext_def i_prefix'_def length_prefix_derw_step by (smt (z3) List.list.size(3) One_nat_def Suc_pred \<open>take (length (prefix derw_step)) (h_ext (after (last derw'_front))) = h_ext prefix'\<close> add_diff_cancel_right' add_eq_if add_leE butlast_take diff_is_0_eq' le_add1 length_butlast length_greater_0_conv plus_1_eq_Suc take_eq_Nil2)
            with h_after_last have \<open>h_ext (take (i_prefix'+1) (after (last derw'_front))) = take (length (prefix derw_step) +1) (after (last derw_front))\<close> by simp
            also have \<open>... = take (length (prefix derw_step) +1) (before derw_step)\<close> using before_hd_eq_one derw_step_DerWit by auto
            also have \<open>... = prefix derw_step @ [Nt (fst (prod derw_step))]\<close> using before_ders_step_split by simp
            finally have h_ext_prefix'_: \<open>h_ext (take (i_prefix'+1) (after (last derw'_front))) = prefix derw_step @ [Nt (fst (prod derw_step))]\<close> .

            have i_prefix'_leq: \<open>i_prefix' + 1 \<le> length (after (last derw'_front))\<close> by (metis Suc_eq_plus1 Suc_n_not_le_n h_ext_prefix' leI length_prefix_derw_step less_eq_iff_succ_less prefix'_def take_all_iff)
            have \<open>take (i_prefix' +1) (after (last derw'_front)) = take i_prefix' (after (last derw'_front)) @ [((after (last derw'_front)) ! i_prefix')]\<close> using take_append_one[of \<open>i_prefix'\<close> \<open>(after (last derw'_front))\<close>] using i_prefix'_leq by fastforce
            then have \<open>h_ext ( [(after (last derw'_front)) ! i_prefix'] ) = [Nt (fst (prod derw_step))]\<close> using h_ext_prefix'_ h_ext_prefix' by (simp add: h_ext_def prefix'_def)
            then have \<open>(after (last derw'_front)) ! (i_prefix') = Nt (fst (prod derw_step))\<close> using h_ext_def by simp 



            then obtain r where \<open>(after (last derw'_front)) = take i_prefix' (after (last derw'_front)) @ [(after (last derw'_front)) ! (i_prefix')] @ r\<close> using split_into_take[OF i_prefix'_leq] using \<open>take (i_prefix' + 1) (after (last derw'_front)) = take i_prefix' (after (last derw'_front)) @ [after (last derw'_front) ! i_prefix']\<close> by auto 

            then have split: \<open>(after (last derw'_front)) = prefix' @ [ Nt (fst (prod derw_step))] @ r\<close> by (simp add: \<open>after (last derw'_front) ! i_prefix' = Nt (fst (prod derw_step))\<close> prefix'_def)

            then have \<open>prefix derw_step @ [ Nt (fst (prod derw_step))] @ h_ext r = h_ext (after (last derw'_front))\<close> using h_ext_def using h_ext_prefix' by auto
            also have \<open>... = after (last derw_front)\<close> by (simp add: h_after_last)
            also have \<open>... = before derw_step\<close> using derw_step_DerWit by force
            also have \<open>... = prefix derw_step @ [Nt (fst (prod derw_step))] @ suffix derw_step\<close> by (simp add: before_ders_step_split)
            finally have \<open>prefix derw_step @ [ Nt (fst (prod derw_step))] @ h_ext r = prefix derw_step @ [Nt (fst (prod derw_step))] @ suffix derw_step\<close> .


            then have h_ext_r: \<open>h_ext r = suffix derw_step\<close> by simp


            define w' where \<open>w' = prefix' @ snd (transform_production (prod derw_step)) @ r\<close>
            define derw'_step where \<open>derw'_step = \<lparr>before = after (last derw'_front), after = w', prod = transform_production (prod derw_step), prefix = prefix', suffix = r\<rparr>\<close>
            define derw' where \<open>derw' = derw'_front @ [derw'_step]\<close>

            have \<open>prod derw_step \<in> P\<close> by (simp add: derw_step_DerSeq in_prods_one)
            have \<open>[derw'_step] \<in> DerSeqs P'\<close> unfolding derw'_step_def apply(rule DerSeqs_singleI)
                apply auto apply (simp add: P'_def \<open>prod derw_step \<in> P\<close>)
               apply (metis List.append.left_neutral \<open>after (last derw'_front) ! i_prefix' = Nt (fst (prod derw_step))\<close> \<open>after (last derw'_front) = take i_prefix' (after (last derw'_front)) @ [after (last derw'_front) ! i_prefix'] @ r\<close> append_Cons eq_fst_iff fst_transform_production prefix'_def)
              by (simp add: w'_def)
            then have derw'_step_DerWit: \<open>[derw'_step] \<in> DerWits P' wb' w'\<close> using derw'_step_def by (smt (verit, ccfv_SIG) DerWitsEmptyD(2) DerWitsI DerWits_appendI List.last.simps List.list.sel(1) One_nat_def Suc_leI Suc_n_not_le_n \<open>n = length derw_front\<close> add_le_mono1 after_last_eq derw'_DerWits last_appendL length_append length_derw' n_geq_1 not_Cons_self2 plus_1_eq_Suc select_convs(1,2))
            then have \<open>derw' \<in> DerWits P' [Nt S] w'\<close> unfolding derw'_def by (meson DerWits_appendI derw'_DerWits) 
            moreover have \<open>length derw' = length derw\<close> by (simp add: derw'_def derw_split length_derw')
            moreover have \<open>(\<forall>i<length derw'. 
                            transform_production (prod (derw ! i)) = prod (derw' ! i) 
                            \<and> after (derw ! i) = h_ext (after (derw' ! i)) 
                            \<and> before (derw ! i) = h_ext (before (derw' ! i)) 
                            \<and> prefix (derw ! i) = h_ext (prefix (derw' ! i)) 
                            \<and> suffix (derw ! i) = h_ext (suffix (derw' ! i)) )\<close>
            proof(intro allI impI, case_tac \<open>i = length derw' -1\<close>, goal_cases)
              case (1 i)
              then have \<open>i = length derw' - 1\<close> by simp
              then have derwi: \<open>derw ! i = derw_step\<close> by (simp add: calculation(2) derw_split)
              then have derw'i: \<open>derw' ! i = derw'_step\<close> by (metis "1"(2) \<open>n = length derw_front\<close> calculation(2) derw'_def diff_add_inverse2 length_derw length_derw' nth_append_length)

              have \<open>transform_production (prod (derw ! i)) = prod (derw' ! i)\<close> using derwi derw'i by (simp add: derw'_step_def)
              moreover have \<open>before (derw ! i) = h_ext (before (derw' ! i))\<close> using derwi derw'i by (simp add: \<open>after (last derw_front) = before derw_step\<close> derw'_step_def h_after_last)
              moreover have \<open>prefix (derw ! i) = h_ext (prefix (derw' ! i))\<close> using derwi derw'i  by (simp add: derw'_step_def h_ext_prefix')
              moreover have \<open>suffix (derw ! i) = h_ext (suffix (derw' ! i))\<close> using derwi derw'i using derw'_step_def h_ext_r by auto
              moreover have \<open>after (derw ! i) = h_ext (after (derw' ! i))\<close> 
              proof-
                have \<open>after (derw' ! i) = w'\<close> using derw'i by (simp add: derw'_step_def)
                moreover have \<open>h_ext (w') = w\<close> using w'_def split by (metis P_CNF \<open>prod derw_step \<in> P\<close> after_last_eq_one after_splits_one derw_step_DerSeq derw_step_DerWit h_ext_def h_ext_prefix' h_ext_r hom_ext_inv the_hom_ext_hom)
                ultimately have \<open>h_ext (after (derw' ! i)) = w\<close> by simp
                have \<open>after (derw ! i) = w\<close> using derwi derw_DerWits after_last_eq using derw_step_DerWit by blast
                with \<open>h_ext (after (derw' ! i)) = w\<close> show ?thesis by simp
              qed

              ultimately show ?case by simp
            next
              case (2 i)
              then have \<open>i < length derw'_front\<close> using \<open>n = length derw_front\<close> calculation(2) length_derw' local.Suc.hyps(2) by linarith
              then have \<open>derw ! i = derw_front ! i\<close> by (simp add: derw_split length_derw' nth_append_left)
              moreover have \<open>derw' ! i = derw'_front ! i\<close> by (simp add: \<open>i < length derw'_front\<close> derw'_def nth_append)
              ultimately show ?case using front_h_front[OF \<open>i < length derw'_front\<close>] by simp
            qed
            ultimately show ?thesis by blast
          qed

        qed    
        then show \<open>\<exists>w' \<in> Ders P' S. w = h_ext w'\<close> sorry
      qed

      then show \<open>\<And>w. (w  \<in> Lang P S \<Longrightarrow> \<exists>w' \<in> L'. w = h w')\<close>
      proof(goal_cases)
        case (1 w)
        then have \<open>(map Tm w) \<in> Ders P S\<close> using Lang_Ders imageI by fastforce
        then obtain w' where w'_def: \<open>w' \<in> Ders P' S\<close> \<open>(map Tm w) = h_ext w'\<close> using \<open>\<And>w. w \<in> Ders P S \<Longrightarrow> \<exists>w'\<in> Ders P' S. w = h_ext w'\<close> by auto
        moreover obtain w'' where \<open>w' = map Tm w''\<close> using w'_def by (metis h_ext_def the_hom_ext_tms_inj)
        then have \<open>w = h w''\<close> using h_eq_h_ext2 h_def h_ext_def by (metis h_eq_h_ext w'_def(2))
        moreover have \<open>w'' \<in> L'\<close> using \<open>w' \<in> Ders P' S\<close> by (metis DersD \<open>L' = dyck_language \<Gamma> \<inter> Re P S\<close> \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re P A)\<close> \<open>w' = map Tm w''\<close>)
        ultimately show ?case by auto
      qed
    qed
    then show \<open>Lang P S \<subseteq> h ` L'\<close> by auto 
  qed

  also have \<open>... = L\<close> by (simp add: \<open>L = Lang P S\<close>)
  finally have \<open>image h ((dyck_language \<Gamma>) \<inter> (Re P S)) = L\<close> by auto

  moreover have hom: \<open>hom h\<close> by (simp add: h_def hom_def)
  moreover have \<open>reg TYPE('n) (Re P S)\<close> sorry
  ultimately have \<open>reg TYPE('n) (Re P S) \<and> L = image h ((Re P S) \<inter> (dyck_language \<Gamma>)) \<and> hom h\<close> by blast 
  then show ?thesis by blast

qed



end