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
aa
aaaa
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

lemma [simp]: \<open>k + 1 \<le> length w' \<Longrightarrow> (take k w') @ [w' ! k] = take (Suc k) w'\<close> by (simp add: take_Suc_conv_app_nth)


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


type_synonym ('n,'t) derivation =  "('n,'t) syms list"

text\<open>Defines the set of derivation sequences\<close>
definition DerSeqs :: \<open>('n,'t)Prods \<Rightarrow> ('n,'t)syms list set \<close> where
\<open>DerSeqs P = {deriv. ( \<forall>i < length deriv - 1.  P \<turnstile> deriv!i \<Rightarrow> deriv!(i+1) ) \<and> deriv \<noteq> []}\<close>

lemma DerSeqsI[intro]:
  assumes "( \<forall>i < length deriv - 1.  P \<turnstile> deriv!i \<Rightarrow> deriv!(i+1) )" and \<open>deriv \<noteq> []\<close> shows "deriv \<in> DerSeqs P"
  using assms by (auto simp: DerSeqs_def)

lemma DerSeqsD[dest]:
  assumes "deriv \<in> DerSeqs P" shows consistent: "( \<forall>i < length deriv - 1.  P \<turnstile> deriv!i \<Rightarrow> deriv!(i+1) )" and DerSeq_not_empty: \<open>deriv \<noteq> []\<close>
  using assms by (auto simp: DerSeqs_def)

lemmas DerSeqsE = DerSeqsD[elim_format]



text\<open>Defines the set of derivation witnesses. This allows for the empty derivation as a witness for undefined\<close>
definition DerWits:: \<open>('n,'t)Prods \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n, 't) syms \<Rightarrow> ('n,'t)syms list set \<close> where
\<open>DerWits P u v = {deriv. deriv \<in> DerSeqs P \<and> (hd deriv = u) \<and> (last deriv = v)}\<close>


lemma DerWitsI[intro]:
  assumes "deriv \<in> DerSeqs P" and \<open>hd deriv = u\<close> and \<open>last deriv = v\<close> shows "deriv \<in> DerWits P u v"
  using assms by (auto simp: DerWits_def)

lemma DerWitsD[dest]:
  assumes "deriv \<in> DerWits P u v" shows deriv_DerSeq: "deriv \<in> DerSeqs P" and hd_deriv: \<open>hd deriv = u\<close> and last_deriv: \<open>last deriv = v\<close> and DerWit_not_empty: \<open>deriv \<noteq> []\<close>
  using assms by (auto simp add: DerWits_def) 

lemmas DerWitsE = DerWitsD[elim_format]




lemma DerSeqs_stepD:
  assumes "deriv \<in> DerSeqs P" and "i < length deriv - 1"
  shows "P \<turnstile> deriv!i \<Rightarrow> deriv!(i+1)"
  using assms by auto

lemmas DerSeqs_stepE = DerSeqs_stepD[elim_format]

lemma DerSeqs_singleton[simp]: "([u]) \<in> DerSeqs P"
  by auto

lemma DerWits_singleton[simp]: "([u]) \<in> DerWits P u u"
  by auto


lemma DerWits_empty[simp, dest!]: \<open>[] \<in> DerWits P u v' \<Longrightarrow> False\<close>
by auto


lemma DerSeqs_append_one:
  assumes "deriv @ [v'] \<in> DerSeqs P"
  and "P \<turnstile> v' \<Rightarrow> v"
  shows "deriv @ [v', v] \<in> DerSeqs P"
proof (auto simp: DerSeqs_def, goal_cases)
  case (1 i)
  then have assm: "i < Suc (length deriv)" .
  have step: "\<And>i. i < length (deriv @ [v']) - 1 \<Longrightarrow> P \<turnstile> (deriv @ [v'])!i \<Rightarrow> (deriv @ [v'])!(i+1)"
    using assms(1) by (auto simp: DerSeqs_def)
  
  show ?case
  proof (cases "i < length (deriv @ [v']) - 1")
    case True
    then show ?thesis using step[OF True]
      by (metis Groups.ab_semigroup_add_class.add.commute add_diff_cancel_left' 
              length_append_singleton not_less_eq not_less_iff_gr_or_eq 
              nth_append nth_append_length plus_1_eq_Suc)
  next
    case False
    then have li: "i = length deriv" using assm by simp
    then have "(deriv @ [v', v]) ! i = v'" by simp
    moreover have "(deriv @ [v', v]) ! (Suc i) = v" 
      by (metis One_nat_def Suc_eq_plus1_left li
              add_diff_cancel_right' le_add2 nth_Cons_0 nth_Cons_Suc nth_append_right)
    ultimately show ?thesis by (simp add: assms(2))

  qed
qed


lemma DerSeqs_append:
  assumes "deriv \<in> DerSeqs P"
  and "deriv' \<in> DerSeqs P"
  and \<open>P \<turnstile> last deriv \<Rightarrow> hd deriv'\<close>
  shows "deriv @ deriv' \<in> DerSeqs P"
proof(standard, intro allI impI)
    fix i
    assume i_less: \<open>i < length (deriv @ deriv') - 1\<close>
    have deriv_not_empty: \<open>deriv \<noteq> []\<close> using assms(1) by auto
    have deriv'_not_empty: \<open>deriv' \<noteq> []\<close> using assms(2) by auto
    then show \<open>P \<turnstile> (deriv @ deriv') ! i \<Rightarrow> (deriv @ deriv') ! (i + 1)\<close>
    proof(cases \<open>i < length deriv -1\<close>)
      case True
      then show ?thesis by (metis DerSeqs_stepD add_lessD1 assms(1) less_diff_conv nth_append)
    next
      case False
      then have i_geq: \<open>\<not> i < length deriv - 1\<close> by simp
      then show ?thesis
      proof(cases \<open>i = length deriv -1\<close>)
        case True
        then have \<open>(deriv) ! i = last deriv\<close> using deriv_not_empty by (simp add: last_conv_nth)
        moreover have hd: \<open>(deriv @ deriv') ! (i + 1) = hd deriv'\<close>  using deriv'_not_empty by (simp add: True deriv_not_empty hd_conv_nth nth_append)
        ultimately show ?thesis using assms(3) by (simp add: True deriv_not_empty nth_append)
      next
        case False
        then have i_bounds: \<open>i > length deriv - 1 \<close> \<open>i < length (deriv @ deriv') - 1\<close> using False i_geq i_less by simp+
        from \<open>deriv' \<in> DerSeqs P\<close> have deriv': \<open>\<And>i. i < length (deriv') - 1 \<Longrightarrow> P \<turnstile> (deriv') ! i \<Rightarrow> (deriv') ! (i + 1)\<close> by auto
        define i' where \<open>i' = i - length deriv\<close>
        then have  \<open>(deriv @ deriv') ! i = deriv' ! i'\<close> using i_bounds deriv_not_empty deriv'_not_empty by (metis Suc_diff_1 length_greater_0_conv not_less_eq nth_append)
        moreover have \<open>(deriv @ deriv') ! (i + 1) = deriv' ! (i' + 1)\<close> using i'_def deriv_not_empty deriv'_not_empty by (metis Suc_diff_1 Suc_leI add_diff_assoc2 i_bounds(1) i_geq length_greater_0_conv less_diff_conv nth_append)
        moreover have \<open>i' < length deriv' - 1\<close> using i'_def using i_bounds by auto

        ultimately show ?thesis using deriv'[of i'] by auto
      qed
    qed
  next
    show \<open>deriv @ deriv' \<noteq> []\<close> using assms(1) by auto
    qed




corollary DerWits_append_one:
  assumes "deriv \<in> DerWits P u v'"
  and "P \<turnstile> v' \<Rightarrow> v"
  shows "deriv @ [v] \<in> DerWits P u v"
proof -
  have "deriv \<noteq> []" using assms(1) by auto
  then obtain beg where beg_def: "deriv = beg @ [v']" by (metis DerWitsD(3) assms(1) snoc_eq_iff_butlast)
  then have "beg @ [v'] \<in> DerSeqs P" using assms(1) by (auto simp: DerWits_def)
  then have "beg @ [v', v] \<in> DerSeqs P" using DerSeqs_append[of beg P \<open>[v', v]\<close>] by (simp add: DerSeqs_append_one assms(2))
  moreover have "hd (beg @ [v', v]) = hd deriv" using beg_def by (simp add: hd_append)  
  moreover have "last (beg @ [v', v]) = v" by simp
  ultimately show ?thesis using assms(1) beg_def by (auto simp: DerWits_def)
qed


lemma last_append_deriv[simp]:
assumes \<open>deriv \<in> DerWits P u v\<close>
shows \<open>last (deriv' @ deriv) = v\<close>
using assms last_appendR by blast

lemma hd_deriv_append[simp]:
assumes \<open>deriv \<in> DerWits P u v\<close>
shows \<open>hd (deriv @ deriv') = u\<close>
using assms by (simp add: DerWitsD(2,4))



corollary DerWits_append:
  assumes "deriv \<in> DerWits P u v"
  and "deriv' \<in> DerWits P v' v''"
  and \<open>P \<turnstile> v \<Rightarrow> v'\<close>
  shows "deriv @ deriv' \<in> DerWits P u v''"
  apply(rule DerWitsI)
apply(rule DerSeqs_append[of deriv P deriv']) 
using assms by auto




lemma DerWits_imp_deriven:
  assumes "deriv \<in> DerWits P u v"
  shows "P \<turnstile> u \<Rightarrow>(length deriv - 1) v"
proof -
  from assms have "deriv \<in> DerSeqs P" and "hd deriv = u" and "last deriv = v" by (auto simp: DerWits_def)
  then have not_empty: "deriv \<noteq> []" and step: "\<And>i. i < length deriv - 1 \<Longrightarrow> P \<turnstile> deriv!i \<Rightarrow> deriv!(i+1)" apply (simp add: DerSeq_not_empty) using \<open>deriv \<in> DerSeqs P\<close> by blast
  have ind: "i < (length deriv) \<Longrightarrow> P \<turnstile> deriv!0 \<Rightarrow>(i) deriv!i" for i
  proof (induction i)
    case 0
    then show ?case by simp
  next
    case (Suc i)
    have "P \<turnstile> deriv ! 0 \<Rightarrow>(i) deriv ! i" using Suc_lessD local.Suc.IH local.Suc.prems by blast
    moreover have "P \<turnstile> deriv ! i \<Rightarrow> deriv ! (Suc i)" using step not_empty using Suc_eq_plus1 less_diff_conv local.Suc.prems by presburger
    ultimately show ?case by auto
  qed

  have l: "length deriv - 1 < length deriv" using not_empty by simp
  have "u = deriv ! 0" using \<open>hd deriv = u\<close> hd_conv_nth not_empty by auto
  moreover have "v = deriv ! (length deriv - 1)" using \<open>last deriv = v\<close> last_conv_nth not_empty by auto
  ultimately show ?thesis using ind[OF l] by simp
qed




lemma deriven_imp_DerWits:
  assumes "P \<turnstile> u \<Rightarrow>(i) v"
  shows "\<exists>deriv. (deriv \<in> DerWits P u v \<and> length deriv = (i+1))"
using assms proof (induction "i" arbitrary: v)
  case 0
  then have "u = v" by simp
  then have "([u]) \<in> DerSeqs P" by simp
  then have "([u]) \<in> DerWits P u v" by (simp add: \<open>u = v\<close>)
  then show ?case by auto
next
  case (Suc i)
  from \<open>P \<turnstile> u \<Rightarrow>(Suc i) v\<close> obtain v' where "P \<turnstile> u \<Rightarrow>(i) v'" "P \<turnstile> v' \<Rightarrow> v" by auto
  from Suc.IH obtain deriv where "deriv \<in> DerWits P u v' \<and> length deriv = i + 1" using \<open>P \<turnstile> u \<Rightarrow>(i) v'\<close> by auto
  then have "deriv @ [v] \<in> DerWits P u v" by (metis DerWits_append_one \<open>P \<turnstile> v' \<Rightarrow> v\<close>)
  then show ?case by (metis Suc_eq_plus1 \<open>deriv \<in> DerWits P u v' \<and> length deriv = i + 1\<close> length_append_singleton)
qed




corollary deriven_iff_DerWits:
  "P \<turnstile> u \<Rightarrow>(i) v \<longleftrightarrow> (\<exists>deriv. (deriv \<in> DerWits P u v \<and> length deriv = (i+1)))"
  using deriven_imp_DerWits DerWits_imp_deriven by (metis add_diff_cancel_right')

corollary derives_iff_DerWits:
  "P \<turnstile> u \<Rightarrow>* v \<longleftrightarrow> (\<exists>deriv. (deriv \<in> DerWits P u v))"
  using deriven_iff_DerWits by (metis DerWits_imp_deriven relpowp_imp_rtranclp rtranclp_imp_relpowp)

(*end section derivation Witnesses*)
















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



  then have \<open>L' = (dyck_language \<Gamma>) \<inter> (Re P S)\<close> by (metis CFL_Lang_eq_CFG_Lang CFL_Lang_if_derives L'_def P'_def derives_if_CFL_Lang inf_absorb2 inf_commute subsetI)
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
        thm derives_bu.induct[where ?x1.0 = \<open>[Nt S]\<close> and ?x2.0 = \<open>w\<close> and ?Pa = \<open>\<lambda>x1 x2. x1 = [Nt S] \<longrightarrow> (\<exists>w' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> x2 = h_ext w')\<close>]
        
        
        (*
        define Q :: "('n, 't) sym list \<Rightarrow> ('n, 't) sym list \<Rightarrow> bool" where \<open>Q = (\<lambda>\<alpha> x2. \<alpha> = [Nt S] \<and> (\<exists>w'. (P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> x2 = h_ext w')))\<close>
        term Q 
        *)

        thm derives_bu.cases
        print_statement derives_bu.induct
        print_statement derives_bu.induct[where Pa = \<open>(\<lambda>\<alpha> x2. \<alpha> = [Nt S] \<longrightarrow> (\<exists>w'. (P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> x2 = h_ext w')))\<close> and ?x1.0 = \<open>[Nt S]\<close> and ?x2.0 = \<open>w\<close>]
        

        then have \<open>P \<turnstile> [Nt S] \<Rightarrow>*  w\<close> by (simp add: DersD)
        then have \<open>P \<turnstile> [Nt S] \<Rightarrow>bu  w\<close> by (simp add: derives_bu_if)
        have \<open>([Nt S]::('n, 't) sym list) = [Nt S] \<longrightarrow> (\<exists>w' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> w = h_ext w')\<close> (* das sollte eigentlich mit derives_bu.induct[where Pa = \<open>Q\<close>] gezeigt werden, aber das geht nicht? *)
         proof(rule derives_bu.induct[where Pa = \<open>(\<lambda>\<alpha> x2. \<alpha> = [Nt S] \<longrightarrow> (\<exists>w' \<in> Ders P' S. (P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> x2 = h_ext w')))\<close> and ?x1.0 = \<open>[Nt S]\<close> and ?x2.0 = \<open>w\<close> and ?P = \<open>P\<close>], goal_cases)
           case 1
           then show ?case by (simp add: \<open>P \<turnstile> [Nt S] \<Rightarrow>bu w\<close>)
         next
           case (2 \<alpha>)
           define w'::\<open>('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym list\<close> where \<open>w' = [Nt S]\<close>
           then show ?case
           proof(clarify)
            have \<open>[Nt S] = h_ext w'\<close> by (simp add: h_ext_def w'_def)
            then show \<open>\<exists>w' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> [Nt S] = h_ext w'\<close> using bu_refl w'_def by (metis DersI derives_if_bu)
           qed

         next
           case (3 A \<alpha>)
           then show ?case
           proof(clarify)
            assume \<open>(S,\<alpha>) \<in> P\<close>
            and \<open>A = S\<close>

            then have \<open>CNF_rule (S, \<alpha>)\<close> using P_CNF by simp
            define \<alpha>' where \<open>\<alpha>' = (snd (transform_production (S,\<alpha>))) \<close>
            then have \<open>h_ext \<alpha>' = \<alpha>\<close> using h_ext_def hom_ext_inv \<open>CNF_rule (S, \<alpha>)\<close> unfolding \<alpha>'_def by fastforce
            then have \<open>P' \<turnstile> [Nt S] \<Rightarrow>bu \<alpha>'\<close> using transform_production_one_step_bu \<alpha>'_def by (metis P'_def P_CNF \<open>(S, \<alpha>) \<in> P\<close>)
            moreover have \<open>\<alpha>' \<in> Ders P' S\<close> by (simp add: DersI calculation derives_if_bu)
            ultimately show \<open>\<exists>w' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> \<alpha> = h_ext w'\<close> by (metis \<open>h_ext \<alpha>' = \<alpha>\<close>)
           qed
         next
           case (4 \<alpha> \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3 \<beta>)
           then show ?case
           proof(clarify)
            assume 1:\<open>P \<turnstile> [Nt S] \<Rightarrow>bu \<alpha>\<^sub>1 @ \<alpha>\<^sub>2 @ \<alpha>\<^sub>3\<close>
            and 2:\<open>[Nt S] = [Nt S] \<longrightarrow> (\<exists>w' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> \<alpha>\<^sub>1 @ \<alpha>\<^sub>2 @ \<alpha>\<^sub>3 = h_ext w')\<close>
            and 3:\<open>P \<turnstile> \<alpha>\<^sub>2 \<Rightarrow>bu \<beta>\<close>
            and 4:\<open>\<alpha>\<^sub>2 = [Nt S] \<longrightarrow> (\<exists>w' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> \<beta> = h_ext w')\<close>
            and 5:\<open>\<alpha> = [Nt S]\<close>

            have \<open>\<exists>\<alpha>' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu \<alpha>' \<and> \<alpha>\<^sub>1 @ \<alpha>\<^sub>2 @ \<alpha>\<^sub>3 = h_ext \<alpha>'\<close> using 2 by simp
            have \<open>\<exists>\<beta>' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu \<beta>' \<and> \<beta> = h_ext \<beta>'\<close> using 4 sorry
            
            have \<open>\<exists>w'\<in>Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> (\<alpha>\<^sub>1 @ \<beta> @ \<alpha>\<^sub>3) = h_ext w'\<close> sorry



            then show \<open>\<exists>w' \<in> Ders P' S. P' \<turnstile> [Nt S] \<Rightarrow>bu w' \<and> \<alpha>\<^sub>1 @ \<beta> @ \<alpha>\<^sub>3 = h_ext w'\<close> sorry
           qed
           
           
         qed
        
       
























          case base
          define w' where \<open>(w'::('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym list) = [Nt S]\<close>
          then have \<open>w' \<in> Ders P' S\<close> by (simp add: DersI)
          moreover have \<open>P' \<turnstile> [Nt S] \<Rightarrow>l* w'\<close> by (simp add: w'_def)
          moreover have \<open>[Nt S] = h_ext w'\<close> unfolding h_ext_def w'_def by simp
          ultimately show ?case by auto
        next
          case (step u A v w)
          have \<open>CNF_rule (A,w)\<close> using P_CNF \<open>(A,w) \<in> P\<close> by auto
          obtain w' where w'_derive: \<open>P' \<turnstile> [Nt S] \<Rightarrow>l* w' \<and> map Tm u @ [Nt A] @ v = h_ext w'\<close> and w'_Ders: \<open>w' \<in> Ders P' S\<close>using local.step.IH by blast
          then have w_split_h: \<open>map Tm u @ [Nt A] @ v = h_ext w'\<close> by auto
          obtain r where \<open>(A, r) = transform_production (A, w)\<close> by (metis fst_eqD fst_transform_production surj_pair)
          then have \<open>(A,r) \<in> P'\<close> using P'_def local.step.hyps(2) by auto
          from \<open>(A, r) = transform_production (A, w)\<close> have \<open>h_ext r = w\<close> using hom_ext_inv \<open>CNF_rule (A,w)\<close> by (metis h_ext_def snd_conv)

          from w_split_h obtain u' v' where u'_v'_def: \<open>w' = map Tm u' @ [Nt A] @ v'\<close> using the_hom_ext_var_split h_ext_def by metis

          have \<open>map Tm u @ [Nt A] @ v = h_ext w'\<close> using w_split_h by simp
          also have \<open>... = h_ext (map Tm u' @ [Nt A] @ v')\<close> using u'_v'_def by simp
          also have \<open>... = (h_ext (map Tm u')) @ [(Nt A)] @ (h_ext v')\<close> using h_ext_def by simp
          finally have \<open>map Tm u @ [Nt A] @ v  =  (h_ext (map Tm u')) @ [(Nt A)] @ (h_ext v')\<close> .

          moreover then have \<open>map Tm u = h_ext (map Tm u')\<close> using h_ext_def same_prefix by fastforce
          ultimately have \<open>v = (h_ext v')\<close> by simp

          then have \<open>h_ext (map Tm u' @ r @ v') = map Tm u @ w @ v\<close> using \<open>h_ext r = w\<close> \<open>map Tm u = h_ext (map Tm u')\<close> h_ext_def by auto

          then have \<open>P' \<turnstile> [Nt S] \<Rightarrow>l* map Tm u' @ [Nt A] @ v'\<close> using w'_derive using u'_v'_def by blast
          then have \<open>P' \<turnstile> [Nt S] \<Rightarrow>l* map Tm u' @ r @ v'\<close> using \<open>(A,r) \<in> P'\<close> by (simp add: CFG.derivel.intros Transitive_Closure.rtranclp.rtrancl_into_rtrancl)

          then show ?case using \<open>h_ext (map Tm u' @ r @ v') = map Tm u @ w @ v\<close> w'_Ders using Ders_def derivels_imp_derives by fastforce
        qed
        then show \<open>\<exists>w' \<in> Ders P' S. w = h_ext w'\<close> by auto
      qed

      then show \<open>\<And>w. (w  \<in> Lang P S \<Longrightarrow> \<exists>w' \<in> L'. w = h w')\<close>
      proof(goal_cases)
        case (1 w)
        then have \<open>(map Tm w) \<in> Ders P S\<close> using Lang_Ders imageI by fastforce
        then obtain w' where w'_def: \<open>w' \<in> Ders P' S\<close> \<open>(map Tm w) = h_ext w'\<close> using \<open>\<And>w. w \<in> Ders P S \<Longrightarrow> \<exists>w'\<in> Ders P' S. w = h_ext w'\<close> by auto
        moreover obtain w'' where \<open>w' = map Tm w''\<close> using w'_def by (metis h_ext_def the_hom_ext_tms_inj)
        then have \<open>w = h w''\<close> using h_eq_h_ext2 h_def h_ext_def by (metis h_eq_h_ext w'_def(2))
        moreover have \<open>w'' \<in> L'\<close> using \<open>w' \<in> Ders P' S\<close> by (metis DersD P'_def \<open>L' = dyck_language \<Gamma> \<inter> Re P S\<close> \<open>\<forall>A x. (transform_production ` P \<turnstile> [Nt S] \<Rightarrow>* map Tm x) = (x \<in> dyck_language \<Gamma> \<inter> Re P A)\<close> \<open>w' = map Tm w''\<close>)
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