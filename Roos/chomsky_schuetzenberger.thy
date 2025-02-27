theory chomsky_schuetzenberger
  imports Finite_Automata_HF.Finite_Automata_HF HOL.Nat "../CFG" "../CFL"
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
definition transform_production :: "('n, 't) prod \<Rightarrow> 
('n, bracket \<times> ('n,'t) prod \<times> version) prod" where
  "transform_production p = (
    case p of
      (A, [Nt B, Nt C]) \<Rightarrow> 
        (A, [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ]) | 
      (A, [Tm a]) \<Rightarrow>   
        (A, [ Tm (Op, (p,One)),       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ]) 
)"


text\<open>Definition of what it means to be a chomksy-form rule.\<close>
definition CNF_rule :: "('c \<times> ('c, 'b) sym list) \<Rightarrow> bool" where
\<open>CNF_rule p \<equiv>  (\<exists>(A::'c) B C. (p = (A,[Nt B, Nt C]))) \<or> (\<exists>A a. p= (A, [Tm a]))\<close>

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
\<open>the_hom_helper (br, (p, i)) = 
    (case p of 
    (A, [Nt B, Nt C]) \<Rightarrow> [] | 
    (A, [Tm a]) \<Rightarrow> (if br = Op \<and> i=One then [a] else []) | 
    _ \<Rightarrow> []
    )
\<close>


text\<open>helper function for the definition of the extended \<open>h_ext\<close>\<close>
fun the_hom_ext_helper :: \<open>('a, bracket \<times> ('a,'b) prod \<times> version ) sym \<Rightarrow> ('a,'b) sym list\<close> where
\<open>the_hom_ext_helper (Tm (br, (p, i))) = 
    (case p of 
    (A, [Nt B, Nt C]) \<Rightarrow> [] | 
    (A, [Tm a]) \<Rightarrow> (if br = Op \<and> i=One then [Tm a] else []) | 
    _ \<Rightarrow> []
    )\<close> | 
\<open>the_hom_ext_helper (Nt A) = [Nt A]\<close>



text\<open>The needed homomorphism in the proof\<close>
fun the_hom :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) list \<Rightarrow> 'b list \<close> where
\<open>the_hom l = concat (map the_hom_helper l)\<close>

text\<open>The needed homomorphism in the proof, but extended on Variables\<close>
fun the_hom_ext :: \<open>('a, bracket \<times> ('a,'b) prod \<times> version ) sym list \<Rightarrow> ('a,'b) sym list \<close> where
\<open>the_hom_ext l = concat (map the_hom_ext_helper l)\<close>


text\<open>helper for showing the next lemma\<close>
lemma helper: \<open>the_hom_ext_helper (Tm x) = map Tm (the_hom_helper x)\<close>
apply(induction x rule: the_hom_helper.induct)
by(auto split: list.splits sym.splits)

text\<open>Show that the extension really is an extension in some sense.\<close>
lemma \<open>the_hom_ext (map Tm x) = map Tm (the_hom x)\<close>
apply(induction x)
apply(simp)
using helper by fastforce




text\<open>The chomsky-scheutzenberger theorem that we want to prove.\<close>
lemma chomsky_schuetzenberger :
fixes L::\<open>'t list set\<close>
assumes \<open>CFL.cfl TYPE('n) L\<close> 
shows \<open>\<exists>(R::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set) h \<Gamma>. (reg TYPE('n) R) \<and> (L = image h (R \<inter> dyck_language \<Gamma>)) \<and> hom h\<close>
proof -
have \<open>\<exists>P S::'n. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> using \<open>cfl TYPE('n) L\<close> CNF_existence by auto
then obtain P and S::'n where \<open>L = Lang P S\<close> and \<open>(\<forall>p \<in> P. CNF_rule p)\<close> by blast

define \<Gamma> where \<open>\<Gamma> = P \<times> {One, Two}\<close>
define P' where \<open>P' = image transform_production P\<close>
define L' where \<open>L' = Lang P' S\<close>
define h where \<open>h = (the_hom::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list \<Rightarrow> 't list)\<close>


have \<open>L' \<subseteq> dyck_language \<Gamma>\<close> sorry (* This might not be needed (but it was listed in the book). Leave this for last *)

have \<open>\<forall>A. \<forall>x. 
(image transform_production P) \<turnstile> [Nt S] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re P A)\<close> sorry (* This is the hard part of the proof - the local lemma in the textbook *)
then have \<open>L' = (dyck_language \<Gamma>) \<inter> (Re P S)\<close> by (metis CFL_Lang_eq_CFG_Lang CFL_Lang_if_derives L'_def P'_def derives_if_CFL_Lang inf_absorb2 inf_commute subsetI)
then have \<open>image h ((dyck_language \<Gamma>) \<inter> (Re P S)) =  image h L'\<close> by simp
also have \<open>... = Lang P S\<close> sorry (* For this h_ext should be used. *)

also have \<open>... = L\<close> by (simp add: \<open>L = Lang P S\<close>)
finally have \<open>image h ((dyck_language \<Gamma>) \<inter> (Re P S)) = L\<close> by auto

moreover have hom: \<open>hom h\<close> by (simp add: h_def hom_def)
moreover have \<open>reg TYPE('n) (Re P S)\<close> sorry
ultimately have \<open>reg TYPE('n) (Re P S) \<and> L = image h ((Re P S) \<inter> (dyck_language \<Gamma>)) \<and> hom h\<close> by blast 
then show ?thesis by blast

qed



end