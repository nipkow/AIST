theory chomsky_schuetzenberger
  imports "../CFG" "../CFL" "../Parse_Tree" "dfa2" "$AFP/Regular-Sets/Regexp_Constructions"
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


text\<open>Version for p = (A, w) (multiple letters) with bsub and esub\<close>
abbreviation open_bracket1' :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("[\<^bsub>_\<^esub>\<^sup>1 ") where
  "[\<^bsub>p\<^esub>\<^sup>1  \<equiv> (Op, (p, One))"

abbreviation close_bracket1' :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("]\<^bsub>_\<^esub>\<^sup>1") where
  "]\<^bsub>p\<^esub>\<^sup>1 \<equiv> (Cl, (p, One))"

abbreviation open_bracket2' :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("[\<^bsub>_\<^esub>\<^sup>2") where
  "[\<^bsub>p\<^esub>\<^sup>2 \<equiv> (Op, (p, Two))"

abbreviation close_bracket2' :: "('a \<times> ('a, 'b) sym list) \<Rightarrow> bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version" ("]\<^bsub>_\<^esub>\<^sup>2 ") where
  "]\<^bsub>p\<^esub>\<^sup>2 \<equiv> (Cl, (p, Two))"



text\<open>definition of what it means to be a balanced string with letters of type \<open>bracket \<times> ('a)\<close> \<close>
inductive bal :: "(bracket  \<times> ('a)) list \<Rightarrow> bool" where
  "bal []" |
  "bal xs \<Longrightarrow> bal ys \<Longrightarrow> bal (xs @ ys)" | 
  "bal xs \<Longrightarrow> bal ((Op, g) # xs @ [(Cl, g)])" 

declare bal.intros(1)[iff] bal.intros(2)[intro,simp] bal.intros(3)[intro!,simp]

lemma bal2[iff]: "bal [(Op,g), (Cl,g)]" using bal.intros(1,3) by fastforce




text\<open>The bracket language over a set R. Every element r \<in> R will get a Closing and an Opening version of itself, via pairing with the type bracket. We later need D := dyck_language ((Prods G) \<times> {1,2})\<close>


definition rhs_in_if :: \<open>('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym list \<Rightarrow> (('a \<times> ('a, 'b) sym list) \<times> version) set \<Rightarrow> bool\<close> where
  \<open>rhs_in_if x \<Gamma> \<equiv> (\<forall>r. Tm (Op, r) \<in> set x \<longrightarrow> r \<in> \<Gamma>) \<and> (\<forall>r. Tm (Cl, r) \<in> set x \<longrightarrow> r \<in> \<Gamma>)\<close>

lemma rhs_in_ifI[intro]:
  assumes \<open>\<And>r br. Tm (br, r) \<in> set x \<Longrightarrow> r \<in> \<Gamma>\<close>
  shows \<open>rhs_in_if x \<Gamma>\<close>
  unfolding rhs_in_if_def using assms by blast

lemma rhs_in_ifD[dest]:
  assumes \<open>rhs_in_if x \<Gamma>\<close>
  shows \<open>\<And>r br. Tm (br, r) \<in> set x \<Longrightarrow> r \<in> \<Gamma>\<close>
  using assms unfolding rhs_in_if_def by (metis (full_types) chomsky_schuetzenberger.bracket.exhaust)

lemmas rhs_in_ifE = rhs_in_ifD[elim_format]


lemma rhs_in_if_del_right: \<open>rhs_in_if (xs@ys) \<Gamma> \<Longrightarrow> rhs_in_if xs \<Gamma>\<close>
proof-
  assume assm: \<open>rhs_in_if (xs@ys) \<Gamma>\<close>
  have \<open>set xs \<subseteq> set (xs @ ys)\<close> by simp
  then show ?thesis using rhs_in_ifD[OF assm] by blast
qed

lemmas rhs_in_if_rightE = rhs_in_if_del_right[elim_format]

lemma rhs_in_if_del_left[dest]: \<open>rhs_in_if (xs@ys) \<Gamma> \<Longrightarrow> rhs_in_if ys \<Gamma>\<close>
proof-
  assume assm: \<open>rhs_in_if (xs@ys) \<Gamma>\<close>
  have \<open>set ys \<subseteq> set (xs @ ys)\<close> by simp
  then show ?thesis using rhs_in_ifD[OF assm] by blast
qed

lemmas rhs_in_if_leftE = rhs_in_if_del_left[elim_format]

lemma rhs_in_if_append[intro, simp]: \<open>rhs_in_if (xs) \<Gamma> \<Longrightarrow> rhs_in_if (ys) \<Gamma> \<Longrightarrow> rhs_in_if (xs@ys) \<Gamma>\<close>
proof-
  assume assm_xs: \<open>rhs_in_if (xs) \<Gamma>\<close>
  assume assm_ys: \<open>rhs_in_if (ys) \<Gamma>\<close>
  then have \<open>set (xs@ys) \<subseteq> set xs \<union> set ys\<close> by simp
  then show ?thesis using rhs_in_ifI[of \<open>xs@ys\<close> \<Gamma>] using assm_xs assm_ys by auto
qed


definition dyck_language :: "'a set \<Rightarrow> (bracket  \<times> ('a)) list set" where
  "dyck_language \<Gamma> = {w. (bal w) \<and> (\<forall>(br,r) \<in> (set w). r \<in> \<Gamma>)}"

lemma dyck_languageI[intro]: 
  assumes \<open>bal w\<close>
    and \<open>\<And>br r. (br,r) \<in> set w \<Longrightarrow> r \<in> \<Gamma>\<close>
  shows \<open>w \<in> dyck_language \<Gamma>\<close>
  using assms unfolding dyck_language_def by blast

lemma dyck_languageD[dest]:
  assumes \<open>w \<in> dyck_language \<Gamma>\<close>
  shows \<open>bal w\<close>
    and \<open>\<And>br r. (br,r) \<in> set w \<Longrightarrow> r \<in> \<Gamma>\<close>
  using assms unfolding dyck_language_def by auto

lemmas dyck_languageE = dyck_languageD[elim_format]

lemma dyck_language_substring[intro]: \<open>bal w \<Longrightarrow> (xs@w@ys) \<in> dyck_language \<Gamma> \<Longrightarrow> w \<in> dyck_language \<Gamma>\<close>
proof-
  assume assms: \<open>bal w\<close> and \<open>(xs@w@ys) \<in> dyck_language \<Gamma>\<close>
  have \<open>set w \<subseteq> set (xs@w@ys)\<close> by (simp add: subsetI)
  then show ?thesis using \<open>bal w\<close> \<open>xs @ w @ ys \<in> dyck_language \<Gamma>\<close> by blast
qed


text\<open>balanced strings of brackets that may contain arbitrary interspersion of Nonterminals\<close>
inductive bal_tm :: "('n, bracket  \<times> ('a)) syms \<Rightarrow> bool" where
  "bal_tm []" |
  "bal_tm [Nt A]" |
  "bal_tm xs \<Longrightarrow> bal_tm ys \<Longrightarrow> bal_tm (xs @ ys)" | 
  "bal_tm xs \<Longrightarrow> bal_tm (Tm (Op, g) # xs @ [Tm (Cl, g)])"

declare bal_tm.intros(1,2)[iff] bal_tm.intros(3)[intro, simp] bal_tm.intros(4)[intro!, simp]

lemma bal_tm_prepend_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (Nt A # xs)\<close> using bal_tm.intros(3) by force
lemma bal_tm_append_Nt[intro!, simp]: \<open>bal_tm xs \<Longrightarrow> bal_tm (xs@[Nt A])\<close> by blast

lemma bal_tm2[iff]: "bal_tm [Tm (Op,g), Tm (Cl,g)]" using bal_tm.intros(1,4) by fastforce

lemma bal_tm2_Nt[iff]: "bal_tm [Tm (Op,g), Tm (Cl,g), Nt A]" using bal_tm.intros(1,3,4) by fastforce









lemma map_Tm_inject[dest!, simp]: "map Tm xs = map Tm ys \<Longrightarrow> xs = ys"
  by (induction xs arbitrary: ys; auto)


lemma split_tm_append: \<open>xs @ ys = map Tm zs \<Longrightarrow> \<exists> xs' ys'. (xs' @ ys' = zs) \<and> (xs = map Tm xs') \<and> (ys = map Tm ys')\<close> 
  by (metis append_eq_map_conv)


lemma bal_imp_bal_tm: \<open>bal xs \<Longrightarrow> bal_tm (map Tm xs)\<close>
  by(induction xs rule: bal.induct; auto)


lemma bal_tm_imp_bal_for_tms: \<open>bal_tm (map Tm xs') \<Longrightarrow> bal xs'\<close>
proof-
  assume assm: \<open>bal_tm (map Tm xs':: ('a, bracket \<times> 'b) sym list)\<close>
  define xs::\<open>('a, bracket \<times> 'b) sym list\<close> where \<open>xs = map Tm xs'\<close> \<comment> \<open>need to enforce the same non-terminal type for xs as for map Tm xs' ...\<close>
  then have \<open>bal_tm xs\<close> using xs_def assm by simp
  from \<open>bal_tm xs\<close> \<open>xs = map Tm xs'\<close> show ?thesis
  proof(induction xs arbitrary: xs' rule: bal_tm.induct)
    case (4 xs g)
    then obtain xs'' where \<open>xs = map Tm xs''\<close> and \<open>xs' = ((Op, g) # (xs'') @ [(Cl, g)])\<close> using split_tm_append by blast
    then have \<open>bal xs''\<close> using "local.4.IH" by blast
    then have \<open>bal ((Op, g) # (xs'') @ [(Cl, g)])\<close> by auto
    then show ?case by (simp add: \<open>xs' = (Op, g) # xs'' @ [(Cl, g)]\<close>)
  next
    case (3 xs ys)
    then show ?case using split_tm_append by blast
  qed auto
qed




section\<open>Function based equivalent description of bal, from T. Nipkow\<close>

text\<open>A stack machine that puts open brackets to the stack, to remember that they must be matched by a closed bracket\<close>
fun stk_bal :: "(bracket \<times> 't) list \<Rightarrow> 't list \<Rightarrow> ((bracket \<times> 't) list) * 't list" where
  "stk_bal [] s = ([],s)" |
  "stk_bal ((Op, g) # xs) s = stk_bal xs (g#s)" |
  "stk_bal ((Cl, g) # xs) (g'#s) = (if g=g' then stk_bal xs s else ((Cl, g) # xs, g' # s))" | 
  "stk_bal xs s = (xs,s)"

lemma stk_bal_append: "stk_bal (xs @ ys) s1 = (let (xs',s1') = stk_bal xs s1 in
stk_bal (xs' @ ys) s1')"
  by(induction xs s1 rule:stk_bal.induct) (auto split: if_splits)

lemma stk_bal_append_if[simp]: "stk_bal xs s1 = ([],s2) \<Longrightarrow> stk_bal (xs @ ys) s1 =
stk_bal ys s2"
  by(simp add: stk_bal_append[of xs])

lemma stk_bal_if_bal:  "bal xs \<Longrightarrow> stk_bal xs s = ([],s)"
  by(induction arbitrary: s rule: bal.induct)(auto split: if_splits)



lemma bal_insert_AB: assumes u: "bal u" shows "u = v@w \<Longrightarrow> bal (v @ (Op, x) # (Cl, x) # w)" using u
proof(induction arbitrary: v w)
  case 1 thus ?case by blast
next
  case (3 u y)
  show ?case
  proof (cases v)
    case Nil
    hence "w = ((Op, y)) # u @ [(Cl, y)]" using "3.prems" by simp
    hence "bal w" using "3.hyps" by blast
    hence "bal ([(Op, x), (Cl, x)] @ w)" by blast
    thus ?thesis using Nil by simp
  next
    case (Cons X v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      from "3.hyps" have "bal (((Op, x) # u @ [(Cl, x)]) @ [(Op, x), (Cl, x)])"
        using bal.intros(2) by blast
      thus ?thesis using Nil Cons 3
        by (metis append_Nil append_Nil2 bal.simps)
    next
      case (snoc w' Y)
      hence u: "u=v'@w'" and [simp]: "X=(Op, y) & Y=(Cl, y)"
        using Cons "3.prems" apply (smt (verit, ccfv_threshold) List.append.assoc List.list.inject append_Cons append_eq_append_conv last_snoc)
        by (metis "local.3.prems" Cons List.append.assoc List.list.inject append_Cons last_snoc snoc)
          \<comment> \<open>this also works by auto, but it takes 4 seconds.\<close>
      thus ?thesis
        by (metis "3.IH" append.assoc append_Cons local.Cons bal.intros(3) snoc)
    qed
  qed
next
  case (2 v' w')
  then obtain r where "v'=v@r \<and> r@w'=w \<or> v'@r=v \<and>w'=r@w" (is "?A \<or> ?B")
    by (auto simp:append_eq_append_conv2)
  thus ?case
  proof
    assume A: ?A
    hence "bal (v @ (Op, x) # (Cl, x) # r)" using "2.IH"(1) by presburger
    hence "bal ((v @ (Op, x) # (Cl, x)#r) @ w')" using \<open>bal w'\<close> by(rule bal.intros(2))
    thus ?thesis using A by auto
  next
    assume B: ?B
    hence "bal (r @ (Op, x) # (Cl, x) # w)" using "2.IH"(2) by presburger
    with \<open>bal v'\<close> have "bal (v'@(r@(Op, x) # (Cl, x)#w))" by(rule bal.intros(2))
    thus ?thesis using B by force
  qed 
qed 



lemma stk_bal_if_stk_bal: "stk_bal w s = ([],[]) \<Longrightarrow> bal (rev(map (\<lambda>x. (Op, x)) s) @ w)"
proof(induction w s rule: stk_bal.induct)
  case (2 x xs s)
  then show ?case by simp
next
  case (3 x xs y s)
  then show ?case by (auto simp add: bal_insert_AB split: if_splits) 
qed (auto)


corollary stk_bal_iff_bal: "stk_bal w [] = ([],[]) \<longleftrightarrow> bal w"
  using stk_bal_if_stk_bal[of w "[]"] stk_bal_if_bal by auto

theorem bal_append_inv: "bal (u @ v) \<Longrightarrow> bal u \<Longrightarrow> bal v"
  using stk_bal_append_if stk_bal_iff_bal by metis


lemma stk_bal_append_inv: \<open>stk_bal (xs@ys) s1 = ([], s') \<Longrightarrow> (let (xs', s1') = stk_bal xs s1 in stk_bal xs s1 = ([], s1'))\<close>
proof(induction xs s1 arbitrary: ys rule: stk_bal.induct)
  case (1 s)
  then show ?case by auto
next
  case (2 g xs s)
  then show ?case by(auto split: prod.splits)
next
  case (3 g xs g' s)
  then show ?case apply simp by (metis List.list.distinct(1) Product_Type.prod.inject)
next
  case (4 A xs s)
  then show ?case by(auto split: prod.splits)
qed


lemma bal_insert: 
  assumes u: "bal u" 
    and b: \<open>bal b\<close>
  shows "u = v@w \<Longrightarrow> bal (v @ b @ w)" 
proof-
  assume uvw: \<open>u = v@w\<close>
  have \<open>stk_bal (b) [] = ([],[])\<close> using assms stk_bal_iff_bal by blast
  have \<open>stk_bal (u) [] = ([],[])\<close> using assms stk_bal_iff_bal by blast

  then obtain s1' where s1'_def: \<open>stk_bal v [] = ([], s1')\<close> by (metis (full_types, lifting) uvw case_prodE stk_bal_append_inv)
  then obtain s' where s'_def: \<open>stk_bal (v @ w) [] = stk_bal (w) s'\<close> using stk_bal_append_if by blast

  then have \<open>([],[]) = stk_bal (v @ w) []\<close> using uvw using \<open>stk_bal u [] = ([], [])\<close> by presburger
  also have \<open>... = stk_bal (w) s'\<close> using s'_def by simp
  also have \<open>... = stk_bal (b@w) s'\<close> by (metis b stk_bal_append_if stk_bal_if_bal)

  finally have \<open>stk_bal (b@w) s' = ([],[])\<close> by simp

  then have \<open>stk_bal (v @ b @ w) [] = ([],[])\<close> using s1'_def by (metis b s'_def stk_bal_append_if stk_bal_if_bal)

  then show \<open>bal (v @ b @ w)\<close> using stk_bal_iff_bal by blast
qed




lemma bal_del: 
  assumes u: "bal u" 
    and b: \<open>bal b\<close>
  shows "u = v @ b @ w \<Longrightarrow> bal (v @ w)" 
proof-
  assume uvbw: \<open>u = v @ b @ w\<close>
  have stk_bal_b: \<open>stk_bal (b) [] = ([],[])\<close> using assms stk_bal_iff_bal by blast
  have stk_bal_vbw: \<open>stk_bal (v @ b @ w) [] = ([],[])\<close> using uvbw assms stk_bal_iff_bal by blast

  then obtain s1' where s1'_def: \<open>stk_bal v [] = ([], s1')\<close> by (metis (full_types, lifting) case_prodE stk_bal_append_inv)

  then have \<open>stk_bal (v@b) [] = ([], s1')\<close> by (metis b stk_bal_append_if stk_bal_if_bal)
  then have \<open>stk_bal (v @  w) [] = ([],[])\<close> using stk_bal_vbw s1'_def by (metis stk_bal_append_if)
  then show \<open>bal (v @ w)\<close> using stk_bal_iff_bal by blast
qed


corollary bal_iff_insert[iff]:
  assumes \<open>bal b\<close>
  shows \<open>bal (v @ b @ w) = bal (v @ w)\<close>
  using bal_del bal_insert by (metis assms)


lemma bal_start_Op: \<open>bal (x#xs) \<Longrightarrow>\<exists>g. x = (Op,g)\<close> 
proof(induction \<open>length (x#xs)\<close> arbitrary: x xs rule: less_induct)
  case less
  have IH: \<open>\<And>w (ws:: (bracket \<times> 'a) list). \<lbrakk>length (w # ws) < length (x # xs); bal (w # ws)\<rbrakk> \<Longrightarrow> \<exists>g. w = (Op, g)\<close> using less by blast
  from less have \<open>bal (x # xs)\<close> by simp
  then show ?case
  proof(induction \<open>x#xs\<close> rule:bal.induct)
    case (2 as bs)
    consider (as_empty)  \<open>as = []\<close> | (bs_empty)\<open>bs = []\<close> | (both_not_empty)\<open>as \<noteq> [] \<and> bs \<noteq> []\<close> by blast
    then show ?case
    proof(cases)
      case as_empty
      then show ?thesis using "local.2.hyps"(4,5) eq_Nil_appendI by blast
    next
      case bs_empty
      then show ?thesis by (metis "local.2.hyps"(2,5) List.append.right_neutral)
    next
      case both_not_empty
      then have \<open>length as < length (x#xs)\<close> by (metis "local.2.hyps"(5) List.append.right_neutral append_eq_conv_conj linorder_not_le take_all_iff)
      moreover have \<open>bal as\<close> by (simp add: "local.2.hyps"(1))
      ultimately have \<open>\<exists>g. hd as = (Op, g)\<close> using IH[of \<open>hd as\<close> \<open>tl as\<close>] using both_not_empty by auto
      moreover have \<open>x = hd as\<close> using both_not_empty by (metis "local.2.hyps"(5) List.list.sel(1) hd_append2)
      ultimately show ?thesis by blast
    qed
  qed auto
qed




lemma bal_Op_split: \<open>bal (x # xs) \<Longrightarrow> \<exists>y r g. bal y \<and> bal r \<and> (x # xs) = (Op, g) # y @ (Cl, g) # r\<close>
proof-
  assume bal_x_xs: \<open>bal (x # xs)\<close>
  then obtain g where x_def: \<open>x = (Op, g)\<close> using bal_start_Op by blast
  then have \<open>bal ((Op, g) # xs) \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> (x # xs) = (Op, g) # y @ (Cl, g) # r\<close>
  proof(induction \<open>length (x # xs)\<close> arbitrary: xs rule: less_induct)
    case less
    have IH: \<open>\<And>w. \<lbrakk>length ((Op, g) # w) < length ((Op, g) # xs); bal ((Op, g) # w)\<rbrakk> \<Longrightarrow> \<exists>y r. bal y \<and> bal r \<and> (Op, g) # w = (Op, g) # y @ (Cl, g) # r\<close> using less by blast
    have \<open>bal ((Op, g) # xs)\<close> using less bal_x_xs by blast
    then show ?case
    proof(induction \<open>(Op,g) # xs\<close> rule: bal.induct)
      case (2 as bs)
      consider (as_empty)  \<open>as = []\<close> | (bs_empty)\<open>bs = []\<close> | (both_not_empty)\<open>as \<noteq> [] \<and> bs \<noteq> []\<close> by blast
      then show ?case
      proof(cases)
        case as_empty
        then show ?thesis using 2 by (metis append_Nil)
      next
        case bs_empty
        then show ?thesis using 2 by (metis append_self_conv)
      next
        case both_not_empty
        then obtain as' where as'_def: \<open>(Op, g) # as' = as\<close> using 2 by (metis append_eq_Cons_conv)
        then have \<open>length ((Op, g) # as') < length ((Op, g) # xs)\<close> by (metis "local.2.hyps"(5) List.append.right_neutral append_eq_conv_conj both_not_empty linorder_not_le take_all_iff)
        with IH \<open>bal as\<close> obtain y r where yr_def: \<open>bal y \<and> bal r \<and> (Op, g) # as' = (Op, g) # y @ (Cl, g) # r\<close> using as'_def by meson

        then have \<open>(Op, g) # xs = (Op, g) # y @ (Cl, g) # r @ bs\<close> using as'_def by (metis "local.2.hyps"(5) List.append.assoc append_Cons)
        moreover have \<open>bal y\<close> and \<open>bal (r@bs)\<close> using yr_def apply blast by (simp add: "local.2.hyps"(3) yr_def)
        ultimately show ?thesis using x_def by blast
      qed
    qed (use x_def in auto)
  qed
  then show ?thesis using x_def using bal_x_xs by blast
qed




lemma bal_not_empty:  
  assumes \<open>bal (x#xs)\<close>
  shows \<open>\<exists>g. x = (Op, g)\<close>
  using assms by (metis (full_types) List.list.distinct(1) List.listrel.simps Product_Type.prod.exhaust_sel bracket.exhaust stk_bal.simps(4) stk_bal_if_bal)








section\<open>Function based equivalent description of bal_tm, from T. Nipkow\<close>

text\<open>A stack machine that puts open brackets to the stack, to remember that they must be matched by a closed bracket\<close>
fun stk_bal_tm :: "('n, bracket \<times> 't) syms \<Rightarrow> 't list \<Rightarrow> ('n, bracket \<times> 't) syms * 't list" where
  "stk_bal_tm [] s = ([],s)" |
  "stk_bal_tm (Tm (Op, g) # xs) s = stk_bal_tm xs (g#s)" |
  "stk_bal_tm (Tm (Cl, g) # xs) (g'#s) = (if g=g' then stk_bal_tm xs s else ((Tm (Cl, g) # xs), g'#s))" | 
  \<open>stk_bal_tm (Nt A # xs) s = stk_bal_tm xs s\<close> | 
  "stk_bal_tm xs s = (xs,s)"

lemma stk_bal_tm_append: "stk_bal_tm (xs @ ys) s1 = (let (xs',s1') = stk_bal_tm xs s1 in
stk_bal_tm (xs' @ ys) s1')"
  by(induction xs s1 rule:stk_bal_tm.induct) (auto split: if_splits)

lemma stk_bal_tm_append_if[simp]: "stk_bal_tm xs s1 = ([],s2) \<Longrightarrow> stk_bal_tm (xs @ ys) s1 =
stk_bal_tm ys s2"
  by(simp add: stk_bal_tm_append[of xs])

lemma stk_bal_tm_if_bal_tm:  "bal_tm xs \<Longrightarrow> stk_bal_tm xs s = ([],s)"
  by(induction arbitrary: s rule: bal_tm.induct)(auto split: if_splits)



lemma bal_tm_insert_AB: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Tm (Op, x) # Tm (Cl, x) # w)" using u
proof(induction arbitrary: v w)
  case 1 thus ?case by simp
next
  case (2 A v w)
  then show ?case
  proof(cases v)
    case Nil
    with 2 have \<open>w = [Nt A]\<close> by (metis append_Nil)
    show ?thesis unfolding Nil \<open>w = [Nt A]\<close> by simp
  next
    case (Cons a list)
    with 2 have \<open>v = [Nt A]\<close> by simp
    then have \<open>w = []\<close> using "2" by blast
    then show ?thesis unfolding \<open>v = [Nt A]\<close> \<open>w = []\<close> by simp
  qed
next
  case (4 u y)
  show ?case
  proof (cases v)
    case Nil
    hence "w = (Tm (Op, y)) # u @ [Tm (Cl, y)]" using "4.prems" by simp
    hence "bal_tm w" using "4.hyps" by blast
    hence "bal_tm ([Tm (Op, x), Tm (Cl, x)] @ w)" by blast
    thus ?thesis using Nil by simp
  next
    case (Cons X v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      from "4.hyps" have "bal_tm ((Tm (Op, x) # u @ [Tm (Cl, x)]) @ [Tm (Op, x), Tm (Cl, x)])"
        using bal.intros(2) by blast
      thus ?thesis using Nil Cons 4
        by (metis append_Nil append_Nil2 bal_tm.simps)
    next
      case (snoc w' Y)
      hence u: "u=v'@w'" and [simp]: "X=Tm (Op, y) & Y=Tm (Cl, y)"
        using Cons "4.prems" apply (smt (verit, ccfv_threshold) List.append.assoc List.list.inject append_Cons append_eq_append_conv last_snoc)
        by (metis "local.4.prems" Cons List.append.assoc List.list.inject append_Cons last_snoc snoc)
          \<comment> \<open>this also works by auto, but it takes 4 seconds.\<close>
      thus ?thesis
        by (metis "4.IH" append.assoc append_Cons local.Cons bal_tm.intros(4) snoc)
    qed
  qed
next
  case (3 v' w')
  then obtain r where "v'=v@r \<and> r@w'=w \<or> v'@r=v \<and>w'=r@w" (is "?A \<or> ?B")
    by (auto simp:append_eq_append_conv2)
  thus ?case
  proof
    assume A: ?A
    hence "bal_tm (v @ Tm (Op, x) # Tm (Cl, x) # r)" using "3.IH"(1) by presburger
    hence "bal_tm ((v @ Tm (Op, x) # Tm (Cl, x)#r) @ w')" using \<open>bal_tm w'\<close> by(rule bal_tm.intros(3))
    thus ?thesis using A by auto
  next
    assume B: ?B
    hence "bal_tm (r @ Tm (Op, x) # Tm (Cl, x) # w)" using "3.IH"(2) by presburger
    with \<open>bal_tm v'\<close> have "bal_tm (v'@(r@Tm (Op, x) # Tm (Cl, x)#w))" by(rule bal_tm.intros(3))
    thus ?thesis using B by force
  qed 
qed 


lemma bal_tm_insert_Nt: assumes u: "bal_tm u" shows "u = v@w \<Longrightarrow> bal_tm (v @ Nt A # w)" using u
proof(induction arbitrary: v w)
  case 1
  then show ?case by blast
next
  case (2 A)
  then show ?case
  proof(cases v)
    case Nil
    with 2 have \<open>w = [Nt A]\<close> by (metis append_Nil)
    show ?thesis unfolding Nil \<open>w = [Nt A]\<close> by simp
  next
    case (Cons a list)
    with 2 have \<open>v = [Nt A]\<close> by simp
    then have \<open>w = []\<close> using "2" by blast
    then show ?thesis unfolding \<open>v = [Nt A]\<close> \<open>w = []\<close> by simp
  qed 
next
  case (3 v' w')
  then obtain r where \<open>(v' = v@r) \<and> (r@w' = w) \<or> (w' = r@w) \<and> (v'@r = v)\<close> (is \<open>?A \<or> ?B\<close>) by (meson append_eq_append_conv2)
  then show ?case
  proof
    assume A: ?A
    then have \<open>bal_tm (v @ Nt A # r)\<close> using "3.IH" by presburger
    then have \<open>bal_tm (v @ Nt A # r @ w')\<close> using \<open>bal_tm w'\<close> using bal_tm.intros(3) by fastforce 
    then show ?thesis using A by blast
  next
    assume B: ?B
    then have \<open>bal_tm (r @ Nt A # w)\<close> using "3.IH" by presburger
    then have \<open>bal_tm (v' @ r @ Nt A # w)\<close> using \<open>bal_tm v'\<close> using bal_tm.intros(3) by fastforce 
    then show ?thesis using B by (metis List.append.assoc)
  qed
next

  case (4 u y)
  show ?case
  proof (cases v)
    case Nil
    hence "w = (Tm (Op, y)) # u @ [Tm (Cl, y)]" using "4.prems" by simp
    hence "bal_tm w" using "4.hyps" by blast
    hence "bal_tm ([Nt A] @ w)" by blast
    thus ?thesis using Nil by simp
  next
    case (Cons X v')
    show ?thesis
    proof (cases w rule:rev_cases)
      case Nil
      from "4.hyps" have "bal_tm ((Tm (Op, x) # u @ [Tm (Cl, x)]) @ [Tm (Op, x), Tm (Cl, x)])"
        using bal.intros(2) by blast
      thus ?thesis using Nil Cons 4
        by (metis append_Nil append_Nil2 bal_tm.simps)
    next
      case (snoc w' Y)
      hence u: "u=v'@w'" and [simp]: "X=Tm (Op, y) & Y=Tm (Cl, y)"
        using Cons "4.prems" apply (smt (verit, ccfv_threshold) List.append.assoc List.list.inject append_Cons append_eq_append_conv last_snoc)
        by (metis "local.4.prems" Cons List.append.assoc List.list.inject append_Cons last_snoc snoc)
          \<comment> \<open>this also works by auto, but it takes 4 seconds.\<close>
      thus ?thesis
        by (metis "4.IH" append.assoc append_Cons local.Cons bal_tm.intros(4) snoc)
    qed
  qed
qed


lemma stk_bal_if_stk_bal_tm: "stk_bal_tm w s = ([],[]) \<Longrightarrow> bal_tm (rev(map (\<lambda>x. Tm (Op, x)) s) @ w)"
proof(induction w s rule: stk_bal_tm.induct)
  case (2 x xs s)
  then show ?case by simp
next
  case (3 x xs y s)
  then show ?case by (auto simp add: bal_tm_insert_AB split: if_splits)
next
  case (4 A xs s)
  then have \<open>stk_bal_tm xs s = ([], [])\<close> by simp
  then show ?case by (metis "local.4.IH" bal_tm_insert_Nt)
qed (auto)

corollary stk_bal_tm_iff_bal_tm: "stk_bal_tm w [] = ([],[]) \<longleftrightarrow> bal_tm w"
  using stk_bal_if_stk_bal_tm[of w "[]"] stk_bal_tm_if_bal_tm by auto

theorem bal_tm_append_inv: "bal_tm (u @ v) \<Longrightarrow> bal_tm u \<Longrightarrow> bal_tm v"
  using stk_bal_tm_append_if stk_bal_tm_iff_bal_tm by metis


lemma stk_bal_tm_append_inv: \<open>stk_bal_tm (xs@ys) s1 = ([], s') \<Longrightarrow> (let (xs', s1') = stk_bal_tm xs s1 in stk_bal_tm xs s1 = ([], s1'))\<close>
proof(induction xs s1 arbitrary: ys rule: stk_bal_tm.induct)
  case (1 s)
  then show ?case by auto
next
  case (2 g xs s)
  then show ?case by(auto split: prod.splits)
next
  case (3 g xs g' s)
  then show ?case apply simp by (metis List.list.distinct(1) Product_Type.prod.inject)
next
  case (4 A xs s)
  then show ?case by(auto split: prod.splits)
next
  case (5 vd va)
  then show ?case by(auto split: prod.splits)
qed


lemma bal_tm_insert: 
  assumes u: "bal_tm u" 
    and b: \<open>bal_tm b\<close>
  shows "u = v@w \<Longrightarrow> bal_tm (v @ b @ w)" 
proof-
  assume uvw: \<open>u = v@w\<close>
  have \<open>stk_bal_tm (b) [] = ([],[])\<close> using assms stk_bal_tm_iff_bal_tm by blast
  have \<open>stk_bal_tm (u) [] = ([],[])\<close> using assms stk_bal_tm_iff_bal_tm by blast

  then obtain s1' where s1'_def: \<open>stk_bal_tm v [] = ([], s1')\<close> by (metis (full_types, lifting) uvw case_prodE stk_bal_tm_append_inv)
  then obtain s' where s'_def: \<open>stk_bal_tm (v @ w) [] = stk_bal_tm (w) s'\<close> using stk_bal_tm_append_if by blast

  then have \<open>([],[]) = stk_bal_tm (v @ w) []\<close> using uvw using \<open>stk_bal_tm u [] = ([], [])\<close> by presburger
  also have \<open>... = stk_bal_tm (w) s'\<close> using s'_def by simp
  also have \<open>... = stk_bal_tm (b@w) s'\<close> by (metis b stk_bal_tm_append_if stk_bal_tm_if_bal_tm)

  finally have \<open>stk_bal_tm (b@w) s' = ([],[])\<close> by simp

  then have \<open>stk_bal_tm (v @ b @ w) [] = ([],[])\<close> using s1'_def by (metis b s'_def stk_bal_tm_append_if stk_bal_tm_if_bal_tm)

  then show \<open>bal_tm (v @ b @ w)\<close> using stk_bal_tm_iff_bal_tm by blast
qed




lemma bal_tm_del: 
  assumes u: "bal_tm u" 
    and b: \<open>bal_tm b\<close>
  shows "u = v @ b @ w \<Longrightarrow> bal_tm (v @ w)" 
proof-
  assume uvbw: \<open>u = v @ b @ w\<close>
  have stk_bal_tm_b: \<open>stk_bal_tm (b) [] = ([],[])\<close> using assms stk_bal_tm_iff_bal_tm by blast
  have stk_bal_tm_vbw: \<open>stk_bal_tm (v @ b @ w) [] = ([],[])\<close> using uvbw assms stk_bal_tm_iff_bal_tm by blast

  then obtain s1' where s1'_def: \<open>stk_bal_tm v [] = ([], s1')\<close> by (metis (full_types, lifting) case_prodE stk_bal_tm_append_inv)

  then have \<open>stk_bal_tm (v@b) [] = ([], s1')\<close> by (metis b stk_bal_tm_append_if stk_bal_tm_if_bal_tm)
  then have \<open>stk_bal_tm (v @  w) [] = ([],[])\<close> using stk_bal_tm_vbw s1'_def by (metis stk_bal_tm_append_if)
  then show \<open>bal_tm (v @ w)\<close> using stk_bal_tm_iff_bal_tm by blast
qed


corollary bal_tm_iff_insert[iff]:
  assumes \<open>bal_tm b\<close>
  shows \<open>bal_tm (v @ b @ w) = bal_tm (v @ w)\<close>
  using bal_tm_del bal_tm_insert by (metis assms)















































































text\<open>TODO mv?\<close>
lemma list_length_1_imp_ex: \<open>length l = 1 \<Longrightarrow> \<exists>x. l = [x]\<close> apply auto by (simp add: length_Suc_conv)


lemma list_length_2_imp_ex: \<open>length l = 2 \<Longrightarrow> \<exists>x y. l = [x, y]\<close>
  by(induction l; use list_length_1_imp_ex in auto)

lemma length_append_one: \<open>length (l1 @ [l]) = (length l1 +1)\<close> by simp





section\<open>Grammar/Production transformation\<close>

text\<open>The transformation of old productions to new productions used in the proof.\<close>
fun transform_production :: "('n, 't) prod \<Rightarrow> 
('n, bracket \<times> ('n,'t) prod \<times> version) prod" where
  \<open>  transform_production (A, [Nt B, Nt C]) =    
        (A, [ Tm (Op, (A, [Nt B, Nt C]), One), Nt B, Tm (Cl, (A, [Nt B, Nt C]), One), Tm (Op, (A, [Nt B, Nt C]), Two), Nt C, Tm (Cl, (A, [Nt B, Nt C]), Two)  ])  \<close> | 

\<open> transform_production (A, [Tm a])  = 
        (A, [ Tm (Op, (A, [Tm a]),One),       Tm (Cl, (A, [Tm a]), One), Tm (Op, ((A, [Tm a]), Two)),       Tm (Cl, (A, [Tm a]), Two)  ]) \<close> | 

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





text\<open>Definition of what it means to be a chomksy-form rule.\<close>
definition CNF_rule :: "('n,'t) prod \<Rightarrow> bool" where
  \<open>CNF_rule p \<equiv>  (\<exists>(A::'n) B C. (p = (A,[Nt B, Nt C]))) \<or> (\<exists>A a. p= (A, [Tm a]))\<close>


lemma transform_production_CNF: \<open>CNF_rule p \<Longrightarrow> (\<exists>A B C. transform_production p = (A, [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ]) \<and> p = (A, [Nt B, Nt C])) \<or> (\<exists>A a. transform_production p = (A, [ Tm [\<^sub>p\<^sup>1,       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ]) \<and> p = (A, [Tm a]) )\<close>
  unfolding CNF_rule_def by auto

lemma transform_production_when_CNF: 
  assumes \<open>CNF_rule p\<close>
  shows \<open>\<exists>A B C a.    
 p = (A, [Nt B, Nt C]) \<and> transform_production p = (A, [ Tm (Op, (A, [Nt B, Nt C]), One), Nt B, Tm (Cl, ((A, [Nt B, Nt C]), One)), Tm (Op, (A, [Nt B, Nt C]), Two), Nt C, Tm (Cl, (A, [Nt B, Nt C]), Two)  ])  
\<or>
 p = (A, [Tm a])       \<and> transform_production p =   (A, [ Tm (Op, (A, [Tm a]),One),       Tm (Cl, (A, [Tm a]), One), Tm (Op, (A, [Tm a]), Two),       Tm (Cl, (A, [Tm a]), Two)  ])  
\<close>
  using assms unfolding CNF_rule_def by auto


lemma transform_production_when_CNF':
  assumes \<open>CNF_rule (A,r)\<close>
  shows \<open>\<exists>B C a.    
 (A,r) = (A, [Nt B, Nt C]) \<and> transform_production (A,r) = (A, [ Tm (Op, (A, [Nt B, Nt C]), One), Nt B, Tm (Cl, ((A, [Nt B, Nt C]), One)), Tm (Op, (A, [Nt B, Nt C]), Two), Nt C, Tm (Cl, (A, [Nt B, Nt C]), Two)  ])  
\<or>
 (A,r) = (A, [Tm a])       \<and> transform_production (A,r) =   (A, [ Tm (Op, (A, [Tm a]),One),       Tm (Cl, (A, [Tm a]), One), Tm (Op, (A, [Tm a]), Two),       Tm (Cl, (A, [Tm a]), Two)  ])  
\<close>
  using transform_production_when_CNF fst_transform_production using assms by blast



lemma transform_production_induct_cnf:
  assumes \<open>CNF_rule p\<close>
    and \<open>\<And>A B C. Q (transform_production (A, [Nt B, Nt C])) (A, [Nt B, Nt C])\<close>
    and \<open>\<And>A a. Q (transform_production (A, [Tm a])) (A, [Tm a])\<close>
  shows \<open>Q (transform_production p) p\<close>
  using assms CNF_rule_def by metis






















































































section\<open>Definition of the regular Language\<close>
text\<open>Defines a Predicate on neighbouring string elements - Is true iff after a Cl,p,1 there always immediately follows a Op,p,2. That also means, Cl,p,1 can't be the end of the string\<close>
fun P1' :: \<open>(bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> (bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> bool\<close> where
  \<open>P1' ((Cl, (p, One))) ((Op, (p', Two)))  = (p = p')\<close> | 
  \<open>P1' ((Cl, (p, One))) y  = False\<close> | 
  \<open>P1' x y = True\<close>

text\<open>Version of P1 for symbols, i.e. strings that may still contain Nt's\<close>
fun P1'_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> bool\<close> where
  \<open>P1'_sym (Tm (Cl, (p, One))) (Tm (Op, (p', Two)))  = (p = p')\<close> | 
  \<open>P1'_sym (Tm (Cl, (p, One))) y  = False\<close> | 
  \<open>P1'_sym x y = True\<close>

lemma P1'D[dest]:
  assumes \<open>P1' (Cl, (p, One)) r\<close>
  shows \<open>r = (Op, (p, Two))\<close> 
  using assms apply(induction \<open>(Cl, (p, One))\<close> \<open>r\<close> rule: P1'.induct) by auto

lemma P1'_symD[dest]:
  assumes \<open>P1'_sym (Tm (Cl, (p, One))) r\<close>
  shows \<open>r = Tm (Op, (p, Two))\<close> 
  using assms apply(induction \<open>(Tm (Cl, (p, One)))::('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close> \<open>r\<close> rule: P1'_sym.induct) by auto

lemmas P1'E = P1'D[elim_format]
lemmas P1'_symE = P1'_symD[elim_format]


text\<open>Asserts that P1' holds for every pair in xs, and that xs doesnt end in (Cl, p, 1)\<close>
fun P1 where
  \<open>P1 xs = ((successively P1' xs) \<and> (if xs \<noteq> [] then (\<nexists>p. last xs = (Cl, (p, One))) else True))\<close>

text\<open>Asserts that P1' holds for every pair in xs, and that xs doesnt end in Tm (Cl, p, 1)\<close>
fun P1_sym where
  \<open>P1_sym xs = ((successively P1'_sym xs) \<and> (if xs \<noteq> [] then (\<nexists>p. last xs = Tm (Cl, (p, One))) else True))\<close>


lemma P1_sym_imp_P1_for_tm[intro, dest]: \<open>P1_sym (map Tm x) \<Longrightarrow> P1 x\<close>
  apply(induction x rule: induct_list012) defer defer apply simp apply(case_tac \<open>(Tm x, Tm y)\<close> rule: P1'_sym.cases) by auto

lemma P1I[intro]: 
  assumes \<open>successively P1' xs\<close>
    and \<open>\<nexists>p. last xs = (Cl, (p, One))\<close>
  shows \<open>P1 xs\<close>
proof(cases xs)
  case Nil
  then show ?thesis using assms by force
next
  case (Cons a list)
  then show ?thesis using assms by (auto split: version.splits sym.splits bracket.splits)
qed

lemma P1_symI[intro]: 
  assumes \<open>successively P1'_sym xs\<close>
    and \<open>\<nexists>p. last xs = Tm (Cl, (p, One))\<close>
  shows \<open>P1_sym xs\<close> apply(cases xs rule: rev_cases) defer apply(case_tac y) using assms by auto


lemma P1D[dest]: \<open>P1 xs \<Longrightarrow> successively P1' xs\<close> by simp

lemma P1_symD[dest]: \<open>P1_sym xs \<Longrightarrow> successively P1'_sym xs\<close> by simp

lemma P1D_not_empty[dest]:
  assumes \<open>xs \<noteq> []\<close>
    and \<open>P1 xs\<close>
  shows \<open>last xs \<noteq> (Cl, p, One)\<close>
proof-
  obtain x xs' where x_eq: \<open>xs = x# xs'\<close> using assms using List.list.exhaust_sel by blast
  with assms have \<open>successively P1' xs\<close> \<open>\<nexists>p. last xs = (Cl, (p, One))\<close> using P1.simps apply blast using P1.simps by (metis assms(1,2))
  then show ?thesis by blast
qed

lemma P1_symD_not_empty'[dest]:
  assumes \<open>xs \<noteq> []\<close>
    and \<open>P1_sym xs\<close>
  shows \<open>last xs \<noteq> Tm (Cl, p, One)\<close>
proof-
  obtain x xs' where x_eq: \<open>xs = x# xs'\<close> using assms using List.list.exhaust_sel by blast
  with assms have \<open>successively P1'_sym xs\<close> \<open>\<nexists>p. last xs = Tm (Cl, (p, One))\<close> using P1_sym.simps apply blast using P1.simps x_eq by (metis assms(1,2) chomsky_schuetzenberger.P1_sym.elims(2))
  then show ?thesis by blast
qed

lemma P1_symD_not_empty[dest]:
  assumes \<open>xs \<noteq> []\<close>
    and \<open>P1_sym xs\<close>
  shows \<open>\<nexists>p. last xs = Tm (Cl, p, One)\<close> using P1_symD_not_empty'[OF assms] by simp


lemmas P1E = P1D[elim_format]
lemmas P1E_not_empty = P1D_not_empty[elim_format]

lemmas P1_symE = P1_symD[elim_format]
lemmas P1_symE_not_empty = P1_symD_not_empty[elim_format]



text\<open>After any (Cl,pi,2) there never comes an (Op,...)\<close>
fun P2 :: \<open>(bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> (bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> bool\<close> where
  \<open>P2 (Cl, (p, Two)) (Op, (p', v))  = False\<close> | 
  \<open>P2 (Cl, (p, Two)) y  = True\<close> | 
  \<open>P2 x y = True\<close>


fun P2_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> bool\<close> where
  \<open>P2_sym (Tm (Cl, (p, Two))) (Tm (Op, (p', v)))  = False\<close> | 
  \<open>P2_sym (Tm (Cl, (p, Two))) y  = True\<close> | 
  \<open>P2_sym x y = True\<close>

lemma P2D[dest]:
  assumes \<open>P2 (Cl, (p, Two)) r\<close>
  shows \<open>r \<noteq> (Op, g)\<close> 
  using assms apply(induction \<open>(Cl, (p, Two))\<close> \<open>r\<close> rule: P2.induct) by auto

lemma P2_symD[dest]:
  assumes \<open>P2_sym (Tm (Cl, (p, Two))) r\<close>
  shows \<open>r \<noteq> Tm (Op, g)\<close> 
  using assms apply(induction \<open>Tm (Cl, (p, Two)):: ('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close> \<open>r\<close> rule: P2_sym.induct) by auto

lemmas P2E = P2D[elim_format]
lemmas P2_symE = P2_symD[elim_format]


lemma P2_sym_imp_P2_for_tm[intro, dest]: \<open>successively P2_sym (map Tm x) \<Longrightarrow> successively P2 x\<close>
  apply(induction x rule: induct_list012) apply simp apply simp apply(case_tac \<open>(Tm x, Tm y)\<close> rule: P2_sym.cases) by auto




text\<open>After each (Op,A\<rightarrow>BC,1), always comes a (Op,(B, _),1),  And after each (Op,A\<rightarrow>BC,2), always comes a (Op,(C, _),1)\<close>
fun P3 :: \<open>(bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> (bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> bool\<close> where
  \<open>P3 (Op, ((A, [Nt B, Nt C]), One)) (p, ((X,y), t)) = (p = Op \<and> t = One \<and> X = B)\<close> |
  \<open>P3 (Op, ((A, [Nt B, Nt C]), Two)) (p, ((X,y), t)) = (p = Op \<and> t = One \<and> X = C)\<close> |
  \<open>P3 x y = True\<close>


text\<open>After each (Op,A\<rightarrow>BC,1), always comes a (Op,(B, _),1) or a Nt B,  And after each (Op,A\<rightarrow>BC,2), always comes a (Op,(C, _),1) or a Nt C\<close>
fun P3_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> bool\<close> where
  \<open>P3_sym (Tm (Op, ((A, [Nt B, Nt C]), One))) (Tm (p, ((X,y), t))) = (p = Op \<and> t = One \<and> X = B)\<close> | \<comment> \<open>Not obvious: the case (Tm (Op, ((A, [Nt B, Nt C]), One))) Nt X is set to True with the catch all\<close>
  \<open>P3_sym (Tm (Op, ((A, [Nt B, Nt C]), One))) (Nt X) = (X = B)\<close> | 

\<open>P3_sym (Tm (Op, ((A, [Nt B, Nt C]), Two))) (Tm (p, ((X,y), t))) = (p = Op \<and> t = One \<and> X = C)\<close> | 
\<open>P3_sym (Tm (Op, ((A, [Nt B, Nt C]), Two))) (Nt X) = (X = C)\<close> | 
\<open>P3_sym x y = True\<close>

lemma P3D1[dest]:
  fixes r::\<open>(bracket \<times> ('n,'t) prod \<times> version)\<close>
  assumes \<open>P3 (Op, ((A, [Nt B, Nt C]), One)) r\<close>
  shows \<open>\<exists>l. r = (Op, (B, l), One)\<close>
  using assms apply(induction \<open>(Op, ((A, [Nt B, Nt C]), One)):: bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version\<close> \<open>r:: bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version\<close> rule: P3.induct) by auto 

lemma P3D2[dest]:
  fixes r::\<open>(bracket \<times> ('n,'t) prod \<times> version)\<close>
  assumes \<open>P3 (Op, ((A, [Nt B, Nt C]), Two)) r\<close>
  shows \<open>\<exists>l. r = (Op, (C, l), One)\<close>
  using assms apply(induction \<open>(Op, ((A, [Nt B, Nt C]), One)):: bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version\<close> \<open>r:: bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version\<close> rule: P3.induct) by auto 


lemma P3_symD1[dest]:
  fixes r::\<open>('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym\<close>
  assumes \<open>P3_sym (Tm (Op, ((A, [Nt B, Nt C]), One))) r\<close>
  shows \<open>(\<exists>l. r = Tm (Op, (B, l), One)) \<or> (r = Nt B)\<close>
  using assms apply(induction \<open>Tm (Op, ((A, [Nt B, Nt C]), One)):: ('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym\<close> \<open>r:: ('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym\<close> rule: P3_sym.induct) by auto 

lemma P3_symD2[dest]:
  fixes r::\<open>('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym\<close>
  assumes \<open>P3_sym (Tm (Op, ((A, [Nt B, Nt C]), Two))) r\<close>
  shows \<open>(\<exists>l. r = Tm (Op, (C, l), One)) \<or> (r = Nt C)\<close>
  using assms apply(induction \<open>Tm (Op, ((A, [Nt B, Nt C]), Two)):: ('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym\<close> \<open>r:: ('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) sym\<close> rule: P3_sym.induct) by auto


lemmas P3E1 = P3D1[elim_format]
lemmas P3E2 = P3D2[elim_format]
lemmas P3_symE1 = P3_symD1[elim_format]
lemmas P3_symE2 = P3_symD2[elim_format]

lemma P3_sym_imp_P3_for_tm[intro, dest]: \<open>successively P3_sym (map Tm x) \<Longrightarrow> successively P3 x\<close>
  apply(induction x rule: induct_list012) apply simp apply simp apply(case_tac \<open>(Tm x, Tm y)\<close> rule: P3_sym.cases) by auto




text\<open>after each (Op,A\<rightarrow>a,1) comes a (Cl,A\<rightarrow>a,1) and after each (Op,A\<rightarrow>a,2) comes a (Cl,A\<rightarrow>a,2)\<close>
fun P4 :: \<open>(bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> (bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> bool\<close> where
  \<open>P4 (Op, ((A, [Tm a]), s)) (p, ((X, y), t)) = (p = Cl \<and> X = A \<and> y = [Tm a] \<and> s = t)\<close> |
  \<open>P4 x y = True\<close>

text\<open>after each (Op,A\<rightarrow>a,1) comes a (Cl,A\<rightarrow>a,1) and after each (Op,A\<rightarrow>a,2) comes a (Cl,A\<rightarrow>a,2)\<close>
fun P4_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> bool\<close> where
  \<open>P4_sym (Tm (Op, ((A, [Tm a]), s))) (Tm (p, ((X, y), t))) = (p = Cl \<and> X = A \<and> y = [Tm a] \<and> s = t)\<close> | 
  \<open>P4_sym (Tm (Op, ((A, [Tm a]), s))) (Nt X) = False\<close> | 
  \<open>P4_sym x y = True\<close>


lemma P4D[dest]:
  fixes r::\<open>(bracket \<times> ('n,'t) prod \<times> version)\<close>
  assumes \<open>P4 (Op, ((A, [Tm a]), v)) r\<close>
  shows \<open>r = (Cl, (A, [Tm a]), v)\<close> 
  using assms apply(induction \<open>(Op, ((A, [Tm a]), v))::(bracket \<times> ('n,'t) prod \<times> version)\<close> \<open>r::(bracket \<times> ('n,'t) prod \<times> version)\<close> rule: P4.induct) by auto

lemma P4_symD[dest]:
  fixes r::\<open>('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close>
  assumes \<open>P4_sym (Tm (Op, ((A, [Tm a]), v))) r\<close>
  shows \<open>r = Tm (Cl, (A, [Tm a]), v)\<close> 
  using assms apply(induction \<open>Tm (Op, ((A, [Tm a]), v)):: ('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close> \<open>r::('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close> rule: P4_sym.induct) by auto

lemmas P4E = P4D[elim_format]
lemmas P4_symE = P4_symD[elim_format]


lemma P4_sym_imp_P4_for_tm[intro, dest]: \<open>successively P4_sym (map Tm x) \<Longrightarrow> successively P4 x\<close>
  apply(induction x rule: induct_list012) apply simp apply simp apply(case_tac \<open>(Tm x, Tm y)\<close> rule: P4_sym.cases) by auto


text\<open>there exists some y, such that x begins with (Op,(A,y),1)\<close>
fun P5 :: \<open>'n \<Rightarrow> (bracket \<times> ('n,'t) prod \<times> version) list \<Rightarrow> bool\<close> where
  \<open>P5 A [] = False\<close> | 
  \<open>P5 A ((Op, (X,y), One) # xs) = (X = A)\<close> | 
  \<open>P5 A (x # xs) = False\<close>

text\<open>there exists some y, such that x begins with (Op,(A,y),1) or it begins with Nt A\<close>
fun P5_sym :: \<open>'n \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) syms \<Rightarrow> bool\<close> where
  \<open>P5_sym A [] = False\<close> | 
  \<open>P5_sym A (Tm (Op, (X,y), One) # xs) = (X = A)\<close> | 
  \<open>P5_sym A ((Nt X) # xs) = (X = A)\<close> | 
  \<open>P5_sym A (x # xs) = False\<close>

lemma P5D[dest]: 
  assumes \<open>P5 A x\<close>
  shows \<open>\<exists>y. (hd x = (Op, (A,y), One))\<close>
  using assms apply(induction A x rule: P5.induct) by auto

lemma P5_symD[dest]: 
  assumes \<open>P5_sym A x\<close>
  shows \<open>(\<exists>y. hd x = Tm (Op, (A,y), One)) \<or> (hd x = Nt A)\<close>
  using assms apply(induction A x rule: P5_sym.induct) by auto

lemmas P5E = P5D[elim_format]
lemmas P5_symE = P5_symD[elim_format]

lemma P5_sym_imp_P5_for_tm[intro, dest]: \<open>P5_sym A (map Tm x) \<Longrightarrow> P5 A x\<close>
  apply(induction x) by auto




text\<open>Before a Nt Y there always comes a Tm (Op, A\<rightarrow>YC, 1) or a Tm (Op, A\<rightarrow>BY, 2)\<close>
fun P7_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> bool\<close> where
  \<open>P7_sym (Tm (b,(A, [Nt B, Nt C]), v )) (Nt Y) = (b = Op \<and> ((Y = B \<and> v = One) \<or> (Y=C \<and> v = Two)) )\<close> | 
  \<open>P7_sym x (Nt Y) = False\<close> | 
  \<open>P7_sym x y = True\<close>


lemma P7_symD[dest]: 
  fixes x:: \<open>('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close>
  assumes \<open>P7_sym x (Nt Y)\<close>
  shows \<open>(\<exists>A C. x = Tm (Op, (A,[Nt Y, Nt C]), One)) \<or> (\<exists>A B. x = Tm (Op, (A,[Nt B, Nt Y]), Two))\<close>
  using assms apply(induction x \<open>Nt Y::('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close> rule: P7_sym.induct) by auto

lemmas P7_symE = P7_symD[elim_format]

text\<open>After a Nt Y there always comes a (Cl, A\<rightarrow>YC, 1) or a (Cl, A\<rightarrow>BY, 2)\<close>
fun P8_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> bool\<close> where
  \<open>P8_sym (Nt Y) (Tm (b,(A, [Nt B, Nt C]), v ))  = (b = Cl \<and> ( (Y = B \<and> v = One) \<or> (Y=C \<and> v = Two)) )\<close> | 
  \<open>P8_sym (Nt Y) x = False\<close> | 
  \<open>P8_sym x y = True\<close>

lemma P8_symD[dest]: 
  fixes x:: \<open>('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close>
  assumes \<open>P8_sym (Nt Y) x\<close>
  shows \<open>(\<exists>A C. x = Tm (Cl, (A,[Nt Y, Nt C]), One)) \<or> (\<exists>A B. x = Tm (Cl, (A,[Nt B, Nt Y]), Two))\<close>
  using assms apply(induction \<open>Nt Y::('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close> x rule: P8_sym.induct) by auto

lemmas P8_symE = P8_symD[elim_format]

text\<open>This is the regular language, where one takes the Start symbol as a parameter, and then has the searched for \<open>R := R\<^sub>A\<close>\<close>
definition Re :: \<open>'n \<Rightarrow> (bracket \<times> (('n, 't) prod) \<times> version) list set\<close> where
  \<open>Re A = {x. (P1 x) \<and> (successively P2 x) \<and> (successively P3 x) \<and> (successively P4 x) \<and> (P5 A x)}\<close>

lemma ReI[intro]:
  assumes \<open>(P1 x)\<close> and \<open>(successively P2 x)\<close> and \<open>(successively P3 x)\<close> and \<open>(successively P4 x)\<close> and \<open>(P5 A x)\<close>
  shows \<open>x \<in> Re A\<close>
  using assms unfolding Re_def by blast

lemma ReD[dest]:
  assumes \<open>x \<in> Re A\<close>
  shows \<open>(P1 x)\<close> and \<open>(successively P2 x)\<close> and \<open>(successively P3 x)\<close> and \<open>(successively P4 x)\<close> and \<open>(P5 A x)\<close>
  using assms unfolding Re_def by blast+

lemmas ReE = ReD[elim_format]

text\<open>Version of Re for symbols, i.e. strings that may still contain Nt's. 
It has 2 more Properties P6 and P7 that vanish for pure terminal strings\<close>
definition Re_sym :: \<open>'n \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) syms set\<close> where
  \<open>Re_sym A = {x. (P1_sym x) \<and> (successively P2_sym x) \<and> (successively P3_sym x) \<and> (successively P4_sym x) \<and> (P5_sym A x) \<and> (successively P7_sym x) \<and> (successively P8_sym x)}\<close>

lemma Re_symI[intro]:
  assumes \<open>P1_sym x\<close> and \<open>successively P2_sym x\<close> and \<open>successively P3_sym x\<close> and \<open>successively P4_sym x\<close> and \<open>P5_sym A x\<close> and \<open>(successively P7_sym x)\<close> and \<open>(successively P8_sym x)\<close>
  shows \<open>x \<in> Re_sym A\<close>
  using assms unfolding Re_sym_def by blast

lemma Re_symD[dest]:
  assumes \<open>x \<in> Re_sym A\<close>
  shows \<open>P1_sym x\<close> and \<open>successively P2_sym x\<close> and \<open>successively P3_sym x\<close> and \<open>successively P4_sym x\<close> and \<open>P5_sym A x\<close> and \<open>(successively P7_sym x)\<close> and \<open>(successively P8_sym x)\<close>
  using assms unfolding Re_sym_def by blast+

lemmas Re_symE = Re_symD[elim_format]


lemma Re_sym_imp_Re_for_tm[intro, dest]: \<open>(map Tm x) \<in> Re_sym A \<Longrightarrow> x \<in> Re A\<close> apply(rule ReI) by auto


text\<open>Definition of monoid-homomorphism where multiplication is that of words.\<close>
definition hom :: \<open>('c list \<Rightarrow> 'd list) \<Rightarrow> bool\<close> where
  \<open>hom h = (\<forall>a b. h (a@b) = (h a) @ h (b))\<close>


text\<open>helper function for the definition of \<open>h\<close>\<close>
fun the_hom_helper :: \<open>(bracket \<times> (('a, 'b) prod) \<times> version) \<Rightarrow> 'b list\<close> where
  \<open>the_hom_helper (Op, ((A, [Tm a]), One)) = [a]\<close> | 
  \<open>the_hom_helper _ = []\<close> 



text\<open>helper function for the definition of the extended \<open>h_ext\<close>\<close>
fun the_hom_ext_helper :: \<open>('a, bracket \<times> ('a,'b) prod \<times> version) sym \<Rightarrow> ('a,'b) sym list\<close> where
  \<open>the_hom_ext_helper (Tm (Op, ((A, [Tm a]), One))) = [Tm a]\<close> | 
  \<open>the_hom_ext_helper (Nt A) = [Nt A]\<close> | 
  \<open>the_hom_ext_helper _ = []\<close>



text\<open>The needed homomorphism in the proof\<close>
fun the_hom :: \<open>(bracket \<times> ('a,'b) prod \<times> version) list \<Rightarrow> 'b list \<close> where
  \<open>the_hom l = concat (map the_hom_helper l)\<close>


text\<open>The needed homomorphism in the proof, but extended on Variables\<close>
fun the_hom_ext :: \<open>('a, bracket \<times> ('a,'b) prod \<times> version ) syms \<Rightarrow> ('a,'b) syms\<close> where
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











lemma transform_production_one_step:
  assumes \<open>CNF_rule (S,w)\<close>
    and \<open>(S,w) \<in> P\<close>
  shows \<open>(transform_production ` P) \<turnstile> [Nt S] \<Rightarrow> snd (transform_production (S,w))\<close>
proof-
  obtain w' where \<open>transform_production (S,w) = (S, w')\<close> by (metis fst_eqD fst_transform_production surj_pair)
  then have \<open>(S, w') \<in> transform_production ` P\<close> using assms(2) by force
  then show ?thesis by (simp add: \<open>transform_production (S, w) = (S, w')\<close> derive_singleton)
qed


lemma [iff]: \<open>bal_tm ([ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ])\<close> using stk_bal_tm_iff_bal_tm by fastforce

lemma [iff]: \<open>bal_tm ([ Tm (Op, (p,One)),       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ])\<close> using stk_bal_tm_iff_bal_tm by fastforce

lemma \<open>rhs_in_if [Nt A] \<Gamma>\<close> by auto

lemma prod1_rhs_in_if [intro, simp]: \<open>p \<in> P \<Longrightarrow> rhs_in_if [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ] (P \<times> {One, Two}) \<close> by auto

lemma prod2_rhs_in_if [intro, simp]: \<open>p \<in> P \<Longrightarrow> rhs_in_if [ Tm (Op, (p,One)),       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ] (P \<times> {One, Two})\<close> by auto

lemma prod_bal_tm[intro!]:
  assumes \<open>p \<in> P\<close>
    and \<open>CNF_rule p\<close>
  shows \<open>bal_tm (snd (transform_production p)) \<and> rhs_in_if (snd (transform_production p)) (P \<times> {One, Two})\<close> 
proof-
  have \<open>(\<exists>A B C. transform_production p = (A, [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ]) ) \<or> (\<exists>A. transform_production p = (A, [ Tm (Op, (p,One)),       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ]))\<close> ( is \<open>?A1 \<or> ?A2\<close>) using transform_production_CNF[OF assms(2)] by blast

  then show ?thesis
  proof
    assume A1: ?A1
    then obtain A B C where \<open>transform_production p = (A, [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ])\<close> by blast
    moreover have \<open>rhs_in_if (snd (transform_production p)) (P \<times> {One, Two})\<close> using prod1_rhs_in_if[of p P] by (simp add: assms(1) calculation)
    ultimately show ?thesis by auto
  next
    assume A2: ?A2
    then obtain A where \<open>transform_production p = (A, [ Tm (Op, (p,One)),       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ])\<close> by blast
    moreover have \<open>rhs_in_if (snd (transform_production p)) (P \<times> {One, Two})\<close> using prod1_rhs_in_if[of p P] by (simp add: assms(1) calculation)
    ultimately show ?thesis by auto
  qed
qed



lemma P'_bal:
  assumes \<open>(image transform_production P) \<turnstile> [Nt A] \<Rightarrow>* x\<close>
    and \<open>\<forall>p \<in> P. CNF_rule p\<close>
  shows \<open>bal_tm x \<and> rhs_in_if x (P \<times> {One, Two})\<close>
  using assms proof(induction rule: derives_induct)
  case base
  then show ?case by auto
next
  case (step u A v w)
  have \<open>bal_tm (u @ [Nt A] @ v)\<close> and \<open>rhs_in_if (u @ [Nt A] @ v) (P \<times> {One, Two})\<close> using local.step.IH local.step.prems by auto
  have \<open>bal_tm w\<close> by (metis imageE local.step.hyps(2) local.step.prems prod_bal_tm snd_conv)
  then have \<open>bal_tm (u @ w @ v)\<close> using \<open>bal_tm (u @ [Nt A] @ v)\<close> by blast

  obtain w' where \<open>(A, w) = transform_production (A, w')\<close> by (metis (no_types, opaque_lifting) Product_Type.prod.collapse fst_transform_production imageE local.step.hyps(2))
  then have \<open>rhs_in_if w (P \<times> {One, Two})\<close> using prod_bal_tm[of \<open>(A, w')\<close> P] by (smt (verit, best) image_iff local.step.hyps(2) local.step.prems prod_bal_tm snd_conv)
  then have \<open>rhs_in_if (u @ w @ v) (P \<times> {One, Two})\<close> using \<open>rhs_in_if (u @ [Nt A] @ v) (P \<times> {One, Two})\<close> by (metis rhs_in_if_append rhs_in_if_del_left rhs_in_if_del_right)

  then show ?case using \<open>bal_tm (u @ w @ v)\<close> by blast
qed





lemma dyck_languageI_tm[intro]: \<open>bal_tm (map Tm xs') \<Longrightarrow> rhs_in_if (map Tm xs') \<Gamma> \<Longrightarrow> xs' \<in> dyck_language \<Gamma>\<close>
proof-
  assume bal: \<open>bal_tm (map Tm xs')\<close> and rhs: \<open>rhs_in_if (map Tm xs') \<Gamma>\<close>
  then have \<open>bal xs'\<close> using bal_tm_imp_bal_for_tms by blast
  moreover have \<open>\<And>br r. (br, r) \<in> set xs' \<Longrightarrow> r \<in> \<Gamma>\<close> using rhs sym.exhaust by (metis (no_types, lifting) List.list.simps(15,9) insert_iff map_append rhs_in_ifD rhs_in_if_del_left split_list_last)
  ultimately show ?thesis using dyck_languageI[of xs' \<Gamma>] by blast
qed




lemma P'_imp_Re:
  assumes \<open>(image transform_production P) \<turnstile> [Nt S] \<Rightarrow>* x\<close>
    and \<open>\<forall>p \<in> P. CNF_rule p\<close>
  shows \<open>x \<in> Re_sym S\<close>
  using assms proof(induction rule: derives_induct)
  case base
  show ?case apply(rule Re_symI) by simp+
next
  case (step u A v w)
  have uAv: \<open>u @ [Nt A] @ v \<in> Re_sym S\<close> using step by blast

  have \<open>(A, w) \<in> transform_production ` P\<close> using step by blast
  then obtain w' where w'_def: \<open>transform_production (A, w') = (A, w)\<close> and \<open>(A,w') \<in> P\<close> by (metis (no_types, opaque_lifting) Product_Type.old.prod.exhaust fst_conv fst_transform_production imageE)
  then have Aw'_cnf: \<open>CNF_rule (A,w')\<close> using step by blast
  then obtain B C a where \<open>((A, w) = (A, [Tm [\<^bsub>(A, w')\<^esub>\<^sup>1 , Nt B, Tm ]\<^bsub>(A, w')\<^esub>\<^sup>1, Tm [\<^bsub>(A, w')\<^esub>\<^sup>2, Nt C, Tm ]\<^bsub>(A, w')\<^esub>\<^sup>2]) \<and> w' = [Nt B, Nt C]) \<or> ((A, w) = (A, [Tm [\<^bsub>(A, w')\<^esub>\<^sup>1 , Tm ]\<^bsub>(A, w')\<^esub>\<^sup>1, Tm [\<^bsub>(A, w')\<^esub>\<^sup>2, Tm ]\<^bsub>(A, w')\<^esub>\<^sup>2]) \<and> w' = [Tm a])\<close> using transform_production_CNF[of \<open>(A,w')\<close>] w'_def by (metis snd_conv)   

  then have w_eq: \<open>w = [Tm [\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>1 , Nt B, Tm ]\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>1, Tm [\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>2, Nt C, Tm ]\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>2]   \<or>    w = [Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>1 , Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>1, Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>2, Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>2]\<close> (is \<open>w = ?w1 \<or> w = ?w2\<close>) by fastforce
  then have w_resym: \<open>w \<in> Re_sym A\<close> unfolding w_eq by auto

  have P5_uAv: \<open>P5_sym S (u @ [Nt A] @ v)\<close> using Re_symD[OF uAv] by blast
  have P1_uAv: \<open>P1_sym (u @ [Nt A] @ v)\<close> using Re_symD[OF uAv] by blast

  have left: \<open>successively P1'_sym (u@w) \<and> successively P2_sym (u@w) \<and> successively P3_sym (u@w) \<and> successively P4_sym (u@w) \<and> successively P7_sym (u@w) \<and> successively P8_sym (u@w)\<close>
  proof(cases u rule: rev_cases)
    case Nil
    show ?thesis apply(rule disjE[OF w_eq]) unfolding Nil by auto
  next
    case (snoc ys y)

    then have \<open>successively P7_sym (ys @ [y] @ [Nt A] @ v)\<close> using Re_symD[OF uAv] snoc by auto
    then have \<open>P7_sym y (Nt A)\<close> by (simp add: successively_append_iff)

    then obtain R X Y v' where y_eq: \<open>y = (Tm (Op,(R, [Nt X, Nt Y]), v' ))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> by blast
    then have \<open>P3_sym y (hd w)\<close> using w_eq apply(cases \<open>w = ?w1\<close>) apply(cases v') apply force apply force by (smt (verit, best) List.list.sel(1) chomsky_schuetzenberger.P3_sym.simps(1,3) chomsky_schuetzenberger.version.exhaust) 

    hence \<open>P1'_sym (last (ys@[y])) (hd w) \<and> P2_sym (last (ys@[y])) (hd w) \<and> P3_sym (last (ys@[y])) (hd w) \<and> P4_sym (last (ys@[y])) (hd w) \<and> P7_sym (last (ys@[y])) (hd w) \<and> P8_sym (last (ys@[y])) (hd w)\<close> unfolding y_eq using w_eq apply(cases \<open>w = ?w1\<close>) apply force by simp
    with Re_symD[OF uAv] moreover have   \<open>successively P1'_sym (ys @ [y]) \<and> successively P2_sym (ys @ [y]) \<and> successively P3_sym (ys @ [y]) \<and> successively P4_sym (ys @ [y]) \<and> successively P7_sym (ys @ [y]) \<and> successively P8_sym (ys @ [y])\<close> unfolding snoc using successively_append_iff by blast
    ultimately show \<open>successively P1'_sym (u@w) \<and>successively P2_sym (u@w) \<and> successively P3_sym (u@w) \<and> successively P4_sym (u@w) \<and> successively P7_sym (u@w) \<and> successively P8_sym (u@w)\<close> unfolding snoc using Re_symD[OF w_resym] using successively_append_iff by blast
  qed


  have right: \<open>successively P1'_sym (w@v) \<and> successively P2_sym (w@v) \<and> successively P3_sym (w@v) \<and> successively P4_sym (w@v) \<and> successively P7_sym (w@v) \<and> successively P8_sym (w@v)\<close>
  proof(cases v)
    case Nil
    show ?thesis apply(rule disjE[OF w_eq]) unfolding Nil by auto
  next
    case (Cons y ys)
    then have \<open>successively P8_sym ([Nt A] @ y # ys)\<close> using Re_symD[OF uAv] Cons using successively_append_iff by blast
    then have \<open>P8_sym (Nt A) y\<close> by fastforce
    then obtain R X Y v' where y_eq: \<open>y = (Tm (Cl,(R, [Nt X, Nt Y]), v' ))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> by blast
    have \<open>P1'_sym (last w) (hd (y#ys)) \<and> P2_sym (last w) (hd (y#ys)) \<and> P3_sym (last w) (hd (y#ys)) \<and> P4_sym (last w) (hd (y#ys)) \<and> P7_sym (last w) (hd (y#ys)) \<and> P8_sym (last w) (hd (y#ys))\<close> unfolding y_eq using w_eq apply(cases \<open>w = ?w1\<close>) apply force by simp
    with Re_symD[OF uAv] moreover have \<open>successively P1'_sym (y # ys) \<and> successively P2_sym (y # ys) \<and> successively P3_sym (y # ys) \<and> successively P4_sym (y # ys) \<and> successively P7_sym (y # ys) \<and> successively P8_sym (y # ys)\<close> unfolding Cons by (metis P1_symD successively_append_iff)
    ultimately show \<open>successively P1'_sym (w@v) \<and> successively P2_sym (w@v) \<and> successively P3_sym (w@v) \<and> successively P4_sym (w@v) \<and> successively P7_sym (w@v) \<and> successively P8_sym (w@v)\<close> unfolding Cons using Re_symD[OF w_resym] using successively_append_iff by blast
  qed

  from left right have P1_uwv: \<open>successively P1'_sym (u@w@v)\<close> using w_eq by (metis (no_types, lifting) List.list.discI hd_append2 successively_append_iff)
  from left right have ch: \<open>successively P2_sym (u@w@v) \<and> successively P3_sym (u@w@v) \<and> successively P4_sym (u@w@v) \<and> successively P7_sym (u@w@v) \<and> successively P8_sym (u@w@v)\<close> using w_eq by (metis (no_types, lifting) List.list.discI hd_append2 successively_append_iff)

  moreover have \<open>P5_sym S (u@w@v)\<close> apply(rule disjE[OF w_eq]; cases u) 
    using P5_uAv apply force
    using P5_uAv apply (metis List.list.sel(1) P5_symD append_Cons chomsky_schuetzenberger.P5_sym.simps(2,3))
    using P5_uAv apply force 
    using P5_uAv by (metis List.list.sel(1) P5_symD append_Cons chomsky_schuetzenberger.P5_sym.simps(2,3))

  moreover have \<open>P1_sym (u@w@v)\<close> 
  proof(cases v rule: rev_cases)
    case Nil
    have \<open>\<nexists>p. last (u@w@v) = Tm (Cl,(p, One))\<close> unfolding Nil apply(rule disjE[OF w_eq]) by auto
    with P1_uwv show \<open>P1_sym (u @ w @ v)\<close> by blast
  next
    case (snoc vs v')
    then have \<open>\<nexists>p. last v = Tm (Cl,(p, One))\<close> using P1_symD_not_empty[OF _ P1_uAv] by (metis Nil_is_append_conv last_appendR not_Cons_self2)
    then have \<open>\<nexists>p. last (u@w@v) = Tm (Cl,(p, One))\<close> by (simp add: snoc)
    with P1_uwv show \<open>P1_sym (u @ w @ v)\<close> by blast
  qed

  ultimately show \<open>(u@w@v) \<in> Re_sym S\<close> by blast 
qed 



lemma P'_imp_last_not_Cl_1:
  assumes \<open>(image transform_production P) \<turnstile> [Nt A] \<Rightarrow>* x\<close>
    and \<open>\<forall>p \<in> P. CNF_rule p\<close>
  shows \<open>last x \<noteq> Tm (Cl,p,One)\<close>
  using assms proof(induction rule: derives_induct)
  case base
  then show ?case by simp
next
  case (step u A v w)
  then show ?case
  proof(cases v)
    case Nil
    have \<open>(A, w) \<in> transform_production ` P\<close> using step by blast
    then obtain w' where w'_def: \<open>transform_production (A, w') = (A, w)\<close> and \<open>(A,w') \<in> P\<close> by (metis (no_types, opaque_lifting) Product_Type.old.prod.exhaust fst_conv fst_transform_production imageE)

    then have Aw'_cnf: \<open>CNF_rule (A,w')\<close> using step by blast
    then obtain B C a where \<open>((A, w) = (A, [Tm [\<^bsub>(A, w')\<^esub>\<^sup>1 , Nt B, Tm ]\<^bsub>(A, w')\<^esub>\<^sup>1, Tm [\<^bsub>(A, w')\<^esub>\<^sup>2, Nt C, Tm ]\<^bsub>(A, w')\<^esub>\<^sup>2]) \<and> w' = [Nt B, Nt C]) \<or> ((A, w) = (A, [Tm [\<^bsub>(A, w')\<^esub>\<^sup>1 , Tm ]\<^bsub>(A, w')\<^esub>\<^sup>1, Tm [\<^bsub>(A, w')\<^esub>\<^sup>2, Tm ]\<^bsub>(A, w')\<^esub>\<^sup>2]) \<and> w' = [Tm a])\<close> using transform_production_CNF[of \<open>(A,w')\<close>] w'_def by (metis snd_conv)   

    then have w_eq: \<open>w = [Tm [\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>1 , Nt B, Tm ]\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>1, Tm [\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>2, Nt C, Tm ]\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>2]   \<or>    w = [Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>1 , Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>1, Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>2, Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>2]\<close> (is \<open>w = ?w1 \<or> w = ?w2\<close>) by fastforce
    then show ?thesis using step using Nil by fastforce
  next
    case (Cons a list)
    then show ?thesis using step by simp
  qed
qed




lemma Re_imp_P':
  assumes \<open>x \<in> (Re A \<inter> (dyck_language (P \<times> {One, Two})))\<close>
    and \<open>\<forall>p \<in> P. CNF_rule p\<close>
  shows \<open>(image transform_production P) \<turnstile> [Nt A] \<Rightarrow>* map Tm x\<close>
  using assms proof(induction \<open>length (map Tm x)\<close> arbitrary: A x rule: less_induct)
  case less
  then have IH: \<open>\<And>w H. \<lbrakk>length (map Tm w) < length (map Tm x);  w \<in> Re H \<inter> dyck_language (P \<times> {One, Two})\<rbrakk> \<Longrightarrow> transform_production ` P \<turnstile> [Nt H] \<Rightarrow>* map Tm w\<close> using less by simp
  have xRe: \<open>x \<in> Re A\<close> and xDL: \<open>x \<in> dyck_language (P \<times> {One, Two})\<close> using less by blast+

  have p1x: \<open>P1 x\<close> and p2x: \<open>successively P2 x\<close> and p3x: \<open>successively P3 x\<close> and p4x: \<open>successively P4 x\<close> and p5x: \<open>P5 A x\<close> using ReD[OF xRe] by blast+

  from p5x obtain \<pi> t where hd_x: \<open>hd x = (Op, \<pi>, One)\<close>  and pi_def: \<open>\<pi> = (A, t)\<close> by (metis List.list.sel(1) P5.elims(2))
  with xRe have \<open>(Op, \<pi>, One) \<in> set x\<close> by (metis List.list.sel(1) List.list.set_intros(1) ReD(5) chomsky_schuetzenberger.P5.elims(2))
  then have pi_in_P: \<open>\<pi> \<in> P\<close> using xDL by auto

  have bal_x: \<open>bal x\<close> using xDL by blast
  then have \<open>\<exists>y r. bal y \<and> bal r \<and> [\<^bsub>\<pi>\<^esub>\<^sup>1  # tl x = [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # r\<close> using hd_x bal_x bal_Op_split[of \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1 \<close>, where ?xs = \<open>tl x\<close>]  by (metis (no_types, lifting) List.list.exhaust_sel List.list.inject Product_Type.prod.inject chomsky_schuetzenberger.P5.simps(1) p5x)

  then obtain y r1 where \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1  # tl x   =   [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # r1\<close> and bal_y: \<open>bal y\<close> and bal_r1: \<open>bal r1\<close> by blast
  then have split1: \<open>x = [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # r1\<close> using hd_x by (metis List.list.exhaust_sel List.list.set(1) \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1 \<in> set x\<close> empty_iff)
  have r1_not_empty: \<open>r1 \<noteq> []\<close> 
  proof(rule ccontr)
    assume \<open>\<not> r1 \<noteq> []\<close>
    then have \<open>last x = ]\<^bsub>\<pi>\<^esub>\<^sup>1 \<close> using split1 by (metis List.list.distinct(1) Nil_is_append_conv last_ConsR last_snoc)
    then show \<open>False\<close> using p1x using P1D_not_empty split1 by blast
  qed

  from p1x have hd_r1: \<open>hd r1 = [\<^bsub>\<pi>\<^esub>\<^sup>2\<close> using split1 r1_not_empty by (metis (no_types, lifting) List.list.discI List.successively.elims(1) P1'D P1.simps successively_Cons successively_append_iff)


  from bal_r1 have \<open>\<exists>z r2. bal z \<and> bal r2 \<and> [\<^bsub>\<pi>\<^esub>\<^sup>2 # tl r1 = [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ ]\<^bsub>\<pi>\<^esub>\<^sup>2  # r2\<close> using bal_Op_split[of \<open>[\<^bsub>\<pi>\<^esub>\<^sup>2\<close> \<open>tl r1\<close>] by (metis List.list.exhaust_sel List.list.sel(1) Product_Type.prod.inject hd_r1 r1_not_empty) 

  then obtain z r2 where split2': \<open>[\<^bsub>\<pi>\<^esub>\<^sup>2 # tl r1   =   [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ ]\<^bsub>\<pi>\<^esub>\<^sup>2  # r2\<close> and bal_z: \<open>bal z\<close> and bal_r2: \<open>bal r2\<close> by blast+

  then have split2: \<open>x  =   [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ ]\<^bsub>\<pi>\<^esub>\<^sup>2  # r2\<close> by (metis List.list.exhaust_sel hd_r1 r1_not_empty split1)

  have r2_empty: \<open>r2 = []\<close>  \<comment> \<open>prove that if r2 notempty, it would need to start with an open bracket, else it cant be balanced. But this cant be with P2.\<close>
  proof(cases r2)
    case (Cons r2' r2's)
    with bal_r2 obtain g where r2_begin_op: \<open>r2' = (Op, g)\<close> using bal_not_empty[of r2' r2's] using Cons by blast
    have \<open>successively P2 ( ]\<^bsub>\<pi>\<^esub>\<^sup>2  # r2' # r2's)\<close> using p2x  unfolding split2 Cons successively_append_iff by (metis append_Cons successively_append_iff)
    then have \<open>P2 ]\<^bsub>\<pi>\<^esub>\<^sup>2 (r2')\<close> by fastforce
    with r2_begin_op have \<open>False\<close> by (metis chomsky_schuetzenberger.P2.simps(1) split_pairs)
    then show ?thesis by blast
  qed blast

  then have split3: \<open>x  =   [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close> using split2 by blast

  consider (BC) \<open>\<exists>B C. \<pi> = (A, [Nt B, Nt C])\<close> | (a) \<open>\<exists>a. \<pi> = (A, [Tm a])\<close> using assms pi_in_P by (metis CNF_rule_def fst_conv pi_def)
  then show \<open>transform_production ` P \<turnstile> [Nt A] \<Rightarrow>* map Tm x\<close>
  proof(cases)
    case BC
    then obtain B C where pi_eq: \<open>\<pi> = (A, [Nt B, Nt C])\<close> by blast

    from split3 have y_successivelys: \<open>successively P1' y \<and> successively P2 y \<and> successively P3 y \<and> successively P4 y\<close> using P1.simps p1x p2x p3x p4x by (metis List.list.simps(3) Nil_is_append_conv successively_Cons successively_append_iff)

    have y_not_empty: \<open>y \<noteq> []\<close> using p3x pi_eq split1 by fastforce
    have \<open>\<nexists>p. last y = (Cl, (p, One))\<close>
    proof(rule ccontr)
      assume \<open>\<not> (\<nexists>p. last y = ]\<^bsub>p\<^esub>\<^sup>1)\<close>
      then obtain p where last_y: \<open>last y = ]\<^bsub>p\<^esub>\<^sup>1 \<close> by blast
      obtain butl where butl_def: \<open>y = butl @ [last y]\<close> by (metis append_butlast_last_id y_not_empty)

      have  \<open>successively P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using p1x split3 by blast 
      then have \<open>successively P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # (butl@[last y]) @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using butl_def by simp
      then have \<open>successively P1' (([\<^bsub>\<pi>\<^esub>\<^sup>1  # butl) @ last y # [ ]\<^bsub>\<pi>\<^esub>\<^sup>1] @ [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>2 ])\<close> by (metis (no_types, opaque_lifting) Cons_eq_appendI append_assoc append_self_conv2) 
      then have \<open>P1' ]\<^bsub>p\<^esub>\<^sup>1  ]\<^bsub>\<pi>\<^esub>\<^sup>1 \<close>  using last_y by (metis (no_types, lifting) List.successively.simps(3) append_Cons successively_append_iff)
      then show \<open>False\<close> by simp
    qed

    with y_successivelys have P1y: \<open>P1 y\<close> by blast

    with p3x pi_eq have \<open>\<exists>g. hd y = (Op, (B,g), One)\<close> using y_not_empty split3 by (metis (no_types, lifting) P3D1 append_is_Nil_conv hd_append2 successively_Cons)

    then have \<open>P5 B y\<close> by (metis \<open>y \<noteq> []\<close> chomsky_schuetzenberger.P5.simps(2) hd_Cons_tl)


    with y_successivelys P1y have \<open>y \<in> Re B\<close> by blast
    moreover have \<open>y \<in> dyck_language (P \<times> {One, Two})\<close> using split3 bal_y dyck_language_substring by (metis append_Cons append_Nil hd_x split1 xDL)
    ultimately have \<open>y \<in> Re B \<inter> dyck_language (P \<times> {One, Two})\<close> by force

    moreover have \<open>length (map Tm y) < length (map Tm x)\<close> using length_append length_map lessI split3 by fastforce
    ultimately have der_y: \<open>transform_production ` P \<turnstile> [Nt B] \<Rightarrow>* map Tm y\<close> using IH[of y B] split3  by blast




    from split3 have z_successivelys: \<open>successively P1' z \<and> successively P2 z \<and> successively P3 z \<and> successively P4 z\<close> using P1.simps p1x p2x p3x p4x by (metis List.list.simps(3) Nil_is_append_conv successively_Cons successively_append_iff)
    then have successively_P3: \<open>successively P3 (([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>1]) @ [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>2 ])\<close> using split3 p3x by (metis List.append.assoc append_Cons append_Nil)

    have z_not_empty: \<open>z \<noteq> []\<close> using p3x pi_eq split1 successively_P3 by (metis List.list.distinct(1) List.list.sel(1) append_Nil chomsky_schuetzenberger.P3.simps(2) chomsky_schuetzenberger.bracket.simps(2) successively_Cons successively_append_iff)

    then have \<open>P3 [\<^bsub>\<pi>\<^esub>\<^sup>2 (hd z)\<close> by (metis append_is_Nil_conv hd_append2 successively_Cons successively_P3 successively_append_iff)
    with p3x pi_eq have \<open>\<exists>g. hd z = (Op, (C,g), One)\<close> using split_pairs by (metis chomsky_schuetzenberger.P3.simps(2))
    then have \<open>P5 C z\<close> by (metis List.list.exhaust_sel \<open>z \<noteq> []\<close> chomsky_schuetzenberger.P5.simps(2)) 
    moreover have \<open>P1 z\<close>
    proof-
      have \<open>\<nexists>p. last z = ]\<^bsub>p\<^esub>\<^sup>1\<close> 
      proof(rule ccontr)
        assume \<open>\<not> (\<nexists>p. last z = ]\<^bsub>p\<^esub>\<^sup>1)\<close>
        then obtain p where last_y: \<open>last z = ]\<^bsub>p\<^esub>\<^sup>1 \<close> by blast
        obtain butl where butl_def: \<open>z = butl @ [last z]\<close> by (metis append_butlast_last_id z_not_empty)

        have  \<open>successively P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using p1x split3 by blast 
        then have \<open>successively P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # butl @ [last z] @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using butl_def by (metis append_assoc)
        then have \<open>successively P1' (([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # [\<^bsub>\<pi>\<^esub>\<^sup>2 # butl) @ last z # [ ]\<^bsub>\<pi>\<^esub>\<^sup>2 ] @ [])\<close> by (metis (no_types, opaque_lifting) Cons_eq_appendI append_assoc append_self_conv2) 
        then have \<open>P1' ]\<^bsub>p\<^esub>\<^sup>1  ]\<^bsub>\<pi>\<^esub>\<^sup>2 \<close> using last_y by (metis List.append.right_neutral List.successively.simps(3) successively_append_iff)

        then show \<open>False\<close> by simp
      qed
      then show \<open>P1 z\<close> using z_successivelys by blast
    qed



    ultimately have \<open>z \<in> Re C\<close> using z_successivelys by blast
    moreover have \<open>z \<in> dyck_language (P \<times> {One, Two})\<close> using split3 bal_z dyck_language_substring by (smt (z3) List.append.assoc append_Cons self_append_conv2 xDL)

    ultimately have \<open>z \<in> Re C \<inter> dyck_language (P \<times> {One, Two})\<close> by force

    moreover have \<open>length (map Tm z) < length (map Tm x)\<close> using length_append length_map lessI split3 by fastforce
    ultimately have der_z: \<open>transform_production ` P \<turnstile> [Nt C] \<Rightarrow>* map Tm z\<close> using IH[of z C] split3  by blast


    have \<open>transform_production ` P \<turnstile> [Nt A] \<Rightarrow>* [ Tm [\<^bsub>\<pi>\<^esub>\<^sup>1 ] @ [(Nt B)] @ [Tm ]\<^bsub>\<pi>\<^esub>\<^sup>1  , Tm [\<^bsub>\<pi>\<^esub>\<^sup>2 ] @  [(Nt C)] @ [   Tm ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close> by (metis List.append.left_neutral append_Cons bu_prod chomsky_schuetzenberger.transform_production.simps(1) derives_if_bu image_eqI pi_eq pi_in_P)

    also have \<open>transform_production ` P \<turnstile> [ Tm [\<^bsub>\<pi>\<^esub>\<^sup>1 ] @ [(Nt B)] @ [Tm ]\<^bsub>\<pi>\<^esub>\<^sup>1  , Tm [\<^bsub>\<pi>\<^esub>\<^sup>2 ] @  [(Nt C)] @ [   Tm ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]    \<Rightarrow>*    [ Tm [\<^bsub>\<pi>\<^esub>\<^sup>1 ] @ map Tm y @ [Tm ]\<^bsub>\<pi>\<^esub>\<^sup>1  , Tm [\<^bsub>\<pi>\<^esub>\<^sup>2 ] @  [(Nt C)] @ [   Tm ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close> using der_y using derives_append derives_prepend by blast

    also have \<open>transform_production ` P \<turnstile> [ Tm [\<^bsub>\<pi>\<^esub>\<^sup>1 ] @ map Tm y @ [Tm ]\<^bsub>\<pi>\<^esub>\<^sup>1  , Tm [\<^bsub>\<pi>\<^esub>\<^sup>2 ] @  [(Nt C)] @ [   Tm ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]    \<Rightarrow>*    [ Tm [\<^bsub>\<pi>\<^esub>\<^sup>1 ] @ map Tm y @ [Tm ]\<^bsub>\<pi>\<^esub>\<^sup>1  , Tm [\<^bsub>\<pi>\<^esub>\<^sup>2 ] @  (map Tm z) @ [   Tm ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close> using der_z by (meson derives_append derives_prepend)

    finally have \<open>transform_production ` P \<turnstile> [Nt A] \<Rightarrow>* [ Tm [\<^bsub>\<pi>\<^esub>\<^sup>1 ] @ map Tm y @ [Tm ]\<^bsub>\<pi>\<^esub>\<^sup>1  , Tm [\<^bsub>\<pi>\<^esub>\<^sup>2 ] @  (map Tm z) @ [   Tm ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close> by blast

    then show ?thesis using split3 by simp
  next
    case a
    then obtain a where pi_eq: \<open>\<pi> = (A, [Tm a])\<close> by blast
    have \<open>y = []\<close>
    proof(cases y)
      case (Cons y' ys')
      have \<open>P4 [\<^bsub>\<pi>\<^esub>\<^sup>1 y'\<close> using Cons append_Cons p4x split3 by (metis List.successively.simps(3)) 
      then have \<open>y' = (Cl, \<pi>, One)\<close> using P4E by (metis pi_eq)
      moreover obtain g where \<open>y' = (Op, g)\<close> using Cons bal_not_empty bal_y by blast
      ultimately have \<open>False\<close> by blast
      then show ?thesis by blast
    qed blast

    have \<open>z = []\<close>
    proof(cases z)
      case (Cons z' zs')
      have \<open>P4 [\<^bsub>\<pi>\<^esub>\<^sup>2 z'\<close> using p4x split3 by (simp add: Cons \<open>y = []\<close>)
      then have \<open>z' = (Cl, \<pi>, One)\<close> using P4E by (metis Cons bal_not_empty bal_z chomsky_schuetzenberger.bracket.simps(2) fst_eqD pi_eq)
      moreover obtain g where \<open>z' = (Op, g)\<close> using Cons bal_not_empty bal_z by blast
      ultimately have \<open>False\<close> by blast
      then show ?thesis by blast
    qed blast

    have \<open>transform_production ` P \<turnstile> [Nt A] \<Rightarrow>* [ Tm [\<^sub>\<pi>\<^sup>1,       Tm ]\<^sub>\<pi>\<^sup>1 , Tm [\<^sub>\<pi>\<^sup>2 ,       Tm ]\<^sub>\<pi>\<^sup>2   ]\<close> by (metis \<open>\<And>thesis. (\<And>a. \<pi> = (A, [Tm a]) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> chomsky_schuetzenberger.transform_production.simps(2) local.less.prems(2) pi_in_P r_into_rtranclp snd_eqD transform_production_one_step)

    then show ?thesis using \<open>y = []\<close> \<open>z = []\<close> by (simp add: split3)

  qed
qed










































definition brackets'::\<open>('n,'t) Prods \<Rightarrow> (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) set\<close> where
  \<open>brackets' P = { (br,(p,v)) | br p v. p \<in> P }\<close>

lemma brackets'I[intro!]: \<open>p \<in> P \<Longrightarrow> (br,(p,v)) \<in> brackets' P\<close> unfolding brackets'_def by blast
lemma brackets'D1: \<open>(br,(p,v)) \<in> brackets' P \<Longrightarrow> p \<in> P\<close> unfolding brackets'_def by blast
lemmas brackets'E1[elim!] = brackets'D1[elim_format]
lemma brackets'E2[elim]: \<open>\<lbrakk>x \<in> brackets' P; \<And>br p v. \<lbrakk>x = (br,(p,v)); p \<in> P\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close> unfolding brackets'_def by blast


abbreviation brackets::\<open>('n,'t) Prods \<Rightarrow> (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set\<close> where
  \<open>brackets P \<equiv> {x. list_all (\<lambda>y. y \<in> brackets' P) x}\<close>

lemma bracketsI[intro!]: \<open>list_all (\<lambda>y. y \<in> brackets' P) x \<Longrightarrow> x \<in> brackets P\<close> by blast
lemma bracketsD: \<open>x \<in> brackets P \<Longrightarrow> list_all (\<lambda>y. y \<in> brackets' P) x\<close> by blast
lemmas bracketsE[elim!] = bracketsD[elim_format]






text\<open>This is already part of the construction to show P2,P3,P4 regular, but we might use it again in another construction for P1 or P5?\<close>
datatype 'a state = start | garbage |  letter 'a


definition allStates :: \<open>('n,'t) Prods \<Rightarrow>   (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) state set \<close>where
\<open>allStates P = { letter (br,(p,v)) | br p v. p \<in> P } \<union> {start, garbage}\<close>

lemma allStatesI: \<open>p \<in> P \<Longrightarrow> letter (br,(p,v)) \<in> allStates P\<close> unfolding allStates_def by blast
lemma [simp]:\<open>start \<in> allStates P\<close> unfolding allStates_def by blast
lemma [simp]:\<open>garbage \<in> allStates P\<close> unfolding allStates_def by blast

lemma allStatesD1: \<open>letter (br,(p,v)) \<in> allStates P \<Longrightarrow> p \<in> P\<close> unfolding allStates_def by blast
lemmas allStatesE1[elim!] = allStatesD1[elim_format]
lemma allStatesE2[elim]: \<open>\<lbrakk>x \<in> allStates P; x = start \<Longrightarrow> thesis; x = garbage \<Longrightarrow> thesis; \<And>br p v. \<lbrakk>x = letter (br,(p,v)); p \<in> P\<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis\<close> unfolding allStates_def by blast

lemma finite_allStates_if: 
fixes P :: \<open>('n,'t) Prods\<close>
assumes \<open>finite P\<close>
shows \<open>finite( allStates P)\<close>
proof -
  define S::\<open>(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) state set\<close> where  "S = {letter (br, (p, v)) | br p v. p \<in> P}"

  have 1:"S = (\<lambda>(br, p, v). letter (br, (p, v))) ` ({Op, Cl} \<times> P \<times> {One, Two})" unfolding S_def apply auto using bracket.exhaust version.exhaust by (smt (verit, best) SigmaI image_eqI insert_iff)
  
  have "finite ({Op, Cl} \<times> P \<times> {One, Two})" using `finite P` by simp
  then have \<open>finite ((\<lambda>(br, p, v). letter (br, (p, v))) ` ({Op, Cl} \<times> P \<times> {One, Two}))\<close> by blast
  then have \<open>finite S\<close> unfolding 1 by blast
  then have "finite (S \<union> {start, garbage})" by simp
  then show \<open>finite (allStates P)\<close> unfolding allStates_def S_def by blast
qed












section\<open>The construction of an automaton that accepts the language \<open>{xs. successively Q xs \<and>  xs \<in> brackets P}\<close> \<close>

locale successivelyConstruction = 

fixes Q :: "(bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> (bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> bool" \<comment> \<open>e.g. P2\<close>
and P :: "('n,'t) Prods"

assumes finiteP: \<open>finite P\<close>
begin

fun succNext :: \<open>(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) state \<Rightarrow> (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) \<Rightarrow> (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) state\<close> where 
\<open>succNext garbage _ = garbage\<close> | 
\<open>succNext start (br', p', v') = (if p' \<in> P then letter (br', p',v') else garbage )\<close> | 
\<open>succNext (letter (br, p, v)) (br', p', v') =  (if Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P then letter (br',p',v') else garbage)\<close>


theorem succNext_induct[case_names garbage startp startnp letterQ letternQ]:
    fixes R :: "(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) state \<Rightarrow> bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version \<Rightarrow> bool"
    fixes a0 :: "(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) state"
    and a1 :: "bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version"
  assumes "\<And>u. R garbage u"
    and "\<And>br' p' v'. p' \<in> P \<Longrightarrow> R state.start (br', p', v')"
    and "\<And>br' p' v'. p' \<notin> P \<Longrightarrow> R state.start (br', p', v')"
    and "\<And>br p v br' p' v'. Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P \<Longrightarrow> R (letter (br, p, v)) (br', p', v')"
    and "\<And>br p v br' p' v'. \<not>(Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P) \<Longrightarrow> R (letter (br, p, v)) (br', p', v')"
  shows "R a0 a1"
apply(induction rule: succNext.induct) 
using assms apply simp 
apply(case_tac \<open>p' \<in> P\<close>) 
using assms apply simp  
using assms apply simp 
apply(case_tac \<open>Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P\<close>) 
using assms by simp+


abbreviation aut  where \<open>aut \<equiv> \<lparr>dfa'.states = allStates P,
                     init  = start,
                     final = allStates P - {garbage},
                     nxt   = succNext\<rparr>\<close>


interpretation aut : dfa' aut
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by simp 
next
  case 2
  then show ?case by simp
next
  case (3 q x)
  then show ?case apply simp apply(induction rule: succNext_induct[of _ q x]) by (auto simp: allStatesI)
next
  case 4
  then show ?case apply simp using finiteP by (simp add: finite_allStates_if)
qed


corollary dfa_aut: "dfa' aut"
  by unfold_locales


lemma nextl_in_allStates[intro]: \<open>q \<in> allStates P \<Longrightarrow> aut.nextl q ys \<in> allStates P\<close>
apply(induction ys arbitrary: q) apply auto using local.aut.nxt by auto

corollary nextl_in_allStates_from_start[simp]: \<open>aut.nextl start ys \<in> allStates P\<close> using nextl_in_allStates by auto

lemma nextl_garbage[simp]: \<open>aut.nextl garbage xs = garbage\<close> apply(induction xs) by auto

lemma drop_right: \<open>xs@ys \<in> aut.language \<Longrightarrow> xs \<in> aut.language\<close>
proof(induction ys)
  case (Cons a ys)
  then have \<open>xs @ [a] \<in> aut.language\<close> using local.aut.language_def local.aut.nextl_app by fastforce
  then have \<open>xs \<in> aut.language\<close> using local.aut.language_def by force
  then show ?case by blast
qed auto



lemma drop_left_general: \<open>aut.nextl (succNext q x) ys \<noteq> garbage \<Longrightarrow> aut.nextl start ys \<noteq> garbage\<close>
proof(induction ys arbitrary: q x)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  then show ?case using nextl_garbage by (smt (verit, ccfv_threshold) local.aut.nextl.simps(2) local.succNext.elims local.succNext.simps(2) select_convs(4))
qed


lemma drop_left: \<open>xs@ys \<in> aut.language \<Longrightarrow> ys \<in> aut.language\<close>
unfolding aut.language_def apply simp 
apply(induction xs arbitrary: ys) using drop_left_general by auto 


lemma empty_in_aut: \<open>[] \<in> aut.language\<close> unfolding aut.language_def by simp  
lemma singleton_in_aut_iff: \<open>[(br, p, v)] \<in> aut.language \<longleftrightarrow> p \<in> P\<close> unfolding aut.language_def by simp
lemma duo_in_aut_iff: \<open>[(br, p, v), (br', p', v')] \<in> aut.language \<longleftrightarrow> Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P\<close> unfolding aut.language_def by auto 


lemma trio_in_aut_iff: \<open>(br, p, v) # (br', p', v') # zs \<in> aut.language \<longleftrightarrow>   Q (br,p,v) (br',p',v')  \<and>   p \<in> P \<and>   p' \<in> P \<and>   (br',p',v') # zs \<in> aut.language\<close> 
proof(standard, goal_cases)
  case 1
  with drop_left have *:\<open>(br', p', v') # zs \<in> aut.language\<close> by (metis append_Cons append_Nil)

  from drop_right 1 have \<open>[(br, p, v), (br', p', v')] \<in> aut.language\<close> by simp
  with duo_in_aut_iff have **:\<open>Q (br,p,v) (br',p',v') \<and> p \<in> P \<and> p' \<in> P\<close> by blast

  from * ** show ?case by simp
next
  case 2
  then show ?case unfolding aut.language_def by auto
qed






lemma aut_lang_iff_succ_Q: \<open>(successively Q xs \<and>  xs \<in> brackets P) \<longleftrightarrow> (xs \<in> aut.language)\<close>
proof(induction xs rule: induct_list012)
  case 1
  then show ?case using empty_in_aut by auto
next
  case (2 x)
  then show ?case
  apply(standard)
  using singleton_in_aut_iff apply fastforce
  using singleton_in_aut_iff by (metis List.successively.simps(2) brackets'I list_all_simps(1,2) mem_Collect_eq surj_pair)  
next
  case (3 x y zs)
  show ?case
  proof(cases x)
    case (fields br p v)
    then have x_eq: \<open>x = (br, p, v)\<close> by simp
    then show ?thesis
    proof(cases y)
      case (fields br' p' v')
      then have y_eq: \<open>y = (br', p', v')\<close> by simp
      have \<open>(x # y # zs \<in> aut.language) \<longleftrightarrow> Q (br,p,v) (br',p',v')  \<and>   p \<in> P \<and>   p' \<in> P \<and>   (br',p',v') # zs \<in> aut.language\<close> unfolding x_eq y_eq using trio_in_aut_iff by blast
      also have                \<open>...     \<longleftrightarrow> Q (br,p,v) (br',p',v')  \<and>   p \<in> P \<and>   p' \<in> P \<and>  (successively Q ((br',p',v') # zs)  \<and> (br',p',v') # zs \<in> brackets P)\<close> using 3 unfolding x_eq y_eq by blast
      also have                \<open>...     \<longleftrightarrow> successively Q ((br,p,v) # (br',p',v') #zs) \<and> (br,p,v) # (br',p',v') # zs \<in> brackets P\<close> by force
      also have                \<open>...     \<longleftrightarrow> successively Q (x # y #zs) \<and> x # y # zs \<in> brackets P\<close> unfolding x_eq y_eq by blast

      finally show ?thesis by blast
    qed
  qed
qed





lemma aut_language_reg: \<open>regular aut.language\<close> by (metis dfa_aut ex_hf_M regular_def)


corollary regular_successively_inter_brackets: \<open>regular {xs. successively Q xs \<and>  xs \<in> brackets P}\<close> using aut_language_reg aut_lang_iff_succ_Q by auto


end



lemma P2_regular:
fixes P::\<open>('n,'t) Prods\<close>
shows \<open>finite P \<Longrightarrow> regular {xs. successively P2 xs \<and>  xs \<in> brackets P} \<close>
proof-
  assume finite_P: \<open>finite P\<close>
  interpret successivelyConstruction P2 P apply(unfold_locales) using finite_P by blast 
  show ?thesis using regular_successively_inter_brackets by blast
qed


lemma P3_regular:
fixes P::\<open>('n,'t) Prods\<close>
shows \<open>finite P \<Longrightarrow> regular {xs. successively P3 xs \<and>  xs \<in> brackets P} \<close>
proof-
  assume finite_P: \<open>finite P\<close>
  interpret successivelyConstruction P3 P apply(unfold_locales) using finite_P by blast 
  show ?thesis using regular_successively_inter_brackets by blast
qed



lemma P4_regular:
fixes P::\<open>('n,'t) Prods\<close>
shows \<open>finite P \<Longrightarrow> regular {xs. successively P4 xs \<and>  xs \<in> brackets P} \<close>
proof-
  assume finite_P: \<open>finite P\<close>
  interpret successivelyConstruction P4 P apply(unfold_locales) using finite_P by blast 
  show ?thesis using regular_successively_inter_brackets by blast
qed

























section\<open>Construction of an automaton for P1. More Precisely, for the "if not empty, then doesnt end in (Cl,_,1)" part. Then use the other construction for P1' to get P1 regular.\<close>

locale P1Construction = 
fixes P :: "('n,'t) Prods"

assumes finite_P: \<open>finite P\<close>

begin

datatype P1_State = last_ok | last_bad | garbage 

text\<open>The good ending letters, are those that are not of the form (Cl, _ , 1)\<close>
fun good where
\<open>good (Cl, p, One)  = False\<close> | 
\<open>good (br, p, v) = True\<close>


fun nxt :: \<open>P1_State \<Rightarrow> (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) \<Rightarrow> P1_State\<close> where 
\<open>nxt garbage _ = garbage\<close> | 
\<open>nxt last_ok  (br, p, v) = (if p \<notin> P then garbage else (if good (br, p, v) then last_ok else last_bad))\<close> | 
\<open>nxt last_bad (br, p, v) = (if p \<notin> P then garbage else (if good (br, p, v) then last_ok else last_bad))\<close>

print_statement nxt.induct

theorem nxt_induct[case_names garbage startp startnp letterQ letternQ]:
    fixes R :: "P1_State \<Rightarrow> bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version \<Rightarrow> bool"
    fixes a0 :: "P1_State"
    and a1 :: "bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version"
  assumes "\<And>u. R garbage u"
    and "\<And>br p v. p \<notin> P \<Longrightarrow> R last_ok (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> good (br, p, v) \<Longrightarrow> R last_ok (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> \<not>(good (br, p, v)) \<Longrightarrow> R last_ok (br, p, v)"
    and "\<And>br p v. p \<notin> P \<Longrightarrow> R last_bad (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> good (br, p, v) \<Longrightarrow> R last_bad (br, p, v)"
    and "\<And>br p v. p \<in> P \<and> \<not>(good (br, p, v)) \<Longrightarrow> R last_bad (br, p, v)"
  shows "R a0 a1"
apply(induction rule: nxt.induct) 
using assms apply simp 
apply(case_tac \<open>p \<notin> P\<close>)
using assms apply simp
apply(case_tac \<open>good (br, p, v)\<close>)
using assms apply simp 
using assms apply simp
apply(case_tac \<open>p \<notin> P\<close>)
using assms apply simp
apply(case_tac \<open>good (br, p, v)\<close>)
using assms apply simp 
using assms by simp 


abbreviation p1_aut  where \<open>p1_aut \<equiv> \<lparr>dfa'.states = {last_ok, last_bad, garbage},
                     init  = last_ok,
                     final = {last_ok},
                     nxt   = nxt\<rparr>\<close>


interpretation p1_aut : dfa' p1_aut
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by simp 
next
  case 2
  then show ?case by simp
next
  case (3 q x)
  then show ?case apply simp apply(induction rule: nxt_induct[of _ q x]) by auto
next
  case 4
  then show ?case by simp
qed


corollary dfa_p1_aut: "dfa' p1_aut"
  by unfold_locales


lemma empty_in_aut[simp]: \<open>[] \<in> p1_aut.language\<close> unfolding p1_aut.language_def by auto

lemma singleton_in_aut_iff: \<open>[(br, p, v)] \<in> p1_aut.language \<longleftrightarrow> (good (br, p, v) \<and> p \<in> P)\<close>
unfolding p1_aut.language_def apply(induction \<open>(br,p,v)\<close> rule: good.induct) by auto

lemma nextl_garbage_iff[simp]:\<open>p1_aut.nextl last_ok xs = garbage \<longleftrightarrow> \<not>(xs \<in> brackets P)\<close>
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by simp 
next
  case (snoc x xs)
  then have \<open>(xs @ [x] \<notin> brackets P) \<longleftrightarrow> (xs \<notin> brackets P \<or> [x] \<notin> brackets P)\<close> by auto
  moreover have \<open>(p1_aut.nextl last_ok (xs@[x]) = garbage) \<longleftrightarrow> (p1_aut.nextl last_ok xs = garbage) \<or> ((p1_aut.nextl last_ok (xs @ [x]) = garbage) \<and> (p1_aut.nextl last_ok (xs) \<noteq> garbage))\<close> by auto
  ultimately show ?case using snoc by (smt (verit, del_insts) brackets'E2 brackets'I list_all_simps(1,2) local.P1_State.exhaust local.P1_State.simps(3,5) local.nxt.simps(2,3) local.p1_aut.nextl_snoc mem_Collect_eq prod_cases3 select_convs(4)) 
  qed




lemma lang_descr_full: \<open>(p1_aut.nextl last_ok xs = last_ok \<longleftrightarrow> (xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets P))) \<and> (p1_aut.nextl last_ok xs = last_bad \<longleftrightarrow> ((xs \<noteq> [] \<and> \<not>good (last xs) \<and> xs \<in> brackets P)))\<close>
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case
  proof(cases \<open>p1_aut.nextl last_ok (xs@[x]) = garbage\<close>)
    case True
    then show ?thesis using nextl_garbage_iff by (metis local.P1_State.distinct(4,6) local.p1_aut.nextl.simps(1))
  next
    case False
    then have br: \<open>xs \<in> brackets P\<close> \<open>[x] \<in> brackets P\<close> by (metis list_all_append mem_Collect_eq nextl_garbage_iff)+
    with snoc consider \<open>(p1_aut.nextl last_ok xs = last_ok)\<close> | \<open>(p1_aut.nextl last_ok xs = last_bad)\<close> using nextl_garbage_iff by blast
    then show ?thesis
    proof(cases)
      case 1
      then show ?thesis using br apply(cases \<open>good x\<close>) by auto 
    next
      case 2
      then show ?thesis using br apply(cases \<open>good x\<close>) by auto 
    qed
  qed
qed



lemma lang_descr: \<open>xs \<in> p1_aut.language \<longleftrightarrow> (xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets P))\<close>
unfolding p1_aut.language_def using lang_descr_full by auto


lemma good_iff[simp]:\<open>(\<forall>a b. last xs \<noteq> ]\<^bsub>(a, b)\<^esub>\<^sup>1) = good (last xs)\<close> apply auto by (metis local.good.elims(3) split_pairs)


lemma in_P1_iff: \<open>(P1 xs \<and> xs \<in> brackets P ) \<longleftrightarrow>  (xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets P)) \<and> successively P1' xs \<and>  xs \<in> brackets P\<close> using good_iff by auto

corollary P1_eq: \<open>{xs. P1 xs \<and> xs \<in> brackets P}  =   {xs. successively P1' xs \<and>  xs \<in> brackets P}   \<inter>   {xs. xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets P)}\<close> using in_P1_iff by blast


lemma P1'_regular:
shows \<open>regular {xs. successively P1' xs \<and>  xs \<in> brackets P} \<close>
proof-
  interpret successivelyConstruction P1' P apply(unfold_locales) using finite_P by blast 
  show ?thesis using regular_successively_inter_brackets by blast
qed

lemma aut_language_reg: \<open>regular p1_aut.language\<close> by (metis dfa_p1_aut ex_hf_M regular_def)

corollary aux_regular: \<open>regular {xs. xs = [] \<or> (xs \<noteq> [] \<and> good (last xs) \<and> xs \<in> brackets P)}\<close> using lang_descr aut_language_reg p1_aut.language_def by simp


corollary regular_P1: \<open>regular {xs. P1 xs \<and> xs \<in> brackets P}\<close> unfolding P1_eq using P1'_regular aux_regular using regular_Int by blast


end




lemma P1_regular:
fixes P::\<open>('n,'t) Prods\<close>
shows \<open>finite P \<Longrightarrow> regular {xs. P1 xs \<and> xs \<in> brackets P} \<close>
proof-
  assume finite_P: \<open>finite P\<close>
  interpret P1Construction P apply(unfold_locales) using finite_P by blast 
  show ?thesis using regular_P1 by blast
qed










locale P5Construction = 
fixes P :: "('n,'t) Prods"
and A :: 'n
assumes finite_P: \<open>finite P\<close>

begin

datatype P5_State = start | first_ok | garbage 

text\<open>The good ending letters, are those that are not of the form (Cl, _ , 1)\<close>
fun ok where
\<open>ok (Op, (X, _), One) = (X = A)\<close> | 
\<open>ok _ = False\<close>



fun nxt :: \<open>P5_State \<Rightarrow> (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) \<Rightarrow> P5_State\<close> where 
\<open>nxt garbage _ = garbage\<close> | 
\<open>nxt start  (br, (X, r), v) = (if (X,r) \<notin> P then garbage else (if ok (br, (X, r), v) then first_ok else garbage))\<close> | 
\<open>nxt first_ok (br, p, v) = (if p \<notin> P then garbage else first_ok)\<close>



theorem nxt_induct[case_names garbage startnp start_p_ok start_p_nok first_ok_np first_ok_p]:
    fixes R :: "P5_State \<Rightarrow> bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version \<Rightarrow> bool"
    fixes a0 :: "P5_State"
    and a1 :: "bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version"
  assumes "\<And>u. R garbage u"
    and "\<And>br p v. p \<notin> P \<Longrightarrow> R start (br, p, v)"
    and "\<And>br X r v. (X, r) \<in> P \<and> ok (br, (X, r), v) \<Longrightarrow> R start (br, (X, r), v)"
    and "\<And>br X r v. (X, r) \<in> P \<and> \<not>ok (br, (X, r), v) \<Longrightarrow> R start (br, (X, r), v)"
    and "\<And>br X r v. (X, r) \<notin> P  \<Longrightarrow> R first_ok (br, (X, r), v)"
    and "\<And>br X r v. (X, r) \<in> P  \<Longrightarrow> R first_ok (br, (X, r), v)"
  shows "R a0 a1"
apply(induction rule: nxt.induct) 
using assms apply simp 
apply(case_tac \<open>(X, r) \<notin> P\<close>; case_tac \<open>ok (br, (X, r), v)\<close>)
using assms apply simp
using assms apply simp
using assms apply simp
using assms apply simp
apply(case_tac \<open>p \<notin> P\<close>)
using assms by fast+


abbreviation p5_aut  where \<open>p5_aut \<equiv> \<lparr>dfa'.states = {start, first_ok, garbage},
                     init  = start,
                     final = {first_ok},
                     nxt   = nxt\<rparr>\<close>


interpretation p5_aut : dfa' p5_aut
proof(unfold_locales, goal_cases)
  case 1
  then show ?case by simp 
next
  case 2
  then show ?case by simp
next
  case (3 q x)
  then show ?case apply simp apply(induction rule: nxt_induct[of _ q x]) by auto
next
  case 4
  then show ?case by simp
qed


corollary dfa_p5_aut: "dfa' p5_aut"
  by unfold_locales



corollary nxt_start_ok_iff: \<open>ok x \<and> x \<in> brackets' P \<longleftrightarrow> nxt start x = first_ok\<close> apply(cases x) apply(rename_tac br p v) apply(case_tac br; case_tac v; case_tac \<open>p \<in> P\<close>) by (auto split: if_splits)

lemma empty_not_in_lang[simp]:\<open>[] \<notin> p5_aut.language\<close> unfolding p5_aut.language_def by auto 

lemma singleton_in_lang_iff: \<open>[x] \<in> p5_aut.language \<longleftrightarrow> ok (hd [x]) \<and> [x] \<in> brackets P\<close> unfolding p5_aut.language_def using nxt_start_ok_iff by auto

lemma singleton_first_ok_iff: \<open>p5_aut.nextl start ([x]) = first_ok \<or> p5_aut.nextl start ([x]) = garbage\<close> apply(cases x) apply(rename_tac br p v) apply(case_tac br; case_tac v; case_tac \<open>p \<in> P\<close>) by (auto split: if_splits)

lemma first_ok_iff: \<open>xs\<noteq> [] \<Longrightarrow> p5_aut.nextl start xs = first_ok \<or> p5_aut.nextl start xs = garbage\<close>
proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by blast
next
  case (snoc x xs)
  then show ?case
  proof(cases \<open>xs = []\<close>)
    case True
    then show ?thesis unfolding True using singleton_first_ok_iff by auto
  next
    case False
    with snoc have \<open>p5_aut.nextl start xs = first_ok \<or> p5_aut.nextl start xs = garbage\<close> by blast
    then show ?thesis apply(cases x) apply(rename_tac br p v) apply(case_tac br; case_tac v; case_tac \<open>p \<in> P\<close>) by (auto split: if_splits)
  qed
qed

lemma lang_descr: \<open>xs \<in> p5_aut.language \<longleftrightarrow> (xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets P)\<close>
proof(induction xs rule: rev_induct)
  case (snoc x xs)
  then have IH: \<open>(xs \<in> p5_aut.language) = (xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets P)\<close> by blast
  then show ?case
  proof(cases xs)
    case Nil
    then show ?thesis using singleton_in_lang_iff by auto
  next
    case (Cons y ys)
    then have xs_eq: \<open>xs = y # ys\<close> by blast
    then show ?thesis
    proof(cases \<open>xs \<in> p5_aut.language\<close>)
      case True
      then have \<open>(xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets P)\<close> using IH by blast
      then show ?thesis apply(cases x) apply(rename_tac br p v) using local.p5_aut.language_def snoc by auto
    next
      case False
      then have \<open>p5_aut.nextl start xs = garbage\<close> unfolding p5_aut.language_def using first_ok_iff[of xs] Cons by auto
      then have \<open>p5_aut.nextl start (xs@[x]) = garbage\<close> by simp
      then show ?thesis using IH unfolding xs_eq by (metis Cons_eq_appendI False List.list.distinct(1) List.list.sel(1) list_all_append local.P5_State.simps(6) local.p5_aut.language_def mem_Collect_eq select_convs(2,3) singleton_iff xs_eq) 
      qed
    qed
  qed simp

lemma in_P5_iff: \<open>P5 A xs \<and> xs \<in> brackets P \<longleftrightarrow> (xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets P)\<close> apply auto by (metis List.list.exhaust_sel chomsky_schuetzenberger.P5.simps(2) local.ok.elims(2))

lemma aut_language_reg: \<open>regular p5_aut.language\<close> by (metis dfa_p5_aut ex_hf_M regular_def)

corollary aux_regular: \<open>regular {xs. xs \<noteq> [] \<and> ok (hd xs) \<and> xs \<in> brackets P}\<close> using lang_descr aut_language_reg p5_aut.language_def by simp

lemma regular_P5:\<open>regular {xs. P5 A xs \<and> xs \<in> brackets P}\<close> using in_P5_iff aux_regular by presburger

end







lemma P5_regular:
fixes P::\<open>('n,'t) Prods\<close>
and A:: 'n
shows \<open>finite P \<Longrightarrow> regular {xs. P5 A xs \<and> xs \<in> brackets P} \<close>
proof-
  assume finite_P: \<open>finite P\<close>
  interpret P5Construction P A apply(unfold_locales) using finite_P by blast 
  show ?thesis using regular_P5 by blast
qed


corollary regular_Re_inter: \<open>finite P \<Longrightarrow> regular ((brackets P) \<inter> Re A)\<close>
proof-
assume finite_P: \<open>finite P\<close>

then have regs: \<open>regular {xs. P1 xs \<and> xs \<in> brackets P}\<close>  \<open>regular {xs. successively P2 xs \<and>  xs \<in> brackets P}\<close> \<open>regular {xs. successively P3 xs \<and>  xs \<in> brackets P}\<close> \<open>regular {xs. successively P4 xs \<and>  xs \<in> brackets P}\<close> \<open>regular {xs. P5 A xs \<and> xs \<in> brackets P}\<close>
using P1_regular[OF \<open>finite P\<close>] P2_regular[OF \<open>finite P\<close>] P3_regular[OF \<open>finite P\<close>] P4_regular[OF \<open>finite P\<close>] P5_regular[OF \<open>finite P\<close>] by blast+ 

hence \<open>regular ({xs. P1 xs \<and> xs \<in> brackets P}\<inter>{xs. successively P2 xs \<and>  xs \<in> brackets P}\<inter>{xs. successively P3 xs \<and>  xs \<in> brackets P}\<inter>{xs. successively P4 xs \<and>  xs \<in> brackets P}\<inter>{xs. P5 A xs \<and> xs \<in> brackets P})\<close> by (meson regular_Int)

moreover have set_eq: \<open>{xs. P1 xs \<and> xs \<in> brackets P}\<inter>{xs. successively P2 xs \<and>  xs \<in> brackets P}\<inter>{xs. successively P3 xs \<and>  xs \<in> brackets P}\<inter>{xs. successively P4 xs \<and>  xs \<in> brackets P}\<inter>{xs. P5 A xs \<and> xs \<in> brackets P} = brackets P \<inter> Re A\<close> by auto 

ultimately show ?thesis by argo
qed



































lemma dyck_lang_imp_star_brackets: \<open>dyck_language (P \<times> {One, Two}) \<subseteq> (brackets P)\<close>
proof
  fix x
  assume \<open>x \<in> dyck_language (P \<times> {One, Two})\<close>
  then have \<open>\<forall>x\<in>set x. x \<in> brackets' P\<close>
  proof(safe, goal_cases)
    case (1 br A r v)
    then have \<open>((A, r), v) \<in> P \<times> {One, Two}\<close> unfolding dyck_language_def by fastforce
    then show ?case unfolding brackets'_def dyck_language_def by blast
  qed
  then show \<open>x \<in> (brackets P)\<close> by (simp add: Ball_set_list_all)
qed














section\<open>Lemmas about star and star1\<close>

text\<open>TODO mv?\<close>

lemma star_mono: \<open>A \<subseteq> B \<Longrightarrow> star A \<subseteq> star B\<close> by (metis (full_types) in_star_iff_concat subsetI subset_trans)


text\<open>splits the string until we finally get something from A\<close>
lemma split_star_union:
  assumes \<open>zs \<in> star( A \<union> B )\<close>
  shows \<open>zs \<in> star B  \<or>  (\<exists>bs a zs'. zs = bs @ a @ zs' \<and> bs \<in> star B \<and> a \<in> A \<and> zs' \<in> star(A \<union> B))\<close>
  using assms proof(induction zs rule: star_induct)
  case (append u zs)
  then consider (A) \<open>u \<in> A\<close> | (B) \<open>u \<in> B\<close> by blast
  then show ?case
  proof(cases)
    case A
    then have \<open>u @ zs = [] @ u @ zs \<and> [] \<in> star B \<and> u \<in> A \<and> zs \<in> star(A \<union> B)\<close> using append by blast 
    then show ?thesis by blast
  next
    case B
    then consider (zsB) \<open>zs \<in> star B\<close> | (Split) \<open>(\<exists>bs a zs'. zs = bs @ a @ zs' \<and> bs \<in> star B \<and> a \<in> A \<and> zs' \<in> star (A \<union> B))\<close> using append by blast
    then show ?thesis
    proof(cases)
      case zsB
      then have \<open>u@zs \<in> star B\<close> using B by simp
      then show ?thesis by blast
    next
      case Split
      then obtain bs a zs' where split: \<open>zs = bs @ a @ zs'\<close> \<open>bs \<in> star B\<close> \<open>a \<in> A\<close> \<open>zs' \<in> star (A \<union> B)\<close> by blast
      then have \<open>u \<in> star B\<close> using B using star_if_lang by blast
      then have \<open>u@bs \<in> star B\<close> using append_in_starI[of u B bs, OF \<open>u \<in> star B\<close> \<open>bs \<in> star B\<close>] by blast
      moreover have \<open>u@zs = (u@bs) @ a @ zs'\<close> unfolding split by simp 
      ultimately have \<open>u@zs = (u@bs) @ a @ zs' \<and> (u@bs) \<in> star B \<and> a \<in> A \<and> zs' \<in> star(A \<union> B)\<close> using split by blast
      then show ?thesis by blast
    qed
  qed
qed auto








section\<open>star1 definition\<close>

text\<open>TODO mv?\<close>

abbreviation star1 :: "'a lang \<Rightarrow> 'a lang" where 
  \<open>star1 A \<equiv> A @@ star A\<close>


lemma conc1_star: \<open>A @@ star A = (\<Union>n. A ^^ (n+1))\<close> by (metis (no_types, lifting) ext Regular_Set.lang_pow.simps(2) Suc_eq_plus1 conc_UNION_distrib(2) conc_pow_comm conc_star_comm star_def)

lemma star1_if_lang_pow_Suc[simp]: "w : A ^^ (n+1) \<Longrightarrow> w : star1 A"  by (metis UNIV_I UN_I conc1_star)

lemma concat_star1_star_concat: \<open>A @@ star1( star A @@ B) \<subseteq> star1( star A @@ B)\<close> using Arden_star_is_sol Un_iff conc_assoc by (metis subsetI)

lemma concat_star1_star1_concat: \<open>A @@ star1( star1 A @@ B) \<subseteq> star1( star1 A @@ B)\<close> using Arden_star_is_sol Un_iff conc_assoc by (metis conc_mono subsetI) 








lemma append_star_star1_conc:
  assumes \<open>bs \<in> star (star1 X @@ Y)\<close>
    and \<open>bs \<noteq> []\<close>
    and \<open>a \<in> X\<close>
  shows \<open>a@bs \<in> star (star1 X @@ Y)\<close>
  using assms by (smt (verit, del_insts) List.append.assoc concI conc_assoc conc_star_comm conc_star_star star_decom star_if_lang)







text\<open>Probably not needed. Delete?\<close>
lemma star1_induct[consumes 1, case_names base append, induct set: star]:
  assumes "w : star1 A"
    and base: "\<And>u. u \<in> A \<Longrightarrow> P u"
    and step: "\<And>u v. u : A \<Longrightarrow> v \<in> star1 A \<Longrightarrow> P v \<Longrightarrow> P (u@v)"
  shows "P w"
proof -
  { fix n have "w \<in> A ^^ (n+1) \<Longrightarrow> P w"
    proof(induct n arbitrary: w) 
      case 0
      then show ?case using base by auto
    next
      case (Suc n)
      then obtain a an where an_def: \<open>w = a @ an\<close> and \<open>an \<in> A^^(n+1)\<close> and \<open>a \<in> A\<close> by (metis Regular_Set.lang_pow.simps(2) Suc_eq_plus1 concE)  
      then have \<open>P an\<close> using Suc by blast
      then have \<open>P (a @ an)\<close> using step[OF \<open>a \<in> A\<close>] using \<open>an \<in> A ^^ (n + 1)\<close> by auto
      then show ?case unfolding an_def by blast
    qed}
  with \<open>w : star1 A\<close> show "P w"  by (metis (no_types, lifting) UN_iff conc1_star)
qed























































































section\<open>Transformation of a parse tree\<close>


abbreviation \<open>prod_rhs ts \<equiv> map root ts\<close>

fun transform_tree :: \<open>('n,'t) tree \<Rightarrow> ('n, bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) tree\<close> where
  \<open>transform_tree (Sym (Nt A)) = (Sym (Nt A))\<close> | 
  \<open>transform_tree (Sym (Tm a)) = (Sym (Tm (Op, ((SOME A. True, [Tm a]), One))))\<close> | 
  \<open>transform_tree (Prod A [Sym (Tm a)]) =             (Prod A [ Sym (Tm (Op, (A, [Tm a]),One)),       Sym(Tm (Cl, (A, [Tm a]), One)), Sym (Tm (Op, (A, [Tm a]), Two)),       Sym(Tm (Cl, (A, [Tm a]), Two))  ])\<close> | 
  \<open>transform_tree (Prod A [Sym (Nt B), Sym (Nt C)]) =  (Prod A [Sym (Tm (Op, (A, [Nt B, Nt C]), One)), Sym (Nt B), Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))), Sym (Tm (Op, (A, [Nt B, Nt C]), Two)), Sym (Nt C), Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))  ])\<close> | 
  \<open>transform_tree (Prod A [Prod B tB, Sym (Nt C)]) =   (Prod A [Sym (Tm (Op, (A, [Nt B, Nt C]), One)), transform_tree (Prod B tB), Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))), Sym (Tm (Op, (A, [Nt B, Nt C]), Two)), Sym (Nt C), Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))  ])  \<close> | 
  \<open>transform_tree (Prod A [Sym (Nt B), Prod C tC]) =   (Prod A [Sym (Tm (Op, (A, [Nt B, Nt C]), One)), Sym (Nt B), Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))), Sym (Tm (Op, (A, [Nt B, Nt C]), Two)), transform_tree (Prod C tC), Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))  ])\<close> | 
  \<open>transform_tree (Prod A [Prod B tB, Prod C tC]) =   (Prod A [Sym (Tm (Op, (A, [Nt B, Nt C]), One)), transform_tree (Prod B tB), Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))), Sym (Tm (Op, (A, [Nt B, Nt C]), Two)), transform_tree (Prod C tC), Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))  ])\<close> | 
  \<open>transform_tree (Prod A y) = (Prod A [])\<close>

lemma root_of_transform_tree[intro]: \<open>root t = Nt X \<Longrightarrow> root (transform_tree t) = Nt X\<close>
  apply(induction t rule: transform_tree.induct) by auto 


lemma transform_tree_correct:
  fixes P
  defines \<open>P' \<equiv> transform_production ` P\<close>
  assumes \<open>parse_tree P t \<and> fringe t = w\<close>
    and \<open>\<And>p. p \<in> P \<Longrightarrow> CNF_rule p\<close>
  shows \<open>parse_tree P' (transform_tree t)  \<and>  the_hom_ext (fringe (transform_tree t)) = w\<close>
  using assms proof(induction t arbitrary: w)
  case (Sym x)
  from Sym have pt: \<open>parse_tree P (Sym x)\<close> and \<open>fringe (Sym x) = w\<close> by blast+
  from Sym have CNF: \<open>\<And>p. p \<in> P \<Longrightarrow> CNF_rule p\<close> by blast
  then show ?case 
  proof(cases x)
    case (Nt x1)
    then have \<open>transform_tree (Sym x) = (Sym (Nt x1))\<close> by simp 
    then show ?thesis using Sym by (metis Nt Parse_Tree.fringe.simps(1) Parse_Tree.parse_tree.simps(1) the_hom_ext_keep_var)
  next
    case (Tm x2)
    then obtain a where \<open>transform_tree (Sym x) = (Sym (Tm (Op, ((SOME A. True, [Tm a]), One))))\<close> by simp
    then have \<open>fringe ... = [(Tm (Op, ((SOME A. True, [Tm a]), One)))]\<close> by simp
    then have \<open>the_hom_ext ... = [Tm a]\<close> by simp
    then have \<open>... = w\<close> using Sym using Tm \<open>transform_tree (Sym x) = Sym (Tm [\<^bsub>(SOME A. True, [Tm a])\<^esub>\<^sup>1 )\<close> by force
    then show ?thesis  using Sym by (metis Parse_Tree.parse_tree.simps(1) \<open>fringe (Sym (Tm [\<^bsub>(SOME A. True, [Tm a])\<^esub>\<^sup>1 )) = [Tm [\<^bsub>(SOME A. True, [Tm a])\<^esub>\<^sup>1 ]\<close> \<open>the_hom_ext [Tm [\<^bsub>(SOME A. True, [Tm a])\<^esub>\<^sup>1 ] = [Tm a]\<close> \<open>transform_tree (Sym x) = Sym (Tm [\<^bsub>(SOME A. True, [Tm a])\<^esub>\<^sup>1 )\<close>)
  qed
next
  case (Prod A ts)
  from Prod have pt: \<open>parse_tree P (Prod A ts)\<close> and fr: \<open>fringe (Prod A ts) = w\<close> by blast+
  from Prod have IH: \<open>\<And>x2a w'. \<lbrakk>x2a \<in> set ts; parse_tree P x2a \<and> fringe x2a = w'\<rbrakk> \<Longrightarrow> parse_tree P' (transform_tree x2a) \<and> the_hom_ext (fringe (transform_tree x2a)) = w'\<close> using P'_def by blast

  from pt have \<open>(A, map root ts) \<in> P\<close> by simp
  then have \<open>CNF_rule (A, map root ts)\<close> using Prod.prems(2) by blast

  then obtain B C a where 
    def: \<open>(A, prod_rhs ts) = (A, [Nt B, Nt C]) \<and> transform_production (A, prod_rhs ts) = (A, [Tm [\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>1 , Nt B, Tm ]\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>1, Tm [\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>2, Nt C, Tm ]\<^bsub>(A, [Nt B, Nt C])\<^esub>\<^sup>2 ]) 
\<or>
       (A, prod_rhs ts) = (A, [Tm a]) \<and> transform_production (A, prod_rhs ts) = (A, [Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>1 , Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>1, Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>2, Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>2 ])\<close> using transform_production_when_CNF' assms(3) by meson
  then obtain e1 e2 e3 where ei_def: \<open>ts = [e1] \<or> ts = [e2, e3]\<close> by blast  
  obtain tB tC where 
    \<open>(ts = [Sym (Tm a)] \<and> prod_rhs ts = [Tm a]) 
\<or> 
prod_rhs ts = [Nt B, Nt C]  \<and>  (ts = [Sym (Nt B), Sym (Nt C)] \<or> ts = [Prod B tB, Sym (Nt C)] \<or> ts = [Sym (Nt B), Prod C tC] \<or> ts = [Prod B tB, Prod C tC])\<close>
    apply(rule disjE[OF def]) 
    using root.elims root.simps \<open>CNF_rule (A, prod_rhs ts)\<close> apply (smt (verit, ccfv_threshold) CFG.sym.inject(1) Cons_eq_map_D Product_Type.prod.inject map_is_Nil_conv)
    using root.elims root.simps \<open>CNF_rule (A, prod_rhs ts)\<close> 
  proof -
    assume a1: "(A, prod_rhs ts) = (A, [Tm a]) \<and> transform_production (A, prod_rhs ts) = (A, [Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>1 , Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>1, Tm [\<^bsub>(A, [Tm a])\<^esub>\<^sup>2, Tm ]\<^bsub>(A, [Tm a])\<^esub>\<^sup>2 ])"
    assume a2: "\<And>tB tC. ts = [Sym (Tm a)] \<and> prod_rhs ts = [Tm a] \<or> prod_rhs ts = [Nt B, Nt C] \<and> (ts = [Sym (Nt B), Sym (Nt C)] \<or> ts = [Prod B tB, Sym (Nt C)] \<or> ts = [Sym (Nt B), Prod C tC] \<or> ts = [Prod B tB, Prod C tC]) \<Longrightarrow> thesis"
    have f3: "prod_rhs [] = []"
      by force
    have "[] \<noteq> ts"
      using a1 by force
    then show ?thesis
      using f3 a2 a1 by (metis (no_types) CFG.sym.simps(4) List.last.simps List.list.simps(9) Parse_Tree.root.elims Product_Type.prod.inject ei_def not_Cons_self2)
  qed


  then consider (Tm) \<open>ts = [Sym (Tm a)] \<and> prod_rhs ts = [Tm a]\<close> | (Nt_Nt) \<open>prod_rhs ts = [Nt B, Nt C] \<and> ts = [Sym (Nt B), Sym (Nt C)]\<close> | (Prod_Nt) \<open>prod_rhs ts = [Nt B, Nt C] \<and> ts = [Prod B tB, Sym (Nt C)]\<close> | (Nt_Prod) \<open>prod_rhs ts = [Nt B, Nt C] \<and> ts = [Sym (Nt B), Prod C tC]\<close> | (Prod_Prod) \<open>prod_rhs ts = [Nt B, Nt C] \<and> ts = [Prod B tB, Prod C tC]\<close> by argo
  then show ?case
  proof(cases)
    case Tm
    then have ts_eq: \<open>ts = [Sym (Tm a)]\<close> and prod_rhs: \<open>prod_rhs ts = [Tm a]\<close> by blast+
    then have \<open>transform_tree (Prod A ts) = (Prod A [ Sym (Tm (Op, (A, [Tm a]),One)),       Sym(Tm (Cl, (A, [Tm a]), One)), Sym (Tm (Op, (A, [Tm a]), Two)),       Sym(Tm (Cl, (A, [Tm a]), Two))  ])\<close> by simp
    then have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = [Tm a]\<close> by simp
    also have \<open>... = w\<close> using fr unfolding ts_eq by auto
    finally have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = w\<close> .

    moreover have \<open>parse_tree (P') (transform_tree (Prod A [Sym (Tm a)]))\<close> using pt prod_rhs unfolding P'_def apply auto by (metis chomsky_schuetzenberger.transform_production.simps(2) imageI) 
    ultimately show ?thesis unfolding ts_eq P'_def by blast
  next
    case Nt_Nt
    then have ts_eq: \<open>ts = [Sym (Nt B), Sym (Nt C)]\<close>  and prod_rhs: \<open>prod_rhs ts = [Nt B, Nt C]\<close> by blast+
    then have \<open>transform_tree (Prod A ts) = (Prod A [Sym (Tm (Op, (A, [Nt B, Nt C]), One)), Sym (Nt B), Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))), Sym (Tm (Op, (A, [Nt B, Nt C]), Two)), Sym (Nt C), Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))  ])\<close> by simp
    then have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = [ Nt B, Nt C  ]\<close> by simp
    also have \<open>... = w\<close> using fr unfolding ts_eq by auto
    finally have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = w\<close> .

    moreover have \<open>parse_tree (P') (transform_tree (Prod A [Sym (Nt B), Sym (Nt C)]))\<close> using pt prod_rhs unfolding P'_def apply auto by (metis chomsky_schuetzenberger.transform_production.simps(1) imageI)
    ultimately show ?thesis unfolding ts_eq by blast
  next
    case Prod_Nt
    then have ts_eq: \<open>ts = [Prod B tB, Sym (Nt C)]\<close>  and prod_rhs: \<open>prod_rhs ts = [Nt B, Nt C]\<close> by blast+
    then have transf_ts: \<open>transform_tree (Prod A ts) = (Prod A   [  Sym (Tm (Op, (A, [Nt B, Nt C]), One)),  transform_tree (Prod B tB),  Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))),  Sym (Tm (Op, (A, [Nt B, Nt C]), Two)),   Sym (Nt C),   Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))    ] )\<close> by simp

    then have frA: \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = the_hom_ext (fringe (transform_tree (Prod B tB))) @ [  Nt C  ]\<close> by simp

    have ptB: \<open>parse_tree P (Prod B tB)\<close> using pt ts_eq by (meson List.list.set_intros(1) Parse_Tree.parse_tree.simps(2))
    then have ptB: \<open>parse_tree (P') (transform_tree (Prod B tB))\<close> \<open>the_hom_ext (fringe (transform_tree (Prod B tB))) = fringe (Prod B tB)\<close>
      using IH[of \<open>Prod B tB\<close> \<open>fringe (Prod B tB)\<close>] by (metis List.list.set_intros(1) assms(2) ts_eq)+

    with frA have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = fringe (Prod B tB) @ [Nt C]\<close> 
      by presburger
    also have \<open>... = fringe (Prod A [Prod B tB, Sym (Nt C)])\<close> 
      using fringe.simps(2)[of A \<open>[Prod B tB, Sym (Nt C)]\<close>] 
      by auto
    also have \<open>... = fringe (Prod A ts)\<close> 
      using ts_eq prod_rhs pt by blast
    also have \<open>... = w\<close> 
      using fr unfolding ts_eq by auto
    finally have fin: \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = w\<close> .

    have \<open>parse_tree (P') (transform_tree (Prod B tB)) \<and> (A, map root ts) \<in> P\<close> 
      by (simp add: \<open>(A, prod_rhs ts) \<in> P\<close> ptB(1)) 
    moreover have \<open>root (transform_tree (Prod B tB)) = Nt B\<close> 
      apply(induction \<open>(Prod B tB)\<close> rule: transform_tree.induct) by auto
    moreover have \<open>transform_production (A, prod_rhs ts) \<in> P'\<close> 
      by (simp add: P'_def \<open>(A, prod_rhs ts) \<in> P\<close>)
    ultimately have \<open>parse_tree (P') (transform_tree (Prod A ts))\<close> 
      unfolding transf_ts ts_eq P'_def using ptB parse_tree.simps prod_rhs def by auto

    then show ?thesis using fin by blast

  next
    case Nt_Prod
    then have ts_eq: \<open>ts = [Sym (Nt B), Prod C tC]\<close>  and prod_rhs: \<open>prod_rhs ts = [Nt B, Nt C]\<close> by blast+
    then have transf_ts: \<open>transform_tree (Prod A ts) = (Prod A   [  Sym (Tm (Op, (A, [Nt B, Nt C]), One)),  Sym (Nt B),  Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))),  Sym (Tm (Op, (A, [Nt B, Nt C]), Two)),   transform_tree (Prod C tC),   Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))    ] )\<close> by simp

    then have frA: \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = the_hom_ext ([  Nt B  ]@fringe (transform_tree (Prod C tC)))\<close> by simp

    have ptC: \<open>parse_tree P (Prod C tC)\<close> using pt ts_eq by (meson List.list.set_intros(1,2) Parse_Tree.parse_tree.simps(2))

    then have ptC: \<open>parse_tree (P') (transform_tree (Prod C tC))\<close> \<open>the_hom_ext (fringe (transform_tree (Prod C tC))) = fringe (Prod C tC)\<close>
      using IH[of \<open>Prod C tC\<close> \<open>fringe (Prod C tC)\<close>] by (metis List.list.set_intros(1,2) ts_eq)+


    with frA have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = [Nt B] @ fringe (Prod C tC)\<close> by (metis the_hom_ext_hom the_hom_ext_keep_var)
    also have \<open>... = fringe (Prod A [Sym (Nt B), Prod C tC])\<close> 
      using fringe.simps(2)[of A \<open>[Sym (Nt B), Prod C tC]\<close>] 
      by auto
    also have \<open>... = fringe (Prod A ts)\<close> 
      using ts_eq prod_rhs pt by blast
    also have \<open>... = w\<close> 
      using fr unfolding ts_eq by auto
    finally have fin: \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = w\<close> .

    have \<open>parse_tree (P') (transform_tree (Prod C tC)) \<and> (A, map root ts) \<in> P\<close> 
      by (simp add: \<open>(A, prod_rhs ts) \<in> P\<close> ptC(1)) 
    moreover have \<open>root (transform_tree (Prod C tC)) = Nt C\<close> 
      apply(induction \<open>(Prod C tC)\<close> rule: transform_tree.induct) by auto
    moreover have \<open>transform_production (A, prod_rhs ts) \<in> P'\<close> 
      by (simp add: P'_def \<open>(A, prod_rhs ts) \<in> P\<close>)
    ultimately have \<open>parse_tree (P') (transform_tree (Prod A ts))\<close> 
      unfolding transf_ts ts_eq P'_def using ptC parse_tree.simps prod_rhs def by auto

    then show ?thesis using fin by blast
  next
    case Prod_Prod
    then have ts_eq: \<open>ts = [Prod B tB, Prod C tC]\<close>  and prod_rhs: \<open>prod_rhs ts = [Nt B, Nt C]\<close> by blast+
    then have transf_ts: \<open>transform_tree (Prod A ts) = (Prod A   [  Sym (Tm (Op, (A, [Nt B, Nt C]), One)),  transform_tree (Prod B tB),  Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))),  Sym (Tm (Op, (A, [Nt B, Nt C]), Two)),  transform_tree (Prod C tC),   Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))    ] )\<close> by simp

    then have frA: \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = the_hom_ext (fringe (transform_tree (Prod B tB))) @ the_hom_ext (fringe (transform_tree (Prod C tC)))\<close> by simp

    have ptB: \<open>parse_tree P (Prod B tB)\<close> using pt ts_eq by (meson List.list.set_intros(1) Parse_Tree.parse_tree.simps(2))
    then have ptB: \<open>parse_tree (P') (transform_tree (Prod B tB))\<close> \<open>the_hom_ext (fringe (transform_tree (Prod B tB))) = fringe (Prod B tB)\<close>
      using IH[of \<open>Prod B tB\<close> \<open>fringe (Prod B tB)\<close>] by (metis List.list.set_intros(1) assms(2) ts_eq)+

    have ptC: \<open>parse_tree P (Prod C tC)\<close> using pt ts_eq by (meson List.list.set_intros(1,2) Parse_Tree.parse_tree.simps(2))
    then have ptC: \<open>parse_tree (P') (transform_tree (Prod C tC))\<close> \<open>the_hom_ext (fringe (transform_tree (Prod C tC))) = fringe (Prod C tC)\<close>
      using IH[of \<open>Prod C tC\<close> \<open>fringe (Prod C tC)\<close>] by (metis List.list.set_intros(1,2) ts_eq)+


    from ptC ptB frA have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = fringe (Prod B tB) @ fringe (Prod C tC)\<close> 
      by presburger
    also have \<open>... = fringe (Prod A [Prod B tB, Prod C tC])\<close> 
      using fringe.simps(2)[of A \<open>[Prod B tB, Prod C tC]\<close>] 
      by auto
    also have \<open>... = fringe (Prod A ts)\<close> 
      using ts_eq prod_rhs pt by blast
    also have \<open>... = w\<close> 
      using fr unfolding ts_eq by auto
    finally have fin: \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = w\<close> .

    have \<open>parse_tree (P') (transform_tree (Prod B tB)) \<and> (A, map root ts) \<in> P\<close> 
      by (simp add: \<open>(A, prod_rhs ts) \<in> P\<close> ptB(1)) 
    moreover have \<open>root (transform_tree (Prod B tB)) = Nt B\<close> 
      apply(induction \<open>(Prod B tB)\<close> rule: transform_tree.induct) by auto
    moreover have \<open>transform_production (A, prod_rhs ts) \<in> P'\<close> 
      by (simp add: P'_def \<open>(A, prod_rhs ts) \<in> P\<close>)
    moreover have \<open>parse_tree (P') (transform_tree (Prod C tC)) \<and> (A, map root ts) \<in> P\<close> 
      by (simp add: \<open>(A, prod_rhs ts) \<in> P\<close> ptC(1)) 
    moreover have \<open>root (transform_tree (Prod C tC)) = Nt C\<close> 
      apply(induction \<open>(Prod C tC)\<close> rule: transform_tree.induct) by auto
    moreover have \<open>transform_production (A, prod_rhs ts) \<in> P'\<close> 
      by (simp add: P'_def \<open>(A, prod_rhs ts) \<in> P\<close>)
    ultimately have \<open>parse_tree (P') (transform_tree (Prod A ts))\<close> 
      unfolding transf_ts ts_eq P'_def using ptB parse_tree.simps prod_rhs def by auto

    then show ?thesis using fin by blast
  qed  
qed



lemma 
  transfer_parse_tree:
  assumes \<open>\<And>p. p \<in> P \<Longrightarrow> CNF_rule p\<close>
    and \<open>w \<in> Ders P S\<close>
  shows \<open>\<exists>w' \<in> Ders (transform_production ` P) S. w = the_hom_ext w'\<close>
proof-

  from assms obtain t where t_def: \<open>parse_tree P t \<and> fringe t = w \<and> root t = Nt S\<close> using parse_tree_if_derives DersD by meson
  then have root_tr: \<open>root (transform_tree t) = Nt S\<close> by blast
  from t_def have \<open>parse_tree (transform_production ` P) (transform_tree t)  \<and>  the_hom_ext (fringe (transform_tree t)) = w\<close> using transform_tree_correct assms by blast
  with root_tr have \<open>fringe (transform_tree t) \<in> Ders (transform_production ` P) S \<and> w = the_hom_ext (fringe (transform_tree t))\<close> using fringe_steps_if_parse_tree by (metis DersI)
  then show ?thesis by blast
qed















































































































(* 
text\<open>TODO: only assume Type 2 for L and finite productions somehow, then obtain a finite CNF grammar in the proof. Use (and adapt CNF_existence).\<close>
text\<open>Existence of chomsky normal form. Doesn't forbid the start symbol on the right though, so it's techinally even weaker.\<close>
lemma CNF_existence :
  assumes \<open>CFL.cfl TYPE('a) L\<close>
  shows \<open>\<exists>P S::'a. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> (* TODO start symbol not on the right side*)
  sorry

*)


section\<open>The Theorem\<close>



text\<open>The chomsky-scheutzenberger theorem that we want to prove.\<close>
lemma chomsky_schuetzenberger :
  fixes L::\<open>'t list set\<close> and  P :: \<open>('n, 't) Prods\<close>
  assumes \<open>L = Lang P S\<close> and P_CNF: \<open>(\<forall>p \<in> P. CNF_rule p)\<close> and \<open>finite P\<close> \<comment> \<open> TODO: only assume Type 2 for L and finite productions somehow, then obtain a finite CNF grammar in the proof. Use (and adapt CNF_existence).  \<close>
  \<comment> \<open>TODO2, with cnf stuff we need to wrap the proof for Languages containing \<epsilon>.\<close>
  shows \<open>\<exists>(R::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set) h \<Gamma>. (regular R) \<and> (L = image h (R \<inter> dyck_language \<Gamma>)) \<and> hom h\<close>
proof -
  (* have \<open>\<exists>P S::'n. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> using \<open>cfl TYPE('n) L\<close> CNF_existence by auto
  then obtain P and S::'n where \<open>L = Lang P S\<close> and P_CNF: \<open>(\<forall>p \<in> P. CNF_rule p)\<close> by blast *)

  define \<Gamma> where \<open>\<Gamma> = P \<times> {One, Two}\<close>
  define P' where \<open>P' = image transform_production P\<close>
  define L' where \<open>L' = Lang P' S\<close>
  define h where \<open>h = (the_hom::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list \<Rightarrow> 't list)\<close>
  define h_ext where \<open>h_ext = (the_hom_ext::('n, bracket \<times> ('n,'t) prod \<times> version ) sym list \<Rightarrow> ('n,'t) sym list)\<close>


  have \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re A)\<close> (* This is the hard part of the proof - the local lemma in the textbook *)
  proof-

    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> bal_tm x \<and> rhs_in_if x (P \<times> {One, Two})\<close> by (simp add: P'_bal P'_def P_CNF)
    then have hr1: \<open>\<And>A x. (P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<Longrightarrow> x \<in> dyck_language \<Gamma>)\<close> using \<Gamma>_def by (meson dyck_languageI_tm)


    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> x \<in> Re_sym A\<close> using P'_imp_Re using P'_def P_CNF by fastforce
    then have hr2: \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<Longrightarrow> x \<in> Re A\<close> by blast

    have rr: \<open>\<And>A x.  x \<in> (dyck_language \<Gamma>) \<inter> (Re A) \<Longrightarrow> (P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x)) \<close> using Re_imp_P' by (metis P'_def P_CNF \<Gamma>_def inf_sup_aci(1))


    show ?thesis using hr1 hr2 rr by (meson Int_iff)

  qed



  then have \<open>L' = (dyck_language \<Gamma>) \<inter> (Re S)\<close> by (metis CFL_Lang_eq_CFG_Lang CFL_Lang_if_derives L'_def derives_if_CFL_Lang inf_absorb2 inf_commute subsetI)
  then have \<open>image h ((dyck_language \<Gamma>) \<inter> (Re S)) =  image h L'\<close> by simp
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
      have \<open>\<And>w. (w \<in> Ders P S \<Longrightarrow> \<exists>w' \<in> Ders P' S. w = h_ext w')\<close> using transfer_parse_tree by (metis P'_def P_CNF h_ext_def)
      then show \<open>\<And>w. (w  \<in> Lang P S \<Longrightarrow> \<exists>w' \<in> L'. w = h w')\<close>
      proof(goal_cases)
        case (1 w)
        then have \<open>(map Tm w) \<in> Ders P S\<close> using Lang_Ders imageI by fastforce
        then obtain w' where w'_def: \<open>w' \<in> Ders P' S\<close> \<open>(map Tm w) = h_ext w'\<close> using \<open>\<And>w. w \<in> Ders P S \<Longrightarrow> \<exists>w'\<in> Ders P' S. w = h_ext w'\<close>[of \<open>map Tm w\<close>] by blast 
        moreover obtain w'' where \<open>w' = map Tm w''\<close> using w'_def by (metis h_ext_def the_hom_ext_tms_inj)
        then have \<open>w = h w''\<close> using h_eq_h_ext2 h_def h_ext_def by (metis h_eq_h_ext w'_def(2))
        moreover have \<open>w'' \<in> L'\<close> using \<open>w' \<in> Ders P' S\<close> by (metis DersD \<open>L' = dyck_language \<Gamma> \<inter> Re S\<close> \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re A)\<close> \<open>w' = map Tm w''\<close>)
        ultimately show ?case by auto
      qed
    qed
    then show \<open>Lang P S \<subseteq> h ` L'\<close> by auto 
  qed

  also have \<open>... = L\<close> by (simp add: \<open>L = Lang P S\<close>)
  finally have \<open>image h ((dyck_language \<Gamma>) \<inter> (Re S)) = L\<close> by auto

  moreover have \<open>((dyck_language \<Gamma>) \<inter> ((brackets P) \<inter> Re S)) = ((dyck_language \<Gamma>) \<inter> (Re S))\<close>
    proof
      show \<open>dyck_language \<Gamma> \<inter> ((brackets P) \<inter> Re S) \<subseteq> dyck_language \<Gamma> \<inter> Re S\<close> by blast
    next
      show \<open>dyck_language \<Gamma> \<inter> Re S \<subseteq> dyck_language \<Gamma> \<inter> ((brackets P) \<inter> Re S)\<close> using \<Gamma>_def dyck_lang_imp_star_brackets by auto
    qed
  moreover have hom: \<open>hom h\<close> by (simp add: h_def hom_def)
  moreover from \<open>finite P\<close> have \<open>regular ((brackets P) \<inter> Re S)\<close> using regular_Re_inter by fast
  ultimately have \<open>regular ((brackets P) \<inter> Re S) \<and> L = image h (((brackets P) \<inter> Re S) \<inter> (dyck_language \<Gamma>)) \<and> hom h\<close> by (simp add: inf_commute)
  then show ?thesis by blast
qed



end