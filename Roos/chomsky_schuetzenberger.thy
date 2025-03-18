theory chomsky_schuetzenberger
  imports  "../CFG" "../CFL" Chain
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
definition CNF_rule :: "('n,'t) prod \<Rightarrow> bool" where
  \<open>CNF_rule p \<equiv>  (\<exists>(A::'n) B C. (p = (A,[Nt B, Nt C]))) \<or> (\<exists>A a. p= (A, [Tm a]))\<close>


lemma transform_production_CNF: \<open>CNF_rule p \<Longrightarrow> (\<exists>A B C. transform_production p = (A, [ Tm [\<^sub>p\<^sup>1 , Nt B, Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 , Nt C, Tm ]\<^sub>p\<^sup>2   ]) \<and> p = (A, [Nt B, Nt C])) \<or> (\<exists>A a. transform_production p = (A, [ Tm [\<^sub>p\<^sup>1,       Tm ]\<^sub>p\<^sup>1 , Tm [\<^sub>p\<^sup>2 ,       Tm ]\<^sub>p\<^sup>2   ]) \<and> p = (A, [Tm a]) )\<close>
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











section\<open>Definition of the regular Language\<close>
text\<open>Defines a Predicate on neighbouring string elements - Is true iff after a Cl,p,1 there always immediately follows a Op,p,2\<close>
fun P1 :: \<open>(bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> (bracket \<times> ('n,'t) prod \<times> version) \<Rightarrow> bool\<close> where
\<open>P1 ((Cl, (p, One))) ((Op, (p', Two)))  = (p = p')\<close> | 
\<open>P1 ((Cl, (p, One))) y  = False\<close> | 
\<open>P1 x y = True\<close>

text\<open>Version of P1 for symbols, i.e. strings that may still contain Nt's\<close>
fun P1_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) sym \<Rightarrow> bool\<close> where
\<open>P1_sym (Tm (Cl, (p, One))) (Tm (Op, (p', Two)))  = (p = p')\<close> | 
\<open>P1_sym (Tm (Cl, (p, One))) y  = False\<close> | 
\<open>P1_sym x y = True\<close>

lemma P1D[dest]:
assumes \<open>P1 (Cl, (p, One)) r\<close>
shows \<open>r = (Op, (p, Two))\<close> 
using assms apply(induction \<open>(Cl, (p, One))\<close> \<open>r\<close> rule: P1.induct) by auto

lemma P1_symD[dest]:
assumes \<open>P1_sym (Tm (Cl, (p, One))) r\<close>
shows \<open>r = Tm (Op, (p, Two))\<close> 
using assms apply(induction \<open>(Tm (Cl, (p, One)))::('a, bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> version) sym\<close> \<open>r\<close> rule: P1_sym.induct) by auto

lemmas P1E = P1D[elim_format]
lemmas P1_symE = P1_symD[elim_format]


lemma P1_sym_imp_P1_for_tm[intro, dest]: \<open>chain P1_sym (map Tm x) \<Longrightarrow> chain P1 x\<close>
apply(induction x rule: induct_list012) apply simp apply simp apply(case_tac \<open>(Tm x, Tm y)\<close> rule: P1_sym.cases) by auto


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


lemma P2_sym_imp_P2_for_tm[intro, dest]: \<open>chain P2_sym (map Tm x) \<Longrightarrow> chain P2 x\<close>
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

lemma P3_sym_imp_P3_for_tm[intro, dest]: \<open>chain P3_sym (map Tm x) \<Longrightarrow> chain P3 x\<close>
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


lemma P4_sym_imp_P4_for_tm[intro, dest]: \<open>chain P4_sym (map Tm x) \<Longrightarrow> chain P4 x\<close>
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


text\<open>there exists some p, such that x ends with (Cl,p,2)\<close>
fun P6 :: \<open>(bracket \<times> ('n,'t) prod \<times> version) list \<Rightarrow> bool\<close> where
\<open>P6 [] = False\<close> | 
\<open>P6 [(b, p, v)] = (b = Cl \<and> v = Two)\<close> | 
\<open>P6 (x#y#zs) = P6 (y#zs)\<close> 

text\<open>there exists some p, such that x ends with (Cl,p,2) or it ends with some Nt X\<close>
fun P6_sym :: \<open>('n, bracket \<times> ('n,'t) prod \<times> version) syms \<Rightarrow> bool\<close> where
\<open>P6_sym [] = False\<close> | 
\<open>P6_sym [Tm (b, p, v)] = (b = Cl \<and>  v = Two)\<close> | 
\<open>P6_sym [Nt X] = True\<close> | 
\<open>P6_sym (x#y#zs) = P6_sym (y#zs)\<close> 

lemma P6D[dest]: 
assumes \<open>P6 x\<close>
shows \<open>\<exists>p. (last x = (Cl, p, Two))\<close>
using assms apply(induction x rule: P6.induct) by auto

lemma P6_symI1[intro]:
assumes \<open>w \<noteq> []\<close>
and \<open>last w = Tm (Cl, p, Two)\<close>
shows \<open>P6_sym w\<close>
proof-
from assms obtain x xs where \<open>w = xs @ [x]\<close> using rev_exhaust by blast
then have \<open>x = Tm (Cl, p, Two)\<close> using assms by (metis last_snoc)
then have \<open>P6_sym (xs@[x])\<close> 
qed

lemma P6_symD[dest]: 
assumes \<open>P6_sym x\<close>
shows \<open>(\<exists>p. last x = Tm (Cl, p, Two)) \<or> (\<exists>X. last x = Nt X)\<close>
using assms apply(induction x rule: P6_sym.induct) by auto

lemmas P6E = P6D[elim_format]
lemmas P6_symE = P6_symD[elim_format]

lemma P6_sym_imp_P6_for_tm[intro, dest]: \<open>P6_sym (map Tm x) \<Longrightarrow> P6 x\<close>
apply(induction x rule: induct_list012) by auto



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
  \<open>Re A = {x. (chain P1 x) \<and> (chain P2 x) \<and> (chain P3 x) \<and> (chain P4 x) \<and> (P5 A x) \<and> (P6 x)}\<close>

lemma ReI[intro]:
assumes \<open>(chain P1 x)\<close> and \<open>(chain P2 x)\<close> and \<open>(chain P3 x)\<close> and \<open>(chain P4 x)\<close> and \<open>(P5 A x)\<close> and \<open>(P6 x)\<close>
shows \<open>x \<in> Re A\<close>
using assms unfolding Re_def by blast

lemma ReD[dest]:
assumes \<open>x \<in> Re A\<close>
shows \<open>(chain P1 x)\<close> and \<open>(chain P2 x)\<close> and \<open>(chain P3 x)\<close> and \<open>(chain P4 x)\<close> and \<open>(P5 A x)\<close> and \<open>(P6 x)\<close>
using assms unfolding Re_def by blast+

lemmas ReE = ReD[elim_format]

text\<open>Version of Re for symbols, i.e. strings that may still contain Nt's. 
It has 2 more Properties P6 and P7 that vanish for pure terminal strings\<close>
definition Re_sym :: \<open>'n \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) syms set\<close> where
  \<open>Re_sym A = {x. (chain P1_sym x) \<and> (chain P2_sym x) \<and> (chain P3_sym x) \<and> (chain P4_sym x) \<and> (P5_sym A x) \<and> (P6_sym x) \<and> (chain P7_sym x) \<and> (chain P8_sym x)}\<close>

lemma Re_symI[intro]:
assumes \<open>chain P1_sym x\<close> and \<open>chain P2_sym x\<close> and \<open>chain P3_sym x\<close> and \<open>chain P4_sym x\<close> and \<open>P5_sym A x\<close> and \<open>P6_sym x\<close> and \<open>(chain P7_sym x)\<close> and \<open>(chain P8_sym x)\<close>
shows \<open>x \<in> Re_sym A\<close>
using assms unfolding Re_sym_def by blast

lemma Re_symD[dest]:
assumes \<open>x \<in> Re_sym A\<close>
shows \<open>chain P1_sym x\<close> and \<open>chain P2_sym x\<close> and \<open>chain P3_sym x\<close> and \<open>chain P4_sym x\<close> and \<open>P5_sym A x\<close> and \<open>P6_sym x\<close> and \<open>(chain P7_sym x)\<close> and \<open>(chain P8_sym x)\<close>
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
  term \<open>P \<times> {One, Two}\<close>
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
    have P6_uAv: \<open>P6_sym (u @ [Nt A] @ v)\<close> using Re_symD[OF uAv] by blast

    have left: \<open>chain P1_sym (u@w) \<and> chain P2_sym (u@w) \<and> chain P3_sym (u@w) \<and> chain P4_sym (u@w) \<and> chain P7_sym (u@w) \<and> chain P8_sym (u@w)\<close>
      proof(cases u rule: rev_cases)
        case Nil
        show ?thesis apply(rule disjE[OF w_eq]) unfolding Nil by auto
      next
        case (snoc ys y)
        
        then have \<open>chain P7_sym (ys @ [y] @ [Nt A] @ v)\<close> using Re_symD[OF uAv] snoc by auto
        then have \<open>P7_sym y (Nt A)\<close> by fastforce
        then obtain R X Y v' where y_eq: \<open>y = (Tm (Op,(R, [Nt X, Nt Y]), v' ))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> by blast
        then have \<open>P3_sym y (hd w)\<close> using w_eq apply(cases \<open>w = ?w1\<close>) apply(cases v') apply force apply force by (smt (verit, best) List.list.sel(1) chomsky_schuetzenberger.P3_sym.simps(1,3) chomsky_schuetzenberger.version.exhaust) 
        
        hence \<open>P1_sym (last (ys@[y])) (hd w) \<and> P2_sym (last (ys@[y])) (hd w) \<and> P3_sym (last (ys@[y])) (hd w) \<and> P4_sym (last (ys@[y])) (hd w) \<and> P7_sym (last (ys@[y])) (hd w) \<and> P8_sym (last (ys@[y])) (hd w)\<close> unfolding y_eq using w_eq by (metis List.list.sel(1) chomsky_schuetzenberger.P1_sym.simps(6) chomsky_schuetzenberger.P2_sym.simps(5) chomsky_schuetzenberger.P4_sym.simps(6) chomsky_schuetzenberger.P7_sym.simps(14) chomsky_schuetzenberger.P8_sym.simps(8) last_snoc)
        with Re_symD[OF uAv] moreover have   \<open>chain P1_sym (ys @ [y]) \<and> chain P2_sym (ys @ [y]) \<and> chain P3_sym (ys @ [y]) \<and> chain P4_sym (ys @ [y]) \<and> chain P7_sym (ys @ [y]) \<and> chain P8_sym (ys @ [y])\<close> unfolding snoc by blast
        ultimately show \<open>chain P1_sym (u@w) \<and> chain P2_sym (u@w) \<and> chain P3_sym (u@w) \<and> chain P4_sym (u@w) \<and> chain P7_sym (u@w) \<and> chain P8_sym (u@w)\<close> unfolding snoc using chain_append[where ?xs = \<open>ys @ [y]\<close> and ?ys = w] Re_symD[OF w_resym] by blast
      qed


      have right: \<open>chain P1_sym (w@v) \<and> chain P2_sym (w@v) \<and> chain P3_sym (w@v) \<and> chain P4_sym (w@v) \<and> chain P7_sym (w@v) \<and> chain P8_sym (w@v)\<close>
      proof(cases v)
        case Nil
        show ?thesis apply(rule disjE[OF w_eq]) unfolding Nil by auto
      next
        case (Cons y ys)
        then have \<open>chain P8_sym ([Nt A] @ y # ys)\<close> using Re_symD[OF uAv] Cons by blast
        then have \<open>P8_sym (Nt A) y\<close> by fastforce
        then obtain R X Y v' where y_eq: \<open>y = (Tm (Cl,(R, [Nt X, Nt Y]), v' ))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> by blast
        have \<open>P1_sym (last w) (hd (y#ys)) \<and> P2_sym (last w) (hd (y#ys)) \<and> P3_sym (last w) (hd (y#ys)) \<and> P4_sym (last w) (hd (y#ys)) \<and> P7_sym (last w) (hd (y#ys)) \<and> P8_sym (last w) (hd (y#ys))\<close> unfolding y_eq using w_eq apply(cases \<open>w = ?w1\<close>) apply force by simp
        with Re_symD[OF uAv] moreover have \<open>chain P1_sym (y # ys) \<and> chain P2_sym (y # ys) \<and> chain P3_sym (y # ys) \<and> chain P4_sym (y # ys) \<and> chain P7_sym (y # ys) \<and> chain P8_sym (y # ys)\<close> unfolding Cons by blast
        ultimately show \<open>chain P1_sym (w@v) \<and> chain P2_sym (w@v) \<and> chain P3_sym (w@v) \<and> chain P4_sym (w@v) \<and> chain P7_sym (w@v) \<and> chain P8_sym (w@v)\<close> unfolding Cons using chain_append[where ?xs = \<open>w\<close> and ?ys = \<open>y#ys\<close>] Re_symD[OF w_resym] by blast
      qed


      from left right have \<open>chain P1_sym (u@w@v) \<and> chain P2_sym (u@w@v) \<and> chain P3_sym (u@w@v) \<and> chain P4_sym (u@w@v) \<and> chain P7_sym (u@w@v) \<and> chain P8_sym (u@w@v)\<close> using w_eq by blast

      moreover have \<open>P5_sym S (u@w@v)\<close> apply(rule disjE[OF w_eq]; cases u) 
        using P5_uAv apply force
        using P5_uAv apply (metis List.list.sel(1) P5_symD append_Cons chomsky_schuetzenberger.P5_sym.simps(2,3))
        using P5_uAv apply force 
        using P5_uAv by (metis List.list.sel(1) P5_symD append_Cons chomsky_schuetzenberger.P5_sym.simps(2,3))

      moreover have \<open>P6_sym (u@w@v)\<close> apply(rule disjE[OF w_eq]; cases v) using P6_uAv 

 

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

  have p1x: \<open>chain P1 x\<close> and p2x: \<open>chain P2 x\<close> and p3x: \<open>chain P3 x\<close> and p4x: \<open>chain P4 x\<close> and p5x: \<open>P5 A x\<close> using ReD[OF xRe] by blast+
  
  from p5x obtain \<pi> t where hd_x: \<open>hd x = (Op, \<pi>, One)\<close>  and pi_def: \<open>\<pi> = (A, t)\<close> by (metis List.list.sel(1) P5.elims(2))
  with xRe have \<open>(Op, \<pi>, One) \<in> set x\<close> by (metis List.list.sel(1) List.list.set_intros(1) ReD(5) chomsky_schuetzenberger.P5.elims(2))
  then have pi_in_P: \<open>\<pi> \<in> P\<close> using xDL by auto

  have bal_x: \<open>bal x\<close> using xDL by blast
  then have \<open>\<exists>y r. bal y \<and> bal r \<and> [\<^bsub>\<pi>\<^esub>\<^sup>1  # tl x = [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # r\<close> using hd_x bal_x bal_Op_split[of \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1 \<close>, where ?xs = \<open>tl x\<close>]  by (metis (no_types, lifting) List.list.exhaust_sel List.list.inject Product_Type.prod.inject chomsky_schuetzenberger.P5.simps(1) p5x)

  then obtain y r1 where \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1  # tl x   =   [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # r1\<close> and bal_y: \<open>bal y\<close> and bal_r1: \<open>bal r1\<close> by blast
  then have split1: \<open>x = [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # r1\<close> using hd_x by (metis List.list.exhaust_sel List.list.set(1) \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1 \<in> set x\<close> empty_iff)
  have r1_not_empty: \<open>r1 \<noteq> []\<close> 
  proof(rule ccontr)
  assume \<open>r1 = []\<close>
  then have \<open>last x = ]\<^bsub>\<pi>\<^esub>\<^sup>1 \<close> using split1 by (metis List.list.distinct(1) Nil_is_append_conv last_ConsR last_snoc)
  then have \<open>last (map Tm x) = Tm ]\<^bsub>\<pi>\<^esub>\<^sup>1\<close> by (metis List.list.discI last_map split1)

  then have \<open>False\<close> using P'_imp_last_not_Cl_1[of P A \<open>map Tm x\<close> \<open>\<pi>\<close>] 

  qed
  
  apply(rule ccontr) using P'_imp_last_not_Cl_1[of P A \<open>map Tm x\<close>] unfolding split1 
  
   \<comment> \<open>prove that no P' string stops with Cl pi 1\<close>
  from p1x have hd_r1: \<open>hd r1 = [\<^bsub>\<pi>\<^esub>\<^sup>2\<close> using split1 r1_not_empty chainE_hd[of P1 \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1  # y\<close> \<open>]\<^bsub>\<pi>\<^esub>\<^sup>1\<close> r1 \<open>[]\<close>] by (smt (z3) Cons_eq_appendI Product_Type.prod.inject chomsky_schuetzenberger.P1.elims(1) chomsky_schuetzenberger.P1.simps(1,3) chomsky_schuetzenberger.bracket.distinct(1) self_append_conv)
  
  from bal_r1 have \<open>\<exists>z r2. bal z \<and> bal r2 \<and> [\<^bsub>\<pi>\<^esub>\<^sup>2 # tl r1 = [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ ]\<^bsub>\<pi>\<^esub>\<^sup>2  # r2\<close> using bal_Op_split[of \<open>[\<^bsub>\<pi>\<^esub>\<^sup>2\<close> \<open>tl r1\<close>] by (metis List.list.exhaust_sel List.list.sel(1) Product_Type.prod.inject hd_r1 r1_not_empty) 

  then obtain z r2 where split2': \<open>[\<^bsub>\<pi>\<^esub>\<^sup>2 # tl r1   =   [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ ]\<^bsub>\<pi>\<^esub>\<^sup>2  # r2\<close> and bal_z: \<open>bal z\<close> and bal_r2: \<open>bal r2\<close> by blast+

  then have split2: \<open>x  =   [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ ]\<^bsub>\<pi>\<^esub>\<^sup>2  # r2\<close> by (metis List.list.exhaust_sel hd_r1 r1_not_empty split1)

  have r2_empty: \<open>r2 = []\<close>  \<comment> \<open>prove that if r2 notempty, it would need to start with an open bracket, else it cant be balanced. But this cant be with P2.\<close>
  proof(cases r2)
    case (Cons r2' r2's)
    from bal_r2 obtain g where r2_begin_op: \<open>r2 = (Op, g) # r2's\<close> using bal_not_empty[of r2' r2's] using Cons by blast
    have \<open>P2 ]\<^bsub>\<pi>\<^esub>\<^sup>2 (hd r2)\<close> using Cons split2 by (metis Chain.chain.simps(3) List.list.sel(1) chain_drop_left chain_drop_left_cons p2x)
    with r2_begin_op have \<open>False\<close> by (metis List.list.sel(1) chomsky_schuetzenberger.P2.simps(1) split_pairs)
    then show ?thesis by blast
  qed blast

  then have split3: \<open>x  =   [\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close> using split2 by blast

  consider (BC) \<open>\<exists>B C. \<pi> = (A, [Nt B, Nt C])\<close> | (a) \<open>\<exists>a. \<pi> = (A, [Tm a])\<close> using assms pi_in_P by (metis CNF_rule_def fst_conv pi_def)
  then show \<open>transform_production ` P \<turnstile> [Nt A] \<Rightarrow>* map Tm x\<close>
  proof(cases)
    case BC
    then obtain B C where pi_eq: \<open>\<pi> = (A, [Nt B, Nt C])\<close> by blast

    from split3 have y_chains: \<open>chain P1 y \<and> chain P2 y \<and> chain P3 y \<and> chain P4 y\<close> by (metis chain_drop_left_cons chain_drop_right p1x p2x p3x p4x)
    have \<open>y \<noteq> []\<close> using p3x pi_eq split1 by fastforce
    with p3x pi_eq have \<open>\<exists>g. hd y = (Op, (B,g), One)\<close> using split3 chainE_hd[of P3, where ?x = \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1\<close> and ?y = y and ?xs = \<open>[]\<close> and ?ys = \<open>]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close>] by (metis append_Nil P3.simps(1) split_pairs)
    then have \<open>P5 B y\<close> by (metis \<open>y \<noteq> []\<close> chomsky_schuetzenberger.P5.simps(2) hd_Cons_tl)

    with y_chains have \<open>y \<in> Re B\<close> by blast
    moreover have \<open>y \<in> dyck_language (P \<times> {One, Two})\<close> using split3 bal_y dyck_language_substring by (metis append_Cons append_Nil hd_x split1 xDL)
    ultimately have \<open>y \<in> Re B \<inter> dyck_language (P \<times> {One, Two})\<close> by force

    moreover have \<open>length (map Tm y) < length (map Tm x)\<close> using length_append length_map lessI split3 by fastforce
    ultimately have der_y: \<open>transform_production ` P \<turnstile> [Nt B] \<Rightarrow>* map Tm y\<close> using IH[of y B] split3  by blast


    

    from split3 have z_chains: \<open>chain P1 z \<and> chain P2 z \<and> chain P3 z \<and> chain P4 z\<close> by (metis chain_drop_left chain_drop_left_cons chain_drop_right p1x p2x p3x p4x)
    then have chain_P3: \<open>chain P3 (([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>1]) @ [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>2 ])\<close> using split3 p3x by (metis List.append.assoc append_Cons append_Nil)

    have \<open>z \<noteq> []\<close> using p3x pi_eq split1 by (metis Chain.chain.simps(3) append_self_conv2 chain_drop_left chain_drop_left_cons P3.simps(2) version.distinct(1) hd_Cons_tl hd_r1 r1_not_empty split2')
    then have \<open>P3 [\<^bsub>\<pi>\<^esub>\<^sup>2 (hd z)\<close> using chainE_hd[OF chain_P3 \<open>z\<noteq>[]\<close>] by blast
    with p3x pi_eq have \<open>\<exists>g. hd z = (Op, (C,g), One)\<close> using split_pairs by (metis chomsky_schuetzenberger.P3.simps(2))
    then have \<open>P5 C z\<close> by (metis List.list.exhaust_sel \<open>z \<noteq> []\<close> chomsky_schuetzenberger.P5.simps(2)) 

    with z_chains have \<open>z \<in> Re C\<close> by blast
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
      have \<open>P4 [\<^bsub>\<pi>\<^esub>\<^sup>1 y'\<close> by (metis Chain.chain.simps(3) Cons append_Cons p4x split3)
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











































































section\<open>The Theorem\<close>



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

  term P
  have \<open>L' \<subseteq> dyck_language \<Gamma>\<close> sorry (* This might not be needed (but it was listed in the book). Leave this for last *)

  have \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re A)\<close> (* This is the hard part of the proof - the local lemma in the textbook *)
  proof-

    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> bal_tm x \<and> rhs_in_if x (P \<times> {One, Two})\<close> by (simp add: P'_bal P'_def P_CNF)
    then have \<open>\<And>A x. (P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<Longrightarrow> x \<in> dyck_language \<Gamma>)\<close> using \<Gamma>_def by auto

    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> x \<in> Re_sym A\<close> using P'_imp_Re using P'_def P_CNF by fastforce
    then have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<Longrightarrow> x \<in> Re A\<close> by blast




    show ?thesis sorry
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

            text\<open>now we have to find the right prefix\<close>
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
        moreover have \<open>w'' \<in> L'\<close> using \<open>w' \<in> Ders P' S\<close> by (metis DersD \<open>L' = dyck_language \<Gamma> \<inter> Re S\<close> \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re A)\<close> \<open>w' = map Tm w''\<close>)
        ultimately show ?case by auto
      qed
    qed
    then show \<open>Lang P S \<subseteq> h ` L'\<close> by auto 
  qed

  also have \<open>... = L\<close> by (simp add: \<open>L = Lang P S\<close>)
  finally have \<open>image h ((dyck_language \<Gamma>) \<inter> (Re S)) = L\<close> by auto

  moreover have hom: \<open>hom h\<close> by (simp add: h_def hom_def)
  moreover have \<open>reg TYPE('n) (Re S)\<close> sorry
  ultimately have \<open>reg TYPE('n) (Re S) \<and> L = image h ((Re S) \<inter> (dyck_language \<Gamma>)) \<and> hom h\<close> by blast 
  then show ?thesis by blast

qed



end