theory chomsky_schuetzenberger
  imports  "../CFG" "../CFL" "../Parse_Tree" Chain "$AFP/Regular-Sets/Regexp_Constructions" "$AFP/Regular-Sets/Regular_Set"
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









section\<open>Regexp stuff TODO mv?\<close>

lemma regular_lang_Union:
  assumes "finite LS" 
  assumes "\<forall>L\<in>LS. regular_lang L"
  shows "regular_lang (\<Union>LS)"
using assms proof (induct LS rule: finite_induct)
  case empty
  show ?case apply auto using Regular_Exp.lang.simps(1) by blast
next
  case (insert L LS)
  have eq: "\<Union>(insert L LS) = L \<union> (\<Union>LS)"
    by auto
  moreover have "regular_lang L" 
    using insert.prems by simp
  moreover have "regular_lang (\<Union>LS)" 
    using insert by blast
  ultimately have \<open>regular_lang (L \<union> (\<Union>LS))\<close> using Regular_Exp.lang.simps(4) by metis
  then show ?case unfolding eq by simp
qed


lemma \<open>finite L \<Longrightarrow> regular_lang L\<close>
proof-
assume \<open>finite L\<close>
have eq: \<open>L = \<Union>{ {a} | a. a \<in> L}\<close> by blast
from \<open>finite L\<close> have \<open>finite { {a} | a. a \<in> L}\<close> by auto
moreover have \<open>\<forall>k \<in> { {a} | a. a \<in> L}. (regular_lang k)\<close>  using lang_rexp_of_word by blast
ultimately have \<open>regular_lang (\<Union>{ {a} | a. a \<in> L})\<close> using regular_lang_Union by blast
then show ?thesis using eq by simp
qed















text\<open>All brackets in P\<close>
definition brackets::\<open>('n,'t) Prods \<Rightarrow> (bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set\<close> where
\<open>brackets P = { [(br,(p,v))] |br p v. p \<in> P}\<close>


lemma dyck_lang_imp_star_brackets: \<open>dyck_language (P \<times> {One, Two}) \<subseteq> star (brackets P)\<close>
proof
fix x
assume \<open>x \<in> dyck_language (P \<times> {One, Two})\<close>

then show \<open>x \<in> star (brackets P)\<close> unfolding dyck_language_def brackets_def sorry
qed



text\<open>All closing brackets, not neccesarily in P\<close>
definition CL::\<open>(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set\<close> where
\<open>CL = { [(Cl,(p,v))] | p v. True }\<close>

text\<open>All opening brackets, not neccesarily in P\<close>
definition OP::\<open>(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set\<close> where
\<open>OP = { [(Op,(p,v))] | p v. True }\<close>

text\<open>All closing brackets with a 2, not neccesarily in P\<close>
definition CL2::\<open>(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set\<close> where
\<open>CL2 = { [(Cl,(p,Two))] | p. True }\<close>

text\<open>All closing brackets with a 2, not neccesarily in P\<close>
definition nCL2::\<open>(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> version) list set\<close> where
\<open>nCL2 = UNIV - { [(Cl,(p,Two))] | p. True }\<close>



lemma Pbrackets_finite[intro, simp]:
assumes \<open>finite P\<close>
shows \<open>finite (brackets P)\<close>
proof -
  have "brackets P = { [(br, (p, v))] | br p v. p \<in> P}"
    by (simp add: brackets_def)
  also have "... = (\<Union>p\<in>P. { [(br, (p, v))] | br v. True})"
    by blast
  also have "finite ..." using assms 
  proof -
    have "\<forall>p\<in>P. finite { [((br::bracket), (p, (v::version)))] | br v. True}"
    proof
      fix p assume "p \<in> P"
      have eq: \<open>{ [(br, (p, v))] | br v. True} = { [(Op, (p, One))], [(Op, (p, Two))], [(Cl, (p, One))], [(Cl, (p, Two))]}\<close> using bracket.exhaust version.exhaust by auto
      have \<open>finite ...\<close> by blast
      then show "finite { [((br::bracket), (p, (v::version)))] | br v. True}" using eq by auto
    qed
    
    with assms show ?thesis using finite_UN by blast
  qed
  finally show "finite (brackets P)" .
qed























































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





text\<open>Existence of chomsky normal form. Doesn't forbid the start symbol on the right though, so it's techinally even weaker.\<close>
lemma CNF_existence :
  assumes \<open>CFL.cfl TYPE('a) L\<close>
  shows \<open>\<exists>P S::'a. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> (* TODO start symbol not on the right side*)
  sorry
















































































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
\<open>P1 xs = ((chain P1' xs) \<and> (if xs \<noteq> [] then (\<nexists>p. last xs = (Cl, (p, One))) else True))\<close>

text\<open>Asserts that P1' holds for every pair in xs, and that xs doesnt end in Tm (Cl, p, 1)\<close>
fun P1_sym where
\<open>P1_sym xs = ((chain P1'_sym xs) \<and> (if xs \<noteq> [] then (\<nexists>p. last xs = Tm (Cl, (p, One))) else True))\<close>


lemma P1_sym_imp_P1_for_tm[intro, dest]: \<open>P1_sym (map Tm x) \<Longrightarrow> P1 x\<close>
apply(induction x rule: induct_list012) defer defer apply simp apply(case_tac \<open>(Tm x, Tm y)\<close> rule: P1'_sym.cases) by auto

lemma P1I[intro]: 
assumes \<open>chain P1' xs\<close>
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
assumes \<open>chain P1'_sym xs\<close>
and \<open>\<nexists>p. last xs = Tm (Cl, (p, One))\<close>
shows \<open>P1_sym xs\<close> apply(cases xs rule: rev_cases) defer apply(case_tac y) using assms by auto


lemma P1D[dest]: \<open>P1 xs \<Longrightarrow> chain P1' xs\<close> by simp

lemma P1_symD[dest]: \<open>P1_sym xs \<Longrightarrow> chain P1'_sym xs\<close> by simp

lemma P1D_not_empty[dest]:
assumes \<open>xs \<noteq> []\<close>
and \<open>P1 xs\<close>
shows \<open>last xs \<noteq> (Cl, p, One)\<close>
proof-
obtain x xs' where x_eq: \<open>xs = x# xs'\<close> using assms using List.list.exhaust_sel by blast
with assms have \<open>chain P1' xs\<close> \<open>\<nexists>p. last xs = (Cl, (p, One))\<close> using P1.simps apply blast using P1.simps by (metis assms(1,2))
then show ?thesis by blast
qed

lemma P1_symD_not_empty'[dest]:
assumes \<open>xs \<noteq> []\<close>
and \<open>P1_sym xs\<close>
shows \<open>last xs \<noteq> Tm (Cl, p, One)\<close>
proof-
obtain x xs' where x_eq: \<open>xs = x# xs'\<close> using assms using List.list.exhaust_sel by blast
with assms have \<open>chain P1'_sym xs\<close> \<open>\<nexists>p. last xs = Tm (Cl, (p, One))\<close> using P1_sym.simps apply blast using P1.simps x_eq by (metis assms(1,2) chomsky_schuetzenberger.P1_sym.elims(2))
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
  \<open>Re A = {x. (P1 x) \<and> (chain P2 x) \<and> (chain P3 x) \<and> (chain P4 x) \<and> (P5 A x)}\<close>

lemma ReI[intro]:
assumes \<open>(P1 x)\<close> and \<open>(chain P2 x)\<close> and \<open>(chain P3 x)\<close> and \<open>(chain P4 x)\<close> and \<open>(P5 A x)\<close>
shows \<open>x \<in> Re A\<close>
using assms unfolding Re_def by blast

lemma ReD[dest]:
assumes \<open>x \<in> Re A\<close>
shows \<open>(P1 x)\<close> and \<open>(chain P2 x)\<close> and \<open>(chain P3 x)\<close> and \<open>(chain P4 x)\<close> and \<open>(P5 A x)\<close>
using assms unfolding Re_def by blast+

lemmas ReE = ReD[elim_format]

text\<open>Version of Re for symbols, i.e. strings that may still contain Nt's. 
It has 2 more Properties P6 and P7 that vanish for pure terminal strings\<close>
definition Re_sym :: \<open>'n \<Rightarrow> ('n, bracket \<times> ('n,'t) prod \<times> version) syms set\<close> where
  \<open>Re_sym A = {x. (P1_sym x) \<and> (chain P2_sym x) \<and> (chain P3_sym x) \<and> (chain P4_sym x) \<and> (P5_sym A x) \<and> (chain P7_sym x) \<and> (chain P8_sym x)}\<close>

lemma Re_symI[intro]:
assumes \<open>P1_sym x\<close> and \<open>chain P2_sym x\<close> and \<open>chain P3_sym x\<close> and \<open>chain P4_sym x\<close> and \<open>P5_sym A x\<close> and \<open>(chain P7_sym x)\<close> and \<open>(chain P8_sym x)\<close>
shows \<open>x \<in> Re_sym A\<close>
using assms unfolding Re_sym_def by blast

lemma Re_symD[dest]:
assumes \<open>x \<in> Re_sym A\<close>
shows \<open>P1_sym x\<close> and \<open>chain P2_sym x\<close> and \<open>chain P3_sym x\<close> and \<open>chain P4_sym x\<close> and \<open>P5_sym A x\<close> and \<open>(chain P7_sym x)\<close> and \<open>(chain P8_sym x)\<close>
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
    have P1_uAv: \<open>P1_sym (u @ [Nt A] @ v)\<close> using Re_symD[OF uAv] by blast

    have left: \<open>chain P1'_sym (u@w) \<and> chain P2_sym (u@w) \<and> chain P3_sym (u@w) \<and> chain P4_sym (u@w) \<and> chain P7_sym (u@w) \<and> chain P8_sym (u@w)\<close>
      proof(cases u rule: rev_cases)
        case Nil
        show ?thesis apply(rule disjE[OF w_eq]) unfolding Nil by auto
      next
        case (snoc ys y)
        
        then have \<open>chain P7_sym (ys @ [y] @ [Nt A] @ v)\<close> using Re_symD[OF uAv] snoc by auto
        then have \<open>P7_sym y (Nt A)\<close> by fastforce
        then obtain R X Y v' where y_eq: \<open>y = (Tm (Op,(R, [Nt X, Nt Y]), v' ))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> by blast
        then have \<open>P3_sym y (hd w)\<close> using w_eq apply(cases \<open>w = ?w1\<close>) apply(cases v') apply force apply force by (smt (verit, best) List.list.sel(1) chomsky_schuetzenberger.P3_sym.simps(1,3) chomsky_schuetzenberger.version.exhaust) 
        
        hence \<open>P1'_sym (last (ys@[y])) (hd w) \<and> P2_sym (last (ys@[y])) (hd w) \<and> P3_sym (last (ys@[y])) (hd w) \<and> P4_sym (last (ys@[y])) (hd w) \<and> P7_sym (last (ys@[y])) (hd w) \<and> P8_sym (last (ys@[y])) (hd w)\<close> unfolding y_eq using w_eq apply(cases \<open>w = ?w1\<close>) apply force by simp
        with Re_symD[OF uAv] moreover have   \<open>chain P1'_sym (ys @ [y]) \<and> chain P2_sym (ys @ [y]) \<and> chain P3_sym (ys @ [y]) \<and> chain P4_sym (ys @ [y]) \<and> chain P7_sym (ys @ [y]) \<and> chain P8_sym (ys @ [y])\<close> unfolding snoc by blast
        ultimately show \<open>chain P1'_sym (u@w) \<and>chain P2_sym (u@w) \<and> chain P3_sym (u@w) \<and> chain P4_sym (u@w) \<and> chain P7_sym (u@w) \<and> chain P8_sym (u@w)\<close> unfolding snoc using chain_append[where ?xs = \<open>ys @ [y]\<close> and ?ys = w] Re_symD[OF w_resym] by blast
      qed


      have right: \<open>chain P1'_sym (w@v) \<and> chain P2_sym (w@v) \<and> chain P3_sym (w@v) \<and> chain P4_sym (w@v) \<and> chain P7_sym (w@v) \<and> chain P8_sym (w@v)\<close>
      proof(cases v)
        case Nil
        show ?thesis apply(rule disjE[OF w_eq]) unfolding Nil by auto
      next
        case (Cons y ys)
        then have \<open>chain P8_sym ([Nt A] @ y # ys)\<close> using Re_symD[OF uAv] Cons by blast
        then have \<open>P8_sym (Nt A) y\<close> by fastforce
        then obtain R X Y v' where y_eq: \<open>y = (Tm (Cl,(R, [Nt X, Nt Y]), v' ))\<close> and \<open>v' = One \<Longrightarrow> A = X\<close> and \<open>v' = Two \<Longrightarrow> A = Y\<close> by blast
        have \<open>P1'_sym (last w) (hd (y#ys)) \<and> P2_sym (last w) (hd (y#ys)) \<and> P3_sym (last w) (hd (y#ys)) \<and> P4_sym (last w) (hd (y#ys)) \<and> P7_sym (last w) (hd (y#ys)) \<and> P8_sym (last w) (hd (y#ys))\<close> unfolding y_eq using w_eq apply(cases \<open>w = ?w1\<close>) apply force by simp
        with Re_symD[OF uAv] moreover have \<open>chain P1'_sym (y # ys) \<and> chain P2_sym (y # ys) \<and> chain P3_sym (y # ys) \<and> chain P4_sym (y # ys) \<and> chain P7_sym (y # ys) \<and> chain P8_sym (y # ys)\<close> unfolding Cons by blast
        ultimately show \<open>chain P1'_sym (w@v) \<and> chain P2_sym (w@v) \<and> chain P3_sym (w@v) \<and> chain P4_sym (w@v) \<and> chain P7_sym (w@v) \<and> chain P8_sym (w@v)\<close> unfolding Cons using chain_append[where ?xs = \<open>w\<close> and ?ys = \<open>y#ys\<close>] Re_symD[OF w_resym] by blast
      qed

      from left right have P1_uwv: \<open>chain P1'_sym (u@w@v)\<close> using w_eq by blast
      from left right have ch: \<open>chain P2_sym (u@w@v) \<and> chain P3_sym (u@w@v) \<and> chain P4_sym (u@w@v) \<and> chain P7_sym (u@w@v) \<and> chain P8_sym (u@w@v)\<close> using w_eq by blast

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

  have p1x: \<open>P1 x\<close> and p2x: \<open>chain P2 x\<close> and p3x: \<open>chain P3 x\<close> and p4x: \<open>chain P4 x\<close> and p5x: \<open>P5 A x\<close> using ReD[OF xRe] by blast+
  
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

  from p1x have hd_r1: \<open>hd r1 = [\<^bsub>\<pi>\<^esub>\<^sup>2\<close> using split1 r1_not_empty chainE_hd[of P1' \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1  # y\<close> \<open>]\<^bsub>\<pi>\<^esub>\<^sup>1\<close> r1 \<open>[]\<close>] by (metis Cons_eq_appendI P1'D P1D self_append_conv)

  
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

    from split3 have y_chains: \<open>chain P1' y \<and> chain P2 y \<and> chain P3 y \<and> chain P4 y\<close> by (metis chain_drop_left_cons chain_drop_right P1.simps p1x p2x p3x p4x)
    have y_not_empty: \<open>y \<noteq> []\<close> using p3x pi_eq split1 by fastforce
    have \<open>\<nexists>p. last y = (Cl, (p, One))\<close>
    proof(rule ccontr)
      assume \<open>\<not> (\<nexists>p. last y = ]\<^bsub>p\<^esub>\<^sup>1)\<close>
      then obtain p where last_y: \<open>last y = ]\<^bsub>p\<^esub>\<^sup>1 \<close> by blast
      obtain butl where butl_def: \<open>y = butl @ [last y]\<close> by (metis append_butlast_last_id y_not_empty)

      have  \<open>chain P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using p1x split3 by blast 
      then have \<open>chain P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # (butl@[last y]) @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using butl_def by simp
      then have \<open>chain P1' (([\<^bsub>\<pi>\<^esub>\<^sup>1  # butl) @ last y # [ ]\<^bsub>\<pi>\<^esub>\<^sup>1] @ [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>2 ])\<close> by (metis (no_types, opaque_lifting) Cons_eq_appendI append_assoc append_self_conv2) 
      then have \<open>P1' ]\<^bsub>p\<^esub>\<^sup>1  ]\<^bsub>\<pi>\<^esub>\<^sup>1 \<close> using chainE[of P1' \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1  # butl\<close> \<open>last y\<close> \<open>]\<^bsub>\<pi>\<^esub>\<^sup>1\<close> \<open>[\<^bsub>\<pi>\<^esub>\<^sup>2  # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close>] using last_y by force 

      then show \<open>False\<close> by simp
      qed

    with y_chains have P1y: \<open>P1 y\<close> by blast

    with p3x pi_eq have \<open>\<exists>g. hd y = (Op, (B,g), One)\<close> using y_not_empty split3 chainE_hd[of P3, where ?x = \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1\<close> and ?y = y and ?xs = \<open>[]\<close> and ?ys = \<open>]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ]\<close>] by (metis append_Nil P3.simps(1) split_pairs)
    then have \<open>P5 B y\<close> by (metis \<open>y \<noteq> []\<close> chomsky_schuetzenberger.P5.simps(2) hd_Cons_tl)


    with y_chains P1y have \<open>y \<in> Re B\<close> by blast
    moreover have \<open>y \<in> dyck_language (P \<times> {One, Two})\<close> using split3 bal_y dyck_language_substring by (metis append_Cons append_Nil hd_x split1 xDL)
    ultimately have \<open>y \<in> Re B \<inter> dyck_language (P \<times> {One, Two})\<close> by force

    moreover have \<open>length (map Tm y) < length (map Tm x)\<close> using length_append length_map lessI split3 by fastforce
    ultimately have der_y: \<open>transform_production ` P \<turnstile> [Nt B] \<Rightarrow>* map Tm y\<close> using IH[of y B] split3  by blast


    

    from split3 have z_chains: \<open>chain P1' z \<and> chain P2 z \<and> chain P3 z \<and> chain P4 z\<close> by (metis chain_drop_left chain_drop_left_cons chain_drop_right p1x p2x p3x p4x P1.simps)
    then have chain_P3: \<open>chain P3 (([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>1]) @ [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @ [ ]\<^bsub>\<pi>\<^esub>\<^sup>2 ])\<close> using split3 p3x by (metis List.append.assoc append_Cons append_Nil)

    have z_not_empty: \<open>z \<noteq> []\<close> using p3x pi_eq split1 by (metis Chain.chain.simps(3) append_self_conv2 chain_drop_left chain_drop_left_cons P3.simps(2) version.distinct(1) hd_Cons_tl hd_r1 r1_not_empty split2')
    then have \<open>P3 [\<^bsub>\<pi>\<^esub>\<^sup>2 (hd z)\<close> using chainE_hd[OF chain_P3 \<open>z\<noteq>[]\<close>] by blast
    with p3x pi_eq have \<open>\<exists>g. hd z = (Op, (C,g), One)\<close> using split_pairs by (metis chomsky_schuetzenberger.P3.simps(2))
    then have \<open>P5 C z\<close> by (metis List.list.exhaust_sel \<open>z \<noteq> []\<close> chomsky_schuetzenberger.P5.simps(2)) 
    moreover have \<open>P1 z\<close>
      proof-
        have \<open>\<nexists>p. last z = ]\<^bsub>p\<^esub>\<^sup>1\<close> 
        proof(rule ccontr)
          assume \<open>\<not> (\<nexists>p. last z = ]\<^bsub>p\<^esub>\<^sup>1)\<close>
          then obtain p where last_y: \<open>last z = ]\<^bsub>p\<^esub>\<^sup>1 \<close> by blast
          obtain butl where butl_def: \<open>z = butl @ [last z]\<close> by (metis append_butlast_last_id z_not_empty)

          have  \<open>chain P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # z @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using p1x split3 by blast 
          then have \<open>chain P1' ([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # butl @ [last z] @[   ]\<^bsub>\<pi>\<^esub>\<^sup>2   ])\<close> using butl_def by (metis append_assoc)
          then have \<open>chain P1' (([\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1 # [\<^bsub>\<pi>\<^esub>\<^sup>2 # butl) @ last z # [ ]\<^bsub>\<pi>\<^esub>\<^sup>2 ] @ [])\<close> by (metis (no_types, opaque_lifting) Cons_eq_appendI append_assoc append_self_conv2) 
          then have \<open>P1' ]\<^bsub>p\<^esub>\<^sup>1  ]\<^bsub>\<pi>\<^esub>\<^sup>2 \<close> using chainE[of P1' \<open>[\<^bsub>\<pi>\<^esub>\<^sup>1  # y @ ]\<^bsub>\<pi>\<^esub>\<^sup>1  # [\<^bsub>\<pi>\<^esub>\<^sup>2 # butl\<close> \<open>last z\<close> \<open>]\<^bsub>\<pi>\<^esub>\<^sup>2\<close> \<open>[]\<close>] using last_y by force 

          then show \<open>False\<close> by simp
        qed
        then show \<open>P1 z\<close> using z_chains by blast
        qed



    ultimately have \<open>z \<in> Re C\<close> using z_chains by blast
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
defines \<open>P' == transform_production ` P\<close>
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

    moreover have \<open>parse_tree (P') (transform_tree (Prod A [Sym (Tm a)]))\<close> using pt prod_rhs unfolding P'_def by force 
    ultimately show ?thesis unfolding ts_eq P'_def by blast
  next
    case Nt_Nt
    then have ts_eq: \<open>ts = [Sym (Nt B), Sym (Nt C)]\<close>  and prod_rhs: \<open>prod_rhs ts = [Nt B, Nt C]\<close> by blast+
    then have \<open>transform_tree (Prod A ts) = (Prod A [Sym (Tm (Op, (A, [Nt B, Nt C]), One)), Sym (Nt B), Sym (Tm (Cl, ((A, [Nt B, Nt C]), One))), Sym (Tm (Op, (A, [Nt B, Nt C]), Two)), Sym (Nt C), Sym (Tm (Cl, (A, [Nt B, Nt C]), Two))  ])\<close> by simp
    then have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = [ Nt B, Nt C  ]\<close> by simp
    also have \<open>... = w\<close> using fr unfolding ts_eq by auto
    finally have \<open>the_hom_ext (fringe (transform_tree (Prod A ts))) = w\<close> .

    moreover have \<open>parse_tree (P') (transform_tree (Prod A [Sym (Nt B), Sym (Nt C)]))\<close> using pt prod_rhs unfolding P'_def by force
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


  have \<open>\<forall>A. \<forall>x. P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language \<Gamma>) \<inter> (Re A)\<close> (* This is the hard part of the proof - the local lemma in the textbook *)
  proof-

    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> bal_tm x \<and> rhs_in_if x (P \<times> {One, Two})\<close> by (simp add: P'_bal P'_def P_CNF)
    then have hr1: \<open>\<And>A x. (P' \<turnstile> [Nt A] \<Rightarrow>* (map Tm x) \<Longrightarrow> x \<in> dyck_language \<Gamma>)\<close> using \<Gamma>_def by auto

    have \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* x \<Longrightarrow> x \<in> Re_sym A\<close> using P'_imp_Re using P'_def P_CNF by fastforce
    then have hr2: \<open>\<And>A x.  P' \<turnstile> [Nt A] \<Rightarrow>* map Tm x \<Longrightarrow> x \<in> Re A\<close> by blast
    
    thm Re_imp_P'
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

  moreover have \<open>((dyck_language \<Gamma>) \<inter> (star (brackets P) \<inter> Re S)) = ((dyck_language \<Gamma>) \<inter> (Re S))\<close>
    proof
      show \<open>dyck_language \<Gamma> \<inter> (star (brackets P) \<inter> Re S) \<subseteq> dyck_language \<Gamma> \<inter> Re S\<close> by blast
    next
      show \<open>dyck_language \<Gamma> \<inter> Re S \<subseteq> dyck_language \<Gamma> \<inter> (star (brackets P) \<inter> Re S)\<close> using \<Gamma>_def dyck_lang_imp_star_brackets by auto
    qed
  moreover have hom: \<open>hom h\<close> by (simp add: h_def hom_def)
  moreover have \<open>reg TYPE('n) (star (brackets P) \<inter> Re S)\<close> sorry
  ultimately have \<open>reg TYPE('n) (star (brackets P) \<inter> Re S) \<and> L = image h ((star (brackets P) \<inter> Re S) \<inter> (dyck_language \<Gamma>)) \<and> hom h\<close> by blast 
  then show ?thesis by blast
qed



end