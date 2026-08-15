(*<*)
theory Paper
  imports 
    "LR0_Base.LR0_Parser"
    "HOL-Library.LaTeXsugar"
begin

section \<open>setup\<close>

declare [[names_short, show_question_marks = false]]

definition sub :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "sub X n \<equiv> X"

notation sub (\<open>\<^latex>\<open>\ensuremath{\<close>_\<^latex>\<open>_{\<close>_\<^latex>\<open>}}\<close>\<close>)

no_notation (latex) Cons (\<open>_ \<cdot>/ _\<close> [66,65] 65)

syntax (latex output)
  "_take" :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_|\<^bsub>_\<^esub>" [1000,0] 1000)
translations 
  "_take xs n" <= "CONST take n xs"

notation (latex output) drop (\<open>\<^bsub>_\<^esub>|_\<close>)

notation (latex output) LangS (\<open>L'(_')\<close>)
notation (latex output) gpda.Lang (\<open>L'(_')\<close>)

abbreviation initial_item :: "'n \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow>  \<cdot> _ ]") where
  "[A \<rightarrow> \<cdot> \<alpha> ] \<equiv>  [A \<rightarrow> [] \<cdot> \<alpha>]"
abbreviation complete_item :: "'n \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow> _ \<cdot> ]") where
  "[A \<rightarrow> \<alpha> \<cdot> ]  \<equiv>  [A \<rightarrow> \<alpha> \<cdot> []]"
abbreviation empty_item :: "'n \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow> \<cdot> ]") where
  "[A \<rightarrow> \<cdot> ]  \<equiv>  [A \<rightarrow> [] \<cdot> []]"

notation (latex output) It (\<open>\<^latex>\<open>\ensuremath{\mathrm{It}_{\<close>_\<^latex>\<open>}}\<close>\<close>)

(*>*)

section \<open>Introduction\<close>
subsection \<open>\<open>LR(k)\<close> Parsing\<close>
subsection \<open>The Isabelle Theorem Prover\<close>
subsection \<open>Isabelle Notation\<close>
subsubsection \<open>General Notation\<close>

text \<open>A term \<open>t\<close> of type \<open>\<tau>\<close> is notated as \<open>t :: \<tau>\<close>, with type variables @{typ 'a}, @{typ 'b},
@{typ 'c}, etc. Tuple types are notated using \<open>\<times>\<close>: for \<open>x\<^sub>0 :: 'a\<^sub>0, x\<^sub>1 :: 'a\<^sub>1,\<dots>, x\<^sub>n :: 'a\<^sub>n\<close>, we write
\<open>(x\<^sub>0,x\<^sub>1,\<dots>,x\<^sub>n) :: 'a\<^sub>0 \<times> 'a\<^sub>1 \<times> \<dots> \<times> 'a\<^sub>n\<close>.
 Type constructors are usually written postfix, as one can see in types such as
@{typ "'a set"}, and in cases of multiple types \<open>'a\<^sub>0, 'a\<^sub>1,\<dots>,'a\<^sub>n\<close>, they are written as 
\mbox{\<open>('a\<^sub>0,'a\<^sub>1,\<dots>,'a\<^sub>n)\<close>}. One of the most common types in this formalization, @{typ "('n, 't) sym"}, 
is an example for this.

The keyword \isakeyword{datatype} is used to declare algebraic data types, which can be seen in the 
commonly used type of natural numbers @{typ nat}, which we define recursively:
\begin{quote}
@{datatype nat}
\end{quote}
Another example is the type for lists, @{typ "'a list"}, which we will also be using frequently:
\begin{quote}
@{datatype list}
\end{quote}

An explicit list can be either written as \<open>x\<^sub>0 # x\<^sub>1 # ... # x\<^sub>n\<close> or as \<open>[x\<^sub>0, x\<^sub>1, ..., x\<^sub>n]\<close>. If 
\<open>xs = y # ys\<close>, \<open>hd xs = y\<close> and \<open>tl xs = ys\<close>. Furthermore, lists are concatenated with the operator 
\<open>@\<close>, @{const rev} reverses a list, @{const set} converts a list to a set, @{term "xs!n"} returns the 
\<open>n\<close>-th element of the list \<open>xs\<close> (with 0-indexing), @{term "take n xs"} is the prefix of length \<open>n\<close> 
of \<open>xs\<close>, and @{term "drop n xs"} is the suffix of \<open>xs\<close> starting at index \<open>n\<close>.

Pattern matching on a term \<open>\<tau>\<close> is done with the keywords \isakeyword{case} and \isakeyword{of}. For 
patterns \<open>\<pi>\<^sub>1, \<pi>\<^sub>2, \<dots>, \<pi>\<^sub>n\<close> and expressions \<open>e\<^sub>1, e\<^sub>2, \<dots>, e\<^sub>n\<close>, the expression
\begin{quote}
\isa{\textsf{case}\ \isafree{\isasymtau}\ \textsf{of}} \<open>\<pi>\<^sub>1 \<Rightarrow> e\<^sub>1 | \<pi>\<^sub>2 \<Rightarrow> e\<^sub>2 | \<dots> | \<pi>\<^sub>n \<Rightarrow> e\<^sub>n\<close>
\end{quote}
returns \<open>e\<^sub>i\<close> if \<open>\<tau>\<close> matches \<open>\<pi>\<^sub>i\<close> and it does not match any \<open>\<pi>\<^sub>j\<close> with \<open>0 < j < i\<close>. If \<open>\<tau>\<close> matches no
\<open>\<pi>\<^sub>i\<close>, @{const undefined} is returned. It is worth noting that variables introduced in \<open>\<pi>\<^sub>i\<close> are bound
on \<open>e\<^sub>i\<close>. 

A simple example on lists returning @{const Nil} if the input is @{const Nil}, and a
singleton list containing the first element otherwise:
\begin{quote}
@{term \<open>case xs of [] \<Rightarrow> [] | y # ys \<Rightarrow> [y]\<close>}
\end{quote}

A record R whose record type has field names  \<open>\<phi>\<^sub>1, \<phi>\<^sub>2, ..., \<phi>\<^sub>n\<close> 
is defined through the notation
\[ \<open>R = \<lparr>\<phi>\<^sub>1 = v\<^sub>1, \<phi>\<^sub>2 = v\<^sub>2, \<phi>\<^sub>n = v\<^sub>n\<rparr>\<close> \]
if R has values \<open>v\<^sub>1, v\<^sub>2, ..., v\<^sub>n\<close> such that \<open>\<phi>\<^sub>i = v\<^sub>i\<close> for every \<open>i \<le> n\<close>.

Lastly, if premises \<open>A\<^sub>1, A\<^sub>2, \<dots>, A\<^sub>n\<close> imply \<open>B\<close>, we write \mbox{\<open>\<lbrakk>A\<^sub>1; A\<^sub>2; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> B\<close>.}\<close>

subsubsection \<open>Context-Free Grammars\<close>

text \<open>Our formalization works on top of the formalization of context-free grammars by 
Nipkow et al.~\<^cite>\<open>Nipkow\<close>. In their theories, they introduce type 
@{typ "('n, 't) sym"} for context-free grammar \concept{symbols} as a tagged union consisting of 
nonterminals (@{const Nt}) and terminals (@{const Tm}) of type @{typ 'n} and @{typ 't} respectively:
@{datatype sym}

Besides defining this type for symbols, they also define the following abbreviations:
\begin{quote}
\begin{tabular}{ll}
Lists of symbols & \<open>('n,'t) syms = ('n, 't) sym list\<close>\\
Productions & \<open>('n,'t) prod = 'n \<times> ('n,'t) syms\<close>\\
Sets of productions & \<open>('n,'t) Prods = ('n,'t) prod set\<close>
\end{tabular}
\end{quote}
where we informally write \<open>(A, \<alpha>) :: ('n, 't) prod\<close> as \<open>A \<rightarrow> \<alpha>\<close>. For \mbox{\<open>\<alpha> :: ('n, 't) syms\<close>}, 
@{term \<open>Nts_syms \<alpha>\<close>} returns the set of all \<open>X :: 'n\<close> such that @{prop \<open>Nt X \<in> set \<alpha>\<close>}. Similarly 
for \<open>P :: ('n, 't) Prods\<close>, Nipkow et al. define @{term \<open>Nts P\<close>}:
\begin{equation*}
@{term \<open>Nts P = (\<Union>(A,\<alpha>)\<in>P. {A} \<union> Nts_syms \<alpha>)\<close>}.
\end{equation*}

They further define the datatype for context-free grammars:
\begin{equation*}
\isakeyword{datatype} \<open>('n, 't) Cfg = Cfg (('n,'t) Prods) 'n\<close>.
\end{equation*}
@{term "Cfg P S"} denotes a context-free grammar with production set \<open>P\<close> and start symbol \<open>S\<close>. If 
@{term "G = Cfg P S"}, @{term "Prods G"} refers to \<open>P\<close>, and analogously, @{term "Start G"} refers to 
\<open>S\<close>.

A derivation step from \<open>\<phi>\<close> to \<open>\<psi>\<close> under production set \<open>P\<close> is notated as \mbox{@{term \<open>P \<turnstile> \<phi> \<Rightarrow> \<psi>\<close>}}.
More formally, for \<open>A :: 'n\<close> and \<open>\<alpha>, \<beta>, \<gamma> :: ('n, 't) syms\<close> they define:
\begin{equation*} 
@{thm derive.intros[of A \<beta> P \<alpha> \<gamma>]}.
\end{equation*}
Moreover, they denote the reflexive transitive closure of derivations by 
\[ @{term \<open>P \<turnstile> \<phi> \<Rightarrow>* \<psi>\<close>}, \] 
and derivations of length \<open>n\<close> by @{term \<open>P \<turnstile> \<phi> \<Rightarrow>(n) \<psi>\<close>}. Rightmost derivations are notated analogously, 
with \<open>\<Rightarrow>r\<close>, \<open>\<Rightarrow>r*\<close> and \<open>\<Rightarrow>r(n)\<close> respectively.

Lastly, Nipkow et al. define the language of a nonterminal w.r.t a set of productions
\begin{equation*}
@{thm Lang_def},
\end{equation*}
and based on this, the language of a grammar
\begin{equation*}
@{term \<open>LangS G\<close>} = @{term [show_abbrevs=false] \<open>Lang (Prods G) (Start G)\<close>}
\end{equation*}
 
Besides type variables @{typ 'n} for nonterminals and @{typ 't} for terminals, we use the following 
variable conventions: for brevity, we refer to \<open>('n, 't) sym\<close> and \<open>('n, 't) syms\<close> simply as @{type sym}
and @{type syms} respectively; \<open>A, B, C :: 'n\<close>; \<open>a, b, c :: 't\<close>; \<open>u, v, w :: 't list\<close>; and finally
\<open>\<alpha>, \<beta>, \<gamma> :: ('n, 't) syms\<close>.\par

For further definitions and notation, we defer to the AFP entry by Nipkow et al~\<^cite>\<open>Nipkow\<close>.\<close>

section \<open>Previous Work\<close>

section \<open>Basic Definitions\<close>
subsection \<open>Extended Grammars\<close>
subsubsection \<open>Reduced Grammars\<close>

text \<open>In general, context-free grammars (CFGs) can contain problematic nonterminals which can be 
removed from the grammar without altering the language. Working with grammars that lack such 
nonterminals is ideal, since having them increases computational complexity and makes the grammar 
less well-behaved.

\begin{example}\label{ex:useless symbols}
Let \<open>G\<close> be a CFG with @{term \<open>S = Start G\<close>} and productions:
\begin{center}
\begin{tabular}{cc}
\<open>S \<rightarrow> A | AB\<close> & \<open>A \<rightarrow> aA | a\<close>\\
\<open>C \<rightarrow> ac | BCD\<close> & \<open>D \<rightarrow> BC | D\<close>
\end{tabular}
\end{center}
Each nonterminal except for \<open>S\<close> and \<open>A\<close> carries problems with it:
\begin{itemize}
\item There are no productions where \<open>B\<close> is on the left-hand side. This means that if \<open>S\<close> 
reaches a sentential form \<open>\<alpha>\<close> such that \<open>Nt B \<in> set \<alpha>\<close>, no word will be derived from \<open>\<alpha>\<close>. 
\item \<open>S\<close> cannot reach \<open>C\<close>, meaning no productions containing \<open>C\<close>, or reachable only 
through \<open>C\<close> (e.g. reaching \<open>D\<close> using production \mbox{\<open>C \<rightarrow> BCD\<close>}), can be used to derive words in \<open>LangS G\<close>.
\item \<open>D\<close>, as opposed to \<open>B\<close>, does show up on the LHS of certain productions, but none of these productions
can lead to a word: \<open>D \<rightarrow> BC\<close> contains \<open>B\<close>, which cannot derive a \<open>'t list\<close>, and \<open>D \<rightarrow> D\<close> has no effect.
Furthermore, similarly to \<open>C\<close>, \<open>D\<close> cannot be reached by \<open>S\<close>.
\end{itemize}
\end{example}

Nipkow et al. define \concept{useful} nonterminals w.r.t. a set of productions and a start 
symbol:
\begin{gather*}
@{abbrev \<open>productives P \<alpha>\<close>}\\
\begin{multlined}
\<open>useful P S A =\<close>\ (@{term \<open>\<exists>\<beta>. P \<turnstile> [Nt S] \<Rightarrow>* \<beta>\<close>}\\
  {} \wedge @{term \<open>Nt A \<in> set \<beta> \<and> productives P \<beta>\<close>})
\end{multlined}
\end{gather*}
For a CFG \<open>G\<close>, \<open>A :: 'n\<close> is \concept{reachable} if there exists a \<open>\<beta> :: syms\<close> such that 
\mbox{\<open>A \<in> set \<beta>\<close>} and @{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<beta>\<close>}. Otherwise, it is \concept{unreachable}.
Similarly, it is \concept{productive} if @{prop [source] \<open>productives (Prods G) [Nt A]\<close>} holds, as 
defined by Nipkow et al. as well:
\begin{equation*}
@{abbrev \<open>productive (Prods G) A\<close>}.
\end{equation*}
Similarly to reachable terminals, a nonterminal that is not productive is \concept{unproductive}. A 
useful nonterminal is therefore a nonterminal that is both reachable and productive.

Nipkow et al. have also proved that removing all nonterminals that are unreachable or unproductive, 
i.e. all non-useful nonterminals, preserves the language~\cite[Lemma Lang\_restrict\_useful]{Nipkow}:
\begin{lemma}
Let 
\[@{term [source] \<open>restrict_Nts R P = {(A,\<alpha>) \<in> P. \<forall>B \<in> {A} \<union> Nts_syms \<alpha>. R B}\<close>}. \]
Then @{thm Lang_restrict_useful}.\qed
\end{lemma}

Consider Example~\ref{ex:useless symbols} once again: if we remove all productions containig 
non-useful nonterminals in the Example, we get the production set:
\begin{center}
\begin{tabular}{cc}
\<open>S \<rightarrow> A\<close> & \<open>A \<rightarrow> aA | a\<close>
\end{tabular}
\end{center}

As we can see, by applying this restriction to arbitrary grammars, the resulting set of 
productions can potentially be much smaller than the original one. This also guarantees that all
nonterminals are more well-behaved; for example, since every nonterminal is productive, we know 
that any sentential form that can be derived from \<open>S\<close> contains only productive nonterminals and can
therefore derive a word in the language. This property will be particularly useful in the coming 
sections.

With this, we now define the notion of \concept{reduced grammars}.
\begin{definition}[Reduced grammar]
\begin{equation*}
@{thm reduced_def}.
\end{equation*}
\end{definition}

Due to the fact that for any CFG we can construct a reduced grammar with equivalent language,
we can safely constrain our automata to work exclusively with these more well-behaved grammars 
without sacrificing generality.\<close>

subsubsection \<open>Extending Grammars by a New Start Symbol\<close>

(*<*)
context Extended_Cfg 
begin

abbreviation \<open>I\<^sub>G \<equiv> Extended_Cfg.IPDA G'\<close>

(*>*)

text\<open>From this point onward in this paper, unless stated otherwise, let \<open>G\<close> be a fixed CFG whose 
start symbol is \<open>S\<close> with the following properties:
\begin{itemize}
\item @{prop \<open>finite (Prods G)\<close>}
\item @{prop \<open>LangS G \<noteq> {}\<close>}
\item @{prop \<open>reduced G\<close>}
\end{itemize}

We extend \<open>G\<close> by a fresh start symbol \<open>S'\<close> with a single production \<open>(S', [Nt S])\<close>. 
The resulting grammar, which we define to be \<open>G'\<close>, is the \concept{extended grammar}, or the 
\concept{extension}, of \<open>G\<close>. We analogously refer to \<open>Prods G'\<close> as the extension of \<open>Prods G\<close> or the 
\concept{extended set of productions} of \<open>G\<close>. Formally:
\begin{gather*}
@{thm S'_def}\\
@{thm G'_def}
\end{gather*}

We now prove that extending a grammar preserves both language and reduction.

\begin{lemma}\label{G'_deriven_Suc_imp_G_deriven}
If there exists a derivation in \<open>G'\<close>
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) \<beta>\<close>}, \]
then there also exists a derivation in \<open>G\<close>
\[ @{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>(n) \<beta>\<close>}. \]
\begin{proof} 
We do a proof induction on \<open>n\<close>. If \<open>n = 0\<close>, \<open>\<beta> = [Nt S]\<close>, and the implication holds.

If \<open>n = Suc m\<close> for some \<open>m\<close>, the induction hypothesis tells us that sentential form \<open>\<alpha>\<close> that 
derives \<open>\<beta>\<close> in the final derivation step can be derived by \<open>S\<close> in \<open>G\<close> in \<open>m\<close> steps. This means that 
all nonterminals in \<open>\<alpha>\<close> are in \<open>G\<close>. Since the only production in @{term \<open>Prods G' - Prods G\<close>}, has 
\<open>S' \<notin> Nts (Prods G)\<close> in the LHS, the final derivation step @{prop \<open>Prods G' \<turnstile> \<alpha> \<Rightarrow> \<beta>\<close>} also 
exists in \<open>G\<close>, completing the proof.
\end{proof}
\end{lemma}

\begin{theorem}\label{Lang_preserved}[Preservation of language]
@{thm Lang_preserved}
\begin{proof} 
Let @{prop \<open>w \<in> LangS G'\<close>}. Then there exists a derivation of @{term \<open>map Tm w\<close>} of nonzero length,
i.e., of the form
\[@{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) map Tm w\<close>} \]
for some \<open>n\<close>. Lemma~\ref{G'_deriven_Suc_imp_G_deriven} then implies @{prop \<open>w \<in> LangS G\<close>}.

Conversely, let @{prop \<open>w \<in> LangS G\<close>}. Then there exists a derivation
\[ @{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>* map Tm w\<close>}. \] 
Since @{prop \<open>Prods G \<subseteq> Prods G'\<close>}, this derivation also exists in \<open>G'\<close>. This, along with the fact 
that that \<open>S'\<close> derives \<open>S\<close> in \<open>G'\<close>, implies that @{prop \<open>w \<in> LangS G'\<close>}.
\end{proof}
\end{theorem}

\begin{lemma}[Preservation of reduction]
If \<open>G\<close> is reduced and @{prop \<open>LangS G \<noteq> {}\<close>}, \<open>G'\<close> is reduced.
\begin{proof}
Since \<open>G\<close> is reduced, all nonterminals in \<open>Prods G\<close> are useful, and the fact that @{prop \<open>LangS G \<noteq> {}\<close>}
implies that there exist \<open>\<alpha> :: syms\<close> and \<open>w \<in> LangS G\<close> such that  
\begin{equation*}
\<open>Prods G \<turnstile> [Nt S] \<Rightarrow> \<alpha> \<Rightarrow>* map Tm w\<close>.
\end{equation*}
This implies that \<open>S \<in> Nts (Prods G)\<close>. Since \<open>Prods G \<subseteq> Prods G'\<close>, this
means that all nonterminals in \<open>Nts (Prods G)\<close> are useful in \<open>Prods G'\<close>. Therefore, to show that 
\<open>G'\<close> is reduced, it suffices to show that \<open>S'\<close> is useful in \<open>Prods G'\<close>, i.e., reachable and productive. 
Reachability is trivial by reflexivity. To show that it is productive, we need to show 
that there exists a \<open>w :: 't list\<close> such that @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>* map Tm w\<close>}, which is 
equivalent to showing there exists some \<open>w \<in> LangS G'\<close>. This follows directly from our assumption 
that @{prop \<open>LangS G \<noteq> {}\<close>} and Theorem~\ref{Lang_preserved}.
\end{proof}
\end{lemma}

We have now defined a way to extend a context-free grammar by a new start symbol, which, as we will 
see in future sections, will allow us to simplify the definition of multiple automata in many 
regards.\<close>

subsection \<open>Context-Free Items\<close>

text \<open>\begin{definition}[Context-free item]
A \concept{context-free item} @{typ \<open>('n, 't) item\<close>} for a CFG \<open>G\<close> is a triple 
\mbox{\<open>(A, \<alpha>, \<beta>) :: 'n \<times> ('n, 't) syms \<times> ('n, 't) syms\<close>} such that 
@{prop \<open>(A, \<alpha>@\<beta>) \<in> Prods G\<close>}. We write the item \<open>(A, \<alpha>, \<beta>)\<close> as @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}, and akin to 
@{type sym} and @{type syms}, we often abbreviate the item type to simply @{type item} for brevity.
\end{definition}

Context-free items allow tracking the current state of the parsing process. Generally, as parsers
work towards deriving a string, the symbols to the right of the bullet (e.g. \<open>\<beta>\<close> in 
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}) are shifted towards the left. If \<open>(A, \<alpha>@\<beta>) \<in> Prods G\<close>, the item
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} denotes the situation where a word has already been derived from the substring 
\<open>\<alpha>\<close>, with a suffix still left to be derived from \<open>\<beta>\<close>. We call the symbols that have already been 
shifted the \concept{history} of the item.

For @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}, \<open>\<alpha> = \<epsilon>\<close> denotes the situation where nothing has been 
derived from \<open>A\<close> yet. Analogously, \<open>\<beta> = \<epsilon>\<close> denotes the situation where a substring of the 
input has been completely derived from \<open>A\<close>. These items are therefore called \concept{initial} and 
\concept{complete} items respectively. 
We often write the empty list implicitly on either side of the bullet, e.g., instead of @{term \<open>[A \<rightarrow> \<alpha> \<cdot> []]\<close>}, we write 
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> ]\<close>}. We also use this convention if both sides of the bullet are empty.

Additionally, we denote the set of all complete items in a set of items \<open>I\<close> by @{term \<open>completes I\<close>}:
\begin{equation*}
@{thm completes_def}.
\end{equation*}
An item that is not complete is referred to as \concept{incomplete}, and we correspondingly define
@{const incompletes} as the complement of @{const completes}:
\begin{equation*}
@{abbrev \<open>incompletes I\<close>}.
\end{equation*}
We also lift the definition of history from items to lists of items:
\begin{equation*}
@{thm hist_def},
\end{equation*}
and lastly, we refer to the set of all items of a CFG \<open>G\<close> as @{term \<open>It G\<close>}:
\begin{equation*}
@{thm It_def}.
\end{equation*}

\begin{lemma}
If \<open>G\<close> is a CFG such that \<open>Prods G\<close> is finite, @{term \<open>It G\<close>} is finite.
\begin{proof}
The definition of @{term \<open>It G\<close>} is clearly equivalent to the union of the sets of items for 
each production in \<open>Prods G\<close>. Formally:
\[ @{term \<open>It G = (\<Union>(A,w)\<in>Prods G. {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w})\<close>}. \]
We can show this union is finite by showing that the individual sets are finite. In order to do 
this, we prove that for arbitrary \<open>A\<close> and \<open>w\<close>, the set @{term \<open>{[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w}\<close>}
is finite. 

We prove this property by showing there exists a bijection between this set and the first
@{term "length w"} natural numbers using the mapping \<open>f :: nat \<Rightarrow> ('n, 't) item\<close>
\[ @{term "f n = [A \<rightarrow> take n w \<cdot> drop n w]"}. \]
\end{proof}
\end{lemma}\<close>

subsection \<open>Generalized Pushdown Automata\<close>

(*<*)
end
context gpda
begin
(*>*)

text \<open>Throughout this paper, we define several automata to lay the foundations for the canonical 
LR(0) parser. Most of these automata, including the parser itself, require a stack to operate, but 
unlike conventional pushdown automata, it is sometimes necessary for them to read multiple stack 
symbols in a single transition steps.
\begin{definition}[Generalized pushdown automata]
A generalized pushdown automata (GPDAs) is a record of type @{typ "('q, 'a) gpda"} where 
@{typ 'q} is the type of stack symbols, @{typ 'a} the type of alphabet symbols, and
\begin{itemize}
\item \<open>states :: 'q set\<close> is a finite set of \concept{states}.
\item \<open>init :: 'q\<close> is the \concept{initial state} with \<open>init \<in> states\<close>.
\item \<open>final :: 'q set\<close> is a set of \concept{final states} with \<open>final \<subseteq> states\<close>.
\item \<open>nxt :: ('q list \<times> 'a \<times> 'q list) set\<close> is the \concept{reading transition relation}, i.e., 
the relation of transitions that read and consume the leftmost symbol of the remaining input.
\item \<open>eps :: ('q list \<times> 'q list) set\<close> is the transition relation for \concept{\epsilon-transitions}, 
i.e., transitions that do not read the input.
\end{itemize}
\end{definition}

It is worth noting that, differently from traditional PDAs, GPDAs do not have a dedicated state. 
Instead, the topmost stack symbols (with varying length) are used to determine the transition. 
Therefore, if \<open>M\<close> is a GPDA, talking about to the state of \<open>M\<close> at a given time is a shorthand to 
refer to the topmost symbol on \<open>M\<close>'s stack at that moment.
Another important aspect is the fact that Wilhelm et al. define the transition relation to be finite, 
which we ignore for the sake of simplicity as this is of no importance to the correctness of our 
automata. This is of interest, however, in the case of the canonical LR(0) parser, which we will 
discuss later.

For \<open>M :: ('q, 'a) gpda\<close> we define a \concept{configuration} as a tuple 
\<open>(qs, w) :: 'q list \<times> 'a list\<close> where \<open>qs\<close> denotes the current stack, and \<open>w\<close> the remaining input to 
be read. In accordance with the Isabelle/HOL list datatype, we define the topmost stack symbol as 
the leftmost list element, deviating from Wilhelm et al. in this regard.

A configuration of \<open>M\<close> is \concept{initial} if the stack consists of a singleton list containing 
the initial state @{term \<open>init M\<close>}, while a \concept{final} configuration for \<open>M\<close> consists of a 
singleton list with some final state on the stack after completely consuming the input, 
i.e., a configuration of the form \<open>([f], \<epsilon>)\<close> for some \<open>f \<in> final M\<close>.

We now define the step relation \<open>\<turnstile>\<close> for GPDAs:
\begin{gather*}
@{thm step_nxt}\\
@{thm step_eps}
\end{gather*}
We refer to sequences of steps as \concept{computations}, and denote \<open>n\<close>-step computations
with \<open>\<turnstile>(n)\<close>, and its reflexive-transitive closure with \<open>\<turnstile>*\<close>.

Finally, we define the \concept{language} @{term \<open>Lang\<close>} for \<open>M\<close> as the set of words for which \<open>M\<close> 
can reach a final configuration from the corresponding initial configuration:
\begin{equation*}
@{thm Lang_def}.
\end{equation*}
\<close>

section \<open>The Item Pushdown Automaton\<close>

(*<*) 
end
context ipda
begin  

notation step (infix \<open>\<turnstile>I\<close> 55)
notation steps (infix \<open>\<turnstile>I*\<close> 55)
notation stepn ( \<open>_ \<turnstile>I'(_') _\<close> 55)

(*>*)

subsection \<open>Definition\<close>

text \<open>One of the main objectives in the construction of our parser is determinism. Despite the ability of
PDAs of recognizing CFLs, they are non-deterministic in general, which means they are not easily
implemented in practice. In this section, we define the Item Pushdown Automaton to a 
context-free grammar, from which we will later derive a deterministic parser.

\begin{definition}[Item pushdown automaton]
The \concept{item pushdown automaton} (IPDA) to a CFG \<open>G\<close> with extension \<open>G'\<close> is the 
@{typeof IPDA}:
\begin{multline*}
  \<open>I\<^sub>G = \<lparr>states = It G', init = [S' \<rightarrow> \<cdot> [Nt S]],\<close>\\
  \<open>final = {[S' \<rightarrow> [Nt S] \<cdot> ]}, nxt = \<Delta>, eps = \<E>\<rparr>\<close>
\end{multline*}
where 
\begin{multline*}
\<open>\<Delta> = {([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], a, [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]])\<close>\\
\<open>| X \<beta> a \<gamma>. (X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'}\<close>
\end{multline*}
and \<open>\<E> = E \<union> R\<close> for
\begin{gather*}
\begin{multlined}
  \<open>E = {([[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[Y \<rightarrow> \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]])\<close>\\ 
  \<open>| X \<beta> Y \<gamma> \<alpha>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'}\<close>
\end{multlined}\\
\begin{multlined}
  \<open>R = {([[Y \<rightarrow> \<alpha> \<cdot> ], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]])\<close>\\
  \<open>| Y \<alpha> X \<beta> \<gamma>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'}\<close>
\end{multlined}
\end{gather*}
\end{definition}

Overall, the IPDA has three types of transitions. We call transitions in @{const nxt} \concept{shifting} 
transitions, transitions in @{term \<open>E \<subseteq> \<E>\<close>} \concept{expanding} transitions, and transitions in 
@{term \<open>R \<subseteq> \<E>\<close>} \concept{reducing} transitions. We denote @{const IPDA} steps by \<open>\<turnstile>I\<close>, \<open>\<turnstile>I*\<close> and
\<open>\<turnstile>I(n)\<close> analogously to the standard symbols. 

Our definitions differ slightly from those by Wilhelm et al.: in all
transition sets, we explicitly restrict the elements to items that correspond to productions of \<open>G'\<close>.
In their book, Wilhelm et al. define the transition relation of a GPDA with state set \<open>Q\<close> and input
alphabet \<open>V\<^sub>T\<close> to be a subset of \mbox{\<open>Q\<^sup>+ \<times> V\<^sub>T \<times> Q\<^sup>*\<close>}. We approximate this in the record type of GPDAs, 
as we stated before, by definining \mbox{\<open>nxt :: ('q list \<times> 'a \<times> 'q list) set\<close>} and 
\mbox{\<open>eps :: ('q list \<times> 'q list) set\<close>} for a \<open>('q, 'a) gpda\<close>. Our definitions of \mbox{\<open>nxt IPDA\<close>} and \<open>eps IPDA\<close>
therefore enforce this by explicitly restricting the set to items whose corresponding production is 
in \<open>Prods G'\<close>, which is equivalent to the items themselves being in @{term \<open>It G'\<close>}.

Intuitively, \<open>I\<^sub>G\<close> accepts a word \<open>w\<close> by finding a rightmost derivation 
\[ @{term \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* map Tm w\<close>}. \]
If the current state of \<open>I\<^sub>G\<close> is @{term \<open>[A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]\<close>} for any \mbox{\<open>a :: 't\<close>}, \<open>I\<^sub>G\<close> will 
invariably shift \<open>Tm a\<close>, effectively replacing this topmost item by @{term \<open>mbox [A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>]\<close>}. 
Similarly, if the state is some complete item @{term \<open>[Y \<rightarrow> \<alpha> \<cdot> ]\<close>}, it will reduce the item 
and shift \<open>Nt Y\<close> on the second-topmost item if possible. If the stack is 
@{term \<open>[Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>\<close>}, the act of reducing the first two items to 
@{term \<open>[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]\<close>} is equivalent to the backwards (i.e. right-to-left)
application of a rightmost derivation step for some \<open>u :: 't list\<close> of the form
\begin{equation*}
@{prop \<open>Prods G' \<turnstile> \<beta> @ Nt Y # map Tm u \<Rightarrow>r \<beta> @ \<alpha> @ map Tm u\<close>}.
\end{equation*}

Lastly, the expanding case is the only transition type where nondeterministic behavior actually 
presents itself. While reducing transitions correspond to the IPDA applying a backward step in a 
rightmost derivation, the expanding step is essentially the IPDA nondeterministically choosing 
\emph{which} production to reduce: as we will later prove, if the IPDA performs the expansion
\begin{multline*}
@{term \<open>([X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>, w)\<close>}\\
  \<open>\<turnstile>I\<close>\ @{term \<open>([Y \<rightarrow> \<cdot> \<alpha> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>, w)\<close>}
\end{multline*}
it will only complete \<open>\<alpha>\<close>, i.e., reach a configuration with stack 
\[ @{term \<open>[Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>\<close>} \]
if for some prefix \<open>u\<close> of the remaining input word \<open>w = uv\<close> holds 
\[ @{prop \<open>Prods G' \<turnstile> \<alpha> \<Rightarrow>* map Tm u\<close>}. \]
 
We will now work towards proving that \<open>I\<^sub>G\<close> accepts exactly @{term \<open>LangS G\<close>}.\<close>

subsection \<open>Language Equivalence\<close>

text\<open>\begin{lemma}[IPDA invariant]\label{ipda.invariant}
@{prop \<open>([init M], u @ v) \<turnstile>I* (rev \<rho>, v)\<close>} implies\\ @{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u\<close>}.
\begin{proof}
We do a proof by induction on the length \<open>n\<close> of the computation for arbitrary \<open>u, v,\<close> and \<open>\<rho>\<close>.

If @{term "([init M], u @ v) \<turnstile>I(0) (rev \<rho>, v)"}, then
\begin{gather*} 
\<open>[init M] = rev \<rho> = [[S' \<rightarrow> \<cdot> [Nt S]]]\<close> \text{ and } @{prop \<open>u @ v = v\<close>} 
\end{gather*}
hold. This in turn implies @{prop \<open>hist \<rho> = []\<close>} and @{prop \<open>u = []\<close>}. Since
\mbox{@{prop \<open>Prods G \<turnstile> [] \<Rightarrow>* []\<close>}} holds, the invariant holds.

On the other hand, if @{term "([init M], u @ v) \<turnstile>I(Suc n) (rev \<rho>, v)"} for some \<open>n :: nat\<close>,
we do a case distinction on the final step of the computation.

If the last step was a shifting transition there exist \<open>A, \<alpha>, a, \<beta>, \<tau>, a, \<close> and \<open>x\<close> such that
the second to last configuration was of the form
\begin{gather}
@{term \<open>([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<tau>, a # v)\<close>}\label{eq:ipda.invariant.shift}
\intertext{and}
@{term \<open>rev \<rho> = [A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>] # \<tau>\<close>}\label{eq:ipda.invariant.rho_shift}.
\end{gather}
This implies the existence of some \<open>y :: 't list\<close> such that the initial input was of the form
\<open>uv = yav\<close>. This, together with \eqref{eq:ipda.invariant.shift}, and the induction hypothesis implies 
\begin{multline*}
\<open>Prods G \<turnstile> hist (rev \<tau> @ [[A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]])\<close>\\ 
  \<open>= hist (rev \<tau>) @ \<alpha> \<Rightarrow>* map Tm y\<close>.
\end{multline*}
With \<open>uv = yav\<close> this implies
\begin{align*}
  \<open>Prods G \<turnstile> hist (rev \<rho>)\<close> 
    & {} = \<open>hist (rev \<tau> @ [[A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>]])\<close>\\
    & {} = \<open>hist (rev \<tau>) @ \<alpha> @ [Tm a]\<close>\\
    & {} = \<open>\<Rightarrow>* map Tm y @ [Tm a] = u\<close>
\end{align*}
The invariant therefore holds.

For the reducing case, we have a second-to-last configuration
\begin{gather}
@{term \<open>([Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close>}\label{eq:ipda.invariant.reduce}\\
\intertext{and final configuration} 
@{term \<open>rev \<rho> = [X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>] # \<tau>\<close>}\label{eq:ipda.invariant.rho_reduce}
\end{gather}
for some \<open>Y, \<alpha>, X, \<beta>, \<gamma>\<close> and \<open>\<tau>\<close>. Since the complete item @{term \<open>[Y \<rightarrow> \<alpha> \<cdot> ]\<close>} is reduced. Therefore,
@{prop \<open>(Y, \<alpha>) \<in> Prods G\<close>} must hold; otherwise, @{prop \<open>(Y, \<alpha>) = (S', [Nt S])\<close>}, which would 
contradict the definition of \<open>G'\<close> and \<open>S'\<close> since @{prop \<open>[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] \<in> It G'\<close>}.
\begin{equation}\label{eq:ipda.invariant.reduce_rs}
@{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow> hist (rev \<tau>) @ \<beta> @ [Nt A]\<close>}.
\end{equation}
By the induction hypothesis, we also know that @{term \<open>hist (rev \<tau>) @ \<beta> @ [Nt A]\<close>} derives \<open>u\<close>, 
meaning the invariant holds once again by transitivity.

Finally, in the expanding case we have
\begin{gather*}
@{term \<open>([X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close>}
\intertext{and} 
@{prop \<open>rev \<rho> = [Y \<rightarrow> [] \<cdot> \<alpha>] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>\<close>}
\end{gather*}
By the induction hypothesis we have once more \<open>Prods G \<turnstile> hist (rev \<tau>) @ \<beta> \<Rightarrow>* map Tm u\<close>. We then 
have
\begin{align*}
\<open>Prods G \<turnstile> hist \<rho>\<close> &\ \<open>= hist ((rev \<tau>) @  [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] @ [Y \<rightarrow> [] \<cdot> \<alpha>])\<close>\\
&\ \<open>= hist (rev \<tau>) @ \<beta> \<Rightarrow>* map Tm u\<close>. 
\end{align*}
The invariant is therefore satisfied for all cases.
\end{proof}
\end{lemma}

\begin{lemma}\label{ipda.Lang_subst_Lang_G}
@{term \<open>gpda.Lang I\<^sub>G \<subseteq> LangS G\<close>}
\begin{proof}
Assume @{prop \<open>w \<in> gpda.Lang I\<^sub>G\<close>}. Then, 
\[ \<open>([init I\<^sub>G], w) =\<close>\ @{prop \<open>([init I\<^sub>G], w @ [])  \<turnstile>I* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>}. \] 
By Lemma~\ref{ipda.invariant}, this implies @{prop \<open>Prods G \<turnstile> hist [final_state] \<Rightarrow>* map Tm w\<close>}.
Since @{prop \<open>hist [final_state] = [Nt S]\<close>}, this proves that @{prop \<open>w \<in> LangS G\<close>}.  
\end{proof}
\end{lemma}

And now, we prove the other direction:

\begin{lemma}\label{completes_Tms}
If @{prop \<open>(A, \<alpha> @ map Tm u @ \<beta>) \<in> Prods G' \<close>}, then 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> map Tm u @ \<beta>]#\<rho>, u@v) \<turnstile>I* ([A \<rightarrow> \<alpha> @ map Tm u \<cdot> \<beta>]#\<rho>, v)\<close>}. \]
\begin{proof}
Trivial by induction on the length of \<open>u\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{derives_imp_completes}[Derivation implies IPDA completion]
If 
\[ @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w\<close>} \] 
and @{prop \<open>(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'\<close>}, then for any \<open>\<rho>, x\<close> holds: 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>@\<gamma>] # \<rho>, w @ x) \<turnstile>I* ([A \<rightarrow> \<alpha>@\<beta> \<cdot> \<gamma>] # \<rho>, x)\<close>}. \]
\begin{proof}
We do a proof by strong induction on the length of the derivation \<open>n\<close>.
If \<open>n = 0\<close>, \<open>\<beta> = map Tm w\<close>, and the implication holds by Lemma~\ref{completes_Tms}.

If \<open>n = Suc m\<close> for some \<open>m :: nat\<close>, \<open>\<beta>\<close> must be of the form 
\begin{equation}\label{d_imp_c.b_decomp(1)}
@{prop \<open>\<beta> = \<delta>\<^sub>1 @ Nt X # \<delta>\<^sub>2\<close>}
\end{equation}
for \<open>X :: 'n\<close> and \<open>\<delta>\<^sub>1, \<delta>\<^sub>2 :: syms\<close>. Furthermore, Nipkow et al. have proved
\begin{multline*}
 \<open>P \<turnstile> u @ v \<Rightarrow>(n) w\<close>\\
  \<open>\<longleftrightarrow> (\<exists>n1 n2 w1 w2. n = n1 + n2 \<and> w = w1 @ w2\<close>\\ 
  \<open>\<and> P \<turnstile> u \<Rightarrow>(n1) w1 \<and> P \<turnstile> v \<Rightarrow>(n2) w2)\<close>.
\end{multline*}

By applying this lemma twice, the derivation of \<open>w\<close> can be decomposed such that:
\begin{subequations}
\begin{gather}
@{prop \<open>w = u @ v @ y\<close>}\label{d_imp_c.b_decomp(2)}\\
@{prop \<open>Prods G' \<turnstile> \<delta>\<^sub>1 \<Rightarrow>(i) map Tm u\<close>}\label{d_imp_c.d1}\\
@{prop \<open>Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v\<close>}\label{d_imp_c.X}\\
@{prop \<open>Prods G' \<turnstile> \<delta>\<^sub>2 \<Rightarrow>(k) map Tm y\<close>}\label{d_imp_c.d2}\\
@{prop \<open>n = i + j + k\<close>}.\label{d_imp_c.b_decomp(6)}
\end{gather}
\end{subequations}
For some \<open>u, v, y :: 't list\<close> and \<open>i, j, k :: nat\<close>.

Since @{prop \<open>Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v\<close>}, @{prop \<open>j > 0\<close>} must hold. With 
\eqref{d_imp_c.b_decomp(6)},  we know that there are only two cases: either @{prop \<open>j = n\<close>} and 
\<open>i = k = 0\<close>, or \<open>i\<close>, \<open>j\<close>, and \<open>k\<close> are all strictly less than \<open>n\<close>. We now distinguish these cases.

If \<open>j = n\<close> and \<open>i = k = 0\<close>, 
\begin{gather}\label{d_imp_c.d1u_d2y}
\<open>\<delta>\<^sub>1 = map Tm u\<close> \text{ and } \<open>\<delta>\<^sub>2 = map Tm y\<close>
\end{gather} 
hold by \eqref{d_imp_c.d1} and \eqref{d_imp_c.d2}. \<open>j = n\<close> also implies the existence of some 
\<open>\<beta>' :: syms\<close> such that 
\begin{equation}\label{eq:d_imp_c.stepm}
\<open>Prods G' \<turnstile> [Nt X] \<Rightarrow> \<beta>' \<Rightarrow>(m) map Tm v\<close>.
\end{equation}

By Lemma~\ref{completes_Tms}, and substituting \eqref{d_imp_c.b_decomp(1)}, 
\eqref{d_imp_c.b_decomp(2)}, and \eqref{d_imp_c.d1u_d2y}, @{term \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] # \<rho>, w @ x)\<close>} 
reaches
\[ @{term \<open>([A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, v @ y @ x)\<close>}, \]
and since \<open>X\<close> derives \<open>\<beta>'\<close>, the item \<open>[X \<rightarrow> \<cdot> \<beta>']\<close> can then be pushed onto the stack through an 
expanding transition. \eqref{eq:d_imp_c.stepm} and the induction hypothesis then imply that 
\<open>I\<^sub>G\<close> reaches
\[ @{term \<open>([X \<rightarrow> \<beta>' \<cdot> ] # [A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X #  map Tm y @ \<gamma>] # \<rho>, y @ x)\<close>}, \]
since \<open>m < Suc m = n\<close>. \<open>I\<^sub>G\<close> then trivially reaches @{term \<open>([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] # \<rho>, x)\<close>} after a 
reducing transition and applying Lemma~\ref{completes_Tms} once again.

Finally, we now consider the case where @{prop \<open>j \<noteq> n\<close>}:

With @{prop \<open>n = i + j + k\<close>} and @{prop \<open>j > 0\<close>}, we know that @{prop \<open>i < n\<close>}, @{prop \<open>j < n\<close>}, and
@{prop \<open>k < n\<close>} all hold. Therefore, we can use the IH for each of the derivations \eqref{d_imp_c.d1}, 
\eqref{d_imp_c.X} and \eqref{d_imp_c.d2} after decomposing \<open>\<beta>\<close> and \<open>w\<close> as we did in the previous
cases with \eqref{d_imp_c.b_decomp(1)} and \eqref{d_imp_c.b_decomp(2)}. This completes the proof.
\end{proof}
\end{lemma}

With this lemma we can finally prove the second direction in the language equivalence proof:

\begin{lemma}\label{ipda.Lang_G_subst_Lang}
@{prop \<open>LangS G \<subseteq> gpda.Lang I\<^sub>G\<close>}
\begin{proof}
Assume @{prop \<open>w \<in> LangS G\<close>}. Since @{prop \<open>Prods G \<subseteq> Prods G'\<close>}, this implies 
\[ @{prop \<open>Prods G' \<turnstile> [Nt S] \<Rightarrow>* map Tm w\<close>} \] by the monotonicity of derivations as proved by 
Nipkow et al. With Lemma~\ref{derives_imp_completes} follows 
\[ @{prop \<open>([[S' \<rightarrow> \<cdot> [Nt S]]], w) \<turnstile>I* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>}. \] 

This is equivalent to @{prop \<open>w \<in> gpda.Lang I\<^sub>G\<close>}.
\end{proof}
\end{lemma}

And thus with Lemma~\ref{ipda.Lang_subst_Lang_G}:

\begin{theorem}\label{ipda.Lang_eq_Lang_G}
@{prop \<open>gpda.Lang I\<^sub>G = LangS G\<close>}
\qed
\end{theorem}

We have now defined a nondeterministic GPDA that works with items and accepts exactly its underlying 
language. With this IPDA definition, we can see one of the benefits of extending \<open>G\<close>: if we were to 
define the set of final states to be the set of all complete items of the form @{term \<open>[S \<rightarrow> \<alpha> \<cdot> ]\<close>},
the automaton could encounter a final state before the end of a computation. Since \<open>S'\<close> is in not 
on the RHS of any production, this scenario can not occur after the extension.\par

As a final remark, it is worth pointing out that our proof differs somewhat from that of
Wilhelm et al. Rather than of Lemma~\ref{derives_imp_completes}, they prove a special case 
thereof~\cite[p. 61]{Wilhelm}, namely the statement
\begin{quote}
\textit{For each derivation \<open>Prods G \<turnstile> [Nt A] \<Rightarrow> \<alpha> \<Rightarrow>* map Tm w\<close> with \<open>A :: 'n\<close>, 
\[ @{prop \<open>([A \<rightarrow> \<cdot> \<alpha>] # \<rho>, w @ v) \<turnstile>I* ([A \<rightarrow> \<alpha> \<cdot> ] # \<rho>, v)\<close>} \] 
for arbitrary \<open>\<rho> :: item list\<close> and \<open>v :: 't list\<close>.}
\end{quote}

However, this statement is too weak, as we will soon need the stronger lemma we have proved instead.\<close>

subsection \<open>Rightmost Chains\<close>

(*<*) 
end
context Extended_Cfg
begin 
(*>*)

text \<open>Wilhelm et al. informally assert that for a rightmost derivation 
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>, there exists a decomposition
of the form
\begin{equation}\label{WSH rm chain}
\begin{split}
\<open>Prods G'\<close>\ & \<open>\<turnstile> [Nt S'] \<Rightarrow>r \<alpha>\<^sub>1 @ Nt X\<^sub>1 # \<beta>\<^sub>1 \<Rightarrow>r* \<alpha>\<^sub>1 @ Nt X\<^sub>1 # map Tm v\<^sub>1\<close>\\
        & \<open>\<Rightarrow>r \<alpha>\<^sub>1\<alpha>\<^sub>2 @ Nt X\<^sub>2 # \<beta>\<^sub>2 @ map Tm v\<^sub>1\<close>\\ 
        & \<open>\<Rightarrow>r* ... \<Rightarrow>r* \<alpha>\<^sub>1 ... \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n ... v\<^sub>1)\<close>\\
        & \<open>\<Rightarrow>r (\<alpha>\<^sub>1 ... \<alpha>\<^sub>n) \<alpha>\<beta> @ map Tm (v\<^sub>n ... v\<^sub>1)\<close>.
\end{split}
\end{equation}
where \<open>X\<^sub>n = A\<close>. In the above expression, we omit most concatenation operators @{term \<open>(@)\<close>} for 
compactness. Instead, we denote concatenation by juxtaposition (such as in \<open>(\<alpha>\<^sub>1 ... \<alpha>\<^sub>n) \<alpha>\<beta>\<close> instead
of \<open>(\<alpha>\<^sub>1 @ ... @ \<alpha>\<^sub>n) @ \<alpha> @ \<beta>\<close>).

We now formalize this concept by defining \concept{rightmost chains} inductively. If sentential 
form \<open>\<alpha>\<close> reaches sentential form \<open>\<beta>\<close> with rightmost chain \<open>\<rho>\<close> under production set \<open>P\<close>, we write 
@{prop \<open>P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>\<close>}. For a fixed \<open>P\<close>, we define a \concept{reflexive} rule:
\begin{gather*}
@{thm rm_chain.refl}\\
\intertext{and a \concept{step} rule:}
@{thm [mode=Rule] rm_chain.step}
\end{gather*}

\begin{example}\label{ex:rm_chain}
By our definition of rightmost chains, we would write \eqref{WSH rm chain} as~\footnote{Note that we 
once more omit most concatenation operators, replacing them by juxtaposition.}
\begin{multline*}
\<open>P \<turnstile> [Nt S'] \<midarrow>[\<close> @{term \<open>sub X (n-1)\<close>}\ \<open>\<rightarrow> \<alpha>\<^sub>n \<cdot> Nt X\<^sub>n # \<beta>\<^sub>n] # [\<close> @{term \<open>sub X (n-2)\<close>}\ \<open>\<rightarrow>\<close>\ 
@{term \<open>sub \<alpha> (n-1)\<close>}\ \<open>\<cdot>\<close>\ 
  @{term \<open>Nt (sub X (n-1)) # (sub \<beta> (n-1))\<close>}]\\ 
  \<open># ... # [[S' \<rightarrow> \<alpha>\<^sub>1 \<cdot> Nt X\<^sub>1 # \<beta>\<^sub>1]]\<rightarrow>r* \<alpha>\<^sub>1 ... \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n...v\<^sub>1)\<close>.
\end{multline*}
\end{example}
We will now show the equivalence between rightmost chains and rightmost derivations.

\begin{lemma}\label{rm_chain_imp_derivers}
If @{prop \<open>P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>\<close>}, then @{prop \<open>P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>\<close>}
\begin{proof}
By induction on the structure of the rightmost chain.
\end{proof}
\end{lemma}

\begin{lemma}\label{derivern_singleton_imp_produced}
If @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # \<beta>\<close>}, there exists a step in the rightmost derivation 
where \<open>\<alpha>\<close> was fully derived, \<open>X\<close> was produced, and the string to the right of \<open>X\<close> derives \<open>\<beta>\<close>. More 
formally: there exist \<open>m :: nat\<close>, \<open>\<alpha>', \<alpha>'', \<beta>' :: syms\<close>, \<open>B :: 'n\<close> and \<open>v :: 't list\<close> such that
\begin{gather*}
@{prop \<open>m < Suc n\<close>}\\
@{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(m) \<alpha>' @ Nt B # map Tm v\<close>}\\
@{prop \<open>P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm v\<close>}\\
@{prop \<open>\<alpha> = \<alpha>' @ \<alpha>''\<close>}\\
@{prop \<open>P \<turnstile> \<beta>' @ map Tm v \<Rightarrow>r* \<beta>\<close>}.
\end{gather*}
\begin{proof}
We do a proof by strong induction on @{term \<open>Suc n\<close>} for arbitrary \<open>\<alpha>\<close> and \<open>\<beta>\<close>. We now distinguish
the two usual cases of \<open>n\<close>:

If \<open>n = 0\<close>, the implication holds for @{prop \<open>m = 0\<close>}, @{prop \<open>\<alpha>' = []\<close>}, @{prop \<open>v = []\<close>}, 
  @{prop \<open>\<alpha>'' = \<alpha>\<close>}, @{prop \<open>\<beta>' = \<beta>\<close>} and @{prop \<open>A = B\<close>}. 

For the case where @{prop \<open>n = Suc k\<close>} for some \<open>k\<close>, the derivation is of the form
\begin{multline}\label{prodd_stepn}
\<open>P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<gamma> @ map Tm v\<close>\\ 
\<open>= \<alpha> @ Nt X # \<beta>\<close>
\end{multline}

We now distinguish two further cases: \<open>X\<close> is in \<open>\<gamma>\<close>, meaning \<open>\<alpha>'\<close> is a prefix of \<open>\<alpha>\<close>, or 
\<open>X\<close> is in \<open>\<alpha>'\<close> and not in \<open>\<gamma>\<close>, meaning \<open>\<alpha>\<close> is a prefix of \<open>\<alpha>'\<close>.

If \<open>X\<close> is in \<open>\<gamma>\<close> and \<open>\<alpha>'\<close> is a prefix of \<open>\<alpha>\<close>, there exist \<open>\<delta>, \<zeta> :: syms\<close> such that \<open>\<gamma> = \<delta> @ Nt X # \<zeta>\<close>,
\<open>\<alpha> = \<alpha>' @ \<delta>\<close> and \<open>\<beta> = \<zeta> @ map Tm v\<close>. The implication then holds for \<open>m = n\<close>.

If \<open>X\<close> is in \<open>\<alpha>'\<close> and not in \<open>\<gamma>\<close>, there exist \<open>\<delta>, \<zeta> :: syms\<close> such that \<open>\<alpha>' = \<delta> @ Nt X # \<zeta>\<close>. From
\eqref{prodd_stepn} we then get
\[ @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(n) \<delta> @ Nt X # \<zeta> @ Nt B # map Tm v\<close>}. \]
Furthermore, since \<open>Suc k = n < Suc n\<close>, and due to the fact that our induction hypothesis holds for 
arbitrary \<open>\<alpha>\<close> and \<open>\<beta>\<close>, we can apply it for \<open>\<delta>\<close> and \<open>(\<zeta> @ Nt B # map Tm v)\<close>, by which the implication 
holds.
\end{proof}
\end{lemma}

\begin{lemma}\label{derivern_Suc_singleton_imp_rm_chain}
If @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v\<close>}, then there exists a rightmost chain of the 
form 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[B \<rightarrow> \<alpha>' \<cdot> Nt X # \<beta>] # \<rho>\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>}. \]
\begin{proof}
We do a proof by strong induction on @{term \<open>Suc n\<close>} for arbitrary \<open>\<alpha>, X,\<close> and \<open>v\<close>. Furthermore, 
we do a case distinction on \<open>n\<close>:

If \<open>n = 0\<close>, then 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[[A \<rightarrow> \<alpha> \<cdot> Nt X # map Tm v]]\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>}. \]

Otherwise, let \<open>n = Suc m\<close> for some \<open>m\<close>. From 
\[ @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v\<close>}, \]
there exist \<open>\<beta>, B, u,\<close> and \<open>\<gamma>\<close> such that 
\begin{gather}
\<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc m) \<beta> @ Nt B # map Tm u \<Rightarrow>r \<beta> @ \<gamma> @ map Tm u\<close>\label{der_rm.Suc_steps}\\
\intertext{and}
@{prop \<open>\<beta> @ \<gamma> @ map Tm u = \<alpha> @ Nt X # map Tm v\<close>}.\label{der_rm.bgu}
\end{gather}
Since \<open>Suc m = n < Suc n\<close>, by the induction hypothesis, \eqref{der_rm.Suc_steps} implies the
existence of some \<open>\<rho>\<close> such that 
\begin{equation}\label{der_rm.ih}
@{prop \<open>P \<turnstile> [Nt A] \<midarrow>\<rho>\<rightarrow>r* \<beta> @ Nt B # map Tm u\<close>}.
\end{equation}
Since \<open>B\<close> derives \<open>\<gamma>\<close> in the last step of the derivation, we now distinguish two more cases:
either \<open>X\<close> was produced by \<open>B\<close> in this final derivation step, meaning @{prop \<open>Nt X \<in> set \<gamma>\<close>}, 
or, if \<open>B\<close> did not produce \<open>X\<close>, \<open>X\<close> was already in the sentential form before the final step.

If @{prop \<open>Nt X \<in> set \<gamma>\<close>}, with \eqref{der_rm.bgu} we know there 
exist \<open>\<delta> :: syms\<close> and \<open>w :: 't list\<close> such that @{prop \<open>\<gamma> = \<delta> @ Nt X # map Tm w\<close>} and @{prop \<open>w @ u = v\<close>}. 
With \eqref{der_rm.ih} this implies
\begin{multline}\label{der_rm.True}
\<open>P \<turnstile> [Nt A] \<midarrow>[B \<rightarrow> \<delta> \<cdot> Nt X # map Tm w] # \<rho>\<rightarrow>r*\<close>\\ 
  @{prop \<open>\<beta> @ \<delta> @ Nt X # map Tm (w @ u) = \<beta> @ \<gamma> @ map Tm u\<close>}
\end{multline}
By \eqref{der_rm.bgu}, this is exactly the chain we were aiming to construct, completing the first 
case.

If, on the other hand, @{prop \<open>Nt X \<notin> set \<gamma>\<close>}, \eqref{der_rm.bgu} implies the existence of 
\<open>\<delta> :: syms\<close> and \<open>y, z :: 't list\<close> such that
\begin{gather}
\<open>\<beta> = \<delta> @ Nt X # map Tm y\<close>\label{der_rm.b_dec}\\
\<open>\<gamma> = map Tm z\<close>\label{der_rm.g_tms}\\
\<open>v = y @ z @ u\<close>.\label{der_rm.yzu}
\end{gather}
By Lemma~\ref{derivern_singleton_imp_produced}, \<open>n = Suc m\<close> implies the existence of some sentential 
form @{term \<open>\<alpha>' @ Nt C # map Tm w\<close>} such that
\begin{gather} 
\begin{multlined}\label{der_rm.prodd(1)}
\<open>P \<turnstile> [Nt A] \<Rightarrow>r(k) \<alpha>' @ Nt C # map Tm w\<close>\\
  \<open>\<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm w\<close>
\end{multlined}\\
\intertext{and}
\<open>P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm y @ Nt B # map Tm u\<close>\label{der_rm.prodd(2)}
\end{gather}
for \<open>\<delta> = \<alpha>' @ \<alpha>''\<close> and \<open>k < Suc m\<close>. Moreover, with \eqref{der_rm.Suc_steps}, \eqref{der_rm.g_tms}, 
and \eqref{der_rm.yzu}, we have 
\begin{equation}\label{der_rm.suffix_derivers_v}
@{prop \<open>P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm v\<close>}
\end{equation}
From \eqref{der_rm.bgu},\eqref{der_rm.b_dec}, \eqref{der_rm.g_tms}, and \eqref{der_rm.yzu} we also 
have 
\begin{equation} \label{der_rm.da}
  @{prop \<open>\<delta> = \<alpha>\<close>}.
\end{equation}

Since our induction hypothesis only holds for a nonzero number of steps, we need to do a case 
distinction on the \<open>k\<close> steps in \eqref{der_rm.prodd(1)}.

If \<open>k = 0\<close>, \eqref{der_rm.prodd(1)} implies that \<open>\<alpha>' = [] = w\<close> and \<open>A = C\<close>. This in turn implies
that \<open>\<delta> = \<alpha>''\<close>. With \eqref{der_rm.da} and \eqref{der_rm.suffix_derivers_v}, this implies 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[[A \<rightarrow> \<alpha>'' \<cdot> Nt X # \<beta>']]\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>}. \]

If, on the other hand, \<open>k = Suc j\<close> for some \<open>j\<close>, we can apply the induction hypothesis for \<open>C\<close>
with \eqref{der_rm.prodd(1)}, i.e., there exists some \<open>\<rho>\<close> such that
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>\<rho>\<rightarrow>r* \<alpha>' @ Nt C # map Tm w\<close>}. \]
We can then use \eqref{der_rm.prodd(1)}, \eqref{der_rm.suffix_derivers_v}, \eqref{der_rm.da}, and 
\<open>\<delta> = \<alpha>' @ \<alpha>''\<close> to show that 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[C \<rightarrow> \<alpha>'' \<cdot> Nt X # \<beta>'] # \<rho>\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>} \]
holds, finishing the proof.
\end{proof}
\end{lemma}

Wilhelm et al.~\cite[p. 107]{Wilhelm} furthermore claim that if @{term \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>', w)\<close>}
reaches the final configuration @{term \<open>([[S' \<rightarrow> \<cdot> [Nt S]]], [])\<close>}, then \<open>\<rho>'\<close> is of the form
\[ \<open>\<rho>' = [\<close> @{term \<open>sub X (n-1)\<close>}\ \<open>\<rightarrow> \<alpha>\<^sub>n \<cdot> Nt X\<^sub>n # \<beta>\<^sub>n] # ... # [[S' \<rightarrow> \<alpha>\<^sub>1 \<cdot> Nt X\<^sub>1 # \<beta>\<^sub>1]]\<close> \]
for some \<open>n \<ge> 0\<close> and \<open>X\<^sub>n = A\<close>~\footnote{We have adapted the original claim to our own notation for 
the sake of consistency and clarity.} It is worth noting that this structure of \<open>\<rho>'\<close> is essentially
the same as that of the item list in a rightmost chain (cf. Example~\ref{ex:rm_chain}). Therefore,
if some \<open>\<sigma> :: item list\<close> is part of some rightmost chain, we will be able to derive the same 
structure that Wilhelm et al. describe. We will now work towards proving that IPDA stacks reaching 
a final configuration have a stack that corresponds to some rightmost chain.\<close>

(*<*)
end
context Extended_Cfg
begin

interpretation I: ipda G IPDA 
  by (fact ipda_IPDA)

notation I.step (infix \<open>\<turnstile>I\<close> 55)
notation I.steps (infix \<open>\<turnstile>I*\<close> 55)
notation I.stepn ( \<open>_ \<turnstile>I'(_') _\<close> 55)

(*>*)

text\<open>
\begin{lemma}\label{reaches_final_imp_last_is_init_or_final}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])\<close>}, then the last element in
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>\<close>} is either @{term \<open>[S' \<rightarrow> \<cdot> [Nt S']]\<close>} or @{term I.final_state}.
\begin{proof}
By backwards induction on the length of the computation, making a case distinction on whether
the first step is shifting, expanding, or reducing in the transitive case.
\end{proof}
\end{lemma}

\begin{lemma}\label{step_reaches_final_imp_S}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> @ \<sigma>, u) \<turnstile>I (I.final_state # \<sigma>, v)\<close>},
then \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> = [[S \<rightarrow> \<alpha> \<cdot> ], [S' \<rightarrow> \<cdot> [Nt S]]]\<close>.
\begin{proof}
By case distinction on the three types of transition.
\end{proof}
\end{lemma}

\begin{lemma}\label{rm_chain_Cons_imp_prod_rightmost}
If @{prop \<open>P \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> Nt B # \<beta>] # \<rho>\<rightarrow>r* \<gamma>\<close>}, there exist \<open>\<delta> :: syms\<close> and \<open>u, v, w :: 't list\<close> 
such that @{prop \<open>\<gamma> = \<delta> @ Nt B # map Tm w\<close>}, @{prop \<open>P \<turnstile> \<beta> \<Rightarrow>r* map Tm u\<close>}, and @{prop \<open>w = u @ v\<close>}.
\begin{proof}
Trivial by rule inversion.
\end{proof}
\end{lemma}

\begin{lemma}\label{rm_chain_second_produces_hd}
If @{prop \<open>Prods G' \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> Nt B # \<beta>] # i # \<rho>\<rightarrow>r* \<gamma>\<close>},
then there exist \<open>X, \<alpha>',\<close> and \<open>\<beta>'\<close> such that \<open>i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']\<close>
\begin{proof}
By rule inversion, we know there exist \<open>\<alpha>' :: syms\<close> and \<open>v, u :: 't list\<close> where
\begin{gather}
@{prop \<open>\<gamma> = \<alpha>' @ \<alpha> @ Nt B # map Tm u @ map Tm v\<close>}\\
@{prop \<open>Prods G' \<turnstile> \<alpha>\<^sub>0 \<midarrow>i # \<rho>\<rightarrow>r* \<alpha>' @ Nt A # map Tm v\<close>}\label{rmc_snd_hd.step}\\
@{prop \<open>Prods G' \<turnstile> \<alpha>' @ Nt A # map Tm v \<Rightarrow>r \<alpha>' @ \<alpha> @ Nt B # \<beta> @ map Tm v\<close>}\\
@{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm u\<close>}
\end{gather}
The implication then follows from all these facts by doing a second rule inversion, this time on 
\eqref{rmc_snd_hd.step}.
\end{proof}
\end{lemma}

\begin{lemma}\label{ipda_reaches_final_imp_rm_chain}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])\<close>}, then either \mbox{@{prop \<open>\<rho> = []\<close>}},
or there exist \<open>\<sigma> :: item list\<close>, \<open>X :: 'n\<close> and \<open>\<alpha>', \<beta>', \<gamma> :: syms\<close> such that
\[ @{prop \<open>\<rho> = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'] # \<sigma>\<close>} \text{ and } @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<gamma>\<close>}. \]
\begin{proof}
We do a proof by backwards induction on the length of the computation of @{const I\<^sub>G} for arbitrary 
\<open>A, \<alpha>, \<beta>, \<rho>\<close>, and \<open>w\<close>.

The reflexive case implies directly that \<open>\<rho> = []\<close>.

For the transitive case, the computation is of the form
\begin{equation}\label{ipda_rmc.step}
\<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I ([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v) \<turnstile>I* ([\<close>@{term I.final_state}\<open>], [])\<close>
\end{equation}
for some \<open>B\<close>, \<open>\<gamma>\<close>, \<open>\<delta>\<close>, \<open>\<tau>\<close> and \<open>v\<close>. This is due to the fact that in all three types of transition, 
\<open>I\<^sub>G\<close> replaces a nonzero amount of topmost stack symbols by a nonempty list, meaning that a step can 
never lead to an empty stack. We can now apply the induction hypothesis on the shorter computation 
starting on @{term \<open>([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v)\<close>}, meaning \<open>\<tau>\<close> is either empty, or it is in some rightmost
chain as we already described.

If \<open>\<tau> = []\<close>, by Lemma~\ref{reaches_final_imp_last_is_init_or_final} we know that @{term \<open>[B \<rightarrow> \<gamma> \<cdot> \<delta>]\<close>}
is either the initial or final state. We can prove this item cannot be the initial state by 
contradiction using \eqref{ipda_rmc.step}. Therefore, @{term \<open>[B \<rightarrow> \<gamma> \<cdot> \<delta>]\<close>} must be the final state 
@{term I.final_state}, implying that @{prop \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] = [S \<rightarrow> \<alpha> \<cdot> ]\<close>} and 
@{prop [source] \<open>\<rho> = [S' \<rightarrow> \<cdot> [Nt S]] # []\<close>} by Lemma~\ref{step_reaches_final_imp_S} for \<open>\<sigma> = []\<close>. 
Therefore, \<open>\<rho>\<close> fulfills our claim.

For the second case, \<open>\<tau>\<close> has the structure
\begin{gather}\label{ipda_rm.ih}
@{prop \<open>\<tau> = [X \<rightarrow> \<alpha>' \<cdot> Nt B # \<beta>'] # \<sigma>\<close>}\\  
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<tau>\<rightarrow>r* \<zeta>\<close>}
\end{gather}
for some \<open>X :: 'n\<close>, \<open>\<alpha>', \<beta>, \<zeta> :: syms\<close> and \<open>\<sigma> :: item list\<close>. We can now do a case distinction on the 
step @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I ([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v)\<close>}.

If the transition is shifting, we have @{prop \<open>A = B\<close>} and @{prop \<open>\<rho> = \<tau>\<close>}. The implication holds by 
\eqref{ipda_rm.ih}.

If the transition is reducing, we know that 
\begin{equation}\label{ipda_rm.r}
@{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) = ([A \<rightarrow> \<alpha> \<cdot> []] # [B \<rightarrow> \<theta> \<cdot> Nt A # \<delta>] # \<tau>, w)\<close>},
\end{equation}
for some \<open>\<theta>\<close> where @{prop \<open>\<gamma> = \<theta> @ [Nt A]\<close>}, meaning that \<open>(B, \<theta> @ Nt A # \<delta>)\<close> is in \<open>Prods G'\<close>. By
Lemma~\ref{rm_chain_Cons_imp_prod_rightmost}, \eqref{ipda_rm.ih} implies that \<open>\<zeta>\<close> is of the form
\[ @{prop \<open>\<zeta> = \<zeta>' @ Nt B # map Tm u\<close>} \]
for some \<open>\<zeta>'\<close> and \<open>u\<close>. Moreover, since \<open>G'\<close> is reduced, there exists a \<open>v :: 't list\<close> that the string \<open>\<delta>\<close> can derive.  
With the fact that \<open>B\<close> produces \<open>\<theta> @ Nt A # \<delta>\<close>, we can extend the chain in \eqref{ipda_rm.ih} by the 
item @{term \<open>[B \<rightarrow> \<theta> \<cdot> Nt A # \<delta>]\<close>}, i.e.
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<midarrow>[B \<rightarrow> \<theta> \<cdot> Nt A # \<delta>] # \<tau>\<rightarrow>r*\<close> 
  \\\<open>\<zeta>' @ \<theta> @ Nt A # map Tm (v@u)\<close>
\end{multline*}
The implication therefore holds by \eqref{ipda_rm.r}.

If the transition is expanding, we have
\begin{equation}\label{ipda_rm.e}
 @{prop \<open>([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v) = ([B \<rightarrow> [] \<cdot> \<delta>] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w)\<close>}.
\end{equation}
If \<open>\<rho> = []\<close>, the implication holds directly. Otherwise, if \<open>\<rho> = i # \<sigma>\<close> for some \<open>i\<close> and \<open>\<sigma>\<close>, 
from \eqref{ipda_rm.ih} and \eqref{ipda_rm.e} we get
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>[A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<sigma>\<rightarrow>r* \<zeta>\<close>}. \]
Finally, by inversion of the step rule for rightmost chains, this implies the existence of some \<open>\<eta>\<close> 
such that
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<eta>\<close>},\] 
and by Lemma~\ref{rm_chain_second_produces_hd}, \<open>i\<close> is of the form @{prop \<open>i = [Z \<rightarrow> \<gamma>' \<cdot> Nt A # \<delta>']\<close>} 
for some \<open>Z, \<gamma>'\<close>, and \<open>\<delta>'\<close>. Together with the existence of \<open>\<eta>\<close>, this completes the proof.
\end{proof}
\end{lemma}

We have now formalized the notion of rightmost chains, proved their existence is equivalent to that
of generic rightmost derivations, and proved that every IPDA stack that reaches an accepting state 
has such a chain of items on the stack. With these chains, we are now able to describe a very 
well-behaved relation between the nonterminals directly to the right of the bullet and the 
nonterminal to the left of the arrow of the preceding item: for any two neighboring items
in the chain's item list 
\[ ...  \<open># [A \<rightarrow> \<alpha> \<cdot> \<beta>] # [B \<rightarrow> \<gamma> \<cdot> \<delta>] #\<close> ... \]
we know that @{prop \<open>hd \<delta> = Nt A\<close>}, meaning the LHS nonterminal of each item is produced in the 
successor item. Wilhelm et al. use these chains on multiple occasions only informally. By formalizing
them, we will be able in the future to induct on them more rigorously, which will be of utmost 
importance in the coming section.\<close>

section \<open>The Characteristic Finite Automaton and the Canonical \<open>LR(0)\<close> Automaton\<close>
(*<*)
notation (latex output) char_fa
  (\<open>\<^latex>\<open>\ensuremath{\mathrm{char}(G)}\<close>\<close>)

notation (latex output) "LR\<^sub>0"
  (\<open>\<^latex>\<open>\ensuremath{LR_0(G)}\<close>\<close>)

notation (latex output) "P\<^sub>0"
  (\<open>\<^latex>\<open>\ensuremath{P_0(G)}\<close>\<close>)


(*>*)

text \<open>In this section, we will show the relation between rightmost derivations and the IPDA in more 
detail, as well as the define finite automata that the canonical LR(0) parser will operate with.\<close>

text\<open>In order to construct our parser, we will first define an automaton that can determine possible
reductions. We again define a nondeterministic automaton, in this case an NFA, that we will call the  
\concept{characteristic finite automaton} to \<open>G\<close>. We base our finite automata on the formalization
thereof by Paulson~\<^cite>\<open>Paulson\<close>.\<close>

subsection \<open>The Characteristic Finite Automaton\<close>

text\<open>\begin{definition}[Characteristic finite automaton]
The characteristic finite automaton to \<open>G\<close> is the @{typ \<open>(('n, 't) sym, ('n, 't) item) nfa\<close>}:
\begin{multline*}
  @{const char_fa} = \<open>\<lparr>states = It G', init = {[S' \<rightarrow> [] \<cdot> [Nt S]]},\<close>\\
  \<open>final = completes (It G'), nxt = \<Delta>, eps = \<E>\<rparr>\<close>
\end{multline*}
with
% Fix style?
@{term [display, margin = 80] \<open>\<Delta>(q, a) = (case q of [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<Rightarrow> 
  if a = Y \<and> (X, \<alpha>@Y#\<beta>) \<in> Prods G' then {[X \<rightarrow> \<alpha>@[Y] \<cdot> \<beta>]}
  else {} | _ \<Rightarrow> {})\<close>}
and
\begin{multline*}
\<open>\<E> = {([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>])\<close>\\
  \<open>| X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G' \<and> (Y, \<gamma>) \<in> Prods G'}\<close>
\end{multline*}
\end{definition}

The characteristic finite automaton can therefore perform shifting and expanding transitions akin to 
those of the IPDA @{const I\<^sub>G}. Meanwhile, the @{const char_fa} shifting nonterminals corresponds to
reducing transitions in @{const I\<^sub>G}. @{const char_fa} can therefore reach an item in @{term \<open>It G\<close>} 
by read the concatenation of the prefixes that @{const I\<^sub>G} processed in order to reach this 
particular item, as explained by Wilhelm et al~\cite[p. 103]{Wilhelm}.

Wilhelm et al.~\cite[p. 104]{Wilhelm} present a theorem stating the equivalence of three statements 
as one of the main results in the \<open>LR(0)\<close> section of the book, Theorem 3.4.1, describing the relation 
between @{const char_fa}, rightmost derivations, and the IPDA. They make the following claim, which
we have adapted to match our own notation:

\begin{quote}
\textit{Let \<open>G\<close> be a CFG and \<open>\<gamma> :: syms\<close>. The following three statements are equivalent:
\begin{enumerate}
\item There exists a computation
\[ @{prop \<open>([S' \<rightarrow> \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
of the characteristic finite automaton @{const char_fa}.
\item There exists a rightmost derivation 
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w\<close>\\
  \<open>\<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>
\end{multline*}
with @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}.
\item There exists a computation
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>} \]
of the IPDA @{const \<open>I\<^sub>G\<close>} such that @{prop \<open>\<gamma> = hist (rev \<rho>) @ \<alpha>\<close>} holds.
\end{enumerate}}
\end{quote}

It is worth noting that we have modified the order of the statements, since in the book there
is a mismatch between the numbering of each statement in the claim and in the proof. We will now
refer to these claims exclusively as we have numbered them.

Wilhelm et al. prove the claim by a circular proof of the form \<open>(1) \<Longrightarrow> (2) \<Longrightarrow> (3) \<Longrightarrow> (1)\<close>. This 
claim, however, is not a consequence of the chain of implications that was proved; we will now
look at each implication more closely. There are certain typographic errors in the proofs which we 
will not address; we infer the author's intention in such cases. 

Implication \<open>(1) \<Longrightarrow> (2)\<close> uses existing constants \<open>S'\<close> and \<open>S\<close>, and fixes variables \<open>\<gamma>\<close> and
@{prop \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> It G'\<close>}. The conclusion then shows that there exist some \<open>\<gamma>' :: syms\<close> and
\<open>w :: 't list\<close> for which the rightmost derivation exists and @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}. The proof itself
is flawed: the authors induct on the number of \<open>\<epsilon>\<close>-transitions instead, and the 
induction hypothesis, which is only established if the remaining input is @{term \<open>[]\<close>}, is
applied on a configuration with nonempty remaining input. Furthermore, the base case does not consider 
the scenario where @{const char_fa} reads \<open>Nt S\<close> from the input before making any \<open>\<epsilon>\<close>-transitions. 
We will later prove the implication in a different manner. 

Implication  \<open>(2) \<Longrightarrow> (3)\<close> fixes \<open>\<gamma>', A, \<alpha>, \<beta>,\<close> and \<open>w\<close>, and shows the existence of some \<open>\<rho>\<close>. Note
that the conclusion of \<open>(1) \<Longrightarrow> (2)\<close> proved only an existentially quantified \<open>w\<close>; this is an 
important distinction that we will address later.
In the statements @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>} and @{prop \<open>\<gamma> = hist (rev \<rho>) @ \<alpha>\<close>}, variable \<open>\<gamma>\<close> is completely
meaningless; it bears no relation to the \<open>\<gamma>\<close> fixed in (1) since no \<open>\<gamma>\<close> is defined in (2) nor in (3). 
Therefore, this can be simplified to 
@{prop \<open>\<gamma>' = hist (rev \<rho>)\<close>}. Furthermore, the proof for this implication assumes that 
\[ @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v\<close>} \]
for some \<open>v :: 't list\<close>. It is not clear what the statement intends to say, and this assumption
might need to be included in statement (2) for it to be correct, depending on what was meant 
originally: since \<open>w\<close> is fixed, the statement of the existence of the IPDA computation seems to 
be stating that the computation holds for the same fixed \<open>w\<close>, but this is not true; as we will see, 
the statement holds for input @{term \<open>v@w\<close>}, where \<open>v\<close> is again the word derived by \<open>\<beta>\<close>. If \<open>w\<close> is 
meant to be existentially quantified in the conclusion, this is not a problem, but this is not made
clear by the authors. The proof of the statement is also incorrect: it uses the book's informal
equivalent of our formalized rightmost chains, but states that one proves by induction that a 
configuration with topmost stack symbol 
\[ @{term \<open>[sub X (n-1) \<rightarrow> \<alpha>\<^sub>n \<cdot> Nt A # \<beta>\<^sub>n]\<close>} \]
and input \<open>w\<close> reaches the final configuration~\footnote{the authors naturally state the structure of
the entire stack, but only the topmost symbol is relevant for our argument.}. However, this 
configuration would first push the initial item @{term \<open>[A \<rightarrow> \<cdot> \<alpha> @ \<beta>]\<close>} onto the stack (this is the 
only possibility based on our assumptions about \<open>A\<close>), and since we haven't made any assumptions 
regarding \<open>\<alpha>\<close>, we cannot make any further claims. It is therefore necessary for the topmost stack 
item to be @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} to be able to make any claims about the computation.

The proof of the final implication is fundamentally correct; it fixes @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} as 
usual, as well as \<open>\<rho>\<close> and \<open>w\<close>. The conclusion does not contain any new variables since \<open>\<gamma>\<close> is just 
a shorthand for @{term \<open>hist (rev \<rho>) @ \<alpha>\<close>} in practice. However, the main issue with this proof is,
as we previously mentioned, that the \<open>w\<close> in the premise is not in the conclusion at all. In order 
to prove the equivalence of (2) and (3), we need the statement \<open>(2) \<Longrightarrow> (3)\<close>, which we have already
proved, and \<open>(3) \<Longrightarrow> (2)\<close>, which we prove through (1), i.e., \<open>(3) \<Longrightarrow> (1) \<Longrightarrow> (2)\<close>. However, since
the original \<open>w\<close> in (3) is lost in (1), it is a new existentially quantified \<open>w\<close> in (2). This means
that the statements (2) and (3) are not equivalent for the same \<open>w\<close>, as it reads in the book, 
but for two different existentially quantified words \<open>u\<close> and \<open>v\<close>. However, the 
main results that we need from the theorem to formalize our parser still hold after addressing 
these errors. A corrected version Theorem 3.4.1:

\begin{theorem}\label{char_derivers_ipda_iffs}[Equivalences between @{const char_fa}, rightmost derivations, and @{const I\<^sub>G}]
The following statements are equivalent:
\begin{enumerate}
\item There exists a computation 
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
of the characteristic finite automaton @{const char_fa}.
\item There exists a rightmost derivation
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm u\<close>\\
  \<open>\<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm u\<close>.
\end{multline*}
for some \<open>u :: 't list\<close>.
\item There exists a computation 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v) \<turnstile>I* ([I.final_state], [])\<close>} \]
of the IPDA @{const I\<^sub>G} for some \<open>\<rho> :: item list\<close> and \<open>v :: 't list\<close> such that 
@{prop \<open>hist (rev \<rho>) = \<gamma>\<close>} holds.
\end{enumerate}
\end{theorem}

We will now work towards proving this theorem. We denote @{const char_fa} transition steps by \<open>\<turnstile>c\<close>, 
and as usual, the reflexive transitive closure by \<open>\<turnstile>c*\<close>, and \<open>n\<close>-length computations by \<open>\<turnstile>c(n)\<close>. 
We first need two lemmas about @{const char_fa}:

\begin{lemma}\label{char_reachable_imp_substring}
If @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], \<delta>)\<close>}, there exists a \<open>\<zeta>\<close> such that 
@{prop \<open>\<gamma> = \<zeta> @ \<alpha> @ \<delta>\<close>}.
\begin{proof}
By induction on the length of the computation, making a case distinction on whether the last step is 
a read transition or an \<open>\<epsilon>\<close>-transition in the inductive step.
\end{proof} 
\end{lemma}

And now we begin our circular proof:

\begin{lemma}[Step 1]\label{char_imp_derivers}
If there exists a computation of @{const char_fa}
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>}, \]
Then there exist \<open>\<gamma>' :: syms\<close> and \<open>w :: 't list\<close> for which there is a rightmost derivation of the
form
\[ \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w \<Rightarrow> \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close> \]
with @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}.
\begin{proof}
We do a proof by induction over the length \<open>n\<close> of the computation for arbitrary \<open>\<gamma>, \<alpha>, \<beta>, \<close> and \<open>A\<close>. 

If \<open>n = 0\<close> the implication holds trivially by reflexivity.

If \<open>n = Suc m\<close> for some \<open>m\<close>, we do a case distinction on the last step of the computation.

If the last step is a read transition, it is of the form
\[ @{prop \<open>([A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>], [Y]) \<turnstile>c ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
for \<open>\<alpha>'\<close> with @{prop \<open>\<alpha> = \<alpha>' @ [Y]\<close>}. With Lemma~\ref{char_reachable_imp_substring}, this implies 
that @{prop \<open>\<gamma> = \<delta> @ \<alpha>' @ [Y]\<close>} for some \<open>\<delta>\<close>, and therefore
\[ @{prop\<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha>') \<turnstile>c(m) ([A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>], [])\<close>}. \]
By the induction hypothesis, this implies
\begin{multline*} 
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w\<close>\\ 
\<open>\<Rightarrow> \<delta>  @ \<alpha>' @ Y # \<beta> @ map Tm w\<close>,
\end{multline*}
and the implication holds with @{prop \<open>\<alpha> = \<alpha>' @ [Y]\<close>}.

If the last step is an \<open>\<epsilon>\<close>-transition, the last step is of the form 
\[ @{prop \<open>([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], []) \<turnstile>c ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>}, \]
which implies that @{prop \<open>\<alpha> = []\<close>}. By the IH we then have
\begin{multline}\label{char_der.ih}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt X # map Tm w\<close>\\
  \<open>\<Rightarrow>r \<gamma>' @ \<alpha>' @ Nt A # \<beta>' @ map Tm w\<close>
\end{multline}
with @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>'\<close>}. Moreover, since \<open>G'\<close> is reduced, there exists a \<open>v :: 't list\<close> such that
@{prop \<open>Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm v\<close>}.
From this and \eqref{char_der.ih} we have
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm (v@w)\<close>\\ 
\<open>\<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm (v@w)\<close>.
\end{multline*}
This completes the proof by the fact that @{prop \<open>\<alpha> = []\<close>}.
\end{proof}
\end{lemma}

We now move on towards proving the second step, for which we first show an auxiliary lemma.

\begin{lemma}\label{deriver_imp_IPDA_comp}
If @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r \<alpha>@\<beta>\<close>} and @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v\<close>}, there exists a 
computation
\[ @{prop \<open>([[S' \<rightarrow> \<alpha> \<cdot> \<beta>]], v) \<turnstile>I* ([I.final_state], [])\<close>} \]
\begin{proof}
Since the only possible production for \<open>S'\<close> is \<open>(S',[Nt S])\<close>, we have @{prop \<open>[Nt S] = \<alpha> @ \<beta>\<close>}.
The proof is then trivial by distinguishing the cases where \<open>\<alpha> = [Nt S]\<close> and \<open>\<beta> = []\<close>, and vice-versa,
using Theorem~\ref{ipda.Lang_eq_Lang_G}.
\end{proof}
\end{lemma}

\begin{lemma}[Step 2]\label{derivers_imp_ipda}
If there exists a rightmost derivation 
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm w\<close>\\ 
\<open>\<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm w\<close>
\end{multline*}
with @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v\<close>},
then there exists an @{const IPDA} computation 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v@w) \<turnstile>I* ([I.final_state], [])\<close>} \]
with @{prop \<open>hist (rev \<rho>) = \<gamma>\<close>}.
\begin{proof}
We begin by distinguishing the cases where @{prop \<open>n = 0\<close>} and @{prop \<open>n > 0\<close>}.

If @{prop \<open>n = 0\<close>}, we have @{prop \<open>S' = A\<close>}, \<open>\<gamma> = w = []\<close>, and @{prop \<open>\<alpha>@\<beta> = [Nt S]\<close>}. The 
computation then exists by Lemma~\ref{deriver_imp_IPDA_comp}.

If @{prop \<open>n > 0\<close>}, Lemma~\ref{derivern_Suc_singleton_imp_rm_chain} implies the existence of some
\<open>\<rho>\<close> with
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<gamma> @ Nt A # map Tm w\<close>}. \]
We can now do an induction on \<open>\<rho>\<close> for arbitrary \<open>\<gamma>, \<alpha>, \<beta>, A, w,\<close> and \<open>v\<close>, akin to the proof by 
Wilhelm et al.

If @{prop \<open>\<rho> = []\<close>}, we again have @{prop \<open>S' = A\<close>}, \<open>\<gamma> = w = []\<close>, and @{prop \<open>\<alpha>@\<beta> = [Nt S]\<close>}, and 
the proof is analogous to the case of @{prop \<open>n = 0\<close>}.

If @{prop \<open>\<rho> = i # \<sigma>\<close>} for some \<open>i\<close> and \<open>\<sigma>\<close>, by rule inversion we know that 
\begin{equation}\label{der_ipda.i}
@{prop \<open>i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']\<close>}
\end{equation}
for some \<open>X\<close>, \<open>\<alpha>'\<close>, \<open>A\<close> and \<open>\<beta>'\<close>. Furthermore, the chain is such that
\begin{gather*}
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<sigma>\<rightarrow>r* \<alpha>'' @ Nt X # map Tm v'\<close>}\\
\intertext{and}
@{prop \<open>Prods G' \<turnstile> \<alpha>'' @ Nt X # map Tm v' \<Rightarrow>r \<alpha>'' @ \<alpha>' @ Nt A # \<beta>' @ map Tm v'\<close>}
\end{gather*}
with @{prop \<open>Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm u\<close>}, @{prop \<open>u @ v' = w\<close>}, and @{prop \<open>\<alpha>'' @ \<alpha>' = \<gamma>\<close>}
for some \<open>\<alpha>'', u,\<close> and \<open>v'\<close>. By the IH, all this implies the existence of some \<open>\<tau>\<close> where
\begin{equation*}
@{prop \<open>([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<tau>, u@v') \<turnstile>I* ([I.final_state], [])\<close>}\\
\end{equation*}
and @{prop \<open>hist (rev \<tau>) = \<alpha>''\<close>}.

Lastly, we can show with Lemma~\ref{derives_imp_completes} and our assumption that \<open>\<beta>\<close> derives 
\<open>map Tm v\<close> that \<open>I\<^sub>G\<close> with configuration 
\[ @{term \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'] # \<tau>, v @ w)\<close>} \]
reaches @{term \<open>([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<tau>, u@v')\<close>}, completing the proof.
\end{proof}
\end{lemma}

It is worth noting that, as opposed to Wilhelm et al., we only assume 
@{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v\<close>} for the above lemma, since specifying this as a rightmost 
derivation makes no difference. We will now prove further properties about @{const char_fa} which 
we will need for the third step.

\begin{lemma}\label{reaches_final_imp_completes}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I(n) ([I.final_state], [])\<close>} holds, 
there exist a \<open>v :: 't list\<close> and \<open>i, j :: nat\<close> such that
\begin{multline*} 
\<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I(i) ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v)\<close>\\
\<open>\<turnstile>I(j) ([\<close>@{term I.final_state}\<open>], [])\<close>
\end{multline*}
and @{prop \<open>i + j = n\<close>}.
\begin{proof}
We do a proof by strong induction on \<open>n\<close> for arbitrary \<open>A, u, \<alpha>, \<beta>,\<close> and \<open>\<rho>\<close>.

If \<open>n = 0\<close>, the implication is trivial.

If \<open>n = Suc m\<close> for some \<open>m\<close>, we do a case distinction on the first step of the computation. 

If the first step is a shifting or a reducing transition, the implication holds by the induction
hypothesis.

If the first step is an expanding transition, there exist \<open>Y :: 'n\<close> and \<open>\<gamma> :: syms\<close> with
\<open>\<beta> = Nt Y # \<gamma>\<close> and
\begin{multline*}
\<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I ([Y \<rightarrow>  \<cdot> \<gamma>] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u)\<close>\\
  \<open>\<turnstile>I(m) ([\<close>@{term I.final_state}\<open>], [])\<close>.
\end{multline*}

By the IH, this implies the existence of some \<open>v :: 't list\<close> and \<open>i, j :: nat\<close> with 
\begin{multline*}
\<open>([Y \<rightarrow>  \<cdot> \<gamma>] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I(i) ([Y \<rightarrow> \<gamma> \<cdot> ] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v)\<close>\\
  \<open>\<turnstile>I(j) ([\<close>@{term I.final_state}\<open>], [])\<close>
\end{multline*}
and \<open>i + j = m\<close>. With the fact that \<open>\<beta> = Nt Y # \<gamma>\<close>, the first step of the computation
\[ \<open>([Y \<rightarrow> \<gamma> \<cdot> ] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v) \<turnstile>I(j) ([\<close>@{term I.final_state}\<open>], [])\<close> \]
is invariably a reducing transition, and since the resulting configuration reaches the accepting 
configuration in \<open>j - 1 < n\<close> steps, we can use the IH again to finish the proof.
\end{proof}
\end{lemma}

\begin{lemma}\label{char_steps_consume}
If @{prop \<open>(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'\<close>}, @{const char_fa} computes
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>], \<beta> @ \<delta>) \<turnstile>c* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>], \<delta>)\<close>} \]
for any \<open>\<delta>\<close>.
\begin{proof}
Trivial by induction on \<open>\<beta>\<close> for arbitrary \<open>\<alpha>\<close>.
\end{proof}
\end{lemma}

And finally, we can prove the final step.

\begin{lemma}[Step 3]\label{ipda_imp_char}
If there exists a computation of \<open>I\<^sub>G\<close>
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])\<close>}, \]
then there also exists a @{const char_fa} computation of the form
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>}. \]
\begin{proof}
We induct on \<open>\<rho>\<close> for arbitrary \<open>A, \<alpha>, \<beta>\<close> and \<open>w\<close>.

If \<open>\<rho> = []\<close>, @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} is either the initial or the final state by 
Lemma~\ref{reaches_final_imp_last_is_init_or_final}. The implication can then be proved by 
distinguishing these two cases.

If \<open>\<rho> = i # \<sigma>\<close>, we know by Lemma~\ref{ipda_reaches_final_imp_rm_chain} that
\begin{gather}\label{ipda_char.chain}
@{prop \<open>i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']\<close>}\\
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>i # \<sigma>\<rightarrow>r* \<gamma>\<close>}
\end{gather}
For some \<open>X :: 'n\<close>, and \<open>\<alpha>', \<beta>, \<gamma> :: syms\<close>. Furthermore, by Lemma~\ref{reaches_final_imp_completes}, 
our initial assumption of the accepting computation implies the existence of some \<open>v\<close> with
\[ @{prop \<open>([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<sigma>, v) \<turnstile>I* ([I.final_state], [])\<close>} \]
Since in the LHS of this computation the topmost stack item is complete, the only possible first step
is a reducing transition, meaning 
\begin{multline}\label{ipda_char.red}
@{prop \<open>([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<sigma>, v) \<turnstile>I ([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<sigma>, v)\<close>}\\
  \<open>\<turnstile>I*\<close>\ @{term \<open>([I.final_state], [])\<close>}
\end{multline}
by \eqref{ipda_char.chain}. With the IH, and substituting @{prop \<open>\<rho> = i # \<sigma>\<close>} and 
\eqref{ipda_char.chain}, we now have
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ [Nt A]) \<turnstile>c* ([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'], [])\<close>}. \]
By a case distinction on the final step of this computation, we know that the initial configuration
reaches @{term \<open>([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], [Nt A])\<close>} immediately before the final step. Since only the
prefix @{term \<open>hist (rev \<rho>)\<close>} of the input is consumed, the computation is independent from the
remaining string. Therefore, the computation
\begin{equation}\label{ipda_char.calc}
@{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ \<alpha>) \<turnstile>c* ([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], \<alpha>)\<close>}
\end{equation}
also exists. Furthermore \eqref{ipda_char.red} implies that \mbox{@{term \<open>(A, \<alpha> @ \<beta>) \<in> Prods G'\<close>}} 
by the definition of the \<open>I\<^sub>G\<close> transition relations. Therefore, \eqref{ipda_char.calc} continues with
\[ \<open>... \<turnstile>c ([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>], \<alpha>)\<close>. \]
The RHS can then reach our target configuration by Lemma~\ref{char_steps_consume}, completing the
proof. Along with Lemmas~\ref{char_imp_derivers} and \ref{derivers_imp_ipda},  
this also completes the proof of Theorem~\ref{char_derivers_ipda_iffs}.
\end{proof}
\end{lemma}

We now define the notion of \concept{reliable prefixes}:

\begin{definition}[Reliable prefix]
\<open>\<gamma>\<close> is a reliable prefix for item @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} if there exists a rightmost derivation 
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w\<close>\\ 
  \<open>\<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>
\end{multline*}
such that @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}. Alternatively, we say that the item @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} is 
\concept{valid} for \<open>\<gamma>\<close>. We therefore also define the set of all valid items for \<open>\<gamma>\<close>:
\[ @{thm valids_def}. \]
\end{definition}

\begin{theorem}\label{char_eq_reliable_prefix}[Equivalence of @{const char_fa} computations and reliable prefixes]
There exists a @{const char_fa} computation
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
if and only if @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} is valid for \<open>\<gamma>\<close>.
\begin{proof}
This is a consequence of Lemmas~\ref{char_imp_derivers}, \ref{derivers_imp_ipda}, and 
\ref{ipda_imp_char}, using the fact that since \<open>G'\<close> is reduced, any sentential form derived from 
@{term \<open>S'\<close>}, or a substring thereof, derives some \<open>v :: 't list\<close>.
\end{proof}
\end{theorem}

By this Theorem, we get two more interesting results:

\begin{corollary}
@{const char_fa} accepts exactly the set of reliable prefixes to complete items.
\qed
\end{corollary}

\begin{lemma}\label{char_fa_nextl_is_valids}
The set of states reachable by @{const char_fa} after reading \<open>\<gamma>\<close> is exactly @{term \<open>valids \<gamma>\<close>}.
\qed
\end{lemma}\<close>

subsection \<open>The Canonical \<open>LR(0)\<close> Automaton\<close>

text\<open>Now that we have defined @{const char_fa} and proved several useful properties, we can finally
define a deterministic automaton that our parser can use. Since @{const char_fa} is an NFA, we 
define the \concept{canonical \<open>LR(0)\<close> automaton} @{const LR\<^sub>0} as the @{typeof LR\<^sub>0} resulting from 
the powerset construction restricted to reachable states. The automaton is once more defined using Paulson's 
theory~\<^cite>\<open>Paulson\<close>. We now show some properties we will need in our parser.

\begin{lemma}\label{state_imp_valids}
For every state @{prop \<open>q \<in> dfa.states LR\<^sub>0\<close>}, there exists a \<open>\<gamma> :: syms\<close> such that 
@{prop \<open>q = valids \<gamma>\<close>}.
\begin{proof}
By the definition of the powerset construction and Lemma~\ref{char_fa_nextl_is_valids}, we know
that the state @{const LR\<^sub>0} reaches after reading an input string \<open>\<alpha> :: syms\<close> is exactly @{term \<open>valids \<alpha>\<close>}.
Moreover, since we define the states of @{const LR\<^sub>0} to be the restricted to the reachable states resulting 
from the powerset construction of @{term char_fa}, we also know that there exists an input string \<open>\<gamma>\<close> 
such that @{const LR\<^sub>0} is in state \<open>q\<close> after reading \<open>\<gamma>\<close>; therefore, \<open>q = valids \<gamma>\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{char_fa_nxts_is_shifts}
For @{prop \<open>Q \<subseteq> It G'\<close>} holds the equality
\[ @{prop \<open>(\<Union>i \<in> Q. nfa.nxt char_fa i A) = {[X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q}\<close>}. \] 
\begin{proof}
We fix some @{prop \<open>i \<in> (\<Union>i \<in> Q. nfa.nxt char_fa i A)\<close>}, and we need to show that it is in the set 
on the RHS of the equation. Since \<open>i\<close> is in the union, there exists a \<open>j\<close> such that
@{prop \<open>i \<in> nfa.nxt char_fa j A\<close>}. Since the \<open>nxt\<close> relation is only defined for incomplete items, 
\<open>j\<close> must be of the form @{term \<open>[X \<rightarrow> \<alpha> \<cdot> B # \<beta>]\<close>}. 
@{prop \<open>i \<in> {[X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q}\<close>} then follows trivially by the 
definition of the \<open>nxt\<close> transition function.

For the converse, there exists some @{prop \<open>[X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q\<close>} for which 
@{prop \<open>i = [X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]\<close>}. With @{prop \<open>Q \<subseteq> It G'\<close>}, this implies @{prop \<open>i \<in> It G'\<close>},
and @{prop \<open>i \<in> (\<Union>i \<in> Q. nfa.nxt char_fa i A)\<close>} follows directly by definition of \<open>nxt\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{eps_reliable_preserved}
If \<open>i\<close> is valid for some \<open>\<gamma> :: syms\<close>, and for some item \<open>k\<close> 
\[ @{prop \<open>(i, k) \<in> (nfa.eps char_fa)\<^sup>*\<close>} \] 
holds, then \<open>k\<close> is also valid for \<open>\<gamma>\<close>.
\begin{proof}
The proof is by backward induction on the number of \<open>\<epsilon>\<close>-transition steps using 
Theorem~\ref{char_eq_reliable_prefix}.
\end{proof}
\end{lemma}

\begin{lemma}\label{dfa_LR0_nxt_is_epsclo_of_shift}
For any state of @{const LR\<^sub>0} @{prop \<open>Q\<close>} and a symbol \<open>Y\<close>, 
@{term \<open>dfa.nxt LR\<^sub>0 Q Y\<close>} is equivalent to the set
\[ @{term \<open>char_fa.epsclo {[X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> Q}\<close>} \]
where @{term \<open>char_fa.epsclo P\<close>} denotes the \<open>\<epsilon>\<close>-closure of set \<open>P\<close> for @{const char_fa}.
\begin{proof}
Follows by the definition of the \<open>nxt\<close> function of the DFA resulting from the powerset construction,
as well as Lemma~\ref{char_fa_nxts_is_shifts}.
\end{proof}
\end{lemma}

\begin{lemma}\label{nxt_dfa_LR0_shift_is_valids_app}
If @{prop \<open>valids \<gamma> \<in> dfa.states LR\<^sub>0\<close>}, then
\[ @{prop \<open>dfa.nxt LR\<^sub>0 (valids \<gamma>) X = valids (\<gamma> @ [X])\<close>} \]
\begin{proof}
By Lemma~\ref{dfa_LR0_nxt_is_epsclo_of_shift}, @{term \<open>dfa.nxt LR\<^sub>0 (valids \<gamma>) X\<close>} is equivalent to 
the set
\[ @{term \<open>char_fa.epsclo {[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]|A \<alpha> \<beta>. [A \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> valids \<gamma>}\<close>}. \]
We will abbreviate this set as \<open>\<E>\<close>.

First, we will show that \<open>\<E>\<close> is a subset of @{term \<open>valids (\<gamma> @ [X])\<close>} by 
Lemma~\ref{eps_reliable_preserved}.

We now show that @{term \<open>valids (\<gamma> @ [X])\<close>} is a subset of \<open>\<E>\<close> to complete the proof.

We assume @{prop \<open>i \<in> valids (\<gamma> @ [X])\<close>}, which means that either
\<open>i\<close> is a complete item, or a incomplete item of the form @{term \<open>[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]\<close>}.
We now distinguish these two cases.

If \<open>i\<close> is complete, we know it is a reachable state of @{const char_fa}. We show by induction on the 
length of the @{const char_fa} computation from the initial state to \<open>i\<close> that there exists an item 
@{term \<open>[Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>]\<close>} such that
\begin{equation*}
\<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c* ([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], []) \<turnstile>c* (i, [])\<close>
\end{equation*}
We can then show that @{prop \<open>i \<in> \<E>\<close>} by Theorem~\ref{char_eq_reliable_prefix} and the fact
that @{prop \<open>([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], i) \<in> (nfa.eps char_fa)\<^sup>*\<close>}, using Lemma~\ref{eps_reliable_preserved}
once again.
\end{proof}
\end{lemma}

As is the case with any DFA resulting from the powerset construction of an NFA, the canonical 
\<open>LR(0)\<close> automaton, working on sets of context-free items, effectively navigates all possible
NFA computations simultaneously, thereby achieving deterministic behavior. Furthermore, by 
Lemmas~\ref{state_imp_valids} and \ref{nxt_dfa_LR0_shift_is_valids_app}, since all @{const LR\<^sub>0} states are 
sets of valid items, and @{const LR\<^sub>0} transitions are equivalent to appending a symbol to a reliable prefix 
shared by all the items in the current state, we can use the canonical \<open>LR(0)\<close> automaton to determine 
in parallel all the items one could possibly be processing given what has already been derived, and 
by the presence of complete items, detect positions for reduction, as we will now see in the 
definition of our parser.\<close>

section \<open>The Canonical \<open>LR(0)\<close> Parser\<close>
(*<*)
interpretation P0: gpda P\<^sub>0
  by (fact gpda_P0)

notation P0.step (infix \<open>\<turnstile>P\<close> 55)
notation P0.steps (infix \<open>\<turnstile>P*\<close> 55)
notation P0.stepn (\<open>_ \<turnstile>P'(_') _\<close> 55)
(*>*)

subsection \<open>Definition\<close>

text\<open>
\begin{definition}[Canonical \<open>LR(0) parser\<close>]
Let @{term \<Delta>\<^sub>G} be the transition relation of the canonical \<open>LR(0)\<close> automaton @{const LR\<^sub>0}, 
\<open>q\<^sub>0\<close> the initial state of @{const LR\<^sub>0}, \<open>Q\<close> the set of states of @{const LR\<^sub>0}, and \<open>f\<close> the singleton 
set @{term \<open>{[S' \<rightarrow> [] \<cdot> []]}\<close>}.
The \concept{canonical LR(0) parser} to the CFG \<open>G\<close> is the @{typeof P\<^sub>0}
\[ @{const P\<^sub>0} = @{term \<open>\<lparr>states = Q \<union> {f}, init = q\<^sub>0, final = {f}, nxt = \<Delta>\<^sub>0, eps = \<E>\<rparr>\<close>}. \]
\end{definition}

In a similar manner to the IPDA, we define three types of transitions, two of which are in the
transition relation \<open>eps\<close>:
\begin{enumerate}
\item A \concept{reading} transition takes place when the parser reads an input symbol \<open>a\<close> and pushes 
the successor state @{term \<open>\<Delta>\<^sub>G q (Tm a)\<close>} onto the stack, where \<open>q\<close> is the current state. This 
transition takes place only if the successor state is not empty. Therefore, we define our \<open>nxt\<close> 
relation via \<open>\<Delta>\<^sub>0\<close>:
\[ @{prop \<open>\<Delta>\<^sub>0 = {([q], a, \<Delta>\<^sub>G q (Tm a) # [q])|q a. q \<in> Q \<and> \<Delta>\<^sub>G q (Tm a) \<noteq> {}}\<close>}. \] 
\item A \concept{reducing} transition occurs when the current state contains a complete
item @{term \<open>[X \<rightarrow> \<alpha> \<cdot> ]\<close>}. If this is the case, the parser first pops the first @{term \<open>length \<alpha>\<close>} 
items off the stack, and pushes the successor state under \<open>X\<close> onto the stack. In other words, the 
parser replaces the topmost stack list \<open>[q\<^sub>1, q\<^sub>2, ..., \<close> @{term \<open>sub q (length \<alpha>)\<close>} \<open>, q]\<close> by 
@{term \<open>[\<Delta>\<^sub>G q (Nt X), q]\<close>}. Formally we define these transitions by the set
\begin{multline*}
  \<open>{let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, \<Delta>\<^sub>G q (Nt X) # [q])\<close>\\
      \<open>| q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> Q \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q\<^sub>n\<close>\\ 
      \<open>\<and> length \<alpha> = length qs \<and> X \<noteq> S'}.\<close> 
\end{multline*}
\item Lastly, \concept{finishing} transitions reduce the complete item @{term \<open>[S' \<rightarrow> [Nt S] \<cdot> ]\<close>}. 
Reducing \<open>S'\<close> in the conventional sense is not possible; therefore, the finish transition signals 
that the parser has successfully reduced the processed input to the start symbol, and it does so by 
reducing the topmost state to the singleton state @{term \<open>{f}\<close>} if the second to last state is \<open>q\<^sub>0\<close>.
Finish transitions therefore correspond to the set 
\[ @{term \<open>{([q, q\<^sub>0], [f])|q. q \<in> Q \<and> [S' \<rightarrow> [Nt S] \<cdot> []] \<in> q}\<close>}. \]
\end{enumerate}
The set \<open>\<E>\<close> is therefore defined as the union of the sets for reduce and finish transitions. 

Our definition of @{const P\<^sub>0} is very similar to that of Wilhelm et al., except that we, as we did when
defining \<open>I\<^sub>G\<close>, restrict the elements of the transition relations to elements of \<open>Q\<close> explicitly
to overcome the same problem we had in the IPDA section. In this case, however, this has one more
benefit: since \<open>Q\<close> is actually a subset of the states of @{const P\<^sub>0}, by restricting our transition functions
to \<open>Q\<close> only, instead of @{term \<open>Q \<union> {f}\<close>}, our transition relations are more well-defined, since we
guarantee that every state that gets passed to the @{const LR\<^sub>0} transition function is a state in @{const LR\<^sub>0}. A 
second detail we added is the condition @{prop \<open>X \<noteq> S'\<close>} in the reduce transition relation. This 
could lead to nondeterministic behavior, since the finish transition condition 
@{prop \<open>[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q\<close>} also implies the reduce transition condition 
@{prop \<open>[X \<rightarrow> \<alpha> \<cdot> []] \<in> q\<^sub>n\<close>}. Restricting reduce transitions only for items fulfilling this 
property causes reduce and finish transitions to be mutually exclusive, avoiding this problem.\<close>

subsection \<open>\<open>LR(0)\<close>-Adequate and Inadequate States\<close>

text \<open>Even though our modified @{const P\<^sub>0} definition circumvents the issue between reduce and finish 
transitions we described before, nondeterminism is still a problem in several other cases. We 
define two types of \concept{conflicts} that can be present in parser states which can lead to 
nondeterministic behavior, as defined by Wilhelm et al.~\cite[p. 110]{Wilhelm}:

\begin{definition}[Shift-reduce/reduce-reduce conflicts and LR(0) inadequacy]
Let \<open>q\<close> be a state of @{const P\<^sub>0}. We say \<open>q\<close> has a \concept{shift-reduce conflict} if it allows for 
@{const P\<^sub>0} to make both a shift and a reduce transition.

Moreover, \<open>q\<close> is said to have a \concept{reduce-reduce conflict} if it is possible to perform 
reducing transitions for two distinct productions.

If \<open>q\<close> has either of these conflicts, it is \concept{\<open>LR(0)\<close>-inadequate}. Otherwise, it is 
\concept{\<open>LR(0)\<close> adequate}.
\end{definition}

It is worth noting that in this context, we consider finishing transitions a special case of reducing
transitions. Therefore, for a state to permit a reducing transition for a production @{term \<open>(A, \<alpha>)\<close>},
it suffices for it to contain the complete item @{term \<open>[A \<rightarrow> \<alpha> \<cdot> ]\<close>}.

Because of this, we formally define \<open>q\<close> to have a reduce-reduce conflict if 
@{term \<open>mbox0 (card (completes q) > 1)\<close>}. Meanwhile, there is a shift-reduce conflict if there exist two 
tuples @{prop \<open>([q], a, rs\<^sub>1) \<in> gpda.nxt P\<^sub>0\<close>} and @{prop \<open>(q#qs, rs\<^sub>2) \<in> gpda.eps P\<^sub>0\<close>}. This is
equivalent to \<open>q\<close> containing at least one complete item, and an incomplete item of the form 
@{term \<open>[X \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]\<close>}.

We will now show a lemma that Wilhelm et al. present without proof and we will need in the future to 
show the final theorem of the \<open>LR(0)\<close> section in the book. First, we prove an 
auxiliary lemma:

\begin{lemma}\label{derivern_non_word_imp_hd_eps_reachable}
If @{prop \<open>Prods G' \<turnstile> [Nt A] \<Rightarrow>r(Suc n) Y # \<gamma>\<close>} and \<open>Y # \<gamma>\<close> is not a terminal word, then there exist
\<open>X :: 'n\<close> and \<open>\<alpha>, \<beta> :: syms\<close> such that \mbox{@{term \<open>[A \<rightarrow> \<cdot> \<alpha>] \<in> It G'\<close>}} and 
@{prop \<open>([A \<rightarrow> [] \<cdot> \<alpha>], [X \<rightarrow> [] \<cdot> Y # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*\<close>}.
\begin{proof}
We induct on \<open>n\<close> for arbitrary \<open>Y\<close> and \<open>\<gamma>\<close>.

If \<open>n = 0\<close>, then @{prop \<open>(A, Y # \<gamma>) \<in> Prods G'\<close>}, and the implication holds trivially by reflexivity.

If \<open>n > 0\<close>, we consider the final step in the derivation. The sentential form that derives 
@{term \<open>Y # \<gamma>\<close>} in the last step must be nonempty and contain at least one nonterminal symbol. Let
@{term \<open>X # \<delta>\<close>} be this sentential form. By the induction hypothesis, there exist
\<open>\<alpha>, \<beta> :: syms\<close> and \<open>W :: 'n\<close> such that \mbox{@{prop \<open>[A \<rightarrow> [] \<cdot> \<alpha>] \<in> It G'\<close>}} and 
\begin{equation}\label{der_hd_eps.ih}
@{prop \<open>([A \<rightarrow> [] \<cdot> \<alpha>], [W \<rightarrow> [] \<cdot> X # \<beta>]) \<in> (nfa.eps char_fa)\<^sup>*\<close>}. 
\end{equation}
We can now do a case distinction on
whether \<open>\<delta>\<close> consists exclusively of terminals.

If \<open>\<delta>\<close> contains no nonterminals, there exists an \<open>X' :: 'n\<close> such that @{prop \<open>X = Nt X'\<close>}. Furthermore, 
there also exists a production @{prop \<open>(X', \<chi>) \<in> Prods G'\<close>} which was applied in the last derivation 
step  was applied, meaning @{prop \<open>\<chi> @ \<delta> = Y # \<gamma>\<close>}. This implies that \<open>\<chi>\<close> cannot be the empty word; 
if this were the case, @{term \<open>Y # \<gamma>\<close>} would contain no nonterminals, which contradicts our assumption 
that it is not a terminal word. Therefore, @{prop \<open>\<chi> = Y # \<zeta>\<close>} for some \<open>\<zeta> :: syms\<close>. From all this 
follows @{prop \<open>([W \<rightarrow> [] \<cdot> Nt X' # \<beta>], [X' \<rightarrow> [] \<cdot> Y # \<zeta>]) \<in> mbox0 (nfa.eps char_fa)\<close>}.
The implication then holds by \eqref{der_hd_eps.ih}.

On the other hand, if \<open>\<delta>\<close> contains at least a nonterminal, we know that @{prop \<open>X = Y\<close>} since there
exists a nonterminal to the right of \<open>X\<close>, meaning that after the final rightmost derivation step,
it remains unchanged. This completes the proof by \eqref{der_hd_eps.ih}.
\end{proof}
\end{lemma}

\begin{lemma}\label{LR0_adequate_cases}
If a state \<open>q\<close> is \<open>LR(0)\<close>-adequate, one of the following holds:
\begin{enumerate}
\item @{prop \<open>completes q = {}\<close>}
\item @{prop \<open>q = {[A \<rightarrow> \<alpha> \<cdot> ]}\<close>} for some \<open>A\<close> and \<open>\<alpha>\<close>.
\item \<open>completes q = {[A \<rightarrow> \<cdot> ]}\<close> and for every incomplete item \<open>i \<in> q\<close>, 
there exist \<open>X, Y :: 'n\<close> and \<open>\<alpha>, \<beta> :: syms\<close> such that @{prop \<open>i = [X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>]\<close>} 
and every rightmost derivation of a word \<open>w\<close> 
\[ \<open>Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* \<gamma> \<Rightarrow>r map Tm w\<close> \]  
implies @{prop \<open>\<gamma> = Nt A # map Tm w\<close>}.
\end{enumerate}
\begin{proof}
Since \<open>q\<close> is a state of @{const P\<^sub>0}, it is either the final state @{term P0_final} or a state of 
@{const LR\<^sub>0}. If @{prop \<open>q = P0_final\<close>}, it is trivially \<open>LR(0)\<close>-adequate and fulfills (2).

Now, we assume \<open>q\<close> is a state of @{const LR\<^sub>0}. Since \<open>q\<close> is \<open>LR(0)\<close>- adequate, we can distinguish two cases:
either \<open>q\<close> has no complete items, or exactly one complete item. If \<open>q\<close> has no complete items, it 
fulfills condition (1).

Otherwise, 
\begin{equation}\label{ad_cases.compq}
@{prop \<open>completes q = {[A \<rightarrow> \<alpha> \<cdot> ]}\<close>}
\end{equation} 
for some \<open>A\<close> and \<open>\<alpha>\<close>. We do another case distinction 
on whether \<open>q\<close> has any incomplete items; if it has none, it fullfils condition (2).

Otherwise, let @{prop \<open>[X \<rightarrow> \<alpha>' \<cdot> Z # \<beta>] \<in> q\<close>}. We know that \<open>Z\<close> must be a nonterminal, since if it
were some terminal symbol \<open>Tm a\<close>, the reading transition 
@{term \<open>mbox ([q], a, [dfa.nxt LR\<^sub>0 q (Tm a), q])\<close>} would be possible, and since \<open>q\<close> also contains a 
complete item, a shift-reduce conflict would be present, contradicting the premise that \<open>q\<close> is 
\<open>LR(0)\<close>-adequate. Thus, let @{prop \<open>Z = Nt Y\<close>}.

Since \<open>G'\<close> is reduced, we know that there must exist a rightmost derivation of a terminal word \<open>w\<close>
of the form \<open>Prods G' \<turnstile> [Nt Y] \<Rightarrow>r* \<gamma> \<Rightarrow>r map Tm w\<close> for some \<open>\<gamma> :: syms\<close>. To complete our proof, 
we need to show that @{prop \<open>mbox0 (\<gamma> = Nt A # map Tm w)\<close>} and @{prop \<open>\<alpha> = []\<close>}. We begin by doing a 
case distinction on the reflexive transitive closure of the derivation from \<open>Y\<close> to \<open>\<gamma>\<close>:

In the reflexive case, \<open>Y\<close> derives @{term \<open>map Tm w\<close>} in a single step, meaning 
\[ @{prop \<open>(Y, map Tm w) \<in> Prods G'\<close>}. \] 
Therefore, @{term \<open>([X \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>], [Y \<rightarrow> \<cdot> map Tm w])\<close>} is in the \<open>\<epsilon>\<close>-transition relation of 
@{const char_fa}; this and @{prop \<open>[X \<rightarrow> \<alpha>' \<cdot> Nt Y # \<beta>] \<in> q\<close>} imply that 
@{prop \<open>mbox0 ([Y \<rightarrow> \<cdot> map Tm w] \<in> q)\<close>} as well. We can now do a case distinction on \<open>w\<close>: if 
@{prop \<open>w = []\<close>}, the implication holds since @{prop \<open>[Y \<rightarrow>  \<cdot> map Tm w] = [A \<rightarrow> \<alpha>  \<cdot> ]\<close>} and 
@{prop \<open>[Nt Y] = \<gamma>\<close>}. If on the other hand \<open>w\<close> is nonempty, \<open>q\<close> has a shift-reduce conflict, which
contradicts its \<open>LR(0)\<close>-adequacy. This completes the reflexive case, and we can now move on to the 
other case.

For the transitive case, we know \<open>Y\<close> derives \<open>\<gamma>\<close>  in @{term \<open>Suc n\<close>} steps for some \<open>n :: nat\<close>. 
Since \<open>\<gamma>\<close> derives \<open>map Tm w\<close> in the final step, it must be nonempty and contain at least one 
nonterminal. Therefore, let 
\begin{equation}\label{ad_cases.gWd}
@{prop \<open>\<gamma> = W # \<delta>\<close>}
\end{equation}
 for some \<open>W :: sym\<close> and \<open>\<delta> :: syms\<close>. From all this, 
Lemma~\ref{derivern_non_word_imp_hd_eps_reachable} tells us there exist \<open>\<gamma>', \<zeta> :: syms\<close> and 
\<open>B :: 'n\<close> such that @{prop \<open>[Y \<rightarrow> [] \<cdot> \<gamma>'] \<in> It G'\<close>} and
\begin{equation}\label{ad_cases.YB_eps} 
@{prop \<open>([Y \<rightarrow> [] \<cdot> \<gamma>'], [B \<rightarrow> [] \<cdot> W # \<zeta>]) \<in> (nfa.eps char_fa)\<^sup>*\<close>}. 
\end{equation}
Moreover, by contradiction we know that \<open>W\<close> must be a nonterminal: if this is not the case, 
@{prop \<open>W = Tm a\<close>} for some \<open>a :: 't\<close>. By transitivity, this along with 
@{prop \<open>[X \<rightarrow> \<alpha>' \<cdot> Z # \<beta>] \<in> q\<close>}, @{prop \<open>Z = Nt Y\<close>}, and \eqref{ad_cases.YB_eps} implies that 
@{prop \<open>[B \<rightarrow> [] \<cdot> Tm a # \<zeta>] \<in> q\<close>}, permitting a reading transition on state \<open>q\<close>. Since 
@{term \<open>completes q\<close>} is nonempty, such a reading transition would make \<open>q\<close> \<open>LR(0)\<close>-inadequate, 
leading to a contradiction to our original assumption. Therefore, let @{prop \<open>W = Nt C\<close>} for some
\<open>C :: 'n\<close>. Then the last step of the rightmost derivation must consist of some production 
@{prop \<open>(C, map Tm u) \<in> Prods G'\<close>} for some terminal word \<open>u\<close> with 
\begin{equation}\label{ad_cases.udw}
@{term \<open>map Tm u @ \<delta> = map Tm w\<close>}.
\end{equation}
This implies that @{prop \<open>([B \<rightarrow> \<cdot> W # \<zeta>], [C \<rightarrow> \<cdot> map Tm u]) \<in> nfa.eps char_fa\<close>}, and 
once again with @{prop \<open>[X \<rightarrow> \<alpha>' \<cdot> Z # \<beta>] \<in> q\<close>}, @{prop \<open>Z = Nt Y\<close>}, and \eqref{ad_cases.YB_eps}, 
this implies that @{prop \<open>([X \<rightarrow> \<alpha>' \<cdot> Z # \<beta>], [C \<rightarrow> \<cdot> map Tm u]) \<in> (nfa.eps char_fa)\<^sup>*\<close>} by transitivity.
This means that the item @{term \<open>[C \<rightarrow> \<cdot> map Tm u]\<close>} is also in \<open>q\<close>. This and \eqref{ad_cases.compq} 
imply 
\begin{equation}\label{C_eq_comp}
@{prop [source] \<open>[C \<rightarrow> [] \<cdot> map Tm u] = [A \<rightarrow> \<alpha> \<cdot> []]\<close>}.
\end{equation}
This follows from the fact that @{term \<open>[C \<rightarrow> \<cdot> map Tm u]\<close>} can only be an incomplete item if \<open>u\<close> is 
nonempty, but this would allow a reading transition to take place. As we already showed, this would 
lead to a contradiction. Therefore, by \eqref{ad_cases.gWd}, \eqref{ad_cases.udw}, and 
\eqref{C_eq_comp}, the criteria for condition (3) of our original claim are fulfilled. 
\end{proof}
\end{lemma}\<close>

subsection \<open>\<open>LR(k)\<close> Grammars\<close>

text \<open>\begin{definition}[LR(k) Grammar]
\<open>G'\<close> is an \concept{LR(k) grammar} if for any \<open>\<alpha>, \<beta>, \<gamma> :: syms\<close>, \<open>X, Y :: 'n\<close>, and 
\<open>w, x, y :: 't list\<close>
\begin{gather*}
\begin{multlined}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w\<close>
\end{multlined}
\intertext{and}
\begin{multlined}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>
\end{multlined}
\end{gather*}
and @{prop \<open>take k w = take k y\<close>}\\[4\jot] 
implies @{prop \<open>\<alpha> = \<gamma>\<close>} @{prop \<open>X = Y\<close>}, and @{prop \<open>x = y\<close>}.
\end{definition}

It is worth noting that our definition, in accordance with that of Wilhelm et 
al.~\cite[p. 113]{Wilhelm}, is restricted to the extension of a CFG. We will discuss a more 
generalized definition applicable to an arbitrary CFG in a later section, but the original definition 
suffices for the main theorem we show, since it relates the \<open>LR(k)\<close> condition only to the parser,
which we have also restricted to extended grammars.
\<close>

subsubsection \<open>Equivalence with \<open>LR(0)\<close>-Adequate States\<close>
subsubsection \<open>Preservation of the \<open>LR(k)\<close> Condition in Extended Grammars\<close>
subsection \<open>Language Equivalence of @{const P\<^sub>0} and its Grammar\<close>
subsubsection \<open>Stack Words: Proving Soundness\<close>
subsubsection \<open>The Shift-Reduce Pushdown Automaton: Proving Completeness\<close>

section \<open>Conclusion\<close>
subsection \<open>Results\<close>
subsection \<open>Discussion of future work\<close>
subsubsection \<open>Addressing Grammar Extensions\<close>
subsubsection \<open>Implementing an Executable \<open>LR(0)\<close> Parser\<close>

(* Finiteness *)
text \<open>In the GPDA section, we mentioned that we disregard the finiteness of our GPDA transition 
relations since they are of no importance for most of our GPDAs. This is not the case for @{const P\<^sub>0}, 
however, since in order to use the parser, one must be able to execute the transition relation.

\<close>

subsubsection \<open>Formalizing \<open>LR(k)\<close> theory for general \<open>k\<close>\<close>
(* maybe *)
subsubsection \<open>Equivalence of PDAs and GPDAs\<close>

(*<*)
end
end
(*>*)
