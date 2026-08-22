(*<*)
theory Paper
  imports 
    "LR0_Base.LR0_Parser"
    "HOL-Library.LaTeXsugar"
begin

section \<open>setup\<close>

declare [[names_short, show_question_marks = false]]

definition sub :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
  "sub X s \<equiv> X"

definition sub' :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "sub' X n \<equiv> X"

definition subs :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'a" where
  "subs X s0 s1 \<equiv> X"

notation sub (\<open>\<^latex>\<open>\ensuremath{\<close>_\<^latex>\<open>_{\<close>_\<^latex>\<open>}}\<close>\<close>)
notation sub' (\<open>\<^latex>\<open>\ensuremath{\<close>_\<^latex>\<open>_{\<close>_\<^latex>\<open>}}\<close>\<close>)
notation subs (\<open>\<^latex>\<open>\ensuremath{\<close>_\<^latex>\<open>_{\<close>_,_\<^latex>\<open>}}\<close>\<close>)


no_notation (latex) Cons (\<open>_ \<cdot>/ _\<close> [66,65] 65)

syntax (latex output)
  "_take" :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_|\<^bsub>_\<^esub>" [999,1000] 1000)
translations 
  "_take xs n" <= "CONST take n xs"

notation (latex output) drop (\<open>\<^bsub>_\<^esub>|_\<close> [1000,999] 1000)


notation (latex output) LangS (\<open>L'(_')\<close>)
notation (latex output) gpda.Lang (\<open>L'(_')\<close>)

abbreviation initial_item :: "'n \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow>  \<cdot> _ ]") where
  "[A \<rightarrow> \<cdot> \<alpha> ] \<equiv>  [A \<rightarrow> [] \<cdot> \<alpha>]"
abbreviation complete_item :: "'n \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow> _ \<cdot> ]") where
  "[A \<rightarrow> \<alpha> \<cdot> ] \<equiv> [A \<rightarrow> \<alpha> \<cdot> []]"
abbreviation empty_item :: "'n \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow> \<cdot> ]") where
  "[A \<rightarrow> \<cdot> ] \<equiv> [A \<rightarrow> [] \<cdot> []]"

notation (latex output) It (\<open>\<^latex>\<open>\ensuremath{\mathrm{It}_{\<close>_\<^latex>\<open>}}\<close>\<close>)

(*>*)

section \<open>Introduction\<close>

text \<open>In the early stages of the compilation process, compilers perform \emph{syntactic analysis},
otherwise known as \emph{parsing}, which in essence consists of verifying that the input program
adheres to the syntax rules of the source language. Wilhelm, Seidl, and Hack (from
this point onward ``Wilhelm et al.'') present the \<open>LR(k)\<close> parsing algorithms and their
underlying theory in their book 
``\emph{Compiler Design: Syntactic and Semantic Analysis}''~\cite{Wilhelm}. This
thesis focuses on one variant of \<open>LR(k)\<close> parsing, namely \<open>LR(0)\<close>, and presents two major results:
a formalization of this section of the book using the Isabelle Proof 
Assistant~\footnote{Some notes on terminology: the word ``formal'' when used throughout this thesis
carries exactly this meaning, i.e., machine-checked. Similarly, a ``formalization'' denotes the
translation of definitions, theorems, and proofs into code that is then machine-checked, in the
case of this thesis by Isabelle.}, and a formal correctness proof of the canonical \<open>LR(0)\<close> parser.
The parser's correctness is not discussed by Wilhelm et al.

The motivations for each of these goals are not identical, albeit similar. The first one is quite
similar to most (if not all) formal verification projects. In few words: informal proofs often
contain errors. Authors naturally rely on intuition to some extent to write such proofs, and some
arguments may seem to be correct on the surface, but turn out to be false if one looks at them more
closely. Machine-checked proofs prevent intuition from betraying the author: every statement and
every logical step in a proof, however simple, is verified by the proof assistant, thereby confirming
the correctness of the statements being proved. Wilhelm et al. are no exception to this, which leads
to one of the two main questions I intend to answer: are the \<open>LR(0)\<close> parsing theory and its proofs
as presented by Wilhelm et al. correct, and if they are not, how must they be modified for this to be
the case?

The central caveat of formalization for this thesis lies in axioms and definitions: since proof
assistants require reasoning that is logically sound, the outcome of formal verification is the
assurance that the theorems are indeed a consequence of the definitions and assumptions provided,
but there is no guarantee that the formal definitions and assumptions themselves are faithful to
their informal counterparts.

In essence, the motivation for the canonical \<open>LR(0)\<close> parser is to define a deterministic automaton
that can determine whether a word is in a particular context-free grammar (CFG)~\footnote{In practice,
parsers perform other tasks such as building an internal representation of the syntactic structure of
the input, but this is out of the scope of the \<open>LR(0)\<close> parsing section of the book.}. In the \<open>LR(0)\<close>
section of the book, the main objective of Wilhelm et al. is to show one particular property: the parser's
determinism. The other core property of the parser, namely the fact that it recognizes the grammar's
language, is not discussed in the book. However, this question of correctness is just as fundamental as
the one about determinism. Therefore, it is of great interest to answer a second question on top of
the formalization of the authors' existing work: what is the language accepted by the canonical 
\<open>LR(0)\<close> parser as defined by Wilhelm et al., and in particular, how does this language relate to
that of the underlying grammar?\<close>

subsection \<open>Previous Work\<close>

text \<open>This thesis builds on the formalization of CFG theory by Nipkow et 
al.~\cite{Nipkow}, which is part of the Archive of Formal Proofs
(AFP)~\footnote{\url{https://www.isa-afp.org/}}, an archive of libraries and formal proof developments for
Isabelle. In this formalization, the authors introduce CFGs, derivations (including leftmost and
rightmost derivations), and the elimination of unreachable and unproductive nonterminals, which are
foundational elements in parsing theory.

% TODO\<close>

subsection \<open>Isabelle Notation\<close>
subsubsection \<open>General Notation\<close>

text \<open>A term \<open>t\<close> of type \<open>\<tau>\<close> is notated as \<open>t :: \<tau>\<close>, with type variables @{typ 'a}, @{typ 'b},
@{typ 'c}, etc. Tuple types are notated using \<open>\<times>\<close>: for \<open>x\<^sub>0 :: 'a\<^sub>0, x\<^sub>1 :: 'a\<^sub>1,\<dots>, x\<^sub>n :: 'a\<^sub>n\<close>, we write
\<open>(x\<^sub>0,x\<^sub>1,\<dots>,x\<^sub>n) :: 'a\<^sub>0 \<times> 'a\<^sub>1 \<times> \<dots> \<times> 'a\<^sub>n\<close>. We denote functions with the arrow \<open>\<Rightarrow>\<close>, and we notate the
image of a set \<open>A\<close> under function \<open>f\<close> as @{term \<open>f ` A\<close>}.

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

An explicit list can be either written as \<open>x\<^sub>0 # x\<^sub>1 # \<dots> # x\<^sub>n\<close> or as \<open>[x\<^sub>0, x\<^sub>1, \<dots>, x\<^sub>n]\<close>. If 
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

Lastly, if premises \<open>A\<^sub>1, A\<^sub>2, \<dots>, A\<^sub>n\<close> imply \<open>B\<close>, we write \mbox{\<open>\<lbrakk>A\<^sub>1; A\<^sub>2; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> B\<close>.}\<close>

subsubsection \<open>Records and Finite Automata\<close>

text \<open>A record R whose record type has field names \<open>\<phi>\<^sub>1, \<phi>\<^sub>2, \<dots>, \<phi>\<^sub>n\<close> 
is defined through the notation
\[ \<open>R = \<lparr>\<phi>\<^sub>1 = v\<^sub>1, \<phi>\<^sub>2 = v\<^sub>2, \<phi>\<^sub>n = v\<^sub>n\<rparr>\<close> \]
if R has values \<open>v\<^sub>1, v\<^sub>2, \<dots>, v\<^sub>n\<close> such that \<open>\<phi>\<^sub>i = v\<^sub>i\<close> for every \<open>1 \<le> i \<le> n\<close>. Furthermore, notation 
\<open>\<phi>\<^sub>i R\<close> refers to the value of field \<open>\<phi>\<^sub>i\<close> of \<open>R\<close> (in this example, \<open>v\<^sub>i\<close>). Note that this 
causes a record field consisting of a function \<open>f :: 'a \<Rightarrow> 'b\<close> to have an additional parameter for 
the record field, i.e., \<open>f :: \<rho> \<Rightarrow> 'a \<Rightarrow> 'b\<close>, where \<open>\<rho>\<close> is the record type of which \<open>f\<close> is a field.

In this thesis, we work with multiple finite automata, which we define and implement on top of 
Paulson's formalization of both nondeterministic and deterministic finite automata
(NFAs and DFAs respectively)~\cite{Paulson}.

NFAs are defined by record @{typ \<open>('a, 'q) nfa\<close>} with alphabet type @{typ 'a} and state type 
@{typ 'q}, with the following fields:
\begin{itemize}
\item \<open>states :: 'q set\<close>: a finite set of states
\item \<open>init :: 'q set\<close>: the set of initial states, with \<open>init \<subseteq> states\<close>
\item \<open>final :: 'q set\<close>: the set of final states, also with \<open>final \<subseteq> states\<close>
\item \<open>nxt :: 'q \<Rightarrow> 'a \<Rightarrow> 'q set\<close>: the transition function for reading transitions.
\item \<open>eps :: ('q \<times> 'q) set\<close>: the \<open>\<epsilon>\<close>-transition relation
\end{itemize}

Furthermore, function \<open>nextl :: 'q set \<Rightarrow> 'a list \<Rightarrow> 'q set\<close> for a NFA denotes the extension of 
\<open>nxt\<close> to sets of states and words. 

DFAs are defined by a record @{typ \<open>('a, 'q) dfa\<close>} where @{typ 'a} and @{typ 'q} are again the 
alphabet and state types respectively. The @{type dfa} record type has the same fields as 
@{type nfa} except that it naturally lacks an \<open>\<epsilon>\<close>-transition relation. Moreover, in a DFA,
\<open>init :: 'q\<close> is a unique initial state, and \<open>nxt :: 'q \<Rightarrow> 'a \<Rightarrow> 'q\<close> returns a unique state.

We also define a \<open>nextl\<close> function for DFAs, lifting the \<open>nxt\<close> function of a DFA from symbols to 
words with \<open>nextl :: 'q \<Rightarrow> 'a list \<Rightarrow> 'q\<close>.\<close>

subsubsection \<open>Context-Free Grammars\<close>

text \<open>In the context-free grammar theory, Nipkow et al.~\<^cite>\<open>Nipkow\<close> introduce type 
@{typ "('n, 't) sym"} for context-free grammar \concept{symbols} as a tagged union consisting of 
nonterminals (@{const Nt}) and terminals (@{const Tm}) of type @{typ 'n} and @{typ 't} respectively:
\[ @{datatype sym} \]

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
\<open>\<alpha>, \<beta>, \<gamma> :: ('n, 't) syms\<close>.\<close>

subsection \<open>Overview\<close>

text \<open>The thesis follows a similar structure to Wilhelm et al. First, we introduce some foundational
definitions and assumptions regarding the CFGs we will be working with. We then define the item
pushdown automaton, followed by a new section not present in the book: a formalized decomposition of
rightmost derivations. Afterwards, we return to the book's structure with the characteristic finite
automaton, the canonical \<open>LR(0)\<close> automaton, and lastly, the canonical \<open>LR(0)\<close> parser. In the final 
parser section, we first finish the formal verification of Wilhelm et al., and afterwards, we
conclude the formalization results with the proof of the parser's correctness.\<close>

section \<open>Basic Definitions\<close>

subsection \<open>Extended and Reduced Grammars\<close>

subsubsection \<open>Extending Grammars by a New Start Symbol\<close>

(*<*)
  context Reduced_Cfg 
begin

lemma substring_derives:
  assumes "reduced G" "LangS G \<noteq> {}" "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* u@\<alpha>@v"
  shows "\<exists>w. Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm w"
  using reduced_nonempty_derives_imp_substring_derives_Tms[OF assms] by blast

abbreviation \<open>I\<^sub>G \<equiv> Reduced_Cfg.IPDA G\<close>
(*>*)

text\<open>Throughout this thesis, we will define several automata which will aid us in our goal of 
constructing a deterministic \<open>LR(0)\<close> parser for a context-free grammar \<open>G\<close>. Naturally, our 
definitions will be defined based on the productions of the grammar, and the starting state of all 
these automata relates to the start symbol of \<open>G\<close>, specifically the productions where \<open>Start G\<close> is
on the LHS. In general, however, a context-free grammar's start symbol can appear on the right-hand 
side of a production, and in many cases we would like to be able to identify that a word has been 
derived when a production of the form @{term \<open>(Start G, \<alpha>)\<close>} is encountered. If \<open>Start G\<close> is on the 
RHS of a production, this is not possible.

To achieve this, we extend a context-free grammar \<open>G\<close> with finite set of productions by a fresh 
start symbol \<open>S'\<close> with a single production \<open>(S', [Nt S])\<close>. The resulting grammar, which we define to 
be \<open>G'\<close>, is the \concept{extended grammar}, or the \concept{extension}, of \<open>G\<close>. We analogously refer 
to \<open>Prods G'\<close> as the extension of \<open>Prods G\<close> or the \concept{extended set of productions} of \<open>G\<close>. Formally:
\begin{gather*}
@{thm S'_def}\\
@{thm G'_def}
\end{gather*}

We now prove that extending the grammar preserves the language. 

\begin{lemma}\label{G'_deriven_Suc_imp_G_deriven}
If there exists a derivation in \<open>G'\<close>
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) \<beta>\<close>}, \]
then there also exists a derivation in \<open>G\<close>
\[ @{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>(n) \<beta>\<close>}. \]
\begin{proof} 
We induct on \<open>n\<close>. If \<open>n = 0\<close>, \<open>\<beta> = [Nt S]\<close>, and the implication holds.

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
that \<open>S'\<close> derives \<open>S\<close> in \<open>G'\<close>, implies that @{prop \<open>w \<in> LangS G'\<close>}.
\end{proof}
\end{theorem}

We can therefore use \<open>G'\<close> construct our parser in order to recognize the language of \<open>G\<close>.\<close>

subsubsection \<open>Reduced Grammars\<close>

text \<open>In general, CFGs can contain problematic nonterminals which can be removed from the grammar 
without altering the language. Working with grammars that lack such nonterminals is ideal, since 
having them increases computational complexity and makes the grammar less well-behaved.

\begin{example}\label{ex:useless symbols}
Let \<open>G\<close> be a CFG with @{term [source] \<open>S = Start G\<close>} and productions:
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

Nipkow et al. define \concept{useful} nonterminals w.r.t. a set of productions and a start symbol:
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

Consider Example~\ref{ex:useless symbols} once again. None of the nonterminals \<open>B, C,\<close> and \<open>D\<close> is 
useful:
\begin{itemize}
\item \<open>B\<close> is reachable but unproductive
\item \<open>C\<close> is productive but unreachable
\item \<open>D\<close> is both unreachable and unproductive.
\end{itemize}
If we remove all productions containing non-useful nonterminals from this grammar, the productions 
that remain are:
\begin{center}
\begin{tabular}{cc}
\<open>S \<rightarrow> A\<close> & \<open>A \<rightarrow> aA | a\<close>
\end{tabular}
\end{center}

As we can see, by applying this restriction to arbitrary grammars, the resulting set of 
productions can potentially become much smaller than the original one. This also guarantees that all
nonterminals are more well-behaved; for example, since every nonterminal is productive, we know 
that any part sentential form that can be derived from \<open>S\<close> contains only productive nonterminals and can
therefore derive a word in the language:

\begin{quote}
@{thm [display] substring_derives}
\end{quote}

This property will be particularly useful in the coming sections.

With this, we now define the notion of \concept{reduced grammars}.
\begin{definition}[Reduced grammar]
\begin{equation*}
@{thm reduced_def}.
\end{equation*}
\end{definition}

\begin{lemma}\label{G'_reduced}[Preservation of reduction]
If \<open>G\<close> is reduced and @{term \<open>LangS G\<close>} is nonempty, \<open>G'\<close> is reduced.
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

With this, we have now defined a way to extend any CFG by a new start symbol while preserving both 
language and the usefulness of all nonterminals.\<close>

subsection \<open>Context-Free Items\<close>

text \<open>\begin{definition}[Context-free item]
A \concept{context-free item} @{typ \<open>('n, 't) item\<close>} for a CFG \<open>G\<close> is a triple 
\mbox{\<open>(A, \<alpha>, \<beta>) :: 'n \<times> ('n, 't) syms \<times> ('n, 't) syms\<close>} such that 
@{prop \<open>(A, \<alpha>@\<beta>) \<in> Prods G\<close>}. We write the item \<open>(A, \<alpha>, \<beta>)\<close> as @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}, and akin to
@{type sym} and @{type syms}, we often abbreviate the item type to simply ``@{type item}'' for
brevity.
\end{definition}

Context-free items allow tracking the current state of the parsing process. Generally, as we
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

text \<open>In later sections, we will define several automata to lay the foundations for the canonical 
\<open>LR(0)\<close> parser. Most of these automata, including the parser itself, require a stack to operate, but 
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
\item \<open>eps :: ('q list \<times> 'q list) set\<close> is the transition relation for \concept{\<open>\<epsilon>\<close>-transitions}, 
i.e., transitions that do not read the input.
\end{itemize}
Lastly, if \<open>M\<close> is a GPDA we assume for all @{prop \<open>(ps, a, qs) \<in> nxt M\<close>} that \<open>ps\<close> is nonempty, 
and both \<open>ps\<close> and \<open>qs\<close> are subsets of \<open>states\<close>. We make the same assumption for all 
@{prop \<open>(ps, qs) \<in> eps M\<close>}.

\end{definition}

It is worth noting that, differently from traditional PDAs, GPDAs do not have a dedicated state. 
Instead, a variable amount of topmost stack symbols are used to determine the transition. 
Therefore, if \<open>M\<close> is a GPDA, talking about "the state" of \<open>M\<close> at a given time is a shorthand to 
refer to the topmost state on \<open>M\<close>'s stack at that moment.

Another important aspect is that as opposed to our definition of GPDAs, Wilhelm et al. define them
as having finite transition relations. This assumption is of importance in particular if one wishes
to show the equivalence between GPDAs and PDAs, which is out of the scope of our formalization.
Besides the parser, our formalization defines the item pushdown automaton as a GPDA. Proving the
finiteness of this automaton's transition relation is a burden that yields a fact we will not use,
so we omit the finiteness assumption in the generic GPDA definition for the sake of simplicity. For
the \<open>LR(0)\<close> parser itself, however, the finiteness of the transition relations is of great interest
due to the question of executability. We will address this in a later section.

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
interpretation I: gpda IPDA
  by (fact gpda_IPDA)

notation I.step (infix \<open>\<turnstile>I\<close> 55)
notation I.steps (infix \<open>\<turnstile>I*\<close> 55)
notation I.stepn (\<open>_ \<turnstile>I'(_') _\<close> 55)
notation (latex output) I.Lang 
  (\<open>\<^latex>\<open>\ensuremath{L(I_G)}\<close>\<close>)


(*>*)

subsection \<open>Definition\<close>

text \<open>One of the main objectives in the construction of our parser is determinism. Despite the ability of
PDAs of recognizing CFLs, they are non-deterministic in general, which means they are not easily
implemented in practice. In this section, we define the Item Pushdown Automaton to a 
context-free grammar, from which we will later derive a deterministic parser. From this point onwards, 
unless stated otherwise, let \<open>G\<close> be a CFG with start symbol \<open>S\<close> such that

\begin{itemize}
\item @{term \<open>Prods G\<close>} is finite
\item @{term \<open>LangS G \<noteq> {}\<close>}
\item \<open>G\<close> is reduced
\item \<open>G'\<close> is the extension of \<open>G\<close> with start symbol \<open>S'\<close>.
\end{itemize}

\begin{definition}[Item pushdown automaton]
The \concept{item pushdown automaton} (IPDA) to \<open>G\<close> is the @{typeof IPDA}:
\begin{multline*}
  \<open>I\<^sub>G = \<lparr>states = It G', init = [S' \<rightarrow> \<cdot> [Nt S]],\<close>\\
  \<open>final = {[S' \<rightarrow> [Nt S] \<cdot> ]}, nxt = \<Delta>\<^sub>I, eps = \<E>\<^sub>I\<rparr>\<close>
\end{multline*}
where 
\begin{multline*}
\<open>\<Delta>\<^sub>I = {([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], a, [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]])\<close>\\
\<open>| X \<beta> a \<gamma>. (X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'}\<close>
\end{multline*}
and \<open>\<E>\<^sub>I = E \<union> R\<close> for
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
as we stated before, by defining \mbox{\<open>nxt :: ('q list \<times> 'a \<times> 'q list) set\<close>} and 
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
We proceed by induction on the length \<open>n\<close> of the computation for arbitrary \<open>u, v,\<close> and \<open>\<rho>\<close>.

If @{term \<open>([init M], u @ v) \<turnstile>I(0) (rev \<rho>, v)\<close>}, then 
$\<open>[init M]\<close> = @{term \<open>mbox [[S' \<rightarrow> \<cdot> [Nt S]]]\<close>} = \<open>rev \<rho>\<close>$ and @{prop \<open>u @ v = v\<close>} hold. This in
turn implies @{prop \<open>hist \<rho> = []\<close>} and @{prop \<open>u = []\<close>}, fulfilling the invariant.

On the other hand, if @{term \<open>([init M], u @ v) \<turnstile>I(Suc n) (rev \<rho>, v)\<close>} for some \<open>n :: nat\<close>,
we distinguish cases on the final step of the computation.

If the last step was a shifting transition there exist \<open>A, \<alpha>, a, \<beta>, \<tau>, a, \<close> and \<open>x\<close> such that
the second to last configuration was of the form
\begin{gather}
@{term \<open>([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<tau>, a # v)\<close>}\label{eq:ipda.invariant.shift}
\intertext{and}
@{term \<open>rev \<rho> = [A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>] # \<tau>\<close>}\label{eq:ipda.invariant.rho_shift}.
\end{gather}
This implies the existence of some \<open>y :: 't list\<close> such that the initial input was of the form
\<open>uv = yav\<close>. This, together with \eqref{eq:ipda.invariant.shift}, and the induction hypothesis implies 
\<open>Prods G \<turnstile> hist (rev \<tau> @ [[A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]])\<close> = \<open>hist (rev \<tau>) @ \<alpha> \<Rightarrow>* map Tm y\<close>. With \<open>uv = yav\<close>
and by substituting \eqref{eq:ipda.invariant.rho_shift}, it follows that
\<open>Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm y @ [Tm a] = u\<close> holds, fulfilling the invariant.

For the reducing case, we have a second-to-last configuration 
@{term \<open>([Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close>}, and 
@{term \<open>rev \<rho>\<close>} = @{term \<open>mbox [X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>] # \<tau>\<close>} holds for some \<open>Y, \<alpha>, X, \<beta>, \<gamma>\<close> and \<open>\<tau>\<close>.
Moreover, @{prop \<open>(Y, \<alpha>) \<in> Prods G\<close>} must hold; otherwise, @{prop \<open>[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] \<in> It G'\<close>} 
would imply that \<open>S'\<close> is on the RHS of a production in \<open>G'\<close>, which cannot be the case by definition.

With all this and the induction hypothesis follows 
\[ @{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow>r hist (rev \<tau>) @ \<beta> @ \<alpha>\<close>} 
  \overset{(IH)}{\Rightarrow\mkern-5mu r} \<open>map Tm u\<close>. \] 
Therefore, the invariant holds once again.

Finally, in the expanding case we have @{term \<open>([X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close>} and 
@{prop \<open>rev \<rho> = [Y \<rightarrow> [] \<cdot> \<alpha>] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>\<close>}

By the induction hypothesis we have once more \<open>Prods G \<turnstile> hist (rev \<tau>) @ \<beta> \<Rightarrow>* map Tm u\<close>. We then 
have
\begin{align*}
\<open>Prods G \<turnstile> hist \<rho>\<close> &\ \<open>= hist ((rev \<tau>) @ [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] @ [Y \<rightarrow> [] \<cdot> \<alpha>])\<close>\\
&\ \<open>= hist (rev \<tau>) @ \<beta> \<Rightarrow>* map Tm u\<close>. 
\end{align*}
The invariant is therefore satisfied for all cases.
\end{proof}
\end{lemma}

\begin{lemma}\label{ipda.Lang_subst_Lang_G}
@{term \<open>gpda.Lang I\<^sub>G \<subseteq> LangS G\<close>}
\begin{proof}
Assume @{prop \<open>w \<in> gpda.Lang I\<^sub>G\<close>}. Then, 
\[ \<open>([init I\<^sub>G], w) =\<close>\ @{prop \<open>([init I\<^sub>G], w @ []) \<turnstile>I* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>}. \] 
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
We perform strong induction on the length of the derivation \<open>n\<close>.
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
\eqref{d_imp_c.b_decomp(6)}, we know that there are only two cases: either @{prop \<open>j = n\<close>} and 
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
\[ @{term \<open>([X \<rightarrow> \<beta>' \<cdot> ] # [A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, y @ x)\<close>}, \]
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
Let \<open>w\<close> be a word in @{term \<open>LangS G\<close>}. Then @{prop \<open>Prods G' \<turnstile> [Nt S] \<Rightarrow>* map Tm w\<close>}
since @{prop \<open>Prods G \<subseteq> Prods G'\<close>}.
With Lemma~\ref{derives_imp_completes} follows
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

section \<open>Rightmost Chains: Decomposing Rightmost Derivations\<close>

(*<*) 
end
context Reduced_Cfg
begin 
(*>*)

text \<open>Wilhelm et al. informally assert that for a rightmost derivation 
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>, there exists a decomposition
of the form
\begin{equation}\label{WSH rm chain}
\begin{split}
\<open>Prods G'\<close>\ & \<open>\<turnstile> [Nt S'] \<Rightarrow>r \<alpha>\<^sub>1 @ Nt X\<^sub>1 # \<beta>\<^sub>1 \<Rightarrow>r* \<alpha>\<^sub>1 @ Nt X\<^sub>1 # map Tm v\<^sub>1\<close>\\
        & \<open>\<Rightarrow>r \<alpha>\<^sub>1\<alpha>\<^sub>2 @ Nt X\<^sub>2 # \<beta>\<^sub>2 @ map Tm v\<^sub>1\<close>\\ 
        & \<open>\<Rightarrow>r* \<dots> \<Rightarrow>r* \<alpha>\<^sub>1 \<dots> \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n \<dots> v\<^sub>1)\<close>\\
        & \<open>\<Rightarrow>r (\<alpha>\<^sub>1 \<dots> \<alpha>\<^sub>n) \<alpha>\<beta> @ map Tm (v\<^sub>n \<dots> v\<^sub>1)\<close>.
\end{split}
\end{equation}
where \<open>X\<^sub>n = A\<close>. In the above expression, we omit most concatenation operators @{term \<open>(@)\<close>} for 
compactness. Instead, we denote concatenation by juxtaposition (such as in \<open>(\<alpha>\<^sub>1 \<dots> \<alpha>\<^sub>n) \<alpha>\<beta>\<close> instead
of \<open>(\<alpha>\<^sub>1 @ \<dots> @ \<alpha>\<^sub>n) @ \<alpha> @ \<beta>\<close>).

We now formalize this concept by defining \concept{rightmost chains} inductively. If sentential 
form \<open>\<alpha>\<close> reaches sentential form \<open>\<beta>\<close> with rightmost chain \<open>\<rho>\<close> under production set \<open>P\<close>, we write 
@{prop \<open>P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>\<close>}. For a fixed \<open>P\<close>, we define a \concept{reflexive} rule:
\begin{gather*}
@{thm rm_chain.refl}\\
\intertext{and a \concept{step} rule:}
@{thm [mode=Rule] rm_chain.step}
\end{gather*}

Essentially, rightmost chains allow us to store a list where each nonterminal produces the 
next, and the \<open>\<beta>\<close> strings derive words in-between the \<open>X\<close>s that build our chain. For this, we 
repurpose context-free items in order to track the entirety of the production that each nonterminal 
applies to produce the following nonterminal in the chain, with the bullet allowing us to pinpoint 
\emph{where} in the production the next nonterminal is located. With this definition, we can describe
rightmost derivations in an equivalent way as the authors do, with the particular advantage that we 
can perform structural induction on these chains, making it well-suited for theorem proving with
Isabelle unlike the authors' index-based definition of the decomposition.

\begin{example}\label{ex:rm_chain}
By our definition of rightmost chains, we would write \eqref{WSH rm chain} as~\footnote{Note that we 
once more omit most concatenation operators, replacing them by juxtaposition.}
\begin{multline*}
\<open>P \<turnstile> [Nt S'] \<midarrow>[\<close> X_{n-1}\ \<open>\<rightarrow> \<alpha>\<^sub>n \<cdot> Nt X\<^sub>n # \<beta>\<^sub>n] # [\<close> X_{n-2}\ \<open>\<rightarrow>\<close>\ 
\alpha_{n-1}\ \<open>\<cdot>\<close>\
  Nt\ X_{n-1}\ \#\ \beta_{n-1}]\\ 
  \<open># \<dots> # [[S' \<rightarrow> \<alpha>\<^sub>1 \<cdot> Nt X\<^sub>1 # \<beta>\<^sub>1]]\<rightarrow>r* \<alpha>\<^sub>1 \<dots> \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n\<dots>v\<^sub>1)\<close>.
\end{multline*}
\end{example}

We will now show the equivalence between rightmost chains and rightmost derivations.

\begin{lemma}\label{rm_chain_imp_derivers}
If @{prop \<open>P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>\<close>}, then @{prop \<open>P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>\<close>}
\begin{proof}
By rule induction on the rightmost chain.
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
We begin the proof by strong induction on @{term \<open>Suc n\<close>} for arbitrary \<open>\<alpha>\<close> and \<open>\<beta>\<close>. We now distinguish
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
We use strong induction on @{term \<open>Suc n\<close>} for arbitrary \<open>\<alpha>, X,\<close> and \<open>v\<close>. Furthermore, 
we distinguish cases on \<open>n\<close>:

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

Since our induction hypothesis only holds for a nonzero number of steps, we need to distinguish 
cases on the \<open>k\<close> steps in \eqref{der_rm.prodd(1)}.

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
\[ \<open>\<rho>' = [\<close> X_{n-1}\ \<open>\<rightarrow> \<alpha>\<^sub>n \<cdot> Nt X\<^sub>n # \<beta>\<^sub>n] # \<dots> # [[S' \<rightarrow> \<alpha>\<^sub>1 \<cdot> Nt X\<^sub>1 # \<beta>\<^sub>1]]\<close> \]
for some \<open>n \<ge> 0\<close> and \<open>X\<^sub>n = A\<close>~\footnote{We have adapted the original claim to our own notation for 
the sake of consistency and clarity.} It is worth noting that this structure of \<open>\<rho>'\<close> is essentially
the same as that of the item list in a rightmost chain (cf. Example~\ref{ex:rm_chain}). Therefore,
if some \<open>\<sigma> :: item list\<close> is part of some rightmost chain, we will be able to derive the same 
structure that Wilhelm et al. describe. We will now work towards proving that IPDA stacks reaching 
a final configuration have a stack that corresponds to some rightmost chain.\<close>

(*<*)
end
context Reduced_Cfg
begin

interpretation I: ipda G IPDA 
  by (fact ipda_IPDA)

notation I.step (infix \<open>\<turnstile>I\<close> 55)
notation I.steps (infix \<open>\<turnstile>I*\<close> 55)
notation I.stepn (\<open>_ \<turnstile>I'(_') _\<close> 55)

(*>*)

text\<open>\begin{lemma}\label{reaches_final_imp_last_is_init_or_final}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])\<close>}, then the last element in
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>\<close>} is either @{term \<open>[S' \<rightarrow> \<cdot> [Nt S']]\<close>} or @{term \<open>mbox I.final_state\<close>}.
\begin{proof}
By backwards induction on the length of the computation, making a case distinction on whether
the first step is shifting, expanding, or reducing in the transitive.
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
We perform backwards induction on the length of the computation of @{const I\<^sub>G} for arbitrary 
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
for some \<open>X :: 'n\<close>, \<open>\<alpha>', \<beta>, \<zeta> :: syms\<close> and \<open>\<sigma> :: item list\<close>. We can now perform a case distinction 
on the step @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I ([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v)\<close>}.

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
\[ \<open>\<dots> # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # [B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<dots>\<close> \]
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
detail, as well as define the finite automata that the canonical \<open>LR(0)\<close> parser will be based on.\<close>

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
particular item, as explained by Wilhelm et al.~\cite[p. 103]{Wilhelm}

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
We will later prove the implication differently. 

Implication \<open>(2) \<Longrightarrow> (3)\<close> fixes \<open>\<gamma>', A, \<alpha>, \<beta>,\<close> and \<open>w\<close>, and shows the existence of some \<open>\<rho>\<close>. Note
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
\[ [X_{n-1}\ \to\ \alpha_n\ \cdot\ Nt\ A\ \#\ \beta_n] \] 
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
We proceed by induction over the length \<open>n\<close> of the computation for arbitrary \<open>\<gamma>, \<alpha>, \<beta>, \<close> and \<open>A\<close>. 

If \<open>n = 0\<close> the implication holds trivially by reflexivity.

On the other hand, if \<open>n = Suc m\<close> for some \<open>m\<close>, we perform a case distinction on the last step of
the computation.

If the last step is a read transition, it is of the form
\[ @{prop \<open>([A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>], [Y]) \<turnstile>c ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
for \<open>\<alpha>'\<close> with @{prop \<open>\<alpha> = \<alpha>' @ [Y]\<close>}. With Lemma~\ref{char_reachable_imp_substring}, this implies 
that @{prop \<open>\<gamma> = \<delta> @ \<alpha>' @ [Y]\<close>} for some \<open>\<delta>\<close>, and therefore
\[ @{prop\<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha>') \<turnstile>c(m) ([A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>], [])\<close>}. \]
By the induction hypothesis, this implies
\begin{multline*} 
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w\<close>\\ 
\<open>\<Rightarrow> \<delta> @ \<alpha>' @ Y # \<beta> @ map Tm w\<close>,
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
The proof is then trivial by distinguishing the cases where \<open>\<alpha> = [Nt S]\<close> and \<open>\<beta> = []\<close>, and vice versa,
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
We can now induct on \<open>\<rho>\<close> for arbitrary \<open>\<gamma>, \<alpha>, \<beta>, A, w,\<close> and \<open>v\<close>, akin to the proof by 
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
We begin our proof by strong induction on \<open>n\<close> for arbitrary \<open>A, u, \<alpha>, \<beta>,\<close> and \<open>\<rho>\<close>.

If \<open>n = 0\<close>, the implication is trivial.

Otherwise, if \<open>n = Suc m\<close> for some \<open>m\<close>, we proceed with a case distinction on the first step of the 
computation. 

If the first step is a shifting or a reducing transition, the implication holds by the induction
hypothesis.

If the first step is an expanding transition, there exist \<open>Y :: 'n\<close> and \<open>\<gamma> :: syms\<close> with
\<open>\<beta> = Nt Y # \<gamma>\<close> and
\begin{multline*}
\<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I ([Y \<rightarrow> \<cdot> \<gamma>] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u)\<close>\\
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
prefix @{term \<open>hist (rev \<rho>)\<close>} of the input is consumed, the computation is independent of the
remaining string. Therefore, the computation
\begin{equation}\label{ipda_char.calc}
@{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ \<alpha>) \<turnstile>c* ([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], \<alpha>)\<close>}
\end{equation}
also exists. Furthermore, \eqref{ipda_char.red} implies that \mbox{@{term \<open>(A, \<alpha> @ \<beta>) \<in> Prods G'\<close>}} 
by the definition of the \<open>I\<^sub>G\<close> transition relations. Therefore, \eqref{ipda_char.calc} continues with
\[ \<open>\<dots> \<turnstile>c ([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>], \<alpha>)\<close>. \]
The RHS can then reach our target configuration by Lemma~\ref{char_steps_consume}, completing the
proof. Along with Lemmas~\ref{char_imp_derivers} and \ref{derivers_imp_ipda}, this also completes 
the proof of Theorem~\ref{char_derivers_ipda_iffs}.
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
\concept{valid} for \<open>\<gamma>\<close>. We also define the set of all valid items for \<open>\<gamma>\<close>:
\[ @{thm valids_def}. \]
\end{definition}

\begin{theorem}\label{char_eq_reliable_prefix}[Equivalence of @{const char_fa} computations and reliable prefixes]
There exists a @{const char_fa} computation @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>}
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
@{thm char_fa_nextl_is_valids}
\qed
\end{lemma}\<close>

subsection \<open>The Canonical \<open>LR(0)\<close> Automaton\<close>

text\<open>Now that we have defined @{const char_fa} and proved several useful properties, we can finally
define a deterministic automaton that our parser can use. Since @{const char_fa} is an NFA, we 
define the \concept{canonical \<open>LR(0)\<close> automaton} @{const LR\<^sub>0} as the @{typeof LR\<^sub>0} resulting from 
the powerset construction restricted to reachable states. The automaton is once more defined using 
Paulson's theory~\<^cite>\<open>Paulson\<close>. We now show some properties we will need in our parser.

\begin{corollary}\label{nextl_dfa_LR0_is_valids}
The state that @{const LR\<^sub>0} reaches after reading input word \<open>\<gamma>\<close> is \<open>valids \<gamma>\<close>.
\begin{proof}
This is a consequence of Lemma~\ref{char_fa_nextl_is_valids} and the definition of the transition 
function of the DFA resulting from the powerset construction.
\end{proof}
\end{corollary}

\begin{lemma}\label{state_imp_valids}
For every state @{prop \<open>q \<in> dfa.states LR\<^sub>0\<close>}, there exists a \<open>\<gamma> :: syms\<close> such that 
@{prop \<open>q = valids \<gamma>\<close>}.
\begin{proof}
Since we define the states of @{const LR\<^sub>0} to be restricted to the reachable states resulting 
from the powerset construction of @{term char_fa}, we also know that there exists an input string \<open>\<gamma>\<close> 
such that @{const LR\<^sub>0} is in state \<open>q\<close> after reading \<open>\<gamma>\<close>. By Corollary~\ref{nextl_dfa_LR0_is_valids},
this implies \<open>q = valids \<gamma>\<close>.
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
\[ @{thm (concl) nxt_dfa_LR0_shift_is_valids_app} \]
\begin{proof}
By Lemma~\ref{dfa_LR0_nxt_is_epsclo_of_shift}, @{term \<open>dfa.nxt LR\<^sub>0 (valids \<gamma>) X\<close>} is equivalent to 
the set
\[ @{term \<open>char_fa.epsclo {[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]|A \<alpha> \<beta>. [A \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> valids \<gamma>}\<close>}. \]
We will abbreviate this set as \<open>\<E>\<close>.

First, we will show that \<open>\<E>\<close> is a subset of @{term \<open>valids (\<gamma> @ [X])\<close>} by 
Lemma~\ref{eps_reliable_preserved}.

We now show that @{term \<open>valids (\<gamma> @ [X])\<close>} is a subset of \<open>\<E>\<close> to complete the proof.

We assume @{prop \<open>i \<in> valids (\<gamma> @ [X])\<close>}, which means that either
\<open>i\<close> is a complete item, or an incomplete item of the form @{term \<open>[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]\<close>}.
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

text \<open>\begin{definition}[Canonical \<open>LR(0) parser\<close>]
Let @{term \<Delta>\<^sub>G} be the transition relation of the canonical \<open>LR(0)\<close> automaton @{const LR\<^sub>0}, 
\<open>q\<^sub>0\<close> the initial state of @{const LR\<^sub>0}, \<open>Q\<close> the set of states of @{const LR\<^sub>0}, and \<open>f\<close> the singleton 
set @{term \<open>{[S' \<rightarrow> \<cdot> ]}\<close>}.
The \concept{canonical \<open>LR(0)\<close> parser} to the CFG \<open>G\<close> is the @{typeof P\<^sub>0}
\[ @{const P\<^sub>0} = @{term \<open>\<lparr>states = Q \<union> {f}, init = q\<^sub>0, final = {f}, nxt = \<Delta>\<^sub>0, eps = \<E>\<^sub>0\<rparr>\<close>}. \]
\end{definition}

Similarly to the IPDA, we define three types of transitions, two of which are in the
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
parser replaces the topmost stack list \<open>[q\<^sub>1, q\<^sub>2, \<dots>, \<close> @{term \<open>sub' q (length \<alpha>)\<close>} \<open>, q]\<close> by 
@{term \<open>[\<Delta>\<^sub>G q (Nt X), q]\<close>}. Formally we define these transitions by the set
\begin{multline*}
  \<open>{let q = last (q\<^sub>n#qs) in (q\<^sub>n # qs, \<Delta>\<^sub>G q (Nt X) # [q])\<close>\\
      \<open>| q\<^sub>n qs X \<alpha>. set (q\<^sub>n#qs) \<subseteq> Q \<and> [X \<rightarrow> \<alpha> \<cdot> ] \<in> q\<^sub>n\<close>\\ 
      \<open>\<and>\<close> @{prop \<open>length \<alpha> = length qs \<and> X \<noteq> S'\<close>}\<open>}.\<close>
\end{multline*}
\item Lastly, \concept{finishing} transitions reduce the complete item @{term \<open>[S' \<rightarrow> [Nt S] \<cdot> ]\<close>}. 
Reducing \<open>S'\<close> in the conventional sense is not possible; therefore, the finish transition signals 
that the parser has successfully reduced the processed input to the start symbol, and it does so by 
reducing the topmost state to the singleton state @{term \<open>{f}\<close>} if the second to last state is \<open>q\<^sub>0\<close>.
Finish transitions therefore correspond to the set 
\[ @{term \<open>{([q, q\<^sub>0], [f])|q. q \<in> Q \<and> [S' \<rightarrow> [Nt S] \<cdot> ] \<in> q}\<close>}. \]
\end{enumerate}
The set \<open>\<E>\<^sub>0\<close> is therefore defined as the union of the sets for reduce and finish transitions. 

Our definition of @{const P\<^sub>0} is very similar to that of Wilhelm et al., except that we, as we did when
defining \<open>I\<^sub>G\<close>, restrict the elements of the transition relations to elements of \<open>Q\<close> explicitly
to overcome the same problem we had in the IPDA section. In this case, however, this has one more
benefit: since \<open>Q\<close> is actually a subset of the states of @{const P\<^sub>0}, by restricting our transition functions
to \<open>Q\<close> only, instead of @{term \<open>Q \<union> {f}\<close>}, our transition relations are more well-defined, since we
guarantee that every state that gets passed to the @{const LR\<^sub>0} transition function is a state in 
@{const LR\<^sub>0}. A second detail we added is the condition @{prop \<open>X \<noteq> S'\<close>} in the reduce transition 
relation. This could lead to nondeterministic behavior, since the finish transition condition 
@{prop \<open>[S' \<rightarrow> [Nt S] \<cdot> []] \<in> q\<close>} also implies the reduce transition condition 
@{prop \<open>[X \<rightarrow> \<alpha> \<cdot> []] \<in> q\<^sub>n\<close>}. Restricting reduce transitions only for items fulfilling this 
property causes reduce and finish transitions to be mutually exclusive, avoiding this problem.

Another minor distinction is that Wilhelm et al. define the final state of the parser as an 
unspecified fresh state not in \<open>Q\<close>. To achieve this, we simply fixed \<open>f\<close> as the singleton set we 
described above because the item \<open>[S' \<rightarrow> \<cdot> ]\<close> is not in @{term \<open>It G'\<close>}, and therefore not in \<open>Q\<close>, 
by the definition of \<open>G'\<close>. The choice of \<open>f\<close>, however, is irrelevant as long as it is not an element
of \<open>Q\<close>.\<close>

subsubsection \<open>Finiteness of the Transition Relations of @{const P\<^sub>0}\<close>

text \<open>We mentioned when defining GPDAs that we do not assume the transition relation to be finite.
This is only because the first GPDA we defined, i.e., the IPDA, only acts as a theoretical construct 
that aids us in proving useful and interesting properties in order to achieve our end goal of a
deterministic parsing algorithm. The \<open>LR(0)\<close> parser is not the same, since this is precisely the
machine we want to achieve determinism with. If we want to define a parser that can actually be used
in practice, its transition relation must be executable, i.e., we need to be able to define a
function to execute our parser's steps. If one defines an automaton as having a transition function,
as is the case for Paulson's DFAs, for example, executability is guaranteed by definition, but the
same does not hold in general when transitions are defined as a relation, which is precisely the
situation of our parser definition.

One possibility of making such a relation executable is through tables: if one has an (n+1)-ary
relation \<open>R\<close>, one can trivially define a function that maps each tuple \<open>(x\<^sub>1, x\<^sub>2, \<dots>, x\<^sub>n)\<close> to a list
\<open>ys\<close> such that for every \<open>y\<close> in \<open>ys\<close> holds \<open>(x\<^sub>1, x\<^sub>2, \<dots>, x\<^sub>n, y) \<in> R\<close> by iterating through the
set. It is easy to see, however, that this method is only possible if \<open>R\<close> is finite.

We can now prove that the transition relations of the @{const P\<^sub>0} are finite.

\begin{proposition}\label{finite_nxt_P0}
The @{const nxt} relation of @{const P\<^sub>0} is finite.
\begin{proof}
Let @{term \<open>f(q, a) = ([q], a, [dfa.nxt LR\<^sub>0 q (Tm a), q])\<close>} be a mapping from \<open>item set \<times> 't\<close> to
\<open>item set list \<times> 't \<times> item set list\<close>. Furthermore, let \<open>T\<close> be the set 
\[ @{prop \<open>T = {(q, a)|q a. q \<in> dfa.states LR\<^sub>0 \<and> dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}}\<close>}. \]
It is easy to see that \<open>nxt\<close> is a subset of @{term \<open>f ` T\<close>}. Thus, it suffices to prove that \<open>T\<close> is 
finite.

\<open>T\<close> is the union of the sets @{term \<open>{(q, a)| a. dfa.nxt LR\<^sub>0 q (Tm a) \<noteq> {}}\<close>} for each
state \<open>q\<close> of @{term LR\<^sub>0}. We can then prove that each of these sets is finite by proving that for
any item set \<open>q\<close>, the set @{term \<open>{X. dfa.nxt LR\<^sub>0 q X \<noteq> {}}\<close>} is finite. This is because if for a 
symbol \<open>X\<close> holds @{prop \<open>dfa.nxt LR\<^sub>0 q X \<noteq> {}\<close>}, there must exist an item in the \<open>\<epsilon>\<close>-closure of 
@{term \<open>q \<inter> It G'\<close>} of the form @{term \<open>[A \<rightarrow> \<alpha> \<cdot> X # \<beta>]\<close>}. Since the \<open>\<epsilon>\<close>-closure of @{const char_fa}
is finite for any set, the proof is complete.
\end{proof}
\end{proposition}

\begin{lemma}\label{finite_lists_complete_length_eq}
The set 
\[ @{prop \<open>L = {q # qs| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 \<and> [X \<rightarrow> \<alpha> \<cdot> ] \<in> q 
    \<and> length \<alpha> = length qs \<and> X \<noteq> S'}\<close>} \]
is finite.
\begin{proof}
We know \<open>L\<close> is a subset of @{term \<open>f ` {(q, qs, X, \<alpha>)| q qs X \<alpha>. set (q # qs) \<subseteq> dfa.states LR\<^sub>0 
    \<and> [X \<rightarrow> \<alpha> \<cdot> []] \<in> q \<and> length \<alpha> = length qs \<and> X \<noteq> S'}\<close>} with the mapping 
@{prop \<open>f (q, qs, X, \<alpha>) = q # qs\<close>}. Moreover, it is easy to see that the set whose image is a superset 
of \<open>L\<close> is finite: all the items sets that make up the lists in \<open>L\<close> are states of @{const LR\<^sub>0}, i.e.,
they are finite. Therefore, there are finitely many items in the head \<open>q\<close> of each list of the form
@{term \<open>[X \<rightarrow> \<alpha> \<cdot> ]\<close>} with \<open>X \<noteq> S'\<close>. Lastly, for each of these items, there are finitely many lists
\<open>qs\<close> such that @{prop \<open>length \<alpha> = length qs\<close>}. This is because every element of each list is in the
set of states of @{const LR\<^sub>0}, which is finite. This completes the proof.
\end{proof}
\end{lemma}

\begin{lemma}\label{finite_eps_P0_reduce}
The set of reduce transitions \<open>R\<close> of @{const P\<^sub>0} is finite.
\begin{proof}
Consider set \<open>L\<close> from Lemma~\ref{finite_lists_complete_length_eq}, which this Lemma tells us is finite.
It can easily be shown that @{prop \<open>R \<subseteq> L \<times> {[p, q]|p q. p \<in> dfa.states LR\<^sub>0 \<and> q \<in> dfa.states LR\<^sub>0}\<close>}.
Moreover, the set @{term \<open>{[p, q]|p q. p \<in> dfa.states LR\<^sub>0 \<and> q \<in> dfa.states LR\<^sub>0}\<close>} can trivially be
shown to be finite through a bijection with @{term \<open>dfa.states LR\<^sub>0 \<times> dfa.states LR\<^sub>0\<close>},
completing the proof.
\end{proof}
\end{lemma}

\begin{proposition}\label{finite_eps_P0}
The @{const eps} relation of @{const P\<^sub>0} is finite.
\begin{proof}
By definition, @{const eps} is the union of the reduce and finish relation sets. 

The set of finish transitions is trivially a subset of @{term \<open>f ` dfa.states LR\<^sub>0\<close>} 
with @{term \<open>f q = ([q, dfa.init LR\<^sub>0], [P0_final])\<close>}. The finiteness of @{const eps} then follows by
the finiteness of the states of @{const LR\<^sub>0} and Lemma~\ref{finite_eps_P0_reduce}.
\end{proof}
\end{proposition}

With Propositions~\ref{finite_nxt_P0} and \ref{finite_eps_P0} we have shown a sufficient condition
for an executable transition function of the canonical \<open>LR(0)\<close> parser. \<close>

subsection \<open>\<open>LR(0)\<close>-Adequate and Inadequate States\<close>

text \<open>Even though our modified @{const P\<^sub>0} definition circumvents the issue between reduce and finish 
transitions we described before, nondeterminism is still a problem in several other cases. We 
define two types of \concept{conflicts} that can be present in parser states which can lead to 
nondeterministic behavior, as defined by Wilhelm et al.~\cite[p. 110]{Wilhelm}:

\begin{definition}[Shift-reduce/reduce-reduce conflicts and \<open>LR(0)\<close> inadequacy]
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

We will now show a lemma that Wilhelm et al. present without proof, and which we will need in the
future to show the final theorem of the \<open>LR(0)\<close> section in the book. First, we prove an auxiliary
lemma:

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
We can now distinguish cases based on whether \<open>\<delta>\<close> consists exclusively of terminals.

If \<open>\<delta>\<close> contains no nonterminals, there exists an \<open>X' :: 'n\<close> such that @{prop \<open>X = Nt X'\<close>}. Furthermore, 
there also exists a production @{prop \<open>(X', \<chi>) \<in> Prods G'\<close>} which was applied in the last derivation 
step was applied, meaning @{prop \<open>\<chi> @ \<delta> = Y # \<gamma>\<close>}. This implies that \<open>\<chi>\<close> cannot be the empty word; 
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
for some \<open>A\<close> and \<open>\<alpha>\<close>. We now consider another two cases on whether \<open>q\<close> has any incomplete items;
if it has none, it fulfils condition (2).

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
@{prop \<open>mbox0 ([Y \<rightarrow> \<cdot> map Tm w] \<in> q)\<close>} as well. We can now perform a case distinction on \<open>w\<close>: if 
@{prop \<open>w = []\<close>}, the implication holds since @{prop \<open>[Y \<rightarrow> \<cdot> map Tm w] = [A \<rightarrow> \<alpha> \<cdot> ]\<close>} and
@{prop \<open>[Nt Y] = \<gamma>\<close>}. If on the other hand \<open>w\<close> is nonempty, \<open>q\<close> has a shift-reduce conflict, which
contradicts its \<open>LR(0)\<close>-adequacy. This completes the reflexive case, and we can now move on to the 
other case.

For the transitive case, we know \<open>Y\<close> derives \<open>\<gamma>\<close> in @{term \<open>Suc n\<close>} steps for some \<open>n :: nat\<close>. 
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
\<open>w, x, y :: 't list\<close>,
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
generalized definition applicable to an arbitrary CFG in a later section, but the original
definition suffices to prove the main theorem for the section on \<open>LR(0)\<close> parsing presented by 
Wilhelm et al.~\cite[p. 114]{Wilhelm}, since it relates the \<open>LR(k)\<close> condition only to the parser,
which we have also restricted to extended grammars. Before this theorem, we show some auxiliary 
lemmas.

\begin{lemma}\label{derivern_Suc_substring_reliable}
If a rightmost derivation @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(Suc n) \<alpha> @ \<beta> @ Nt X # map Tm w\<close>} exists,
there also exists an incomplete item @{term \<open>mbox [A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>']\<close>} valid for \<open>\<alpha>\<close> with
\begin{gather*}
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Y # \<beta>' @ map Tm w'\<close>}\\
@{prop \<open>Prods G' \<turnstile> Y # \<beta>' @ map Tm w' \<Rightarrow>r* \<beta> @ Nt X # map Tm w\<close>}
\end{gather*}
\begin{proof}
Since the rightmost derivation has length greater than zero, we know there exists a \<open>\<rho>\<close> where
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<alpha> @ \<beta> @ Nt X # map Tm w\<close>}. The length of the derivation also 
implies @{prop \<open>[Nt S'] \<noteq> \<alpha> @ \<beta> @ Nt X # map Tm w\<close>}. We now use this inequality to induct on \<open>\<rho>\<close> 
for arbitrary \<open>X, \<alpha>, \<beta>\<close> and \<open>w\<close>. 

The case \<open>\<rho> = []\<close> cannot hold, since it would contradict the inequality.

If \<open>\<rho> = i # \<sigma>\<close> for some \<open>i\<close> and \<open>\<sigma>\<close>, performing rule inversion on the rightmost chain implies the
existence of some \<open>A :: 'n\<close>, \<open>\<alpha>', \<alpha>'', \<beta>' :: syms\<close>, and \<open>u, v :: 't list\<close> such that
\begin{subequations}
\begin{gather}
@{prop \<open>i = [A \<rightarrow> \<alpha>'' \<cdot> Nt X # \<beta>']\<close>}\label{der_sucn.start}\\
\begin{multlined}\label{der_sucn.eq}
\<open>\<alpha> @ \<beta> @ Nt X # map Tm w\<close>\\
  = \<open>\<alpha>' @ \<alpha>'' @ Nt X # map Tm u @ map Tm v\<close>
\end{multlined}\\
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<sigma>\<rightarrow>r* \<alpha>' @ Nt A # map Tm v\<close>}\label{der_sucn.sig}\\
\begin{multlined}\label{der_sucn.deriver}
\<open>Prods G' \<turnstile> \<alpha>' @ Nt A # map Tm v\<close>\\
  \<open>\<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm v\<close>
\end{multlined}\\
@{prop \<open>Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm u\<close>}\label{der_sucn.end}
\end{gather}
\end{subequations}
We can now use \eqref{der_sucn.sig} in a second rule inversion.

The reflexive case implies \<open>\<alpha> = \<beta> = []\<close>, \<open>X = S\<close> and \<open>w = []\<close>, and the implication holds for item 
@{term [source] \<open>[S' \<rightarrow> [] \<cdot> Nt S # []]\<close>}.

In the \<open>step\<close> case, we can distinguish two cases based on \eqref{der_sucn.eq}: either \<open>\<alpha>\<close> is a 
prefix of \<open>\<alpha>'\<close>, or vice versa. 

If \<open>\<alpha>\<close> is a prefix of \<open>\<alpha>'\<close>, there exists some \<open>\<gamma>\<close> where @{prop \<open>\<alpha>' = \<alpha> @ \<gamma>\<close>} and 
@{prop \<open>\<beta> = \<gamma> @ \<alpha>''\<close>}. Therefore, this is the case where a previous, shorter chain already derived 
our prefix \<open>\<alpha>\<close>, meaning we will work towards using our induction hypothesis. To achieve this, we can 
use equations \eqref{der_sucn.start} - \eqref{der_sucn.end} to show that 
\[ @{prop \<open>Prods G' \<turnstile> \<gamma> @ Nt A # map Tm v \<Rightarrow>r* \<beta> @ Nt X # map Tm w\<close>}. \]
Furthermore, with our \<open>step\<close> assumptions for \eqref{der_sucn.sig}, 
@{prop \<open>[Nt S'] \<noteq> \<alpha> @ \<gamma> @ Nt A # map Tm v\<close>} must hold. With all this we can show the claim holds 
by the IH. 

On the other hand, if \<open>\<alpha>'\<close> is a prefix of \<open>\<alpha>\<close> there exists some \<open>\<gamma>\<close> with
@{prop \<open>\<alpha> = \<alpha>' @ \<gamma>\<close>} and @{prop \<open>\<alpha>'' = \<gamma> @ \<beta>\<close>}. Furthermore, by \eqref{der_sucn.deriver} and 
\eqref{der_sucn.eq} we have 
\begin{equation}\label{der_sucn.A_deriver}
@{prop \<open>Prods G' \<turnstile> \<alpha>' @ Nt A # map Tm v \<Rightarrow>r \<alpha> @ \<beta> @ Nt X # \<beta>' @ map Tm v\<close>}.
\end{equation}
All this implies that @{term \<open>[A \<rightarrow> \<gamma> \<cdot> \<beta> @ Nt X # \<beta>']\<close>} is valid for \<open>\<alpha>\<close>. Moreover,
from \eqref{der_sucn.end} we have that 
@{prop \<open>Prods G' \<turnstile> \<beta> @ Nt X # \<beta>' @ map Tm v \<Rightarrow>r* \<beta> @ Nt X # map Tm w\<close>}, again by \eqref{der_sucn.eq}.
Finally, Lemma~\ref{rm_chain_imp_derivers} with \eqref{der_sucn.sig}, followed by
\eqref{der_sucn.A_deriver} by transitivity, imply that the claim holds for item 
@{term \<open>[A \<rightarrow> \<gamma> \<cdot> \<beta> @ Nt X # \<beta>']\<close>}.
\end{proof}
\end{lemma}

\begin{lemma}\label{derivers_substring_reliable}
If a rightmost derivation 
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ \<beta> @ Nt X # map Tm w\<close>} \] 
exists, there also exists an incomplete item valid for \<open>\<alpha>\<close>.
\begin{proof}
The proof is by a case distinction on the derivation length. If it is \<open>0\<close>, \<open>\<alpha>\<close> must be an empty 
string. Since @{term \<open>[S' \<rightarrow> \<cdot> [Nt S]]\<close>} is valid for @{const Nil}, the implication holds.

If the length is greater than \<open>0\<close>, the claim follows directly from 
Lemma~\ref{derivern_Suc_substring_reliable}.
\end{proof}
\end{lemma}

\begin{lemma}\label{prefix_comp_unique_imp_eps}
If the set @{term \<open>valids \<alpha>\<close>} is \<open>LR(0)\<close>-adequate and contains item @{term \<open>mbox [X \<rightarrow> \<cdot>]\<close>}, then 
\begin{equation*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ \<alpha>' @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ map Tm y\<close>
\end{equation*}
implies @{prop \<open>\<alpha>' = [] \<and> Y = X \<and> x = y\<close>}.
\begin{proof}
We first distinguish cases on the length of the derivation of \<open>\<alpha> @ \<alpha>' @ Nt Y # map Tm x\<close>.

If the length is \<open>0\<close>, the implication holds trivially by reflexivity.

If the length is nonzero, by Lemma~\ref{derivern_Suc_substring_reliable} there exists an item 
@{term \<open>mbox [A \<rightarrow> \<beta> \<cdot> Z' # \<gamma>]\<close>} in @{term \<open>valids \<alpha>\<close>} such that for some \<open>z\<close> holds
\begin{multline}\label{pref_eps.deriver}
 \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Z' # \<gamma> @ map Tm z\<close>\\
\<open>\<Rightarrow>r* \<alpha>' @ Nt Y # map Tm x\<close>.
\end{multline}
By case 3 of Lemma~\ref{LR0_adequate_cases}, we know there exists some nonterminal \<open>Z''\<close> with
@{prop \<open>Z' = Nt Z''\<close>}. This, the final step in the rightmost derivation in our assumption, and 
\eqref{pref_eps.deriver} imply that the derivation
\begin{multline*}
\<open>Prods G' \<turnstile> Nt Z'' # \<gamma> @ map Tm z \<Rightarrow>r* \<alpha>' @ Nt Y # map Tm x\<close>\\
\<open>\<Rightarrow>r map Tm y\<close>.
\end{multline*}
can be decomposed into
\begin{multline*}
\<open>Prods G' \<turnstile> Nt Z'' # \<gamma> @ map Tm z \<Rightarrow>r* Nt Z'' # map Tm v\<close>\\
  \<open>\<Rightarrow>r* \<gamma>' @ map Tm v \<Rightarrow>r map Tm y\<close>
\end{multline*}
for some \<open>\<gamma>' :: syms\<close> and \<open>v :: 't list\<close> with @{prop \<open>\<gamma>' @ map Tm v = \<alpha>' @ Nt Y # map Tm x\<close>}.
This decomposition in turn implies the existence of some \<open>u :: 't list\<close> such that 
@{prop \<open>y = u @ v\<close>} and
\[ \<open>Prods G' \<turnstile> [Nt Z''] \<Rightarrow>r* \<gamma>' \<Rightarrow>r map Tm u\<close>.  \]
By case 3 of Lemma~\ref{LR0_adequate_cases}, this implies that @{prop \<open>\<gamma>' = Nt X # map Tm u\<close>}.
This and the decomposition of the derivation imply 
\[ \<open>\<alpha>' @ Nt Y # map Tm x = Nt X # map Tm y\<close>. \]
From this follows @{prop \<open>\<alpha>' = [] \<and> Y = X \<and> x = y\<close>}, completing the proof.
\end{proof}
\end{lemma}

\begin{lemma}\label{is_LR_wlogI}
In order to prove that \<open>G'\<close> is an \<open>LR(k)\<close> grammar, it suffices to prove for arbitrary 
\<open>\<alpha>, \<beta>, \<gamma>, \<delta> :: syms\<close>, \<open>X, Y :: 'n\<close>, and \<open>w, x, y :: 't list\<close>:

The conjunction of the following statements
\begin{gather*}
\begin{multlined}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w\<close>,
\end{multlined}\\
\begin{multlined}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>,
\end{multlined}\\
@{prop \<open>\<gamma> @ \<delta> @ map Tm x = \<alpha> @ \<beta> @ map Tm y\<close>},\\
@{prop \<open>length (\<alpha> @ \<beta>) \<le> length (\<gamma> @ \<delta>)\<close>},\\
@{prop \<open>take k w = take k y\<close>}
\end{gather*}
implies @{prop \<open>\<alpha> = \<gamma>\<close>}, @{prop \<open>X = Y\<close>}, and @{prop \<open>x = y\<close>}.
\begin{proof}
We begin by assuming that our implication holds, i.e., the conjunction of the statements above 
indeed implies @{prop \<open>\<alpha> = \<gamma> \<and> X = Y \<and> x = y\<close>}. Let (I) be this implication. Now it must be shown 
that (I) implies the \<open>LR(k)\<close> condition for \<open>G'\<close>. We therefore fix two rightmost derivations
\begin{gather}
\begin{multlined}\label{LR_wlog.X}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w\<close>
\end{multlined}
\intertext{and}
\begin{multlined}\label{LR_wlog.Y}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>
\end{multlined}
\intertext{such that}
@{prop \<open>take k w = take k y\<close>}\label{LR_wlog.wkyk},
\end{gather}
and our goal is to show that @{prop \<open>\<alpha> = \<gamma> \<and> X = Y \<and> x = y\<close>} holds.

By \eqref{LR_wlog.Y}, there exists a production \<open>(Y, \<delta>)\<close> that was applied in the last step, meaning 
\begin{equation}\label{LR_wlog.deriver}
@{prop \<open>\<alpha> @ \<beta> @ map Tm y = \<gamma> @ \<delta> @ map Tm x\<close>}.
\end{equation}
We now distinguish two cases: @{prop \<open>length (\<alpha> @ \<beta>) \<le> length (\<gamma> @ \<delta>)\<close>} and 
@{prop \<open>length (\<gamma> @ \<delta>) \<le> length (\<alpha> @ \<beta>)\<close>}.

If @{prop \<open>length (\<alpha> @ \<beta>) \<le> length (\<gamma> @ \<delta>)\<close>}, @{prop \<open>\<alpha> = \<gamma> \<and> X = Y \<and> x = y\<close>} follows by (I) and
equations \eqref{LR_wlog.X} - \eqref{LR_wlog.deriver}.

If @{prop \<open>length (\<gamma> @ \<delta>) \<le> length (\<alpha> @ \<beta>)\<close>}, by \eqref{LR_wlog.deriver} we know that there exists 
some \<open>z :: 't list\<close> such that 
\begin{equation}\label{LR_wlog.ab_eq}
@{prop \<open>\<alpha> @ \<beta> = \<gamma> @ \<delta> @ map Tm z\<close>} \text{ and } @{prop \<open>x = z @ y\<close>}.
\end{equation} 
Furthermore, this and \eqref{LR_wlog.wkyk} imply that @{prop \<open>take k x = take k (z@w)\<close>}. With this 
we can finally show @{prop \<open>\<alpha> = \<gamma> \<and> X = Y \<and> x = y\<close>} by substituting \eqref{LR_wlog.ab_eq} into the 
final step of \eqref{LR_wlog.X}, and \eqref{LR_wlog.deriver} into the final step of 
\eqref{LR_wlog.Y}.
\end{proof}
\end{lemma}

This lemma tells us that when proving the \<open>LR(k)\<close> condition holds for \<open>G'\<close>, we can assume without 
loss of generality that \<open>\<alpha> @ \<beta>\<close> is a prefix of \<open>\<gamma> @ \<delta>\<close>, where \<open>\<delta>\<close> is the handle of 
\<open>\<alpha> @ \<beta> @ map Tm y\<close>. In other words, we can assume WLOG that the handle of \<open>\<alpha> @ \<beta> @ map Tm y\<close> is not 
contained in \<open>\<alpha> @ \<beta>\<close>, except in the case of equality. This assumption will greatly simplify the proof 
of the following theorem.

\begin{theorem}\label{is_LR0_iff_no_LR0_inadequates}
\<open>G'\<close> is an \<open>LR(0)\<close> grammar if and only if @{const LR\<^sub>0} has no \<open>LR(0)\<close>-inadequate states.
\begin{proof}
For direction "\<open>\<Longrightarrow>\<close>", we prove the implication by contradiction.
Assume \<open>G'\<close> is \<open>LR(0)\<close> and @{const LR\<^sub>0} has an \<open>LR(0)\<close>-inadequate state \<open>q\<close> meaning it either has a 
shift-reduce or a reduce-reduce conflict. 

If \<open>q\<close> has a shift-reduce conflict, there exist two items @{term \<open>[X \<rightarrow> \<beta> \<cdot> ]\<close>} and 
@{term \<open>mbox [Y \<rightarrow> \<delta> \<cdot> Tm a # \<alpha>]\<close>} in \<open>q\<close>. By Lemma~\ref{state_imp_valids}, we know there exists some 
\<open>\<gamma> :: syms\<close> that is a reliable prefix for both of these states. Therefore, there exist rightmost
derivations of the form
\begin{gather}
  \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt X # map Tm w \<Rightarrow>r \<gamma>' @ \<beta> @ map Tm w\<close>\label{LR0_iff.X_derivers1}
\intertext{and}
\begin{multlined}\label{LR0_iff.Y_derivers1}
  \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<nu> @ Nt Y # map Tm y\<close>\\
  \<open>\<Rightarrow>r \<nu> @ \<delta> @ Tm a # \<alpha> @ map Tm y\<close>
\end{multlined}
\intertext{such that}
\<open>\<gamma> = \<gamma>' @ \<beta> = \<nu> @ \<delta>\<close>\label{LR0_iff.g_rp}
\end{gather}
Since \<open>G'\<close> is reduced, there exists some \<open>v :: 't list\<close> derived by \<open>\<alpha>\<close>. 
If this derivation has length 0, i.e., \<open>\<alpha> = map Tm v\<close>, we get a contradiction, since the \<open>LR(0)\<close> 
condition requires $\<open>y\<close> \overset{!}{=} \<open>a # v @ y\<close>$, which clearly cannot hold.

On the other hand, if the rightmost derivation of \<open>v\<close> has a final step of the form 
\begin{multline*}
\<open>Prods G' \<turnstile> \<alpha> \<Rightarrow>r* map Tm u @ Nt Z # map Tm x\<close>\\
  \<open>\<Rightarrow>r map Tm (u @ v' @ x) = map Tm v\<close>,
\end{multline*}
with \eqref{LR0_iff.Y_derivers1} and \eqref{LR0_iff.g_rp}, this implies
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S']\<close>\\
  \<open>\<Rightarrow>r* \<nu> @ \<delta> @ Tm a # map Tm u @ Nt Z # map Tm (x @ y)\<close>\\
  \<open>\<Rightarrow>r \<gamma>' @ \<beta> @ Tm a # map Tm (u @ v' @ x @ y)\<close>.
\end{multline*}
This is again a contradiction, since by \eqref{LR0_iff.X_derivers1} the \<open>LR(0)\<close> condition requires 
$\<open>x @ y\<close> \overset{!}{=} \<open>a # u @ v' @ x @ y\<close>$. This finishes the case where state \<open>q\<close> has a 
shift-reduce conflict.

In the case where \<open>q\<close> has a reduce-reduce conflict, there exist two distinct complete items 
@{term \<open>[X \<rightarrow> \<beta> \<cdot> ]\<close>} and @{term \<open>[Y \<rightarrow> \<delta> \<cdot> ]\<close>} in \<open>q\<close>. Once again by Lemma~\ref{state_imp_valids},
there exists a \<open>\<gamma>\<close> for which both items are valid. Therefore, there exist rightmost derivations of 
the form
\begin{gather*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt X # map Tm w \<Rightarrow>r \<gamma>' @ \<beta> @ map Tm w\<close>
\intertext{and}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<nu> @ Nt Y # map Tm y \<Rightarrow>r \<nu> @ \<delta> @ map Tm y\<close>
\end{gather*}
with \<open>\<gamma> = \<gamma>' @ \<beta> = \<nu> @ \<delta>\<close>. Since the two items are distinct, there are two cases:
\begin{itemize}
\item \<open>\<beta> \<noteq> \<delta>\<close>, implying \<open>\<gamma>' \<noteq> \<nu>\<close>; or
\item \<open>X \<noteq> Y\<close>
\end{itemize}
Either case contradicts the \<open>LR(0)\<close> condition, thus proving the reduce-reduce case.

We now move on to direction "\<open>\<Longleftarrow>\<close>". We assume the canonical \<open>LR(0)\<close> automaton has no 
\<open>LR(0)\<close>-inadequate states, must prove that the \<open>LR(0)\<close> condition holds for \<open>G'\<close>. By 
Lemma~\ref{is_LR_wlogI}, consider rightmost derivations
\begin{subequations}
\begin{gather*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w\<close>\label{LR0_iff.X_derivers2}\\
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>\label{LR0_iff.Y_derivers2}\\
\intertext{such that the following hold}
@{prop \<open>\<gamma> @ \<delta> @ map Tm x = \<alpha> @ \<beta> @ map Tm y\<close>}\label{LR0_iff.ydx}\\
@{prop \<open>length (\<alpha> @ \<beta>) \<le> length (\<gamma> @ \<delta>)\<close>}\label{LR0_iff.leq}
\end{gather*}
\end{subequations}
We have to show @{prop \<open>\<alpha> = \<gamma>\<close>}, @{prop \<open>X = Y\<close>}, and @{prop \<open>x = y\<close>}. We omit the premise 
@{prop \<open>take 0 w = take 0 y\<close>} since it is trivially true for any two lists.

Let \<open>p\<close> be the state that @{const LR\<^sub>0} reaches after reading input word @{term \<open>\<alpha> @ \<beta>\<close>}. By 
Corollary~\ref{nextl_dfa_LR0_is_valids}, we know that this state is the set @{term \<open>valids (\<alpha> @ \<beta>)\<close>}. 
With \eqref{LR0_iff.X_derivers2}, this implies that @{prop \<open>[X \<rightarrow> \<beta> \<cdot> ] \<in> p\<close>}. Since by our initial 
assumption, \<open>p\<close> is \<open>LR(0)\<close>-adequate, we can now consider the three cases that
Lemma~\ref{LR0_adequate_cases} gives us.

If \<open>p\<close> consists of a single complete item, @{prop \<open>p = {[X \<rightarrow> \<beta> \<cdot> ]}\<close>} must hold. Moreover, 
\eqref{LR0_iff.ydx} and \eqref{LR0_iff.leq} imply the existence of some \<open>z :: 't\<close> list such that
\begin{equation}\label{LR0_iff.z_defs}
@{prop \<open>\<gamma> @ \<delta> = \<alpha> @ \<beta> @ map Tm z\<close>} \text{ and } @{prop \<open>z @ x = y\<close>}.
\end{equation}

We can now distinguish two more cases based on whether \<open>\<alpha> @ \<beta>\<close> is a substring of \<open>\<gamma>\<close>.

If this is true, there exist \<open>u, v :: 't list\<close> such that \<open>\<gamma> = \<alpha> @ \<beta> @ map Tm u\<close>, \<open>\<delta> = map Tm v\<close>, and
\<open>z = u @ v\<close>. Since from \eqref{LR0_iff.X_derivers2} we have 
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x\<close>}, \] 
we can substitute @{prop \<open>\<gamma> = \<alpha> @ \<beta> @ map Tm u\<close>}. By Lemma~\ref{derivers_substring_reliable} this implies the 
existence of some incomplete item in @{term \<open>valids (\<alpha> @ \<beta>)\<close>}, contradicting the fact that
@{prop \<open>p = {[X \<rightarrow> \<beta> \<cdot> ]}\<close>}.

Otherwise, if \<open>\<alpha> @ \<beta>\<close> is not a substring of \<open>\<gamma>\<close>, \eqref{LR0_iff.z_defs} implies the existence of 
some \<open>\<delta>' :: syms\<close> such that @{prop \<open>\<gamma> @ \<delta>' = \<alpha> @ \<beta>\<close>} and @{prop \<open>\<delta> = \<delta>' @ map Tm z\<close>}. This implies 
that item @{term \<open>[Y \<rightarrow> \<delta>' \<cdot> map Tm z]\<close>} is valid for @{term \<open>\<alpha> @ \<beta>\<close>} by \eqref{LR0_iff.Y_derivers2}, 
\eqref{LR0_iff.ydx}, and the fact that @{prop \<open>z @ x = y\<close>}, meaning it is in \<open>p\<close>. This and 
@{prop \<open>p = {[X \<rightarrow> \<beta> \<cdot> ]}\<close>} in turn imply @{prop \<open>\<alpha> = \<gamma> \<and> X = Y \<and> x = y\<close>}, meaning the implication holds. % clarify?
This completes the case where \<open>p\<close> consists of a single complete item.

In the case where @{prop \<open>completes p = {[A \<rightarrow> \<cdot> ]}\<close>}, the fact that @{prop \<open>[X \<rightarrow> \<beta> \<cdot> ] \<in> p\<close>} forces
@{prop \<open>[A \<rightarrow> \<cdot> ] = [X \<rightarrow> \<beta> \<cdot> ]\<close>}. From \eqref{LR0_iff.ydx} we can now distinguish cases on whether 
@{term \<open>\<alpha> @ \<beta>\<close>} is a prefix of \<open>\<gamma>\<close>.

If this is the case, there exists some \<open>\<zeta>\<close> such that @{prop \<open>\<gamma> = \<alpha> @ \<beta> @ \<zeta>\<close>}, and we can rewrite 
\eqref{LR0_iff.Y_derivers2} as 
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* (\<alpha> @ \<beta>) @ \<zeta> @ Nt Y # map Tm x\<close>\\ 
\<open>\<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>.
\end{multline*}
By Lemma~\ref{prefix_comp_unique_imp_eps} this implies that @{prop \<open>\<zeta> = [] \<and> X = Y \<and> x = y\<close>} holds,
which trivially implies \<open>\<alpha> = \<gamma>\<close> since \<open>\<beta> = []\<close>.

Lastly, if @{term \<open>\<alpha> @ \<beta>\<close>} is not a prefix of \<open>\<gamma>\<close>, there exist \<open>\<zeta> :: syms\<close> and \<open>x' :: 't list\<close> such 
that @{prop \<open>\<alpha> @ \<beta> = \<gamma> @ \<zeta>\<close>}, @{prop \<open>\<delta> = \<zeta> @ map Tm x'\<close>}, and @{prop \<open>y = x' @ x\<close>}. We can then 
perform a final case distinction on \<open>x'\<close>, where the case @{prop \<open>x' = []\<close>} forces @
{term \<open>[Y \<rightarrow> \<zeta> \<cdot> map Tm x'] = [X \<rightarrow> \<cdot> ]\<close>}, and @{prop \<open>x' \<noteq> []\<close>} implies a contradiction by 
Lemma~\ref{LR0_adequate_cases}. This completes the proof.
\end{proof}
\end{theorem}

We have now proved the main theorem of the \<open>LR(0)\<close> section in the work of Wilhelm et al. Our proof 
of the first implication, "\<open>G'\<close> is \<open>LR(0)\<close> \<open>\<Longrightarrow>\<close> the parser has no \<open>LR(0)\<close>-inadequate states", is 
quite similar to the one given by the authors. Their proof of the converse, however is incorrect.
Recall the original rightmost derivations as stated in the proof:
\begin{subequations}
\begin{gather}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<alpha> @ Nt X # map Tm w \<Rightarrow>r \<alpha> @ \<beta> @ map Tm w\<close>\label{iff_disc1}\\
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt Y # map Tm x \<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>\label{iff_disc2}
\end{gather}
\end{subequations}
Instead of distinguishing on the 3 cases provided by Lemma~\ref{LR0_adequate_cases} like we did,
they distinguish cases on \<open>\<beta>\<close> in the usual way. In both cases, they seem to implicitly assume that 
the rightmost derivation of \<open>\<alpha> @ \<beta> @ map Tm y\<close> implies that there exists a valid item for 
@{term \<open>\<alpha> @ \<beta>\<close>} of the form @{term \<open>[Y \<rightarrow> \<zeta> \<cdot> \<eta>]\<close>}.

This does not hold in general; consider the case where the handle of @{term \<open>\<alpha> @ \<beta> @ map Tm y\<close>}
is some \<open>\<delta>\<close> with @{prop \<open>\<alpha> = \<gamma> @ \<delta>\<close>}, and @{prop \<open>map Tm x = \<beta> @ map Tm y\<close>}. In such a case, item 
@{term \<open>[Y \<rightarrow> \<delta> \<cdot> ]\<close>} would be valid for \<open>\<alpha>\<close>, which does not force it to be in state 
@{term \<open>valids (\<alpha> @ \<beta>)\<close>} in general. The same issue can arise in other cases; if @{term \<open>\<alpha> @ \<beta>\<close>} is
a proper prefix of \<open>\<gamma>\<close>, one cannot use \eqref{iff_disc2} to derive the existence of any item of the 
form @{term \<open>[Y \<rightarrow> \<zeta> \<cdot> \<eta>]\<close>} that is valid for \<open>\<alpha> @ \<beta>\<close> by the definition of reliable prefixes: 
if @{term \<open>\<alpha> @ \<beta>\<close>} is a proper prefix of \<open>\<gamma>\<close>, there exists a nonempty string \<open>\<theta>\<close> with 
@{prop \<open>\<gamma> = \<alpha> @ \<beta> @ \<theta>\<close>}. Using \eqref{iff_disc2}, an item of the form @{term \<open>[Y \<rightarrow> \<zeta> \<cdot> \<eta>]\<close>} can only
be valid for the string @{term \<open>\<alpha> @ \<beta> @ \<theta> @ \<zeta>\<close>}. For this reason, our argument for the case where 
@{term \<open>\<alpha> @ \<beta>\<close>} is a prefix of \<open>\<gamma>\<close> is based on Lemma~\ref{derivers_substring_reliable}, which
derives a contradiction independently of \<open>Y\<close>. 

In general, we found that the issues caused by approaching the proof through a case distinction on
\<open>\<beta>\<close> are mostly caused by the fact that if the handle of \<open>\<alpha> @ \<beta> @ map Tm y\<close> in \eqref{iff_disc2} is
\<open>\<delta>\<close>, meaning @{prop \<open>\<gamma> @ \<delta> @ map Tm x = \<alpha> @ \<beta> @ map Tm y\<close>}, there are far too many cases to consider
as to how the lists are split, and the cases where \<open>\<gamma> @ \<delta>\<close> is a proper prefix of @{term \<open>\<alpha> @ \<beta>\<close>} are 
particularly problematic. This was our motivation towards assuming WLOG more well-behaved rightmost 
derivations where we are guaranteed that either @{term \<open>\<alpha> @ \<beta>\<close>} was already previously derived, 
allowing us to use Lemma~\ref{derivers_substring_reliable}, or \<open>\<delta>\<close> "completes" the prefix \<open>\<alpha> @ \<beta>\<close>, 
in which case we are guaranteed that an item corresponding to production @{term \<open>(Y, \<delta>)\<close>} is valid 
for @{term \<open>\<alpha> @ \<beta>\<close>}, allowing us to argue about \<open>p\<close>.\<close>

subsubsection \<open>Preservation of the \<open>LR(k)\<close> Condition in Extended Grammars\<close>

text\<open>There is another issue worth discussing in the topic of \<open>LR(k)\<close>, which is the definition of the 
\<open>LR(k)\<close> condition itself. As we stated before, our definition, which is based on that of Wilhelm et 
al., is restricted to the extension of a CFG. Since extending a grammar preserves several properties, 
such as the language and quality of being reduced, as we showed in Theorem~\ref{Lang_preserved} and
Lemma~\ref{G'_reduced}, one could intuitively assume that the extension has no effect on the original
grammar's fulfillment of the \<open>LR(k)\<close> condition. In our formalization of \<open>LR(k)\<close>, we remained working
within the context of our Extended Grammars, which fixes \<open>G'\<close> as the extension of the original CFG \<open>G\<close>.
Since our grammars are fixed, we defined the \<open>LR(k)\<close> condition per Wilhelm et al. as the predicate 
\<open>is_LR :: nat \<Rightarrow> bool\<close>:
\begin{quote}
@{thm is_LR_def}
\end{quote}
Consider now the more general \<open>is_LR' :: nat \<Rightarrow> ('a, 'b) Cfg \<Rightarrow> bool\<close>:
\begin{quote}
@{thm is_LR'_def}
\end{quote}
This definition for arbitrary CFGs, is not preserved by extension, i.e., for our fixed \<open>G\<close> and \<open>G'\<close>,
the equality 
\[ @{term \<open>is_LR' k G\<close>} \overset{?}{=} @{term\<open>is_LR' k G'\<close>} \]
does not hold in general. We will prove two lemmas that show that for grammars with certain 
properties, the extension does preserve the \<open>LR(k)\<close> condition, and in the process explain why the 
property is necessary for the condition to be preserved.

One direction of the claim does hold for all \<open>k\<close>:

\begin{lemma}
Let \<open>G\<close> be a CFG and \<open>G'\<close> its extension. For all \<open>k\<close> holds
\[ @{thm LR'k_G'_imp_LR'k_G} \]
\begin{proof}
Trivial using the fact that @{term \<open>Prods G \<subseteq> Prods G'\<close>}.
\end{proof}
\end{lemma}

We show two lemmas for the converse:

\begin{lemma}\label{LR'0_G_imp_LR'0_G'}[Preservation of \<open>LR(0)\<close>]
Let \<open>G\<close> be a reduced \<open>LR(0)\<close> grammar with start symbol \<open>S\<close> and nonempty language, and \<open>G'\<close> 
its extension with start symbol \<open>S'\<close>. 
Furthermore, assume there does not exist a left recursion of the form
\[ @{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>(Suc n) Nt S # \<alpha>\<close>} \]
for any \<open>n :: nat\<close> or \<open>\<alpha> :: syms\<close>. 

Then \<open>G'\<close> is an \<open>LR(0)\<close> grammar.
\begin{proof}
Consider the rightmost derivations 
\begin{gather*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(n) \<alpha> @ Nt X # map Tm w\<close>
  \<open>\<Rightarrow>r \<alpha> @ \<beta> @ map Tm w\<close>\\
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(m) \<gamma> @ Nt Y # map Tm x\<close>
  \<open>\<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>
\end{gather*}
We have to prove that @{prop \<open>\<alpha> = \<gamma> \<and> X = Y \<and> x = y\<close>} holds. We again omit the assumption 
@{prop \<open>take 0 w = take 0 y\<close>} since it is trivially true.

We distinguish cases on the lengths of the derivations \<open>m\<close> and \<open>n\<close>.

If \<open>n = m = 0\<close>, the implication holds trivially.

If \<open>n = 0\<close> and \<open>m = Suc m'\<close> for some \<open>m'\<close>, we know from \<open>n = 0\<close> that \<open>\<alpha> = []\<close>, \<open>\<beta> = [Nt S]\<close>, and 
\<open>w = []\<close>.
This also implies that @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc (Suc m')) Nt S # map Tm y\<close>}, by 
Lemma~\ref{G'_deriven_Suc_imp_G_deriven}, this contradicts our assumption about the absence of left 
recursions for \<open>S\<close> in \<open>G\<close>.

If we did not assume that \<open>G\<close> is free of such left recursions, the \<open>LR(0)\<close> condition would be broken: 
from \<open>n = 0\<close>, we know that \<open>X = S'\<close>. Since \<open>S'\<close> is not in \<open>G\<close>, this immediately makes the condition 
\<open>X = Y\<close> unsatisfiable. Besides this, the \<open>Y\<close> that produces \<open>S\<close> could also produce terminals to its 
right, violating the \<open>x = y\<close> condition as well. 

The opposite case, \<open>n = Suc n'\<close> for some \<open>n'\<close> and \<open>m = 0\<close>, is analogous.

Finally, for the case where both derivations have nonzero length, one can show the same
property from Lemma~\ref{G'_deriven_Suc_imp_G_deriven} holds for rightmost derivations as well, i.e.,
\[ @{thm G'_derivern_Suc_imp_G_derivern}. \] 
The proof is analogous to that of Lemma~\ref{G'_deriven_Suc_imp_G_deriven}. With this property, the
final case is trivial.
\end{proof}
\end{lemma}

\begin{lemma}\label{LR'_Suc_G_imp_LR'_Suc_G'}[Preservation of \<open>LR(k)\<close> for nonzero \<open>k\<close>]
Let \<open>G\<close> be an \<open>LR(k)\<close> grammar for \<open>k > 0\<close> with start symbol \<open>S\<close> and \<open>G'\<close> its extension with start 
symbol \<open>S'\<close>. Furthermore, assume there does not exist a cycle
\[ @{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>(Suc n) [Nt S]\<close>} \]
for any \<open>n :: nat\<close>. 
\begin{proof}
Consider the rightmost derivations 
\begin{gather*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(n) \<alpha> @ Nt X # map Tm w\<close>
  \<open>\<Rightarrow>r \<alpha> @ \<beta> @ map Tm w\<close>\\
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r(m) \<gamma> @ Nt Y # map Tm x\<close>
  \<open>\<Rightarrow>r \<alpha> @ \<beta> @ map Tm y\<close>
\end{gather*}
with @{prop \<open>take k w = take k y\<close>}
We have to prove that @{prop \<open>\<alpha> = \<gamma> \<and> X = Y \<and> x = y\<close>} holds.
We will first focus on the case where \<open>n = 0\<close> and \<open>m = Suc m'\<close> for some \<open>m'\<close>:

This case once again implies that 
\begin{equation}\label{LR_Suc_k}
@{prop \<open>\<alpha> = []\<close>}, @{prop \<open>\<beta> = [Nt S]\<close>}, \text{ and } @{prop \<open>w = []\<close>},
\end{equation}
and we again have a left recursion of the form 
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc (Suc m')) Nt S # map Tm y\<close>}. \]
However, in this case, since @{prop \<open>k > 0\<close>} and @{prop \<open>w = []\<close>}, @{prop \<open>take k w = take k y\<close>} 
can only hold if \<open>y = []\<close>. This contradicts the assumption that \<open>G\<close> is cycle-free.

Similarly to the \<open>LR(0)\<close> case, if \<open>G\<close> were not cycle-free, this case would violate the 
\<open>LR(k)\<close> condition since, again, $\<open>X\<close> \overset{!}{=} \<open>Y\<close>$ cannot hold, but although this situation 
bears similarity to the case for \<open>LR(0)\<close>, it has a rather meaningful implication: \<open>LR(k)\<close> grammars 
with nonzero \<open>k\<close> are possible to extend despite left recursions, which makes them much more powerful 
than \<open>LR(0)\<close> grammars in this regard. If a left recursion is possible, the lookahead prevents 
\<open>S' \<rightarrow> S\<close> from creating ambiguity, since this production always implies the lookahead is empty, as 
we can see in \eqref{LR_Suc_k}.

The proof for the other cases is analogous to that of Lemma~\ref{LR'0_G_imp_LR'0_G'}.
\end{proof}
\end{lemma}

It is worth highlighting that in the CFG section of the book, Wilhelm et al. 
explain:~\cite[p. 52]{Wilhelm}
\begin{quote}
Context-free grammars that describe programming languages should be unambiguous. If this is the case, 
then there exist exactly one parse tree, one leftmost and one rightmost derivation for each 
syntactically correct program.
\end{quote}

This is of great importance to our result from Lemma~\ref{LR'_Suc_G_imp_LR'_Suc_G'}: a grammar
with a cycle through its start symbol has infinitely many derivations for every word in the
language, i.e., it is ambiguous. We can therefore conclude, based on our results and the authors'
claims about the importance of grammars being unambiguous, that the precondition for the preservation
of the \<open>LR(k)\<close> condition for \<open>k > 0\<close>, i.e., the grammar being cycle-free, is essentially guaranteed
to hold in practice. This is because the extension only causes the previously satisfied condition to 
be violated in grammars which the theory we are formalizing already deems inadequate to begin with.

For the case of \<open>k = 0\<close>, however, this does become problematic. Grammars with left recursions
are fairly standard, meaning that our precondition makes it possible to guarantee the preservation
of the \<open>LR(0)\<close> condition only for a subset of \<open>LR(0)\<close> grammars, namely those that lack a left-recursive
start symbol. It is worth noting that our formal proof only delivers a sufficient condition for the 
preservation of the \<open>LR(0)\<close> condition, but its necessity remains an open question.

With these results and our proof of Theorem~\ref{is_LR0_iff_no_LR0_inadequates}, we have completed
our goal of verifying the \<open>LR(0)\<close> parsing theory as presented by Wilhelm et al. We now move on towards
showing a second major result about the canonical \<open>LR(0)\<close> parser which is not in the original text.\<close>

subsection \<open>Language Equivalence of @{const P\<^sub>0} and its Grammar\<close>
(*<*) 
notation (latex output) P0.Lang 
  (\<open>\<^latex>\<open>\ensuremath{L(P_0(G))}\<close>\<close>)
(*>*)
text \<open>Now that we have finished formalizing the basic \<open>LR(0)\<close> theory, the most interesting question
that remains open is perhaps the correctness of the canonical \<open>LR(0)\<close> parser we have formalized.
We will answer this question by proving that @{const P\<^sub>0} accepts exactly @{term \<open>LangS G\<close>}. In this
section, we denote parser steps, their reflexive transitive closure, and \<open>n\<close>-step computations by
\<open>\<turnstile>P\<close>, \<open>\<turnstile>P*\<close>, and \<open>\<turnstile>P(n)\<close> respectively.\<close>

subsubsection \<open>Stack Words: Proving Soundness\<close>

text \<open>We will begin our correctness proof by showing that our parser is sound, i.e., every word
accepted by our parser is a word in @{term \<open>LangS G\<close>}. We will show an invariant for @{const P\<^sub>0} 
computations from which we will derive this property. Consider the following excerpt of Wilhelm
et al. on the parser's stack~\cite[p. 110]{Wilhelm}:
\begin{quote}
The construction of @{const LR\<^sub>0} guarantees that for each noninitial and nonfinal state \<open>q\<close> there
exists exactly one entry symbol under which the automaton can make a transition into \<open>q\<close>. The
pushdown contents \<open>q\<^sub>0, \<dots>, q\<^sub>n\<close> with @{prop\<open>q\<^sub>0 = subs q G 0\<close>}~\footnote{Recall that the authors define
the topmost stack symbol to be the rightmost one when writing out a list, which is the opposite of 
our convention.} corresponds therefore to a uniquely determined word \<open>\<alpha> = [X\<^sub>1, \<dots>, X\<^sub>n] :: syms\<close> for
which $\Delta_G\ q_i\ X_{i+1} = q_{i+1}$ holds. This word \<open>\<alpha>\<close> is a reliable prefix, and \<open>q\<^sub>n\<close> is the
set of all items valid for \<open>\<alpha>\<close>.
\end{quote}

The authors do not develop this idea further. It is of particular interest, as we will soon see,
what the relation between the reliable prefix \<open>\<alpha>\<close> and the input that has been consumed at that point
is. We use this intuitive explanation of the inner workings of the parser's stack as inspiration to 
formalize what we call the parser's \concept{stack words}. For configurations of @{const P\<^sub>0} \<open>c\<^sub>0\<close> and
\<open>c\<^sub>1\<close>, we write @{prop \<open>\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1\<close>} to mean that \<open>c\<^sub>0\<close> reaches \<open>c\<^sub>1\<close> with stack word \<open>\<alpha>\<close>. This is 
defined inductively with a
\concept{reflexive} rule:
\begin{gather*}
@{thm sw_refl}\\
\intertext{and a \concept{step} rule:}
@{thm [mode=Rule] sw_step}
\end{gather*}

With stack words, we are now able to track the reliable prefix that corresponds to the parser's stack
akin to what the authors describe: note that in both read and reduce transitions, our parser always
pushes @{term \<open>dfa.nxt LR\<^sub>0 q X\<close>} on top of the stack, where \<open>q\<close> is the second-topmost state after 
the transition was made. In reduce transitions, some topmost stack string is deleted and replaced by
the successor of the state that becomes the topmost state immediately after the deletion. 
This is the purpose of the \<open>ps\<close> list in the \<open>step\<close> rule. In read transitions, the stack simply grows 
by the successor of the topmost state, so in this case our \<open>ps\<close> is simply the empty list. Since in 
both cases we remove @{term \<open>length ps\<close>} symbols from the stack, we do the exact same for the stack 
word, which is why we replace the old stack word \<open>\<alpha>\<close> by the suffix @{term \<open>drop (length ps) \<alpha>\<close>}. By 
pushing the symbol \<open>X\<close> that gets passed to the \<open>nxt\<close> function to compute the new topmost state, we
keep track of the symbols that the authors describe in the excerpt. It is worth remarking that our 
stack words are stored in reverse, once again, to make the inductive rules more fitting to the
Isabelle list datatype It is also important to note that stack words as we defined them have a 
caveat: the stack word that is being tracked only truly corresponds to the parser's stack if 
for @{prop \<open>\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1\<close>}, the stack of \<open>c\<^sub>0\<close> is empty, i.e., @{prop \<open>c\<^sub>0 = ([p], w)\<close>} for some state 
\<open>p\<close> and input \<open>w\<close>. This limitation, however, is not an obstacle for us, since the starting 
configuration of the parser fulfills this precondition.

In order to prove the parser sound, we will first need to show some additional properties.

\begin{lemma}\label{inj_nxt_dfa_LR0_if_nonempty}
If @{prop \<open>dfa.nxt LR\<^sub>0 q X = dfa.nxt LR\<^sub>0 q Y\<close>} and @{prop \<open>dfa.nxt LR\<^sub>0 q X \<noteq> {}\<close>}, then
@{prop \<open>X = Y\<close>} holds.
\begin{proof}
With Lemma~\ref{char_fa_nxts_is_shifts} we can show that for any state \<open>p\<close> of @{const LR\<^sub>0} holds
\[ @{prop \<open>dfa.nxt LR\<^sub>0 p X = char_fa.epsclo {[X' \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]|X' \<alpha> \<beta>. [X' \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> p}\<close>}. \]
The claim then follows trivially.
\end{proof}
\end{lemma}

\begin{lemma}\label{P0_init_stack_word_length_inv}
If @{term \<open>([gpda.init P\<^sub>0], u)\<close>} reaches some configuration @{term \<open>(qs, v)\<close>} with stack word \<open>\<alpha>\<close>, 
then @{term \<open>length qs = length \<alpha> + 1\<close>} holds.
\begin{proof}
By rule induction on the stack word.
\end{proof}
\end{lemma}

\begin{lemma}\label{stack_word_imp_P0_steps}
If @{prop \<open>\<alpha> \<Turnstile> c\<^sub>0 \<turnstile>P* c\<^sub>1\<close>}, then @{prop \<open>c\<^sub>0 \<turnstile>P* c\<^sub>1\<close>}.
\begin{proof}
By rule induction on the stack word.
\end{proof}
\end{lemma}

\begin{lemma}\label{P0_steps_imp_stack_word}
If a computation @{prop \<open>c\<^sub>0 \<turnstile>P* (q # qs, w)\<close>} exists for some state of @{const LR\<^sub>0} \<open>q\<close>, 
there exists a stack word \<open>\<alpha>\<close> with which \<open>c\<^sub>0\<close> reaches \<open>(q # qs, w)\<close>.
\begin{proof}
The proof is by induction on the length of the computation, with a case distinction on the 
transition type in the last step for the transitive case, and using the fact that after a 
finish transition, the topmost state on the stack is not a state of @{const LR\<^sub>0}.
\end{proof}
\end{lemma}

\begin{lemma}\label{P0_nth_is_valids_of_nth_stack_word}
If @{prop \<open>\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (q # qs, v)\<close>}, then 
\[ @{prop \<open>(q # qs) ! n  = valids (rev (drop n \<alpha>))\<close>} \]
holds for $\<open>0 \<le> n\<close> < @{term \<open>length (q # qs)\<close>}$.
\begin{proof}
We perform rule induction on the stack word for arbitrary \<open>q, qs, u,\<close> and \<open>v\<close>.

The reflexive case holds by showing that @{prop \<open>gpda.init P\<^sub>0 = valids []\<close>} using 
Lemma~\ref{nextl_dfa_LR0_is_valids}.

For the step case, we know the initial configuration reaches some configuration 
@{term  \<open>(ps @ q # qs, v)\<close>} with stack word \<open>\<alpha>\<close>, and then the parser takes a step from this
configuration into @{term \<open>(dfa.nxt LR\<^sub>0 q X # q # qs, w)\<close>}. We need to show that 
for $\<open>0 \<le> n\<close> < @{term \<open>length (dfa.nxt LR\<^sub>0 q X # q # qs)\<close>}$, 
@{prop \<open>mbox0 ((dfa.nxt LR\<^sub>0 q X # q # qs) ! n) = valids (rev (drop n (X # drop (length ps) \<alpha>)))\<close>}
holds. We now distinguish the usual cases on the final step.

In the reading transition case, we know the stack word after the step is exactly \<open>X # \<alpha>\<close>.
Furthermore, by the induction hypothesis we know that for all $\<open>0 \<le> n\<close> < @{term \<open>length (q # qs)\<close>}$
holds @{prop \<open>(q # qs) ! n  = valids (rev (drop n \<alpha>))\<close>}. Thus, we know \<open>q\<close> is exactly @{term \<open>valids \<alpha>\<close>}.
Moreover, by Lemma~\ref{nxt_dfa_LR0_shift_is_valids_app}, @{term \<open>dfa.nxt LR\<^sub>0 q X\<close>} is 
@{term \<open>mbox0 (valids (rev (X # \<alpha>)))\<close>}. With all this, the implication holds.

If the transition is reducing, the induction hypothesis tells us that for all 
$\<open>0 \<le> n\<close> < @{term \<open>length (q # qs)\<close>}$ holds 
@{prop \<open>(q # qs) ! n = valids (rev (drop (length ps + n) \<alpha>))\<close>}, which implies that 
@{prop \<open>q = valids (rev (drop (length ps) \<alpha>))\<close>}. With this we can then use
Lemma~\ref{nxt_dfa_LR0_shift_is_valids_app} to show that the implication once again holds, 
finishing the proof.
\end{proof}
\end{lemma}

This lemma highlights the correspondence between the stack word and the stack that we described. In
particular, compare this to what Wilhelm et al. explain in the excerpt we quoted: ``This word \<open>\<alpha>\<close> is
a reliable prefix, and \<open>q\<^sub>n\<close> is the set of all items valid for \<open>\<alpha>\<close>.'', where \<open>q\<^sub>n\<close> refers to the topmost
stack state. Our lemma shows that this property is not only true, but also remains true for every
suffix of the stack and the stack word.

We will now show the parser's soundness with the following invariant:

\begin{lemma}\label{P0_invariant}
If @{prop \<open>\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u @ v) \<turnstile>P* (q # qs, v)\<close>} and @{prop \<open>q \<noteq> {}\<close>}, then 
  @{prop \<open>Prods G' \<turnstile> rev \<alpha> \<Rightarrow>r* map Tm u\<close>}
\begin{proof}
We proceed by rule induction on the stack word for arbitrary \<open>q, qs, u,\<close> and \<open>v\<close>.

The reflexive case is trivial since @{prop \<open>u @ v = v\<close>} implies @{prop \<open>u = []\<close>}.

In the step case, we know the starting configuration with input @{term \<open>u @ v\<close>} reaches some
configuration @{term \<open>(ps @ q # qs, w)\<close>} with some stack word \<open>\<alpha>\<close>. We will call this configuration
\<open>c\<^sub>1\<close>. Furthermore, we also know that the successor configuration is
@{term \<open>(mbox0 (dfa.nxt LR\<^sub>0 q X # q # qs), v)\<close>} with @{prop \<open>dfa.nxt LR\<^sub>0 q X \<noteq> {}\<close>}. Let \<open>c\<^sub>2\<close> be
this successor configuration. 

Our goal is to show that
\[ @{prop \<open>Prods G' \<turnstile> rev (X # drop (length ps) \<alpha>) \<Rightarrow>r* map Tm u\<close>} \]
holds. 

From the case assumptions, we know there exists some \<open>u'\<close> such that @{prop \<open>u @ v = u' @ w\<close>}. By
the induction hypothesis, this implies that @{prop \<open>Prods G' \<turnstile> rev \<alpha> \<Rightarrow>r* map Tm u'\<close>}. We can now 
distinguish cases based on the type of transition in the step @{prop \<open>c\<^sub>1 \<turnstile>P c\<^sub>2\<close>}.

If the step is a read transition, we know that \<open>ps\<close> is the empty list, and @{prop \<open>u = u' @ [a]\<close>}. 
Furthermore, we also know that @{term \<open>rev (X # drop (length ps) \<alpha>)\<close>} is exactly 
@{term \<open>rev \<alpha> @ [Tm a]\<close>}. Therefore, the invariant is fulfilled.

If the step is a reducing transition, we know there is an item @{term \<open>[Y \<rightarrow> \<beta> \<cdot> ]\<close>} in the topmost
state of @{term \<open>ps @ q # qs\<close>} which signaled the reduction, i.e., @{term \<open>length \<beta>\<close>} stack states 
were removed. By Lemma~\ref{P0_nth_is_valids_of_nth_stack_word}, this means that @{term \<open>[Y \<rightarrow> \<beta> \<cdot> ]\<close>}
is valid for \<open>rev \<alpha>\<close>. This implies that \<open>\<alpha>\<close> is of the form @{term \<open>rev \<beta> @ \<alpha>'\<close>} for some
\<open>\<alpha>' :: syms\<close>. Since we know that the length of \<open>\<beta>\<close> equals the length of \<open>ps\<close>, this means
that @{prop \<open>\<alpha> = rev \<beta> @ drop (length ps) \<alpha>\<close>}. Since we know that after the reducing configuration,
@{term \<open>dfa.nxt LR\<^sub>0 q (Nt Y)\<close>} is the topmost, with Lemma~\ref{inj_nxt_dfa_LR0_if_nonempty} we know that
@{prop \<open>X = Nt Y\<close>} holds by our assumption that @{term \<open>dfa.nxt LR\<^sub>0 q X\<close>} is nonempty. Moreover, from
the reducing transition assumptions we know that @{prop \<open>u' = u\<close>} must hold, since the remaining
input after the transition is \<open>v\<close>, and we know that this transition does not consume symbols. From
all this, we can show the invariant is satisfied.

The last case, which is that of the finish transition, contradicts the structure of the stack word.
This is because the topmost state being @{term \<open>dfa.nxt LR\<^sub>0 q X\<close>} means that it is either empty,
or a state of @{const LR\<^sub>0}. This is a direct consequence of the definition of the transition
functions of @{const LR\<^sub>0} and @{const char_fa}. Since @{term P0_final} is not a state of
@{const LR\<^sub>0}, this case cannot occur. The proof of the invariant is therefore complete.
\end{proof}
\end{lemma}

\begin{theorem}[Soundness of the canonical \<open>LR(0)\<close> parser]\label{P0_sound}
Every word accepted by @{const P\<^sub>0} is a word in @{term \<open>LangS G\<close>}.
\begin{proof}
We begin by fixing \<open>w\<close> and assuming that @{prop \<open>w \<in> P0.Lang\<close>}. Therefore, the initial computation 
of @{const P\<^sub>0} reaches the final configuration @{term \<open>([mbox {[S' \<rightarrow> [] \<cdot> []]}], [])\<close>}. We know this 
computation has nonzero length because @{term P0_final} is distinct from the initial state.
We also know that the last step of the computation must have been a finishing transition, meaning
there exists a state \<open>q\<close> of @{const LR\<^sub>0} such that @{prop \<open>[S' \<rightarrow> [Nt S] \<cdot> ] \<in> q\<close>} for which 
@{const P\<^sub>0} computes @{prop \<open>mbox ([gpda.init P\<^sub>0], w) \<turnstile>P* ([q, dfa.init LR\<^sub>0], [])\<close>}. With this, we know by 
Lemma~\ref{P0_steps_imp_stack_word} that there exists some \<open>\<alpha> :: syms\<close> with
\[ @{prop \<open>\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], w) \<turnstile>P* ([q, dfa.init LR\<^sub>0], [])\<close>}. \] 
We also know by Lemma~\ref{P0_init_stack_word_length_inv} that this stack word is of the form 
@{prop \<open>\<alpha> = [X]\<close>} for some symbol \<open>X\<close>. By Lemma~\ref{P0_nth_is_valids_of_nth_stack_word}, we know 
that @{prop \<open>q = valids [X]\<close>}, and since @{prop \<open>mbox0 ([S' \<rightarrow> [Nt S] \<cdot> ] \<in> q)\<close>}, there exists a \<open>\<gamma>\<close> such 
that @{prop \<open>[X] = \<gamma> @ [Nt S]\<close>} since \<open>[X]\<close> is a reliable prefix for this item. This forces 
@{prop \<open>X = Nt S\<close>}, and by Lemma~\ref{P0_invariant} this stack word implies 
@{prop \<open>Prods G' \<turnstile> [Nt S] \<Rightarrow>r* map Tm w\<close>}. Since \<open>S'\<close> derives \<open>[Nt S]\<close> by definition, this means 
that @{prop \<open>w \<in> LangS G'\<close>}, and the proof is complete by the language preservation of the grammar 
extension.
\end{proof}
\end{theorem}\<close>

subsubsection \<open>The Shift-Reduce Pushdown Automaton: Proving Completeness\<close>

(*<*)
interpretation MG: srpda G M\<^sub>G 
  by unfold_locales auto

notation MG.step (infix \<open>\<turnstile>M\<close> 55)
notation MG.steps (infix \<open>\<turnstile>M*\<close> 55)
notation (latex output) MG.Lang
  (\<open>\<^latex>\<open>\ensuremath{L(M_G)}\<close>\<close>)


(*>*)

text \<open>Now that we have proven the soundness of our parser, all that is left is proving its 
completeness, i.e., that every word in the grammar is accepted by the parser.

We will again need stack words to prove completeness, but constructing a valid parser computation 
from a rightmost derivation directly is quite challenging since the parser's construction, albeit
ideal for our original goal of achieving a deterministic parsing algorithm, is too far removed from 
the pure concept of rightmost derivations. We will overcome this by defining the
\concept{shift-reduce pushdown automaton} (SRPDA), proving the completeness of this machine w.r.t
the grammar, and then show the relation between SRPDA and @{const P\<^sub>0} computations, which will allow
us to prove the parser complete. Our definition of the SRPDA is based on the lecture slides by
Petter~\cite{Petter}.

The SRPDA is an automaton that uses a CFG's symbols as its states. In order to distinguish an
initial or final state from symbols that are being parsed by the automaton, it is necessary for us
to extend the grammar's symbols by two more. We achieve this with a new datatype @{type srpda_state}:
\[ @{datatype srpda_state} \]

\begin{definition}[Shift-reduce pushdown automaton]
The shift-reduce pushdown automaton (SRPDA) to an arbitrary CFG @{term_type \<open>G :: ('n, 't) Cfg\<close>}
is the @{typeof M\<^sub>G}
\begin{multline*}
\<open>M\<^sub>G = \<lparr>gpda.states = UNIV, init = Init, final = {Final}\<close>\\
  \<open>nxt = range (\<lambda>(q, x). ([q], x, [Sym (Tm x), q])), eps = \<E>\<^sub>M\<rparr>\<close>
\end{multline*}
\end{definition}

Where @{const range} denotes the image of a function, and a term of the form (\<open>\<lambda>x\<^sub>1 x\<^sub>2 \<dots> x\<^sub>n. y\<close>) 
denotes a mapping that takes parameters \<open>x\<^sub>1, x\<^sub>2, \<dots>, x\<^sub>n\<close> and returns \<open>y\<close>. 

We define three types of transition once again:
\begin{itemize}
\item in a \concept{reading} transition, \<open>M\<^sub>G\<close> reads a symbol from the input, and pushes it onto the 
stack. This corresponds, as is the case with the other automata we have defined until now, to the 
\<open>nxt\<close> relation. Since we define the relation as the range of the mapping, this transition is
completely independent of the current state.
\item \concept{Reducing} transitions allow the SRPDA to reduce a topmost stack string \<open>\<alpha>\<close> to a 
nonterminal \<open>A\<close> if the production \<open>(A, \<alpha>)\<close> is in \<open>G\<close>. Formally, this is the set
\[ @{term \<open>{(map Sym (rev \<alpha>) @ [q], [Sym (Nt A), q])|A \<alpha> q. (A, \<alpha>) \<in> Prods G}\<close>} \]
\item Lastly, the \concept{finishing} transition, very similarly to the canonical \<open>LR(0)\<close> parser, 
signals that the consumed input has successfully been reduced to the start symbol. This corresponds
to the singleton set @{term \<open>([Sym (Nt (Start G)), Init], [Final])\<close>}
\end{itemize}
\<open>\<E>\<^sub>M\<close> is once again the union of reducing transitions and the singleton finishing transition set.

The SRPDA, unlike our \<open>LR(0)\<close> parser, computes reductions extremely similar to how its grammar
derives words. Essentially, it mimics the grammar's derivation of a word, but backwards. It is worth
noting that this automaton is not a GPDA in the strict sense of our definition. This is due to the 
fact that we define the alphabet of a CFG through types rather than sets. Since our SRPDA states 
are the grammar's symbols, in order to satisfy the assumption that the set of states is finite, one 
would need to prove that the types for terminals and nonterminals are both finite. Applying such a
constraint to a type is much more restrictive than to a set, and we purposefully avoid doing it so
our parser can be used for grammars of arbitrary types. The fact that this automaton does not fulfill
the finiteness condition in general is not problematic for our purposes, but it is a discrepancy
with our original GPDA definition that is worth noting.

We will now prove that the SRPDA to our reduced grammar \<open>G\<close> is complete, i.e., every word in 
@{term \<open>LangS G\<close>} is accepted by @{const M\<^sub>G}. We denote \<open>M\<^sub>G\<close> steps and their reflexive transitive
closure as \<open>\<turnstile>M\<close> and \<open>\<turnstile>M*\<close> respectively.

\begin{lemma}\label{prefix_consumable}
@{prop \<open>(X # \<alpha>, u @ v) \<turnstile>M* (map (Sym \<circ> Tm) (rev u) @ X # \<alpha>, v)\<close>} holds for any SRPDA state list 
\<open>X # \<alpha>\<close> and input \<open>u @ v :: 't list\<close>.
\begin{proof}
By induction on \<open>u\<close> for arbitrary \<open>X\<close> and \<open>\<alpha>\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{Tms_on_stack_imp_consumed}
@{prop \<open>(\<alpha>, u @ v @ w) \<turnstile>M* (map (Sym \<circ> Tm) (rev v) @ \<beta>, w)\<close>} implies
\[ @{prop \<open>(\<alpha>, u @ v @ w) \<turnstile>M* (\<beta>, v @ w)\<close>}. \]
\begin{proof}
The proof is by reverse induction on \<open>v\<close> for arbitrary \<open>u\<close> and \<open>w\<close>, i.e., for the step case, we 
append an element on the right, instead of on the left as we do in a regular list induction.

The base case is trivial.

In the inductive case, \<open>v = x @ [a]\<close> for some \<open>x :: 't list\<close> and \<open>a :: 't\<close>. With the case 
assumptions, we have
\[ @{prop \<open>(\<alpha>, u @ (v @ [a]) @ w) \<turnstile>M* (map (Sym \<circ> Tm) (rev (v @ [a])) @ \<beta>, w)\<close>}. \]
We distinguish the reflexive and transitive cases on this computation to prove that the SRPDA 
computes
\[ @{prop \<open>(\<alpha>, u @ (v @ [a]) @ w) \<turnstile>M* (map (Sym \<circ> Tm) (rev v) @ \<beta>, a # w)\<close>}. \]
The claim then follows directly by the induction hypothesis.
\end{proof}
\end{lemma}

\begin{lemma}[SRPDA invariant]\label{srpda.invariant}
If @{prop \<open>Prods G \<turnstile> \<alpha> \<Rightarrow>r* map Tm w\<close>}, then 
\[ @{prop \<open>([Init], w) \<turnstile>M* (map Sym (rev \<alpha>) @ [Init], [])\<close>}. \]
\begin{proof}
We use reverse induction on the length of the derivation. 

The reflexive case is trivial by Lemma~\ref{prefix_consumable}.

For the transitive case, we consider the first step of the derivation.

We know that \<open>\<alpha> = \<beta> @ Nt A # map Tm v\<close> for some \<open>A :: 'n\<close>, \<open>\<beta> :: syms\<close>, and \<open>v :: 't list\<close>, and the 
right sentential form produced is @{term \<open>\<beta> @ \<gamma> @ map Tm v\<close>} for some \<open>\<gamma> :: syms\<close> such that 
@{prop \<open>(A, \<gamma>) \<in> Prods G\<close>}. By the induction hypothesis we know that 
@{prop \<open>([Init], w) \<turnstile>M* (map Sym (rev (\<beta> @ \<gamma> @ map Tm v)) @ [Init], [])\<close>} holds.
By Lemma~\ref{Tms_on_stack_imp_consumed}, this implies that the starting configuration for \<open>w\<close> also 
reaches @{term \<open>(map Sym (rev \<delta> @ rev \<gamma>) @ [Init], v)\<close>}. The SRPDA can then reduce \<open>rev \<delta>\<close> to \<open>A\<close>, 
and put @{term \<open>rev v\<close>} on the stack by Lemma~\ref{prefix_consumable}. Since this is equivalent to 
\<open>rev \<alpha>\<close>, the proof is now complete.
\end{proof}
\end{lemma}

We can now use this invariant to show completeness.

\begin{lemma}[Completeness of the shift-reduce PDA]\label{srpda_complete}
If a word is in @{term \<open>LangS G\<close>}, it is accepted by @{const M\<^sub>G}.
\begin{proof}
We begin by fixing some \<open>w\<close> in 
@{term \<open>LangS G\<close>}. This implies that @{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* map Tm w\<close>}.
By Lemma~\ref{srpda.invariant}, this derivation implies the existence of the computation
\[ @{prop \<open>([Init], w) \<turnstile>M* ([Sym (Nt (Start G)), Init], [])\<close>}. \]
Trivially, the configuration @{term \<open>([Sym (Nt (Start G)), Init], [])\<close>} reaches 
@{term \<open>([Final], [])\<close>} in a single step via a finishing transition, meaning @{prop \<open>w \<in> MG.Lang\<close>}.
The proof is thus complete.
\end{proof}
\end{lemma}

We will now show the relation between @{const M\<^sub>G} and @{const P\<^sub>0} which will allow us to prove the 
parser's correctness. It is worth noting that we are using the SRPDA for \<open>G\<close>, not for \<open>G'\<close>. 
We first show an auxiliary lemma.

\begin{lemma}\label{nonempty_valids_imp_nonempty_valids_prefix}
If @{prop \<open>valids (\<alpha>@\<beta>) \<noteq> {}\<close>}, then @{prop \<open>valids \<alpha> \<noteq> {}\<close>}
\begin{proof}
Since @{prop \<open>valids (\<alpha>@\<beta>) \<noteq> {}\<close>}, there exists an item @{term \<open>[X \<rightarrow> \<gamma> \<cdot> \<delta>]\<close>} valid for \<open>\<alpha> @ \<beta>\<close>. 
Therefore, there exists a \<open>\<gamma>'\<close> such that \<open>\<alpha> @ \<beta> = \<gamma>' @ \<gamma>\<close>. We now distinguish cases on whether \<open>\<alpha>\<close> is 
a prefix of \<open>\<gamma>'\<close>. If it is, we show there must exist a valid item for \<open>\<alpha>\<close> by 
Lemma~\ref{derivers_substring_reliable}. Otherwise, there exists an \<open>\<alpha>'\<close> with \<open>\<gamma>' @ \<alpha>' = \<alpha>\<close> and 
\<open>\<alpha>' @ \<beta> = \<gamma>\<close>, and thus item @{term \<open>[X \<rightarrow> \<alpha>' \<cdot> \<beta> @ \<delta>]\<close>} is valid for \<open>\<alpha>\<close>, completing the proof.
\end{proof}
\end{lemma}

\begin{lemma}\label{MG_steps_imp_stack_word}
If @{prop \<open>([Init], u) \<turnstile>M* (map Sym \<alpha> @ [Init], v)\<close>} and 
@{prop \<open>valids (rev \<alpha>) \<noteq> {}\<close>}, there exists a stack \<open>qs\<close> such that 
\[ @{prop \<open>\<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<alpha>) # qs, v)\<close>}. \]
\begin{proof}
We induct on the length of the computation for arbitrary \<open>\<alpha>\<close> and \<open>v\<close>.

The reflexive case holds trivially for \<open>qs = []\<close>, since the initial state is @{term \<open>valids []\<close>}.

In the transitive case, we distinguish the type of transition for the final step of the computation.

If the final step is a reading transition, we know the second-to-last configuration is of the form 
\<open>c = (x # xs, a # v)\<close>. We then distinguish cases based on whether \<open>xs\<close> is empty. 

If it is, we know \<open>\<alpha>\<close> is @{term \<open>[Sym (Tm a)]\<close>}. We can therefore show that 
@{prop \<open>\<alpha> \<Turnstile> (mbox [gpda.init P\<^sub>0], a # v) \<turnstile>P* ([valids [Tm a], gpda.init P\<^sub>0], v)\<close>}
by first showing that @{prop \<open>([gpda.init P\<^sub>0], a # v) \<turnstile>P ([valids [Tm a], gpda.init P\<^sub>0], v)\<close>}
holds, using the fact that @{term \<open>gpda.init P\<^sub>0\<close>} is @{term \<open>valids []\<close>}, the fact that 
@{prop \<open>valids \<alpha> \<noteq> {}\<close>} and Lemma~\ref{nxt_dfa_LR0_shift_is_valids_app}. This completes the empty case.

If \<open>xs\<close> on the other hand is nonempty, we know that \<open>c = (map Sym (tl \<alpha>) @ [gpda.init M\<^sub>G], a # v)\<close>.
From Lemma~\ref{nonempty_valids_imp_nonempty_valids_prefix} we know that 
@{term \<open>valids (rev (tl \<alpha>)) \<noteq> {}\<close>} by our assumption that @{prop \<open>valids (rev \<alpha>) \<noteq> {}\<close>}. We can 
therefore use the induction hypothesis to obtain some \<open>qs\<close> with
@{prop \<open>tl \<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<beta>) # qs, a # v)\<close>}.
We can then finish the proof for this case by showing  
@{prop \<open>Tm a # tl \<alpha> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<alpha>) # valids (rev \<beta>) # qs, v)\<close>}
analogously to the case where @{prop \<open>xs = []\<close>}, finishing the shifting transition case.

For the reducing transition case, we know that \<open>c = (map Sym (rev \<beta>) @ map Sym \<gamma> @ [gpda.init M\<^sub>G], v)\<close>.
and @{prop \<open>\<alpha> = Nt A # \<gamma>\<close>}. Since \<open>A\<close> produces \<open>\<beta>\<close> and we originally assumed that @{term \<open>valids \<alpha> \<noteq> {}\<close>},
we can use the definition of reliable prefixes to show that 
@{prop \<open>[A \<rightarrow> \<beta> \<cdot> []] \<in> valids (rev \<gamma> @ \<beta>)\<close>}. We can now use the IH once again to obtain some \<open>qs\<close> 
such that 
\begin{equation}\label{MG_sw}
@{prop \<open>rev \<beta> @ \<gamma> \<Turnstile> ([gpda.init P\<^sub>0], u) \<turnstile>P* (valids (rev \<gamma> @ \<beta>) # qs, v)\<close>}.
\end{equation}

In order to show the implication holds, it suffices for us to show now that 
\begin{multline*}
@{term \<open>Nt A # \<gamma>\<close>}\ \<open>\<Turnstile>\<close>\ @{term \<open>([gpda.init P\<^sub>0], u)\<close>}\\
      \<open>\<turnstile>P*\<close>\ @{term \<open>(valids (rev \<gamma> @ [Nt A]) # drop (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs), v)\<close>}
\end{multline*}

We first show the existence of the reduction step 
\begin{multline}\label{redstep}
  @{term \<open>(valids (rev \<gamma> @ \<beta>) # qs, v)\<close>}\\
  \<open>\<turnstile>P\<close>\ @{term \<open>(valids (rev \<gamma> @ [Nt A]) # drop (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs), v)\<close>}.
\end{multline}
This follows from the fact that @{prop \<open>[A \<rightarrow> \<beta> \<cdot> []] \<in> valids (rev \<gamma> @ \<beta>)\<close>}, and with 
Lemmas~\ref{P0_nth_is_valids_of_nth_stack_word} and \ref{P0_init_stack_word_length_inv} for 
\eqref{MG_sw}, which we use to prove that 
@{prop \<open>(valids (rev \<gamma> @ \<beta>) # qs) ! length \<beta> = valids (rev \<gamma>)\<close>}. The property that 
@{prop \<open>A \<noteq> S'\<close>} is guaranteed by the fact that \<open>A\<close> is in a production of \<open>G\<close>, since it originates
from the computation of @{const M\<^sub>G}.

Next, we need to show that this reduction pops a topmost stack string off the stack, and pushes 
the successor function of the topmost state after popping. We know this popped string is exactly 
@{term \<open>take (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs)\<close>}. With 
Lemma~\ref{P0_init_stack_word_length_inv} again for \eqref{MG_sw}, and 
Lemma~\ref{nxt_dfa_LR0_shift_is_valids_app} we can rewrite the reduction step \eqref{redstep} as
\begin{multline*} 
\<open>(\<close>@{term \<open>take (length \<beta>) (valids (rev \<gamma> @ \<beta>) # qs)\<close>}\\
    \<open>@\<close>\ @{term \<open>valids (rev \<gamma>) # drop ((length \<beta>)+1) (valids (rev \<gamma> @ \<beta>) # qs)\<close>}\<open>, v)\<close>\\
  \<open>\<turnstile>P (\<close> @{term \<open>dfa.nxt LR\<^sub>0 (valids (rev \<gamma>)) (Nt A)\<close>}\\
        \<open>#\<close>\ @{term \<open>valids (rev \<gamma>) # drop ((length \<beta>)+1) (valids (rev \<gamma> @ \<beta>) # qs)\<close>} \<open>, v)\<close>.
\end{multline*}
Finally, we can also use the same instance of the lemma to show that 
@{prop \<open>\<gamma> = drop (length \<beta>) (rev \<beta> @ \<gamma>)\<close>}, completing the 
proof for the computation with stack word @{prop \<open>Nt A # \<gamma> = \<alpha>\<close>}. Since the topmost state of the 
configuration on the RHS of the stack word computation is equal to @{term \<open>rev \<alpha>\<close>}, the proof for the
reduce case is complete.
\end{proof}
\end{lemma}

We can at last prove our parser complete.

\begin{theorem}[Completeness of the canonical \<open>LR(0)\<close> parser]\label{P0_complete}
Every word in @{term \<open>LangS G\<close>} is accepted by @{const P\<^sub>0}.
\begin{proof}
We begin by fixing some \<open>w\<close> in @{term \<open>LangS G\<close>}. By Lemma~\ref{srpda_complete}, this implies
that @{prop \<open>w \<in> MG.Lang\<close>}, i.e., @{prop \<open>([Init], w) \<turnstile>M* ([Final], [])\<close>}. Since @{const Init}
and @{const Final} are distinct by definition, the computation has nonzero length, meaning 
@{prop \<open>([Init], w) \<turnstile>M* ([Sym (Nt S), Init], [])\<close>} holds. Furthermore, it is trivial to prove that
the set @{term \<open>valids [Nt S]\<close>} is nonempty by showing that the item @{term \<open>[S' \<rightarrow> [Nt S] \<cdot> ]\<close>} is
a member. We can now use Lemma~\ref{MG_steps_imp_stack_word} to obtain some \<open>qs\<close> where
\[ @{prop \<open>[Nt S] \<Turnstile> ([gpda.init P\<^sub>0], w) \<turnstile>P* (valids [Nt S] # qs, [])\<close>}. \]
By Lemmas~\ref{P0_nth_is_valids_of_nth_stack_word} and \ref{P0_init_stack_word_length_inv}, we can 
then show that @{prop \<open>qs = [gpda.init P\<^sub>0]\<close>}. With Lemma~\ref{stack_word_imp_P0_steps}, this implies
that @{prop \<open>([gpda.init P\<^sub>0], w) \<turnstile>P* ([valids [Nt S], gpda.init P\<^sub>0], [])\<close>} holds. By the fact that
@{term \<open>[S' \<rightarrow> [Nt S] \<cdot> ]\<close>} is in @{term \<open>valids [Nt S]\<close>}, we know that the RHS configuration of this
computation can then perform a finishing transition, meaning that 
\[ @{prop \<open>([gpda.init P\<^sub>0], w) \<turnstile>P* ([P0_final], [])\<close>}. \]
This is equivalent to @{prop \<open>w \<in> P0.Lang\<close>}, completing the proof.
\end{proof}
\end{theorem}

With the completeness, we can prove our final goal.

\begin{theorem}[Correctness of the canonical \<open>LR(0)\<close> parser]
The language accepted by the canonical \<open>LR(0)\<close> parser is exactly the language of its underlying 
context-free grammar.
\begin{proof}
This is a consequence of Theorems~\ref{P0_sound} and \ref{P0_complete}.
\end{proof}
\end{theorem}

This concludes our formalization of the canonical \<open>LR(0)\<close> parser and the general \<open>LR(0)\<close> parsing 
theory. With this theorem along with the equivalence between \<open>LR(0)\<close> grammars and the parser 
having no \<open>LR(0)\<close>-inadequate states, we have successfully formalized the parsing algorithm 
presented by Wilhelm et al., and verified the correctness of their theories while additionally
proving the parser itself correct.\<close>

section \<open>Conclusion\<close>
subsection \<open>Results\<close>
subsection \<open>Discussion of future work\<close>
subsubsection \<open>Addressing Grammar Extensions: Necessary Conditions\<close>
subsubsection \<open>Implementing an Executable \<open>LR(0)\<close> Parser\<close>

subsubsection \<open>Formalizing \<open>LR(k)\<close> theory for general \<open>k\<close>\<close>
(* maybe *)
subsubsection \<open>Equivalence of PDAs and GPDAs\<close>

(*<*)
end
end
(*>*)
