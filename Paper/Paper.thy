(*<*)
theory Paper
imports
  Context_Free_Grammar.Pumping_Lemma_CFG
  Greibach_Normal_Form.Greibach_Normal_Form
  Base.Algorithm
  Sugar
  PreStar
begin
declare [[show_question_marks=false]]

lemma expand_hd_simp2: "expand_hd A (B#Bs) P =
 (let P' = expand_hd A Bs P
  in subst_hd P' {r \<in> P'. \<exists>w. r = (A, Nt B # w)})"
  by simp

lemma expand_tri_simp2: "expand_tri (A#As) P =
 (let P' = expand_tri As P
  in subst_hd P' {r \<in> P'. \<exists>w B. r = (A, Nt B # w) \<and> B \<in> set As})"
  by simp

(*>*)
text \<open>
% TODO no ==, just =

%rebase LL1 parser on CFG!

\section{Introduction}

This paper reports on a concerted formalization of large parts of the basic of 
context-free grammars and languages (henceforth CFG and CFL).
The formalization is unified in the sense that many of the topics that were 
previously formalized independently (and in different provers) are now
unified in a single formalization, available in the Archive of Formal Proofs as separate entries
\cite{Context_Free_Grammar-AFP,Pushdown_Automata-AFP,Greibach_Normal_Form-AFP,Chomsky_Schuetzenberger-AFP,Parikh-AFP}.
%TODO pre*

The main contributions of our work are:
\begin{itemize}
\item a verified executable transformation into Greibach Normal Form (Sect.~\ref{sec:GNF}),
\item a verified \prestar\ algorithm for solving many CFG problems automatically
 (e.g.\ the word problem), and
\item the verification of two foundational theorems of context-free languages that had not been formalized before:
the Chomsky-Sch\"utzenberger Theorem (Sect.~\ref{sec:ChSch}) and Parikh's Theorem (Sect.~\ref{sec:Parikh}).
\end{itemize}

Of course only textbook+, no parsing (separate).

%\subsection{Related Work}

We will mostly discuss related work at the relevant places, but would like to mention already
the three related formalizations that are closest to our work: the work by
Barthwal and Norrish \cite{csl/BarthwalN10,wollic/BarthwalN10,BarthwalN14} (in HOL4),
Hofmann \cite{JHofmann} (in Coq) and Ramos \emph{et al.} \cite{RamosAMQ,RamosAMQ16,RamosQMA16} (in Coq).


\subsection{Isabelle Notation} \label{sec:isabelle}

Isabelle is based on a fragment of higher-order logic. It supports core
concepts commonly found in functional programming languages.

The notation \<open>t :: \<tau>\<close> indicates that term \<open>t\<close> has type
\<open>\<tau>\<close>. Basic types include @{typ bool} and @{typ nat}, while type variables are written @{typ 'a}, @{typ 'b} etc.
Pairs are expressed
as \mbox{@{term "(a, b)"}}, and triples as @{term "(a, b, c)"}, and so forth.
%Functions {term fst} and {term snd} return the first and second components of a pair,
%while the operator {term "(\<times>)"} is used for pairs at the type level.
Most type constructors are written postfix, such as @{typ "'a set"} and  @{typ "'a list"}, and the function
space arrow is \<open>\<Rightarrow>\<close>. Function @{const set} converts a list to a set.

Lists are constructed from the empty list @{term "[]"} using the infix cons-operator @{term "(#)"}.
The operator @{term "(@)"} appends two lists, @{term "length xs"} denotes the length of @{term xs},
@{term "xs!n"} returns the \<open>n\<close>-th element of the list @{term xs} (starting with @{prop "n=(0::nat)"}).
%and @{term "take n xs"} is the prefix of length \<open>n\<close> of \<open>xs\<close>.

Algebraic data types are defined using the \isakeyword{datatype} keyword. A predefined data type:
\begin{quote}
@{datatype option}
\end{quote}
The notation \mbox{\<open>\<lbrakk>A\<^sub>1, \<dots>, A\<^sub>n\<rbrakk> \<Longrightarrow> B\<close>} denotes an implication with premises \<open>A\<^sub>1\<close>, \ldots, \<open>A\<^sub>n\<close> and conclusion \<open>B\<close>.
Equality on type @{type bool} denotes logical equivalence.


\section{The Basic Theory}

\subsection{Context-Free Grammars}

All our types are parameterized by type variables \<open>'n\<close> and \<open>'t\<close>, the types of nonterminals and terminals.
Symbols are a tagged union type:
\begin{quote}
@{datatype sym}
\end{quote}
Variable convention:
 \<open>a, b, c :: 't\<close>, \<open>A, B, C :: 'n\<close> and  \<open>x, y, z :: ('n,'t) sym\<close>.
For compactness we sometimes drop the \<open>'n\<close> and \<open>'t\<close> parameters,
e.g.\ we write \<open>sym\<close> instead of \<open>('n,'t)sym\<close>.

A production, informally written \<open>A \<rightarrow> w\<close>, is a pair of \<open>A :: 'n\<close> and a \<open>w\<close> \<open>::\<close> \mbox{\<open>sym list\<close>}.
We use the following abbreviations:
\begin{quote}
\<open>syms = sym list\<close> \quad \<open>prod = ('n \<times> syms)\<close> \quad \<open>Prods = prod set\<close>
\end{quote}
Variable convention:
\<open>u, v, w\<close> are \<open>syms\<close> of the form @{term "map Tm"} \<open>\<dots>\<close>, which we call \concept{words};
\<open>\<alpha>, \<beta>, \<gamma> :: syms\<close>; \<open>syms\<close> are sometimes called \concept{sentential forms}.


Our theory is primarily based on sets of productions rather than grammars:
the start symbol is irrelevant most of the time.
\emph{For succinctness, we use \concept{grammar} to refer to a set (or list) of productions.}
Moreover, we only restrict to finite sets of productions when necessary.
However, some constructions are hard or impossible even for finite grammars,
unless we have some order on them: if we need to create new variables that appear in the output,
the order in which a grammar is processed is crucial. Therefore we work with \emph{lists} of
productions half of the time and define \<open>prods = prod list\<close>.
We work with sets whenever possible (because of their abstractness) and with lists only if necessary.
Function \<^const>\<open>set\<close> converts in one direction, but we cannot convert from sets to lists
in a computable manner (unless we impose some order on something).

The identifier \<open>P\<close> is reserved for sets of productions.
Every \<open>P\<close> induces a single step derivation relation on \<open>syms\<close> in the standard manner:
\begin{quote}
@{thm derive.intros[of _ \<beta> _ \<alpha> \<gamma>]}
\end{quote}
Its transitive-reflexive closure is denoted by @{prop "P \<turnstile> u \<Rightarrow>* w"}.

The language of some nonterminal \<open>A\<close> generated by \<open>P\<close> is easily defined:
\begin{quote}
@{thm Lang_def}
\end{quote}
There is also the abbreviation @{abbrev "lang ps A"}. This is an example of our convention:
functions named \<open>Fn\<close> (starting with a capital letter) operate on sets, the lower case \<open>fn\<close>
is its analogue on lists. We usually present only one of the two versions and silently use the other one
(if it exists).

Fresh names are generated by these functions: @{term "fresh0 X"} (generates a name not in \<open>X\<close>)
and @{term "freshs X As"} (generates variants of the names in list \<open>As\<close> not in \<open>X\<close>).
These functions live in type classes. Executable instances for \<open>nat\<close>, \<open>int\<close> and \<open>string\<close> exist
but our proofs are independent of them.


\subsection{Chomsky Normal Form and Pumping Lemma}

Naturally we have shown that a finite grammar has an equivalent (modulo \<open>[]\<close>) finite grammar in Chomsky Normal Form:
\begin{quote}
@{thm CNF_def}\\
@{thm cnf_exists}
\end{quote}
Our proof is based on the one by Bart A constructive formalization is due to Hofmann \<^cite>\<open>JHofmann\<close>.
Ramos \cite{RamosAMQ} also formalized four applications, two of which we also formalized
(non-context freeness of $a^nb^nc^n$ and non-closedness of context-free languages under intersection)
using only 10--15\% of the number of lines.

It is worth pointing out a detail of our proof (due to Thomas Ammer),
namely how to avoid formalizing any kind of parse trees (as done in other formalizations).
It suffices to introduce these two inductive relations, assuming \<open>P\<close> is in CNF:
@{prop "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w"} means that \<open>p :: 'n list\<close> is a path in the (implicit) parse tree
of the derivation from \<open>B :: 'n\<close> to \<open>w :: 't list\<close>; @{prop "P \<turnstile> A \<Rightarrow>\<llangle>p\<rrangle> w"} is similar
but \<open>p\<close> is the longest path. This avoids reasoning about trees altogether.

\subsection{Pushdown Automata}

Pushdown automata and the standard equivalence proofs
(with CFGs, and equivalence of acceptance by empty stack and final state)
were first formalized by Barthwal and Norrish \cite{wollic/BarthwalN10}.
Our proofs are largely based on this online Lean formalization \cite{Leichtfried}
and are found here \cite{Pushdown_Automata-AFP}.

\subsection{Automata}

2DFA AFA?


\section{\prestar}

\subsection{Informal Introduction}

Bouajjani \emph{et al.} \cite{BouajjaniEFMRWW00} realized that a device that Book and Otto \cite{BookO93}
had used to solve problems
for string rewriting systems can also be applied to a number of standard CFG problems
(e.g.\ determining if some nonterminal is productive).
Let \<open>P :: ('n,'t) Prods\<close> and \<open>L :: ('n,'t) list set\<close>.
Then @{term "pre_star P L"} is the set of predecessors of words in \<open>L\<close>
w.r.t.\ @{prop "P \<turnstile> DUMMY \<Rightarrow>* DUMMY"}:
\begin{quote}
@{thm pre_star_def}
\end{quote}
The two key insights are that (if \<open>P\<close> finite):
 if \<open>L\<close> is regular, so is \<open>pre_star P L\<close>, and if \<open>L\<close> is given as an NFA \<open>M\<close>,
an NFA for \<open>pre_star P L\<close> can be computed \<open>M\<close>.

Why does this help to decide, for example, the productivity problem?
Let \<open>P\<close> be a grammar over a terminal alphabet \<open>\<Sigma>\<close>.
Build an automaton \<open>U\<close> that accepts exactly \<open>\<Sigma>\<^sup>*\<close> (but no mixed word!);
this requires only a single state.
We want to decide if @{prop "Lang P A \<noteq> {}"} for some \<open>A\<close>.
This is the case iff there is a word \<open>w \<in> \<Sigma>\<^sup>*\<close> such that @{prop "P \<turnstile> [Nt A] \<Rightarrow>* w"},
which is the case iff @{text "[Nt A] \<in> pre_star P \<Sigma>\<^sup>*"} \<open>=: L\<close>. But because \<open>U\<close> accepts \<open>\<Sigma>\<^sup>*\<close>
we can compute an automaton for \<open>L\<close> from \<open>U\<close> (as claimed above) and we only need to check
if that automaton accepts @{term \<open>[Nt A]\<close>}.

The algorithm for computing @{const pre_star} on the level of an NFA \<open>M\<close>
extends \<open>M\<close> with new transitions as long as possible.
Given a production \<open>A \<rightarrow> \<alpha>\<close> in \<open>P\<close>, if \<open>M\<close> has a sequence of transitions from state \<open>p\<close>
to state \<open>p'\<close> labeled with \<open>\<alpha>\<close>, we add the transition \<open>(p, Nt A, p')\<close>. Now comes
the formalization.


\subsection{Executable Formalization}
%TODO reachable_from -> reachable
%TODO lang_nfa -> Lang_nfa

For the purpose of computing \prestar\, we represent NFAs over some state type \<open>'s\<close> by
transitions of type \<^typ>\<open>'s \<times> ('n,'t)sym \<times> 's\<close>. A set of such triples is usually denoted by \<open>\<delta>\<close>.
It is easy to define a function @{const steps} of type
@{typ "('s \<times> ('n,'t)sym \<times> 's) set \<Rightarrow> ('n,'t)syms \<Rightarrow> 's \<Rightarrow> 's set"}
such that @{term "steps \<delta> \<alpha> p"} is the set of states reachable from \<open>p\<close> via \<open>\<alpha>\<close> using \<open>\<delta>\<close>.
An NFA \<open>M\<close> consists of some \<open>\<delta>\<close>, an initial state and a final state set.
We also define @{text "lang_nfa M"}, the words accepted by \<open>M\<close>, and @{term "reachable_from \<delta> q"},
the states reachable from \<open>q\<close> via \<open>\<delta>\<close>.

Function @{const prestar_step} adds all possible new transitions to a set of transitions \<open>\<delta>\<close>
using the production \<open>P\<close> backwards:
\begin{quote}
@{thm [break] prestar_step_def}% beta -> alpha?
\end{quote}

%TODO while -> lfp
The closure of some \<open>\<delta>\<close> under @{const prestar_step} can be defined by repeated application like this:
\begin{quote}
@{thm [break] prestar_while_def}
\end{quote}
using the predefined combinator @{const_typ while_option} \cite{Nipkow11}.
We do not dwell on its definition but it is executable because it obeys this recursion equation:
\begin{quote}
@{thm [break] while_option_unfold}
\end{quote}
In case the recursion does not terminate, the mathematical value is @{const None}.
Hence proving that the return value is always @{const Some} amounts to proving termination.

Using the lemma library for @{const while_option}, we proved correctness and termination
of @{const prestar_while}. Correctness essentiall says that the result of @{const prestar_while}
is the analogue of @{const pre_star} on the level of transition relations:
\begin{quote}
@{thm [break] prestar_while_correct}
\end{quote}
%TODO wait for new version
%define lang_trans

%This combinator comes with an partial correctness proof rule for showing that some invariant \<open>P\<close>
%holds for the output \<open>t\<close> if it holds for the input \<open>s\<close>:
%\begin{quote}
%{thm [break] while_option_rule}
%\end{quote}
%Termination can be guaranteed if a) \<open>c\<close> is a monotone function on sets and b)
%there is finite bounding set \<open>C\<close> (the closure) such that @{prop "X \<subseteq> C \<Longrightarrow> f X \<subseteq> C"}.
Termination can be guaranteed under the obvious finiteness assumptions:
\begin{quote}
@{thm prestar_while_terminates}
\end{quote}

This is the core of the theory which is then lifted to the level of NFAs.

\subsection{Applications}

Membership or Word Problem: generalize to derivability:
pre_star_derivability:
  \<open>P \<turnstile> \<alpha> \<Rightarrow>* \<beta> \<longleftrightarrow> \<alpha> \<in> pre_star P {\<beta>}\<close>
build NFA B for \<open>{\<beta>}\<close>, compute A = prestar-nfa B, decide if A accepts \<open>\<alpha>\<close>

Nullability reduces to can \<open>[]\<close> be derived.

Productivity: \<open>[Nt A]\<close> in pre_star P UNIV

Always word in lang

\section{Greibach}\label{sec:GNF}%AY

--- notes ---\\
\<^cite>\<open>BlumK99\<close> defines Greibach as our head Greibach.
\<^cite>\<open>ReghizziBM19\<close> calls it real-time.
\\--- note ends ---\\


\begin{definition}
A grammar \<open>P\<close> is in \emph{head Greibach normal form (GNF)} if
every right-hand side in \<open>P\<close> starts with a terminal symbol.
Formally,
\begin{quote}
@{def GNF_hd}
\end{quote}
\end{definition}

The main result of this section is the construction of the function @{const gnf_hd},
which turns a grammar into GNF while preserving the language modulo \<open>\<epsilon>\<close>.
\begin{theorem}
@{thm GNF_hd_gnf_hd}\\
@{thm Lang_gnf_hd}
\end{theorem}
Note that @{const gnf_hd} takes grammar in a list representation \<open>ps\<close>,
because the algorithm depends on the order of productions.
Moreover, because the translation introduces fresh nonterminals,
the language preservation is restricted to nonterminals
which already appear in the original grammar (\<open>A \<in> nts ps\<close>).
(This will not be relevant if one fixes the start symbol.)

The outline of the definition of @{const gnf_hd} is as follows:
\begin{definition}
@{def gnf_hd}
\end{definition}
It first enumerates the nonterminals as a list \<open>As\<close>,
and make their fresh copies as \<open>As'\<close>.
Then it takes three steps of conversions:
first eliminate \<open>\<epsilon>\<close>-productions (@{const Eps_elim}),
then transform to a triangular form (@{const solve_tri}),
and finally obtain head GNF (@{const expand_tri}).
The last two steps follow textbook algorithms for deriving
GNF~\cite{Harrison78,HopcroftU79},
except that we do not require input in Chomsky normal form
but only eliminate \<open>\<epsilon>\<close>-productions.
As a result we arrive at head GNF, and turning them into GNF is easy.
!!TODO!!

We say a grammar \<open>P\<close> is \emph{triangular on} a list \<open>[A\<^sub>1,...,A\<^sub>n]\<close> of nonterminals,
if \<open>A\<^sub>i \<rightarrow> A\<^sub>j \<alpha> \<in> P\<close> implies \<open>i > j\<close>.
Inductively, \<open>P\<close> is triangular on \<open>[]\<close>,
and on \<open>A#As\<close> if it is on \<open>As\<close> and \<open>A \<rightarrow> B \<alpha> \<in> P\<close> implies \<open>B \<notin> set As\<close>.

To make triangular grammar \<open>P\<close> on \<open>As\<close> triangular on \<open>A#As\<close>,
first, repeatedly expand \<open>A \<rightarrow> B \<alpha> \<in> P\<close> for all \<open>B \<in> set As\<close>
with respect to the \<open>B\<close>-productions in \<open>P\<close>.
Formally,
\begin{quote}
@{def "subst_hd"}\\
@{fun expand_hd[expand_hd.simps(1) expand_hd_simp2]}
\end{quote}


Afterwards productions of form \<open>A \<rightarrow> A v \<in> P\<close> remain to be solved.
Let \<open>V\<close> collect all such \<open>v\<close>,
and let \<open>U\<close> collect all \<open>u\<close> of \<open>A \<rightarrow> u \<in> P\<close> that does not start with \<open>A\<close>.
Then the language of \<open>A\<close> is \<open>U \<union> U V\<^sup>+\<close>;
hence we introduce a fresh nonterminal \<open>A'\<close> whose language is \<open>V\<^sup>+\<close>.

\begin{quote}
@{def rrec_of_lrec}
\end{quote}

\begin{quote}
@{def solve_lrec[solve_lrec_def[unfolded rm_lrec_def]]}
\end{quote}

The above formalization is almost the same as the textual description,
except that
we do not introduce extra productions if @{prop \<open>V = {}\<close>}.
This optimization is not present in \<^cite>\<open>HopcroftU79\<close>,
although their Example 4.10 performs this implicitly.

Recursively applying @{const solve_lrec} and @{const expand_hd}
transforms a grammar into a triangular form.
\begin{quote}
@{fun solve_tri}
\end{quote}

\begin{theorem}
Assume @{thm(prem 1) triangular_solve_tri},
@{thm(prem 2) triangular_solve_tri},
and @{thm(prem 3) triangular_solve_tri}.
Then @{thm(concl) triangular_solve_tri}.
If moreover @{thm(prem 4) solve_tri_Lang}
and @{thm(prem 5) solve_tri_Lang},
then @{thm(concl) solve_tri_Lang}.
\end{theorem}

<<<<<<< Updated upstream
\begin{quote}
@{def subst_hd}
\end{quote}
=======
>>>>>>> Stashed changes


\begin{quote}
@{fun expand_tri[expand_tri.simps(1) expand_tri_simp2]}
\end{quote}

\subsection{Complexity}

It is known that the textbook algorithms for deriving GNF has
exponential worst-case complexity~\cite{?},
and the situation is the same for our head GNF transformation.

This is demonstrated by the family \<open>bad_grammar\<close> of grammars 
where each @{term "bad_grammar n"}
consists of \<open>A\<^sub>0 \<rightarrow> a | b\<close> and $A_{i+1} \to A_i a \mid A_i b$ for \<open>i < n\<close>.

While @{term "bad_grammar n"} is already triangular and consisting of only $2n$ rules,
we formally verify that
the expansion step yields $2^{n+1}$ productions for \<open>A\<^sub>n\<close>.

\begin{theorem}
@{thm expand_tri_blowup}
\end{theorem}



\section{Chomsky-Sch\"utzenberger}\label{sec:ChSch}

The Chomsky-Sch\"utzenberger Theorem \cite{ChomskyS} states that every CFL is the homomorphic image of the
intersection of a Dyck language and a regular language, where a Dyck language is a language
of properly parenthesized words over some alphabet of opening and closing parentheses,
e.g. $\{(,),[,]\}$. It is sometimes called the Chomsky-Sch\"utzenberger Representation Theorem
to distinguish it from the Chomsky-Sch\"utzenberger Enumeration Theorem \cite{ChomskyS}
about the number of words of a given length generated by an unambiguous CFG. 


\section{Parikh}\label{sec:Parikh}%FL

In a nutshell, Parikh's Theorem says that if we consider words not as lists but as multisets of
terminals, then every context-free language is regular. A simple consequence is that any CFL

We follow the proof by Pilling \cite{Pilling}.
\<close>
(*<*)
end
(*>*)