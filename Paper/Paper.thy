(*<*)
theory Paper
imports
  Context_Free_Grammar.Pumping_Lemma_CFG
  Greibach_Normal_Form.Greibach_Normal_Form
  Chomsky_Schuetzenberger.Chomsky_Schuetzenberger
  Sugar
  PreStar
begin
declare [[show_question_marks=false]]
declare [[names_short=true]]

lemma Expand_hd_simp2: "Expand_hd A (B#Bs) P =
 (let P' = Expand_hd A Bs P
  in Subst_hd P' {r \<in> P'. \<exists>\<alpha>. r = (A, Nt B # \<alpha>)})"
  by simp

lemma Expand_tri_simp2: "Expand_tri (A#As) P =
 (let P' = Expand_tri As P
  in Subst_hd P' {r \<in> P'. \<exists>\<alpha> B. r = (A, Nt B # \<alpha>) \<and> B \<in> set As})"
  by simp

(* problem with eta-contraction of lang_nfa abberv. Make original lang_nfa a def? *)
definition Lang_auto where "Lang_auto = LTS_Automata.Lang_auto"
hide_const (open) LTS_Automata.Lang_auto

lemma pre_star_auto_correct:
  assumes "finite P" and "finite (auto.lts M)"
  shows "Lang_auto (pre_star_auto P M) = pre_star P (Lang_auto M)"
using assms pre_star_auto_correct unfolding Lang_auto_def by blast

lemma pre_star_emptiness':
  fixes P :: "('n, 't) Prods"
  shows "Lang P A \<noteq> {} \<longleftrightarrow> [Nt A] \<in> pre_star P (lists (Tm ` Tms P))"
unfolding lists_eq_set using pre_star_emptiness[of P A] by blast
(*>*)
text \<open>
% sf font for constants?? - if we have too much time :)
% TODO no ==, just =

%rebase LL1 parser on CFG!

\section{Introduction}

This paper reports on a concerted formalization of large parts of the basic of 
context-free grammars and languages (henceforth CFG and CFL).
The formalization is unified in the sense that many of the topics that were 
previously formalized independently (and in different provers) are now
unified in a single formalization, available in the Archive of Formal Proofs as separate entries
\cite{Context_Free_Grammar-AFP,Pushdown_Automata-AFP,Greibach_Normal_Form-AFP,Chomsky_Schuetzenberger-AFP,Parikh-AFP,PreStar-AFP}.
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

When we use the term executability we mean that the definitions (or derived lemmas!) form
a functional program and that Isabelle can generate programs in various functional
languages (Haskell, OCaml and SML) \cite{HaftmannN10}.

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

A production, informally written \<open>A \<rightarrow> \<alpha>\<close>, is a pair of \<open>A :: 'n\<close> and \<open>\<alpha>\<close> \<open>::\<close> \mbox{\<open>sym list\<close>}.
We use the following abbreviations:
\begin{quote}
\<open>syms = sym list\<close> \quad \<open>prod = 'n \<times> syms\<close> \quad \<open>Prods = prod set\<close>
\end{quote}
Variable convention:
\<open>w :: 't list\<close>; words over terminal symbols are called \concept{terminal words};
\<open>\<alpha>, \<beta>, \<gamma> :: syms\<close>; elements of type @{type syms} are usually called sentential forms.

Our theory is primarily based on sets of productions rather than grammars:
the start symbol is irrelevant most of the time.
\emph{For succinctness, we use \concept{grammar} to refer to a set (or list) of productions.}
Moreover, we only restrict to finite sets of productions when necessary.
However, some constructions are hard or impossible even for finite grammars,
unless we have some order on them: if we need to create new variables that appear in the output,
the order in which a grammar is processed is crucial. Therefore we work with \emph{lists} of
productions some of the time and define \<open>prods = prod list\<close>.
We work with sets whenever possible (because of their abstractness) and with lists only if necessary.
Function \<^const>\<open>set\<close> converts in one direction, but we cannot convert from sets to lists
in a computable manner (unless we impose some order on something).

The identifier \<open>P\<close> is reserved for sets of productions.
Every \<open>P\<close> induces a single step derivation relation on \<open>syms\<close> in the standard manner:
\begin{quote}
@{thm derive.intros[of _ \<beta> _ \<alpha> \<gamma>]}
\end{quote}
Its transitive-reflexive closure is denoted by @{prop "P \<turnstile> \<alpha> \<Rightarrow>* \<beta>"}.

The language of some nonterminal \<open>A\<close> generated by \<open>P\<close> is easily defined:
\begin{quote}
@{thm Lang_def}
\end{quote}
There is also the abbreviation @{abbrev "Context_Free_Grammar.lang ps A"}. This is an example of our convention:
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

\subsection{Right-Linear Grammars and Automata}

We have shown that every right-linear grammar (production have the form \<open>A \<rightarrow> w B\<close> or \<open>A \<rightarrow> w\<close>
where \<open>w\<close> is a sequence of terminals) can be transformed into a strongly right-linear one
(productions have the form \<open>A \<rightarrow> a B\<close> or \<open>A \<rightarrow> \<epsilon>\<close> where \<open>a\<close> is a terminal).
Strongly right-linear grammars are just automata in disguise.
Building on Paulson's theory of finite automata \cite{Paulson15} we proved that
the language of a finite strongly right-linear grammar is regular
and every regular language can be generated by a strongly right-linear grammar.


\section{\prestar}

\subsection{Informal Introduction}

%Bouajjani \emph{et al.} \cite{BouajjaniEFMRWW00}
Esparza and Rossmanith\cite{EsparzaR97} realized that a device that Book and Otto \cite{BookO93}
had used to solve problems for string rewriting systems can also be applied to a number of
standard CFG problems (e.g.\ determining if some nonterminal is productive).
Let \<open>P :: ('n,'t) Prods\<close> and \<open>L :: ('n,'t) syms set\<close>.
Then @{term "pre_star P L"} is the set of predecessors of words in \<open>L\<close>
w.r.t.\ @{prop "P \<turnstile> DUMMY \<Rightarrow>* DUMMY"}:
\begin{quote}
@{thm pre_star_def}
\end{quote}
The two key insights are (if \<open>P\<close> finite):
 if \<open>L\<close> is regular, so is \<open>pre_star P L\<close>, and if \<open>L\<close> is given as an NFA \<open>M\<close>,
an NFA for \<open>pre_star P L\<close> can be computed from \<open>M\<close>.
This result has been discovered multiple times \cite{Buechi64,Caucal92}

Why does this help to decide, for example, the productivity problem?
Let \<open>P\<close> be a grammar over a terminal alphabet \<open>\<Sigma>\<close>.
Build an automaton \<open>U\<close> that accepts exactly \<open>\<Sigma>\<^sup>*\<close> (but no words containing @{const Nt}s);
this requires only a single state.
We want to decide if @{prop "Lang P A \<noteq> {}"} for some \<open>A\<close>.
This is the case iff there is a word \<open>w \<in> \<Sigma>\<^sup>*\<close> such that @{prop "P \<turnstile> [Nt A] \<Rightarrow>* w"},
which is the case iff @{text "[Nt A] \<in> pre_star P \<Sigma>\<^sup>*"} \<open>=: L\<close>. But because \<open>U\<close> accepts \<open>\<Sigma>\<^sup>*\<close>
we can compute an automaton for \<open>L\<close> from \<open>U\<close> (as claimed above) and we only need to check
if that automaton accepts @{term \<open>[Nt A]\<close>}.

The algorithm for computing @{const pre_star} on the level of an NFA \<open>M\<close>
extends \<open>M\<close> with new transitions as long as possible.
Given a production \<open>A \<rightarrow> \<alpha>\<close> in \<open>P\<close>, if \<open>M\<close> has a sequence of transitions from state \<open>p\<close>
to state \<open>p'\<close> labeled with \<open>\<alpha>\<close>, we add the transition \<open>(p, Nt A, p')\<close>.


\subsection{Executable Formalization}
%TODO reachable_from -> reachable

For the purpose of computing @{const pre_star}, we represent NFAs over some state type \<open>'s\<close> by
a \concept{labeled transition system} (usually denoted by \<open>T\<close>) of type @{typ\<open>('s,'a) lts\<close>} = \<^typ>\<open>('s \<times> ('n,'t)sym \<times> 's) set\<close>.
It is easy to define a function @{const steps_lts} \<open>::\<close>
@{typ "('s,'a) lts \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's set"}
such that @{term "steps_lts T \<alpha> p"} is the set of states reachable from \<open>p\<close> via \<open>\<alpha>\<close> using \<open>T\<close>.
An automaton \<open>M\<close> (of type \<^typ>\<open>('s,'a) auto\<close>) consists of some \<open>T\<close>, an initial state and a final state set.
If \<open>T\<close> is finite, we call \<open>M\<close> an NFA.
We also define @{term "Lang_auto M"}, the words accepted by \<open>M\<close>, and @{term "reachable_from T q"},
the states reachable from \<open>q\<close> via \<open>T\<close>.
Below, the label type \<^typ>\<open>'a\<close> will always be @{typ\<open>('n,'t)sym\<close>}.

Function @{const pre_lts} adds all possible new transitions to a set of transitions \<open>T\<close>
using the production \<open>P\<close> backwards:
\begin{quote}
@{thm [break] pre_lts_def}% beta -> alpha?
\end{quote}

%TODO while -> lfp
The closure of some \<open>T\<close> under @{const pre_lts} can be defined by repeated application like this:
\begin{quote}
@{thm [break] pre_star_lts_def}
\end{quote}
using the predefined combinator @{const_typ while_option} \cite{Nipkow11}.
We do not dwell on its definition but it is executable because it obeys this recursion equation:
\begin{quote}
@{thm [break] while_option_unfold}
\end{quote}
In case the recursion does not terminate, the mathematical value is @{const None}.
Hence proving that the return value is always @{const Some} amounts to proving termination.

We proved correctness and termination of @{const pre_star_lts}.
Correctness essentially says that the result of @{const pre_star_lts}
is the analogue of @{const pre_star} on the level of @{type lts}:
\begin{quote}
@{thm [break] pre_star_lts_correct}
\end{quote}

%This combinator comes with an partial correctness proof rule for showing that some invariant \<open>P\<close>
%holds for the output \<open>t\<close> if it holds for the input \<open>s\<close>:
%\begin{quote}
%{thm [break] while_option_rule}
%\end{quote}
%Termination can be guaranteed if a) \<open>c\<close> is a monotone function on sets and b)
%there is finite bounding set \<open>C\<close> (the closure) such that @{prop "X \<subseteq> C \<Longrightarrow> f X \<subseteq> C"}.
Termination can be guaranteed under the obvious finiteness assumptions:
\begin{quote}
@{thm pre_star_lts_terminates}
\end{quote}

This is the core of the theory. It is easily lifted to the level of NFAs, yielding
this main correctness theorem:
\begin{theorem}\label{pre_star_auto_correct}
@{thm (concl) pre_star_auto_correct} if \<open>P\<close> and the transitions of \<open>M\<close> are finite.
\end{theorem}


\subsection{Applications}

We show how the membership (in \<open>Lang P A\<close>), nullability and productivity problems can be decided
(following Bouajjani \emph{et al.} \cite{BouajjaniEFMRWW00}).
All of these problems can be reduced to problems of the form \<open>\<alpha> \<in>\<close> \mbox{@{term "pre_star L P"}}
for a suitable regular language \<open>L\<close>. Given an NFA \<open>M\<close> with @{prop \<open>Lang_auto M = L\<close>},
Theorem~\ref{pre_star_auto_correct} translates @{prop \<open>\<alpha> \<in> pre_star L P\<close>} into
@{prop \<open>\<alpha> \<in> Lang_auto (pre_star_auto M P)\<close>}, which can be executed because @{const pre_star_auto}
and membership in @{const Lang_auto} are executable.

The membership problem easily generalizes to derivability because
@{thm [mode=iffSpace] pre_star_derivability}. That is, in order to decide @{prop \<open>P \<turnstile> \<alpha> \<Rightarrow>* \<beta>\<close>}
build an NFA \<open>M\<close> for @{term "{\<beta>}"} and execute @{prop "\<alpha> \<in> Lang_auto(pre_star_auto M P)"}.
As a special case, nullability of \<open>A\<close> is equivalent to @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>* []\<close>}.

Productivity of \<open>A\<close>, i.e.\ reachability of some terminal word, can be expressed like this:
@{thm [mode=iffSpace] pre_star_emptiness'}
where @{term "lists (Tm ` Tms P)"} is the language of all words
over the terminal symbols in \<open>P\<close>. That language is accepted by a simple NFA \<open>M\<close>
and we can evaluate @{prop "[Nt A] \<in> Lang_auto(pre_star_auto M P)"} to determine productivity.

Because @{thm [mode=iffSpace] pre_star_disjointness[where S=A]},
the test for disjointness from and containment in a regular language
(given by an NFA) can also be automated.


\section{Greibach Normal Forms}\label{sec:GNF}%AY

Any \<open>\<epsilon>\<close>-free context-free language has a
\emph{Greibach Normal Form (GNF)} representation,
where every right-hand side is a terminal followed by nonterminals.
The same holds for 
a general version of GNF, which we call \emph{head GNF},\footnote{
This notion is sometimes just called GNF~\cite{BlumK99} or real-time form~\cite{ReghizziBM19}.
}
where
every right-hand side starts with a terminal symbol.
\begin{quote}
@{def GNF_hd}
\end{quote}

In this section we define an executable function @{const GNF_hd_of},
which turns a grammar into head GNF while preserving the language modulo \<open>\<epsilon>\<close>.
It is easy to turn head GNF into GNF by introducing nonterminals for terminals that appear
at non-head position of right-hand sides.

The procedure takes three steps of conversions:
first eliminate \<open>\<epsilon>\<close>-productions (@{const Eps_elim}),
then transform to a triangular form (@{const solve_tri}),
and finally obtain head GNF (@{const Expand_tri}).

The last two steps follow textbook algorithms~\cite{Harrison78,HopcroftU79} for deriving GNF,
except that
we do not require input in Chomsky normal form
but only eliminate \<open>\<epsilon>\<close>-productions.
As a result we arrive at head GNF.

We say a grammar \<open>P\<close> is \emph{triangular on} a list \<open>[A\<^sub>1,...,A\<^sub>n]\<close> of nonterminals,
if \<open>A\<^sub>i \<rightarrow> A\<^sub>j \<alpha> \<in> P\<close> implies \<open>i > j\<close>.
Defined inductively, \<open>P\<close> is triangular on \<open>[]\<close>,
and on \<open>A#As\<close> if it is so on \<open>As\<close> and
there exist no \<open>A \<rightarrow> B \<alpha> \<in> P\<close> with \<open>B \<in> set As\<close>.

We inductively make a grammar which is triangular on \<open>As\<close> also triangular on \<open>A#As\<close>.
First, we repeatedly expand productions of form \<open>A \<rightarrow> B \<alpha>\<close> for all \<open>B \<in> set As\<close>
with respect to the \<open>B\<close>-productions in \<open>P\<close>,
using the following function:
\begin{quote}
@{def[margin=70] "Subst_hd"}\\
@{fun[margin=70] Expand_hd[Expand_hd.simps(1) Expand_hd_simp2]}
\end{quote}


Afterwards productions of form \<open>A \<rightarrow> A v\<close> remain to be solved.
Let \<open>V\<close> collect all such \<open>v\<close>,
and let \<open>U\<close> collect all \<open>u\<close> of productions \<open>A \<rightarrow> u\<close> that does not start with \<open>A\<close>.
Then the language of \<open>A\<close> is that of \<open>U \<union> U V\<^sup>+\<close>;
hence we introduce a fresh nonterminal \<open>A'\<close> whose language corresponds to \<open>V\<^sup>+\<close>,
and replace \<open>A \<rightarrow> A v\<close> productions by \<open>A \<rightarrow> U A'\<close>.

\begin{quote}
@{def Rrec_of_lrec}
\end{quote}

\begin{quote}
@{def Solve_lrec[Solve_lrec_def[unfolded Rm_lrec_def]]}
\end{quote}

The above formalization is almost the same as the textual description,
except that
we do not introduce extra productions if @{prop \<open>V = {}\<close>}.
This optimization is not explicit in \cite[Fig.\ 4.9]{HopcroftU79},
although their Example 4.10 performs this implicitly.

Recursively applying @{const Expand_hd} and @{const Solve_lrec}
transforms \<open>\<epsilon>\<close>-free grammars into triangular forms.
\begin{quote}
@{thm[break] Solve_tri.simps(1)}
\end{quote}

\begin{lemma}
Suppose that
\begin{itemize}
\item \<open>P\<close> is \<open>\<epsilon>\<close>-free (@{thm(prem 1) Triangular_Solve_tri}),
\item \<open>As'\<close> has as many nonterminals as \<open>As\<close> (@{thm(prem 2) Triangular_Solve_tri}),
\item there are no duplicates in \<open>As\<close> and \<open>As'\<close> (@{thm(prem 3) Triangular_Solve_tri}), and
\item nonterminals of \<open>P\<close> are in \<open>As\<close> (@{thm(prem 4) Triangular_Solve_tri}).
\end{itemize}
Then @{thm(concl) Triangular_Solve_tri}.
If moreover @{thm(prem 4) Lang_Solve_tri}
and @{thm(prem 5) Lang_Solve_tri},
then @{thm(concl) Lang_Solve_tri}.
\end{lemma}
Besides the clarification of the conditions,
clarifying the list (\<open>As @ rev As'\<close>) the result is triangular on required some effort.

!!TODO!!

From a triangular form,
expanding head nonterminals in the right order turns the grammar into head GNF.
\begin{quote}
@{fun Expand_tri[Expand_tri.simps(1) Expand_tri_simp2]}\\
\end{quote}
\begin{definition}
@{def GNF_hd_of}
\end{definition}

Because the procedure processes nonterminals one by one,
we explicitly give a list of nonterminals as an argument to @{const GNF_hd_of}.
We also provide a version which computes such a list by
taking the input grammar in the list representation.
It first makes fresh copies \<open>As'\<close> of nonterminals in \<open>As\<close>.

\begin{theorem}
Let \<open>As\<close> be a list of distinct nonterminals in \<open>P\<close>.
Then @{thm(concl) GNF_hd_GNF_hd_of}.
For all @{thm(prem 3) Lang_GNF_hd_of}, @{thm(concl) Lang_GNF_hd_of}.
\end{theorem}

We close the section with demonstrating the exponential complexity of
the (head) GNF translation algorithm~\cite{?}.

This is demonstrated by the family \<open>bad_grammar\<close> of grammars 
where each @{term "bad_grammar n"}
consists of \<open>A\<^sub>0 \<rightarrow> a | b\<close> and $A_{i+1} \to A_i a \mid A_i b$ for \<open>i < n\<close>.

While @{term "bad_grammar n"} is already triangular and consisting of only $2n$ rules,
we formally verify that
the expansion step yields $2^{n+1}$ productions for \<open>A\<^sub>n\<close>.

\begin{theorem}
@{thm Expand_tri_blowup}
\end{theorem}



\section{Chomsky-Sch\"utzenberger}\label{sec:ChSch}

The Chomsky-Sch\"utzenberger Theorem \cite{ChomskyS} states that every CFL is the homomorphic image of the
intersection of a Dyck language and a regular language, where a Dyck language is a language
of properly parenthesized words over some alphabet of opening and closing parentheses,
e.g. $\{(,),[,]\}$. It is sometimes called the Chomsky-Sch\"utzenberger Representation Theorem
to distinguish it from the Chomsky-Sch\"utzenberger Enumeration Theorem \cite{ChomskyS}
about the number of words of a given length generated by an unambiguous CFG. 

\begin{quote}% a random example
@{fun transform_rhs}
\end{quote}


\section{Parikh}\label{sec:Parikh}%FL

In a nutshell, Parikh's Theorem says that if we consider words not as lists but as multisets of
terminals, then every context-free language is regular. A simple consequence is that any CFL

We follow the proof by Pilling \cite{Pilling}.


\section{Conclusion}

The total size of the formalizations discussed in the paper runs to 17 KLOC. + PreStar!
\<close>
(*<*)
end
(*>*)