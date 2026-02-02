(*<*)
theory Paper
imports
  Context_Free_Grammar.Pumping_Lemma_CFG
  Greibach_Normal_Form.Greibach_Normal_Form
  Chomsky_Schuetzenberger.Chomsky_Schuetzenberger
  Pre_Star_CFG.Applications
  Parikh.Pilling
  Sugar
begin
declare [[show_question_marks=false]]
declare [[names_short=true]]

lemma Expand_hd_rec_simp2: "Expand_hd_rec A (B#Bs) P =
 (let P' = Expand_hd_rec A Bs P
  in Subst_hd P' {r \<in> P'. \<exists>\<alpha>. r = (A, Nt B # \<alpha>)})"
  by simp

lemma Expand_tri_simp2: "Expand_tri (A#As) P =
 (let P' = Expand_tri As P
  in Subst_hd P' {r \<in> P'. \<exists>\<alpha> B. r = (A, Nt B # \<alpha>) \<and> B \<in> set As})"
  by simp

notation (latex) P1 ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>1\<^latex>\<open>}\<close>")
notation (latex) P2 ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>2\<^latex>\<open>}\<close>")
notation (latex) P3 ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>3\<^latex>\<open>}\<close>")
notation (latex) P4 ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>4\<^latex>\<open>}\<close>")
notation (latex) P5 ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>5\<^latex>\<open>}\<close>")

notation (latex) P1' ("\<^latex>\<open>$\\isaconst{P}_1'$\<close>")
notation (latex) P1_sym ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>1'_sym\<^latex>\<open>}\<close>")
notation (latex) P5_sym ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>5'_sym\<^latex>\<open>}\<close>")
notation (latex) P7_sym ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>7'_sym\<^latex>\<open>}\<close>")
notation (latex) P8_sym ("\<^latex>\<open>\\isaconst{\<close>P\<^sub>8'_sym\<^latex>\<open>}\<close>")

consts brackets :: "'a \<Rightarrow> 'b set" (* fake constant only used in formulas in text below *)

notation reachable_from ("\<^latex>\<open>\\isaconst{\<close>reachable'_lts\<^latex>\<open>}\<close>")

(* problem with eta-contraction of Lang_lts abbrv. Make Lang_lts a def? *)
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

notation parikh_img ("\<Psi>")
notation reg_eval ("\<^latex>\<open>\\isaconst{\<close>reg'_pres\<^latex>\<open>}\<close>")

lemma bipart_rlexp_def:
  "bipart_rlexp x f = (\<exists>p q. mbox0(reg_eval p \<and> reg_eval q) \<and>
    f = Union p (Concat q (Var x)) \<and> x \<notin> vars p)"
  by(simp add: mbox0_def bipart_rlexp_def)
(*>*)
text \<open>
% TODO
%rebase LL1 parser on CFG - if we have too much time :)

\section{Introduction}

This paper reports on a concerted formalization of large parts of the basic theory of 
context-free grammars and languages (henceforth CFG and CFL).
The formalization is unified in the sense that many of the topics that were 
previously formalized independently (and in different provers) are now
unified in a single formalization, available in the Archive of Formal Proofs as separate entries
\cite{Context_Free_Grammar-AFP,Pushdown_Automata-AFP,Greibach_Normal_Form-AFP,Chomsky_Schuetzenberger-AFP,Parikh-AFP,Pre_Star_CFG-AFP}.

The main novel contributions of our work are:
\begin{itemize}
\item a verified executable transformation into Greibach Normal Form (Sect. \ref{sec:GNF}),
\item a verified executable \prestar\ algorithm for solving a number of elementary CFG problems
 (e.g.\ the word problem) automatically (Sect. \ref{sec:prestar}), and
\item the verification of two foundational theorems of context-free languages that had not been formalized before:
the Chomsky-Sch\"utzenberger Theorem (Sect. \ref{sec:ChSch}) and Parikh's Theorem (Sect. \ref{sec:Parikh}).
\end{itemize}

When we use the term executability we mean that the definitions (or derived lemmas!) form
a functional program and that Isabelle can generate programs in various functional
languages (Haskell, OCaml and SML) \cite{HaftmannN10}.

%\subsection{Related Work}

We will mostly discuss related work at the relevant places, but would like to mention already
the three related formalizations that are closest to our work: the work by
Barthwal and Norrish \cite{BarthwalPhD,csl/BarthwalN10,wollic/BarthwalN10,BarthwalN14} (in HOL4),
Hofmann \cite{JHofmann} (in Coq) and Ramos \emph{et al.} \cite{RamosAMQ,RamosAMQ16,RamosQMA16} (in Coq).

The one fundamental area we do not cover is parsing. Specific parsing algorithms
have been formalized in the literature independently
(e.g.\ \cite{BarthwalN09,JourdanPL12,LasserCFR19,BlaudeauS20,RauN24}).


\subsection{Isabelle Notation} \label{sec:isabelle}

Isabelle is based on a fragment of higher-order logic. It supports core
concepts commonly found in functional programming languages.

The notation \<open>t :: \<tau>\<close> means that term \<open>t\<close> has type
\<open>\<tau>\<close>. Basic types include @{typ bool} and @{typ nat}, while type variables are written @{typ 'a}, @{typ 'b} etc.
Functions @{const fst} and @{const snd} return the first and second components of a pair,
Most type constructors are written postfix, such as @{typ "'a set"} and  @{typ "'a list"}, and the function
space arrow is \<open>\<Rightarrow>\<close>.
The image of function \<open>f\<close> over set \<open>M\<close> is denoted by \<^term>\<open>f ` M\<close>.
Function update @{term "f(a := b)"} is short for @{thm (rhs) fun_upd_def}.

Lists are constructed from the empty list @{term "[]"} using the infix cons-operator @{term "(#)"}.
The operator @{term "(@)"} appends two lists, @{term "length xs"} denotes the length of @{term xs},
and @{const set} converts a list to a set.
%{term "xs!n"} returns the \<open>n\<close>-th element of the list {term xs} (starting with @{prop "n=(0::nat)"}).
%and {term "take n xs"} is the prefix of length \<open>n\<close> of \<open>xs\<close>.

Algebraic data types are defined using the \isakeyword{datatype} keyword. A predefined data type:
%\begin{quote}
@{datatype option}
%\end{quote}

The notation \mbox{\<open>\<lbrakk>A\<^sub>1, \<dots>, A\<^sub>n\<rbrakk> \<Longrightarrow> B\<close>} denotes an implication with premises \<open>A\<^sub>1\<close>, \ldots, \<open>A\<^sub>n\<close> and conclusion \<open>B\<close>.
Equality on type @{type bool} denotes logical equivalence.


\section{The Basic Theory}

\subsection{Context-Free Grammars}

All our types are parameterized by type variables \<open>'n\<close> and \<open>'t\<close>, the types of \concept{nonterminals} and \concept{terminals}.
\concept{Symbols} are a tagged union type:
\begin{quote}
@{datatype sym}
\end{quote}
Variable convention:
 \<open>a, b, c :: 't\<close>, \<open>A, B, C :: 'n\<close> and  \<open>x, y, z :: ('n,'t) sym\<close>.
For compactness we sometimes drop the \<open>'n\<close> and \<open>'t\<close> parameters,
e.g.\ we write \<open>sym\<close> instead of \<open>('n,'t)sym\<close>.

A \concept{production}, informally written \<open>A \<rightarrow> \<alpha>\<close>, is a pair of \<open>A :: 'n\<close> and \<open>\<alpha>\<close> \<open>::\<close> \mbox{\<open>sym list\<close>}.
We use the following abbreviations:
\begin{quote}
\<open>syms = sym list\<close> \quad \<open>prod = 'n \<times> syms\<close> \quad \<open>Prods = prod set\<close>
\end{quote}
Variable convention:
\<open>w :: 't list\<close>; words over terminal symbols are called \concept{terminal words};
\<open>\<alpha>, \<beta>, \<gamma> :: syms\<close>; elements of type @{type syms} are called \concept{sentential forms}.

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

We also have parse trees and their relation to \<open>\<Rightarrow>*\<close>,
which turns out to be useful not just for parsing but also in
the proof of the Chomsky-Sch\"utzenberger Theorem below.

%Fresh names are generated by these functions: @ {term "fresh0 X"} (generates a name not in \<open>X\<close>)
%and @ {term "freshs X As"} (generates variants of the names in list \<open>As\<close> not in \<open>X\<close>).
%These functions live in type classes. Executable instances for \<open>nat\<close>, \<open>int\<close> and \<open>string\<close> exist
%but our proofs are independent of them.


\subsection{Chomsky Normal Form and Pumping Lemma}

We have defined an executable translation into Chomsky Normal Forms
\begin{quote}
@{thm CNF_def}\smallskip\\
@{thm [break]cnf_of_def}
\end{quote}
and proved its correctness:
\begin{quote}
@{thm cnf_of_CNF_Lang(1)} \qquad @{thm cnf_of_CNF_Lang(2)}
\end{quote}
Our proof is based partly on the non-constructive one by Barthwal and Norrish \cite{csl/BarthwalN10}.
Another constructive translation was formalized by Hofmann \<^cite>\<open>JHofmann\<close>.

The first formal proof of the Pumping Lemma is due to Barthwal \cite{BarthwalPhD},
followed by Ramos \emph{et al.} \cite{RamosAMQ16}.
Our proof is due to Thomas Ammer and has the unique feature that it does not require parse trees.
He introduces these two inductive relations, assuming \<open>P\<close> is in CNF:
@{prop "P \<turnstile> A \<Rightarrow>\<langle>p\<rangle> w"} means that \<open>p :: 'n list\<close> is a path in the (implicit!) parse tree
of the derivation from \<open>B :: 'n\<close> to \<open>w :: 't list\<close>; @{prop "P \<turnstile> A \<Rightarrow>\<llangle>p\<rrangle> w"} is similar
but \<open>p\<close> is the longest path.
Ramos \emph{et al.} \cite{RamosAMQ} also formalized four applications, two of which we also formalized
(non-context freeness of $a^nb^nc^n$ and non-closedness of context-free languages under intersection)
using only 10--15\% of the number of lines.


\subsection{Pushdown Automata}

Pushdown automata and the standard equivalence proofs
(with CFGs, and equivalence of acceptance by empty stack and final state)
were first formalized by Barthwal and Norrish \cite{wollic/BarthwalN10}.
Our proofs are largely based on this online Lean formalization \cite{Leichtfried}
and are found here \cite{Pushdown_Automata-AFP}.

\subsection{Right-Linear Grammars and Automata}

We have shown that every right-linear grammar (production have the form \<open>A \<rightarrow> wB\<close> or \<open>A \<rightarrow> w\<close>
where \<open>w\<close> is a terminal word) can be transformed into a strongly right-linear one
(productions have the form \<open>A \<rightarrow> aB\<close> or \<open>A \<rightarrow> \<epsilon>\<close> where \<open>a\<close> is a terminal symbol).
Strongly right-linear grammars are just automata in disguise.
Building on Paulson's theory of finite automata \cite{Paulson15} we proved that
the language of a finite strongly right-linear grammar is regular
and every regular language can be generated by a strongly right-linear grammar.


\section{Greibach Normal Forms}\label{sec:GNF}%AY

Any \<open>\<epsilon>\<close>-free context-free language has a
\concept{Greibach Normal Form} (\concept{GNF}) representation,
where every right-hand side is a terminal followed by nonterminals.
\begin{quote}
@{def GNF}
\end{quote}
In this section we formalize an executable function @{const GNF_of},
which turns a grammar into GNF while preserving the language modulo \<open>\<epsilon>\<close>.

While there already exists a HOL4-formalization of GNF transformation~\cite{BarthwalPhD},
the previous formalization only proves
that there exists a path of small language-preserving transformations leading to GNF,
but does not tell how to reach GNF.
To the best of our knowledge,
our work is the first executable GNF transformation whose correctness is formally proved.
In addition, our version does not require the initial CNF transformation,
and the (exponential) complexity is also formalized.

We start with a weaker version of GNF, which we call \concept{head GNF},\footnote{
This notion is sometimes just called GNF~\cite{BlumK99} or real-time form~\cite{ReghizziBM19}.
}
where
every right-hand side starts with a terminal symbol.
\begin{quote}
@{def GNF_hd}
\end{quote}

The procedure takes three steps of conversions:
first eliminate \<open>\<epsilon>\<close>-productions (@{const Eps_elim}),
then transform to a triangular form (@{const solve_tri}),
and finally obtain head GNF (@{const Expand_tri}).

The last two steps follow textbook algorithms~\cite{Harrison78,HopcroftU79} for deriving GNF,
except that
we do not require input in CNF
but only eliminate \<open>\<epsilon>\<close>-productions.
As a result we arrive at head GNF.

We say a grammar \<open>P\<close> is \concept{triangular on} a list \<open>[A\<^sub>1,...,A\<^sub>n]\<close> of nonterminals,
if \<open>A\<^sub>i \<rightarrow> A\<^sub>j\<alpha> \<in> P\<close> implies \<open>i > j\<close>.
Defined inductively, \<open>P\<close> is triangular on \<open>[]\<close>,
and on \<open>A#As\<close> if it is so on \<open>As\<close> and
there exist no \<open>A \<rightarrow> B\<alpha> \<in> P\<close> with \<open>B \<in> set As\<close>.

We inductively make a grammar which is triangular on \<open>As\<close> also
triangular on to \<open>A#As\<close>.
First, we repeatedly expand productions of form \<open>A \<rightarrow> B\<alpha>\<close> for all \<open>B \<in> set As\<close>
with respect to the \<open>B\<close>-productions in \<open>P\<close>,
using the following function:
\begin{quote}
@{fun[margin=70] Expand_hd_rec[Expand_hd_rec.simps(1) Expand_hd_rec_simp2]}\smallskip\\
@{def[margin=70] "Subst_hd"}
\end{quote}


Afterwards productions of form \<open>A \<rightarrow> Av\<close> remain to be solved.
Let \<open>V\<close> collect all such \<open>v\<close>,
and let \<open>U\<close> collect all \<open>u\<close> of productions \<open>A \<rightarrow> u\<close> that does not start with \<open>A\<close>.
Then the language of \<open>A\<close> is that of \<open>U \<union> UV\<^sup>+\<close>;
hence we introduce a fresh nonterminal \<open>A'\<close> whose language corresponds to \<open>V\<^sup>+\<close>,
and replace \<open>A \<rightarrow> Av\<close> productions by \<open>A \<rightarrow> UA'\<close>.

\begin{quote}
@{def Solve_lrec[Solve_lrec_def[unfolded Rm_lrec_def]]}
\end{quote}

\begin{quote}
@{def Rrec_of_lrec}
\end{quote}

The above formalization is almost the same as the textual description,
except that
we do not introduce extra productions if @{prop \<open>V = {}\<close>}.
This optimization is not explicit in \cite[Fig.\ 4.9]{HopcroftU79},
although their Example 4.10 performs this implicitly.

Recursively applying @{const Expand_hd_rec} and @{const Solve_lrec}
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
In particular, textbook arguments do not treat triangularity
with respect to nonterminals in \<open>As'\<close> explicitly,
which is however necessary for formally proving the termination of the next step.

From a triangular form,
repeatedly expanding head nonterminals \emph{in the right order} (@{const Expand_tri})
turns the grammar into head GNF.
Thus the function @{const GNF_hd}
first makes fresh copies \<open>As'\<close> of nonterminals in \<open>As\<close>,
applies @{const Solve_tri} and then @{const Expand_tri} in the reversed order of
\<open>As @ rev As'\<close> on which triangularity is ensured.
\begin{definition}
@{def GNF_hd_of}
\begin{quote}
@{fun Expand_tri[Expand_tri.simps(1) Expand_tri_simp2]}\\
\end{quote}
\end{definition}
Because the procedure processes nonterminals one by one,
we explicitly give a list of nonterminals as an argument to @{const GNF_hd_of}.
For brevity, we present the version @{const gnf_hd_of} which computes such a list by
taking the input grammar in the list representation.

\begin{theorem}
For any grammar \<open>P\<close> in list representation,
@{thm(concl) gnf_hd_gnf_hd_of[where ps = P]}.
For all @{thm(prem 1) lang_gnf_hd_of[where ps = P]}, @{thm(concl) lang_gnf_hd_of[where ps = P]}.
\end{theorem}

Finally, we turn head GNF into GNF by introducing nonterminals for terminals
that appear at non-head position of right-hand sides (\concept{bad terminals}).
We prove that any occurrence of a bad terminal \<open>a\<close> can be replaced by
fresh nonterminal $A_a$,
provided the grammar is extended with $A_a \to a$ for each $a$.
We also use the same function in the CNF translation.

\begin{theorem} @{thm gnf_gnf_of}\\
@{thm lang_gnf_of}
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
\begin{proof}[sketch]
The core insight is that expanding $A_{i}$ in $A_{i+1} \to A_i a \mid A_i b$
yields twice as many $A_{i+1}$-productions as $A_{i}$ productions.
\end{proof}

\section{\prestar}
\label{sec:prestar}

\subsection{Informal Introduction}

%Bouajjani \emph{et al.} \cite{BouajjaniEFMRWW00}
Esparza and Rossmanith \cite{EsparzaR97} realized that a device that Book and Otto \cite{BookO93}
had used to solve problems for string rewriting systems can also be applied to a number of
elementary CFG problems.
Let \<open>P :: ('n,'t) Prods\<close> and \<open>L :: ('n,'t) syms set\<close>.
Then @{term "pre_star P L"} is the set of predecessors of words in \<open>L\<close>
w.r.t.\ \<open>\<Rightarrow>*\<close>:%{prop "P \<turnstile> DUMMY \<Rightarrow>* DUMMY"}
\begin{quote}
@{thm pre_star_def}
\end{quote}
The two key insights are (if \<open>P\<close> finite):
 if \<open>L\<close> is regular, so is @{term \<open>pre_star P L\<close>}, and if \<open>L\<close> is given as an NFA \<open>M\<close>,
an NFA for @{term \<open>pre_star P L\<close>} can be computed from \<open>M\<close>.
This result has been discovered multiple times \cite{Buechi64,Caucal92}

As an example, consider the productivity problem of determining if @{prop "mbox(Lang P A) \<noteq> {}"}.
Let \<open>P\<close> be a grammar over a terminal alphabet \<open>\<Sigma>\<close>.
Build an automaton \<open>U\<close> that accepts exactly \<open>\<Sigma>\<^sup>*\<close>, but no words containing @{const Nt}s
(this requires only a single state).
Clearly @{prop "Lang P A \<noteq> {}"} iff there is a word \<open>w \<in> \<Sigma>\<^sup>*\<close> such that @{prop "P \<turnstile> mbox([Nt A]) \<Rightarrow>* w"}
iff @{term "[Nt A]"} \<open>\<in>\<close> @{term "pre_star P"} \<open>\<Sigma>\<^sup>*\<close> \<open>=: L\<close>. But because \<open>U\<close> accepts \<open>\<Sigma>\<^sup>*\<close>
we can compute an automaton for \<open>L\<close> from \<open>U\<close> (as claimed above) and we only need to check
if that automaton accepts @{term \<open>[Nt A]\<close>}.

The algorithm for computing @{const pre_star} on the level of an NFA \<open>M\<close>
extends \<open>M\<close> with new transitions as long as possible.
Given a production \<open>A \<rightarrow> \<alpha>\<close> in \<open>P\<close>, if \<open>M\<close> has a sequence of transitions from state \<open>p\<close>
to state \<open>p'\<close> labeled with \<open>\<alpha>\<close>, we add the transition \<open>(p, Nt A, p')\<close>.


\subsection{Executable Formalization}
%TODO reachable_from -> reachable

For the purpose of computing @{const pre_star}, we represent NFAs over some state type \<open>'s\<close> by
a \concept{labeled transition system} (usually denoted by \<open>T\<close>) of type \mbox{@{typ\<open>('s,'a) lts\<close>}} = \<^typ>\<open>('s \<times> ('n,'t)sym \<times> 's) set\<close>.
It is easy to define a function @{const steps_lts} \<open>::\<close>
\mbox{@{typ "('s,'a) lts"}} \<open>\<Rightarrow>\<close> @{typ "'a list \<Rightarrow> 's \<Rightarrow> 's set"}
such that @{term "steps_lts T \<alpha> p"} is the set of states reachable from \<open>p\<close> via \<open>\<alpha>\<close> using \<open>T\<close>.
An automaton \<open>M\<close> (of type \<^typ>\<open>('s,'a) auto\<close>) consists of some \<open>T\<close>, an initial state and a final state set.
If \<open>T\<close> is finite, we call \<open>M\<close> an NFA.
We also define @{term "Lang_auto M"}, the words accepted by \<open>M\<close>, and @{term "reachable_from T q"},
the states reachable from \<open>q\<close> via \<open>T\<close>.
Below, the label type \<^typ>\<open>'a\<close> will always be \mbox{@{typ\<open>('n,'t)sym\<close>}}.

Function @{const pre_lts} adds all possible new transitions to a set of transitions \<open>T\<close>
(over the state space \<open>Q\<close>) using the productions in \<open>P\<close> backwards once:
\begin{quote}
@{thm [break] pre_lts_def}% beta -> alpha?
\end{quote}

The closure of some \<open>T\<close> under @{const pre_lts} can be defined by repeated application like this:
\begin{quote}
@{thm [break] pre_star_lts_def[unfolded while_saturate_def]}
\end{quote}
using the predefined combinator @{const_typ while_option} \cite{Nipkow11}.
We do not dwell on its definition but it is executable because it obeys this recursion equation:
\begin{quote}
@{thm [break] while_option_unfold}
\end{quote}
In case the recursion does not terminate, the mathematical value is @{const None}.
Hence proving that the return value is always @{const Some} amounts to proving termination.

We proved correctness and termination of @{const pre_star_lts}.
Correctness says that the result of @{const pre_star_lts}
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
@{thm [break] pre_star_lts_terminates}
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

Previous formalizations of \prestar\ were based on and applied to pushdown systems
\cite{SchlichtkrullSST22,Pushdown_Systems-AFP} and networks \cite{LammichMW09}, not CFGs.


\section{Chomsky-Schützenberger}\label{sec:ChSch}
The Chomsky-Schützenberger Theorem \cite{ChomskyS} states that every CFL is the homomorphic image
of the intersection of a Dyck language and a regular language, where a Dyck language is a language
of properly bracketed words over some alphabet of opening and closing brackets,
e.g. the set containing 
\[  
     [_a  \qquad  ]_a  \qquad  [_b  \qquad  ]_b .
\]
Formally, if \<open>P\<close> is finite:
\begin{quote}
@{thm (concl) Chomsky_Schuetzenberger}
\end{quote}

It is sometimes called the Chomsky-Schützenberger Representation Theorem to distinguish it from the Chomsky-Schützenberger Enumeration Theorem \cite{ChomskyS} about the number of words of a given length generated by an unambiguous CFG. 

\subsection{Proof Intuition}

In everything that follows, we denote by $L$ the originally given CFL.
The proof will define a homomorphism @{term "\<h>"}, a Dyck language @{term "Dyck_lang \<Gamma>"}, and a regular language $R$, such that
\[
  @{prop "L = \<h> ` L'"}\quad \text{where}\ @{prop "L' = R \<inter> Dyck_lang \<Gamma>"}
\]
The strategy will be to impose enough structure on $L$, obtaining a language $L'$ such that the words
of $L'$ can be identified using only regular properties $R$ and the information that its words are
balanced words of brackets over @{term \<open>\<Gamma>\<close>}. We can then delete all this new structure again---using the homomorphism @{term \<open>\<h>\<close>}---to arrive at the original language $L$.
For this, the homomorphism will only need to act on a per letter basis---we will use it to replace or delete letters. This proof strategy follows closely the proof presented by Kozen \cite{Kozen}.

\subsection{Dyck Languages}\label{subsec:dyck}

Brackets labeled with elements of type \<open>'a\<close> are modeled as pairs:
\begin{quote}
@{typ "'a bracket"} = @{typ "bool \<times> 'a"}\\
@{abbrev "Open a"} \quad @{abbrev "Close a"}
\end{quote}
\concept{Balanced} (= correctly bracketed) words are described inductively:
\[
@{thm [mode=Rule] bal.intros(1)} \qquad
@{thm [mode=Rule] bal.intros(3)} \qquad
@{thm [mode=Rule] bal.intros(2)}
\]

The Dyck language over @{term \<open>\<Gamma>\<close>} is the set of balanced words, where the bracket labels come from @{term \<open>\<Gamma>\<close>}:

\[
  @{def Dyck_lang}.
\]

In the proof of the Chomsky-Sch\"utzenberger Theorem we needed the following lemma,
which we proved via a functional characterization (@{const bal_stk}) of balanced words that
uses a stack to remember opening brackets.
\begin{quote}
@{thm bal_Open_split}.
\end{quote}

Function @{const bal_tm} lifts \<^const>\<open>bal\<close> from @{typ \<open>'a bracket list\<close>}
to @{typ[source]\<open>('n,'a bracket)syms\<close>} by deleting all \<^const>\<open>Nt\<close>'s and stripping off all \<^const>\<open>Tm\<close>'s.
%    {thm bal_iff_bal_tm}.


\subsection{From \<open>L\<close> to \<open>L'\<close>}

The key idea is to encode \<open>P\<close>-parse trees for words in \<open>L\<close>
into words of $L'$ generated by \<open>P'\<close>. The definition of \<open>P'\<close>
(from \<open>P\<close>) is simplified by assuming that \<open>P\<close> is in Chomsky normal form.
This is the translation from \<open>P\<close> to \<open>P'\<close>:
\begin{align*}
   \pi &= A \rightarrow BC && \text{ becomes } & \pi' &= A \rightarrow [^1_\pi \, B \, ]^1_\pi \, [^2_\pi \, C \, ]^2_\pi \\
   \pi &= A \rightarrow a && \text{ becomes } & \pi' &= A \rightarrow [^1_\pi \, ]^1_\pi \, [^2_\pi \, ]^2_\pi.
\end{align*}
%
Note that in both cases the full production $\pi$ appears on the right-hand side as a bracket label.
We need two copies of these brackets to distinguish the two nonterminals \<open>B\<close> and \<open>C\<close>.
The two copies differ by an exponent (\<open>1\<close> or \<open>2\<close>). Formally, this is our label set \<open>\<Gamma>\<close>:
\[
@{prop \<open>\<Gamma> = P \<times> {1, 2::nat}\<close>}
%@ {thm "Chomsky_Schuetzenberger_locale.\<Gamma>_def"}
% does not work because outside the locale
\]
Note that the newly introduced brackets are all terminals.

%In Isabelle these definitions look more verbose:
%\begin{quote}
%{fun transform_prod}\\
%{fun transform_rhs}\\
%{abbrev "wrap1 A a"}\\
%{abbrev "wrap2 A B C"}
%\end{quote}


\subsection{Proving $@{prop \<open>L = \<h> ` L'\<close>}$}

%The homomorphism {term \<open>\<h>\<close>} collapses $[^1_\pi \, ]^1_\pi \, [^2_\pi \, ]^2_\pi$ to $a$ if $\pi$ is of the form $\pi = A \rightarrow a$, else it is collapsed to \<open>\<epsilon>\<close>. More precisely, $[^1_\pi$ is mapped to $a$, all the other brackets to \<open>\<epsilon>\<close>.
The homomorphism @{term \<open>\<h>\<close>} maps @{term "open_bracket1 (A,a)"} to @{term \<open>a\<close>}
and all other brackets to \<open>\<epsilon>\<close>. Thus it maps every application of a rule \<open>\<pi>' =\<close>
$[^1_\pi \, ]^1_\pi \, [^2_\pi \, ]^2_\pi$, where $\pi$ is of the form $\pi = A \rightarrow a$,
to an application of the original rule \<open>\<pi>\<close>. The justification for rules \<open>\<pi>\<close> of the form \<open>A \<rightarrow> BC\<close>
is more complicated. We need to lift \<open>\<h>\<close> to a generalized version that works on sentential forms,
where it is the identity on nonterminals. Because \<open>\<h>\<close> maps brackets coming from rules \<open>\<pi>\<close> of the form \<open>A \<rightarrow> BC\<close>
to \<open>\<epsilon>\<close>, every application of a rule \<open>\<pi>' =\<close>
$[^1_\pi \, A \, ]^1_\pi \, [^2_\pi \, B \, ]^2_\pi$ is mapped to an application of the original rule \<open>\<pi>\<close>.

The direction @{prop \<open>\<h> ` L' \<subseteq> L\<close>} went through as expected and follows the above argument.
For the other direction, we didn't succeed in proving it on the level of derivations alone.
We finally settled on a constructive transformation of $P$-parse trees to $P'$-parse trees.


\subsection{Formalizing the Regular Language}

To obtain @{prop "L = \<h> ` L'"} it now suffices to represent $L'$ as 
\[
@{prop "L' = (R \<inter> Dyck_lang \<Gamma>)"},
\]
where $R$ is some regular language.
The paper proof describes the regular language $R$ using 5 conditions,
which assert that after certain letters always/never another certain letter follows.
For example, the first property asserts that a bracket of the form $]^1_\pi$ is always immediately followed by the bracket $[^2_\pi$.
It also asserts that $]^1_\pi$ can never be the end of a word.

In Isabelle we realize this by first defining the predicate @{const P1'}
(that compares two neighbouring input elements) and then extending this to @{const P1}
via the @{const successively} predicate:
\begin{quote}
@{fun_input P1'}\smallskip\\
@{fun P1}   
\end{quote}
where @{term "successively Q"} \<open>[x\<^sub>0, x\<^sub>1, ...]\<close>
means @{text "Q x\<^sub>i x\<^bsub>i+1\<^esub>"} for all neighbours, if there are any.
To enforce that a word never ends on $]^1_\pi$, the last letter is treated separately.

The condition @{const P5} \<open>A u\<close> checks \<open>u\<close> is non-empty and that its first letter is of the form @{term \<open>[\<^sup>1\<^bsub>(A,DUMMY)\<^esub>\<close>}.
It is later used with the start symbol.
The intersection of all these conditions already almost define the regular language $R$:
\begin{quote}
@{term "Reg A"} = @{thm [break] (rhs) Reg_def}
\end{quote}
But @{term \<open>Reg S\<close>} is only regular if there are only finitely many different brackets, i.e.\ if the set of productions \<open>P\<close> is finite.
When we formally show the regularity, we will therefore only show the regularity of @{prop \<open>R \<equiv> (Reg S) \<inter> (brackets P)\<close>} for finite \<open>P\<close>
(with some start symbol \<open>S\<close>).
Here @{term \<open>brackets P\<close>} denotes the set of arbitrary words consisting of the brackets with labels in \<open>P\<close>.

We proved the \<open>\<subseteq>\<close> direction of @{prop "L = \<h> ` (R \<inter> Dyck_lang \<Gamma>)"} by proving that the conditions @{const P1} -- @{const P5} are preserved by each derivation step.

This of course required lifting the conditions @{const P1} -- @{const P5} to conditions @{const P1_sym} -- @{const P5_sym}
on sentential forms. Since sentential forms are more general we needed to strengthen the induction hypothesis
by including two more properties @{const P7_sym} and @{const P8_sym} that localize the possible positions of nonterminals.
%Originally we thought to also include another condition $P6$ which was later found superfluous and doesn't appear in the proof text anymore. 

The \<open>\<supseteq>\<close> direction went through as described by Kozen.
Here we needed to make use of the lemma proved using @{term \<open>bal_stk\<close>} that we mentioned in Sect.~\ref{subsec:dyck}.

\subsection{Proving Regularity}
Kozen handwaves the regularity of the \<open>\<^latex>\<open>\isaconst{\<close>P\<^sub>i\<^latex>\<open>}\<close>\<close>'s away to ``can be described by a regular expression''.
But actually writing down the correct expressions is a surprisingly hard task,
and furthermore proving the generated language equivalent to the---otherwise very practical---description via the \<open>\<^latex>\<open>\isaconst{\<close>P\<^sub>i\<^latex>\<open>}\<close>\<close>'s is a tedious task, since the regular expression contains multiple Kleene stars.

A much easier approach was to use a deterministic finite automaton \cite{Paulson15}.
The DFA would remember its last seen bracket in its state and the transition function makes implementing
the conditions and the pairwise checking straightforward.

We were able to use the same general automaton for @{const P2}, @{const P3} and @{const P4},
since we were able to give an automaton for @{term \<open>{u. successively Q u \<and> u \<in> brackets P}\<close>}
for an arbitrary pairwise condition \<open>Q\<close>.



\section{Parikh}\label{sec:Parikh}%FL

In a nutshell, Parikh's Theorem says that if we consider words not as lists but as multisets of
terminals, then every context-free language is regular. A simple consequence is that any CFL
over a single letter alphabet is regular.

We use the notation @{term "parikh_img L"} to refer to the \concept{Parikh image} of the language
\<open>L\<close>, i.e.\ the set of all words in \<open>L\<close> where words are multisets of terminals (instead of lists),
or in other words @{def parikh_img}, where @{const mset} converts lists to multisets.
Parikh's Theorem can then be formulated in the following way:

\begin{theorem}
For each context-free language \<open>L\<close> there exists a regular language \<open>L'\<close> such that
@{prop "parikh_img L = parikh_img L'"}.
\end{theorem}
We have followed the proof by Pilling~\cite{Pilling}.
The idea is to express a context-free grammar as a system of inequalities
such that the CFG's language is a minimal solution to the system.
By constructing a regular language which is minimal solution to the same system of inequalities,
it follows that both solutions have the same Parikh image.

\subsection{CFGs as Systems of Inequalities}
\label{sec:parikh_eq_sys}

As described in~\cite{Pilling}, each context-free grammar induces a system of inequalities such that
the CFG's language is a minimal solution to the system.
Let $X_0, X_1, \dots, X_r$ be the nonterminals that occur in the CFG. Then the system of
inequalities has the following form:
\begin{align*}
X_0 &\supseteq f_0(X_0, \dots, X_r)\\
&\vdots\\
X_r &\supseteq f_r(X_0, \dots, X_r).
\end{align*}
While setting up the system is straightforward and is not further explained in~\cite{Pilling},
doing this in Isabelle, and proving that the CFG's language is a minimal solution, requires some effort:
Since the functions $f_i$ imitate the right-hand sides of the grammar's productions,
we can restrict the functions to a limited set of operations, mainly concatenation and
union of languages. This leads to the type of \concept{regular language expressions}:
\begin{quote}
@{datatype [break,margin=90] rlexp}
\end{quote}
@{term "Var i"} refers to the variable $X_i$, @{term "Const L"} represents
the constant language \<open>L\<close> (which is primarily needed to denote terminal symbols in productions) and
\mbox{@{term "Star r"}} represents the Kleene star.

Given a regular language expression \<open>r :: 'a rlexp\<close> and a valuation \<open>v ::\<close> @{typ "nat \<Rightarrow> 'a list set"},
i.e.\ a function which instantiates each variable with a concrete language,
@{term "eval r v"} describes the language obtained by evaluating \<open>r\<close> under \<open>v\<close>.
Furthermore, @{term "subst s r"} denotes the regular language expression which we obtain
by substituting each occurrence of the variable \<open>i\<close> in \<open>r\<close> by the regular language expression \<open>s i\<close>;
and @{term "vars r"} describes the set of variables occurring in \<open>r\<close>.
A regular language expression \<open>r\<close> which contains as constants only regular languages is called
\concept{regularity preserving}, denoted @{term "reg_eval r"} in Isabelle.
Such regular language expressions are of particular interest since they are guaranteed to
evaluate to a regular language if all variables occurring in \<open>r\<close> are instantiated with a regular language.

Thanks to the type \<open>rlexp\<close>, a system of inequalities \<open>sys\<close> can be represented as a list of
regular language expressions, i.e.\ \<open>sys :: 'a rlexp list\<close>,
where the \<open>i\<close>-th element of the list (@{term "sys ! i"})
corresponds to the right-hand side of the \<open>i\<close>-th inequality.
Solutions to \<open>sys\<close> are defined in a straightforward way, as valuations \<open>v\<close> satisfying 
\begin{quote}
@{thm solves_ineq_sys_def}
\end{quote}
Furthermore, we write @{term "min_sol_ineq_sys sys v"} if the valuation \<open>v\<close> is a minimal solution
to \<open>sys\<close>.

A CFG can be translated into a system of inequalities as follows:
For a single symbol (terminal symbol or nonterminal), we perform a simple pattern matching
\begin{quote}
@{term "(case s of Tm a \<Rightarrow> Const {[a]} | Nt A \<Rightarrow> Var (\<gamma>' A))"}
\end{quote}
where $\gamma$ is a fixed bijection from natural numbers to nonterminals and $\gamma'$ is its inverse
(introducing this bijection is necessary as the CFG's nonterminals can be of arbitrary type).
By concatenation and union, the definition can be lifted to a regular language expression for $f_i$,
and doing so for every nonterminal yields a system of inequalities.
It remains to prove that the CFG's language is a minimal solution to this system:
We do not show this directly but use as an intermediate step
the alternative characterization of a CFG's language as a least fixpoint (@{const lfp})
\begin{quote}
@{def Lang_lfp}
\end{quote}
where @{term "subst_lang P L"} is the function substituting every occurrence of a nonterminal
\<open>A\<close> on the right-hand sides of all productions in \<open>P\<close> by the language \<open>L A\<close>.
The proof proceeds in multiple steps, by first considering only a single inequality and then
lifting this to a system of inequalities. We do not want to go into detail at this point
but only state the final result, namely that
\begin{quote}
@{term "sol \<equiv> \<lambda>i. if i < card (Nts P) then Lang_lfp P (\<gamma> i) else \<emptyset>"}
\end{quote}
is a minimal solution to
some system of inequalities induced by the CFG:
\begin{lemma}
@{prop [break] "\<exists>sys. (\<forall>eq \<in> set sys. reg_eval eq) \<and> (\<forall>eq \<in> set sys. \<forall>x \<in> vars eq. x < length sys)
\<and> min_sol_ineq_sys sys sol"}
\end{lemma}
We have also proved that all inequalities of the system are regularity preserving which is
an important prerequisite for the rest of the proof.


\subsection{Systems of Inequalities with Parikh Image}

The system of inequalities from the previous section is too strict in the
sense that it differentiates between solutions with identical Parikh image.
Thus, we adjust the system
by adding the Parikh image operator on both sides such that the \<open>i\<close>-th inequality looks as follows:
\[\Psi X_i \supseteq \Psi (f_i(X_0, \dots, X_r))\]
In Isabelle, we do not adjust the representation of the system directly but only the definition
of its solutions, i.e.\ we use @{prop "solves_ineq_sys_comm sys v"} instead of
@{prop "solves_ineq_sys sys v"} where the former differs from the latter by applying the
Parikh image operator on both sides of $\subseteq$.

Additionally, we need the notion of partial solutions: These are functions of the type
@{typ "nat \<Rightarrow> 'a rlexp"}, i.e.\ they map each inequality to a regular language expression representing
the solution for that inequality; using regular language expressions at this point allows us
to specify solutions depending on other variables.
Formally, \<open>sols\<close> is a partial, minimal solution to the first \<open>n\<close> inequalities of \<open>sys\<close> (i.e.\ \<^term>\<open>take n sys\<close>)
if it satisfies the following definition:
\begin{quote}
@{thm [break] partial_min_sol_ineq_sys_def}
\end{quote}
The definition consists of four parts:
The first part states that \<open>sols\<close> is a solution, the second part ensures that \<open>sols\<close>
does not specify solutions to other than the first \<open>n\<close> inequalities, the third part formalizes
that \<open>sols\<close> only depends on variables greater than \<open>n-1\<close>, i.e.\ only on inequalities which have
not yet been solved, and the last part expresses that \<open>sols\<close> is minimal.


\subsection{Pilling's Proof}

We call a regular language expression \<open>f\<close> \concept{bipartite}
with respect to the variable \<open>x\<close>
if it is the union of two regularity preserving regular language expressions of which only one
contains \<open>x\<close>:
\begin{quote}
@{thm [break] bipart_rlexp_def}
\end{quote}
Bipartite regular language expressions correspond to the normal form introduced in Equation~(3)
of~\cite{Pilling}. To each regularity preserving regular language expression \<open>f\<close> exists a bipartite
regular language expression with identical Parikh image; this can be proved by induction on \<open>f\<close>:
\begin{quote}
@{prop [break] "reg_eval f \<Longrightarrow>
    \<exists>f'. bipart_rlexp x f' \<and> vars f' = vars f \<union> {x} \<and>
         (\<forall>v. \<Psi> (eval f v) = \<Psi> (eval f' v))"}
\end{quote}

Following Pilling's proof~\cite{Pilling}, we first construct a regular, minimal solution to a system
consisting of a single inequality: The above lemma allows us to assume that the right-hand side of
the inequality is bipartite.
Thus, let \<open>eq\<close> be the bipartite inequality, consisting of the two parts \<open>p\<close> and \<open>q\<close>;
then @{term "sol \<equiv> Concat (Star (subst (Var(x := p)) q)) p"} is regularity preserving and it
is a minimal, partial solution to \<open>eq\<close>.
The proof relies on the following property of regular language expressions:
\begin{quote}
@{thm [break] rlexp_homogeneous_aux}
\end{quote}
where \<open>Y\<close> and \<open>Z\<close> are languages and @{term star} and \<open>@@\<close> denote the Kleene star and the
concatenation of languages, respectively.
In contrast to our proof, Pilling claims equality but under an additional assumption which is
more difficult to formalize.

It remains to generalize this result to whole systems of regularity preserving inequalities.
For this purpose, we show by induction on \<open>n\<close> that the first \<open>n\<close> inequalities have a minimal,
partial solution which is regularity preserving:
\begin{lemma} \label{lem:parikh_ind_step}~\\
@{thm [break] exists_minimal_reg_sol_sys_aux[of _ n]}
\end{lemma}
The centerpiece of the induction step works as follows: Given \<open>sols :: nat \<Rightarrow>\<close> \mbox{\<open>'a rlexp\<close>}, a partial,
minimal solution to the first \<open>n\<close> inequalities, we can determine a partial, minimal solution \<open>n_sol\<close>
to the \<open>n\<close>-th inequality, as described above in the single-inequality case. This allows us to
substitute all occurrences of the variable \<open>n\<close> with \<open>sol_n\<close>:
\begin{quote}
@{term "sols' \<equiv> \<lambda>i. subst (Var (n := sol_n)) (sols i)"}
\end{quote}
Now, \<open>sols'\<close> contains one variable less,
it is still regularity preserving (since both \<open>sols\<close> and \<open>sol_n\<close> are regularity preserving)
and it is a partial, minimal solution to the first \<open>n+1\<close> inequalities of the system.
Notably, our proof does not rely on the Lemma presented in~\cite{Pilling};
although Pilling suggests to apply this lemma in the induction step, we were not able to do so.

When instantiating Lemma~\ref{lem:parikh_ind_step} with \<open>n = |sys|\<close>,
the partial solution \<open>sols\<close> contains no variables anymore,
so it is in fact a valuation.
This shows that the system of inequalities has a regular, minimal solution.
After proving that each minimal solution to the system without Parikh images
(i.e.\ of the system considered in Section~\ref{sec:parikh_eq_sys}) is also a minimal
solution to the system with Parikh images (i.e. of the system considered in this and the previous section),
it follows that the CFG's language and the regular solution have the same
Parikh image since both are minimal solutions to the same system.


\section{Conclusion}

We have presented a unified formalization of the basic theory of context-free
languages as it is taught even in advanced introductory courses on formal languages.
The total size of the formalizations discussed in the paper runs to 19~KLOC.

The huge area of formal language theory (e.g.\ \cite{hfl/1997-1}) offers amazing possibilities for further formalizations.
Most pressing seems to be a unified treatment of parsing.
\<close>
(*<*)
end
(*>*)
