(*<*)
theory Paper
imports Greibach_Normal_Form.Greibach_Normal_Form Sugar
begin
(*>*)
text \<open>
\section{Introduction}

The formalization is unified in the sense that some of the topics that were 
previously formalized independently (and in different provers) are now
unified in a single formalization.
%rebase LL1 parser on CFG!

Of course only textbook+, no parsing (separate).

\subsection{Related Work}

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

\begin{quote}
@{datatype sym}
\end{quote}

Our theory is primarily based on sets of productions rather than grammars:
the terminals and nonterminals are part of the type and the start symbol is irrelevant most of the time.

@{prop "P \<turnstile> u \<Rightarrow> w"} and @{prop "P \<turnstile> u \<Rightarrow>* w"}

\subsection{Chomsky Normal Form}
\subsection{Pushdown Automata}
\subsection{Pumping Lemma}
\subsection{Automata}

2DFA AFA?

\section{Pre*}

\section{Greibach}

\section{Chomsky-Sch\"utzenberger}

\section{Parikh}
\<close>
(*<*)
end
(*>*)