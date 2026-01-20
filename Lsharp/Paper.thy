(*<*)
theory Paper
imports
  Lsharp
  "HOL-Library.LaTeXsugar"
begin
declare [[show_question_marks=false]]
declare [[names_short=true]]

notation process_output_query ("add'_io")

notation apart ("(2_ \<turnstile> _ \<sharp> _)" [50,0,50] 50)

lemma (in Lsharp_rel) invar_def2: "invar (S,F,T) =
    (mbox0(finite S \<and> finite F \<and> S \<inter> F = {} \<and>
    (\<forall> e \<in> S. orun T e \<noteq> None)) \<and>
    sapart (S,F,T) \<and>
    (\<forall> i. orun T i \<noteq> None \<longrightarrow> orun T i = Some (output_query M i)) \<and>
    F = frontier (S,F,T) \<and>
    [] \<in> S \<and> (\<forall> s \<in> S. s = [] \<or> (\<exists> s2 \<in> S. \<exists> i. s2 @ [i] = s)))"
  unfolding mbox0_def invar_def by presburger
(*>*)

text\<open>
% TODO: relate our functions to those by V.?

\subsection{Isabelle Notation} \label{sec:isabelle}

Isabelle is based on a fragment of higher-order logic. It supports core
concepts commonly found in functional programming languages.

The notation \<open>t :: \<tau>\<close> means that term \<open>t\<close> has type
\<open>\<tau>\<close>. Basic types include @{typ bool} and @{typ nat}, while type variables are written @{typ 'a}, @{typ 'b} etc.
Functions @{const fst} and @{const snd} return the first and second components of a pair,
Most type constructors are written postfix, such as @{typ "'a set"} and  @{typ "'a list"}, and the function
space arrow is \<open>\<Rightarrow>\<close>.
The image of function \<open>f\<close> over set \<open>M\<close> is denoted by \<^term>\<open>f ` M\<close>.

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

\section{Mealy Machines}

\<close>
text (in Lsharp_rel) \<open>
\section{$L^\#$}

\begin{quote}
@{datatype otree}
\end{quote}
Observation tree is separate data type rather than a Mealy machine.
Get tree structure for free but need to duplicate some functionality.
Better: conversion from \<open>otree\<close> to \<open>mealy\<close>? But currently not possible
because \<open>mealy\<close> is total. State = input sequence (for getting there).

Function @{term "orun ot is"} yields the output list of ``running'' \<open>ot\<close> on \<open>is\<close>,
i.e.\ traversing \<open>ot\<close> along \<open>is\<close> and emitting the output.

Function @{term "add_io ot is os"} extends \<open>ot\<close> such that \<open>is\<close> is mapped to \<open>os\<close>.

@{prop "apart T s\<^sub>1 s\<^sub>2"} means that \<open>T\<close> cannot tell \<open>s\<^sub>1\<close> and \<open>s\<^sub>2\<close> apart
(with some \<open>is\<close> that produces different outputs when running \<open>T\<close> from  \<open>s\<^sub>1\<close> and \<open>s\<^sub>2\<close>).

\begin{quote}
@{thm [mode=Rule] algo_step.intros(1)}\medskip\\
@{thm [mode=Rule] algo_step.intros(2)}\medskip\\
@{thm [mode=Rule] (sub) algo_step.intros(3)}\medskip\\
@{thm [mode=Rule] (sub) algo_step.intros(4)}
\end{quote}
\begin{quote}
@{thm [break] (sub) invar_def2[unfolded sapart.simps]}
\end{quote}

\<close>
(*<*)
end
(*>*)