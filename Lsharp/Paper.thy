(*<*)
theory Paper
imports
  Lsharp
begin
declare [[show_question_marks=false]]
declare [[names_short=true]]
(*>*)

text\<open>
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
text (in Mealy) \<open>
\begin{quote}
@{thm [mode=Rule] algo_step.intros}
\end{quote}
\<close>
(*<*)
end
(*>*)