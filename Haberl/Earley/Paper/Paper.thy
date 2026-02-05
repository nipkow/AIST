(*<*)
theory Paper
imports
  "Earley.EarleyWorklist"
  Sugar
begin
declare [[show_question_marks=false]]
declare [[names_short=true]]

(* to get rid of annoying eta-contraction *)
notation (output) id ("_")
(*>*)

text\<open>

\section{Introduction}

@{term "xs ! n"} is the n-th element

@{prop "Px & Q"} \<open>1 ... n\<close>

\cite{BouajjaniEFMRWW00}

\section{Isabelle Notation} \label{sec:isabelle}
\<close>

text (in Earley_Gw_eps)\<open>
\section{Inductive Definition of Earley's State Sets} \label{sec:Earley}
\begin{quote}
@{def Predict_L}\\

@{fun minus_LWL}
\end{quote}
\begin{lemma}
@{thm bins_L_eq_\<S>}
\end{lemma}
\<close>
(*<*)
end
(*>*)