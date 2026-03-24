(*<*)
theory Thesis
imports
  "Earley.EarleyWorklist"
  Sugar
begin
declare [[show_question_marks=false]]
declare [[names_short=true]]

(* to get rid of annoying eta-contraction *)
notation (output) id ("_")

context Earley_Gw begin
definition X :: "nat \<Rightarrow> ('n,'a) item set"
  ("(\<S>\<^bsub>_\<^esub>)" [800] 1000) where
"(\<S>\<^bsub>i\<^esub>) = ({x. (x,i) \<in> Earley})"

lemma Earley_eq_\<S>1: "(x,i) \<in> Earley \<longleftrightarrow> x \<in> \<S>\<^bsub>i\<^esub>"
by(simp add: X_def)

lemma Earley_predict: assumes "x \<in> (\<S>\<^bsub>i\<^esub>)" and "next_sym_Nt x A" and "p \<in> P" and "lhs p = A" shows "Item p 0 i \<in> \<S>\<^bsub>i\<^esub>"
  using Earley.Predict[of x i "Item p 0 i"] assms by (cases p) (auto simp add: X_def Predict_def)

lemma Earley_complete: assumes "x \<in> (\<S>\<^bsub>i\<^esub>)" "is_complete x" "from x = f" "y \<in> \<S>\<^bsub>f\<^esub>" "next_sym_Nt y (lhs (prod x))" shows "mv_dot y \<in> \<S>\<^bsub>i\<^esub>"
  using Earley.Complete[of x i] assms by (auto simp add: X_def)

lemma Earley_init: assumes "p \<in> P" "lhs p = S" shows "Item p 0 0 \<in> \<S>\<^bsub>0\<^esub>"
  using Earley.Init[of "Item p 0 0"] assms by (cases p) (auto simp add: X_def Init_def)

lemma accepted_def2: shows "accepted = (\<exists>x \<in> (id (\<S>\<^bsub>length w\<^esub>)). is_final (id x))" 
  unfolding accepted_def by (auto simp add: \<S>_def X_def)

end
(*P definition outside of Earley_Gw for certain uses*)
definition P where " P = {(1 :: nat, ([] :: (nat, 'b) sym list))}"

notation (latex) X ("(\<S>\<^bsub>\<^latex>\<open>\\isaconst{\<close>_\<^latex>\<open>}\<close>\<^esub>)" [0] 0)
notation (latex) \<S> ("(\<S>\<^bsub>\<^latex>\<open>\\isaconst{\<close>_\<^latex>\<open>}\<close>\<^esub>)" [0] 0)
(*>*)

(*type_synonym ('n, 't) sentential = "('n,'t) sym list"*)

text\<open>

\chapter{Introduction} \label{chap:Intro}
This is a test sentence that has been changed incredibly much
This is another test
\<close>

text\<open>
\chapter{Background} \label{chap:Background}

\section{Context Free Grammars}

Languages are sets of words, which are strings made up of terminal symbols. The whole set of terminal symbols is called the alphabet $\Sigma$.
One way to define what words are in a Language are context free grammars (CFGs) which introduce new non-terminal symbols and productions 
that formalize how a string of non-terminal and terminal symbols can be changed to derive words step by step, starting from a single non-terminal.
A production expresses one such possible step, where you replace one non-terminal symbol by a string of non-terminal and terminal symbols.
The Language of a CFG is then the set of strings containing only terminal symbols that can be reached from the starting non-terminal, following the modifications described by the productions.
Strings of non-terminals and terminals are called sententials and strings of only terminal symbols are called sentences.

Formally in Isabelle strings are represented by lists and so to be able to represent sententials non-terminals and terminals are grouped together into the wrapper symbol 
datatype @{type sym} which can represent either a terminal or non-terminal symbol.
\begin{quote}
  @{datatype sym}
\end{quote}
Productions \<open>(A, \<alpha>)\<close> are a pair of a non-terminal \<open>A\<close> and a sentential \<open>\<alpha>\<close>, where the non-terminal is called the left-hand side (lhs) and the sentential is called the right-hand side (rhs) of the production.
In text we will write productions like this \<open>(A \<rightarrow> \<alpha>)\<close>.
A set of productions $P$ then defines the so called derivation relation @{term "P \<turnstile> u \<Rightarrow> v"}, which is formally defined as follows:
\begin{quote}
@{const_typ derive}\\
@{thm derive.simps[of P u v, rename_abs A \<beta> x y]}
\end{quote} %TODO think about type synonyms
This represents one modification step as described informally above. Context free grammars are made up of a set of productions $P$ 
and a non-terminal as a starting symbol, commonly named $S$. The Language of a CFG is then defined in terms of the transitive closure of the derivation relation @{term "P \<turnstile> u \<Rightarrow>* v"}. 
Specifically by which sentences can be reached from the starting non-terminal @{term "[Nt S]"}.
\begin{quote}
  @{datatype Cfg}\\[2.5mm]
  @{def Lang}\\[2.5mm]
  @{const_typ LangS}\\[1mm]
  @{abbrev LangS}
\end{quote}

A CFG implicitly defines the sets of terminals and non-terminals by which appear in its productions.
\begin{quote}
  @{def Nts_syms}\\[1.5mm]
  @{def Nts}\\[2.5mm]
  @{def Tms_syms}\\[1.5mm]
  @{def Tms}
\end{quote}

There exist multiple interesting computational questions concerning languages. One very natural question is, given a word $w$, is it in the Language given by a CFG?
This is called recognition and a natural continuation is asking about the derivation of such a word if it is in the Language, which is called parsing.

%This relation takes a set of Productions and two sentential forms and returns true if and only if 
%there exists a production @{text "(Nt A, \<beta>)"}, @{text "Nt A"} appears in the first sentential form and is replaced by $\beta$ in the second sentential form.

\section{Parse Trees}

\begin{itemize}
  \item CFG in Isabelle
  \item Parse trees in Isabelle
\end{itemize}
\<close>

text\<open>
\chapter{Earley Recognizer Formalization} \label{chap:Earley_formal}
In this thesis we formalize a recognizer first proposed by Earley \cite{Earley1970}. We fix for the following chapter a word $w$ and a CFG $C$ which induces the Language $L$.
Earley's recognizer builds sets of items for each index of $w$, where an item in one of these sets represents that a sub-string of $w$ has been recognized.
These items consist of a production, and two natural numbers that are called the dot and from.\<close>

text_raw \<open>\begin{quote}\isamarkuptrue\<close>
datatype ('n,'a) item = Item (prod: "('n,'a) prod") (dot : nat) ("from" : nat)
text_raw \<open>\end{quote}\<close>
(*datatype item*)
text (in Earley_Gw)\<open>
We will write an item \<open>Item p d f\<close> like this \<open>(A \<rightarrow> \<alpha>\<Zspot>\<beta>, f)\<close>, where the production is \<open>(A, \<alpha>\<beta>)\<close> and \<open>|\<alpha>| = d\<close>.
The idea behind the recognizer is that an item @{term "Item p k l"} in set $\mathcal{S}_i$ symbolizes that we have recognized the sub-string of $w$ 
starting at index $l$ and ending at index $i$ and that it can be derived from the partial right-hand side of $p$ that is left of the dot at position $k$.
We call this property soundness.
\begin{definition}\label{soundness}
  @{term "Item p k l \<in> \<S>\<^sub>i \<Longrightarrow> P \<turnstile> slice 0 k (rhs p) \<Rightarrow>* slice l i w"}. %could use sound_item_def
\end{definition}
@{term "slice i k s"} returns the sub-string starting at index i and ending at index k-1. It is equivalent to @{term "take k (drop i s)"}.

For better readability we define some helper functions:
\begin{quote}
  @{def is_complete}\\[2.5mm]
  @{def next_symbol}\\[2.5mm]
  @{abbrev next_sym_Nt}\\[2.5mm]
  @{def mv_dot} 
\end{quote}
@{const is_complete} checks whether the dot is at the end of the production, @{const next_symbol} returns an option of the symbol after the dot, 
@{const next_sym_Nt} checks if the next symbol is a specific non-terminal and @{const mv_dot} moves the dot over the next symbol.\\
We also define a predicate to check if an item is well-formed in the context of the recognizer algorithm, so what items could appear in a set $\mathcal{S}_k$. We check that the production is part of the grammar, 
that the dot is a valid index into the right-hand side of the production, that the from value is less than or equal to $k$ and that $k$ is less than or equal to the length of $w$.
\begin{quote}
  @{def wf_item}
\end{quote}

Earley then goes on to define three operations for the recognizer algorithm which generate items for these sets in an inductive manner. These are called \emph{predict}, \emph{complete} and\emph{scan}.
If we have an item in set $\mathcal{S}_i$ with its dot in front of a non-terminal \<open>A\<close> we predict. So we start recognizing a new a sub-string starting at index $i$ of w from the non-terminal $A$.
\begin{quote}
{\sc Predict}: $\inferrule{@{thm (prem 1) Earley_predict} \\
  @{thm (prem 2) Earley_predict}\\
  @{thm (prem 3) Earley_predict}\\
  @{thm (prem 4) Earley_predict}}{@{thm (concl) Earley_predict}}$
\end{quote}
%This means we add @{term "{Item p 0 i | p. p \<in> P \<and> lhs p = A}"} items to set $\mathcal{S}_i$. 
Completion occurs when we have fully recognized an item \<open>B \<rightarrow> \<alpha>\<Zspot>, f\<close>, meaning its dot is at the end of the right-hand side of the production.
In this case we have recognized a sub-string of $w$ starting at \<open>f\<close>. This recognition started with the non-terminal on the productions left-hand side \<open>B\<close>.
So we can extend the recognition of sub-strings up to \<open>f\<close> (@{term "P \<turnstile> u \<Rightarrow>* slice k f w"}) with this sub-string recognition as follows @{term "P \<turnstile> u @ [Nt B] \<Rightarrow>* slice k i w"}.
In terms of items this means we are taking an item recognizing a sub-string up to \<open>f\<close> from set \<open>\<S>\<^sub>f\<close> and can extend its recognition if the symbol after the dot is the non-terminal \<open>B\<close>.\\
\begin{quote}
{\sc Complete}: $\inferrule{@{thm (prem 1) Earley_complete} \\
  @{thm (prem 2) Earley_complete}\\
  @{thm (prem 3) Earley_complete}\\\\
  @{thm (prem 4) Earley_complete}\\
  @{thm (prem 5) Earley_complete}}{@{thm (concl) Earley_complete}}$
\end{quote}
%Formally: We add @{term "{mv_dot it | it. it \<in> \<S>\<^sub>k \<and> next_symbol it = Some (Nt B)}"} to \<open>\<S>\<^sub>i\<close>.
The last operation scan occurs when the next symbol of an item is a terminal. In this case we can advance recognition of the sub-string if the next symbol in $w$ is said terminal.
In this case we add these items to the next set $\mathcal{S}_{i+1}$, since the length of the recognized sub-string of $w$ has increased by one.
\begin{quote}
{\sc Scan}: $\inferrule{@{thm (prem 1) Earley.Scan[simplified Earley_eq_\<S>1]}\\
  @{thm (prem 2) Earley.Scan[simplified Earley_eq_\<S>1]}\\
  @{thm (prem 3) Earley.Scan[simplified Earley_eq_\<S>1]}}
  {@{thm (concl) Earley.Scan[simplified Earley_eq_\<S>1]}}$
\end{quote}
%Formally: @{term "{mv_dot it | it. it \<in> \<S>\<^sub>i \<and> next_symbol it = Some (w ! i)}"} 
Lastly we need a starting point for this inductive definition, which is given by the prediction operation on the starting symbol.
\begin{quote}
  {\sc Init}: $\inferrule{@{thm (prem 1) Earley_init}\\
  {@{thm (prem 2) Earley_init}}}
  {@{thm (concl) Earley_init}}$
\end{quote}
%Formally: @{term "{Item p 0 0 | p. p \<in> P \<and> lhs p = S}"}

From these inductive definitions we can derive the following functions producing sets resulting from the operations on a single item.
\begin{quote}
  @{thm Predict_def[of it i, rename_abs _ p]}\\
  @{const Complete} @{text " \<S>\<^sub>k B = "} @{term "{mv_dot it | it. it \<in> \<S>\<^sub>k \<and> next_symbol it = Some (Nt B)}"}\\ % might want to change this to the original definition
  @{thm Scan_def[of \<S>\<^sub>i i, rename_abs _ it]}\\
  @{thm Init_def[rename_abs _ p]}
\end{quote}
\<close>


text \<open>
We also define a top level predicate for $w$ called recognized, which returns true if we find a complete item with the start-symbol as its left-hand side in set $\mathcal{S}_{|w|}$.
By soundness this means that @{term "P \<turnstile> [Nt S] \<Rightarrow>* w"} holds.
\begin{definition}
  @{thm (concl) accepted_def2}\\[1ex] %TODO fix eta expansion somehow
  where @{thm is_final_def}
\end{definition}
\<close>

text \<open>
We give an example to better understand and visualize the algorithm:
Given a CFG with productions \<open>P = {A \<rightarrow> AB, A \<rightarrow> BA, A \<rightarrow> a, B \<rightarrow> b}\<close> and starting non-terminal \<open>A\<close> we get the following sets for the word "bab".\\
\begin{table}[h]
\begin{center}
\begin{tabularx}{12cm}{|X c|X c|X c|X c|}
\hline
  \multicolumn{2}{|c|}{$\mathcal{S}_0$} & \multicolumn{2}{|c|}{$\mathcal{S}_1$}  & \multicolumn{2}{|c|}{$\mathcal{S}_2$}  & \multicolumn{2}{|c|}{$\mathcal{S}_3$} \\
\hline
  \<open>A \<rightarrow> \<Zspot>AB\<close> & 0 & \<open>B \<rightarrow> b\<Zspot>\<close>  & 0 & \<open>A \<rightarrow> a\<Zspot>\<close>  & 1 & \<open>B \<rightarrow> b\<Zspot>\<close>  & 2 \\
  \<open>A \<rightarrow> \<Zspot>BA\<close> & 0 & \<open>A \<rightarrow> B\<Zspot>A\<close> & 0 & \<open>A \<rightarrow> BA\<Zspot>\<close> & 0 & \<open>A \<rightarrow> AB\<Zspot>\<close> & 1 \\
  \<open>A \<rightarrow> \<Zspot>a\<close>  & 0 & \<open>A \<rightarrow> \<Zspot>AB\<close> & 1 & \<open>A \<rightarrow> A\<Zspot>B\<close> & 1 & \<open>A \<rightarrow> AB\<Zspot>\<close> & 0 \\
  \<open>B \<rightarrow> \<Zspot>b\<close>  & 0 & \<open>A \<rightarrow> \<Zspot>BA\<close> & 1 & \<open>A \<rightarrow> A\<Zspot>B\<close> & 0 & \<open>A \<rightarrow> BA\<Zspot>\<close> & 0 \\
            &   & \<open>A \<rightarrow> \<Zspot>a\<close>  & 1 & \<open>B \<rightarrow> \<Zspot>b\<close>  & 2 & \<open>A \<rightarrow> A\<Zspot>B\<close> & 1 \\
            &   & \<open>B \<rightarrow> \<Zspot>b\<close>  & 1 &            &   & \<open>A \<rightarrow> A\<Zspot>B\<close> & 0 \\ 
            &   &            &   &           &   & \<open>B \<rightarrow> \<Zspot>b\<close> & 3 \\
\hline
\end{tabularx}
\end{center}
\caption{Example of the sets constructed by the Earley parser}
\end{table}
TODO maybe make different visualization showing what different operations add
\<close>



text (in Earley_Gw)\<open>
\section{Inductive definition}
Towards a formal proof of this recognizer, we define one inductive Earley-set, which will be the union of all $\mathcal{S}_i$ where $i < |w|$. 
To differentiate which set the items are in we will save pairs of Earley-items and a natural number indicating which set they are from.
It is constructed inductively by the three operations and the initial set discussed previously.
\begin{quote}
  @{const_typ Earley}
\end{quote}

For correctness we need to prove the two directions of soundness and completeness. Which entails that if the recognizer accepts a word, 
it is in the language and the opposite direction, that if a word is in the language then the recognizer accepts it.
Soundness is quite easy to prove for this definition, we only need to prove soundness of every item in this set, 
which can be done by proving that all operations preserve soundness, and the initial set is sound. From these individual proofs overall soundness follows:
\begin{theorem}
  @{thm accpted_sound}
\end{theorem}
To prove completeness we show that if there is an item in the Earley-set and the rest of the items right-hand side after the dot can derive a sub-string of w following the sub-sting already derived by the item, 
then the complete item will also be in the set.
\begin{lemma}
  @{thm Earley_complete_induction}
\end{lemma}
This is proven using total induction on the length of the derivation and an induction on the length of the rest of the right-hand side of the item.
%We sketch this proof. The base case where the remainder of the right-hand side is zero is trivial, as the item is complete and therefore the completed item is in the set.
%If the item is incomplete, we differentiate two cases based on if the next symbol is a terminal or a non-terminal
%could go into a bit more detail if necessary
From this the full completeness follows rather easily, as the initial set contains all possible incomplete items after one step of derivation. 
Therefore if the entire word is derivable one of these items will be complete in the final Earley-set $\mathcal{S}_{|w|}$ and thus the word is accepted by the recognizer.
\begin{theorem}
  @{thm Earley_complete}
\end{theorem}
\<close>
(*Towards executability:
- First we change to an iterative computation of the Earley sets using an inductive closure algorithm (bins & Close)
- We constrain the input to epsilon-free grammars to achieve a one-pass closure (Close1)
- We make a nondeterministic worklist algorithm for the one pass closure  (Close2)*)
text (in Earley_Gw)\<open>
\section{Towards executability}
While this theoretical Earley recognizer is well suited for proves it lends itself badly for execution, because of the inductive definition. 
Instead the iterative set computation suggested by Earley is better suited.
Looking at the four operations of the Earley algorithm we see that only \emph{predict} and \emph{complete} add items to the current set, 
while \emph{init} is the staring set and \emph{scan} adds item to the next set, resulting in the starting set of the next set.
Every operation also only depends on items in sets with lower or equal index, letting us compute the sets in order.
So we can split the algorithm into two steps first compute the starting set for set $\mathcal{S}_i$ using \emph{init} or \emph{scan} 
and then compute the closure of this set under \emph{predict} and \emph{complete}. This can then be repeated until we have computed all sets.

Going forward we will call item sets \emph{bins}, to which we extend the well formedness predicate. %TODO include maybe
The algorithm will follow this general form:
\begin{quote}
  @{fun bins}
\end{quote}
It computes a list of bins as described before, using @{const Close} to compute the closure. 
This way we can refine the closure algorithm step by step, while the underlying structure of the algorithm does not change.
From now on \<open>Bs\<close> will always refer to the list of bins computed previously.

To prove that this new algorithm computes the same sets as the fully inductive definition we first use an inductive set closure. It takes a starting set \<open>B\<close> - either a result of \emph{init} or \emph{scan} - 
and the previously computed list of bins \<open>Bs\<close> and returns the closure \<open>C\<close> under \emph{predict} and \emph{complete}.
\begin{quote}
  @{const_typ Close}\\
  @{const Close} \<open>Bs\<close> \<open>B\<close> =\\
  @{const Init} : @{thm Close.Init}\\
  @{const Predict} : @{thm Close.Predict}\\
  @{const Complete} : @{thm (prem 1) Close.Complete} \<open>\<Longrightarrow>\<close> @{thm (prem 2) Close.Complete} \<open>\<Longrightarrow>\<close> @{thm (prem 3) Close.Complete}\\
   \mbox{\qquad \<open>\<Longrightarrow>\<close> @{thm (prem 4) Close.Complete} \<open>\<Longrightarrow>\<close> @{thm (prem 5) Close.Complete}}\\
   \mbox{\qquad \<open>\<Longrightarrow>\<close> @{thm (concl) Close.Complete}}
\end{quote}

We then prove equivalence of the @{const bins} method using @{const Close} to the original Earley implementation.
\begin{theorem}
  @{thm bins_eq_\<S>}
\end{theorem}
Here the function \<open>\<S>\<close> collects all items of the fully inductive Earley-set that are in the i-th set.
\<close>

text \<open>
We are working towards a one pass closure algorithm, where we only need to consider every element once.
This is possible if the items added by \emph{predict} and \emph{complete}, do not depend on the items in the current set closure we are computing.
This is the case for the predict operation, which only depends on the set of productions.
For the complete operation it is only the case, if the complete items from-value is the index of a previous bin.
This is equivalent to the CFG not having any productions of length zero. 
The handling of the complete operation for length zero productions it not straight-forward, so we require the grammar to be epsilon free.
\begin{definition}
  @{const_typ Eps_free}\\[1ex]
  @{thm Eps_free_def[of P, rename_abs lhs rhs]}
\end{definition}
This way we simplify the algorithm. We also give some options on how to deal with not epsilon free grammars in \ref{sec:epsilon}.
So we create another closure under this assumption @{const Close1} which works the same as @{const Close}, but the complete operation is simplified, as we assume the grammar to be epsilon free:
\begin{quote}
  @{const Complete} : @{thm (prem 1) Close1.Complete} \<open>\<Longrightarrow>\<close> @{thm (prem 2) Close1.Complete} \<open>\<Longrightarrow>\<close> @{thm (prem 3) Close1.Complete}\\[1ex]
  \mbox{\qquad \<open>\<Longrightarrow>\<close> @{thm (prem 4) Close1.Complete} \<open>\<Longrightarrow>\<close> @{thm (concl) Close1.Complete}}
\end{quote}
We prove equivalence to @{const Close} under the assumption of epsilon free-ness.
\begin{lemma}
  @{const Eps_free} \<open>P\<close> \<open>\<Longrightarrow>\<close> @{thm (prem 1) Close1_eq_Close} \<open>\<Longrightarrow>\<close> @{thm (prem 2) Close1_eq_Close}\\[1ex]
  \mbox{\qquad\<open>\<Longrightarrow>\<close> @{thm (concl) Close1_eq_Close}}
\end{lemma}
Unless specified otherwise we will assume that the grammar is epsilon free from here on out.
The next step towards executability is replacing the inductive closures with a one pass worklist algorithm.\<close> (*TODO IMPORTANT lemmas from Earley_Gw_eps do not have epsilon free as assumption*)


(*%One tricky detail is the handling of productions deriving the empty word. The \emph{predict} operation only depends on the set of productions, which does not change
%and the \emph{complete} operation depends on the set, where its recognition started. For non-empty productions this is a bin that has already been fully constructed.
%In the case of an empty production we can get the item \<open>(A \<rightarrow> \<Zspot>, i)\<close>, which points into the current bin $i$. 
%So the set of items resulting of its \emph{completion} is not fully determined during the algorithm for closure.
%This means we have to deal with this special case differently. Some options are presented in \ref{sec:epsilon}.
%To simplify things we will focus on the case where the grammar is epsilon free, meaning it does not contain any productions that derive the empty word.\<close>*)


text (in Earley_Gw)\<open>
\section{Workset closure}
We keep track of a pair of sets, the workset \<open>B\<close> and the accumulator \<open>C\<close>.
The workset comprises items in the closure which have yet to be considered, while the accumulator keeps track of all previously considered items in the closure.
So at any step \<open>B \<union> C\<close> are all items we know to be in the closure and it should hold that \<open>B \<inter> C = \<emptyset>\<close>.
One step of this worklist algorithm then looks like this:
\begin{itemize}
  \item choose an item from \<open>B\<close> to be considered \<open>b \<in> B\<close>
  \item compute the set of items \<open>D\<close> added by \<open>b\<close> under \emph{predict} or \emph{complete}
  \item move \<open>b\<close> from \<open>B\<close> to \<open>C\<close> and add \<open>D\<close> to \<open>B\<close>, while making sure that \mbox{\<open>B \<inter> C = \<emptyset>\<close>} by the end
\end{itemize} 
The last step we do as follows @{term "((B \<union> D) - (C \<union> {b}), (C \<union> {b}))"}.
To formalize this approach we define a step relation that relates any two such set pairs that differ by one step.
\begin{definition}
  @{const_typ [break] Close2}\\
  Predict : @{thm (prem 1) Close2.Predict} \<open>\<Longrightarrow>\<close> @{thm (prem 2) Close2.Predict}\\[1ex]
  \mbox{\qquad\<open>\<Longrightarrow>\<close> @{thm (concl) Close2.Predict}}\\[1ex]
  Complete : @{thm (prem 1) Close2.Complete} \<open>\<Longrightarrow>\<close> @{thm (prem 2) Close2.Complete}\\ \smallskip
  \mbox{\qquad\<open>\<Longrightarrow>\<close> @{thm (concl) Close2.Complete}}\\
\end{definition}
The closure is then given by the set \<open>C\<close> when repeated steps result in \<open>B = \<emptyset>\<close>. This will always be the case, as the set of valid Earley items is finite.
More on this in \ref{chap:space}.
Formally this means we are looking for the accumulator \<open>C\<close> of a set pair \<open>(\<emptyset>, C)\<close> that is reachable from \<open>(B, \<emptyset>)\<close> under the step realtion.
But since this formalisation is non-deterministic in the order that items are chosen from the workset 
we require the Hilbert choice operator for the formalisation to get a random but distinct set \<open>C\<close> if it exists. In reality this set is unique and always exists. %possibly refer to a lemma about that
\begin{definition}
  @{def close2}
\end{definition}
We again prove equivalence of @{const close2} to @{const Close1}.
\begin{lemma}
  @{thm close2_eq_Close1}
\end{lemma}\<close>

text \<open>
For this proof we need two other lemmas. First that @{const close2} terminates and second that the result is equal to the set obtained by @{const Close1}.
We will first focus on the set equality. The direction that @{const close2} is a subset of @{const Close1} is simple, 
by the fact that the result after one step is always a subset of the final result of @{const Close1}.
The other direction is a bit trickier. We do a proof by induction on the items in @{const Close1} and have to check three cases.
First the initial items in \<open>B\<close> are also in the result of @{const close2}, which is easily apparent as any item in \<open>B\<close> will at some point be moved to \<open>C\<close>.
Second for the induction step we have to prove that under the assumption that an item @{term "x \<in> Close1 Bs B"} 
is also in \<open>C\<close> of @{const close2}, all items obtained by the operations \emph{predict} or \emph{complete} on \<open>x\<close> also end up in \<open>C\<close>.
This proof boils down to the observation that if \<open>x\<close> ends up in \<open>C\<close> there must exist a step where it is picked from \<open>B\<close> and moved to \<open>C\<close>.
In this step all of the items added to @{const Close1} by \<open>x\<close> are also added to \<open>B\<close> in the @{const Close2} step and therefore end up in \<open>C\<close> eventually.

For termination we define a well founded potential function which decreases with every step taken.
It is a lexicographic ordering primarily on the number of well-formed items not in the worklist or accumulator, 
which decreases whenever an item is added through \emph{predict} or \emph{complete}, 
and secondarily on the size of the worklist, which decreases, if no new items are added, as one item is always moved to the accumulator.

After proving that the step relation always decreases this potential, we can prove termination of the algorithm and finish the equivalence proof of @{const close2} and @{const Close1}.

\<close>

(*text \<open>
\begin{quote}
  @{fun step_fun}
\end{quote}

- create a closure under complete and predict
- scan transitions between sets after full closure
- a natural way to implement this is as a WorkList algorithm
\<close>*)

text\<open>
\section{Epsilon treatment} \label{sec:epsilon}

\begin{itemize}
  \item do epsilon treatment outside of this Algorithm (is there an isabelle implementation of epsilon removal (constructing L - {$\epsilon$}))
  \item check which Nts could produce epsilon and change predict to also do epsilon completion for these Nts (would require changing underlying algorithm and doing a lot of proving)
  \item TODO check literature for different stratagies
\end{itemize}

\<close>

text\<open>
%\begin{itemize}
  %\item inductive definition lends itself well to first correctness proof
  %\item towards executability we do iterative computation of sets, as earley suggested
  %\item example
  %\item WorkList algorithm for the closure of one set under predict and complete
%\end{itemize}

%\begin{itemize}
%  \item Earley-items
%  \item Inductive Definition
%  \item Soundness
%  \item Completeness
%  \item section about empty word treatment possibilities (modifying Predict)
%\end{itemize}
\<close>

text\<open>
\chapter{Executable List based Version} \label{chap:List_version}

We can now go on to implement a list based version.
We first start off by implementing the four Earley operations using lists:
\begin{quote}
  @{def Init_L}\\
  @{def Predict_L}\\
  @{def Complete_L}\\
  @{def Scan_L}
\end{quote}
We then go on to prove equivalence to the set based version defined earlier.
\begin{quote}
  %TODO
\end{quote}

The closure is implemented using @{const "while_option"}.

\chapter{Efficient Itemlist Datastructure for running time guarantees}
Our aim is to prove the running time analysis given by Earley \cite{Earley1970}. For this we require linear runtime of the @{const step_fun},
 which is not given using standard list based set-functions, as the set difference operation takes $O(n^2)$ time when using lists.
To fix this we follow Earley's idea to implement a $O(1)$ item lookup and insertion, which is enough to design an $O(n)$ set difference.
The main idea is to group items in a set by their \emph{from} value. For every value of \emph{from} there are only a constant number of items.
And the \emph{from} are also in the range $[0, i]$ for closure of $\mathcal{S}_i$. This would allow for the storage of all items in an array of item lists where the list at index $i$ has all items for \emph{from} value $i$.
Assuming constant access time for an array we can then implement @{const isin} and @{const insert} in $O(1)$.
\begin{itemize}
  \item WorkList Datatype + why requirement for cubic runtime
  \item WorkList insert intracasies (set bahavior using upsize for ease of theoretical analysis, but isnt used in actual algorithm)
  \item List based functions
  \item correctness by equivalence to inductive set based WorkListAlgorithm
  \item WorkList Algorithm with help of while\_option
\end{itemize}

\chapter{Runingtime Analysis} \label{chap:Runingtime_1}
\begin{itemize}
  \item analysis with WorkList T\_nth parameter (assumed to be constatnt for array)
  \item WorkList insert requires WorkList map\_length bound, which has to be carried through proofs
  \item runtime of list functions
  \item parametized runingtime (cubic if T\_nth is constant)
\end{itemize}

\chapter{Space Analysis} \label{chap:space}

\chapter{Expansion to Parse Trees} \label{chap:Parse_trees}
\begin{itemize}
  \item set version which does not require only one tree per Earley item
  \item parse items and well formedness characterisation
  \item list version for executability
  \item in many ways similar proof to first version
\end{itemize}


\chapter{Runingtime Analysis of Expanded Algorithm} \label{chap:Runingtime_2}

\begin{itemize}
  \item same O runingtime as version without (different prefactors)
\end{itemize}
\<close>



(*------------------------------------------------------------------------------------------------*)

text (in Earley_Gw_eps)\<open>
\chapter{Try out examples}


@{term "xs ! n"} is the n-th element

@{prop "Px & Q"} \<open>1 ... n\<close>

\begin{lemma}
  @{thm bins_L_eq_\<S>}
\end{lemma}
"\<close>

(*text (in Earley_Gw_eps)\<open>
\begin{quote}
@{def Predict_L}\\

@{fun minus_LWL}
\end{quote}
\begin{center}
@{thm bins_L_eq_\<S>}
\end{center}
\<close>*)
(*<*)
end
(*>*)