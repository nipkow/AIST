(*<*)
theory Paper
  imports "LR0_Base.LR0_Parser"
begin

lemma t': True
  by blast

declare [[names_short, show_question_marks = false]]

context Extended_Cfg 
begin

(*>*)

section \<open>Basic Definitions\<close>
subsection \<open>Extended Grammars\<close>

(*<*)
definition "P' \<equiv> Prods G'"
(*>*)

text \<open>

\begin{definition}[Reduced grammars]
A CFG is a \concept{reduced grammar} if its productions contain only useful symbols, or equivalently,
no unreachable or unproductive symbols.%:\\@{thm reduced_def} 
\end{definition}

Let \<open>G\<close> be a context-free grammar with productions \<open>P\<close>, start symbol \<open>S\<close>, set of nonterminals \<open>N\<close> and 
terminals \<open>T\<close>. In order to simplify 
the process of parsing and operate on more well-behaved grammars, we will assume certain properties: \\

\begin{itemize}
\item \<open>P\<close> is finite.
\item \<open>L(G) \<noteq> \<emptyset>\<close>
\item \<open>G\<close> is reduced.
\end{itemize}

We then extend \<open>G\<close> by a fresh start symbol \<open>S'\<close> with a single production \mbox{\<open>S' \<rightarrow> S\<close>}. 
The resulting grammar, which we conventionally call \<open>G'\<close>, is the \concept{extended grammar}, or the 
\concept{extension}, of \<open>G\<close> with the set of productions \<open>P' := P \<union> {S' \<rightarrow> S}\<close>. We analogously refer 
to this set as the \concept{extension} of \<open>P\<close> or the \concept{extended set of productions} of \<open>G\<close>. \\

\begin{lemma}\label{G' no S' imp G}
If \<open>\<alpha>\<close>~\derive[G']~\<open>\<beta>\<close> and \<open>S' \<notin> \<alpha>\<close>, then \<open>\<alpha>\<close>~\derive[G]~\<open>\<beta>\<close>.
\begin{proof}
Since \<open>\<alpha>\<close>~\derive[G']~\<open>\<beta>\<close>, there exist \<open>\<gamma> \<in> (N \<union> T)\<^sup>*\<close>, \<open>w \<in> T\<^sup>*\<close> and \mbox{\<open>X \<rightarrow> \<delta> \<in> P'\<close>} such that 
\<open>\<alpha> = \<gamma>Xw\<close> and \<open>\<beta> = \<gamma>\<delta>w\<close>. Since \<open>S' \<notin> \<alpha>\<close>, \<open>X \<rightarrow> \<delta> \<noteq> S' \<rightarrow> S\<close>, which implies \<open>X \<rightarrow> \<delta> \<in> P\<close>. 
The derivation then also exists in \<open>G\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{G' imp G}
If a derivation \<open>S'\<close>~\deriven[G']{n+1}~\<open>\<alpha>\<close> exists,
there also exists a derivation \<open>S\<close>~\deriven[G]{n}~\<open>\<alpha>\<close>.
\begin{proof} 
The proof is by trivial induction on n using Lemma~\ref{G' no S' imp G} and the fact that
for any \<open>\<beta>\<close>, \<open>S\<close>~\derives[G]~\<open>\<beta>\<close> implies \<open>S' \<notin> \<beta>\<close>.
\end{proof}
\end{lemma}

\begin{theorem}
\<open>L(G') = L(G)\<close>
\begin{proof} 
Let \<open>w \<in> L(G')\<close>. Then there exists a derivation of the form \\
\<open>S'\<close>~\derive[G']~\<open>S\<close> \derives \<open>w\<close>. Therefore, there exists an \<open>n \<in> \<nat>\<close> such that 
\<open>S'\<close>~\deriven[G']{n+1}~\<open>w\<close>. By Lemma~\ref{G' imp G}, this implies the existence of a 
derivation \<open>S\<close>~\deriven[G]{n}~\<open>w\<close>, and thus \mbox{\<open>w \<in> L(G)\<close>}. \\
Conversely, let \<open>w \<in> L(G)\<close>. Then there exists a derivation \<open>S\<close>~\derives~\<open>w\<close> under \<open>P\<close>. Since 
\<open>S'\<close>~\derive[G]~\<open>S\<close> and \mbox{\<open>P \<subseteq> P'\<close>}, \<open>S'\<close>~\derives[G']~\<open>w\<close> also holds by 
transitivity. Therefore, \<open>w \<in> L(G')\<close>. This completes the proof. 
\end{proof}
\end{theorem}

\<close>

subsection \<open>Context-Free Items\<close>



subsection \<open>Generalized Pushdown Automata\<close>

section \<open>Context-Free Items and the Item Pushdown Automaton\<close>
section \<open>The Characteristic Finite Automaton and the Canonical LR(0) Automaton\<close>
section \<open>The Canonical LR(0) Parser\<close>

(*<*)
end
end
(*>*)
