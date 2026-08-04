(*<*)
theory Paper
  imports 
    "LR0_Base.LR0_Parser"
    "HOL-Library.LaTeXsugar"
begin

declare [[names_short, show_question_marks = false]]

no_notation (latex) Cons (\<open>_ \<cdot>/ _\<close> [66,65] 65)

syntax (latex output)
  "_take" :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_|\<^bsub>_\<^esub>" [1000,0] 1000)

translations 
  "_take xs n" <= "CONST take n xs"

notation (latex output) drop (\<open>\<^bsub>_\<^esub>|_\<close>)

abbreviation initial_item :: "'n \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow>  \<cdot> _ ]") where
  "[A \<rightarrow> \<cdot> \<alpha> ] \<equiv>  [A \<rightarrow> [] \<cdot> \<alpha>]"
abbreviation complete_item :: "'n \<Rightarrow> ('n,'t) syms \<Rightarrow> ('n,'t) item" ("[_ \<rightarrow> _ \<cdot> ]") where
  "[A \<rightarrow> \<alpha> \<cdot> ]  \<equiv>  [A \<rightarrow> \<alpha> \<cdot> []]"

notation (latex output) It (\<open>\<^latex>\<open>\ensuremath{\mathrm{It}_{\<close>_\<^latex>\<open>}}\<close>\<close>)


(*>*)

section \<open>Introduction\<close>
subsection \<open>\<open>LR(k)\<close> Parsing\<close>
subsection \<open>The Isabelle Theorem Prover\<close>
subsection \<open>Isabelle Notation\<close>
subsubsection \<open>General Notation\<close>

text \<open>A term \<open>t\<close> of type \<open>\<tau>\<close> is notated as \<open>t :: \<tau>\<close>, with type variables @{typ 'a}, @{typ 'b},
@{typ 'c}, etc. Tuple types are notated using \<open>\<times>\<close>: for \<open>x\<^sub>0 :: 'a\<^sub>0, x\<^sub>1 :: 'a\<^sub>1,\<dots>, x\<^sub>n :: 'a\<^sub>n\<close>, we write
\<open>(x\<^sub>0,x\<^sub>1,\<dots>,x\<^sub>n) :: 'a\<^sub>0 \<times> 'a\<^sub>1 \<times> \<dots> \<times> 'a\<^sub>n\<close>.
 Type constructors are usually written postfix, as one can see in types such as
@{typ "'a set"}, and in cases of multiple types \<open>'a\<^sub>0, 'a\<^sub>1,\<dots>,'a\<^sub>n\<close>, they are written as 
\mbox{\<open>('a\<^sub>0,'a\<^sub>1,\<dots>,'a\<^sub>n)\<close>}. One of the most common types in this formalization, @{typ "('n, 't) sym"}, 
is an example for this.\\
The keyword \isakeyword{datatype} is used to declare algebraic data types, which can be seen in 
@{typ "'a list"}:

@{datatype list}

Furthermore, lists are concatenated with the operator \<open>@\<close>, @{const rev} reverses a list, @{const set}
converts a list to a set, @{term "xs!n"} returns the \<open>n\<close>-th element of the list \<open>xs\<close> (with 
0-indexing), @{term "take n xs"} is the prefix of length \<open>n\<close> of \<open>xs\<close>, and @{term "drop n xs"} is the 
suffix of \<open>xs\<close> starting at index \<open>n\<close>.\<close>

subsubsection \<open>Context-Free Grammars\<close>

text \<open>Nipkow et al.\<^cite>\<open>Nipkow\<close> introduce type @{typ "('n, 't) sym"} for context-free grammar 
\concept{symbols} as a tagged union consisting of nonterminals (@{const Nt}) and terminals (@{const Tm}) 
of type @{typ 'n} and @{typ 't} respectively:

@{datatype sym}

Besides defining this type for symbols, they also define the following abbreviations:
\begin{quote}
\begin{tabular}{ll}
Lists of symbols & \<open>('n,'t) syms = ('n, 't) sym list\<close>\\
Productions & \<open>('n,'t) prod = 'n \<times> ('n,'t) syms\<close>\\
Sets of productions & \<open>('n,'t) Prods = ('n,'t) prod set\<close>
\end{tabular}
\end{quote}

Lastly, Nipkow et al. also define the datatype for context-free grammars:
\isakeyword{datatype} \<open>('n, 't) Cfg = Cfg (('n,'t) Prods) 'n\<close> 
% antiquotation @{datatype Cfg} unfolds type synonyms Prods and prod

@{term "Cfg P S"} denotes a context-free grammar with production set \<open>P\<close> and start symbol \<open>S\<close>. If 
@{term "G = Cfg P S"}, @{term "Prods G"} refers to \<open>P\<close>, and analogously, @{term "Start G"} refers to 
\<open>S\<close>.\\
A derivation step from \<open>\<phi>\<close> to \<open>\<psi>\<close> under production set \<open>P\<close> is notated as \mbox{@{term \<open>P \<turnstile> \<phi> \<Rightarrow> \<psi>\<close>}}.
More formally, for any nonterminal \<open>A\<close>, and symbols \<open>\<beta>\<close>, \<open>\<alpha>\<close> and \<open>\<gamma>\<close> holds:
\begin{quote} 
@{thm derive.intros[of A \<beta> P \<alpha> \<gamma>]}
\end{quote}

Moreover, we denote the reflexive transitive closure of derivations by \mbox{@{term \<open>P \<turnstile> \<phi> \<Rightarrow>* \<psi>\<close>}}, 
and derivations of length \<open>n\<close> by @{term \<open>P \<turnstile> \<phi> \<Rightarrow>(n) \<psi>\<close>}. Rightmost derivations are notated analogously, 
with \<open>\<Rightarrow>r\<close>, \<open>\<Rightarrow>r*\<close> and \<open>\<Rightarrow>r(n)\<close> respectively.

Lastly, Nipkow et al. define the language of a nonterminal w.r.t a set of 
productions:
\begin{quote}
@{thm Lang_def}
\end{quote}
And based on this, the language of a grammar:
\begin{quote}
\<open>LangS G = Lang (Prods G) (Start G)\<close>
\end{quote}
 
Besides type variables @{typ 'n} for nonterminals and @{typ 't} for terminals, we use the following 
variable conventions: for brevity, we refer to \<open>('n, 't) sym\<close> and \<open>('n, 't) syms\<close> simply as @{type sym}
and @{type syms} respectively; \<open>A, B, C :: 'n\<close>; \<open>a, b, c :: 't\<close>; \<open>u, v, w :: 't list\<close>; and finally
\<open>\<alpha>, \<beta>, \<gamma> :: ('n, 't) syms\<close>.

For further definitions and notation, we defer to the AFP entry by Nipkow et al~\<^cite>\<open>Nipkow\<close>.
\<close>

section \<open>Previous Work\<close>

section \<open>Basic Definitions\<close>
subsection \<open>Extended Grammars\<close>



text \<open>In general, context-free grammars (CFGs) can contain problematic nonterminals which can be 
removed from the grammar without altering the language. Working with grammars that lack such 
nonterminals is ideal, since having them increases computational complexity and makes the grammar 
less well-behaved.

\begin{example}
Let \<open>G\<close> be a CFG with productions:
\begin{center}
\begin{tabular}{cc}
\<open>Start G \<rightarrow> A | AB\<close> & \<open>A \<rightarrow> aA | a\<close>\\
\<open>C \<rightarrow> aacc | BCD\<close> & \<open>D \<rightarrow> BC | D\<close>
\end{tabular}
\end{center}

Each nonterminal except for \<open>Start G\<close> and \<open>A\<close> carries problems with it:
\begin{itemize}
\item There are no productions where \<open>B\<close> is on the left-hand side. This means that if \<open>Start G\<close> 
reaches a sentential form \<open>\<alpha>\<close> such that \<open>Nt B \<in> set \<alpha>\<close>, no word will be derived from \<open>\<alpha>\<close>. 
\item \<open>Start G\<close> cannot reach \<open>C\<close>, meaning no productions containing \<open>C\<close>, or reachable only 
through \<open>C\<close> (e.g. reaching \<open>D\<close> using production \mbox{\<open>C \<rightarrow> BCD\<close>}), can be used to derive words in \<open>LangS G\<close>.
\item \<open>D\<close>, as opposed to \<open>B\<close>, does show up on the LHS of certain productions, but none of these productions
can lead to a word: \<open>D \<rightarrow> BC\<close> contains \<open>B\<close>, which cannot derive a \<open>'t list\<close>, and \<open>D \<rightarrow> D\<close> has no effect.
Furthermore, similarly to \<open>C\<close>, \<open>D\<close> cannot be reached by \<open>Start G\<close>.
\end{itemize}
\end{example}

Nipkow et al.\<^cite>\<open>Nipkow\<close> define \concept{useful} nonterminals w.r.t. a set of productions and a start 
symbol:
\begin{quote}
@{abbrev productives}\\
@{thm useful_def}
\end{quote}

For a CFG \<open>G\<close>, \<open>A :: 'n\<close> is \concept{reachable} if there exists a \<open>\<beta> :: syms\<close> such that 
\mbox{\<open>A \<in> set \<beta>\<close>} and @{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<beta>\<close>}. Otherwise, it is \concept{unreachable}.
Similarly, it is \concept{productive} if @{prop \<open>productives (Prods G) [Nt A]\<close>} holds, and 
\concept{unproductive} otherwise. A useful nonterminal is therefore a nonterminal that is both 
reachable and productive. 

Nipkow et al. have proved that removing all unreachable and unproductive nonterminals preserves the
language:
\begin{quote}
@{thm restrict_Nts_def}\\
@{thm Lang_restrict_useful}
\end{quote}\<close>

(*<*)
context Extended_Cfg 
begin
(*>*)

text\<open>Based on these definitions, and thanks to the fact that we can construct a CFG with only useful
symbols equivalent to an arbitrary CFG, we can use these well-behaved grammars as the foundation
of our automata in future sections, which we will call \concept{reduced grammars}:

\begin{quote}
@{thm reduced_def}
\end{quote}

Let \<open>G\<close> be a fixed CFG whose start symbol is \<open>S\<close>. We assume the following properties:

\begin{itemize}
\item @{prop \<open>finite (Prods G)\<close>}
\item @{prop \<open>LangS G \<noteq> {}\<close>}
\item @{prop \<open>reduced G\<close>}
\end{itemize}

We extend \<open>G\<close> by a fresh start symbol \<open>S'\<close> with a single production \mbox{$S' \to S$}. 
The resulting grammar, which we define to be \<open>G'\<close>, is the \concept{extended grammar}, or the 
\concept{extension}, of $G$. We analogously refer to the set of productions of $G'$, 
as the extension of \<open>Prods G\<close> or the \concept{extended set of productions} of $G$.
Formally:
\begin{quote}
@{thm S'_def}\\
@{thm G'_def}
\end{quote}

We now prove that extending a grammar preserves both language and reduction.\<close>

(*<*)
end
(*>*)

text\<open>\begin{lemma}\label{S_deriven_Suc_imp_all_nts_in_Nts}
Let \<open>G\<close> be an arbitrary CFG. If \mbox{@{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc n) \<alpha>\<close>}} and 
@{prop \<open>A \<in> Nts_syms \<alpha>\<close>}, then @{prop \<open>A \<in> Nts (Prods G)\<close>}.
\begin{proof}
We do a proof by induction on \<open>n\<close> for arbitrary \<open>\<alpha>\<close>. In the base case, the derivation is a 
single step @{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow> \<alpha>\<close>}, meaning \<open>(Start G, \<alpha>) \<in> Prods G\<close>. Together with 
the fact that \<open>A \<in> Nts_syms \<alpha>\<close>, this implies @{prop \<open>A \<in> Nts (Prods G)\<close>}.\\
For the inductive case, we must prove the statement holds for \<open>\<alpha>\<close> assuming 
@{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc (Suc n)) \<alpha>\<close>} for some \<open>n\<close> and @{prop \<open>A \<in> Nts_syms \<alpha>\<close>}. 
This implies there is a second-to-last step of the form:\\
\<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc n) \<gamma> @ [Nt B] @ \<delta> \<Rightarrow> \<gamma> @ \<beta> @ \<delta> = \<alpha>\<close> with \<open>(B, \<beta>) \<in> Prods G\<close>\\
We now make a case distinction on whether \<open>A \<in> Nts_syms \<beta>\<close> holds.\\
If \<open>A \<in> Nts_syms \<beta>\<close>, then \<open>A \<in> Nts (Prods G)\<close> by the fact that \<open>(B, \<beta>) \<in> Prods G\<close> directly.\\
If \<open>A \<notin> Nts_syms \<beta>\<close>, this together with \<open>A \<in> Nts_syms \<alpha>\<close> implies \<open>A \<in> Nts_syms (\<gamma> @ [Nt B] @ \<delta>)\<close>. 
By the induction hypothesis, this implies \<open>A \<in> Nts (Prods G)\<close>, and the proof is thus complete.
\end{proof}
\end{lemma}\<close>

(*<*)
context Extended_Cfg 
begin
(*>*)

text\<open>\begin{lemma}\label{G'_derive_imp_G_derive_if_no_S'}
@{thm G'_derive_imp_G_derive_if_no_S'}
\begin{proof}
Since @{prop \<open>Prods G' \<turnstile> \<alpha> \<Rightarrow> \<beta>\<close>}, there exist \<open>\<gamma>, \<zeta> :: syms\<close> and @{prop \<open>(X, \<delta>) \<in> Prods G'\<close>} such 
that @{prop \<open>\<alpha> = \<gamma> @ Nt X # \<zeta>\<close>} and @{prop \<open>\<beta> = \<gamma> @ \<delta> @ \<zeta>\<close>}. Furthermore, @{prop \<open>Nt S' \<notin> set \<alpha>\<close>} 
implies @{prop \<open>(X, \<delta>) \<noteq> (S', [Nt S])\<close>}, which itself implies @{prop \<open>(X, \<delta>) \<in> Prods G\<close>}.
The derivation then also exists under \<open>Prods G\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{G'_deriven_Suc_imp_G_deriven}
@{thm G'_deriven_Suc_imp_G_deriven}
\begin{proof} 
The proof is by trivial induction on \<open>n\<close> using Lemma~\ref{S_deriven_Suc_imp_all_nts_in_Nts} and 
Lemma~\ref{G'_derive_imp_G_derive_if_no_S'} in conjunction with the fact that 
@{prop \<open>S' \<notin> Nts (Prods G)\<close>}.
\end{proof}
\end{lemma}

\begin{theorem}\label{Lang_preserved}[Preservation of language]
@{thm Lang_preserved}
\begin{proof} 
Let @{prop \<open>w \<in> LangS G'\<close>}. Then there exists a derivation of the form
\begin{quote}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow> [Nt S] \<Rightarrow>* map Tm w\<close>
\end{quote}
Therefore, there exists an \<open>n :: nat\<close> such that 
\begin{quote}
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) map Tm w\<close>}.
\end{quote}
By Lemma~\ref{G'_deriven_Suc_imp_G_deriven}, this implies the existence of a derivation\\
@{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>(n) map Tm w\<close>}, and thus @{prop \<open>w \<in> LangS G\<close>}. \\
Conversely, let @{prop \<open>w \<in> LangS G\<close>}. Then there exists a derivation\\
@{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>* map Tm w\<close>}. Since @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow> [Nt S]\<close>} and 
@{prop \<open>Prods G \<subseteq> Prods G'\<close>}, @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>* map Tm w\<close>} also holds by 
transitivity and the monotonicity of \<open>\<Rightarrow>*\<close>, as proven by Nipkow et al.:

\begin{quote}
@{thm derives_mono}
\end{quote}

Therefore, @{prop \<open>w \<in> LangS G'\<close>}. This completes the proof.
\end{proof}
\end{theorem}

\begin{theorem}[Preservation of reduction]
If \<open>G\<close> is reduced and @{prop \<open>LangS G \<noteq> {}\<close>}, \<open>G'\<close> is reduced.
\begin{proof}
Since \<open>G\<close> is reduced, all nonterminals in \<open>Prods G\<close> are useful, and the fact that @{prop \<open>LangS G \<noteq> {}\<close>}
implies that there exist \<open>\<alpha> :: syms\<close> and \<open>w \<in> LangS G\<close> such that  
\begin{quote}
\<open>Prods G \<turnstile> [Nt S] \<Rightarrow> \<alpha> \<Rightarrow>* map Tm w\<close>
\end{quote}
This implies that \<open>S \<in> Nts (Prods G)\<close>. Since \<open>Prods G \<subseteq> Prods G'\<close>, this
means that all nonterminals in \<open>Nts (Prods G)\<close> are useful in \<open>Prods G'\<close>. Therefore, to show that 
\<open>G'\<close> is reduced, it suffices to show that \<open>S'\<close> is useful in \<open>Prods G'\<close>, i.e., reachable and productive. 
Reachability is trivial by the reflexivity of \<open>\<Rightarrow>*\<close>. To show that it is productive, we need to show 
that there exists a \<open>w :: 't list\<close> such that @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>* map Tm w\<close>}, which is 
equivalent to showing there exists some \<open>w \<in> LangS G'\<close>. This follows directly from our assumption 
that @{prop \<open>LangS G \<noteq> {}\<close>} and Theorem~\ref{Lang_preserved}.
\end{proof}
\end{theorem}

We have now defined a way to extend a context-free grammar by a new start symbol, which, as we will 
see in future sections, will allow us to simplify the definition of multiple automata in many 
regards.\<close>

subsection \<open>Context-Free Items\<close>

text \<open>\begin{definition}[Context-free item]
A \concept{context-free item} for a CFG \<open>G\<close> is a triple \<open>(A, \<alpha>, \<beta>)\<close> such 
that @{prop \<open>(A, \<alpha>@\<beta>) \<in> Prods G\<close>}. We write the item \<open>(A, \<alpha>, \<beta>)\<close> as @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}.
\end{definition}

Context-free items allow tracking the current state of the parsing process. Generally, as parsers
work towards deriving a string, the symbols to the right of the bullet (e.g. \<open>\<beta>\<close> in 
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}) are shifted towards the left. If \<open>(A, \<alpha>@\<beta>) \<in> Prods G\<close>, the item
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} denotes the situation where a word has already been derived from the substring 
\<open>\<alpha>\<close>, with a suffix still left to be derived from \<open>\<beta>\<close>. We call the symbols that have already been 
shifted the \concept{history} of the item.\\

For @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}, \<open>\<alpha> = \<epsilon>\<close> denotes the situation where nothing has been 
derived from \<open>A\<close> yet. Analogously, \<open>\<beta> = \<epsilon>\<close> denotes the situation where a substring of the 
input has been completely derived from \<open>A\<close>. These items are therefore called \concept{initial} and 
\concept{complete} items respectively. For both of these kinds of item, we write \<open>\<epsilon>\<close> implicitly, 
e.g., instead of @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<epsilon>]\<close>}, we write @{term \<open>[A \<rightarrow> \<alpha> \<cdot> ]\<close>}.

We also lift the definition of history from items to lists of items:
\begin{quote}
@{thm hist_def}
\end{quote}

Lastly, we refer to the set of all items of a CFG \<open>G\<close> as @{term \<open>It G\<close>}:
\begin{quote}
@{thm It_def}
\end{quote}

\begin{lemma}\label{prod_items_finite}
@{thm prod_items_finite}
\begin{proof}
The proof is trivial by showing the existence of a bijection between this set and the first 
@{term "length w"} natural numbers using the mapping\\ @{term "f n = [A \<rightarrow> take n w \<cdot> drop n w]"}.
\end{proof}
\end{lemma}

\begin{lemma}
If \<open>G\<close> is a CFG such that \<open>Prods G\<close> is finite, @{term \<open>It G\<close>} is finite.
\begin{proof}
The definition of @{term \<open>It G\<close>} is clearly equivalent to the union of the sets of items for 
each production in \<open>Prods G\<close>. Formally:
\begin{quote}
@{term \<open>It G = (\<Union>(A,w)\<in>Prods G. {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w})\<close>}
\end{quote}
By Lemma~\ref{prod_items_finite}, each of these sets is finite, meaning their union is also finite.
\end{proof}
\end{lemma}\<close>
(*<*)
end
context gpda
begin
(*>*)

subsection \<open>Generalized Pushdown Automata\<close>

text \<open>Throughout this paper, we define several automata to lay the foundations for the canonical 
LR(0) parser. Most of these automata, including the parser itself, require a stack to operate, but 
unlike conventional pushdown automata, it is sometimes necessary for them to read multiple stack 
symbols in a single transition steps.

We define generalized pushdown automata (GPDAs) as a record of type @{typ "('q, 'a) gpda"} where 
@{typ 'q} is the type of stack symbols, @{typ 'a} the type of alphabet symbols, and
\begin{itemize}
\item \<open>states :: 'q set\<close> is a finite set of states.
\item \<open>init :: 'q\<close> is the initial state with \<open>init \<in> states\<close>.
\item \<open>final :: 'q set\<close> is a set of final states with \<open>final \<subseteq> states\<close>.
\item \<open>nxt :: ('q list \<times> 'a \<times> 'q list) set\<close> is the transition relation with input reading.
\item \<open>eps :: ('q list \<times> 'q list) set\<close> is the transition relation for \<open>\<epsilon>\<close>-transitions.
\end{itemize}

It is worth noting that, differently from traditional PDAs, GPDAs do not have a dedicated state. 
Instead, the topmost stack symbols (with varying length) are used to determine the transition. 
Another important aspect is the fact that Wilhelm et al. define the transition relation to be finite, 
which we ignore for the sake of simplicity as this is of no importance to the correctness of our 
automata. This is of interest, however, in the case of the canonical LR(0) parser, which we will 
discuss later.

For \<open>M :: ('q, 'a) gpda\<close> we define a \concept{configuration} as a tuple 
\<open>(qs, w) :: 'q list \<times> 'a list\<close> where \<open>qs\<close> denotes the current stack, and \<open>w\<close> the remaining input to 
be read. In accordance with the Isabelle/HOL list datatype, we define the topmost stack symbol as 
the leftmost list element, deviating from Wilhelm et al. in this regard. \\

A configuration of \<open>M\<close> is \concept{initial} if the stack consists of a singleton list containing 
the initial state @{term \<open>init M\<close>}, while a \concept{final} configuration for \<open>M\<close> consists of a 
singleton list with some final state on the stack after completely consuming the input, 
i.e., a configuration of the form \<open>([f], \<epsilon>)\<close> for some \<open>f \<in> final M\<close>.

We now define the step relation for GPDAs:

@{thm step_nxt step_eps}

We refer to sequences of configurations as \concept{computations}, and denote \<open>n\<close>-step computations
with \<open>\<turnstile>(n)\<close>, and its reflexive-transitive closure with \<open>\<turnstile>*\<close>.\\

Finally, we define the \concept{language} @{term \<open>Lang\<close>} for \<open>M\<close> as the set of words for which \<open>M\<close> 
can reach a final configuration from the corresponding initial configuration:
\begin{quote}
@{thm Lang_def}
\end{quote}\<close>
(*<*) 
end
context Extended_Cfg
begin
(*>*)

section \<open>The Item Pushdown Automaton\<close>

text \<open>One of the main objectives in the construction of our parser is determinism. Despite the ability of
PDAs of recognizing CFLs, they are non-deterministic in general, which means they are not easily
implemented in practice. In this section, we define the Item Pushdown Automaton to a 
context-free grammar, from which we will later derive a deterministic parser.\\

The \concept{item pushdown automaton} (IPDA) to a CFG \<open>G\<close> with extension \<open>G'\<close> is the 
\<open>(('n, 't) item, 't) gpda\<close>:
\begin{quote}
@{term \<open>\<lparr>gpda.states = It G', init = [S' \<rightarrow> [] \<cdot> [Nt S]], final = {mbox [S' \<rightarrow> [Nt S] \<cdot> []]}, 
  nxt = \<Delta>, eps = \<E>\<rparr>\<close>}
\end{quote}
where \<open>\<Delta> = TODO\<close> and \<open>\<E> = TODO\<close>
\<close>

section \<open>The Characteristic Finite Automaton and the Canonical LR(0) Automaton\<close>
section \<open>The Canonical LR(0) Parser\<close>

section \<open>Conclusion\<close>
subsection \<open>Discussion of future work\<close>

(*<*)
end
end
(*>*)
