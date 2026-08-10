(*<*)
theory Paper
  imports 
    "LR0_Base.LR0_Parser"
    "HOL-Library.LaTeXsugar"
begin

section \<open>setup\<close>

declare [[names_short, show_question_marks = false]]

no_notation (latex) Cons (\<open>_ \<cdot>/ _\<close> [66,65] 65)

syntax (latex output)
  "_take" :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_|\<^bsub>_\<^esub>" [1000,0] 1000)

translations 
  "_take xs n" <= "CONST take n xs"

notation (latex output) drop (\<open>\<^bsub>_\<^esub>|_\<close>)

notation (latex output) LangS (\<open>L'(_')\<close>)
notation (latex output) gpda.Lang (\<open>L'(_')\<close>)

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
\begin{quote}
@{datatype list}
\end{quote}

An explicit list can be either written as \<open>x\<^sub>0 # x\<^sub>1 # ... # x\<^sub>n\<close> or as \<open>[x\<^sub>0, x\<^sub>1, ..., x\<^sub>n]\<close>. If 
\<open>xs = y # ys\<close>, \<open>hd xs = y\<close> and \<open>tl xs = ys\<close>. Furthermore, lists are concatenated with the operator 
\<open>@\<close>, @{const rev} reverses a list, @{const set} converts a list to a set, @{term "xs!n"} returns the 
\<open>n\<close>-th element of the list \<open>xs\<close> (with 0-indexing), @{term "take n xs"} is the prefix of length \<open>n\<close> 
of \<open>xs\<close>, and @{term "drop n xs"} is the suffix of \<open>xs\<close> starting at index \<open>n\<close>.

Pattern matching on a term \<open>\<tau>\<close> is done with the keywords \isakeyword{case} and \isakeyword{of}. For 
patterns \<open>\<pi>\<^sub>1, \<pi>\<^sub>2, \<dots>, \<pi>\<^sub>n\<close> and expressions \<open>e\<^sub>1, e\<^sub>2, \<dots>, e\<^sub>n\<close>, the expression
\begin{quote}
\isa{\textsf{case}\ \isafree{\isasymtau}\ \textsf{of}} \<open>\<pi>\<^sub>1 \<Rightarrow> e\<^sub>1 | \<pi>\<^sub>2 \<Rightarrow> e\<^sub>2 | \<dots> | \<pi>\<^sub>n \<Rightarrow> e\<^sub>n\<close>
\end{quote}
returns \<open>e\<^sub>i\<close> if \<open>\<tau>\<close> matches \<open>\<pi>\<^sub>i\<close> and it does not match any \<open>\<pi>\<^sub>j\<close> with \<open>0 < j < i\<close>. If \<open>\<tau>\<close> matches no
\<open>\<pi>\<^sub>i\<close>, @{const undefined} is returned. It is worth noting that variables introduced in \<open>\<pi>\<^sub>i\<close> are bound
on \<open>e\<^sub>i\<close>. 

A simple example on lists returning @{const Nil} if the input is @{const Nil}, and a
singleton list containing the first element otherwise:
\begin{quote}
@{term \<open>case xs of [] \<Rightarrow> [] | y # ys \<Rightarrow> [y]\<close>}
\end{quote}

Finally, if premises \<open>A\<^sub>1, A\<^sub>2, \<dots>, A\<^sub>n\<close> imply \<open>B\<close>, we write \mbox{\<open>\<lbrakk>A\<^sub>1; A\<^sub>2; \<dots>; A\<^sub>n\<rbrakk> \<Longrightarrow> B\<close>.}\<close>

subsubsection \<open>Context-Free Grammars\<close>

text \<open>Our formalization works on top of the formalization of context-free grammars by 
Nipkow et al.~\<^cite>\<open>Nipkow\<close>. In their theories, they introduce type 
@{typ "('n, 't) sym"} for context-free grammar \concept{symbols} as a tagged union consisting of 
nonterminals (@{const Nt}) and terminals (@{const Tm}) of type @{typ 'n} and @{typ 't} respectively:
@{datatype sym}

Besides defining this type for symbols, they also define the following abbreviations:
\begin{quote}
\begin{tabular}{ll}
Lists of symbols & \<open>('n,'t) syms = ('n, 't) sym list\<close>\\
Productions & \<open>('n,'t) prod = 'n \<times> ('n,'t) syms\<close>\\
Sets of productions & \<open>('n,'t) Prods = ('n,'t) prod set\<close>
\end{tabular}
\end{quote}
where we informally write \<open>(A, \<alpha>) :: ('n, 't) prod\<close> as \<open>A \<rightarrow> \<alpha>\<close>. For \mbox{\<open>\<alpha> :: ('n, 't) syms\<close>}, 
@{term \<open>Nts_syms \<alpha>\<close>} returns the set of all \<open>X :: 'n\<close> such that @{prop \<open>Nt X \<in> set \<alpha>\<close>}. Similarly 
for \<open>P :: ('n, 't) Prods\<close>, Nipkow et al. define @{term \<open>Nts P\<close>}:
\begin{equation*}
@{term \<open>Nts P = (\<Union>(A,\<alpha>)\<in>P. {A} \<union> Nts_syms \<alpha>)\<close>}.
\end{equation*}

They further define the datatype for context-free grammars:
\begin{equation*}
\isakeyword{datatype} \<open>('n, 't) Cfg = Cfg (('n,'t) Prods) 'n\<close>.
\end{equation*}
@{term "Cfg P S"} denotes a context-free grammar with production set \<open>P\<close> and start symbol \<open>S\<close>. If 
@{term "G = Cfg P S"}, @{term "Prods G"} refers to \<open>P\<close>, and analogously, @{term "Start G"} refers to 
\<open>S\<close>.

A derivation step from \<open>\<phi>\<close> to \<open>\<psi>\<close> under production set \<open>P\<close> is notated as \mbox{@{term \<open>P \<turnstile> \<phi> \<Rightarrow> \<psi>\<close>}}.
More formally, for \<open>A :: 'n\<close> and \<open>\<alpha>, \<beta>, \<gamma> :: ('n, 't) syms\<close> they define:
\begin{equation*} 
@{thm derive.intros[of A \<beta> P \<alpha> \<gamma>]}.
\end{equation*}
Moreover, they denote the reflexive transitive closure of derivations by \mbox{@{term \<open>P \<turnstile> \<phi> \<Rightarrow>* \<psi>\<close>}}, 
and derivations of length \<open>n\<close> by @{term \<open>P \<turnstile> \<phi> \<Rightarrow>(n) \<psi>\<close>}. Rightmost derivations are notated analogously, 
with \<open>\<Rightarrow>r\<close>, \<open>\<Rightarrow>r*\<close> and \<open>\<Rightarrow>r(n)\<close> respectively.\par

Lastly, Nipkow et al. define the language of a nonterminal w.r.t a set of productions
\begin{equation*}
@{thm Lang_def},
\end{equation*}
and based on this, the language of a grammar
\begin{equation*}
@{term \<open>LangS G\<close>} = @{term [show_abbrevs=false] \<open>Lang (Prods G) (Start G)\<close>}
\end{equation*}
 
Besides type variables @{typ 'n} for nonterminals and @{typ 't} for terminals, we use the following 
variable conventions: for brevity, we refer to \<open>('n, 't) sym\<close> and \<open>('n, 't) syms\<close> simply as @{type sym}
and @{type syms} respectively; \<open>A, B, C :: 'n\<close>; \<open>a, b, c :: 't\<close>; \<open>u, v, w :: 't list\<close>; and finally
\<open>\<alpha>, \<beta>, \<gamma> :: ('n, 't) syms\<close>.\par

For further definitions and notation, we defer to the AFP entry by Nipkow et al~\<^cite>\<open>Nipkow\<close>.\<close>

section \<open>Previous Work\<close>

section \<open>Basic Definitions\<close>
subsection \<open>Extended Grammars\<close>
subsubsection \<open>Reduced Grammars\<close>

text \<open>In general, context-free grammars (CFGs) can contain problematic nonterminals which can be 
removed from the grammar without altering the language. Working with grammars that lack such 
nonterminals is ideal, since having them increases computational complexity and makes the grammar 
less well-behaved.

\begin{example}
Let \<open>G\<close> be a CFG with @{term \<open>S = Start G\<close>} and productions:
\begin{center}
\begin{tabular}{cc}
\<open>S \<rightarrow> A | AB\<close> & \<open>A \<rightarrow> aA | a\<close>\\
\<open>C \<rightarrow> ac | BCD\<close> & \<open>D \<rightarrow> BC | D\<close>
\end{tabular}
\end{center}
Each nonterminal except for \<open>S\<close> and \<open>A\<close> carries problems with it:
\begin{itemize}
\item There are no productions where \<open>B\<close> is on the left-hand side. This means that if \<open>S\<close> 
reaches a sentential form \<open>\<alpha>\<close> such that \<open>Nt B \<in> set \<alpha>\<close>, no word will be derived from \<open>\<alpha>\<close>. 
\item \<open>S\<close> cannot reach \<open>C\<close>, meaning no productions containing \<open>C\<close>, or reachable only 
through \<open>C\<close> (e.g. reaching \<open>D\<close> using production \mbox{\<open>C \<rightarrow> BCD\<close>}), can be used to derive words in \<open>LangS G\<close>.
\item \<open>D\<close>, as opposed to \<open>B\<close>, does show up on the LHS of certain productions, but none of these productions
can lead to a word: \<open>D \<rightarrow> BC\<close> contains \<open>B\<close>, which cannot derive a \<open>'t list\<close>, and \<open>D \<rightarrow> D\<close> has no effect.
Furthermore, similarly to \<open>C\<close>, \<open>D\<close> cannot be reached by \<open>S\<close>.
\end{itemize}
\end{example}

Nipkow et al. define \concept{useful} nonterminals w.r.t. a set of productions and a start 
symbol:
\begin{gather*}
@{abbrev \<open>productives P \<alpha>\<close>}\\
\begin{multlined}
\<open>useful P S A =\<close>\ (@{term \<open>\<exists>\<beta>. P \<turnstile> [Nt S] \<Rightarrow>* \<beta>\<close>}\\
  {} \wedge @{term \<open>Nt A \<in> set \<beta> \<and> productives P \<beta>\<close>})
\end{multlined}
\end{gather*}
For a CFG \<open>G\<close>, \<open>A :: 'n\<close> is \concept{reachable} if there exists a \<open>\<beta> :: syms\<close> such that 
\mbox{\<open>A \<in> set \<beta>\<close>} and @{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<beta>\<close>}. Otherwise, it is \concept{unreachable}.
Similarly, it is \concept{productive} if @{prop [source] \<open>productives (Prods G) [Nt A]\<close>} holds, as 
defined by Nipkow et al. as well:
\begin{equation*}.
@{abbrev \<open>productive (Prods G) A\<close>}
\end{equation*}
Similarly to reachable terminals, a nonterminal that is not productive is \concept{unproductive}. A 
useful nonterminal is therefore a nonterminal that is both reachable and productive. 

Nipkow et al. have also proved that removing all nonterminals that are unreachable or unproductive, 
i.e. all non-useful nonterminals, preserves the language~\cite[Lemma Lang\_restrict\_useful]{Nipkow}:
\begin{lemma}
Let 
\[@{term [source] \<open>restrict_Nts R P = {(A,\<alpha>) \<in> P. \<forall>B \<in> {A} \<union> Nts_syms \<alpha>. R B}\<close>}. \]
Then @{thm Lang_restrict_useful}.\qed
\end{lemma}

With this, we now define the notion of \concept{reduced grammars}.
\begin{definition}[Reduced grammar]
\begin{equation*}
@{thm reduced_def}.
\end{equation*}
\end{definition}

Due to the fact that for any CFG we can construct a reduced grammar with equivalent language,
we can safely constrain our automata to work exclusively with these more well-behaved grammars 
without sacrificing generality.\<close>

subsubsection \<open>Extending Grammars by a New Start Symbol\<close>

(*<*)
context Extended_Cfg 
begin
(*>*)

text\<open>From this point onward in this paper, let \<open>G\<close> be a fixed CFG whose start symbol is \<open>S\<close> with the 
following properties:
\begin{itemize}
\item @{prop \<open>finite (Prods G)\<close>}
\item @{prop \<open>LangS G \<noteq> {}\<close>}
\item @{prop \<open>reduced G\<close>}
\end{itemize}

We extend \<open>G\<close> by a fresh start symbol \<open>S'\<close> with a single production \<open>(S', [Nt S])\<close>. 
The resulting grammar, which we define to be \<open>G'\<close>, is the \concept{extended grammar}, or the 
\concept{extension}, of \<open>G\<close>. We analogously refer to \<open>Prods G'\<close> as the extension of \<open>Prods G\<close> or the 
\concept{extended set of productions} of \<open>G\<close>. Formally:
\begin{gather*}
@{thm S'_def}\\
@{thm G'_def}
\end{gather*}

We now prove that extending a grammar preserves both language and reduction.\<close>

(*<*)
end
(*>*)
(* Needed? (trivial?) *)
text\<open>\begin{lemma}\label{S_deriven_Suc_imp_all_nts_in_Nts}
If \<open>G\<close> is an arbitrary CFG and there exist \<open>\<alpha> :: syms\<close>, \<open>A :: 'n\<close> where @{prop \<open>A \<in> Nts_syms \<alpha>\<close>} 
and
\[ @{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc n) \<alpha>\<close>}, \]
Then @{prop \<open>A \<in> Nts (Prods G)\<close>}.
\begin{proof}
We do a proof by induction on \<open>n\<close> for arbitrary \<open>\<alpha>\<close>. In the base case, the derivation is a 
single step @{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow> \<alpha>\<close>}, meaning \mbox{\<open>(Start G, \<alpha>) \<in> Prods G\<close>}. 
Together with the fact that \<open>A \<in> Nts_syms \<alpha>\<close>, this implies @{prop \<open>A \<in> Nts (Prods G)\<close>}.

For the inductive step, we must prove the statement holds for \<open>\<alpha>\<close> assuming 
@{prop \<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc (Suc n)) \<alpha>\<close>} for some \<open>n\<close> and @{prop \<open>A \<in> Nts_syms \<alpha>\<close>}. 
This implies there is a last step of the form
\begin{equation*}
\<open>Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>(Suc n) \<gamma> @ [Nt B] @ \<delta> \<Rightarrow> \<gamma> @ \<beta> @ \<delta> = \<alpha>\<close>
\end{equation*}
with @{term \<open>(B, \<beta>) \<in> Prods G\<close>}. 

We now make a case distinction on whether \<open>A \<in> Nts_syms \<beta>\<close> holds:

If \<open>A \<in> Nts_syms \<beta>\<close>, then \<open>A \<in> Nts (Prods G)\<close> follows directly by the fact that 
\mbox{\<open>(B, \<beta>) \<in> Prods G\<close>}.

If \<open>A \<notin> Nts_syms \<beta>\<close>, this and \<open>A \<in> Nts_syms \<alpha>\<close> imply
\[ \<open>A \<in> Nts_syms (\<gamma> @ [Nt B] @ \<delta>)\<close>. \] 
By the induction hypothesis, this in turn implies \<open>A \<in> Nts (Prods G)\<close>, and the proof is thus 
complete.
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
\begin{equation*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow> [Nt S] \<Rightarrow>* map Tm w\<close>.
\end{equation*}
Therefore, there exists an \<open>n :: nat\<close> such that 
\begin{equation*}
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>(Suc n) map Tm w\<close>}.
\end{equation*}
By Lemma~\ref{G'_deriven_Suc_imp_G_deriven}, this implies the existence of a derivation
\mbox{@{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>(n) map Tm w\<close>}}, and thus \mbox{@{prop \<open>w \<in> LangS G\<close>}}.

Conversely, let @{prop \<open>w \<in> LangS G\<close>}. Then there exists a derivation\\
@{prop \<open>Prods G \<turnstile> [Nt S] \<Rightarrow>* map Tm w\<close>}. Since @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow> [Nt S]\<close>} and 
@{prop \<open>Prods G \<subseteq> Prods G'\<close>}, @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>* map Tm w\<close>} also holds by 
transitivity and the monotonicity of \<open>\<Rightarrow>*\<close>, as proven by Nipkow et al.~\cite[Lemma derives\_mono]{Nipkow}:
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
\begin{equation*}
\<open>Prods G \<turnstile> [Nt S] \<Rightarrow> \<alpha> \<Rightarrow>* map Tm w\<close>.
\end{equation*}
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
A \concept{context-free item} @{typ \<open>('n, 't) item\<close>} for a CFG \<open>G\<close> is a triple 
\mbox{\<open>(A, \<alpha>, \<beta>) :: 'n \<times> ('n, 't) syms \<times> ('n, 't) syms\<close>} such that 
@{prop \<open>(A, \<alpha>@\<beta>) \<in> Prods G\<close>}. We write the item \<open>(A, \<alpha>, \<beta>)\<close> as @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}, and akin to 
@{type sym} and @{type syms}, we often abbreviate the item type to simply @{type item} for brevity.
\end{definition}

Context-free items allow tracking the current state of the parsing process. Generally, as parsers
work towards deriving a string, the symbols to the right of the bullet (e.g. \<open>\<beta>\<close> in 
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}) are shifted towards the left. If \<open>(A, \<alpha>@\<beta>) \<in> Prods G\<close>, the item
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} denotes the situation where a word has already been derived from the substring 
\<open>\<alpha>\<close>, with a suffix still left to be derived from \<open>\<beta>\<close>. We call the symbols that have already been 
shifted the \concept{history} of the item.

For @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>}, \<open>\<alpha> = \<epsilon>\<close> denotes the situation where nothing has been 
derived from \<open>A\<close> yet. Analogously, \<open>\<beta> = \<epsilon>\<close> denotes the situation where a substring of the 
input has been completely derived from \<open>A\<close>. These items are therefore called \concept{initial} and 
\concept{complete} items respectively. For both of these kinds of item, we write \<open>\<epsilon>\<close> implicitly, 
e.g., instead of @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<epsilon>]\<close>}, we write @{term \<open>[A \<rightarrow> \<alpha> \<cdot> ]\<close>}. Additionally, we denote the 
set of all complete items in a set of items \<open>I\<close> by @{term \<open>completes I\<close>}:
\begin{equation*}
@{thm completes_def}.
\end{equation*}
An item that is not complete is referred to as \concept{noncomplete}, and we correspondingly define
@{const noncompletes} as the complement of @{const completes}:
\begin{equation*}
@{abbrev \<open>noncompletes I\<close>}.
\end{equation*}
We also lift the definition of history from items to lists of items:
\begin{equation*}
@{thm hist_def},
\end{equation*}
and lastly, we refer to the set of all items of a CFG \<open>G\<close> as @{term \<open>It G\<close>}:
\begin{equation*}
@{thm It_def}.
\end{equation*}

\begin{lemma}\label{in_Prods_iff_in_It}
@{term \<open>(A, \<alpha>@\<beta>) \<in> Prods G \<longleftrightarrow> [A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> It G\<close>}
\begin{proof}
Trivial by the definition of @{term \<open>It G\<close>}.
\end{proof}
\end{lemma}

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
\[ @{term \<open>It G = (\<Union>(A,w)\<in>Prods G. {[A \<rightarrow> \<alpha> \<cdot> \<beta>] | \<alpha> \<beta>. \<alpha>@\<beta> = w})\<close>}. \]
By Lemma~\ref{prod_items_finite}, each of these sets is finite, meaning their union is also finite.
\end{proof}
\end{lemma}\<close>

subsection \<open>Generalized Pushdown Automata\<close>

(*<*)
end
context gpda
begin
(*>*)

text \<open>Throughout this paper, we define several automata to lay the foundations for the canonical 
LR(0) parser. Most of these automata, including the parser itself, require a stack to operate, but 
unlike conventional pushdown automata, it is sometimes necessary for them to read multiple stack 
symbols in a single transition steps.
\begin{definition}[Generalized pushdown automata]
A generalized pushdown automata (GPDAs) is a record of type @{typ "('q, 'a) gpda"} where 
@{typ 'q} is the type of stack symbols, @{typ 'a} the type of alphabet symbols, and
\begin{itemize}
\item \<open>states :: 'q set\<close> is a finite set of states.
\item \<open>init :: 'q\<close> is the initial state with \<open>init \<in> states\<close>.
\item \<open>final :: 'q set\<close> is a set of final states with \<open>final \<subseteq> states\<close>.
\item \<open>nxt :: ('q list \<times> 'a \<times> 'q list) set\<close> is the transition relation consuming input symbols.
\item \<open>eps :: ('q list \<times> 'q list) set\<close> is the transition relation for \<open>\<epsilon>\<close>-transitions.
\end{itemize}
\end{definition}

It is worth noting that, differently from traditional PDAs, GPDAs do not have a dedicated state. 
Instead, the topmost stack symbols (with varying length) are used to determine the transition. 
Another important aspect is the fact that Wilhelm et al. define the transition relation to be finite, 
which we ignore for the sake of simplicity as this is of no importance to the correctness of our 
automata. This is of interest, however, in the case of the canonical LR(0) parser, which we will 
discuss later.

For \<open>M :: ('q, 'a) gpda\<close> we define a \concept{configuration} as a tuple 
\<open>(qs, w) :: 'q list \<times> 'a list\<close> where \<open>qs\<close> denotes the current stack, and \<open>w\<close> the remaining input to 
be read. In accordance with the Isabelle/HOL list datatype, we define the topmost stack symbol as 
the leftmost list element, deviating from Wilhelm et al. in this regard.

A configuration of \<open>M\<close> is \concept{initial} if the stack consists of a singleton list containing 
the initial state @{term \<open>init M\<close>}, while a \concept{final} configuration for \<open>M\<close> consists of a 
singleton list with some final state on the stack after completely consuming the input, 
i.e., a configuration of the form \<open>([f], \<epsilon>)\<close> for some \<open>f \<in> final M\<close>.

We now define the step relation \<open>\<turnstile>\<close> for GPDAs:
@{thm [display] step_nxt step_eps}
We refer to sequences of configurations as \concept{computations}, and denote \<open>n\<close>-step computations
with \<open>\<turnstile>(n)\<close>, and its reflexive-transitive closure with \<open>\<turnstile>*\<close>.

\begin{lemma}\label{reachable_imp_substring}
If @{prop \<open>(ps, w) \<turnstile>* (qs, v)\<close>}, \<open>v\<close> is a suffix of \<open>w\<close>, i.e., there exists a \<open>u\<close> such that 
@{prop \<open>w = u @ v\<close>}.
\begin{proof}
The proof is by induction on the length of the computation, distinguishing between whether the final 
step of the computation is a \<open>nxt\<close>-step or an \<open>eps\<close>-step for the transitive case.
\end{proof}
\end{lemma}

Finally, we define the \concept{language} @{term \<open>Lang\<close>} for \<open>M\<close> as the set of words for which \<open>M\<close> 
can reach a final configuration from the corresponding initial configuration:
\begin{equation*}
@{thm Lang_def}.
\end{equation*}\<close>

section \<open>The Item Pushdown Automaton\<close>

(*<*) 
end
context ipda
begin
abbreviation \<open>I\<^sub>G \<equiv> IPDA\<close>
abbreviation ipda_step :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
  "(\<turnstile>) \<equiv> (gpda.step M)"

abbreviation ipda_steps :: "('n,'t) item list \<times> 't list \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" (infix \<open>\<turnstile>*\<close> 55) where
  "(\<turnstile>*) \<equiv> (gpda.steps M)"

abbreviation ipda_stepn :: "('n,'t) item list \<times> 't list \<Rightarrow> nat \<Rightarrow> ('n,'t) item list \<times> 't list 
                    \<Rightarrow> bool" ( \<open>_ \<turnstile>'(_') _\<close> 55) where
  "c0 \<turnstile>(n) c1 \<equiv> (gpda.stepn M) c0 n c1"

(*>*)

subsection \<open>Definition\<close>

text \<open>One of the main objectives in the construction of our parser is determinism. Despite the ability of
PDAs of recognizing CFLs, they are non-deterministic in general, which means they are not easily
implemented in practice. In this section, we define the Item Pushdown Automaton to a 
context-free grammar, from which we will later derive a deterministic parser.\par

\begin{definition}[Item pushdown automaton]
The \concept{item pushdown automaton} (IPDA) to a CFG \<open>G\<close> with extension \<open>G'\<close> is the 
\mbox{\<open>(('n, 't) item, 't) gpda\<close>}:
\begin{multline*}
  \<open>I\<^sub>G = \<lparr>gpda.states = It G', init = [S' \<rightarrow> \<cdot> [Nt S]],\<close>\\
  \<open>final = {[S' \<rightarrow> [Nt S] \<cdot> ]}, nxt = \<Delta>, eps = \<E>\<rparr>\<close>
\end{multline*}
where 
\begin{multline*}
\<open>\<Delta> = {([[X \<rightarrow> \<beta> \<cdot> Tm a # \<gamma>]], a, [[X \<rightarrow> \<beta> @ [Tm a] \<cdot> \<gamma>]])\<close>\\
\<open>| X \<beta> a \<gamma>. (X, \<beta> @ Tm a # \<gamma>) \<in> Prods G'}\<close>
\end{multline*}
and \<open>\<E> = E \<union> R\<close> for
\begin{gather*}
\begin{multlined}
  \<open>E = {([[X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[Y \<rightarrow> \<cdot> \<alpha>], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]])\<close>\\ 
  \<open>| X \<beta> Y \<gamma> \<alpha>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'}\<close>
\end{multlined}\\
\begin{multlined}
  \<open>R = {([[Y \<rightarrow> \<alpha> \<cdot> ], [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>]], [[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]])\<close>\\
  \<open>| Y \<alpha> X \<beta> \<gamma>. (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G' \<and> (Y, \<alpha>) \<in> Prods G'}\<close>
\end{multlined}
\end{gather*}
\end{definition}

Overall, the IPDA has three types of transitions. We call transitions in @{const nxt} \concept{shifting} 
transitions, transitions in @{term \<open>E \<subseteq> \<E>\<close>} \concept{expanding} transitions, and transitions in 
@{term \<open>R \<subseteq> \<E>\<close>} \concept{reducing} transitions.

Our definitions differ slightly from those by Wilhelm et al.: in all
transition sets, we explicitly restrict the elements to items that correspond to productions of \<open>G'\<close>.
In their book, Wilhelm et al. define the transition relation of a GPDA with state set \<open>Q\<close> and input
alphabet \<open>V\<^sub>T\<close> to be a subset of \mbox{\<open>Q\<^sup>+ \<times> V\<^sub>T \<times> Q\<^sup>*\<close>}. We approximate this in the record type of GPDAs, 
as we stated before, by definining \mbox{\<open>nxt :: ('q list \<times> 'a \<times> 'q list) set\<close>} and 
\mbox{\<open>eps :: ('q list \<times> 'q list) set\<close>} for a \<open>('q, 'a) gpda\<close>. Our definitions of \mbox{\<open>nxt IPDA\<close>} and \<open>eps IPDA\<close>
therefore enforce this by explicitly restricting the set to items whose corresponding production is 
in \<open>Prods G'\<close>, which is equivalent to the items themselves being in @{term \<open>It G'\<close>} by 
Lemma~\ref{in_Prods_iff_in_It}.

%\begin{lemma}
%\<open>I\<^sub>G\<close> fullfills all GPDA assumptions
%\begin{proof}
%\end{proof} 
%\end{lemma}

Intuitively, \<open>I\<^sub>G\<close> accepts a word \<open>w\<close> by finding a rightmost derivation 
\[ @{term \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* map Tm w\<close>}. \]
If the current topmost stack item is @{term \<open>[A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]\<close>} for any \mbox{\<open>a :: 't\<close>}, \<open>I\<^sub>G\<close> will 
invariably shift \<open>Tm a\<close>, effectively replacing this topmost item by @{term \<open>mbox [A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>]\<close>}. 
Similarly, if the topmost item is some complete item @{term \<open>[Y \<rightarrow> \<alpha> \<cdot> ]\<close>}, it will reduce the item 
and shift \<open>Nt Y\<close> on the second-topmost item if possible. If the stack is 
@{term \<open>[Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>\<close>}, the act of reducing the first two items to 
@{term \<open>[X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>]\<close>} is equivalent to the backwards (i.e. right-to-left)
application of a rightmost derivation step for some \<open>u :: 't list\<close> of the form
\begin{equation*}
@{prop \<open>Prods G' \<turnstile> \<beta> @ Nt Y # map Tm u \<Rightarrow>r \<beta> @ \<alpha> @ map Tm u\<close>}.
\end{equation*}

Lastly, the expanding case is the only transition type where nondeterministic behavior actually 
presents itself. While reducing transitions correspond to the IPDA applying a backward step in a 
rightmost derivation, the expanding step is essentially the IPDA nondeterministically choosing 
\emph{which} production to reduce: as we will later prove, if the IPDA performs the expansion
\begin{multline*}
@{term \<open>([X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>, w)\<close>}\\
  \<open>\<turnstile>\<close>\ @{term \<open>([Y \<rightarrow> \<cdot> \<alpha> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>, w)\<close>}
\end{multline*}
it will only complete \<open>\<alpha>\<close>, i.e., reach a configuration with stack 
\[ @{term \<open>[Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>\<close>} \]
if for some prefix \<open>u\<close> of the remaining input word \<open>w = uv\<close> holds 
\[ @{prop \<open>Prods G' \<turnstile> \<alpha> \<Rightarrow>* map Tm u\<close>}. \]
 
We will now work towards proving that \<open>I\<^sub>G\<close> accepts exactly @{term \<open>LangS G\<close>}.\<close>

subsection \<open>Language Equivalence\<close>

text\<open>\begin{lemma}\label{reducing_imp_in_Prods_G}
@{thm reducing_imp_in_Prods_G}
\begin{proof}
Because \<open>I\<^sub>G\<close> transitions are only defined for elements of @{term \<open>It G\<close>}, we know that 
\<open>(Y, \<alpha>), (X, \<beta> @ Nt Y # \<gamma>) \<in> Prods G'\<close>. Hence, either \<open>(Y, \<alpha>) \<in> Prods G\<close> or \<open>(Y, \<alpha>) = (S', S)\<close>.\par
If \<open>(Y, \<alpha>) = (S', S)\<close> were true, S' would be on the RHS of the production \<open>(X, \<beta> @ Nt Y # \<gamma>)\<close>. Since
we know no such production exists, this would be a contradiction. Therefore, \<open>(Y, \<alpha>) \<in> Prods G\<close>.
\end{proof}
\end{lemma}

\begin{corollary}\label{steps_shift_decomp}
If there exists a computation of the form  
\begin{equation*}
@{term \<open>(\<rho>, u @ v) \<turnstile>* ([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<sigma>, a # v)\<close>} 
  \vdash @{term (rhs) \<open>([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<sigma>, a # v) \<turnstile> (\<tau>, v)\<close>},
\end{equation*}
then there exists an \<open>x :: 't list\<close> such that \<open>u = xa\<close>.
\begin{proof}
This is a direct consequence of Lemma~\ref{reachable_imp_substring}.
\end{proof}
\end{corollary}

\begin{lemma}[IPDA invariant]\label{ipda.invariant}
@{prop \<open>([init M], u @ v) \<turnstile>* (rev \<rho>, v)\<close>} implies\\ @{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u\<close>}.
\begin{proof}
We do a proof by induction on the length \<open>n\<close> of the computation for arbitrary \<open>u, v,\<close> and \<open>\<rho>\<close>.\\
If @{term "([init M], u @ v) \<turnstile>(0) (rev \<rho>, v)"}, then
\begin{gather*} 
\<open>[init M] = rev \<rho> = [[S' \<rightarrow> \<cdot> [Nt S]]]\<close> \text{ and } @{prop \<open>u @ v = v\<close>} 
\end{gather*}
hold. This in turn implies @{prop \<open>hist \<rho> = []\<close>} and @{prop \<open>u = []\<close>}. Since
\mbox{@{prop \<open>Prods G \<turnstile> [] \<Rightarrow>* []\<close>}} holds, the invariant holds.

On the other hand, if @{term "([init M], u @ v) \<turnstile>(Suc n) (rev \<rho>, v)"} for some \<open>n :: nat\<close>, there 
exist \<open>\<sigma> :: item list\<close> and \<open>w :: 't list\<close> where
\begin{equation}\label{eq:ipda.invariant.stepn}
\<open>([init M], u @ v) \<turnstile>(n) (rev \<sigma>, w) \<turnstile> (rev \<rho>, v)\<close>.
\end{equation}
We now make a case distinction on the final step of the computation.

If the last step was a shifting transition there exist \<open>A, \<alpha>, a, \<beta>, \<tau>, a, \<close> and \<open>x\<close> such that
\begin{gather}
@{term \<open>(rev \<sigma>, w) = ([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<tau>, a # v)\<close>}\label{eq:ipda.invariant.shift}
\intertext{and}
@{term \<open>rev \<rho> = [A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>] # \<tau>\<close>}\label{eq:ipda.invariant.rho_shift}.
\end{gather}
With Corollary~\ref{steps_shift_decomp}, this implies the existence of some \<open>y :: 't list\<close> such that
\mbox{\<open>u = ya\<close>}. This, together with \eqref{eq:ipda.invariant.stepn}, 
\eqref{eq:ipda.invariant.shift}, and the induction hypothesis implies 
\begin{equation}\label{eq:ipda.invariant.ih_shift}
@{prop \<open>Prods G \<turnstile> hist \<sigma> \<Rightarrow>* map Tm y\<close>}.
\end{equation}

Furthermore, from \eqref{eq:ipda.invariant.shift} and \eqref{eq:ipda.invariant.rho_shift} follows
\[ \<open>hist \<rho> = hist (rev \<tau>) @ \<alpha> @ [Tm a] = hist \<sigma> @ [Tm a]\<close>. \]
This, \<open>u = ya\<close> and \eqref{eq:ipda.invariant.ih_shift} imply 
\[ \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow>* ya = u\<close>. \]
This satisfies the invariant.

For the reducing case, we have 
\begin{gather}
@{term \<open>(rev \<sigma>, w) = ([Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close>}\label{eq:ipda.invariant.reduce}\\
\intertext{and} @{term \<open>rev \<rho> = [X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>] # \<tau>\<close>}\label{eq:ipda.invariant.rho_reduce}
\end{gather}
for some \<open>Y, \<alpha>, X, \<beta>, \<gamma>\<close> and \<open>\<tau>\<close>. By Lemma~\ref{reducing_imp_in_Prods_G}, we know that 
\mbox{@{prop \<open>(Y, \<alpha>) \<in> Prods G\<close>}}. Furthermore, \eqref{eq:ipda.invariant.reduce} and 
\eqref{eq:ipda.invariant.rho_reduce} imply @{prop \<open>hist \<rho> = hist (rev \<tau>) @ \<beta> @ [Nt Y]\<close>} and 
\mbox{@{prop \<open>hist \<sigma> = hist (rev \<tau>) @ \<beta> @ \<alpha>\<close>}}. From this follows
\begin{equation}\label{eq:ipda.invariant.reduce_rs}
@{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow> hist \<sigma>\<close>}.
\end{equation}

Furthermore, the induction hypothesis along with \eqref{eq:ipda.invariant.stepn} and 
\eqref{eq:ipda.invariant.reduce} implies  
\[ @{prop \<open>Prods G \<turnstile> hist \<sigma> \<Rightarrow>* map Tm u\<close>}. \]
@{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u\<close>} follows from this and \eqref{eq:ipda.invariant.reduce_rs} by 
transitivity, fulfilling the invariant.

Finally, in the expanding case we have 
\begin{gather*}
\<open>(rev \<sigma>, w) = ([X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close> \intertext{and} 
  \<open>rev \<rho> = [Y \<rightarrow> [] \<cdot> \<alpha>] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>\<close> 
\end{gather*}
With the induction hypothesis and \eqref{eq:ipda.invariant.stepn}, this implies
\begin{gather*}
\<open>hist \<rho> = hist \<sigma>\<close>\\ 
\intertext{and}
\<open>Prods G \<turnstile> hist \<sigma> \<Rightarrow>* map Tm u\<close>.
\end{gather*}
The invariant is therefore satisfied, completing the proof.
\end{proof}
\end{lemma}

\begin{lemma}\label{ipda.Lang_subst_Lang_G}
@{term \<open>gpda.Lang I\<^sub>G \<subseteq> LangS G\<close>}
\begin{proof}
Assume @{prop \<open>w \<in> gpda.Lang I\<^sub>G\<close>}. Then, 
\[ \<open>([init I\<^sub>G], w) =\<close>\ @{prop \<open>([init I\<^sub>G], w @ [])  \<turnstile>* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>}. \] 
By Lemma~\ref{ipda.invariant}, this implies @{prop \<open>Prods G \<turnstile> hist [final_state] \<Rightarrow>* map Tm w\<close>}.
Since @{prop \<open>hist [final_state] = [Nt S]\<close>}, this proves that @{prop \<open>w \<in> LangS G\<close>}.  
\end{proof}
\end{lemma}

And now, we prove the other direction:

\begin{lemma}\label{completes_Tms}
If @{prop \<open>(A, \<alpha> @ map Tm u @ \<beta>) \<in> Prods G' \<close>}, then 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> map Tm u @ \<beta>]#\<rho>, u@v) \<turnstile>* ([A \<rightarrow> \<alpha> @ map Tm u \<cdot> \<beta>]#\<rho>, v)\<close>}. \]
\begin{proof}
Trivial by induction on the length of \<open>u\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{derives_imp_completes}[Derivation implies IPDA completion]
If 
\[ @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w\<close>} \] 
and @{prop \<open>(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'\<close>}, then for any \<open>\<rho>, x\<close> holds: 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>@\<gamma>] # \<rho>, w @ x) \<turnstile>* ([A \<rightarrow> \<alpha>@\<beta> \<cdot> \<gamma>] # \<rho>, x)\<close>}. \]
\begin{proof}
We do a proof by strong induction on the length of the derivation \<open>n\<close>.\par
If \<open>n = 0\<close>, \<open>\<beta> = map Tm w\<close>, and the implication holds by Lemma~\ref{completes_Tms}.\par
If \<open>n = Suc m\<close> for some \<open>m :: nat\<close>, the derivation can be decomposed into \<open>\<delta>\<^sub>1, \<delta>\<^sub>2 :: syms\<close>, \<open>X :: 'n\<close>, 
\<open>u, v, y :: 't list\<close> and \<open>i, j, k :: nat\<close> such that:
\begin{subequations}
\begin{gather}
@{prop \<open>\<beta> = \<delta>\<^sub>1 @ Nt X # \<delta>\<^sub>2\<close>}\label{d_imp_c.b_decomp(1)}\\
@{prop \<open>w = u @ v @ y\<close>}\label{d_imp_c.b_decomp(2)}\\
@{prop \<open>Prods G' \<turnstile> \<delta>\<^sub>1 \<Rightarrow>(i) map Tm u\<close>}\label{d_imp_c.d1}\\
@{prop \<open>Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v\<close>}\label{d_imp_c.X}\\
@{prop \<open>Prods G' \<turnstile> \<delta>\<^sub>2 \<Rightarrow>(k) map Tm y\<close>}\label{d_imp_c.d2}\\
@{prop \<open>n = i + j + k\<close>}.\label{d_imp_c.b_decomp(6)}
\end{gather}
\end{subequations}
Furthermore, @{prop \<open>Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v\<close>} implies @{prop \<open>j > 0\<close>}, since @{prop \<open>j = 0\<close>}
would imply @{prop \<open>[Nt X] = map Tm v\<close>}, which is a contradiction. We will now do a case distinction 
on whether @{prop \<open>j = n\<close>} holds.\par
If \<open>j = n\<close>, then \<open>i = k = 0\<close> and therefore
\begin{gather}\label{d_imp_c.d1u_d2y}
\<open>\<delta>\<^sub>1 = map Tm u\<close> \text{ and } \<open>\<delta>\<^sub>2 = map Tm y\<close>
\end{gather} 
hold. \<open>j = n\<close> also implies the existence of some \<open>\<beta>' :: syms\<close> such that 
\begin{equation}\label{eq:d_imp_c.stepm}
\<open>Prods G' \<turnstile> [Nt X] \<Rightarrow> \<beta>' \<Rightarrow>(m) map Tm v\<close>.
\end{equation}
We now distinguish yet another two cases, now on \<open>m\<close>. \<open>\<turnstile>\<^sub>R\<close> and \<open>\<turnstile>\<^sub>E\<close> denote a reducing and an expanding 
transition respectively.

If \<open>m = 0\<close>, then @{prop \<open>Prods G' \<turnstile> [Nt X] \<Rightarrow> v\<close>}. With Lemma~\ref{completes_Tms}
(L\ref{completes_Tms}) follows:
\begin{align*}
&@{term \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] # \<rho>, w @ x)\<close>}\\
&\;\overset{(\ref{d_imp_c.b_decomp(1)}, \ref{d_imp_c.b_decomp(2)}, \ref{d_imp_c.d1u_d2y})}{=\ }
 @{term \<open>([A \<rightarrow> \<alpha> \<cdot> map Tm u @ Nt X # map Tm y @ \<gamma>] # \<rho>, u @ v @ y @ x)\<close>}\\
&\;\overset{(L\ref{completes_Tms})}{\<open>\<turnstile>*\<close>\ } 
  @{term \<open>([A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, v @ y @ x)\<close>}\\
&\;\<open>\<turnstile>\<^sub>E\<close>\ @{term \<open>([X \<rightarrow> \<cdot> map Tm v] # [A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, v @ y @ x)\<close>}\\
&\;\overset{(L\ref{completes_Tms})}{\<open>\<turnstile>*\<close>\ }
  @{term \<open>([X \<rightarrow> map Tm v \<cdot> ] # [A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, y @ x)\<close>}\\
&\;\<open>\<turnstile>\<^sub>R\<close>\ @{term \<open>([A \<rightarrow> \<alpha> @ map Tm u @ [Nt X] \<cdot> map Tm y @ \<gamma>] # \<rho>, y @ x)\<close>}\\
&\;\overset{(L\ref{completes_Tms})}{\<open>\<turnstile>*\<close>\ }
  @{term \<open>([A \<rightarrow> \<alpha> @ map Tm u @ [Nt X] @ map Tm y \<cdot> \<gamma>] # \<rho>, x)\<close>}
\overset{(\ref{d_imp_c.b_decomp(1)}, \ref{d_imp_c.d1u_d2y})}{=\ } \<open>([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] # \<rho>, x).\<close>
\end{align*}
Therefore, the implication holds.

Otherwise, if \<open>m = Suc m'\<close> for some \<open>m'\<close>, the derivation @{prop \<open>Prods G' \<turnstile> \<beta>' \<Rightarrow>(m) map Tm v\<close>} can 
be decomposed as we did before: there exist \<open>\<xi>\<^sub>1, \<xi>\<^sub>2 :: syms\<close>, \<open>Y :: 'n\<close>, \<open>u', v', y' :: 't list\<close>, 
and \<open>i', j', k' :: nat\<close> such that:
\begin{subequations}
\begin{gather}
@{prop \<open>\<beta>' = \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2\<close>}\label{d_imp_c.b'_decomp(1)}\\
@{prop \<open>v = u' @ v' @ y'\<close>}\label{d_imp_c.b'_decomp(2)}\\
@{prop \<open>Prods G' \<turnstile> \<xi>\<^sub>1 \<Rightarrow>(i') map Tm u'\<close>}\label{d_imp_c.xi1}\\
@{prop \<open>Prods G' \<turnstile> [Nt Y] \<Rightarrow>(j') map Tm v'\<close>}\label{d_imp_c.Y}\\
@{prop \<open>Prods G' \<turnstile> \<xi>\<^sub>2 \<Rightarrow>(k') map Tm y'\<close>}\\
@{prop \<open>i' + j' + k' = m\<close>}.
\end{gather}
\end{subequations}

This in turn implies that @{prop \<open>i' < n\<close>}, @{prop \<open>j' < n\<close>} and @{prop \<open>k' < n\<close>}, and once again,
\eqref{d_imp_c.Y} implies that @{prop \<open>j' > 0\<close>}, i.e., @{prop \<open>j' = Suc j''\<close>} for some \<open>j''\<close>, 
meaning this derivation of \<open>v'\<close> is of the form 
\begin{equation}\label{eq:d_imp_c.stepj''}
\<open>Prods G' \<turnstile> [Nt Y] \<Rightarrow> \<gamma>' \<Rightarrow>(j'') map Tm v'\<close>
\end{equation}
for some \<open>\<gamma>' :: syms\<close>. Furthermore, @{prop \<open>j' < n\<close>} implies @{prop \<open>j'' < n\<close>}, and  since 
\begin{gather}\label{ijk'_less}
@{prop \<open>i' < n\<close>} \text{, } @{prop \<open>j'' < n\<close>} \text{ and } @{prop \<open>k' < n\<close>}, 
\end{gather}
we can use the induction hypothesis (IH) on their corresponding derivations. 
Let @{term \<open>\<sigma> = [A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>\<close>}. The computation then is similar to 
the previous case, except that
\[ @{term \<open>([A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, v @ y @ x)\<close>} \] 
now expands to 
\[ @{term \<open>([X \<rightarrow> \<cdot> \<xi>\<^sub>1 @ Nt Y # \<xi>\<^sub>2] # \<sigma>, u' @ v' @ y' @ y @ x)\<close>} \]
by \eqref{eq:d_imp_c.stepm}, \eqref{d_imp_c.b'_decomp(1)} and \eqref{d_imp_c.b'_decomp(2)}.
By the induction hypothesis, 
\<open>I\<^sub>G\<close> can then complete \<open>\<xi>\<^sub>1\<close>:
\[ ... \overset{(IH, \ref{d_imp_c.xi1}, \ref{ijk'_less})}{\<open>\<turnstile>*\<close>\ } 
@{term \<open>([X \<rightarrow> \<xi>\<^sub>1 \<cdot> Nt Y # \<xi>\<^sub>2] # \<sigma>, v' @ y' @ y @ x)\<close>}, \]
and now by \eqref{eq:d_imp_c.stepj''}, \<open>I\<^sub>G\<close> expands:
\[ ...\ \<open>\<turnstile>\<^sub>E\<close>\ @{term \<open>([Y \<rightarrow> \<cdot> \<gamma>'] # [X \<rightarrow> \<xi>\<^sub>1 \<cdot> Nt Y # \<xi>\<^sub>2] # \<sigma>, v' @ y' @ y @ x)\<close>}. \]
The computation then continues analogously to the first case, applying the IH again to complete 
\<open>\<gamma>'\<close> and \<open>\<xi>\<^sub>2\<close>. Therefore, the implication also holds in the case where @{prop \<open>j = n\<close>}. 

Finally, we now consider the case where @{prop \<open>j \<noteq> n\<close>}:

With @{prop \<open>n = i + j + k\<close>} and @{prop \<open>j > 0\<close>}, we know that @{prop \<open>i < n\<close>}, @{prop \<open>j < n\<close>}, and
@{prop \<open>k < n\<close>} all hold. Therefore, we can use the IH for each of the derivations \eqref{d_imp_c.d1}, 
\eqref{d_imp_c.X} and \eqref{d_imp_c.d2} after decomposing \<open>\<beta>\<close> and \<open>w\<close> as we did in the previous
cases with \eqref{d_imp_c.b_decomp(1)} and \eqref{d_imp_c.b_decomp(2)}. This completes the proof.
\end{proof}
\end{lemma}

With this lemma we can finally prove the second direction in the language equivalence proof:

\begin{lemma}\label{ipda.Lang_G_subst_Lang}
@{prop \<open>LangS G \<subseteq> gpda.Lang I\<^sub>G\<close>}
\begin{proof}
Assume @{prop \<open>w \<in> LangS G\<close>}. Since @{prop \<open>Prods G \<subseteq> Prods G'\<close>}, this implies 
\[ @{prop \<open>Prods G' \<turnstile> [Nt S] \<Rightarrow>* map Tm w\<close>} \] by the monotonicity of derivations as proved by 
Nipkow et al. With Lemma~\ref{derives_imp_completes} follows 
\[ @{prop \<open>([[S' \<rightarrow> \<cdot> [Nt S]]], w) \<turnstile>* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>}. \] 

This is equivalent to @{prop \<open>w \<in> gpda.Lang I\<^sub>G\<close>}.
\end{proof}
\end{lemma}

And thus with Lemma~\ref{ipda.Lang_subst_Lang_G}:

\begin{theorem}\label{ipda.Lang_eq_Lang_G}
@{prop \<open>gpda.Lang I\<^sub>G = LangS G\<close>}
\qed
\end{theorem}

We have now defined a nondeterministic GPDA that works with items and accepts exactly its underlying 
language. With this IPDA definition, we can see one of the benefits of extending \<open>G\<close>: if we were to 
define the set of final states to be the set of all complete items of the form @{term \<open>[S \<rightarrow> \<alpha> \<cdot> ]\<close>},
the automaton could encounter a final state before the end of a computation. Since \<open>S'\<close> is in not 
on the RHS of any production, this scenario can not occur after the extension.\par

As a final remark, it is worth pointing out that our proof differs somewhat from that of
Wilhelm et al. Rather than of Lemma~\ref{derives_imp_completes}, they prove a special case 
thereof~\cite[p. 61]{Wilhelm}, namely the statement
\begin{quote}
\textit{For each derivation \<open>Prods G \<turnstile> [Nt A] \<Rightarrow> \<alpha> \<Rightarrow>* map Tm w\<close> with \<open>A :: 'n\<close>, 
\[ @{prop \<open>([A \<rightarrow> \<cdot> \<alpha>] # \<rho>, w @ v) \<turnstile>* ([A \<rightarrow> \<alpha> \<cdot> ] # \<rho>, v)\<close>} \] 
for arbitrary \<open>\<rho> :: item list\<close> and \<open>v :: 't list\<close>.}
\end{quote}

However, this statement is too weak, as we will soon need the stronger lemma we have proved instead.\<close>

section \<open>The Characteristic Finite Automaton and the Canonical LR(0) Automaton\<close>
(*<*)
end
context Extended_Cfg
begin

notation (latex output) char_fa
  (\<open>\<^latex>\<open>\ensuremath{\mathrm{char}(G)}\<close>\<close>)
(*>*)

text \<open>In this section, we will show the relation between rightmost derivations and the IPDA in more 
detail, as well as the define finite automata that the canonical LR(0) parser will operate with.\<close>

text\<open>In order to construct our parser, we will first define an automaton that can determine possible
reductions. We again define a nondeterministic automaton, in this case an NFA, that we will call the  
\concept{characteristic finite automaton} to \<open>G\<close>. We base our finite automata on the formalization
thereof by Paulson~\<^cite>\<open>Paulson\<close>.

\begin{definition}[Characteristic finite automaton]
The characteristic finite automaton to \<open>G\<close> is the @{typ \<open>(('n, 't) sym, ('n, 't) item) nfa\<close>}:
\begin{multline*}
  @{const char_fa} = \<open>\<lparr>nfa.states = It G', init = {[S' \<rightarrow> [] \<cdot> [Nt S]]},\<close>\\
  \<open>final = completes (It G'), nxt = \<Delta>, eps = \<E>\<rparr>\<close>
\end{multline*}
with
% Fix style?
@{term [display, margin = 80] \<open>\<Delta>(q, a) = (case q of [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<Rightarrow> 
  if a = Y \<and> (X, \<alpha>@Y#\<beta>) \<in> Prods G' then {[X \<rightarrow> \<alpha>@[Y] \<cdot> \<beta>]}
  else {} | _ \<Rightarrow> {})\<close>}
and
\begin{multline*}
\<open>\<E> = {([X \<rightarrow> \<alpha> \<cdot> Nt Y # \<beta>], [Y \<rightarrow> [] \<cdot> \<gamma>])\<close>\\
  \<open>| X \<alpha> Y \<beta> \<gamma>. (X, \<alpha> @ Nt Y # \<beta>) \<in> Prods G' \<and> (Y, \<gamma>) \<in> Prods G'}\<close>
\end{multline*}
\end{definition}

The characteristic finite automaton can therefore perform shifting and expanding transitions akin to 
those of the IPDA @{const ipda.I\<^sub>G}. The inability of @{const char_fa} of performing reducing 
transitions is compensated by the fact that it is able to shift nonterminals as well as terminals. 
@{const char_fa} can therefore reach an item in @{term \<open>It G\<close>} by read the concatenation of prefixes 
leading to this particular item, as explained by Wilhelm et al.~\cite[p. 103]{Wilhelm}

We will now work towards showing certain equivalences between @{const char_fa} computations, rightmost 
derivations, and @{const ipda.I\<^sub>G} computations.\<close>

subsection \<open>Rightmost Chains\<close>

text \<open>Wilhelm et al. informally assert that for a rightmost derivation 
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>, there exists a decomposition
of the form
\begin{equation}\label{WSH rm chain}
\begin{split}
\<open>Prods G'\<close>\ & \<open>\<turnstile> [Nt S'] \<Rightarrow>r \<alpha>\<^sub>1 @ Nt X\<^sub>1 # \<beta>\<^sub>1 \<Rightarrow>r* \<alpha>\<^sub>1 @ Nt X\<^sub>1 # map Tm v\<^sub>1\<close>\\
        & \<open>\<Rightarrow>r \<alpha>\<^sub>1\<alpha>\<^sub>2 @ Nt X\<^sub>2 # \<beta>\<^sub>2 @ map Tm v\<^sub>1\<close>\\ 
        & \<open>\<Rightarrow>r* ... \<Rightarrow>r* \<alpha>\<^sub>1\<alpha>\<^sub>2 ... \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n ... v\<^sub>2v\<^sub>1)\<close>\\
        & \<open>\<Rightarrow>r (\<alpha>\<^sub>1 ... \<alpha>\<^sub>n) \<alpha>\<beta> @ map Tm (v\<^sub>n ... v\<^sub>1)\<close>.
\end{split}
\end{equation}
where \<open>X\<^sub>n = A\<close> and terms such as \<open>\<alpha>\<^sub>1\<alpha>\<^sub>2\<close>, \<open>\<alpha>\<beta>\<close>, or \<open>v\<^sub>2v\<^sub>1\<close> denote the concatenation of the individual 
\<open>\<alpha>\<^sub>1, \<alpha>\<^sub>2, \<alpha>, \<beta> :: syms\<close>, and  \<open>v\<^sub>2, v\<^sub>1 :: 't list\<close>. 

We will now formalize this concept by defining \concept{rightmost chains} inductively. If sentential 
form \<open>\<alpha>\<close> reaches sentential form \<open>\<beta>\<close> with rightmost chain \<open>\<rho>\<close> under production set \<open>P\<close>, we write 
@{prop \<open>P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>\<close>}. We define the following rules for some fixed \<open>P\<close>:
\begin{itemize}
\item @{thm rm_chain.refl} 
\item 
@{thm [mode=Rule] rm_chain.step}
\end{itemize}

\begin{example}
By our definition of rightmost chains, we would write \eqref{WSH rm chain} as
\begin{equation*}
\begin{split}
\<open>P \<turnstile> [Nt S']\<close> & \<open>\<midarrow>[\<close>X_{n-1} \<open>\<rightarrow> \<alpha>\<^sub>n \<cdot> Nt X\<^sub>n # \<beta>\<^sub>n] #\<close> \cfitem{X_{n-2}}{\alpha_{n-1}}{Nt X_{n-1} 
  \# \beta_{n-1}}\\
              & 
\begin{multlined}
\# ... \<open># [S' \<rightarrow> \<alpha>\<^sub>1 \<cdot> Nt X\<^sub>1 # \<beta>\<^sub>1] # []\<rightarrow>\<close>\\ 
  \<open>\<alpha>\<^sub>1 @ \<alpha>\<^sub>2 @ \<sigma> \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n @ ... @ v\<^sub>2 @ v\<^sub>1)\<close>.
\end{multlined}
\end{split}
\end{equation*}
\end{example}

\<close>



section \<open>The Canonical LR(0) Parser\<close>

section \<open>Conclusion\<close>
subsection \<open>Discussion of future work\<close>

(*<*)
end
end
(*>*)
