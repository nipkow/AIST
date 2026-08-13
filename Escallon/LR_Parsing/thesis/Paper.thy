(*<*)
theory Paper
  imports 
    "LR0_Base.LR0_Parser"
    "HOL-Library.LaTeXsugar"
begin

section \<open>setup\<close>

declare [[names_short, show_question_marks = false]]

definition sub :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "sub X n \<equiv> X"

notation sub (\<open>\<^latex>\<open>\ensuremath{\<close>_\<^latex>\<open>_{\<close>_\<^latex>\<open>}}\<close>\<close>)

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
is an example for this.

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

abbreviation \<open>I\<^sub>G \<equiv> Extended_Cfg.IPDA G'\<close>

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
transitivity and the monotonicity. 
Therefore, @{prop \<open>w \<in> LangS G'\<close>}. This completes the proof.
\end{proof}
\end{theorem}

\begin{lemma}[Preservation of reduction]
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
\end{lemma}

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
\concept{complete} items respectively. For both of these kinds of item, we often write the empty 
list implicitly, e.g., instead of @{term \<open>[A \<rightarrow> \<alpha> \<cdot> []]\<close>}, we write @{term \<open>[A \<rightarrow> \<alpha> \<cdot> ]\<close>}. 
Additionally, we denote the set of all complete items in a set of items \<open>I\<close> by @{term \<open>completes I\<close>}:
\begin{equation*}
@{thm completes_def}.
\end{equation*}
An item that is not complete is referred to as \concept{incomplete}, and we correspondingly define
@{const incompletes} as the complement of @{const completes}:
\begin{equation*}
@{abbrev \<open>incompletes I\<close>}.
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
\item \<open>states :: 'q set\<close> is a finite set of \concept{states}.
\item \<open>init :: 'q\<close> is the \concept{initial state} with \<open>init \<in> states\<close>.
\item \<open>final :: 'q set\<close> is a set of \concept{final states} with \<open>final \<subseteq> states\<close>.
\item \<open>nxt :: ('q list \<times> 'a \<times> 'q list) set\<close> is the \concept{reading transition relation}, i.e., 
the relation of transitions that consume the leftmost remaining input symbol.
\item \<open>eps :: ('q list \<times> 'q list) set\<close> is the transition relation for \concept{\epsilon-transitions}, 
i.e., transitions that do not read the input.
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
(*>*)

subsection \<open>Definition\<close>

text \<open>One of the main objectives in the construction of our parser is determinism. Despite the ability of
PDAs of recognizing CFLs, they are non-deterministic in general, which means they are not easily
implemented in practice. In this section, we define the Item Pushdown Automaton to a 
context-free grammar, from which we will later derive a deterministic parser.

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
@{term \<open>R \<subseteq> \<E>\<close>} \concept{reducing} transitions. We denote @{const IPDA} steps by \<open>\<turnstile>I\<close>, \<open>\<turnstile>I*\<close> and
\<open>\<turnstile>I(n)\<close> analogously to the standard symbols. 

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
  \<open>\<turnstile>I\<close>\ @{term \<open>([Y \<rightarrow> \<cdot> \<alpha> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<rho>, w)\<close>}
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

\begin{lemma}[IPDA invariant]\label{ipda.invariant}
@{prop \<open>([init M], u @ v) \<turnstile>I* (rev \<rho>, v)\<close>} implies\\ @{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow>* map Tm u\<close>}.
\begin{proof}
We do a proof by induction on the length \<open>n\<close> of the computation for arbitrary \<open>u, v,\<close> and \<open>\<rho>\<close>.

If @{term "([init M], u @ v) \<turnstile>I(0) (rev \<rho>, v)"}, then
\begin{gather*} 
\<open>[init M] = rev \<rho> = [[S' \<rightarrow> \<cdot> [Nt S]]]\<close> \text{ and } @{prop \<open>u @ v = v\<close>} 
\end{gather*}
hold. This in turn implies @{prop \<open>hist \<rho> = []\<close>} and @{prop \<open>u = []\<close>}. Since
\mbox{@{prop \<open>Prods G \<turnstile> [] \<Rightarrow>* []\<close>}} holds, the invariant holds.

On the other hand, if @{term "([init M], u @ v) \<turnstile>I(Suc n) (rev \<rho>, v)"} for some \<open>n :: nat\<close>,
we do a case distinction on the final step of the computation.

If the last step was a shifting transition there exist \<open>A, \<alpha>, a, \<beta>, \<tau>, a, \<close> and \<open>x\<close> such that
the second to last configuration was of the form
\begin{gather}
@{term \<open>([A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>] # \<tau>, a # v)\<close>}\label{eq:ipda.invariant.shift}
\intertext{and}
@{term \<open>rev \<rho> = [A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>] # \<tau>\<close>}\label{eq:ipda.invariant.rho_shift}.
\end{gather}
This implies the existence of some \<open>y :: 't list\<close> such that the initial input was of the form
\<open>uv = yav\<close>. This, together with \eqref{eq:ipda.invariant.shift}, and the induction hypothesis implies 
\begin{multline*}
\<open>Prods G \<turnstile> hist (rev \<tau> @ [[A \<rightarrow> \<alpha> \<cdot> Tm a # \<beta>]])\<close>\\ 
  \<open>= hist (rev \<tau>) @ \<alpha> \<Rightarrow>* map Tm y\<close>.
\end{multline*}
With \<open>uv = yav\<close> this implies
\begin{align*}
  \<open>Prods G \<turnstile> hist (rev \<rho>)\<close> 
    & {} = \<open>hist (rev \<tau> @ [[A \<rightarrow> \<alpha> @ [Tm a] \<cdot> \<beta>]])\<close>\\
    & {} = \<open>hist (rev \<tau>) @ \<alpha> @ [Tm a]\<close>\\
    & {} = \<open>\<Rightarrow>* map Tm y @ [Tm a] = u\<close>
\end{align*}
The invariant therefore holds.

For the reducing case, we have a second-to-last configuration
\begin{gather}
@{term \<open>([Y \<rightarrow> \<alpha> \<cdot> ] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close>}\label{eq:ipda.invariant.reduce}\\
\intertext{and final configuration} 
@{term \<open>rev \<rho> = [X \<rightarrow> \<beta> @ [Nt Y] \<cdot> \<gamma>] # \<tau>\<close>}\label{eq:ipda.invariant.rho_reduce}
\end{gather}
for some \<open>Y, \<alpha>, X, \<beta>, \<gamma>\<close> and \<open>\<tau>\<close>. By Lemma~\ref{reducing_imp_in_Prods_G}, we know that 
\mbox{@{prop \<open>(Y, \<alpha>) \<in> Prods G\<close>}}. From all this follows that
\begin{equation}\label{eq:ipda.invariant.reduce_rs}
@{prop \<open>Prods G \<turnstile> hist \<rho> \<Rightarrow> hist (rev \<tau>) @ \<beta> @ [Nt A]\<close>}.
\end{equation}
By the induction hypothesis, we also know that @{term \<open>hist (rev \<tau>) @ \<beta> @ [Nt A]\<close>} derives \<open>u\<close>, 
meaning the invariant holds once again by transitivity.

Finally, in the expanding case we have
\begin{gather*}
@{term \<open>([X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>, v)\<close>}
\intertext{and} 
@{prop \<open>rev \<rho> = [Y \<rightarrow> [] \<cdot> \<alpha>] # [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] # \<tau>\<close>}
\end{gather*}
By the induction hypothesis we have once more \<open>Prods G \<turnstile> hist (rev \<tau>) @ \<beta> \<Rightarrow>* map Tm u\<close>. We then 
have
\begin{align*}
\<open>Prods G \<turnstile> hist \<rho>\<close> &\ \<open>= hist ((rev \<tau>) @  [X \<rightarrow> \<beta> \<cdot> Nt Y # \<gamma>] @ [Y \<rightarrow> [] \<cdot> \<alpha>])\<close>\\
&\ \<open>= hist (rev \<tau>) @ \<beta> \<Rightarrow>* map Tm u\<close>. 
\end{align*}
The invariant is therefore satisfied, completing the proof.
\end{proof}
\end{lemma}

\begin{lemma}\label{ipda.Lang_subst_Lang_G}
@{term \<open>gpda.Lang I\<^sub>G \<subseteq> LangS G\<close>}
\begin{proof}
Assume @{prop \<open>w \<in> gpda.Lang I\<^sub>G\<close>}. Then, 
\[ \<open>([init I\<^sub>G], w) =\<close>\ @{prop \<open>([init I\<^sub>G], w @ [])  \<turnstile>I* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>}. \] 
By Lemma~\ref{ipda.invariant}, this implies @{prop \<open>Prods G \<turnstile> hist [final_state] \<Rightarrow>* map Tm w\<close>}.
Since @{prop \<open>hist [final_state] = [Nt S]\<close>}, this proves that @{prop \<open>w \<in> LangS G\<close>}.  
\end{proof}
\end{lemma}

And now, we prove the other direction:

\begin{lemma}\label{completes_Tms}
If @{prop \<open>(A, \<alpha> @ map Tm u @ \<beta>) \<in> Prods G' \<close>}, then 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> map Tm u @ \<beta>]#\<rho>, u@v) \<turnstile>I* ([A \<rightarrow> \<alpha> @ map Tm u \<cdot> \<beta>]#\<rho>, v)\<close>}. \]
\begin{proof}
Trivial by induction on the length of \<open>u\<close>.
\end{proof}
\end{lemma}

\begin{lemma}\label{derives_imp_completes}[Derivation implies IPDA completion]
If 
\[ @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm w\<close>} \] 
and @{prop \<open>(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'\<close>}, then for any \<open>\<rho>, x\<close> holds: 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>@\<gamma>] # \<rho>, w @ x) \<turnstile>I* ([A \<rightarrow> \<alpha>@\<beta> \<cdot> \<gamma>] # \<rho>, x)\<close>}. \]
\begin{proof}
We do a proof by strong induction on the length of the derivation \<open>n\<close>.
If \<open>n = 0\<close>, \<open>\<beta> = map Tm w\<close>, and the implication holds by Lemma~\ref{completes_Tms}.

If \<open>n = Suc m\<close> for some \<open>m :: nat\<close>, there exists at least one nonterminal \<open>X\<close> in \<open>\<beta>\<close>. \<open>\<beta>\<close> is therefore
of the form 
\begin{equation}\label{d_imp_c.b_decomp(1)}
@{prop \<open>\<beta> = \<delta>\<^sub>1 @ Nt X # \<delta>\<^sub>2\<close>}
\end{equation}
for \<open>\<delta>\<^sub>1, \<delta>\<^sub>2 :: syms\<close>. Furthermore, Nipkow et al. have proved
\begin{multline*}
 \<open>P \<turnstile> u @ v \<Rightarrow>(n) w\<close>\\
  \<open>\<longleftrightarrow> (\<exists>n1 n2 w1 w2. n = n1 + n2 \<and> w = w1 @ w2\<close>\\ 
  \<open>\<and> P \<turnstile> u \<Rightarrow>(n1) w1 \<and> P \<turnstile> v \<Rightarrow>(n2) w2)\<close>.
\end{multline*}

By applying this lemma twice, the derivation of \<open>w\<close> can be decomposed such that:
\begin{subequations}
\begin{gather}
@{prop \<open>w = u @ v @ y\<close>}\label{d_imp_c.b_decomp(2)}\\
@{prop \<open>Prods G' \<turnstile> \<delta>\<^sub>1 \<Rightarrow>(i) map Tm u\<close>}\label{d_imp_c.d1}\\
@{prop \<open>Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v\<close>}\label{d_imp_c.X}\\
@{prop \<open>Prods G' \<turnstile> \<delta>\<^sub>2 \<Rightarrow>(k) map Tm y\<close>}\label{d_imp_c.d2}\\
@{prop \<open>n = i + j + k\<close>}.\label{d_imp_c.b_decomp(6)}
\end{gather}
\end{subequations}
For some \<open>u, v, y :: 't list\<close> and \<open>i, j, k :: nat\<close>.

@{prop \<open>Prods G' \<turnstile> [Nt X] \<Rightarrow>(j) map Tm v\<close>} implies @{prop \<open>j > 0\<close>}, since @{prop \<open>j = 0\<close>}
would imply @{prop \<open>[Nt X] = map Tm v\<close>}, which is a contradiction. Furthermore, \eqref{d_imp_c.b_decomp(6)}
implies that \<open>i\<close>, \<open>j\<close> and \<open>k\<close> are all less or equal to \<open>n\<close>. From this and the additional constraint
that \<open>j\<close> cannot be \<open>0\<close>, we know that there are only two cases: either @{prop \<open>j = n\<close>} and \<open>i = k = 0\<close>,
or \<open>i\<close>, \<open>j\<close>, and \<open>k\<close> are strictly less than \<open>n\<close>. We now distinguish these cases.
We can now distinguish two cases:

If \<open>j = n\<close> and \<open>i = k = 0\<close>, 
\begin{gather}\label{d_imp_c.d1u_d2y}
\<open>\<delta>\<^sub>1 = map Tm u\<close> \text{ and } \<open>\<delta>\<^sub>2 = map Tm y\<close>
\end{gather} 
hold by \eqref{d_imp_c.d1} and \eqref{d_imp_c.d2}. \<open>j = n\<close> also implies the existence of some 
\<open>\<beta>' :: syms\<close> such that 
\begin{equation}\label{eq:d_imp_c.stepm}
\<open>Prods G' \<turnstile> [Nt X] \<Rightarrow> \<beta>' \<Rightarrow>(m) map Tm v\<close>.
\end{equation}

By Lemma~\ref{completes_Tms}, and substituting \eqref{d_imp_c.b_decomp(1)}, 
\eqref{d_imp_c.b_decomp(2)}, and \eqref{d_imp_c.d1u_d2y}, @{term \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>] # \<rho>, w @ x)\<close>} reaches
\[ @{term \<open>([A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X # map Tm y @ \<gamma>] # \<rho>, v @ y @ x)\<close>}, \]
and since \<open>X\<close> derives \<open>\<beta>'\<close>, the item \<open>[X \<rightarrow> \<cdot> \<beta>']\<close> can then be pushed onto the stack through an 
expanding transition. \eqref{eq:d_imp_c.stepm} and the induction hypothesis then imply that 
\<open>I\<^sub>G\<close> reaches
\[ @{term \<open>([X \<rightarrow> \<beta>' \<cdot> ] # [A \<rightarrow> \<alpha> @ map Tm u \<cdot> Nt X #  map Tm y @ \<gamma>] # \<rho>, y @ x)\<close>}, \]
since \<open>m < Suc m = n\<close>. \<open>I\<^sub>G\<close> then trivially reaches @{term \<open>([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>] # \<rho>, x)\<close>} after a 
reducing transition and applying Lemma~\ref{completes_Tms} once again.

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
\[ @{prop \<open>([[S' \<rightarrow> \<cdot> [Nt S]]], w) \<turnstile>I* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>}. \] 

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
\[ @{prop \<open>([A \<rightarrow> \<cdot> \<alpha>] # \<rho>, w @ v) \<turnstile>I* ([A \<rightarrow> \<alpha> \<cdot> ] # \<rho>, v)\<close>} \] 
for arbitrary \<open>\<rho> :: item list\<close> and \<open>v :: 't list\<close>.}
\end{quote}

However, this statement is too weak, as we will soon need the stronger lemma we have proved instead.\<close>

subsection \<open>Rightmost Chains\<close>

(*<*) 
end
context Extended_Cfg
begin 
(*>*)

text \<open>Wilhelm et al. informally assert that for a rightmost derivation 
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w \<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>, there exists a decomposition
of the form
\begin{equation}\label{WSH rm chain}
\begin{split}
\<open>Prods G'\<close>\ & \<open>\<turnstile> [Nt S'] \<Rightarrow>r \<alpha>\<^sub>1 @ Nt X\<^sub>1 # \<beta>\<^sub>1 \<Rightarrow>r* \<alpha>\<^sub>1 @ Nt X\<^sub>1 # map Tm v\<^sub>1\<close>\\
        & \<open>\<Rightarrow>r \<alpha>\<^sub>1\<alpha>\<^sub>2 @ Nt X\<^sub>2 # \<beta>\<^sub>2 @ map Tm v\<^sub>1\<close>\\ 
        & \<open>\<Rightarrow>r* ... \<Rightarrow>r* \<alpha>\<^sub>1 ... \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n ... v\<^sub>1)\<close>\\
        & \<open>\<Rightarrow>r (\<alpha>\<^sub>1 ... \<alpha>\<^sub>n) \<alpha>\<beta> @ map Tm (v\<^sub>n ... v\<^sub>1)\<close>.
\end{split}
\end{equation}
where \<open>X\<^sub>n = A\<close>. In the above expression, we omit most concatenation operators @{term \<open>(@)\<close>} for 
compactness. Instead, we denote concatenation by juxtaposition (such as in \<open>(\<alpha>\<^sub>1 ... \<alpha>\<^sub>n) \<alpha>\<beta>\<close> instead
of \<open>(\<alpha>\<^sub>1 @ ... @ \<alpha>\<^sub>n) @ \<alpha> @ \<beta>\<close>).

We now formalize this concept by defining \concept{rightmost chains} inductively. If sentential 
form \<open>\<alpha>\<close> reaches sentential form \<open>\<beta>\<close> with rightmost chain \<open>\<rho>\<close> under production set \<open>P\<close>, we write 
@{prop \<open>P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>\<close>}. For a fixed \<open>P\<close>, we define a \concept{reflexive} rule:
\begin{gather*}
@{thm rm_chain.refl}\\
\intertext{and a \concept{step} rule:}
@{thm [mode=Rule] rm_chain.step}
\end{gather*}

\begin{example}\label{ex:rm_chain}
By our definition of rightmost chains, we would write \eqref{WSH rm chain} as~\footnote{Note that we 
once more omit most concatenation operators, replacing them by juxtaposition.}
\begin{multline*}
\<open>P \<turnstile> [Nt S'] \<midarrow>[\<close> @{term \<open>sub X (n-1)\<close>}\ \<open>\<rightarrow> \<alpha>\<^sub>n \<cdot> Nt X\<^sub>n # \<beta>\<^sub>n] # [\<close> @{term \<open>sub X (n-2)\<close>}\ \<open>\<rightarrow>\<close>\ 
@{term \<open>sub \<alpha> (n-1)\<close>}\ \<open>\<cdot>\<close>\ 
  @{term \<open>Nt (sub X (n-1)) # (sub \<beta> (n-1))\<close>}]\\ 
  \<open># ... # [[S' \<rightarrow> \<alpha>\<^sub>1 \<cdot> Nt X\<^sub>1 # \<beta>\<^sub>1]]\<rightarrow>r* \<alpha>\<^sub>1 ... \<alpha>\<^sub>n @ Nt X\<^sub>n # map Tm (v\<^sub>n...v\<^sub>1)\<close>.
\end{multline*}
\end{example}
We will now show the equivalence between rightmost chains and rightmost derivations.

\begin{lemma}\label{rm_chain_imp_derivers}
If @{prop \<open>P \<turnstile> \<alpha> \<midarrow>\<rho>\<rightarrow>r* \<beta>\<close>}, then @{prop \<open>P \<turnstile> \<alpha> \<Rightarrow>r* \<beta>\<close>}
\begin{proof}
By induction on the structure of the rightmost chain.
\end{proof}
\end{lemma}

\begin{lemma}\label{derivern_singleton_imp_produced}
If @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # \<beta>\<close>}, there exists a step in the rightmost derivation 
where \<open>\<alpha>\<close> was fully derived, \<open>X\<close> was produced, and the string to the right of \<open>X\<close> derives \<open>\<beta>\<close>. More 
formally: there exist \<open>m :: nat\<close>, \<open>\<alpha>', \<alpha>'', \<beta>' :: syms\<close>, \<open>B :: 'n\<close> and \<open>v :: 't list\<close> such that
\begin{gather*}
@{prop \<open>m < Suc n\<close>}\\
@{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(m) \<alpha>' @ Nt B # map Tm v\<close>}\\
@{prop \<open>P \<turnstile> \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm v\<close>}\\
@{prop \<open>\<alpha> = \<alpha>' @ \<alpha>''\<close>}\\
@{prop \<open>P \<turnstile> \<beta>' @ map Tm v \<Rightarrow>r* \<beta>\<close>}.
\end{gather*}
\begin{proof}
We do a proof by strong induction on @{term \<open>Suc n\<close>} for arbitrary \<open>\<alpha>\<close> and \<open>\<beta>\<close>. We now distinguish
the two usual cases of \<open>n\<close>:

If \<open>n = 0\<close>, the implication holds for @{prop \<open>m = 0\<close>}, @{prop \<open>\<alpha>' = []\<close>}, @{prop \<open>v = []\<close>}, 
  @{prop \<open>\<alpha>'' = \<alpha>\<close>}, @{prop \<open>\<beta>' = \<beta>\<close>} and @{prop \<open>A = B\<close>}. 

For the case where @{prop \<open>n = Suc k\<close>} for some \<open>k\<close>, the derivation is of the form
\begin{multline}\label{prodd_stepn}
\<open>P \<turnstile> [Nt A] \<Rightarrow>r(n) \<alpha>' @ Nt B # map Tm v \<Rightarrow>r \<alpha>' @ \<gamma> @ map Tm v\<close>\\ 
\<open>= \<alpha> @ Nt X # \<beta>\<close>
\end{multline}

We now distinguish two further cases: \<open>X\<close> is in \<open>\<gamma>\<close>, meaning \<open>\<alpha>'\<close> is a prefix of \<open>\<alpha>\<close>, or 
\<open>X\<close> is in \<open>\<alpha>'\<close> and not in \<open>\<gamma>\<close>, meaning \<open>\<alpha>\<close> is a prefix of \<open>\<alpha>'\<close>.

If \<open>X\<close> is in \<open>\<gamma>\<close> and \<open>\<alpha>'\<close> is a prefix of \<open>\<alpha>\<close>, there exist \<open>\<delta>, \<zeta> :: syms\<close> such that \<open>\<gamma> = \<delta> @ Nt X # \<zeta>\<close>,
\<open>\<alpha> = \<alpha>' @ \<delta>\<close> and \<open>\<beta> = \<zeta> @ map Tm v\<close>. The implication then holds for \<open>m = n\<close>.

If \<open>X\<close> is in \<open>\<alpha>'\<close> and not in \<open>\<gamma>\<close>, there exist \<open>\<delta>, \<zeta> :: syms\<close> such that \<open>\<alpha>' = \<delta> @ Nt X # \<zeta>\<close>. From
\eqref{prodd_stepn} we then get
\[ @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(n) \<delta> @ Nt X # \<zeta> @ Nt B # map Tm v\<close>}. \]
Furthermore, since \<open>Suc k = n < Suc n\<close>, and due to the fact that our induction hypothesis holds for 
arbitrary \<open>\<alpha>\<close> and \<open>\<beta>\<close>, we can apply it for \<open>\<delta>\<close> and \<open>(\<zeta> @ Nt B # map Tm v)\<close>, by which the implication holds.
\end{proof}
\end{lemma}

\begin{lemma}\label{derivern_Suc_singleton_imp_rm_chain}
If @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v\<close>}, then there exists a rightmost chain of the 
form 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[B \<rightarrow> \<alpha>' \<cdot> Nt X # \<beta>] # \<rho>\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>}. \]
\begin{proof}
We do a proof by strong induction on @{term \<open>Suc n\<close>} for arbitrary \<open>\<alpha>, X,\<close> and \<open>v\<close>. Furthermore, 
we do a case distinction on \<open>n\<close>:

If \<open>n = 0\<close>, then 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[[A \<rightarrow> \<alpha> \<cdot> Nt X # map Tm v]]\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>}. \]

Otherwise, let \<open>n = Suc m\<close> for some \<open>m\<close>. From 
\[ @{prop \<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc n) \<alpha> @ Nt X # map Tm v\<close>}, \]
there exist \<open>\<beta>, B, u,\<close> and \<open>\<gamma>\<close> such that 
\begin{gather}
\<open>P \<turnstile> [Nt A] \<Rightarrow>r(Suc m) \<beta> @ Nt B # map Tm u \<Rightarrow>r \<beta> @ \<gamma> @ map Tm u\<close>\label{der_rm.Suc_steps}\\
\intertext{and}
@{prop \<open>\<beta> @ \<gamma> @ map Tm u = \<alpha> @ Nt X # map Tm v\<close>}.\label{der_rm.bgu}
\end{gather}
Since \<open>Suc m = n < Suc n\<close>, by the induction hypothesis, \eqref{der_rm.Suc_steps} implies the
existence of some \<open>\<rho>\<close> such that 
\begin{equation}\label{der_rm.ih}
@{prop \<open>P \<turnstile> [Nt A] \<midarrow>\<rho>\<rightarrow>r* \<beta> @ Nt B # map Tm u\<close>}.
\end{equation}
Since \<open>B\<close> derives \<open>\<gamma>\<close> in the last step of the derivation, we now distinguish two more cases:
either \<open>X\<close> was produced by \<open>B\<close> in this final derivation step, meaning @{prop \<open>Nt X \<in> set \<gamma>\<close>}, 
or, if \<open>B\<close> did not produce \<open>X\<close>, \<open>X\<close> was already in the sentential form before the final step.

If @{prop \<open>Nt X \<in> set \<gamma>\<close>}, note that \eqref{der_rm.bgu} implies that \<open>X\<close> is the rightmost nonterminal
in the sentential form, meaning there exists an instance of \<open>X\<close> followed exclusively by terminals. 
Therefore, and with the fact that \<open>X\<close> is in \<open>\<gamma>\<close>, and \<open>\<gamma>\<close> itself is only followed by terminals, there 
exist \<open>\<delta> :: syms\<close> and \<open>w :: 't list\<close> such that @{prop \<open>\<gamma> = \<delta> @ Nt X # map Tm w\<close>} and @{prop \<open>w @ u = v\<close>}. 
With \eqref{der_rm.ih} this implies
\begin{multline}\label{der_rm.True}
\<open>P \<turnstile> [Nt A] \<midarrow>[B \<rightarrow> \<delta> \<cdot> Nt X # map Tm w] # \<rho>\<rightarrow>r*\<close>\\ 
  \<open>\<beta> @ \<delta> @ Nt X # map Tm (w @ u)\<close>.
\end{multline}
Furthermore, we have
\begin{multline*} 
\<open>\<beta> @ \<delta> @ Nt X # map Tm (w @ u) = \<beta> @ \<gamma> @ map Tm u\<close>\\ 
  \<open>= \<alpha> @ Nt X # map Tm v\<close>
\end{multline*}
From @{prop \<open>w @ u = v\<close>}, this implies @{prop \<open>\<beta> @ \<delta> = \<alpha>\<close>}, meaning \eqref{der_rm.True} is exactly the rightmost chain we 
were trying to construct.

On the other hand, if @{prop \<open>Nt X \<notin> set \<gamma>\<close>}, the fact that \<open>X\<close> is the rightmost nonterminal in 
\<open>\<beta> @ \<gamma> @ map Tm u\<close> implies the existence of \<open>\<delta> :: syms\<close> and \<open>y, z :: 't list\<close> such that
\begin{gather}
\<open>\<beta> = \<delta> @ Nt X # map Tm y\<close>\label{der_rm.b_dec}\\
\<open>\<gamma> = map Tm z\<close>\label{der_rm.g_tms}\\
\<open>v = y @ z @ u\<close>.\label{der_rm.yzu}
\end{gather}
By Lemma~\ref{derivern_singleton_imp_produced}, \<open>n = Suc m\<close> implies the existence of some sentential 
form @{term \<open>\<alpha>' @ Nt C # map Tm w\<close>} such that
\begin{gather} 
\begin{multlined}\label{der_rm.prodd(1)}
\<open>P \<turnstile> [Nt A] \<Rightarrow>r(k) \<alpha>' @ Nt C # map Tm w\<close>\\
  \<open>\<Rightarrow>r \<alpha>' @ \<alpha>'' @ Nt X # \<beta>' @ map Tm w\<close>
\end{multlined}\\
\intertext{and}
\<open>P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm y @ Nt B # map Tm u\<close>\label{der_rm.prodd(2)}
\end{gather}
for \<open>\<delta> = \<alpha>' @ \<alpha>''\<close> and \<open>k < Suc m\<close>. Moreover, with \eqref{der_rm.Suc_steps}, \eqref{der_rm.g_tms}, 
and \eqref{der_rm.yzu}, we have 
\begin{equation}\label{der_rm.suffix_derivers_v}
@{prop \<open>P \<turnstile> \<beta>' @ map Tm w \<Rightarrow>r* map Tm v\<close>}
\end{equation}
From \eqref{der_rm.bgu},\eqref{der_rm.b_dec}, \eqref{der_rm.g_tms}, and \eqref{der_rm.yzu} we also 
have 
\begin{equation} \label{der_rm.da}
  @{prop \<open>\<delta> = \<alpha>\<close>}.
\end{equation}

Since our induction hypothesis only holds for a nonzero number of steps, we need to do a case 
distinction on the \<open>k\<close> steps in \eqref{der_rm.prodd(1)}.

If \<open>k = 0\<close>, \eqref{der_rm.prodd(1)} implies that \<open>\<alpha>' = [] = w\<close> and \<open>A = C\<close>. This in turn implies
that \<open>\<delta> = \<alpha>''\<close>. With \eqref{der_rm.da} and \eqref{der_rm.suffix_derivers_v}, this implies 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[[A \<rightarrow> \<alpha>'' \<cdot> Nt X # \<beta>']]\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>}. \]

If, on the other hand, \<open>k = Suc j\<close> for some \<open>j\<close>, we can apply the induction hypothesis for \<open>C\<close>
with \eqref{der_rm.prodd(1)}, i.e., there exists some \<open>\<rho>\<close> such that
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>\<rho>\<rightarrow>r* \<alpha>' @ Nt C # map Tm w\<close>}. \]
We can then use \eqref{der_rm.prodd(1)}, \eqref{der_rm.suffix_derivers_v}, \eqref{der_rm.da}, and 
\<open>\<delta> = \<alpha>' @ \<alpha>''\<close> to show that 
\[ @{prop \<open>P \<turnstile> [Nt A] \<midarrow>[C \<rightarrow> \<alpha>'' \<cdot> Nt X # \<beta>'] # \<rho>\<rightarrow>r* \<alpha> @ Nt X # map Tm v\<close>} \]
holds, completing the proof.
\end{proof}
\end{lemma}

Wilhelm et al.~\cite[p. 107]{Wilhelm} furthermore claim that if @{term \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>', w)\<close>}
reaches the final configuration @{term \<open>([[S' \<rightarrow> \<cdot> [Nt S]]], [])\<close>}, then \<open>\<rho>'\<close> is of the form
\[ \<open>\<rho>' = [\<close> @{term \<open>sub X (n-1)\<close>}\ \<open>\<rightarrow> \<alpha>\<^sub>n \<cdot> Nt X\<^sub>n # \<beta>\<^sub>n] # ... # [[S' \<rightarrow> \<alpha>\<^sub>1 \<cdot> Nt X\<^sub>1 # \<beta>\<^sub>1]]\<close> \]
for some \<open>n \<ge> 0\<close> and \<open>X\<^sub>n = A\<close>~\footnote{We have adapted the original claim to our own notation for 
the sake of consistency and clarity.} It is worth noting that this structure of \<open>\<rho>'\<close> is essentially
the same as that of the item list in a rightmost chain (cf. Example~\ref{ex:rm_chain}). Therefore,
if some \<open>\<sigma> :: item list\<close> is part of some rightmost chain, we will be able to derive the same 
structure that Wilhelm et al. describe. We will now work towards proving that IPDA stacks reaching 
a final configuration have a stack that corresponds to some rightmost chain.\<close>

(*<*)
end
context Extended_Cfg
begin

interpretation I: ipda G IPDA 
  by (fact ipda_IPDA)

(*>*)

text\<open>
\begin{lemma}\label{reaches_final_imp_last_is_init_or_final}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])\<close>}, then the last element in
@{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>\<close>} is either @{term \<open>[S' \<rightarrow> \<cdot> [Nt S']]\<close>} or @{term I.final_state}.
\begin{proof}
By backwards induction on the length of the computation, making a case distinction on whether
the first step is shifting, expanding, or reducing in the transitive case.
\end{proof}
\end{lemma}

\begin{lemma}\label{step_reaches_final_imp_S}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> @ \<sigma>, u) \<turnstile>I (I.final_state # \<sigma>, v)\<close>},
then 
\[ \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho> = [[S \<rightarrow> \<alpha> \<cdot> ], [S' \<rightarrow> \<cdot> [Nt S]]]\<close> \]
\begin{proof}
By case distinction on the three types of transition.
\end{proof}
\end{lemma}

\begin{lemma}\label{rm_chain_Cons_imp_prod_rightmost}
If @{prop \<open>P \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> Nt B # \<beta>] # \<rho>\<rightarrow>r* \<gamma>\<close>}, there exist \<open>\<delta> :: syms\<close> and \<open>u, v, w :: 't list\<close> 
such that 
\begin{gather*}
@{prop \<open>\<gamma> = \<delta> @ Nt B # map Tm w\<close>}\\
@{prop \<open>P \<turnstile> \<beta> \<Rightarrow>r* map Tm u\<close>}\\
\intertext{and}
@{prop \<open>w = u @ v\<close>}
\end{gather*}
\begin{proof}
Trivial by rule inversion.
\end{proof}
\end{lemma}

\begin{lemma}\label{rm_chain_second_produces_hd}
If 
\[ @{prop \<open>Prods G' \<turnstile> \<alpha>\<^sub>0 \<midarrow>[A \<rightarrow> \<alpha> \<cdot> Nt B # \<beta>] # i # \<rho>\<rightarrow>r* \<gamma>\<close>}, \]
then there exist \<open>X, \<alpha>',\<close> and \<open>\<beta>'\<close> such that \<open>i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']\<close>
\begin{proof}
By rule inversion, we know there exist \<open>\<alpha> :: syms\<close> and \<open>v, u :: 't list\<close> where
\begin{equation}
@{prop \<open>Prods G' \<turnstile> \<alpha>\<^sub>0 \<midarrow>i # \<rho>\<rightarrow>r* \<alpha> @ Nt A # map Tm v\<close>}.
\end{equation}
The implication then follows by a second rule inversion on this rightmost chain, using the other
facts that we have obtained from the first rule inversion.
\end{proof}
\end{lemma}

\begin{lemma}\label{ipda_reaches_final_imp_rm_chain}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])\<close>}, then either
\begin{gather*}
@{prop \<open>\<rho> = []\<close>},
\intertext{or there exist \<open>\<sigma> :: item list\<close>, \<open>X :: 'n\<close> and \<open>\<alpha>', \<beta>', \<gamma> :: syms\<close> such that}
@{prop \<open>\<rho> = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'] # \<sigma>\<close>} \text{ and } @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<gamma>\<close>}. 
\end{gather*}
\begin{proof}
We do a proof by backwards induction on the length of the computation of @{const I\<^sub>G} for arbitrary 
\<open>A, \<alpha>, \<beta>, \<rho>\<close>, and \<open>w\<close>.

The reflexive case is trivial since it implies directly that \<open>\<rho> = []\<close>.

For the transitive case, the computation is of the form
\begin{equation}\label{ipda_rmc.step}
\<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I ([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v) \<turnstile>I* ([\<close>@{term I.final_state}\<open>], [])\<close>
\end{equation}
for some \<open>B\<close>, \<open>\<gamma>\<close>, \<open>\<delta>\<close>, \<open>\<tau>\<close> and \<open>v\<close>. This is due to the fact that in all three types of transition, 
\<open>I\<^sub>G\<close> replaces a nonzero amount of topmost stack symbols by a nonempty list, meaning that a step can 
never lead to an empty stack. We can now apply the induction hypothesis on the shorter computation 
starting on @{term \<open>([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v)\<close>}, meaning \<open>\<tau>\<close> is either empty, or it is in some rightmost
chain as we already described.

If \<open>\<tau> = []\<close>, by Lemma~\ref{reaches_final_imp_last_is_init_or_final} we know that @{term \<open>[B \<rightarrow> \<gamma> \<cdot> \<delta>]\<close>}
is either the initial or final state. We can prove this item cannot be the initial state by 
contradiction using \eqref{ipda_rmc.step}. Therefore, @{term \<open>[B \<rightarrow> \<gamma> \<cdot> \<delta>]\<close>} must be the final state 
@{term I.final_state}, implying that @{prop \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] = [S \<rightarrow> \<alpha> \<cdot> ]\<close>} and 
@{prop [source] \<open>\<rho> = [S' \<rightarrow> \<cdot> [Nt S]] # []\<close>} by Lemma~\ref{step_reaches_final_imp_S} for \<open>\<sigma> = []\<close>. 
Therefore, \<open>\<rho>\<close> fulfills our claim.

For the second case, \<open>\<tau>\<close> has the structure
\begin{gather}\label{ipda_rm.ih}
@{prop \<open>\<tau> = [X \<rightarrow> \<alpha>' \<cdot> Nt B # \<beta>'] # \<sigma>\<close>}\\  
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<tau>\<rightarrow>r* \<zeta>\<close>}
\end{gather}
for some \<open>X :: 'n\<close>, \<open>\<alpha>', \<beta>, \<zeta> :: syms\<close> and \<open>\<sigma> :: item list\<close>. We can now do a case distinction on the 
step @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I ([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v)\<close>}.

If the transition is shifting, we have @{prop \<open>A = B\<close>} and @{prop \<open>\<rho> = \<tau>\<close>}. The implication holds by 
\eqref{ipda_rm.ih}.

If the transition is reducing, we know that 
\begin{equation}\label{ipda_rm.r}
@{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) = ([A \<rightarrow> \<alpha> \<cdot> []] # [B \<rightarrow> \<theta> \<cdot> Nt A # \<delta>] # \<tau>, w)\<close>},
\end{equation}
for some \<open>\<theta>\<close> where @{prop \<open>\<gamma> = \<theta> @ [Nt A]\<close>}, meaning that \<open>(B, \<theta> @ Nt A # \<delta>)\<close> is in \<open>Prods G'\<close>. By
Lemma~\ref{rm_chain_Cons_imp_prod_rightmost}, \eqref{ipda_rm.ih} implies that \<open>\<zeta>\<close> is of the form
\[ @{prop \<open>\<zeta> = \<zeta>' @ Nt B # map Tm u\<close>} \]
for some \<open>\<zeta>'\<close> and \<open>u\<close>. Moreover, since \<open>G'\<close> is reduced, there exists a \<open>v :: 't list\<close> that the string \<open>\<delta>\<close> can derive.  
With the fact that \<open>B\<close> produces \<open>\<theta> @ Nt A # \<delta>\<close>, we can extend the chain in \eqref{ipda_rm.ih} by the 
item @{term \<open>[B \<rightarrow> \<theta> \<cdot> Nt A # \<delta>]\<close>}, i.e.
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<midarrow>[B \<rightarrow> \<theta> \<cdot> Nt A # \<delta>] # \<tau>\<rightarrow>r*\<close> 
  \\\<open>\<zeta>' @ \<theta> @ Nt A # map Tm (v@u)\<close>
\end{multline*}
The implication therefore holds by \eqref{ipda_rm.r}.

If the transition is expanding, we have
\begin{equation}\label{ipda_rm.e}
 @{prop \<open>([B \<rightarrow> \<gamma> \<cdot> \<delta>] # \<tau>, v) = ([B \<rightarrow> [] \<cdot> \<delta>] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w)\<close>}.
\end{equation}
If \<open>\<rho> = []\<close>, the implication holds directly. Otherwise, if \<open>\<rho> = i # \<sigma>\<close> for some \<open>i\<close> and \<open>\<sigma>\<close>, 
from \eqref{ipda_rm.ih} and \eqref{ipda_rm.e} we get
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>[A \<rightarrow> \<alpha> \<cdot> \<beta>] # i # \<sigma>\<rightarrow>r* \<zeta>\<close>}. \]
Finally, by inversion of the step rule for rightmost chains, this implies the existence of some \<open>\<eta>\<close> 
such that
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<eta>\<close>},\] 
and by Lemma~\ref{rm_chain_second_produces_hd}, \<open>i\<close> is of the form @{prop \<open>i = [Z \<rightarrow> \<gamma>' \<cdot> Nt A # \<delta>']\<close>} 
for some \<open>Z, \<gamma>'\<close>, and \<open>\<delta>'\<close>. With the existence of \<open>\<eta>\<close> and this structure of \<open>i\<close>, the proof is 
complete.
\end{proof}
\end{lemma}

We have now formalized the notion of rightmost chains, proved their existence is equivalent to that
of generic rightmost derivations, and proved that every IPDA stack that reaches an accepting state 
has such a chain of items on the stack. With these chains, we are now able to describe a very 
well-behaved relation between the nonterminals directly to the right of the bullet and the 
nonterminal to the left of the arrow of the preceding item: for any two neighboring items
in the chain's item list 
\[ ...  \<open># [A \<rightarrow> \<alpha> \<cdot> \<beta>] # [B \<rightarrow> \<gamma> \<cdot> \<delta>] #\<close> ... \]
we know that @{prop \<open>hd \<delta> = Nt A\<close>}, meaning the LHS nonterminal of each item is produced in the 
successor item. Wilhelm et al. use these chains on multiple occasions only informally. By formalizing
them, we will be able in the future to induct on them more rigorously, which will be of utmost 
importance in the coming section.\<close>

section \<open>The Characteristic Finite Automaton and the Canonical \<open>LR(0)\<close> Automaton\<close>
(*<*)
notation (latex output) char_fa
  (\<open>\<^latex>\<open>\ensuremath{\mathrm{char}(G)}\<close>\<close>)
(*>*)

text \<open>In this section, we will show the relation between rightmost derivations and the IPDA in more 
detail, as well as the define finite automata that the canonical LR(0) parser will operate with.\<close>

text\<open>In order to construct our parser, we will first define an automaton that can determine possible
reductions. We again define a nondeterministic automaton, in this case an NFA, that we will call the  
\concept{characteristic finite automaton} to \<open>G\<close>. We base our finite automata on the formalization
thereof by Paulson~\<^cite>\<open>Paulson\<close>.\<close>

subsection \<open>The Characteristic Finite Automaton\<close>

text\<open>\begin{definition}[Characteristic finite automaton]
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
those of the IPDA @{const I\<^sub>G}. Meanwhile, the @{const char_fa} shifting nonterminals corresponds to
reducing transitions in @{const I\<^sub>G}. @{const char_fa} can therefore reach an item in @{term \<open>It G\<close>} 
by read the concatenation of the prefixes that @{const I\<^sub>G} processed in order to reach this 
particular item, as explained by Wilhelm et al~\cite[p. 103]{Wilhelm}.

Wilhelm et al.~\cite[p. 104]{Wilhelm} present a theorem stating the equivalence of three statements 
as one of the main results in the \<open>LR(0)\<close> section of the book, Theorem 3.4.1, describing the relation 
between @{const char_fa}, rightmost derivations, and the IPDA. They make the following claim, which
we have adapted to match our own notation:

\begin{quote}
\textit{Let \<open>G\<close> be a CFG and \<open>\<gamma> :: syms\<close>. The following three statements are equivalent:
\begin{enumerate}
\item There exists a computation
\[ @{prop \<open>([S' \<rightarrow> \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
of the characteristic finite automaton @{const char_fa}.
\item There exists a rightmost derivation 
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w\<close>\\
  \<open>\<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>
\end{multline*}
with @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}.
\item There exists a computation
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([[S' \<rightarrow> [Nt S] \<cdot> ]], [])\<close>} \]
of the IPDA @{const \<open>I\<^sub>G\<close>} such that @{prop \<open>\<gamma> = hist (rev \<rho>) @ \<alpha>\<close>} holds.
\end{enumerate}}
\end{quote}

It is worth noting that we have modified the order of the statements, since in the book there
is a mismatch between the numbering of each statement in the claim and in the proof. We will now
refer to these claims exclusively as we have numbered them.

Wilhelm et al. prove the claim by a circular proof of the form \<open>(1) \<Longrightarrow> (2) \<Longrightarrow> (3) \<Longrightarrow> (1)\<close>. This 
claim, however, is not a consequence of the chain of implications that was proved; we will now
look at each implication more closely. There are certain typographic errors in the proofs which we 
will not address; we infer the author's intention in such cases. 

Implication \<open>(1) \<Longrightarrow> (2)\<close> uses existing constants \<open>S'\<close> and \<open>S\<close>, and fixes variables \<open>\<gamma>\<close> and
@{prop \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>] \<in> It G'\<close>}. The conclusion then shows that there exist some \<open>\<gamma>' :: syms\<close> and
\<open>w :: 't list\<close> for which the rightmost derivation exists and @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}. The proof itself
is flawed: the authors induct on the number of \<open>\<epsilon>\<close>-transitions instead, and the 
induction hypothesis, which is only established if the remaining input is @{term \<open>[]\<close>}, is
applied on a configuration with nonempty remaining input. Furthermore, the base case does not consider 
the scenario where @{const char_fa} reads \<open>Nt S\<close> from the input before making any \<open>\<epsilon>\<close>-transitions. 
We will later prove the implication in a different manner. 

Implication  \<open>(2) \<Longrightarrow> (3)\<close> fixes \<open>\<gamma>', A, \<alpha>, \<beta>,\<close> and \<open>w\<close>, and shows the existence of some \<open>\<rho>\<close>. Note
that the conclusion of \<open>(1) \<Longrightarrow> (2)\<close> proved only an existentially quantified \<open>w\<close>; this is an 
important distinction that we will address later.
In the statements @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>} and @{prop \<open>\<gamma> = hist (rev \<rho>) @ \<alpha>\<close>}, variable \<open>\<gamma>\<close> is completely
meaningless; it bears no relation to the \<open>\<gamma>\<close> fixed in (1) since no \<open>\<gamma>\<close> is defined in (2) nor in (3). 
Therefore, this can be simplified to 
@{prop \<open>\<gamma>' = hist (rev \<rho>)\<close>}. Furthermore, the proof for this implication assumes that 
\[ @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>r* map Tm v\<close>} \]
for some \<open>v :: 't list\<close>. It is not clear what the statement intends to say, and this assumption
might need to be included in statement (2) for it to be correct, depending on what was meant 
originally: since \<open>w\<close> is fixed, the statement of the existence of the IPDA computation seems to 
be stating that the computation holds for the same fixed \<open>w\<close>, but this is not true; as we will see, 
the statement holds for input @{term \<open>v@w\<close>}, where \<open>v\<close> is again the word derived by \<open>\<beta>\<close>. If \<open>w\<close> is 
meant to be existentially quantified in the conclusion, this is not a problem, but this is not made
clear by the authors. The proof of the statement is also incorrect: it uses the book's informal
equivalent of our formalized rightmost chains, but states that one proves by induction that a 
configuration with topmost stack symbol 
\[ @{term \<open>[sub X (n-1) \<rightarrow> \<alpha>\<^sub>n \<cdot> Nt A # \<beta>\<^sub>n]\<close>} \]
and input \<open>w\<close> reaches the final configuration~\footnote{the authors naturally state the structure of
the entire stack, but only the topmost symbol is relevant for our argument.}. However, this 
configuration would first push the initial item @{term \<open>[A \<rightarrow> \<cdot> \<alpha> @ \<beta>]\<close>} onto the stack (this is the 
only possibility based on our assumptions about \<open>A\<close>), and since we haven't made any assumptions 
regarding \<open>\<alpha>\<close>, we cannot make any further claims. It is therefore necessary for the topmost stack 
item to be @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} to be able to make any claims about the computation.

The proof of the final implication is fundamentally correct; it fixes @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} as 
usual, as well as \<open>\<rho>\<close> and \<open>w\<close>. The conclusion does not contain any new variables since \<open>\<gamma>\<close> is just 
a shorthand for @{term \<open>hist (rev \<rho>) @ \<alpha>\<close>} in practice. However, the main issue with this proof is,
as we previously mentioned, that the \<open>w\<close> in the premise is not in the conclusion at all. In order 
to prove the equivalence of (2) and (3), we need the statement \<open>(2) \<Longrightarrow> (3)\<close>, which we have already
proved, and \<open>(3) \<Longrightarrow> (2)\<close>, which we prove through (1), i.e., \<open>(3) \<Longrightarrow> (1) \<Longrightarrow> (2)\<close>. However, since
the original \<open>w\<close> in (3) is lost in (1), it is a new existentially quantified \<open>w\<close> in (2). This means
that the statements (2) and (3) are not equivalent for the same \<open>w\<close>, as it reads in the book, 
but for two different existentially quantified words \<open>u\<close> and \<open>v\<close>. However, the 
main results that we need from the theorem to formalize our parser still hold after addressing 
these errors. A corrected version Theorem 3.4.1:

\begin{theorem}\label{char_derivers_ipda_iffs}[Equivalences between @{const char_fa}, rightmost derivations, and @{const I\<^sub>G}]
The following statements are equivalent:
\begin{enumerate}
\item There exists a computation 
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>' @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
of the characteristic finite automaton @{const char_fa}.
\item There exists a rightmost derivation
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm u\<close>\\
  \<open>\<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm u\<close>.
\end{multline*}
for some \<open>u :: 't list\<close>.
\item There exists a computation 
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v) \<turnstile>I* ([I.final_state], [])\<close>} \]
of the IPDA @{const I\<^sub>G} for some \<open>\<rho> :: item list\<close> and \<open>v :: 't list\<close> such that 
@{prop \<open>hist (rev \<rho>) = \<gamma>'\<close>} holds.
\end{enumerate}
\end{theorem}

We will now work towards proving this theorem. We denote @{const char_fa} transition steps by \<open>\<turnstile>c\<close>, 
and as usual, the reflexive transitive closure by \<open>\<turnstile>c*\<close>, and \<open>n\<close>-length computations by \<open>\<turnstile>c(n)\<close>. 
We first need two lemmas about @{const char_fa}:

\begin{lemma}\label{char_reachable_imp_substring}
If @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], \<delta>)\<close>}, there exists a \<open>\<zeta>\<close> such that 
\[ @{prop \<open>\<gamma> = \<zeta> @ \<alpha> @ \<delta>\<close>} \]
\begin{proof}
By induction on the length of the computation, making a case distinction on whether the last step is 
a read transition or an \<open>\<epsilon>\<close>-transition in the inductive step.
\end{proof} 
\end{lemma}

And now we begin our circular proof:

\begin{lemma}[Step 1]\label{char_imp_derivers}
If there exists a computation of @{const char_fa}
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>}, \]
Then there exist \<open>\<gamma>' :: syms\<close> and \<open>w :: 't list\<close> for which there is a rightmost derivation of the
form
\[ \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w \<Rightarrow> \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close> \]
with @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}.
\begin{proof}
We do a proof by induction over the length \<open>n\<close> of the computation for arbitrary \<open>\<gamma>, \<alpha>, \<beta>, \<close> and \<open>A\<close>. 

If \<open>n = 0\<close> the implication holds trivially by reflexivity.

If \<open>n = Suc m\<close> for some \<open>m\<close>, we do a case distinction on the last step of the computation.

If the last step is a read transition, it is of the form
\[ @{prop \<open>([A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>], [Y]) \<turnstile>c ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
for \<open>\<alpha>'\<close> with @{prop \<open>\<alpha> = \<alpha>' @ [Y]\<close>}. With Lemma~\ref{char_reachable_imp_substring}, this implies 
that 
\[ @{prop \<open>\<gamma> = \<delta> @ \<alpha>' @ [Y]\<close>} \] 
for some \<open>\<delta>\<close>, and therefore
\[ @{prop\<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<delta> @ \<alpha>') \<turnstile>c(m) ([A \<rightarrow> \<alpha>' \<cdot> Y # \<beta>], [])\<close>}. \]
By the induction hypothesis, this implies
\begin{multline*} 
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w\<close>\\ 
\<open>\<Rightarrow> \<delta>  @ \<alpha>' @ Y # \<beta> @ map Tm w\<close>,
\end{multline*}
and the implication holds with @{prop \<open>\<alpha> = \<alpha>' @ [Y]\<close>}.

If the last step is an \<open>\<epsilon>\<close>-transition, the last step is of the form 
\[ @{prop \<open>([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], []) \<turnstile>c ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>}, \]
which implies that @{prop \<open>\<alpha> = []\<close>}. By the IH we then have
\begin{multline}\label{char_der.ih}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt X # map Tm w\<close>\\
  \<open>\<Rightarrow>r \<gamma>' @ \<alpha>' @ Nt A # \<beta>' @ map Tm w\<close>
\end{multline}
with @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>'\<close>}. Moreover, since \<open>G'\<close> is reduced, there exists a \<open>v :: 't list\<close> such that
\[ @{prop \<open>Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm v\<close>}. \]
From this and \eqref{char_der.ih} we have
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm (v@w)\<close>\\ 
\<open>\<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm (v@w)\<close>.
\end{multline*}
Lastly @{prop \<open>\<alpha> = []\<close>}, implies that @{prop \<open>\<gamma> = \<gamma> @ \<alpha>\<close>}. Therefore, this rightmost derivation 
completes the proof.
\end{proof}
\end{lemma}

We now move on towards proving the second step, for which we first show an auxiliary lemma.

\begin{lemma}\label{deriver_imp_IPDA_comp}
If @{prop \<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r \<alpha>@\<beta>\<close>} and @{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v\<close>}, there exists a 
computation
\[ @{prop \<open>([[S' \<rightarrow> \<alpha> \<cdot> \<beta>]], v) \<turnstile>I* ([I.final_state], [])\<close>} \]
\begin{proof}
Since the only possible production for \<open>S'\<close> is \<open>(S',[Nt S])\<close>, we have @{prop \<open>[Nt S] = \<alpha> @ \<beta>\<close>}.
The proof is then trivial by distinguishing the cases where \<open>\<alpha> = [Nt S]\<close> and \<open>\<beta> = []\<close>, and vice-versa,
using Theorem~\ref{ipda.Lang_eq_Lang_G}.
\end{proof}
\end{lemma}

\begin{lemma}[Step 2]\label{derivers_imp_ipda}
If there exists a rightmost derivation 
\begin{gather*}
\begin{multlined}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma> @ Nt A # map Tm w\<close>\\ 
\<open>\<Rightarrow>r \<gamma> @ \<alpha> @ \<beta> @ map Tm w\<close>
\end{multlined}
\intertext{with}
@{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v\<close>},
\end{gather*}
then there exists an @{const IPDA} computation 
\begin{gather*}
@{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v@w) \<turnstile>I* ([I.final_state], [])\<close>}
\intertext{with}
@{prop \<open>hist (rev \<rho>) = \<gamma>\<close>}.
\end{gather*}
\begin{proof}
We begin by distinguishing the cases where @{prop \<open>n = 0\<close>} and @{prop \<open>n > 0\<close>}.

If @{prop \<open>n = 0\<close>}, we have @{prop \<open>S' = A\<close>}, \<open>\<gamma> = w = []\<close>, and @{prop \<open>\<alpha>@\<beta> = [Nt S]\<close>}. The 
computation then exists by Lemma~\ref{deriver_imp_IPDA_comp}.

If @{prop \<open>n > 0\<close>}, Lemma~\ref{derivern_Suc_singleton_imp_rm_chain} implies the existence of some
\<open>\<rho>\<close> with
\[ @{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<rho>\<rightarrow>r* \<gamma> @ Nt A # map Tm w\<close>}. \]
We can now do an induction on \<open>\<rho>\<close> for arbitrary \<open>\<gamma>, \<alpha>, \<beta>, A, w,\<close> and \<open>v\<close>, akin to the proof by 
Wilhelm et al.

If @{prop \<open>\<rho> = []\<close>}, we again have @{prop \<open>S' = A\<close>}, \<open>\<gamma> = w = []\<close>, and @{prop \<open>\<alpha>@\<beta> = [Nt S]\<close>}, and 
the proof is analogous to the case of @{prop \<open>n = 0\<close>}.

If @{prop \<open>\<rho> = i # \<sigma>\<close>} for some \<open>i\<close> and \<open>\<sigma>\<close>, by rule inversion we know that 
\begin{equation}\label{der_ipda.i}
@{prop \<open>i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']\<close>}
\end{equation}
for some \<open>X\<close>, \<open>\<alpha>'\<close>, \<open>A\<close> and \<open>\<beta>'\<close>. Furthermore, the chain is such that
\begin{gather*}
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>\<sigma>\<rightarrow>r* \<alpha>'' @ Nt X # map Tm v'\<close>}\\
@{prop \<open>Prods G' \<turnstile> \<alpha>'' @ Nt X # map Tm v' \<Rightarrow>r \<alpha>'' @ \<alpha>' @ Nt A # \<beta>' @ map Tm v'\<close>}\\
\intertext{with}
@{prop \<open>Prods G' \<turnstile> \<beta>' \<Rightarrow>r* map Tm u\<close>}\label{der_ipda.bv}\\
@{prop \<open>u @ v' = w\<close>} \text{, and } @{prop \<open>\<alpha>'' @ \<alpha>' = \<gamma>\<close>}
\end{gather*}
for some \<open>\<alpha>'', u,\<close> and \<open>v'\<close>. By the IH, all this implies the existence of a \<open>\<rho>'\<close> where
\begin{gather}
@{prop \<open>([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<rho>', u@v') \<turnstile>I* ([I.final_state], [])\<close>}\\
\intertext{and}
@{prop \<open>hist (rev \<rho>') = \<alpha>''\<close>}.
\end{gather}
Lastly, we can show with Lemma~\ref{derives_imp_completes} that \<open>I\<^sub>G\<close> with configuration 
\[ @{term \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'] # \<rho>', v @ w)\<close>} \]
reaches @{term \<open>([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<rho>', u@v')\<close>}, completing the proof.
\end{proof}
\end{lemma}

It is worth noting that, as opposed to Wilhelm et al., we only assume 
@{prop \<open>Prods G' \<turnstile> \<beta> \<Rightarrow>* map Tm v\<close>} for the above lemma, since specifying this as a rightmost 
derivation makes no difference. We will now prove further properties about @{const char_fa} which 
we will need for the third step.

\begin{lemma}\label{reaches_final_imp_completes}
If @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I(n) ([I.final_state], [])\<close>} holds, 
there exist a \<open>v :: 't list\<close> and \<open>i, j :: nat\<close> such that
\begin{gather*} 
\<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I(i) ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # \<rho>, v) \<turnstile>I(j) ([\<close>@{term I.final_state}\<open>], [])\<close>
\intertext{and}
@{prop \<open>i + j = n\<close>}
\end{gather*}
\begin{proof}
We do a proof by strong induction on \<open>n\<close> for arbitrary \<open>A, u, \<alpha>, \<beta>,\<close> and \<open>\<rho>\<close>.

If \<open>n = 0\<close>, the implication is trivial.

If \<open>n = Suc m\<close> for some \<open>m\<close>, we do a case distinction on the first step of the computation. 

If the first step is a shifting or a reducing transition, the implication holds by the induction
hypothesis.

If the first step is an expanding transition, there exist \<open>Y :: 'n\<close> and \<open>\<gamma> :: syms\<close> with
\begin{gather}
\<open>\<beta> = Nt Y # \<gamma>\<close>\label{rf_comp.b}
\intertext{and}
\begin{multlined}
\<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I ([Y \<rightarrow>  \<cdot> \<gamma>] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u)\<close>\\
  \<open>\<turnstile>I(m) ([\<close>@{term I.final_state}\<open>], [])\<close>.
\end{multlined}
\end{gather}
By the IH, this implies the existence of some \<open>v :: 't list\<close> and \<open>i, j :: nat\<close> with 
\begin{gather*}
\begin{multlined}
\<open>([Y \<rightarrow>  \<cdot> \<gamma>] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, u) \<turnstile>I(i) ([Y \<rightarrow> \<gamma> \<cdot> ] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v)\<close>\\
  \<open>\<turnstile>I(j) ([\<close>@{term I.final_state}\<open>], [])\<close>
\end{multlined}
\intertext{and}
\<open>i + j = m\<close>.
\end{gather*}
The first step of the computation
\[ \<open>([Y \<rightarrow> \<gamma> \<cdot> ] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v) \<turnstile>I(j) ([\<close>@{term I.final_state}\<open>], [])\<close> \]
is invariably the reducing transition
\[ @{prop \<open>([Y \<rightarrow> \<gamma> \<cdot> ] # [A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, v) \<turnstile>I ([A \<rightarrow> \<alpha> @ [Nt Y] \<cdot> \<gamma>] # \<rho>, v)\<close>} \]
by \eqref{rf_comp.b}. Since the RHS of this transition reaches the accepting configuration in
\<open>j - 1 < n\<close> steps, we can use the IH again to finish the proof.
\end{proof}
\end{lemma}

\begin{lemma}\label{char_steps_consume}
If @{prop \<open>(A, \<alpha> @ \<beta> @ \<gamma>) \<in> Prods G'\<close>}, @{const char_fa} computes
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta> @ \<gamma>], \<beta> @ \<delta>) \<turnstile>c* ([A \<rightarrow> \<alpha> @ \<beta> \<cdot> \<gamma>], \<delta>)\<close>} \]
for any \<open>\<delta>\<close>.
\begin{proof}
Trivial by induction on \<open>\<beta>\<close> for arbitrary \<open>\<alpha>\<close>.
\end{proof}
\end{lemma}

And finally, we can prove the final step.

\begin{lemma}[Step 3]\label{ipda_imp_char}
If there exists a computation of \<open>I\<^sub>G\<close>
\[ @{prop \<open>([A \<rightarrow> \<alpha> \<cdot> \<beta>] # \<rho>, w) \<turnstile>I* ([I.final_state], [])\<close>}, \]
then there also exists a @{const char_fa} computation of the form
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ \<alpha>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>}. \]
\begin{proof}
We induct on \<open>\<rho>\<close> for arbitrary \<open>A, \<alpha>, \<beta>\<close> and \<open>w\<close>.

If \<open>\<rho> = []\<close>, @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} is either the initial or the final state by 
Lemma~\ref{reaches_final_imp_last_is_init_or_final}. The implication can then be proved by 
distinguishing these two cases.

If \<open>\<rho> = i # \<sigma>\<close>, we know by Lemma~\ref{ipda_reaches_final_imp_rm_chain} that
\begin{gather}\label{ipda_char.chain}
@{prop \<open>i = [X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>']\<close>}\\
@{prop \<open>Prods G' \<turnstile> [Nt S'] \<midarrow>i # \<sigma>\<rightarrow>r* \<gamma>\<close>}
\end{gather}
For some \<open>X :: 'n\<close>, and \<open>\<alpha>', \<beta>, \<gamma> :: syms\<close>. Furthermore, by Lemma~\ref{reaches_final_imp_completes}, 
our initial assumption of the accepting computation implies the existence of some \<open>v\<close> with
\[ @{prop \<open>([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<sigma>, v) \<turnstile>I* ([I.final_state], [])\<close>} \]
Since in the LHS of this computation the topmost stack itemcomplete, the only possible first step
is a reducing transition, meaning 
\begin{multline}\label{ipda_char.red}
@{prop \<open>([A \<rightarrow> \<alpha> @ \<beta> \<cdot> []] # i # \<sigma>, v) \<turnstile>I ([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'] # \<sigma>, v)\<close>}\\
  \<open>\<turnstile>I*\<close>\ @{term \<open>([I.final_state], [])\<close>}
\end{multline}
by \eqref{ipda_char.chain}. With the IH, and substituting @{prop \<open>\<rho> = i # \<sigma>\<close>} and 
\eqref{ipda_char.chain}, we now have
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ [Nt A]) \<turnstile>c* ([X \<rightarrow> \<alpha>' @ [Nt A] \<cdot> \<beta>'], [])\<close>}. \]
By a case distinction on the final step of this computation, we know that the initial configuration
reaches @{term \<open>([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], [Nt A])\<close>} immediately before the final step. Since only the
prefix @{term \<open>hist (rev \<rho>)\<close>} of the input is consumed, the computation is independent from the
remaining string. Therefore, the computation
\begin{equation}\label{ipda_char.calc}
@{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], hist (rev \<rho>) @ \<alpha>) \<turnstile>c* ([X \<rightarrow> \<alpha>' \<cdot> Nt A # \<beta>'], \<alpha>)\<close>}
\end{equation}
also exists. Furthermore \eqref{ipda_char.red} implies that \mbox{@{term \<open>(A, \<alpha> @ \<beta>) \<in> Prods G'\<close>}} 
by the definition of the \<open>I\<^sub>G\<close> transition relations. Therefore, \eqref{ipda_char.calc} continues with
\[ \<open>... \<turnstile>c ([A \<rightarrow> [] \<cdot> \<alpha> @ \<beta>], \<alpha>)\<close>. \]
The RHS can then reach our target configuration by Lemma~\ref{char_steps_consume}, completing the
proof of both the Lemma and, along with Lemmas~\ref{char_imp_derivers} and \ref{derivers_imp_ipda},  
the proof of Theorem~\ref{char_derivers_ipda_iffs}.
\end{proof}
\end{lemma}

We now define the notion of \concept{reliable prefixes}:

\begin{definition}[Reliable prefix]
\<open>\<gamma>\<close> is a reliable prefix for item @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} if there exists a rightmost derivation 
\begin{multline*}
\<open>Prods G' \<turnstile> [Nt S'] \<Rightarrow>r* \<gamma>' @ Nt A # map Tm w\<close>\\ 
  \<open>\<Rightarrow>r \<gamma>' @ \<alpha> @ \<beta> @ map Tm w\<close>
\end{multline*}
such that @{prop \<open>\<gamma> = \<gamma>' @ \<alpha>\<close>}. Alternatively, we say that the item @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} is 
\concept{valid} for \<open>\<gamma>\<close>. We therefore also define the set of all valid items for \<open>\<gamma>\<close>:
\[ @{thm valids_def}. \]
\end{definition}

\begin{theorem}\label{char_eq_reliable_prefix}[Equivalence of @{const char_fa} computations and reliable prefixes]
There exists a @{const char_fa} computation
\[ @{prop \<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma>) \<turnstile>c* ([A \<rightarrow> \<alpha> \<cdot> \<beta>], [])\<close>} \]
if and only if @{term \<open>[A \<rightarrow> \<alpha> \<cdot> \<beta>]\<close>} is valid for \<open>\<gamma>\<close>.
\begin{proof}
This is a consequence of Lemmas~\ref{char_imp_derivers}, \ref{derivers_imp_ipda}, and 
\ref{ipda_imp_char}, using the fact that since \<open>G'\<close> is reduced, any sentential form derived from 
@{term \<open>S'\<close>}, or a substring thereof, derives some \<open>v :: 't list\<close>.
\end{proof}
\end{theorem}

By this Theorem, we get two more interesting results:

\begin{corollary}
@{const char_fa} accepts exactly the set of reliable prefixes to complete items.
\qed
\end{corollary}

\begin{lemma}
The set of states reachable by @{const char_fa} after reading \<open>\<gamma>\<close> is exactly @{term \<open>valids \<gamma>\<close>}.
\qed
\end{lemma}\<close>

subsection \<open>The Canonical \<open>LR(0)\<close> Automaton\<close>

text\<open>Now that we have defined @{const char_fa} and proved several useful properties, we can finally
define a deterministic automaton that our parser can use. Since @{const char_fa} is an NFA, we 
define the \concept{canonical \<open>LR(0)\<close> automaton} @{const LR\<^sub>0} as the DFA resulting from the powerset 
construction restricted to reachable states. The automaton is once more defined using Paulson's 
theory~\<^cite>\<open>Paulson\<close>. We now show some properties we will need in our parser.

\begin{lemma}\label{char_fa_nxts_is_shifts}
For @{prop \<open>Q \<subseteq> It G'\<close>} holds the equality
\[ @{prop \<open>(\<Union>i \<in> Q. nfa.nxt char_fa i A) = {[X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q}\<close>}. \] 
\begin{proof}
We fix some @{prop \<open>i \<in> (\<Union>i \<in> Q. nfa.nxt char_fa i A)\<close>}, and we need to show that it is in the set 
on the RHS of the equation. Since \<open>i\<close> is in the union, there exists a \<open>j\<close> such that
@{prop \<open>i \<in> nfa.nxt char_fa j A\<close>}. Since the \<open>nxt\<close> relation is only defined for incomplete items, 
\<open>j\<close> must be of the form @{term \<open>[X \<rightarrow> \<alpha> \<cdot> B # \<beta>]\<close>}. 
@{prop \<open>i \<in> {[X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q}\<close>} then follows trivially by the 
definition of the \<open>nxt\<close> transition function.

For the converse, there exists some @{prop \<open>[X \<rightarrow> \<alpha> \<cdot> A # \<beta>] \<in> Q\<close>} for which 
@{prop \<open>i = [X \<rightarrow> \<alpha> @ [A] \<cdot> \<beta>]\<close>}. With @{prop \<open>Q \<subseteq> It G'\<close>}, this implies @{prop \<open>i \<in> It G'\<close>},
and @{prop \<open>i \<in> (\<Union>i \<in> Q. nfa.nxt char_fa i A)\<close>} follows directly by definition of \<open>nxt\<close>.

\end{proof}
\end{lemma}

\begin{lemma}\label{eps_reliable_preserved}
If \<open>i\<close> is valid for some \<open>\<gamma> :: syms\<close>, and for some item \<open>k\<close> 
\[ @{prop \<open>(i, k) \<in> (nfa.eps char_fa)\<^sup>*\<close>} \] 
holds, then \<open>k\<close> is also valid for \<open>\<gamma>\<close>.
\begin{proof}
The proof is by backward induction on the number of \<open>\<epsilon>\<close>-transition steps using 
Theorem~\ref{char_eq_reliable_prefix}.
\end{proof}
\end{lemma}

\begin{lemma}\label{dfa_LR0_nxt_is_epsclo_of_shift}
For any state of \<open>LR\<^sub>0\<close> @{prop \<open>Q\<close>} and a symbol \<open>Y\<close>, 
@{term \<open>dfa.nxt LR\<^sub>0 Q Y\<close>} is equivalent to the set
\[ @{term \<open>char_fa.epsclo {[X \<rightarrow> \<alpha> @ [Y] \<cdot> \<beta>]|X \<alpha> \<beta>. [X \<rightarrow> \<alpha> \<cdot> Y # \<beta>] \<in> Q}\<close>} \]
where @{term \<open>char_fa.epsclo P\<close>} denotes the \<open>\<epsilon>\<close>-closure of set \<open>P\<close> for @{const char_fa}.
\begin{proof}
Follows by the definition of the \<open>nxt\<close> function of the DFA resulting from the powerset construction,
as well as Lemma~\ref{char_fa_nxts_is_shifts}.
\end{proof}
\end{lemma}

\begin{lemma}\label{nxt_dfa_LR0_shift_is_valids_app}
If @{prop \<open>valids \<gamma> \<in> dfa.states LR\<^sub>0\<close>}, then
\[ @{prop \<open>dfa.nxt LR\<^sub>0 (valids \<gamma>) X = valids (\<gamma> @ [X])\<close>} \]
\begin{proof}
By Lemma~\ref{dfa_LR0_nxt_is_epsclo_of_shift}, @{term \<open>dfa.nxt LR\<^sub>0 (valids \<gamma>) X\<close>} is equivalent to 
the set
\[ @{term \<open>char_fa.epsclo {[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]|A \<alpha> \<beta>. [A \<rightarrow> \<alpha> \<cdot> X # \<beta>] \<in> valids \<gamma>}\<close>}. \]
We will abbreviate this set as \<open>\<E>\<close>.

First, we will show that \<open>\<E>\<close> is a subset of @{term \<open>valids (\<gamma> @ [X])\<close>} by 
Lemma~\ref{eps_reliable_preserved}.

We now show that @{term \<open>valids (\<gamma> @ [X])\<close>} is a subset of \<open>\<E>\<close> to complete the proof.

We assume @{prop \<open>i \<in> valids (\<gamma> @ [X])\<close>}, which means that either
\<open>i\<close> is a complete item, or a incomplete item of the form 
\[ @{term \<open>[A \<rightarrow> \<alpha> @ [X] \<cdot> \<beta>]\<close>}. \]
We now distinguish these two cases.

If \<open>i\<close> is complete, we know it is a reachable state of @{const char_fa}. We show by induction on the 
length of the @{const char_fa} computation from the initial state to \<open>i\<close> that there exists an item 
@{term \<open>[Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>]\<close>} such that
\begin{equation*}
\<open>([S' \<rightarrow> [] \<cdot> [Nt S]], \<gamma> @ [X]) \<turnstile>c* ([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], []) \<turnstile>c* (i, [])\<close>
\end{equation*}
We can then show that @{prop \<open>i \<in> \<E>\<close>} by Theorem~\ref{char_eq_reliable_prefix} and the fact
that @{prop \<open>([Y \<rightarrow> \<delta> @ [X] \<cdot> \<zeta>], i) \<in> (nfa.eps char_fa)\<^sup>*\<close>}, using Lemma~\ref{eps_reliable_preserved}
once again.
\end{proof}
\end{lemma}

And now, we can finally define our parser.\<close>

section \<open>The Canonical \<open>LR(0)\<close> Parser\<close>
subsection \<open>Definition\<close>
subsubsection \<open>Finiteness of the Transition Relations\<close>
subsection \<open>\<open>LR(0)\<close>-Adequate and Inadequate States\<close>
subsection \<open>\<open>LR(k)\<close> Grammars\<close>
subsubsection \<open>Definition\<close>
subsubsection \<open>Equivalence with \<open>LR(0)-Adequate States\<close>\<close>
subsubsection \<open>Preservation of the \<open>LR(k)\<close> Condition in Extended Grammars\<close>
subsection \<open>Language Equivalence of \<open>P\<^sub>0\<close> and its Grammar\<close>
subsubsection \<open>Stack Words: Proving Soundness\<close>
subsubsection \<open>The Shift-Reduce Pushdown Automaton: Proving Completeness\<close>

section \<open>Conclusion\<close>
subsection \<open>Discussion of future work\<close>

(*<*)
end
end
(*>*)
