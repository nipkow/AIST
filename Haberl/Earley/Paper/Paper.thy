(*<*)
theory Paper
imports
  "Earley.EarleyWorklist"
  Sugar
begin
declare [[show_question_marks=false]]
declare [[names_short=true]]

definition le_O :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("(_/ \<le>O _/ IF _)" [50, 1000, 0] 0)
where "(f \<le>O g IF Q) = (\<exists>c d. \<forall>x. Q x \<longrightarrow> f x \<le> c * g x + d)"

notation (latex) le_O ("(_/ \<le>\<^bsub>\<^latex>\<open>\\isaconst{\<close>O\<^latex>\<open>}\<close>\<^esub> _/ IF _)" [50, 1000, 0] 0)
abbreviation le_O_True :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool"
   (infix "\<le>O" 50)  where "f \<le>O g \<equiv> (f \<le>O g IF (\<lambda>x. True))"

lemma le_O_trans: "f \<le>O g IF Q \<Longrightarrow> g \<le>O h IF Q \<Longrightarrow> f \<le>O h IF Q"
  apply(auto simp: le_O_def)
  apply(rename_tac cg ch dg dh)
apply(rule_tac x="cg*ch" in exI)
  apply(rule_tac x="cg*dh + dg" in exI)
  apply auto
apply(erule_tac x=x in allE)
apply(erule_tac x=x in allE)
  apply(simp add: algebra_simps)
  by (metis add_mono_thms_linordered_semiring(2) distrib_left dual_order.trans mult_le_mono2)

lemma le_O_trans2: "f \<le>O g IF Q \<Longrightarrow> g \<le>O h \<Longrightarrow> f \<le>O h IF Q"
  by (metis le_O_def le_O_trans)

lemma le_O_id: "f \<le>O f IF Q"
apply(auto simp: le_O_def)
apply(rule_tac x="1" in exI)
apply(rule_tac x="0" in exI)
by simp

lemma le_O_k: "(\<lambda>_. k) \<le>O (\<lambda>n. f n) IF Q"
apply(auto simp add: le_O_def)
apply(rule_tac x="0" in exI)
apply(rule_tac x="k" in exI)
by simp

lemma le_O_add: "g \<le>O f IF Q1 \<Longrightarrow> h \<le>O f IF Q2 \<Longrightarrow> (\<lambda>x. g x + h x) \<le>O f IF (\<lambda>x. Q1 x \<and> Q2 x)"
apply(auto simp add: le_O_def)
subgoal for cg ch dg dh
apply(rule_tac x="cg+ch" in exI)
apply(rule_tac x="dg+dh" in exI)
apply auto
subgoal for x
apply(erule_tac x=x in allE)
apply(erule_tac x=x in allE)
apply(simp add: algebra_simps)
done
done
done

corollary le_O_add1: "g \<le>O f IF Q \<Longrightarrow> h \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x + h x) \<le>O f IF Q"
  using le_O_add by fastforce

corollary le_O_Suc1: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. Suc(g x)) \<le>O f IF Q"
  using le_O_add1[where h = "\<lambda>x. 1", OF _ le_O_k]
  by (metis (no_types, lifting) ext Suc_eq_plus1)

lemma le_O_mult_k: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. k * g x) \<le>O f IF Q"
apply(auto simp add: le_O_def)
apply(rule_tac x="k*c" in exI)
apply(rule_tac x="k*d" in exI)
apply auto
by (metis add_mult_distrib2 mult.assoc mult_le_mono2)

corollary le_O_mult_k2: "g \<le>O f IF Q \<Longrightarrow> (\<lambda>x. g x * k) \<le>O f IF Q"
  by (simp add: ab_semigroup_mult_class.mult.commute le_O_mult_k)

lemma le_O_le_power: assumes "k \<le> l" shows "(\<lambda>n. (f n)^k) \<le>O (\<lambda>n. (f n)^l) IF Q"
  unfolding le_O_def [[metis_instantiate]]
  by (metis add.commute assms less_one linorder_not_le nat_mult_1 order_class.order_eq_iff
      power_increasing trans_le_add1)

lemma le_O_id_le_power: "1 \<le> l \<Longrightarrow> (\<lambda>x. m x) \<le>O (\<lambda>x. (m x)^l) IF Q"
using le_O_le_power by fastforce

lemma le_O_init: "(\<And>x. Q x \<Longrightarrow> f x \<le> g x) \<Longrightarrow> f \<le>O g IF Q"
by (metis add.commute add_0 le_O_def nat_mult_1)

lemma le_O_init3: "(\<And>x y z. Q x y z \<Longrightarrow> f x y z \<le> g x y z)
 \<Longrightarrow> (\<lambda>(x,y,z). f x y z) \<le>O (\<lambda>(x,y,z). g x y z) IF (\<lambda>(x,y,z). Q x y z)"
  by (simp add: le_O_init split_def)

lemmas le_O_Is = le_O_k le_O_Suc1 le_O_add1 le_O_mult_k le_O_mult_k2 le_O_le_power le_O_id_le_power

lemma "(\<lambda>x. 6*x^3 + 3*x^2 + 7*x + 13) \<le>O (\<lambda>n. n^3) IF Q"
by(simp add: le_O_Is)

(* TODO Earley: get rid of next_sym = Some, use not is_final ?? *)
(* in step_fun: rename it*)
(*
abbreviation "iupdate xs i f \<equiv> xs[i := f(xs!i)]"
notation iupdate ("_[[_ := _]]" [1000,0,0] 0)
*)
(* rename? *)
hide_const (open) \<alpha>
hide_const (open) \<beta>

(* TODO modify thy *)
abbreviation "next_sym x s \<equiv> next_symbol x = Some s"
hide_const (open) next_symbol

lemma accepted_def2: "accepted = (\<exists>x \<in> \<S> (length w). is_final (id x))"
unfolding id_def accepted_def by(rule refl)

lemma accepted_complete: "P \<turnstile> [Nt S] \<Rightarrow>* w \<Longrightarrow> accepted"
using Earley_complete
by(auto simp: accepted_def recognized_def \<S>_def)

notation insert_list (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation union_list (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation diff_list (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<close> 65)

notation ItemList ("\<^latex>\<open>\\isaconst{\<close>IL\<^latex>\<open>}\<close>")
notation inv_IL (\<open>\<^latex>\<open>\isaconst{\<close>inv\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation isin (\<open>\<^latex>\<open>\isaconst{\<close>isin\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)

context Earley_Gw
begin

notation ps ("\<^latex>\<open>\\isaconst{\<close>ps\<^latex>\<open>}\<close>")
notation S ("\<^latex>\<open>\\isaconst{\<close>S\<^latex>\<open>}\<close>")

notation set_ItemList (\<open>\<^latex>\<open>\isaconst{\<close>set\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation empty_IL (\<open>\<^latex>\<open>\isaconst{\<close>empty\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>\<close>)
notation insert  (infixr \<open>#\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation union_LIL (infixl \<open>\<union>\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)
notation minus_LIL ("\<^latex>\<open>\\isaconst{\<close>diff\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>LIL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation minus_IL (infixl \<open>-\<^bsub>\<^latex>\<open>\isaconst{\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<close> 65)

lemma Close2L_Predict: "\<lbrakk> \<not> is_complete x; C' = insert_list x C \<rbrakk> \<Longrightarrow>
    Close2L Bs (x#B,C) (diff_list (union_list (Predict_L x (length Bs)) B) C', C')"
  using Close2L.Predict by blast

lemma Close2L_Complete: "\<lbrakk> is_complete x; C' = insert_list x C \<rbrakk> \<Longrightarrow>
    Close2L Bs (x#B,C) (diff_list (union_list (Complete_L Bs x) B) C', C')"
  using Close2L.Complete by blast

notation Predict_L ("\<^latex>\<open>\\isaconst{\<close>Predict\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation Complete_L ("\<^latex>\<open>\\isaconst{\<close>Complete\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation step2L ("\<^latex>\<open>\\isaconst{\<close>step2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation close2L ("\<^latex>\<open>\\isaconst{\<close>close2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

notation Init_L ("\<^latex>\<open>\\isaconst{\<close>Init\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation Scan_L ("\<^latex>\<open>\\isaconst{\<close>Scan\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>L\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation step_fun ("\<^latex>\<open>\\isaconst{\<close>step2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation close2_L ("\<^latex>\<open>\\isaconst{\<close>close2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")
notation bins_L ("\<^latex>\<open>\\isaconst{\<close>bins\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

end

locale Earley_Gw_eps_T2 = Earley_Gw_eps_T where ps = ps for ps :: "('n,'a) prods" +
  assumes dist_ps: "distinct ps"
  assumes T_nth_IL: "T_nth_IL i = i+1"
begin

notation T_step_fun ("\<^latex>\<open>\\isaconst{\<close>T'_step2\<^bsub>\<^latex>\<open>\\isaconst{\\scriptsize \<close>IL\<^latex>\<open>}\<close>\<^esub>\<^latex>\<open>}\<close>")

lemma T_step_fun_bound2:
  "(\<lambda>(Bs,il1,il2). T_step_fun Bs (il1, il2)) \<le>O
(\<lambda>(Bs,il1,il2). L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
    + 7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K)
IF (\<lambda>(Bs,il1,il2). id(list il1 \<noteq> [] \<and> wf_bins1 (map set Bs) \<and>
  (\<forall>i < length Bs. distinct (Bs ! i))) \<and> id(wf1_IL il1 (length Bs) \<and> inv_IL il1 \<and>
  length (froms il1) = Suc (length Bs)) \<and> wf1_IL il2 (length Bs) \<and> inv_IL il2 \<and>
  length (froms il2) = Suc (length Bs))" unfolding id_def
  apply(rule le_O_init3)
  apply(rule T_step_fun_bound)
  using dist_ps apply blast+
  done

lemma aux2: "(n::nat)*(n*m) = n^2 * m"
  by(simp add: power2_eq_square)

lemma T_step_fun_bound3: "(\<lambda>(Bs,il\<^sub>1,il\<^sub>2).
  L * Suc K * Suc (length Bs) * (7 * T_nth_IL (length Bs) + 3* L * Suc K + 7 + 2 * (K + 2))
+ 7 * T_nth_IL (length Bs) + 3 * Suc (length Bs) + 2* L * Suc K + 7 + Suc K) \<le>O
  (\<lambda>(Bs,il1,il2). (length Bs)^2)"
  unfolding split_def T_nth_IL
  by (simp add: le_O_Is algebra_simps aux2 flip: power2_eq_square)

lemmas T_step_fun_bound4 = le_O_trans2[OF T_step_fun_bound2 T_step_fun_bound3]

end

(*>*)

text\<open>

\section{Introduction}

\section{Isabelle Notation} \label{sec:isabelle}

@{term "xs ! n"}

where @{prop "f ` A = {b. \<exists>a\<in>A. f a = b}"}.

@{const the}


\subsection{Context-Free Grammars}

All our types are parameterized by type variables \<open>'n\<close> and \<open>'t\<close>, the types of \concept{nonterminals} and \concept{terminals}.
\concept{Symbols} are a tagged union type:
\begin{quote}
@{datatype sym}
\end{quote}
Variable convention:
% \<open>a, b, c :: 't\<close>, \<open>A, B, C :: 'n\<close> and  \<open>x, y, z :: ('n,'t) sym\<close>.
For compactness we sometimes drop the \<open>'n\<close> and \<open>'t\<close> parameters,
e.g.\ we write \<open>sym\<close> instead of \<open>('n,'t)sym\<close>.

A \concept{production}, informally written \<open>A \<rightarrow> \<alpha>\<close>, is a pair of \<open>A :: 'n\<close> (the @{const lhs})
and \<open>\<alpha>\<close> \<open>::\<close> \mbox{\<open>sym list\<close>} (the @{const rhs}).
We use the following abbreviations:
\begin{quote}
\<open>syms = sym list\<close> \quad \<open>prod = 'n \<times> syms\<close> \quad \<open>Prods = prod set\<close>
\end{quote}
%Variable convention:
%\<open>w :: 't list\<close>; lists over terminal symbols are called \concept{terminal words};
%\<open>\<alpha>, \<beta>, \<gamma> :: syms\<close>; elements of type @{type syms} are called \concept{sentential forms}.

Our theory is primarily based on sets of productions rather than grammars:
the start symbol is irrelevant most of the time.
\emph{For succinctness, we use \concept{grammar} to refer to a set (or list) of productions.}
Moreover, we only restrict to finite sets of productions when necessary.

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
\<close>

text (in Earley_Gw_eps)\<open>
\section{The Story so far}

\cite{NipkowR-CBJ24}

\subsection{Inductive Definition of Earley's Item Sets} \label{sec:Earley}

An Earley recognizer decides if some word is in the language described by a grammar
by generating a set of so-called \emph{items} (\emph{states} in \cite{Earley} and \cite{NipkowR-CBJ24})
and checking if it contains a \emph{final} item.
In the sequel, we fix the following ``global variables'':
\begin{itemize}
\item a grammar @{const P}
\item a start symbol @{const S}
\item an input @{const w} \<open>::\<close> \mbox{@{type "syms"}} consisting only of terminal symbols.
\end{itemize}

An item is a triple @{term "Item r d i"}
where \<open>r = (A, \<alpha>)\<close> is a production from \<open>P\<close>, \<open>d\<close> is a natural number such that@{prop "d \<le> length \<alpha>"},
indicating how far the algorithm has recognized \<open>\<alpha>\<close>,
and \<open>i\<close> is a natural number representing the start index of the subword of \<open>w\<close>
recognized by this item. The three projection functions are
@{const prod}, @{const dot} and @{const from}. We use the letters \<open>x\<close> and \<open>y\<close> for items.

A production \<open>A \<rightarrow> \<alpha>\<close> together
with a @{const dot} \<open>d\<close> is shown as \<open>A \<rightarrow> \<alpha>\<^sub>1\<Zspot>\<alpha>\<^sub>2\<close>, where \<open>\<alpha>\<^sub>1\<close> is the prefix of the first \<open>d\<close> symbols of \<open>\<alpha>\<close> and \<open>\<alpha>\<^sub>2\<close>
is the suffix. We will informally show item as pairs \<open>(A \<rightarrow> \<alpha>\<Zspot>\<beta>, i)\<close>.

Below we need the following auxiliary functions on items that query or modify the dotted
production but not the @{const from} component of the item.
\begin{description}
\item[@{const mv_dot}] moves the dot one position to the right:\\
 \mbox{@{const mv_dot} \<open>(A \<rightarrow> \<alpha>\<Zspot>s\<beta>, i)\<close>} \<open>= (A \<rightarrow> \<alpha>s\<Zspot>\<beta>, i)\<close>
%\smallskip

\item[@{const is_complete} \<open>x\<close>] checks if \<open>x\<close> is of the form \mbox{\<open>(A \<rightarrow> \<alpha>\<Zspot>, i)\<close>}.
%\smallskip

\item[@{const next_sym} \<open>x s\<close>] is true iff \<open>x\<close> is of the form \<open>(A \<rightarrow> \<alpha>\<Zspot>s\<beta>, i)\<close>.
\end{description}
Note that @{prop "next_sym x s"} implies @{prop "\<not> is_complete x"}.

Next we give an abstract inductive definition of @{const Earley}, a set
of pairs @{term "(x,j)"} of items and an index. However, it is more intuitive
to present it as an inductive definition of indexed item sets: we write
\mbox{@{prop "x \<in> \<S> j"}} instead of @{term "(x,j)"} \<open>\<in> Earley\<close>.
In the indexed presentation, we define item sets
\mbox{@{term "\<S> j"}}, @{prop \<open>j \<le> |w|\<close>}, that depend on each other. However, the dependence is in
one direction only: later sets depend on earlier ones, not the other way around.
Thus the @{term "\<S> j"} can be generated in ascending order. This is the subject of the next section
but plays no role now.

The intuitive meaning of @{prop "Item r d i \<in> \<S> j"} is that the subword
@{term "slice i j w"} (which stands for @{term "drop i (take j w)"}) has been recognized.
We call \<open>i\<close> the \emph{start index} and \<open>j\<close> the \emph{end index} (which is excluded).

The four defining rules are: the initial set of items, and one rule for each of the core operations that
expand the set of items: scanning, prediction, and completion.
\begin{quote}
{\sc Init}: @{thm [mode=Rule] Earley.Init[simplified Earley_eq_\<S>]} \quad where
@{thm Init_def}
\end{quote}

\begin{quote}
{\sc Scan}: @{thm [mode=Rule] Earley.Scan[simplified Earley_eq_\<S>]}
\end{quote}

\begin{quote}
{\sc Predict}: @{thm [mode=Rule] Earley.Predict[simplified Earley_eq_\<S>]}\\
where @{thm[margin=75,break] Predict_def}
\end{quote}

\begin{quote}
%{\sc Complete}:\\ {thm [mode=Rule] Earley.Complete[simplified Earley_eq_\<S>]}
{\sc Complete}: $\inferrule{@{thm (prem 1) Earley.Complete[simplified Earley_eq_\<S>]} \\
  @{thm (prem 2) Earley.Complete[simplified Earley_eq_\<S>]}\\\\
  @{thm (prem 3) Earley.Complete[simplified Earley_eq_\<S>]}\\
  @{thm (prem 4) Earley.Complete[simplified Earley_eq_\<S>]}}{@{thm (concl) Earley.Complete[simplified Earley_eq_\<S>]}}$
\end{quote}

%\subsection{Correctness}

Input @{const \<open>w\<close>} is \emph{accepted} if @{term "\<S> (length w)"}
contains a final item \mbox{\<open>(S \<rightarrow> \<gamma>\<Zspot>, 0)\<close>}, i.e.\ the entire input has been recognized:
\begin{quote}
%{const_typ is_final}\smallskip\\
@{thm is_final_def}\\

@{thm accepted_def2}
\end{quote}

%In order to split the rhs of a dotted production into the prefix up to the dot and the suffix
%after the dot we introduce two functions @ {const \<alpha>} and @ {const \<beta>}:
%\begin{quote}
%@{thm \<alpha>_def} \qquad @{thm \<beta>_def}
%\end{quote}

We proved \emph{soundness} and \emph{completeness}
of the item-based acceptance w.r.t.\ the grammar:
\begin{quote}
@{thm accpted_sound} \qquad and \qquad
@{thm accepted_complete}
\end{quote}
%Aside: works also for sentential forms


\subsection{The Standard Definition}
\label{sec:standard}

The standard definition of Earley's algorithm
generates each @{term "\<S> j"} completely before moving on to @{term "\<S> (j+1)"}.
This sequential strategy works because elements of @{term "\<S> j"}
do not depend on @{term "\<S> k"} where \<open>j < k\<close>.
Therefore Earley \cite{Earley} starts with
a more algorithmic formulation. The sets @{term "\<S> 0"}, @{term "\<S> 1"}, \dots, @{term "\<S> (length w)"}
are generated in that order. We follow Jones and define a sequence of \emph{bins} (= item sets),
where the \<open>i\<close>th bin is meant to hold @{term "\<S> i"}.
Function @{const bins} recursively computes the list of bins
\begin{quote}
%{const_typ "bins::bool"}\smallskip\\
@{thm bins.simps}
\end{quote}
In each step, it takes the (currently) last bin, generates a set of new itemss by scanning
\begin{quote}
@{thm Scan_def}
\end{quote}
and closes this set under prediction and completion.
The closure operator @{const Close} takes two arguments: the current list of bins and the
result of scanning. It is defined in analogy with {\sc Predict} and {\sc Complete}:
\begin{quote}
@{thm [mode=Rule] Close.Init}
\qquad
@{thm [mode=Rule] Close.Predict}
\bigskip

@{thm [mode=Rule] Close_Complete}\smallskip\\
@{thm Complete_def}
\end{quote}

In the end we proved the following correctness theorem:
\begin{quote}
@{thm bins_eq_\<S>}
\end{quote}


\subsection{Epsilon-free Closure}

To simplify the computation of @{const Close}, we follow Jones and assume that @{const P}
is epsilon-free in the rest of the paper, i.e. there is no production in @{const P} with an empty @{const rhs}.
In that case, in the completion rule for @{const Close},
@{prop "x \<in> mbox((Bs @ [Close Bs B])) ! from y"} can be simplified to
@{prop "x \<in> Bs ! from y"}. Formally, we define a variant @{const Close1} of @{const Close}
with the simplified completion rule and prove their equivalence:
\begin{quote}
@{thm Close1_eq_Close}
\end{quote}
We mostly ignore wellformedness conditions in this paper but the crucial point of
@{prop "wf_bin1 B (length Bs)"} is that all complete items in \<open>B\<close> have a @{const from}
index of \<open><\<close> @{term \<open>length Bs\<close>}. Thus completion only needs to consult \<open>Bs\<close> and not
the current bin \<open>B\<close>.
Moreover @{term "wf_bins1 Bs"} \<open>\<equiv>\<close> @{prop "\<forall>k < length Bs. wf_bin1 (Bs!k) k"}.


\subsection{One-Pass Closure}
\label{sec:OnePassClosure}

Our previous work concludes with an abstract one-pass formulation of @{const Close1}.
It is still on the level of sets and intentionally nondeterministic.

We formulate the one-pass closure as a transition system @{prop "Bs \<turnstile> (B,C) \<rightarrow> mbox(B',C')"}
where \<open>B\<close>, \<open>C\<close>, \<open>B'\<close>, \<open>C'\<close> are sets of states: \<open>B\<close> is the current set whose closure is to be computed
(the ``worklist''), \<open>C\<close> is the accumulator for the closure, and \mbox{\<open>(B', C')\<close>} is the result
of a) moving some state @{prop "x \<in> B"} to the accumulator (i.e.\ @{prop "C' = C \<union> {x}"}
and b) extending the worklist with all results of prediction or completion (depending on \<open>x\<close>).
The definition is again inductive:
\begin{quote}
@{thm [mode=Rule] Close2.Predict}
\medskip

@{thm [mode=Rule] Close2.Complete}
\end{quote}
Note that a more efficient version of @{term "B \<union> Predict x (length Bs) - (C \<union> {x})"}
would be @{term "(B - {x}) \<union> (Predict x (length Bs) - (C \<union> {x}))"}
(and similarly for @{const Complete})
because \<open>B\<close> and \<open>C\<close> should be disjoint. For simplicity we have ignored this optimization.

The full closure ``algorithm'' consists of the stepwise reduction of \<open>B\<close> to the empty set:
\begin{quote}
@{thm close2_def}
\end{quote}
where \<open>SOME\<close> is Hilbert's epsilon operator: @{term "SOME x. Q"} denotes an arbitrary (but fixed!)
\<open>x\<close> that satisfies \<open>Q\<close> (if such an \<open>x\<close> exists). In our case it does exist, as witnessed by the following
lemma:
\begin{quote}
@{thm [break,margin=70] Close2_NF}
\end{quote}
The proof is by induction on a suitable wellfounded relation (that is based on the fact that
 there are only finitely many wellformed states).
Although it is not obvious, there is a unique \<open>C'\<close> such that @{prop "Bs \<turnstile> (B, C) \<rightarrow>* ({}, C')"},
i.e.\ the result of @{const close2} is independent of which result \<open>SOME\<close> chooses.

As for @{const Close} and @{const Close1}, we can also prove the equivalence of @{const Close1} and @{const close2}:
\begin{quote}
@{thm close2_eq_Close1}
\end{quote}

We will sketch the proof because it is omitted in \cite{NipkowR-CBJ24}.
All proofs are by obvious inductions.

The following lemmas are generally useful:
\begin{quote}
@{thm Close2_steps_disj}\\
@{thm Close2_steps_incr}
\end{quote}

Soundness (@{thm Close2_steps_subset_Close1'}) follows in two obvious steps:
\begin{quote}
@{thm Close2_step_subset_Close1}\\
@{thm Close2_steps_subset_Close1}
\end{quote}

Completeness is a bit trickier. The key lemma says that in an \<open>\<rightarrow>\<close> sequence. where an element \<open>x\<close>
starts in \<open>B\<close> and ends up in \<open>C'\<close>, there is a \<open>\<rightarrow>\<close> step where that transition takes place.
Completeness can be proved from this lemma.
\begin{quote}
@{thm [break,margin=75] (sub) Close2_steps_subdivide}\smallskip\\
@{thm Close2_sim_Close1}
\end{quote}

Altogether this yields the desired
\begin{quote}
@{thm Close2_eq_Close1}
\end{quote}

Of course we still need to show termination of \<open>\<rightarrow>\<close>.
This follows because the set of well-formed items (let us call it \<open>I\<close>) is finite,
because there are only finitely many dotted productions and @{const from} fields.
In each \<open>(B,C) \<rightarrow> (B',C')\<close> step, either @{term "card (I - (B \<union> C))"} decreases
or it remains the same (because no new item was generated) and @{prop "B' \<subset> B"},
which implies termination.
By induction on this wellfounded relation it follows that eventually @{prop "B={}"}
because if not, either prediction or completion applies.


TODO Get rid of this:?

Finally we can replace @{const Close} by @{const close2} in the definition of @{const bins}
and obtain (by proof)
\begin{quote}
@{thm (concl) bins0_close2}\\
@{thm (concl) binsSuc_close2}
\end{quote}
where we need to assume that @{prop "k < length w"}. This assumption does no harm
because by definition of @{const accepted}, we only need to compute the bins up to @{term "length w"}.

Of course, we have not yet arrived at an executable formulation because of the presence of \<open>SOME\<close>
in @{const close2}.


\section{Refinement}

This section is concerned with an efficient, executable implementation of the closure
operation on bins, and thus all of the recognizer. We proceed in three steps:
\begin{enumerate}
\item Implement sets by lists.
\item Turn the inductive definition into a (functional) while-loop.
\item Augment bins with a data structure for efficient search for items.
\end{enumerate}


\subsection{From Sets to Lists}

This is a canonical data refinement step. We take the worklist algorithm for closure from Section
\ref{sec:OnePassClosure} and replace @{type set} by @{type list}. The new transition relation
has the syntax @{prop \<open>Bs \<turnstile>\<^sub>L (B,C) \<rightarrow> (B',C')\<close>} where \<open>B\<close>, \<open>C\<close>, \<open>B'\<close>, \<open>C'\<close> are item lists
and \<open>Bs\<close> is a list of item lists:
\begin{quote}
@{thm [mode=Rule] Close2L.Predict}
\medskip

@{thm [mode=Rule] Close2L.Complete}
\end{quote}
where
\begin{quote}
@{thm Predict_L_def}\\
@{thm [break] Complete_L_def}
\end{quote}
and @{const insert_list}, @{const union_list} and @{const diff_list} implement the corresponding
set functions on lists. They are defined in Appendix~\ref{SetByList}. We have also replaced
the set of productions @{const P} by a list @{const ps} and assume
@{lemma "P = set (id ps)" by simp}.

Correctness and termination can be proved straightforwardly:
\begin{quote}
@{thm (prem 1,sub) Close2s_if_Close2Ls}\<open>\<Longrightarrow>\<close> @{thm (concl,sub) Close2s_if_Close2Ls}
\medskip

@{thm (concl) Close2L_NF}
\end{quote}
assuming @{thm (prem 2) Close2s_if_Close2Ls}, @{thm (prem 3) Close2s_if_Close2Ls}
(and in the second theorem @{thm (prem 3) Close2L_NF}).

Note that the transition rules preserve the absence of duplicates in both \<open>B\<close> and \<open>C\<close>,
but that this property is not needed in the above proofs.
It will be needed in the later complexity analysis.

\subsection{From Inductive to Recursive}

Finally we take the step from inductive predicate to directly executable functional
algorithm. We employ an Isabelle/HOL library theory defining a while-combinator
\begin{quote}
@{const_typ while_option}
\end{quote}
whose definition is explained elsewhere \cite{Nipkow-ITP11}. All we need to know is that it is
executable by means of this recursion equation provable as a lemma:
\begin{quote}
@{thm while_option_unfold}
\end{quote}
Termination is equivalent with a @{const Some} result.

The closure computation is performed by the obvious worklist loop:
\begin{quote}
@{thm close2L_def}
\medskip

@{thm [break] step2L.simps}
\end{quote}

By the same well-founded induction as before
we can show termination of @{const close2L}:
\begin{quote}
@{thm (concl) close2L_Some}
\end{quote}
Correctness is provable by a standard invariant preservation argument:
\begin{quote}
@{thm [break] (sub) close2L_Some_iff_Close2s}
\end{quote}


\subsection{Efficient Access to Bins}

The expensive part of the closure construction is checking, in each step,
if a newly generated item is already present (in \<open>B\<close> or \<open>C\<close>).
The number of possible items is bounded by the number of dotted productions (a constant
\<open>k\<close> depending on @{const P}) times the number of possible @{const from} values,
i.e.\ @{term "k * length w"}. We will store \<open>B\<close> and \<open>C\<close> not just as linear lists
but will partition them by their @{const from} values. When searching for an item \<open>x\<close>,
if we can access partition @{term "from x"} directly, the search takes
time at most \<open>k\<close>, the maximum size of each partition.
When processing the \<open>i\<close>-th input character, i.e. @{term \<open>i = length Bs\<close>}, we
augment \<open>B\<close> (and \<open>C\<close>) with a list (think array) \<open>F\<close> of size \<open>i\<close> such that
@{term "F ! j"} is a list of all @{prop \<open>x \<in> B\<close>} where @{prop \<open>from x = j\<close>}.

\begin{quote}
@{datatype [break] efficientItemList}
\end{quote}
with the projection functions @{const list} and @{const froms}.

The invariant
\begin{quote}
@{thm [break] inv_IL.simps[of xs fs]}
\end{quote}
ensures
that \<open>fs\<close> is long enough to accommodate all of \<open>xs\<close>,
that \<open>fs\<close> is an indexed version of \<open>xs\<close>,
and that there are no duplicates.
The condition @{prop "length fs > 0"} simplifies some technicalities and can easily be guaranteed.

This is a data refinement step where we replace item lists by their indexed version
@{type efficientItemList}.
The refinement of the closure algorithm @{const close2L} looks like this:
\begin{quote}
@{thm [break] step_fun.simps}\\

@{thm [break,margin=85]close2_L_def[unfolded steps_def]}
\end{quote}
Upon termination of @{const while_option},
@{term "list o snd o the"} extracts the closure as an item list.
The set operations @{const "empty_IL"}, @{const "insert"},  @{const "union_LIL"} and @{const "minus_IL"}
are defined in Appendix~\ref{SetByList2}.

Finally, we are ready for the executable top-level algorithm,
a refinement of @{const bins} from Section~\ref{sec:standard}:
\begin{quote}
@{thm [break,margin=85] bins_L.simps}\\

@{thm Init_L_def}\\

@{thm [break] Scan_L_def}
\end{quote}

Correctness: @{thm bins_L_eq_\<S>}
\<close>
text (in Earley_Gw_eps_T2)\<open>
\section{Complexity}

We have analyzed the running time of the recognizer following the approach detailed elsewhere
\cite{Nipkow-ACMbook}: from the definition of an executable function \<open>\<^latex>\<open>\isaconst{\<close>f\<^latex>\<open>}\<close> :: \<tau> \<Rightarrow> \<tau>'\<close>,
we automatically generate a (time) function definition \<open>\<^latex>\<open>\isaconst{\<close>T_f\<^latex>\<open>}\<close> :: \<tau> \<Rightarrow> nat\<close>
such that  \<open>\<^latex>\<open>\isaconst{\<close>T_f\<^latex>\<open>}\<close> x\<close>
is the number of computation steps of \<open>\<^latex>\<open>\isaconst{\<close>f\<^latex>\<open>}\<close> x\<close> where we count only calls of recursive
user-defined functions. For example, the time function @{const T_isin_list} (for @{const isin_list}
from Appendix~\ref{SetByList}) is defined like this:
\begin{quote}
@{thm T_isin_list.simps}
\end{quote}
The boon and bane of this approach is that one obtains very detailed formulas with somewhat arbitrary
constants. Arbitrary because they depend on the abstract machine model embodied in the generation of
the time functions which may be quite different from a real machine.
\begin{quote}
@{thm [break] T_Scan_L_bound}
\end{quote}
where @{const K} is the maximum length of the @{const rhs} of any production.

@{thm [break] (concl) T_step_fun_bound}

@{thm [break] T_step_fun_bound4[rename_abs _ il\<^sub>1 il\<^sub>2 _ il\<^sub>1 il\<^sub>2 _ il\<^sub>1 il\<^sub>2]}


\appendix

\section{Set Operations on type  @{type list}}
\label{SetByList}

\begin{quote}
@{thm filter.simps}\\

@{thm fold_simps}\\

@{thm isin_list.simps}\\

@{thm insert_list_def}\\

@{thm union_list_def2}\\

@{thm diff_list_def}
\end{quote}

\section{Set Operations on type @{type efficientItemList}}
\label{SetByList2}

The following definitions are mostly self-explanatory.
\begin{quote}
@{thm [break] EarleyWorklist.isin.simps}\\

@{thm [break] empty_IL_def}\\

@{thm [break] insert.simps}\\

@{thm union_LIL.simps}\\

@{thm IL_of_List_def}\\

@{thm [break]minus_LIL.simps}\\

@{thm [break](sub)minus_IL_def}
\end{quote}
Note that
\begin{description}
\item[@{const empty_IL}] initializes the @{const froms} list with
a list that is sufficiently large for the items that are expected to go into it.
The required size can be determined statically in our setting.
Function @{const replicate} creates a list of that size where every element is @{const Nil}.
\item[@{const union_LIL}] takes as its first argument a list.
\item[@{const minus_LIL}] takes as a first argument the size
of the required @{const froms} list and as the second argument a list.
\end{description}
\<close>

(*<*)
end
(*>*)