theory Sugar
  imports Main
begin

(* Boxing *)

definition mbox :: "'a \<Rightarrow> 'a" where
"mbox x = x"

definition mbox0 :: "'a \<Rightarrow> 'a" where
"mbox0 x = x"

notation (latex) mbox ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>" [999] 999)

notation (latex) mbox0 ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>" [0] 999)

(* LOGIC *)
notation (latex output)
  If  ("(\<^latex>\<open>\\textsf{\<close>if\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\textsf{\<close>then\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\textsf{\<close>else\<^latex>\<open>}\<close> (_))" 10)

syntax (latex output)

  "_Let"        :: "[letbinds, 'a] => 'a"
  ("(\<^latex>\<open>\\textsf{\<close>let\<^latex>\<open>}\<close> (_)/ \<^latex>\<open>\\textsf{\<close>in\<^latex>\<open>}\<close> (_))" 10)

  "_case_syntax":: "['a, cases_syn] => 'b"
  ("(\<^latex>\<open>\\textsf{\<close>case\<^latex>\<open>}\<close> _ \<^latex>\<open>\\textsf{\<close>of\<^latex>\<open>}\<close>/ _)" 10)


(* SETS *)

(* empty set *)
notation (latex)
  "Set.empty" ("\<emptyset>")

(* insert *)
translations 
  "{x} \<union> A" <= "CONST insert x A"
  "{x,y}" <= "{x} \<union> {y}"
  "{x,y} \<union> A" <= "{x} \<union> ({y} \<union> A)"
  "{x}" <= "{x} \<union> \<emptyset>"

(* set comprehension *)
syntax (latex output)
  "_Collect" :: "pttrn => bool => 'a set"              ("(1{_ |/ _})")
  "_CollectIn" :: "pttrn => 'a set => bool => 'a set"   ("(1{_ \<in> _ | _})")
translations
  "_Collect p P"      <= "{p. P}"
  "_Collect p P"      <= "{p|xs. P}"
  "_CollectIn p A P"  <= "{p : A. P}"

(* card *)
notation (latex output)
  card  ("|_|")

(* LISTS *)

(* Cons *)
(*
notation (latex)
  Cons  ("_ \<cdot>/ _" [66,65] 65)
*)

(* length *)
syntax
  length :: "'a list \<Rightarrow> nat" ("|_|")

notation (latex output)
  length  ("|_|")

(* DUMMY *)
consts DUMMY :: 'a ("\<^latex>\<open>\\_\<close>")

(* THEOREMS *)
notation (Rule output)
  Pure.imp  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{\<close>_\<^latex>\<open>}}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

syntax (Rule output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>\\mbox{}\\inferrule{\<close>_\<^latex>\<open>}\<close>\<^latex>\<open>{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" 
  ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\\\\\<close>/ _")

  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

notation (Axiom output)
  "Trueprop"  ("\<^latex>\<open>\\mbox{}\\inferrule{\\mbox{}}{\\mbox{\<close>_\<^latex>\<open>}}\<close>")

notation (IfThen output)
  Pure.imp  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
syntax (IfThen output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close> /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("\<^latex>\<open>\\mbox{\<close>_\<^latex>\<open>}\<close>")

notation (IfThenNoBox output)
  Pure.imp  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _/ \<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
syntax (IfThenNoBox output)
  "_bigimpl" :: "asms \<Rightarrow> prop \<Rightarrow> prop"
  ("\<^latex>\<open>{\\normalsize{}\<close>If\<^latex>\<open>\\,}\<close> _ /\<^latex>\<open>{\\normalsize \\,\<close>then\<^latex>\<open>\\,}\<close>/ _.")
  "_asms" :: "prop \<Rightarrow> asms \<Rightarrow> asms" ("_ /\<^latex>\<open>{\\normalsize \\,\<close>and\<^latex>\<open>\\,}\<close>/ _")
  "_asm" :: "prop \<Rightarrow> asms" ("_")

abbreviation (iffSpace)
  iffSpace :: "[bool, bool] => bool"  (infixr "\<^latex>\<open>\\ \<close>\<longleftrightarrow>\<^latex>\<open>\\ \<close>" 25)
where
  "iffSpace A B == A = B"

setup \<open>
  Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>const_typ\<close>
    (Scan.lift Parse.embedded_inner_syntax)
    (fn ctxt => fn c =>
      let val tc = Proof_Context.read_const {proper = false, strict = false} ctxt c in
        Pretty.block [Document_Output.pretty_term ctxt tc, Pretty.str " ::",
          Pretty.brk 1, Syntax.pretty_typ ctxt (fastype_of tc)]
      end)
\<close>

ML \<open>
fun dummy_pats_style (wrap $ (eq $ lhs $ rhs)) =
  let
    val rhs_vars = Term.add_vars rhs [];
    fun dummy (t as Var (v as (_, T))) =
          if member ((=) ) rhs_vars v then t else Const (@{const_name DUMMY}, T)
      | dummy (t $ u) = dummy t $ dummy u
      | dummy (Abs (n, T, b)) = Abs (n, T, dummy b)
      | dummy t = t;
  in wrap $ (eq $ dummy lhs $ rhs) end
\<close>

setup\<open>
Term_Style.setup @{binding dummy_pats} (Scan.succeed (K dummy_pats_style))
\<close>

(* Dummy vars on lhs in case expressions: *)
syntax (output)
  "_case1'" :: "['a, 'b] \<Rightarrow> case_syn"  ("(2_ \<Rightarrow>/ _)" 10)

print_ast_translation \<open>
  let
    fun vars (Ast.Constant _) = []
      | vars (Ast.Variable x) = [x]
      | vars (Ast.Appl ts) = flat(map vars ts);
    fun dummy vs (Ast.Appl ts) = Ast.Appl(map (dummy vs) ts)
      | dummy vs (Ast.Variable x) = Ast.Variable (if member (op =) vs x then x else "_")
      | dummy _ c = c
    fun case1_tr' [l,r] =
          Ast.Appl [Ast.Constant @{syntax_const "_case1'"}, dummy (vars r) l, r]
  in [(\<^syntax_const>\<open>_case1\<close>, K case1_tr')] end
\<close>

setup \<open>
let

fun eta_expand Ts t xs = case t of
    Abs(x,T,t) =>
      let val (t', xs') = eta_expand (T::Ts) t xs
      in (Abs (x, T, t'), xs') end
  | _ =>
      let
        val (a,ts) = strip_comb t (* assume a atomic *)
        val (ts',xs') = fold_map (eta_expand Ts) ts xs
        val Bs = binder_types (fastype_of1 (Ts,t));
        val n = Int.min (length Bs, length xs');
        val bs = map Bound ((n - 1) downto 0);
        val xBs = ListPair.zip (xs',Bs);
        val xs'' = drop n xs';
        val t' = incr_boundvars n (list_comb (a, ts'));
        val t'' = fold_rev Term.abs xBs (list_comb(t', bs))
      in (t'', xs'') end

val style_eta_expand =
  (Scan.repeat Args.name) >> (fn xs => fn ctxt => fn t => fst (eta_expand [] t xs))

in Term_Style.setup @{binding eta_expand} style_eta_expand end
\<close>

setup \<open>
  Document_Output.antiquotation_pretty_embedded \<^binding>\<open>const_name\<close>
    (Args.const {proper = true, strict = false})
    (fn ctxt => fn c => Pretty.mark_str (Markup.const, Proof_Context.extern_const ctxt c))
\<close>

ML \<open>
fun pretty_const_typ ctxt (c, maybe_typ) : Pretty.T =
  (*taken from Prog_Prove/LaTeXsugar.thy*)
  let
    val tc = Proof_Context.read_const {proper = true, strict = false} ctxt c
    val pretty_typ =
      (case maybe_typ of
        NONE => Syntax.pretty_typ ctxt (fastype_of tc)
      | SOME typ =>
        let val typ_instance = Type.typ_instance o Proof_Context.tsig_of in
          if typ_instance ctxt (typ, fastype_of tc) then Syntax.pretty_typ ctxt typ
          else error ("constant " ^ quote (Proof_Context.markup_const ctxt c) ^ " is not of type " ^
            quote (Syntax.string_of_typ ctxt typ))
        end)
  in
    Pretty.block [Document_Output.pretty_term ctxt tc, Pretty.str " ::",
    Pretty.brk 1, pretty_typ]
  end

fun pretty_eqs_style (f:Proof.context -> string -> term list) ctxt (style, (name, maybe_thms)) : Pretty.T =
  let val eq = Document_Output.pretty_term ctxt o style
  in
    (case maybe_thms of
      SOME thms => map eq thms |> Pretty.chunks
    | NONE =>
      f ctxt name
      |> map eq
      |> Pretty.chunks)
  end

fun separate_texts (sep: Latex.text) (texts: Latex.text list) : Latex.text =
  separate sep texts |> List.concat

fun pretty_funs_style_generic f ctxt (style, names) : Latex.text =
  names
  |> map (fn ((name, typ), eqs) =>
    let
      val thy_output = Document_Output.pretty ctxt
      val equations = pretty_eqs_style f ctxt (dummy_pats_style o style, (name, eqs)) |> thy_output
 (*     val header = pretty_const_typ ctxt (name, typ) |> thy_output*)
    in separate_texts (Latex.string "\\\\[\\funheadersep]" ) [(*header,*) equations] end)
  |> separate_texts (Latex.string "\\\\\\\\")
  |> XML.enclose "{\\parindent0pt" "}"
\<close>

setup \<open>
let
 val parse =
  Args.const {proper = true, strict = false} --
  Scan.option (Scan.lift (Args.$$$ "::") |-- Args.typ) --
  Scan.option (Scan.lift (Args.$$$ "[") |-- (Attrib.thms >> map Thm.full_prop_of) --| Scan.lift (Args.$$$ "]"))
 fun eqns suf ctxt n = map Thm.full_prop_of (Proof_Context.get_thms ctxt (n ^ suf))
 fun input_eqns ctxt n = #input_eqns (Function.get_info ctxt (Syntax.read_term ctxt n))
in
  Document_Output.antiquotation_raw \<^binding>\<open>def\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic (eqns "_def"))
  #> Document_Output.antiquotation_raw \<^binding>\<open>fun\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic (eqns ".simps"))
  #> Document_Output.antiquotation_raw \<^binding>\<open>fun_input\<close>
    (Term_Style.parse -- Parse.and_list1' parse)
      (Config.put Document_Antiquotation.thy_output_break true
      #> pretty_funs_style_generic input_eqns)
end
\<close>

(* Suc *)

translations "n+1" <= "CONST Suc n"

(* append *)
syntax (latex output)
  "_appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^latex>\<open>\\isacharat\<close>" 65)
translations
  "_appendL xs ys" <= "xs @ ys" 
  "_appendL (_appendL xs ys) zs" <= "_appendL xs (_appendL ys zs)"

(* Let *)
translations 
  "_bind (p, CONST DUMMY) e" <= "_bind p (CONST fst e)"
  "_bind (CONST DUMMY, p) e" <= "_bind p (CONST snd e)"

  "_tuple_args x (_tuple_args y z)" ==
    "_tuple_args x (_tuple_arg (_tuple y z))"

  "_bind (CONST Some p) e" <= "_bind p (CONST the e)"
  "_bind (p # CONST DUMMY) e" <= "_bind p (CONST hd e)"
  "_bind (CONST DUMMY # p) e" <= "_bind p (CONST tl e)"

end