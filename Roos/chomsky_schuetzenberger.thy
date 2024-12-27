theory chomsky_schuetzenberger
  imports Finite_Automata_HF.Finite_Automata_HF HOL.Nat "../CFG" "../CFL"
begin



definition reg :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"reg (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> True) " (*TODO add type 3 stuff here*)               
   

definition hom :: \<open>('c list \<Rightarrow> 'b list) \<Rightarrow> bool\<close> where
\<open>hom h = (\<forall>a b. h (a@b) = (h a) @ h (b))\<close>

(* Klammertyp, wird kombiniert mit anderen Symbolen *)
datatype bracket = Op | Cl


inductive balanced :: "(bracket  \<times> ('a)) list \<Rightarrow> bool" where
  empty[intro]: "balanced []" |
  pair[intro]: "balanced xs \<Longrightarrow> balanced ((Op, g) # xs @ [(Cl, g)])" |
  concat[intro]: "balanced xs \<Longrightarrow> balanced ys \<Longrightarrow> balanced (xs @ ys)"


(* Die Klammersprache über einer Menge R. Jedes Element r \<in> R wird zu einer öffnenden und einer schließenden Klammer gemacht, durch paarung mit bracket. (Cl, r) ist die Schließende Klammer, (Op, r) die öffnende. *)
(*Wir brauchen später D := dyck_language ((Prods G) \<times> {1,2}) *)

definition dyck_language :: "'a set \<Rightarrow> (bracket  \<times> ('a)) list set" where
  "dyck_language R = {l. (balanced l) \<and> (\<forall>(br,r) \<in> (set l). r \<in> R)}"


(* die im Beweis genutzte Transformation der Produktionen *)
definition transform_production :: "('n, 't) prod \<Rightarrow> 
('n, bracket \<times> ('n,'t) prod \<times> nat ) prod" where
  "transform_production p = (
    case p of
      (A, [Nt B, Nt C]) \<Rightarrow> 
        (A, [ Tm (Op, (p,1)), Nt B, Tm (Cl, (p,1)), Tm (Op, (p,2)), Nt C, Tm (Cl, (p,2))  ]) | 
      (A, [Tm a]) \<Rightarrow>   
        (A, [ Tm (Op, (p,1)),       Tm (Cl, (p,1)), Tm (Op, (p,2)),       Tm (Cl, (p,2))  ]) 
)"

term \<open>(A::'n,[Tm (Op, (p:: ('n, 't) prod   ,1::nat))])\<close>
(*  "P \<times> {1, 2}"
  :: "(('a \<times> ('a, 'b) sym list) \<times> nat) set"   *)

(* was eine Regel erfüllen muss um Chomsky zu sein *)
definition CNF_rule :: "('c \<times> ('c, 'b) sym list) \<Rightarrow> bool" where
\<open>CNF_rule p \<equiv>  (\<exists>(A::'c) B C. (p = (A,[Nt B, Nt C]))) \<or> (\<exists>A a. p= (A, [Tm a]))\<close>

(* Existenz der Chomsky-Normalform *)
lemma CNF_existence :
assumes \<open>CFL.cfl TYPE('a) L\<close>
shows \<open>\<exists>P S::'a. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> (* TODO Startsymbol nicht auf rechter Seite?*)
sorry

(* Unser gewünschtes Resultat *)
lemma chomsky_schuetzenberger :
assumes \<open>CFL.cfl TYPE('a) L\<close> 

shows \<open>\<exists>R h \<Gamma>. (reg TYPE('a) R) \<and> (L = image h (R \<inter> dyck_language \<Gamma>)) \<and> hom h\<close>
proof -
have \<open>\<exists>P S::'a. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> using \<open>cfl TYPE('a) L\<close> CNF_existence by auto
then obtain P where \<open>\<exists>S::'a. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> by blast
then obtain S where \<open>L = Lang P S\<close> and \<open>(\<forall>p \<in> P. CNF_rule p)\<close> by blast (* Warum geht das nicht in einzer Zeile...?*)

let ?\<Gamma> = \<open>P \<times> {1::nat,2}\<close>
let ?P' = \<open>image transform_production P\<close>
let ?L' = \<open>Lang ?P' S\<close>

have \<open>?L' \<subseteq> dyck_language ?\<Gamma>\<close> sorry




qed



end