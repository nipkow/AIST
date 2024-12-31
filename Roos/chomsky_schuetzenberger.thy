theory chomsky_schuetzenberger
  imports Finite_Automata_HF.Finite_Automata_HF HOL.Nat "../CFG" "../CFL"
begin

declare [[names_short]]

definition reg :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"reg (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> True) " (*TODO add type 3 stuff here*)               
   






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

(* (Directly) After each (Cl,p,1) always comes a (Op,p,2)*)
definition P1 :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list \<Rightarrow> bool\<close> where
\<open>P1 P x = (\<forall>p \<in> P. \<forall> i < length x.
  x ! i = (Cl, (p, 1)) \<longrightarrow> ( i+1 < length x \<and> x ! (i+1) = (Op, (p, 2))))\<close>

(*After any (Cl,pi,2) there never comes an (Op,...) *)
definition P2 :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list \<Rightarrow> bool\<close> where
\<open>P2 P x = (\<forall>p \<in> P. \<forall>r. (\<forall>i j. i < length x \<and> j < length x \<and> i < j \<and> x ! i = (Cl, (p, 2)) \<longrightarrow> x ! j \<noteq> (Op, r)))\<close>

(*If pi = A\<rightarrow>BC, then after each (Op,pi,1) always comes a (Op,p,1) where B = lhs of p And after each (Op,pi,2) always comes a (Op,sigma,1) where C = lhs of sigma *)
definition P3 :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list \<Rightarrow> bool\<close> where
\<open>P3 x = (\<forall>i < length x. 
       (\<exists>A B C. x ! i = (Op, ((A, [Nt B, Nt C]), 1)) \<longrightarrow> 
          ((i+1) < length x \<and> (\<exists>p l. x ! (i+1) = (Op, (p, 1)) \<and> p = (B, l)))) \<and>
       (\<exists>A B C. x ! i = (Op, ((A, [Nt B, Nt C]), 2)) \<longrightarrow> 
          ((i+1) < length x \<and> (\<exists>\<sigma> l. x ! (i+1) = (Op, (\<sigma>, 1)) \<and> \<sigma> = (C, l)))))\<close>


(*If pi = A\<rightarrow>a then after each (Op,pi,1) comes a (Cl,pi,1) and after each (Op,pi,2) comes a (Cl,pi,2) *)
definition P4 :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list \<Rightarrow> bool\<close> where
\<open>P4 x = ((\<forall>i < length x - 1. 
        (\<exists>A a. x ! i = (Op, ((A, [Tm a]), 1)) \<longrightarrow> x ! (i + 1) = (Cl, ((A, [Tm a]), 1))) \<and>
        (\<exists>A a. x ! i = (Op, ((A, [Tm a]), 2)) \<longrightarrow> x ! (i + 1) = (Cl, ((A, [Tm a]), 2)))))\<close>

(*For all A, if A produces x under P', then there eists some pi \<in> P with lhs A such that x begins with (Op,pi,1) *)
definition P5 :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> 'a \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list \<Rightarrow> bool\<close> where
\<open>P5 P A x = (( (\<forall>w. derives (image transform_production P) [Nt A] w) \<longrightarrow> 
       (\<exists>\<pi> l. \<pi> \<in> P \<and> \<pi> = (A, l) \<and> x \<noteq> [] \<and> x ! 0 = (Op, \<pi>, 1))))\<close>

(* das ist die gesuchte Reguläre Sprache für den Schnitt mit der dyck-sprache *)
definition Re :: \<open>('a \<times> ('a, 'b) sym list) set \<Rightarrow> 'a \<Rightarrow> (bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list set\<close> where
\<open>Re P A = {x::(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list. 
(P1 P x) \<and> (P2 P x) \<and> (P3 x) \<and> (P4 x) \<and> (P5 P A x)}\<close>



definition hom :: \<open>('c list \<Rightarrow> 'd list) \<Rightarrow> bool\<close> where
\<open>hom h = (\<forall>a b. h (a@b) = (h a) @ h (b))\<close>



(* helper funktion für das eigentliche h im Resultat *)
fun he :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) \<Rightarrow> 'b list\<close> where
\<open>he (br, (p, i)) = 
    (case p of 
    (A, [Nt B, Nt C]) \<Rightarrow> [] | 
    (A, [Tm a]) \<Rightarrow> (if br = Op \<and> i=1 then [a] else []) | 
    _ \<Rightarrow> []
    )
\<close>

(* auf symbole erweiterte helper funktion für das eigentliche h im Resultat *)
fun he_ext :: \<open>('a, bracket \<times> ('a,'b) prod \<times> nat ) sym \<Rightarrow> ('a,'b) sym list\<close> where
\<open>he_ext (Tm (br, (p, i))) = 
    (case p of 
    (A, [Nt B, Nt C]) \<Rightarrow> [] | 
    (A, [Tm a]) \<Rightarrow> (if br = Op \<and> i=1 then [Tm a] else []) | 
    _ \<Rightarrow> []
    )\<close> | 
\<open>he_ext (Nt A) = [Nt A]\<close>



(* Der gesuchte Homomorphismus im Resultat*)
fun h :: \<open>(bracket \<times> ('a \<times> ('a, 'b) sym list) \<times> nat) list \<Rightarrow> 'b list \<close> where
\<open>h l = concat (map he l)\<close>

(* Auf symbole erweitertes h des Resultats *)
fun h_ext :: \<open>('a, bracket \<times> ('a,'b) prod \<times> nat ) sym list \<Rightarrow> ('a,'b) sym list \<close> where
\<open>h_ext l = concat (map he_ext l)\<close>

(* by defining h on D we get a homomorphism on D* by extending it homomorphically *)
lemma extending_gives_hom :
fixes h:: \<open>'a \<Rightarrow> 'b list\<close>
shows \<open>hom (\<lambda>x. (concat (map h x)))\<close>
unfolding hom_def by simp


lemma helper: \<open>he_ext (Tm x) = map Tm (he x)\<close>
apply(induction x rule: he.induct)
by(auto split: list.splits sym.splits)

lemma \<open>h_ext (map Tm x) = map Tm (h x)\<close>
apply(induction x)
apply(simp)
using helper by fastforce



(* Unser gewünschtes Resultat *)
lemma chomsky_schuetzenberger :
fixes L::\<open>'t list set\<close>
assumes \<open>CFL.cfl TYPE('n) L\<close> 

shows \<open>\<exists>(R::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> nat) list set) h \<Gamma>. (reg TYPE('n) R) \<and> (L = image h (R \<inter> dyck_language \<Gamma>)) \<and> hom h\<close>
proof -
have \<open>\<exists>P S::'n. L = Lang P S \<and> (\<forall>p \<in> P. CNF_rule p)\<close> using \<open>cfl TYPE('n) L\<close> CNF_existence by auto
then obtain P and S::'n where \<open>L = Lang P S\<close> and \<open>(\<forall>p \<in> P. CNF_rule p)\<close> by blast

let ?\<Gamma> = \<open>P \<times> {1::nat,2}\<close>
let ?P' = \<open>image transform_production P\<close>
let ?L' = \<open>Lang ?P' S\<close>
let ?h = \<open>h::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> nat) list \<Rightarrow> 't list\<close>

have \<open>?L' \<subseteq> dyck_language ?\<Gamma>\<close> sorry (* evtl gar nicht benötigt? *)

have \<open>\<forall>A. \<forall>x::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> nat) list. 
(image transform_production P) \<turnstile> [Nt S] \<Rightarrow>* (map Tm x) \<longleftrightarrow> x \<in> (dyck_language ?\<Gamma>) \<inter> (Re P A)\<close> sorry
then have \<open>?L' = (dyck_language ?\<Gamma>) \<inter> (Re P S)\<close> by (metis (no_types, lifting) CFG.Lang_def mem_Collect_eq subsetI subset_antisym)
then have \<open>image h ((dyck_language ?\<Gamma>) \<inter> (Re P S)) =  image h ?L'\<close> by simp
also have \<open>... = Lang P S\<close> sorry

also have \<open>... = L\<close> by (simp add: \<open>L = Lang P S\<close>)
finally have \<open>image h ((dyck_language ?\<Gamma>) \<inter> (Re P S)) = L\<close> by auto

moreover have hom: \<open>hom (h::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> nat) list \<Rightarrow> 't list)\<close>
   using extending_gives_hom by (simp add: hom_def)
moreover have \<open>reg TYPE('n) (Re P S)\<close> sorry
ultimately have \<open>reg TYPE('n) (Re P S) \<and> L = image h ((Re P S) \<inter> (dyck_language ?\<Gamma>)) \<and> hom (h::(bracket \<times> ('n \<times> ('n, 't) sym list) \<times> nat) list \<Rightarrow> 't list)\<close> by blast 
then show ?thesis by blast

qed



end