theory chomsky_schuetzenberger
  imports Finite_Automata_HF.Finite_Automata_HF HOL.Nat "../CFG" "../CFL"
begin



definition reg :: "'n itself \<Rightarrow> 't list set \<Rightarrow> bool" where
"reg (TYPE('n)) L = (\<exists>P S::'n. L = Lang P S \<and> True) " (*TODO add type 3 stuff here*)               
   

definition hom :: \<open>('c list \<Rightarrow> 'b list) \<Rightarrow> bool\<close> where
\<open>hom h = (\<forall>a b. h (a@b) = (h a) @ h (b))\<close>

(* Wir brauchen als Grundlage für die Klammersprache später zu jeder Produktion 2 Versionen, und es muss ein type sein.*)
datatype ('p) two_copies = V1 'p | V2 'p

(* Macht jedes p zu einer öffnenden (Op) oder schließenden (Cl) Klammer *)
datatype ('g) brackets = Op 'g | Cl 'g


inductive balanced :: "('g) brackets list \<Rightarrow> bool" where
  empty[intro]: "balanced []" |
  pair[intro]: "balanced xs \<Longrightarrow> balanced (Op g # xs @ [Cl g])" |
  concat[intro]: "balanced xs \<Longrightarrow> balanced ys \<Longrightarrow> balanced (xs @ ys)"


(* Die Klammersprache über einen Typ 'g. Akzeptiert nur balancierte Ausdrücke über 'g brackets *)
definition dyck_language :: "'g itself \<Rightarrow> ('g) brackets list set" where
  "dyck_language g = {xs. balanced xs}" (* TODO stimmt hier alles mit den Parametern? *)


lemma chomsky_schuetzenberger :
assumes \<open>cfl TYPE('a) L\<close> 

shows \<open>\<exists>R h. reg TYPE('a) R \<and> L = image h (R) \<and> hom h\<close> (*TODO hier fehlt noch die Klammersprache im Schnitt mit R*)
sorry



end