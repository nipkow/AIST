theory Chomsky_Normal_Form_Fun
  imports "Context_Free_Grammar.Chomsky_Normal_Form" HOL.List
begin

fun tm_list_of_prods :: "('n,'t) prods \<Rightarrow> ('n,'t) sym list" where
  "tm_list_of_prods ps = 
    (let rs = map snd ps in filter isTm (concat rs))"

lemma in_tm_list_of_prods_impl_Tm:
  assumes "tm \<in> set (tm_list_of_prods ps)"
  obtains t where "tm = Tm t"
proof -
  from assms obtain xs where "tm \<in> set (filter isTm xs)" by auto
  then show thesis using that isTm_def by fastforce 
qed

(*(l,r) as argument in f bad practice?*)
fun uniformize_tm :: "['t, 'n, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_tm t nt ps = 
    (let f = (\<lambda>(l,r). if length r < 2 then (l,r) 
                      else (l,map (\<lambda>s. if s = (Tm t) then (Nt nt) else s) r))  
    in map f ps)"

lemma uniformize_tm_is_uniformized:
  "uniformize (fresh (nts ps \<union> {S})) t S ps (uniformize_tm t (fresh (nts ps \<union> {S})) ps)"
  sorry


fun uniformize' :: "['n::infinite, ('n,'t) syms, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize' _ [] ps = ps" |
  "uniformize' S (t#ts) ps = 
    uniformize' S ts (uniformize_tm (destTm t) (fresh (nts ps \<union> {S})) ps)"

fun uniformize_fun :: "['n::infinite, ('n,'t) prods] \<Rightarrow> ('n,'t) prods" where
  "uniformize_fun S ps = uniformize' S (tm_list_of_prods ps) ps"





end