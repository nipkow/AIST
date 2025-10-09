theory EarleyWorklist

imports "Earley" "HOL-Library.While_Combinator"

begin

value "while_option (\<lambda>(as,bs). as \<noteq> []) (step_fun Bs) ([], [])"

context Earley_Gw
begin


(* must not be empty, otherwise by def step_rel is always false *)
definition step_rel :: "('n, 'a) state set list \<Rightarrow> ('n, 'a) state set \<times> ('n, 'a) state set \<Rightarrow> ('n, 'a) state set \<times> ('n, 'a) state set \<Rightarrow> bool" where
"step_rel  \<equiv> Close2"

(*fun Predict_L_help :: "('n, 'a) prods \<Rightarrow> ('n, 'a) state \<Rightarrow> nat \<Rightarrow> ('n, 'a) state list" where
  "Predict_L_help [] x k = []"
| "Predict_L_help (p#Ps) x k = (let ps' = (Predict_L_help Ps x k) in (if next_sym_Nt x (lhs p) then (State p 0 k) # ps' else ps' ))"*)

(*fun Predict_L_eps_complete where
  "Predict_L_eps_complete = undefined"*)

(*definition Predict_L :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> ('n,'a) state list" where
  "Predict_L x k = Predict_L_help ps x k"*)

definition Predict_L :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> ('n,'a) state list" where
  "Predict_L x k = map (\<lambda> p. State p 0 k) (filter (\<lambda> p. next_sym_Nt x (lhs p)) ps)"


(*fun Complete_L_help :: "('n, 'a) state list \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) state list" where
  "Complete_L_help [] y = []"
| "Complete_L_help (b#bs) y = (let acc = Complete_L_help bs y in (if next_sym_Nt b (lhs(prod y)) then (mv_dot b) # acc else acc))"*)

definition Complete_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) state list" where
  "Complete_L Bs y = map mv_dot (filter (\<lambda> b. next_sym_Nt b (lhs(prod y))) (Bs ! from y))"
 (*= Complete_L_help (Bs ! from y) y"*)


definition minus_L :: "'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" (infix "-l" 50) where
  "minus_L As Bs = foldr (removeAll) Bs As"

lemma minus_L_set[simp]: "set (As -l Bs) = set As - set Bs"
  by (induction Bs) (auto simp add: minus_L_def)


fun step_fun :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list * ('n, 'a) state list \<Rightarrow> ('n, 'a) state list * ('n, 'a) state list" where
  "step_fun Bs ((b#bs), C) = ( (List.union bs (if is_complete b then Complete_L Bs b else Predict_L b (length Bs))) -l (b # C) , (b # C)) "

(*definition "wf_binL B k = (list_all (\<lambda> x. wf_state1 x k) B)"

fun wf_binsL_help where
  "wf_binsL_help [] k = True"
| "wf_binsL_help (B#Bs) k = (wf_binL B k \<and> wf_binsL_help Bs (Suc k))"
definition "wf_binsL Bs = wf_binsL_help Bs 0"

lemma wf_binL_eq: "wf_binL B k = wf_bin1 (set B) k"
   by (induction B) (auto simp add: wf_bin1_def wf_binL_def)

lemma wf_binsL_help_eq: "wf_binsL_help Bs n = (\<forall>k < length Bs. wf_binL (Bs!k) (k + n))"
  by (induction Bs arbitrary: n) (auto simp add: less_Suc_eq_0_disj)

lemma wf_binsL_eq: "wf_binsL Bs = wf_bins1 (map set Bs)" 
  by (auto simp add: wf_binsL_def wf_bins1_def wf_binL_eq wf_binsL_help_eq)*)

lemma Predict_eq: "set (Predict_L st k) = Predict st k"
  by (auto simp add: Predict_L_def Predict_def)


lemma Complete_eq: "from st < length Bs \<Longrightarrow> set (Complete_L Bs st) = Complete (map set Bs) st"
  by (auto simp add: Complete_L_def Complete_def nths_map)

lemma step_fun: "as \<noteq> [] \<Longrightarrow> wf_bin1 (set as) (length Bs) \<Longrightarrow> step_fun Bs (as,bs) = (as',bs') \<Longrightarrow> step_rel (map set Bs) (set as,set bs) (set as', set bs')"
proof-
  assume assms: "as \<noteq> []" and wf: "wf_bin1 (set as) (length Bs)" and sf: "step_fun Bs (as,bs) = (as',bs')"
  have comp: "\<forall>a \<in> set as. is_complete a \<longrightarrow> from a < length Bs" using wf by (auto simp add: wf_bin1_def wf_state1_def)
  from assms obtain a as' where P :"as = a # as'"
    using list.exhaust by auto 
  show ?thesis
   proof (cases "is_complete a")
      case True
      then have 1: "a \<in> set as \<and> next_symbol a = None " by (auto simp add: P next_symbol_def)
      then have 2: "(map set Bs) \<turnstile> (set as, set bs) \<rightarrow> ((set as \<union> Complete (map set Bs) a) - (set bs \<union> {a}), (set bs \<union> {a}))"
        using Close2.Complete by (auto)
      then show ?thesis using 1 2 P True Nil comp sf Complete_eq step_rel_def by auto
    next
      case False
      then have 1: "a \<in> set as \<and> next_symbol a \<noteq> None " by (auto simp add: P next_symbol_def)
      then have 2: "(map set Bs) \<turnstile> (set as, set bs) \<rightarrow> (set as \<union> Predict a (length Bs) - (set bs \<union> {a}), insert a (set bs))"
        by (metis Earley_Gw.Close2.Predict length_map)
      then show ?thesis using 2 P False sf 1 Predict_eq step_rel_def by fastforce 
    qed
qed
end (*Earley_Gw*)

context Earley_Gw_eps
begin

lemma wf1_Predict: "wf_state1 st k \<Longrightarrow> wf_bin1 (set (Predict_L st k)) k"
  using wf1_Predict Predict_eq by (auto simp add: wf_bin1_def)

lemma wf1_Complete: "wf_bins1 (map set Bs) \<Longrightarrow> wf_state1 st (length Bs) \<Longrightarrow> is_complete st \<Longrightarrow> wf_bin1 (set (Complete_L Bs st)) (length Bs)"
proof-
  assume assms: "wf_bins1 (map set Bs)" "wf_state1 st (length Bs)" "is_complete st"
  then have 1: "\<forall>x \<in>  (set (filter (\<lambda> b. next_sym_Nt b (lhs(prod st))) (Bs ! from st))). wf_state x (from st)"
    by (simp add: wf_bin1_def wf_bins1_def wf_state1_def)
  then have 2: "\<forall>x \<in> (set  (filter (\<lambda> b. next_sym_Nt b (lhs(prod st))) (Bs ! from st))). wf_state (mv_dot x) (from st)"
    using assms 1 unfolding wf_state_def is_complete_def next_symbol_def mv_dot_def
    by (auto split: if_splits)
  have "from st < length Bs"
    using assms(2,3) wf_state1_def by auto
  then show ?thesis
     using assms 2 Complete_L_def in_set_conv_nth wf1_Complete wf_bin1_def wf_bins1_def by fastforce  
qed
  

lemma step_fun_wf: " as \<noteq> [] \<Longrightarrow> wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set as) (length Bs) \<Longrightarrow> step_fun Bs (as, bs) = (as', bs') \<Longrightarrow> wf_bin1 (set as') (length Bs)"
proof -
  assume assms: "as \<noteq> []" "wf_bins1 (map set Bs)" "wf_bin1 (set as) (length Bs)" "step_fun Bs (as, bs) = (as', bs')"
  then show ?thesis using assms Close2_step_pres1 length_map
    by (metis step_fun step_rel_def)
qed

lemma step_fun_wf2: 
  assumes "as \<noteq> []" "wf_bins1 (map set Bs)" "wf_bin1 (set as) (length Bs)" "wf_bin1 (set bs) (length Bs)" "step_fun Bs (as, bs) = (as', bs')"
  shows "wf_bin1 (set bs') (length Bs)"
  using assms Close2_step_pres2 length_map step_fun step_rel_def by metis
  

definition steps :: "('a, 'b) state list list \<Rightarrow> ('a, 'b) state list \<times> ('a, 'b) state list \<Rightarrow> (('a, 'b)state list \<times> ('a, 'b) state list) option" where
"steps Bs asbs = while_option (\<lambda>(as,bs). as \<noteq> []) (step_fun Bs) asbs"




definition close2_L :: "('a, 'b) state list list \<Rightarrow> ('a, 'b) state list \<Rightarrow> ('a, 'b) state list" where
"close2_L Bs B = snd (the (steps Bs (B,[])))"

lemma steps_sound: assumes "wf_bin1 (set B) (length Bs)" "wf_bins1 (map set Bs)" "steps Bs (B,[]) = Some (B',C)" shows "((step_rel (map set Bs))^**) (set B,{}) ({},set C)"
proof -
  let ?P = "\<lambda>(B',C'). ((step_rel (map set Bs))^**) (set B,{}) (set B',set C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)" 
  show ?thesis using while_option_rule[where P="?P"] assms[unfolded steps_def] step_fun step_fun_wf 
    by (smt (verit, ccfv_SIG) case_prodE case_prodI2 empty_set old.prod.case rtranclp.simps step_fun
        while_option_stop)
qed

(*lemma steps_Some[no_atp]: assumes "wf_bin1 (set as) (length Bs)" "wf_bins1 (map set Bs)"
  shows "\<exists>cs. steps Bs (as,bs) = Some([],cs)"
sorry

lemma close2_sound: assumes "wf_bin1 (set B) (length Bs)" "wf_bins1 (map set Bs)" shows "((step_rel (map set Bs))^** ) (set B, {}) ({}, set (close2_L Bs B))"
using steps_sound steps_Some unfolding close2_L_def
  by (metis assms(1,2) option.sel snd_conv)*)

end (*Earley_Gw_eps*)


context Earley_Gw
begin

(*definition wf_state where
"wf_state = undefined"

abbreviation "wf_states B \<equiv> (\<forall>x\<in>B. wf_state x)"*)

(*unused*)
lemma finite_ex_wf_state1: "finite ({x. wf_state1 x k})"
proof -
  have "{x. wf_state1 x k} \<subseteq> {x. wf_state x k}" by (auto simp add: wf_state1_def)
  then show ?thesis using finite_ex_wf_state rev_finite_subset by auto
qed


(* This is the wellfounded relation for the termination proof.
It should really be called step_fun_less but I have kept the original name.
I adapted it to work on lists rather that sets.
To simplify matters, I dropped the parameter k *)
definition step_fun_less :: "nat \<Rightarrow> ((('n, 'a) state list \<times> ('n, 'a) state list) \<times> (('n, 'a) state list \<times> ('n, 'a) state list)) set" where
"step_fun_less k = (\<lambda>(B,C). card({x. wf_state x k} - (set B \<union> set C))) <*mlex*> inv_image finite_psubset (set o fst)"

lemma step_fun_less_eq: "((A, B), (C,D)) \<in> step_fun_less k \<longleftrightarrow> ((set A, set B), (set C, set D)) \<in> Close2_less k"
  by (simp add: step_fun_less_def Close2_less_def mlex_prod_def)

lemma wf_step_fun_less: "wf (step_fun_less k)"
  by (simp add: step_fun_less_def wf_mlex)

(* This is the important property of step_fun: it goes down in the Close2_less relation.
   The wf_states premises may not be 100% right *)
lemma step_fun_less_step: assumes "B\<noteq>[]" "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "wf_bin1 (set C) (length Bs)"
  shows "(step_fun Bs (B,C), (B,C)) \<in> (step_fun_less (length Bs))"
proof-
  let ?B' = "fst (step_fun Bs (B,C))"
  let ?C' = "snd (step_fun Bs (B,C))"
  have 1: "(?B', ?C') = step_fun Bs (B, C) " by simp
  have "Close2 (map set Bs) (set B, set C) (set ?B', set ?C')"
    using step_fun step_rel_def
    by (simp add: assms(1,3))
  then show ?thesis using assms Close2_less_step step_fun_less_eq 1
    by (metis length_map) 
qed

end (*Earley_Gw*)

context Earley_Gw_eps
begin


lemma step_fun_wf_states: "\<lbrakk>wf_bins1 (map set Bs); wf_bin1 (set B) (length Bs); wf_bin1 (set C) (length Bs); B \<noteq> [] \<rbrakk>
 \<Longrightarrow> \<exists>B' C'. step_fun Bs (B,C) = (B',C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bin1 (set C') (length Bs)"
  by (metis step_fun_wf2 step_fun.elims step_fun_wf)


theorem Close2_NF: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> wf_bin1 (set C) (length Bs) \<Longrightarrow> \<exists>C'. steps Bs (B,C) = Some ([],C')"
unfolding steps_def
using wf_step_fun_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "B = []"
    thus ?thesis by(simp add: while_option_unfold[of _ _ "([],C)"])
  next
    let ?steps = "while_option (\<lambda>(as,bs). as \<noteq> []) (step_fun Bs)"
    assume cons: "B \<noteq> []"
    then obtain B' C'
      where "(B',C') = step_fun Bs (B,C)" and wf': "wf_bin1 (set B') (length Bs)" "wf_bin1 (set C') (length Bs)"
      using step_fun_wf_states[OF less.prems] by auto
    then have "((B',C'), (B, C)) \<in> step_fun_less (length Bs)"
      by (simp add: Earley_Gw.step_fun_less_step \<open>B \<noteq> []\<close> less.prems(1,2,3))
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf']
    show ?thesis
      by (simp add: \<open>(B', C') = step_fun Bs (B, C)\<close> while_option_unfold)
  qed
qed

end


unused_thms

end