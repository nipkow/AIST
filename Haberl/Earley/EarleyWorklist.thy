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
  "Predict_L x k = map (\<lambda>p. State p 0 k) (filter (\<lambda>p. next_sym_Nt x (lhs p)) ps)"

(*fun Complete_L_help :: "('n, 'a) state list \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) state list" where
  "Complete_L_help [] y = []"
| "Complete_L_help (b#bs) y = (let acc = Complete_L_help bs y in (if next_sym_Nt b (lhs(prod y)) then (mv_dot b) # acc else acc))"*)

definition Complete_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state \<Rightarrow> ('n, 'a) state list" where
  "Complete_L Bs y = map mv_dot (filter (\<lambda> b. next_sym_Nt b (lhs(prod y))) (Bs ! from y))"
 (*= Complete_L_help (Bs ! from y) y"*)

definition Init_L :: "('n,'a) state list" where
  "Init_L =  map (\<lambda> p. State p 0 0) (filter (\<lambda> p. lhs p = (S)) ps)"

lemma Init_L_eq_Init: "set Init_L = Init"
  by (auto simp add: Init_L_def Init_def)

definition Scan_L :: "('n,'a) state list \<Rightarrow> nat \<Rightarrow> ('n,'a) state list" where
  "Scan_L Bs k = map mv_dot (filter (\<lambda> b. next_symbol b = Some (w!k)) Bs)"

lemma Scan_L_eq_Scan: "set (Scan_L Bs k) = Scan (set Bs) k"
  by (auto simp add: Scan_L_def Scan_def)


definition minus_L :: "'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" (infix "-l" 50) where
  "minus_L As Bs = foldr (removeAll) Bs As"

lemma minus_L_set[simp]: "set (As -l Bs) = set As - set Bs"
  by (induction Bs) (auto simp add: minus_L_def)


fun step_fun :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list * ('n, 'a) state list \<Rightarrow> ('n, 'a) state list * ('n, 'a) state list" where
  "step_fun Bs ([], C) = undefined" |
  "step_fun Bs ((b#bs), C) = ( (List.union bs (if is_complete b then Complete_L Bs b else Predict_L b (length Bs))) -l (b # C) , (b # C)) "

definition steps :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list \<times> ('n, 'a) state list \<Rightarrow> (('n, 'a)state list \<times> ('n, 'a) state list) option" where
  "steps Bs asbs = while_option (\<lambda>(as,bs). as \<noteq> []) (step_fun Bs) asbs"

definition close2_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list \<Rightarrow> ('n, 'a) state list" where
"close2_L Bs B = snd (the (steps Bs (B,[])))"

fun bins_L :: "nat \<Rightarrow> ('n,'a) state list list" where
"bins_L 0 = [close2_L [] Init_L]" |
"bins_L (Suc k) = (let Bs = bins_L k in Bs @ [close2_L Bs (Scan_L (last Bs) k)])"

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

lemma step_fun_sound: "as \<noteq> [] \<Longrightarrow> wf_bin1 (set as) (length Bs) \<Longrightarrow> step_fun Bs (as,bs) = (as',bs') \<Longrightarrow> step_rel (map set Bs) (set as,set bs) (set as', set bs')"
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

lemma wf1_Predict_L: "wf_state1 st k \<Longrightarrow> wf_bin1 (set (Predict_L st k)) k"
  using wf1_Predict Predict_eq by (auto simp add: wf_bin1_def)

lemma wf1_Complete_L: "wf_bins1 (map set Bs) \<Longrightarrow> wf_state1 st (length Bs) \<Longrightarrow> is_complete st \<Longrightarrow> wf_bin1 (set (Complete_L Bs st)) (length Bs)"
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
    by (metis step_fun_sound step_rel_def)
qed

lemma step_fun_wf2: 
  assumes "as \<noteq> []" "wf_bins1 (map set Bs)" "wf_bin1 (set as) (length Bs)" "wf_bin1 (set bs) (length Bs)" "step_fun Bs (as, bs) = (as', bs')"
  shows "wf_bin1 (set bs') (length Bs)"
  using assms Close2_step_pres2 length_map step_fun_sound step_rel_def by metis
  

lemma steps_sound: assumes "wf_bin1 (set B) (length Bs)" "wf_bin1 (set C) (length Bs)" "wf_bins1 (map set Bs)" "steps Bs (B,C) = Some (B',C')" shows "((step_rel (map set Bs))^**) (set B, set C) ({},set C')"
proof -
  let ?P = "\<lambda>(B',C'). ((step_rel (map set Bs))^**) (set B, set C) (set B',set C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)" 
  show ?thesis using while_option_rule[where P="?P"] assms[unfolded steps_def] step_fun_sound step_fun_wf 
    by (smt (verit, ccfv_SIG) case_prodE case_prodI2 empty_set old.prod.case rtranclp.simps step_fun_sound
        while_option_stop)
qed

lemma steps_sound1: assumes "wf_bin1 (set B) (length Bs)" "wf_bins1 (map set Bs)" "steps Bs (B,[]) = Some (B',C)" shows "((step_rel (map set Bs))^**) (set B,{}) ({},set C)"
  by (metis assms(1,2,3) empty_iff empty_set steps_sound wf_bin1_def)
(*proof -
  let ?P = "\<lambda>(B',C'). ((step_rel (map set Bs))^** ) (set B,{}) (set B',set C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs)" 
  show ?thesis using while_option_rule[where P="?P"] assms[unfolded steps_def] step_fun step_fun_wf 
    by (smt (verit, ccfv_SIG) case_prodE case_prodI2 empty_set old.prod.case rtranclp.simps step_fun
        while_option_stop)
qed*)

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
    using step_fun_sound step_rel_def
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


theorem Close2_L_NF: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> wf_bin1 (set C) (length Bs) \<Longrightarrow> \<exists>C'. steps Bs (B,C) = Some ([],C')"
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

lemma Close2_close2: "wf_bins1 Bs \<Longrightarrow> wf_bin1 B (length Bs) \<Longrightarrow> Bs \<turnstile> (B, {}) \<rightarrow>* ({}, close2 Bs B)"
  by (metis Earley.Earley_Gw_eps.Close2_NF Earley_Gw.Close1_subset_Close2 Earley_Gw.Close2_steps_subset_Close1' Earley_Gw_eps_axioms close2_eq_Close1 empty_iff
      subset_antisym wf_bin1_def)


lemma close2_L_eq_Close1: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> set (close2_L Bs B) = Close1 (map set Bs) (set B)"
proof-
  assume assms: "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)"

  have "wf_bin1 (set []) (length Bs)" by (auto simp add: wf_bin1_def)
  then obtain D where D1: "steps Bs (B,[]) = Some ([],D)" using assms Close2_L_NF
    by blast
  then have "(map set Bs) \<turnstile> (set B, {}) \<rightarrow>* ({}, set D)" using steps_sound
    by (metis Earley_Gw.step_rel_def assms(1,2) steps_sound1)
  then have DC1: "set D = Close1 (map set Bs) (set B)"
    by (simp add: Close1_subset_Close2 Close2_steps_subset_Close1' subset_antisym)
  have "set D = set (close2_L Bs B)" using D1 by (auto simp add: close2_L_def)
  then show ?thesis using DC1 by auto
qed

lemma close2_L_eq_close2: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> set (close2_L Bs B) = close2 (map set Bs) (set B)"
  by (auto simp add: close2_L_eq_Close1 close2_eq_Close1)

lemma close2_L_eq_Close: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> set (close2_L Bs B) = Close (map set Bs) (set B) "
  by (auto simp add: close2_L_eq_Close1 Close1_eq_Close)

lemma set_last: "As \<noteq> [] \<Longrightarrow> set (last As) = last (map set As)"
  by (induction As) auto

lemma length_bins_L: "length (bins_L k) = Suc k"
  by (induction k) (auto simp add: Let_def)

lemma bins_L_eq_bins: "k \<le> length w \<Longrightarrow> map set (bins_L k) = bins k"
proof (induction k)
  case 0
  have "wf_bins1 (map set []) \<and> wf_bin1 (set Init_L) 0"
    by (simp add: Init_L_eq_Init wf_bin1_Init wf_bins1_def)
  then have "set (close2_L [] Init_L) = Close [] Init"
    by (simp add: close2_L_eq_Close Earley_Gw.Init_L_eq_Init)
  then show ?case by simp
next
  case (Suc k)
  let ?Bs = "bins_L k"
  have 1: "set (Scan_L (last ?Bs) k) = (Scan (last (map set ?Bs)) k)" using Suc
    by (metis Scan_L_eq_Scan Suc_leD bins_nonempty map_is_Nil_conv set_last)
  have "wf_bin1 (set (last ?Bs)) k"
    by (metis Earley_Gw.bins_nonempty Suc.IH Suc.prems Suc_leD last_map list.map_disc_iff wf_bin1_last)
  then have 2: "wf_bin1 (set (Scan_L (last ?Bs) k)) (Suc k)"
    using Scan_L_eq_Scan Suc.prems wf_bin1_Scan by fastforce
  have "wf_bins1 (map set (bins_L k))"
    by (simp add: Suc.IH Suc.prems Suc_leD wf_bins1_bins)
  
  then have "set (close2_L ?Bs (Scan_L (last ?Bs) k)) = Close (map set ?Bs) (Scan (last (map set ?Bs)) k)"
    using 2 by (simp add: close2_L_eq_Close length_bins_L 1)
  then show ?case using Suc by (auto simp add: Let_def)
qed 

lemma "k \<le> length w \<Longrightarrow> set (bins_L (length w) ! k) = \<S> k"
  using bins_eq_\<S> bins_L_eq_bins length_bins_L
  by (metis less_Suc_eq_le nth_map order_refl)
(*lemma bins0_close2_L: "bins 0 = map set [close2_L [] Init_L]"
  by(simp flip: Close1_eq_Close add: close2_L_eq_Close1 wf_bins1_def wf_bin1_Init Init_L_eq_Init)

lemma binsSuc_close2_L:
  "k < length w \<Longrightarrow> bins (Suc k) = map set (let Bs = bins_L k in Bs @ [close2_L Bs (Scan_L (last Bs) k)])"
by(simp flip: Close1_eq_Close add: close2_eq_Close1 wf_bins1_bins wf_bin1_Scan wf_bin1_last Let_def)*) 

end

definition ps where "ps = [((0::nat), [Tm (1::int)]), (0, [Nt (0::nat), Nt 0])]"
definition S :: nat where "S = 0"
definition w1 where "w1 = [1, 1, (1 :: int)]"

interpretation Earley_Gw_eps
  where ps = ps and S = S and w0 = w1 
proof
  show "Earley_Gw.\<epsilon>_free ps" by (auto simp add: Earley_Gw.\<epsilon>_free_def ps_def rhs_def)
qed

declare Earley_Gw.Predict_L_def[code]
declare Earley_Gw.mv_dot_def[code]
declare Earley_Gw.Complete_L_def[code]
declare Earley_Gw.Scan_L_def[code]
declare Earley_Gw.minus_L_def[code]
declare Earley_Gw.Init_L_def[code]
declare Earley_Gw.step_fun.simps[code]
declare Earley_Gw.steps_def[code]
declare Earley_Gw.close2_L_def[code]
declare Earley_Gw.bins_L.simps[code]
declare Earley_Gw.w_def[code]


value "bins_L 0"
value "bins_L 1"
value "bins_L 2"
value "bins_L 3"

unused_thms

(*unused*)
context Earley_Gw_eps
begin
lemma "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> set (close2_L Bs B) \<subseteq> close2 (map set Bs)  (set B)"
proof -
  assume wf: "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)"
  have 1: "wf_bin1 (set []) k" for k by (auto simp add: wf_bin1_def)
  from wf 1 obtain C' where C': "steps Bs (B,[]) = Some ([],C')" using Close2_L_NF by blast
  then have "(step_rel (map set Bs))^** (set B, {}) ({}, set (close2_L Bs B))" 
    using wf Close2_NF steps_sound1 by (auto simp add: close2_L_def)
  then show ?thesis
    by (simp add: Close2_steps_subset_Close1' close2_eq_Close1 local.wf(1,2) step_rel_def)
qed


lemma Close2_step_subset_Close1_2: "Bs \<turnstile> (B,C) \<rightarrow> (B',C') \<Longrightarrow> B' \<union> C' \<subseteq> C \<union> Close1 Bs B"
proof(induction rule: Close2_induct)
  case (Predict x B C)
  then show ?case using Close1_incr Close1.Predict by blast
next
  case (Complete x B C)
  have *: "B \<subseteq> Close1 Bs B" using Close1_incr by blast
  have 1: "x \<in> Close1 Bs B" using Complete Close1_incr by blast
  then have "Complete Bs x \<subseteq> Close1 Bs B"
    using Complete Close1.Complete * unfolding Complete_def next_symbol_def by (auto split: if_splits)
  then show ?case using * 1 by fastforce
qed


lemma Close2_step_snd_subset: "Bs \<turnstile> (B,C) \<rightarrow> (D,E) \<Longrightarrow> C \<subseteq> E"
by (induction rule: Close2_induct) auto


lemma Close2_steps_snd_subset: "Bs \<turnstile> (B,C) \<rightarrow>* (D,E) \<Longrightarrow> C \<subseteq> E"
proof(induction rule: rtranclp_induct2)
  case refl
  then show ?case by simp
next
  case (step B' C' B'' C'')
  then show ?case using Close2_step_snd_subset by fastforce
qed

lemma Close2_disj: "Bs \<turnstile> (B, C) \<rightarrow> (D, E) \<Longrightarrow> D \<inter> E = {}"
  by (induction rule: Close2_induct) auto

lemma Close2_steps_subset_Close1'_2: "Bs \<turnstile> (B,C) \<rightarrow>* (D,E) \<Longrightarrow> B \<inter> C = {} \<Longrightarrow> D \<union> E \<subseteq> C \<union> Close1 Bs B"
proof(induction rule: rtranclp_induct2)
  case refl
  thus ?case
    using Close1_incr by blast
next
  case (step B' C' B'' C'')
  have 1: "B' \<subseteq> B'' \<union> C''" using step Close2_step_incr by auto
  have "B'' \<union> C'' \<subseteq> C' \<union> Close1 Bs B'"
    using Close2_step_subset_Close1_2[OF step.hyps(2)] by simp
  then have *: "B'' \<union> C'' \<subseteq> B' \<union> C' \<union> Close1 Bs B'" using 1 by auto
  have 2: "C \<subseteq> C'" using Close2_steps_snd_subset step by auto
  have 3: "B' \<inter> C' = {}" using step
    by (simp add: Close2_steps_disj)
  then have "B' \<subseteq> Close1 Bs B" using step 2 by fastforce
  then have "Close1 Bs B' \<subseteq> Close1 Bs B"
    using Close1_idemp1 Close1_mono1 by blast
  then show ?case
    using * step by fastforce
qed

lemma 1: "Bs \<turnstile> (B, C) \<rightarrow> (D, E) \<Longrightarrow> Bs \<turnstile> (B, C \<union> F) \<rightarrow> (D - F, E \<union> F)"
proof-
  assume assm: "Bs \<turnstile> (B, C) \<rightarrow> (D, E)"
  then show ?thesis
  proof (cases rule: Close2.cases)
    case (Predict x)
    have "B \<union> Predict x (length Bs) - ((C \<union> F) \<union> {x}) = B \<union> Predict x (length Bs) - (C \<union> {x}) - F" by auto
    then show ?thesis using Predict Close2.Predict[of x B Bs "C \<union> F"]
      by simp
  next
    case (Complete x)
    have "B \<union> Complete Bs x - ((C \<union> F) \<union> {x}) = B \<union> Complete Bs x - (C \<union> {x}) - F" by auto
    then show ?thesis using Complete Close2.Complete[of x B Bs "C \<union> F"] by simp
  qed
qed



lemma Close1_elem_union: "x \<in> Close1 Bs (B \<union> C) \<Longrightarrow> x \<in> Close1 Bs B \<union> Close1 Bs C"
proof (induction rule: Close1.induct)
  case (Init x)
  then show ?case
    using Close1.Init by blast 
next
  case (Predict x x')
  then show ?case
    using Close1.Predict by blast 
next
  case (Complete y x)
  then show ?case
    using Close1.Complete by blast 
qed

lemma Close_of_empty: "Close1 Bs {} = {}"
proof-
  have "Bs \<turnstile> ({},{}) \<rightarrow>* ({},{})" by simp
  then have "Close1 Bs {} \<subseteq> {}" using Close1_subset_Close2 by auto
  then show "Close1 Bs {} = {}" by auto
qed

lemma Close2_steps_from_empty: "Bs \<turnstile> ({},C) \<rightarrow>* ({},C') \<Longrightarrow> C = C'"
proof-
  assume assm: "Bs \<turnstile> ({},C) \<rightarrow>* ({},C')"
  then have " C' \<subseteq> C \<union> Close1 Bs {}" using Close2_steps_subset_Close1'_2 by auto
  then have 1: "C' \<subseteq> C" using Close_of_empty by simp
  have 2: "C \<subseteq> C'" using assm
    using Close2_steps_snd_subset by auto
  then show ?thesis using 1 by auto
qed

(*lemma "((step_rel (map set Bs))^** ) (set B, set C) ({},set C') \<Longrightarrow> wf_bins1 (map set Bs) 
  \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> wf_bin1 (set C) (length Bs) \<Longrightarrow> (steps Bs (B, C)) = Some ([], D) 
  \<Longrightarrow> set D = set C'"
unfolding steps_def
using wf_step_fun_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C D rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "B = []"
    thus ?thesis using less Close2_steps_from_empty
      by (simp add: while_option_unfold[of _ _ "([],C)"] step_rel_def)
   next
    let ?steps = "while_option (\<lambda>(as,bs). as \<noteq> []) (step_fun Bs)"
    assume cons: "B \<noteq> []"
    then obtain B' C''
      where step: "(B',C'') = step_fun Bs (B,C)" and wf': "wf_bin1 (set B') (length Bs)" "wf_bin1 (set C'') (length Bs)"
      using step_fun_wf_states[OF less.prems(2,3,4)] by auto
    then have "((B',C''), (B, C)) \<in> step_fun_less (length Bs)"
      by (simp add: Earley_Gw.step_fun_less_step \<open>B \<noteq> []\<close> less.prems(2,3,4))
    have "steps Bs (B', C'') = Some ([], D)" using less cons while_option_unfold
      by (metis (mono_tags, lifting) Earley_Gw_eps.steps_def Earley_Gw_eps_axioms case_prodI local.step)
      (*using Close2_NF less.prems(2) wf'(1,2) by blast*)
    then have "((step_rel (map set Bs))^** ) (set B', set C'') ({},set C')"
      using less.prems(1) step steps_sound cons wf'
    from less.hyps[OF this \<open>wf_bins1 (map set Bs)\<close> wf']
    show ?thesis
      by (simp add: \<open>(B', C'') = step_fun Bs (B, C)\<close> while_option_unfold)
  qed
qed*)
end (*Gw_eps*)



end