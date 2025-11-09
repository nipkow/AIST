theory EarleyWorklist

imports "Earley" "HOL-Library.While_Combinator" "HOL-Data_Structures.Define_Time_Function"

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

lemma bins_L_eq_\<S>: "i \<le> k \<Longrightarrow> k \<le> length w \<Longrightarrow> set (bins_L k ! i) = \<S> i"
  using bins_eq_\<S> bins_L_eq_bins length_bins_L
  by (metis bins_L_eq_bins bins_eq_\<S>_gen le_imp_less_Suc length_bins_L nth_map)
(*lemma bins0_close2_L: "bins 0 = map set [close2_L [] Init_L]"
  by(simp flip: Close1_eq_Close add: close2_L_eq_Close1 wf_bins1_def wf_bin1_Init Init_L_eq_Init)

lemma binsSuc_close2_L:
  "k < length w \<Longrightarrow> bins (Suc k) = map set (let Bs = bins_L k in Bs @ [close2_L Bs (Scan_L (last Bs) k)])"
by(simp flip: Close1_eq_Close add: close2_eq_Close1 wf_bins1_bins wf_bin1_Scan wf_bin1_last Let_def)*) 

end


(*TODO space analyse und Zeit analyse mit eigen gesetzten laufzeiten für listenoperationen*)

(*Section space analysis*)
context Earley_Gw
begin

definition "K = Max { length (rhs r) | r. r \<in> set ps }"
definition "N = length w0"
definition "L = length ps"

lemma card_wf: "\<forall>p \<in> set ps. length (rhs p) \<le> k \<Longrightarrow> \<forall>x \<in> bs. wf_state x i \<Longrightarrow> card bs \<le> (length ps) * (Suc k) * (Suc i)"
proof -
  assume assm: "\<forall>p \<in> set ps. length (rhs p) \<le> k" "\<forall>x \<in> bs. wf_state x i"
  let ?f = "\<lambda> (p, m, k). State p m k"
  define Top where "Top = (P \<times> {0..k} \<times> {0..i})"
  hence top_card: "card Top = card (set ps) * Suc k * (Suc i)"
    using Groups_Big.card_cartesian_product by (auto simp add: add_mult_distrib add_mult_distrib2)
  have fin: "finite Top" using finite_cartesian_product finite Top_def by blast
  have inj: "inj_on ?f Top"
    unfolding Top_def inj_on_def by simp
  have 1: "bs \<subseteq> ?f ` Top"
  proof
    fix x
    assume "x \<in> bs"
    then have "\<exists>p m k. x = State p m k \<and> p \<in> P \<and> m \<le> length (rhs p) \<and> k \<le> i \<and> i \<le> length w"
      by (metis Earley_Gw.wf_state_def state.exhaust_sel assm(2))
    then obtain p m j where x: "x = State p m j" and wf: "p \<in> P \<and> m \<le> length (rhs p) \<and> j \<le> i \<and> i \<le> length w" by blast
    then have 1: "(p, m, j) \<in> Top" using assm by (auto simp add: Top_def)
    have "?f (p, m, j) = x" using x by simp
    then show "x \<in> (\<lambda>(p, m, k). State p m k) ` Top" using 1 by blast
  qed

  then have "card  bs \<le> card Top" using fin
    by (simp add: surj_card_le)
  then show ?thesis using top_card card_length
    by (metis (no_types, lifting) dual_order.trans mult_le_mono1)
qed

lemma card_wf1: "\<forall>x \<in> bs. wf_state x i \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
proof-
  assume assm: "\<forall>x \<in> bs. wf_state x i"
  have "K = Max (length ` (rhs ` (set ps)))" using K_def
    by (metis Setcompr_eq_image image_image)
  then have "\<forall>p \<in> (length ` (rhs ` (set ps))). p \<le> K" using K_def by (auto)
  then have "\<forall>p \<in> set ps. length (rhs p) \<le> K" by simp
  then show ?thesis using card_wf assm L_def by simp
qed

lemma card_wf_bin1: "wf_bin1 bs i \<Longrightarrow> card bs \<le> L * (Suc K) * (Suc i)"
  using card_wf1 by (simp add: wf_bin1_def wf_state1_def)

lemma card_Si: "card (\<S> i) \<le> L * (Suc K) * (Suc i)"
  using card_wf1 wf_EarleyS by simp

lemma Si_empty: "i > length w \<Longrightarrow> \<S> i = {}"
  using wf_Earley by (fastforce simp add: \<S>_def wf_state_def)

lemma "card Earley \<le> L * (Suc K) * (Suc (length w))^2"
proof-
  let ?X = "{x. (\<exists>i \<le> length w. x = {(y, z). wf_state y z \<and> z = i})}"

  have "Earley \<subseteq> {(x, k). wf_state x k \<and> k \<le> length w}"
    using wf_Earley by (fastforce simp add: wf_state_def)
  also have "... = \<Union> {x. (\<exists>i \<le> length w. x = {(y, z). wf_state y z \<and> z = i})}" by (auto simp add: wf_state_def)
  finally have 1: "Earley \<subseteq> \<Union> {x. (\<exists>i \<le> length w. x = {(y, z). wf_state y z \<and> z = i})}".

  have 2: "x \<in> ?X \<longrightarrow> card x \<le> L * (Suc K) * (Suc (length w))" for x 
  proof
    fix x
    assume assm: "x \<in> ?X"
    then have "\<exists>i \<le> length w. \<forall>(y, z) \<in> x. wf_state y i \<and> z = i" by auto
    then obtain i where P: "\<forall>(y, z) \<in> x. wf_state y i \<and> z = i" and l: "i \<le> length w" by blast
    then have 3: "x \<subseteq> {y. wf_state y i} \<times> {i}" by fastforce

    have "finite ({y. wf_state y i} \<times> {i})"
      by (simp add: finite_ex_wf_state)
    then have "card x \<le> card {y. wf_state y i}" 
      using Groups_Big.card_cartesian_product[of "{y. wf_state y i}" "{i}"] 
            Finite_Set.card_mono[of "{y. wf_state y i} \<times> {i}"] 3 by auto
    also have "... \<le> L * (Suc K) * (Suc i)" using card_wf1 by auto
    also have "... \<le> L * (Suc K) * (Suc (length w))" using l by auto
    finally show "card x \<le> L * (Suc K) * (Suc (length w))".
  qed

  let ?f = "\<lambda>k. {(x, z). wf_state x z \<and> z = k}"
  let ?Y = "{i. i \<le> (length w)}"

  have fin: "?X = ?f ` ?Y" and "finite ?Y" by auto
  then have "card ?X  \<le> card ?Y"
    using card_image_le by force
  then have 3: "card ?X \<le> Suc (length w)" by auto

  have "\<forall> x \<in> ?X. \<exists>i. x \<subseteq> {y. wf_state y i} \<times> {i}" by fastforce
  then have "\<forall>x \<in> ?X. finite x" using finite_wf_state
    by (metis (no_types, lifting) ext finite.emptyI finite_SigmaI finite_ex_wf_state finite_insert rev_finite_subset)
  then have "finite (\<Union> ?X)"
    by (simp add: fin)
  then have "card Earley \<le> card (\<Union> ?X)" using 1
    by (meson card_mono)
  also have "... \<le> sum card ?X" using Groups_Big.card_Union_le_sum_card by simp
  also have "... \<le> L * (Suc K) * (Suc (length w)) * (Suc (length w))" 
    using 2 3 Groups_Big.sum_bounded_above[of ?X card "L * (Suc K) * (Suc (length w))"]
    by (smt (verit, best) le_trans mult_le_mono2 mult_of_nat_commute of_nat_id)
  finally show ?thesis
    by (metis mult.assoc power2_eq_square)
qed


fun T_Scan_L :: "('n,'a) state list \<Rightarrow> nat \<Rightarrow> nat" where
"T_Scan_L Bs k = length Bs"

fun T_Predict_L :: "('n,'a) state \<Rightarrow> nat \<Rightarrow> nat" where
"T_Predict_L _ _ = length ps"

fun T_Complete_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state \<Rightarrow> nat" where
"T_Complete_L Bs y = length (Bs ! from y)"

definition T_Init_L where
"T_Init_L = length ps"


fun minus_opt :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list \<Rightarrow> ('n, 'a) state list" where
"minus_opt Bs [] = []" |
"minus_opt Bs (a#as) = (if a \<in> set (Bs ! (from a)) then minus_opt Bs as else a # (minus_opt Bs as))"

lemma minus_opt_simp: "x \<in> set (minus_opt Bs xs) \<longleftrightarrow> x \<in> set xs \<and> x \<notin> set (Bs ! (from x))"
  by (induction xs) auto

lemma "\<forall>x. x \<in> xs \<longleftrightarrow> x \<in> set (Bs ! from x) \<Longrightarrow> set (minus_opt Bs ys) = (set ys - xs)"
  by (fastforce simp add: minus_opt_simp)

fun T_minus_opt where
"T_minus_opt Bs [] = 0" |
"T_minus_opt Bs (a#as) = (length (Bs ! from a)) + T_minus_opt Bs (as)"

(*actual runtime of minus_L is currently (length Bs)^2 or smth like that, this runtime assumes optimizations using descripitons from Earley*)
fun T_minus_L where
"T_minus_L As Bs = length As"

fun T_union where
"T_union As Bs = length Bs"

fun T_step_fun :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list * ('n, 'a) state list \<Rightarrow> nat" where
"T_step_fun Bs ((b#bs), C) = (let X = (if is_complete b then Complete_L Bs b else Predict_L b (length Bs)) in
 (if is_complete b then T_Complete_L Bs b else T_Predict_L b (length Bs)) + (T_union bs X) + (T_minus_L (List.union bs X) (b # C))) "

fun steps_time :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list \<times> ('n, 'a) state list \<Rightarrow> nat \<Rightarrow> ((('n, 'a)state list \<times> ('n, 'a) state list) \<times> nat) option" where
"steps_time Bs asbs y = while_option (\<lambda>((as,bs),k). as \<noteq> []) (\<lambda>((as,bs),k). (step_fun Bs (as, bs), k + T_step_fun Bs (as, bs))) (asbs, y)"

fun T_steps :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list \<times> ('n, 'a) state list \<Rightarrow> nat" where
"T_steps Bs asbs = snd (the (steps_time Bs asbs 0))"

definition T_close2_L :: "('n, 'a) state list list \<Rightarrow> ('n, 'a) state list \<Rightarrow> nat" where
"T_close2_L Bs B = T_steps Bs (B,[])"

(*dissregards append runtime*)
fun T_bins_L where
"T_bins_L 0 = (T_close2_L [] Init_L) + (T_Init_L)" |
"T_bins_L (Suc k) = (T_bins_L k) + (let Bs = bins_L k in T_close2_L Bs (Scan_L (last Bs) k) + T_Scan_L (last Bs) k) "

end (*Context Earley_Gw*)

context Earley_Gw_eps
begin

lemma distinct_Init: "distinct ps \<Longrightarrow> distinct Init_L"
proof -                                           
  assume assm: "distinct ps"
  have "inj_on (\<lambda> p. State p 0 0) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. State p 0 0) ps)" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Init_L_def distinct_map_filter)
qed

lemma distinct_Predict_L: "distinct ps \<Longrightarrow> distinct (Predict_L x k)"
proof -                                           
  assume assm: "distinct ps"
  have "inj_on (\<lambda>p. State p 0 k) (set ps)"
    using inj_on_def by auto
  then have "distinct (map (\<lambda> p. State p 0 k) ps)" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Predict_L_def distinct_map_filter)
qed

lemma distinct_Complete_L: "distinct (Bs ! from y) \<Longrightarrow> distinct (Complete_L Bs y)"
proof -                                           
  assume assm: "distinct (Bs ! from y)"
  have "inj_on mv_dot (set (Bs ! from y))"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel state.expand state.inject)
  then have "distinct (map mv_dot (Bs ! from y))" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Complete_L_def distinct_map_filter)
qed

lemma distinct_Scan_L: "distinct B \<Longrightarrow> distinct (Scan_L B k)"
proof -                                           
  assume assm: "distinct B"
  have "inj_on mv_dot (set B)"
    using inj_on_def mv_dot_def
    by (smt (verit, ccfv_threshold) add_right_cancel state.expand state.inject)
  then have "distinct (map mv_dot B)" using assm by (simp add: distinct_map)
  then show ?thesis using assm by (simp add: Scan_L_def distinct_map_filter)
qed

lemma distinct_List_union: "distinct Bs \<Longrightarrow> distinct (List.union As Bs)"
  by simp

lemma distinct_List_minus: "distinct As \<Longrightarrow> distinct (As -l Bs)"
  unfolding minus_L_def
  by(induction Bs) (auto simp add: distinct_removeAll)

lemma distinct_step_fun: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> \<forall>i < length Bs. distinct (Bs ! i) \<Longrightarrow> distinct ps \<Longrightarrow> distinct (B@C) \<Longrightarrow> B \<noteq> [] 
  \<Longrightarrow> (step_fun Bs (B, C)) = (D, E) \<Longrightarrow> distinct (D@E)"
proof-
  assume comp_assm: "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" 
    and assm: "distinct ps" "distinct (B@C)" "B \<noteq> []" and step: "(step_fun Bs (B, C)) = (D, E)"
  then obtain b bs where bbs: "B = b # bs"
    using list.exhaust by blast
  then have "b \<notin> set C" using assm by auto
  then have 1: "distinct E" using bbs assm step by auto

  have "is_complete b \<longrightarrow> from b < length Bs" using bbs comp_assm wf_bin1_def
    by (simp add: wf_state1_def)
  then have "is_complete b \<longrightarrow> distinct (Complete_L Bs b)" using comp_assm step distinct_Complete_L by auto
  then have 2: "distinct D" using assm step bbs distinct_Predict_L by (auto simp add: distinct_List_union distinct_List_minus)

  show ?thesis using 1 2 step bbs by auto
qed

lemma distinct_steps: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct ps" "distinct (B@C)" "steps Bs (B,C) = Some (B',C')" "distinct C" shows "distinct (B'@C')"
proof -
  let ?P = "\<lambda>(B',C'). distinct (B'@C') \<and> wf_bin1 (set B') (length Bs) \<and> wf_bins1 (map set Bs) \<and> (\<forall>i < length Bs. distinct (Bs ! i)) \<and> distinct ps" 
  show ?thesis using while_option_rule[where P="?P"] assms[unfolded steps_def] step_fun_sound step_fun_wf distinct_step_fun
    by (smt (verit, ccfv_SIG) case_prodE case_prodI2 empty_set old.prod.case rtranclp.simps
        while_option_stop)
qed


lemma distinct_close2: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct ps" "distinct B" shows "distinct (close2_L Bs B)"
proof-
  have "wf_bin1 (set []) (length Bs)" by (simp add: wf_bin1_def)
  then obtain C' where c': "steps Bs (B, []) = Some ([], C')" using Close2_L_NF assms by blast
  have "distinct []" by simp
  then have "distinct C'" using distinct_steps assms c'
    by (metis Int_empty_right distinct_append empty_set)
  then show ?thesis using close2_L_def c' by auto
qed

lemma distinct_bins_L: "k \<le> length w \<Longrightarrow> distinct ps \<Longrightarrow> i < length (bins_L k) \<Longrightarrow> distinct (bins_L k ! i)"
proof(induction k arbitrary: i)
  case 0
  then have "i = 0"
    by simp
  then show ?case using distinct_Init distinct_close2
    by (simp add: "0.prems"(1,2) Init_L_eq_Init wf_bin1_Init wf_bins1_def)
next
  case (Suc k)
  then have 1: "i < Suc k \<longrightarrow> distinct (bins_L (Suc k) ! i)" using length_bins_L by (auto simp add: Let_def nth_append_left)

  have 2: "wf_bins1 (map set (bins_L k))" using "Suc.prems"(1)
    by (simp add: bins_L_eq_bins wf_bins1_bins)
  have "wf_bin1 (set (last (bins_L k))) k" using "Suc.prems"(1)
    by (metis Suc_leD Zero_not_Suc bins_L_eq_bins last_map length_bins_L list.size(3) wf_bin1_last)
  then have 3: "wf_bin1 (set (Scan_L (last (bins_L k)) k)) (Suc k)"
    using Scan_L_eq_Scan Suc.prems(1) wf_bin1_Scan by auto
  have "bins_L k \<noteq> []"
    by (metis Zero_not_Suc length_0_conv length_bins_L)
  then have "distinct (last (bins_L k))" using last_conv_nth length_bins_L Suc by (auto simp add: last_conv_nth)
  then have 4: "distinct (Scan_L (last (bins_L k)) k)" using distinct_Scan_L by simp
  have 5: "distinct (close2_L (bins_L k) (Scan_L (last (bins_L k)) k))" using 2 3 4 Suc distinct_close2
    by (simp add: length_bins_L)

  have "\<not> i < Suc k \<longrightarrow> i = Suc k" using Suc
    by (metis le_Suc_eq length_bins_L less_Suc_eq_le)
  then show ?case using 1 5 using nth_append_length[of "bins_L k"] length_bins_L by (auto simp add: Let_def)
qed

lemma T_Complete_Bound: "distinct ps \<Longrightarrow> Bs = bins_L k \<Longrightarrow> from y < length Bs \<Longrightarrow> k \<le> length w \<Longrightarrow> T_Complete_L Bs y \<le> L * (Suc K) * (Suc (length Bs))"
proof-
  assume assms: "distinct ps" "Bs = bins_L k" "from y < length Bs" "k \<le> length w"
  then have 1: "set (Bs ! (from y)) = \<S> (from y)" using bins_L_eq_\<S>
    by (simp add: length_bins_L)
  have 2: "length (Bs ! from y) = card (set (Bs ! (from y)))" using distinct_bins_L assms by (auto simp flip: distinct_card)
  have "from y \<le> length w" using assms by (auto simp add: length_bins_L)
  then have "T_Complete_L Bs y \<le> L * (Suc K) * (Suc (from y))" using 1 2 card_Si assms by auto
  then show ?thesis using \<open>from y < length Bs\<close>
    by (meson Suc_le_mono le_trans less_or_eq_imp_le mult_le_mono2)
qed

(*helper*)
lemma length_union: "length (List.union as bs) \<le> length as + length bs"
proof(induction as arbitrary: bs)
  case Nil
  then show ?case by (auto simp add: List.union_def)
next
  case (Cons a as)
  then have "length (fold List.insert as bs) \<le> length as + length bs" by (auto simp add: List.union_def List.insert_def)
  then show ?case using Cons.IH[of "a#bs"] by (auto simp add: List.union_def List.insert_def)
qed

lemma T_step_fun_bound: assumes "B \<noteq> []" "distinct ps" "wf_bins1 (map set Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "wf_bin1 (set B) (length Bs)" "distinct B"
  shows "T_step_fun Bs (B, C) \<le> 3*(L * (Suc K) * (Suc (length Bs)))"
proof-
  obtain b bs where bbs: "B = b#bs" using assms
    using list.exhaust by blast
  have "length (b#bs) \<le> L * (Suc K) * (Suc (length Bs))" using card_wf_bin1[of "set (b#bs)"] assms by (auto simp add: distinct_card bbs)
  then have 5: "length bs \<le> L * (Suc K) * (Suc (length Bs))" by simp

  show ?thesis
  proof(cases "is_complete b")
    case True
    then have 1: "from b < length Bs" using assms
      by (simp add: bbs wf_bin1_def wf_state1_def)
  
    then have 2: "distinct (Bs ! from b)" using assms
      by simp
    have "wf_bin1 (set (Bs ! from b)) (from b)" using assms 1
      by (simp add: wf_bins1_def)
    then have 3: "length (Bs ! from b) \<le> L * (Suc K) * (Suc (from b))" 
      using card_wf1 2
      by (metis card_wf_bin1 distinct_card)
    then have 4: "length (Bs ! from b) \<le> L * (Suc K) * (Suc (length Bs))" using 1
      by (meson Suc_le_mono le_trans mult_le_mono2 nat_less_le)
  
    have x: "wf_bin1 (set (Complete_L Bs b)) (length Bs)"
      by (metis Earley_Gw_eps.wf1_Complete_L Earley_Gw_eps_axioms True assms(3,5) bbs list.set_intros(1) wf_bin1_def)
    then have 6: "length (Complete_L Bs b) \<le> L * (Suc K) * (Suc (length Bs))" 
      using card_wf_bin1[of "set (Complete_L Bs b)"] assms distinct_Complete_L 2 by (auto simp add: distinct_card)

    have "wf_bin1 (set (List.union bs (Complete_L Bs b))) (length Bs)" using assms bbs x by (auto simp add: wf_bin1_def)
    then have "length (List.union bs (Complete_L Bs b)) \<le> L * (Suc K) * (Suc (length Bs))"
      by (metis "2" card_wf_bin1 distinct_Complete_L distinct_List_union distinct_card)
    then have "length (Bs ! from b) + length (Complete_L Bs b) + length (List.union bs (Complete_L Bs b))
      \<le> 3*(L * (Suc K) * (Suc (length Bs)))" using 4 6 by linarith
    then show ?thesis using True by (auto simp add: Let_def bbs)
  next
    case False
    have "length (Predict_L b (length Bs)) \<le> L" by (auto simp add: L_def Predict_L_def)
    then have 1: "length (Predict_L b (length Bs)) \<le> L * (Suc K) * (Suc (length Bs))" by simp

    have "wf_bin1 (set (Predict_L b (length Bs))) (length Bs)"
      by (metis assms(5) bbs list.set_intros(1) wf1_Predict_L wf_bin1_def)
    then have "wf_bin1 (set (List.union bs (Predict_L b (length Bs)))) (length Bs)" using assms bbs by (auto simp add: wf_bin1_def)
    then have 2: "length (List.union bs (Predict_L b (length Bs))) \<le> L * (Suc K) * (Suc (length Bs))"
      by (metis assms(2) card_wf_bin1 distinct_List_union distinct_Predict_L distinct_card)
    have "length ps \<le> L * (Suc K) * (Suc (length Bs))" by (simp add: L_def)

    then have "length ps + length (Predict_L b (length Bs)) + length (List.union bs (Predict_L b (length Bs)))
       \<le> 3*(L * (Suc K) * (Suc (length Bs)))"
      using 1 2 by linarith
    then show ?thesis using False by (auto simp add: Let_def bbs)
  qed
qed

lemma length_step_fun2: "B \<noteq> [] \<Longrightarrow> (B', C') = step_fun Bs (B, C) \<Longrightarrow> length C' = Suc (length C)"
  using step_fun.elims[of Bs "(B, C)" "step_fun Bs (B, C)"] by fastforce

lemma steps_time_time: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "wf_bin1 (set C) (length Bs)" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct ps" "distinct (B@C)" 
  "steps_time Bs (B,C) k = Some ((B',C'), k')" "k \<le> (length C) * (3*(L * (Suc K) * (Suc (length Bs))))" "distinct C" 
  shows "k' \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))" and "wf_bin1 (set C') (length Bs)" and "distinct C'"
proof -
  let ?P3 = "\<lambda>((B',C'),k). wf_bin1 (set B') (length Bs) \<and> wf_bin1 (set C') (length Bs) \<and> wf_bins1 (map set Bs)"
  let ?P1 = "\<lambda>((B',C'),k). wf_bin1 (set B') (length Bs) \<and> wf_bin1 (set C') (length Bs) \<and> wf_bins1 (map set Bs) \<and> distinct (B'@C') \<and> (\<forall>i < length Bs. distinct (Bs ! i)) \<and> distinct ps"
  let ?P2 = "\<lambda>((B',C'),k). k \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))"
  let ?P = "\<lambda>x. ?P1 x \<and> ?P2 x"
  let ?b = "(\<lambda>((as,bs),k). as \<noteq> [])"
  let ?c = "(\<lambda>((as,bs),k). (step_fun Bs (as, bs), k + T_step_fun Bs (as, bs)))"

  have init: "?P ((B,C), k)" using assms by auto


  have P1: "(?P1 ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P1 (?c ((a,b), y)))" for a b y using distinct_step_fun step_fun_wf step_fun_wf2
    by (smt (verit, ccfv_threshold) case_prodI2' case_prod_conv)
  have "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P2 (?c ((a,b), y)))" for a b y
  proof -
    assume assms: "?P ((a,b), y)" "?b ((a,b), y)"
    then have 1: "T_step_fun Bs (a, b) \<le> 3*(L * (Suc K) * (Suc (length Bs)))" using T_step_fun_bound by auto
    obtain a' b' y' where P1: "?c ((a,b),y) = ((a', b'), y')"
      by (metis (lifting) old.prod.exhaust)
    then have "(a', b') = step_fun Bs (a,b)" by auto
    then have "length b' = Suc (length b)" using length_step_fun2 assms by auto
    then have 2: "length b' * 3*(L * (Suc K) * (Suc (length Bs))) = length b * 3*(L * (Suc K) * (Suc (length Bs))) + 3*(L * (Suc K) * (Suc (length Bs)))"
      by (simp add: add.commute add_mult_distrib)
    have "y' \<le> y + 3*(L * (Suc K) * (Suc (length Bs)))" using P1 1 by auto
    also have "... \<le> length b * 3*(L * (Suc K) * (Suc (length Bs))) + 3*(L * (Suc K) * (Suc (length Bs)))" 
      using assms by (auto simp add: add_mult_distrib2)
    also have "... = length b' * 3*(L * (Suc K) * (Suc (length Bs)))" using 2 by auto
    finally have "y' \<le> length b' * 3*(L * (Suc K) * (Suc (length Bs)))".
    then show "?P2 (?c ((a,b), y))" using P1
      by (simp add: ab_semigroup_mult_class.mult_ac(1))
  qed

  then have t: "(?P ((a,b), y) \<Longrightarrow> ?b ((a,b), y) \<Longrightarrow> ?P (?c ((a,b), y)))" for a b y using P1 by auto
  then show "k' \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] assms init by auto
  show "wf_bin1 (set C') (length Bs)"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto
  show "distinct C'"
    using while_option_rule[where P="?P", where b="?b", where c="?c", where s="((B,C),k)", where t="((B',C'), k')"] t assms init by auto
qed

theorem steps_time_NF: "wf_bins1 (map set Bs) \<Longrightarrow> wf_bin1 (set B) (length Bs) \<Longrightarrow> wf_bin1 (set C) (length Bs) \<Longrightarrow> \<exists>C' k'. steps_time Bs (B,C) k = Some (([],C'),k')"
using wf_step_fun_less[of "length Bs"]
proof (induction "(B,C)" arbitrary: B C k rule: wf_induct_rule)
  case less
  show ?case
  proof cases
    assume "B = []"
    thus ?thesis by(simp add: while_option_unfold[of _ _ "(([],C),k)"])
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


lemma T_close2_L_bound: assumes "wf_bins1 (map set Bs)" "wf_bin1 (set B) (length Bs)" "distinct ps" "\<forall>i < length Bs. distinct (Bs ! i)" "distinct B"
  shows "T_close2_L Bs B \<le> 3*(L * L * (Suc K) * (Suc K) * (Suc (length Bs)) * (Suc (length Bs)))"
proof-
  have "\<exists>C' k'. steps_time Bs (B,[]) 0 = Some (([],C'),k')" using assms
    using steps_time_NF wf_bin1_def by auto
  then obtain C' k' where steps: "steps_time Bs (B,[]) 0 = Some (([],C'),k')" by blast
  then have wfC': "wf_bin1 (set C') (length Bs)" and k'le: "k' \<le> (length C') * (3*(L * (Suc K) * (Suc (length Bs))))" and C'_d: "distinct C'"
    using steps_time_time[of Bs B "[]" 0 "[]" C' k'] assms
    by (simp_all add: wf_bin1_def)
  then have "length C' \<le> L * (Suc K) * (Suc (length Bs))" 
    by (metis card_wf_bin1 distinct_card)
  then have "k' \<le> (L * (Suc K) * (Suc (length Bs))) * (3*(L * (Suc K) * (Suc (length Bs))))"
    by (meson k'le le_trans mult_le_mono1) 
  then have "k' \<le> 3*(L * L * (Suc K) * (Suc K) * (Suc (length Bs)) * (Suc (length Bs)))"
    by (metis (no_types, opaque_lifting) mult.commute mult.left_commute)
  then show ?thesis using steps by (simp add: T_close2_L_def)
qed


lemma T_bins_L_bound: "k \<le> length w \<Longrightarrow> distinct ps \<Longrightarrow> T_bins_L k \<le> 3*L * L * (Suc K) * (Suc K) * (Suc k) * (Suc k) * (Suc k) + L"
proof(induction k)
  case 0
  then have "wf_bin1 (set Init_L) 0"
    using Init_L_eq_Init wf_bin1_Init by auto
  then have "T_bins_L 0 \<le> 3*(L * L * (Suc K) * (Suc K)) + L" 
    using "0" T_close2_L_bound[of "[]" "Init_L"] T_Init_L_def distinct_Init 
    by (auto simp add: wf_bins1_def wf_bin1_def L_def)
  then show ?case
    by linarith
next
  case (Suc k)
  then have 0: "T_bins_L k \<le> 3*L * L * (Suc K) * (Suc K) * (Suc k) * (Suc k) * (Suc k) + L" by simp
  have "(Suc k) * (Suc k) * (Suc k) = (k * k * k + 3* k*k + 3*k+1)" by (auto simp add: add_mult_distrib)
  then have 1: "T_bins_L k \<le> 3*L * L * (Suc K) * (Suc K) * (k * k * k + 3* k*k + 3*k+1) + L" using 0
    by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1))

  have P1: "\<forall>i < length (bins_L k). distinct ((bins_L k) ! i)" using distinct_bins_L Suc
    using Suc_leD by blast
  have P2: "wf_bin1 (set (Scan_L (last (bins_L k)) k)) (length (bins_L k))"
    by (metis Scan_L_eq_Scan Suc.prems(1) Zero_not_Suc bins_L_eq_bins le_Suc_eq length_bins_L list.size(3) nat_less_le not_less_eq_eq set_last wf_bin1_Scan
        wf_bin1_last)
  have P3: "distinct (Scan_L (last (bins_L k)) k)"
    by (metis P1 all_nth_imp_all_set bot_nat_0.extremum_strict distinct_Scan_L last_in_set length_bins_L lessI list.size(3))
  have 2: "T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) \<le> 3*(L * L * (Suc K) * (Suc K) * (Suc (Suc k)) * (Suc (Suc k)))"
    using T_close2_L_bound[of "(bins_L k)" "(Scan_L (last (bins_L k)) k)"] P1 P2 P3
    using Suc.prems(1,2) bins_L_eq_bins length_bins_L wf_bins1_bins by fastforce
  have "(Suc (Suc k)) * (Suc (Suc k)) = (k*k + 4 *k + 4)" by (auto simp add: add_mult_distrib)
  then have 3: "T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) \<le> 3*L * L * (Suc K) * (Suc K) * (k*k + 4 *k + 4)" using 2
    by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1))

  have Q1: "wf_bin1 (set (last (bins_L k))) k"
    by (metis Suc.prems(1) Suc_leD Zero_not_Suc bins_L_eq_bins length_bins_L list.size(3) set_last wf_bin1_last)
  have "distinct (last (bins_L k))"
    by (metis P1 all_nth_imp_all_set bot_nat_0.extremum_strict last_in_set length_bins_L list.size(3) not_less_eq)
  then have "length (last (bins_L k)) \<le> L * (Suc K) * (Suc k)" using Q1
    by (metis card_wf_bin1 distinct_card)
  then have 4: "length (last (bins_L k)) \<le> 3* L *L * (Suc K) * (Suc K) * (Suc k)" 
  proof - (*TODO make easier*)
    have "\<forall>n na. (n::nat) \<le> na \<or> \<not> n * n \<le> na"
      using dual_order.trans le_square by blast
    then have "L \<le> 3 * L * L * Suc K" 
      by (metis (no_types) Suc_mult_le_cancel1 mult_le_mono mult_le_mono1 mult_numeral_1 mult_numeral_1_right numeral_le_iff semiring_norm(68))
    then show ?thesis
      by (meson \<open>length (last (bins_L k)) \<le> L * Suc K * Suc k\<close> dual_order.trans mult_le_mono1)
  qed

  have "T_bins_L k + (T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) + length (last (bins_L k))) 
        \<le> 3*L * L * (Suc K) * (Suc K) * (k*k*k + 4*k*k + 8*k+6) + L" 
    using 1 3 4 Rings.semiring_class.distrib_left[of "3*L * L * (Suc K) * (Suc K)"] by auto
  also have "... \<le> 3*L * L * (Suc K) * (Suc K) * (k * k * k + 6* k*k + 12*k+8) + L" by auto
  finally have 5: "T_bins_L k + (T_close2_L (bins_L k) (Scan_L (last (bins_L k)) k) + length (last (bins_L k))) 
        \<le> 3*L * L * (Suc K) * (Suc K) * (k * k * k + 6* k*k + 12*k+8) + L".

  have "(Suc (Suc k)) * (Suc (Suc k)) * (Suc (Suc k)) = (k * k * k + 6* k*k + 12*k+8)" by (auto simp add: add_mult_distrib)
  then have "3*L * L * (Suc K) * (Suc K) * (Suc (Suc k) * (Suc (Suc k)) * (Suc (Suc k))) 
    = 3*L * L * (Suc K) * (Suc K) * (k * k * k + 6* k*k + 12*k+8)"
    by (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1))
  then show ?case using 5
    by (smt (z3) T_Scan_L.simps T_bins_L.simps(2) mult.commute mult.left_commute)
qed

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
end

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