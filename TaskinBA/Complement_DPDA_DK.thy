theory Complement_DPDA_DK
  imports DPDA_DK
begin

datatype 'q st_primed = N 'q | P 'q

instance st_primed :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = N q} \<union> {t. \<exists>q. t = P q}"
    by auto (metis st_primed.exhaust)
  show "finite (UNIV :: 'a st_primed set)"
    by (simp add: * full_SetCompr_eq)
qed

context dpda begin

definition end_check_final_states :: "'q st_primed set" where
  "end_check_final_states \<equiv> P ` final_states M"

fun end_check_trans_fun :: "'q st_primed \<Rightarrow> 'a input_with_marker \<Rightarrow> 's \<Rightarrow> ('q st_primed \<times> 's list) set" where
  "end_check_trans_fun (N q) (Input a) Z = (\<lambda>(p, \<alpha>). (N p, \<alpha>)) ` (trans_fun M q (Input a) Z)"
| "end_check_trans_fun (P q) a Z = (\<lambda>(p, \<alpha>). (P p, \<alpha>)) ` (trans_fun M q a Z)"
| "end_check_trans_fun (N q) End_marker Z = (\<lambda>(p, \<alpha>). (P p, \<alpha>)) ` (trans_fun M q End_marker Z)"

fun end_check_eps_fun :: "'q st_primed \<Rightarrow> 's \<Rightarrow> ('q st_primed \<times> 's list) set" where
  "end_check_eps_fun (N q) Z = (\<lambda>(p, \<alpha>). (N p, \<alpha>)) ` (eps_fun M q Z)"
| "end_check_eps_fun (P q) Z = (\<lambda>(p, \<alpha>). (P p, \<alpha>)) ` (eps_fun M q Z)"

definition end_check_dpda :: "('q st_primed, 'a input_with_marker, 's) pda" where
  "end_check_dpda \<equiv> \<lparr> init_state = N (init_state M), init_symbol = init_symbol M, 
                      final_states = end_check_final_states, trans_fun = end_check_trans_fun, eps_fun = end_check_eps_fun \<rparr>"

lemma end_check_card_trans_N: "card (end_check_trans_fun (N q) a Z) = card (trans_fun M q a Z)"
  apply (induction "N q" a Z rule: end_check_trans_fun.induct)
   apply (rule sym, rule bij_betw_same_card[where ?f = "\<lambda>(p, \<alpha>). (N p, \<alpha>)"])
   defer
   apply (rule sym, rule bij_betw_same_card[where ?f = "\<lambda>(p, \<alpha>). (P p, \<alpha>)"])
   apply (auto simp: bij_betw_def inj_on_def)
  done

lemma end_check_card_trans_P: "card (end_check_trans_fun (P q) a Z) = card (trans_fun M q a Z)"
  apply (rule sym, rule bij_betw_same_card[where ?f = "\<lambda>(p, \<alpha>). (P p, \<alpha>)"])
    apply (auto simp: bij_betw_def inj_on_def)
  done

lemma end_check_card_eps_N: "card (end_check_eps_fun (N q) Z) = card (eps_fun M q Z)"
  apply (rule sym, rule bij_betw_same_card[where ?f = "\<lambda>(p, \<alpha>). (N p, \<alpha>)"])
    apply (auto simp: bij_betw_def inj_on_def)
  done

lemma end_check_card_eps_P: "card (end_check_eps_fun (P q) Z) = card (eps_fun M q Z)"
  apply (rule sym, rule bij_betw_same_card[where ?f = "\<lambda>(p, \<alpha>). (P p, \<alpha>)"])
    apply (auto simp: bij_betw_def inj_on_def)
  done

lemma dpda_end_check: "dpda end_check_dpda"
proof (standard, goal_cases)
  case (1 p x z)
  have "finite (end_check_trans_fun p x z)"
    by (induction p x z rule: end_check_trans_fun.induct) (auto simp: finite_trans)
  then show ?case
    by (simp add: end_check_dpda_def)
next
  case (2 p z)
  have "finite (end_check_eps_fun p z)"
    by (induction p z rule: end_check_eps_fun.induct) (auto simp: finite_eps)
  then show ?case
    by (simp add: end_check_dpda_def)
next
  case (3 q a Z)
  then show ?case 
    using det end_check_card_trans_N end_check_card_eps_N end_check_card_trans_P end_check_card_eps_P
    by (cases q) (auto simp: end_check_dpda_def)
next
  case (4 q \<alpha> p a)
  hence "(q, \<alpha>) \<in> end_check_trans_fun p a (init_symbol M)"
    by (simp add: end_check_dpda_def)
  hence "\<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
    by (induction p a "init_symbol M" rule: end_check_trans_fun.induct) (auto simp: init_trans)
  thus ?case
    by (simp add: end_check_dpda_def)
next
  case (5 q \<alpha> p)
  hence "(q, \<alpha>) \<in> end_check_eps_fun p (init_symbol M)"
    by (simp add: end_check_dpda_def)
  hence "\<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
    by (induction p "init_symbol M" rule: end_check_eps_fun.induct) (auto simp: init_eps)
  thus ?case
    by (simp add: end_check_dpda_def)
qed

declare dpda.det_step\<^sub>1.simps[OF dpda_end_check, simp]
declare dpda.det_stepn.simps[OF dpda_end_check, simp]

lemma pda_end_check: "pda end_check_dpda"
  using dpda_def dpda_end_check by auto

lemma end_check_dpda_input_det_step\<^sub>1:
  "dpda.det_step\<^sub>1 M (p\<^sub>1, map Input w\<^sub>1, \<alpha>\<^sub>1) = Some (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    dpda.det_step\<^sub>1 end_check_dpda (N p\<^sub>1, map Input w\<^sub>1, \<alpha>\<^sub>1) = Some (N p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
by (use det_step\<^sub>1_rule_ext end_check_dpda_def dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] in auto)

lemma end_check_dpda_marker_det_step\<^sub>1:
  "dpda.det_step\<^sub>1 M (p\<^sub>1, End_marker#w, \<alpha>\<^sub>1) = Some (p\<^sub>2, w, \<alpha>\<^sub>2) \<longleftrightarrow>
    dpda.det_step\<^sub>1 end_check_dpda (N p\<^sub>1, End_marker#w, \<alpha>\<^sub>1) = Some (P p\<^sub>2, w, \<alpha>\<^sub>2)"
by (use det_step\<^sub>1_rule_ext end_check_dpda_def dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] in auto)

lemma end_check_dpda_P_det_step\<^sub>1:
  "dpda.det_step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) = Some (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    dpda.det_step\<^sub>1 end_check_dpda (P p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) = Some (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
by (use det_step\<^sub>1_rule_ext end_check_dpda_def dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] in auto)

lemma end_check_dpda_input_in_N:
  assumes "dpda.det_step\<^sub>1 end_check_dpda (N p, map Input w\<^sub>1, \<alpha>\<^sub>1) = Some (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = N q'"
by (use assms end_check_dpda_def dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] in auto)

lemma end_check_dpda_marker_in_N:
  assumes "dpda.det_step\<^sub>1 end_check_dpda (N p, End_marker#w, \<alpha>\<^sub>1) = Some (q, w, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
by (use assms end_check_dpda_def dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] in auto)

lemma end_check_dpda_inputs_in_N:
  assumes "dpda.det_stepn end_check_dpda n (N p, map Input w\<^sub>1, \<alpha>\<^sub>1) = Some (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = N q'"
using assms proof (induction n "(N p, map Input w\<^sub>1, \<alpha>\<^sub>1)" arbitrary: p w\<^sub>1 \<alpha>\<^sub>1 rule: dpda.det_stepn.induct[OF dpda_end_check])
  case (2 n \<alpha>)
  from 2(2) obtain p' w' \<alpha>' where fs: "dpda.det_step\<^sub>1 end_check_dpda (N p, map Input w\<^sub>1, \<alpha>) = Some (p', w', \<alpha>')"
                              and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (q, w\<^sub>2, \<alpha>\<^sub>2)"
    by (auto split: option.splits)
  from fs obtain p'' where p'_def[simp]: "p' = N p''"
    using end_check_dpda_input_in_N by blast
  from fs obtain w'' where w'_def[simp]: "w' = map Input w''"
    using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by blast
  from 2(1)[OF fs _ _ lss[unfolded p'_def w'_def]] show ?case by simp
qed auto

lemma end_check_dpda_input_in_N_det_stepn:
  "dpda.det_stepn M n (p\<^sub>1, map Input w, \<alpha>\<^sub>1) = Some (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
    dpda.det_stepn end_check_dpda n (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) = Some (N p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" proof (induction n "(p\<^sub>1, map Input w, \<alpha>\<^sub>1)" arbitrary: p\<^sub>1 w \<alpha>\<^sub>1 rule: det_stepn.induct)
    case (2 n p \<alpha>)
    from 2(2) obtain p' w' \<alpha>' where fs: "det_step\<^sub>1 (p, map Input w, \<alpha>) = Some (p', w', \<alpha>')" 
                                and lss: "det_stepn n (p', w', \<alpha>') = Some (p\<^sub>2, [], \<alpha>\<^sub>2)"
      by (auto split: option.splits)
    from fs obtain w'' where w'_def[simp]: "w' = map Input w''"
      using det_step\<^sub>1_rule_ext by blast

    from 2(1)[OF fs _ _ lss[unfolded w'_def]] 
      have "dpda.det_stepn end_check_dpda n (N p', map Input w'', \<alpha>') = Some (N p\<^sub>2, [], \<alpha>\<^sub>2)" by simp

    moreover from fs have "dpda.det_step\<^sub>1 end_check_dpda (N p, map Input w, \<alpha>) = Some (N p', w', \<alpha>')"
      using end_check_dpda_input_det_step\<^sub>1 by blast

    ultimately show ?case by simp
  qed simp
next
  show "?r \<Longrightarrow> ?l" proof (induction n "(N p\<^sub>1, map Input w, \<alpha>\<^sub>1)" arbitrary: p\<^sub>1 w \<alpha>\<^sub>1 rule: dpda.det_stepn.induct[OF dpda_end_check])
    case (2 n \<alpha>)
    from 2(2) obtain p' w' \<alpha>' where fs: "dpda.det_step\<^sub>1 end_check_dpda (N p\<^sub>1, map Input w, \<alpha>) = Some (p', w', \<alpha>')" 
                                and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (N p\<^sub>2, [], \<alpha>\<^sub>2)"
      by (auto split: option.splits)
    from fs obtain p'' where p'_def[simp]: "p' = N p''"
      using end_check_dpda_input_in_N by blast
    from fs obtain w'' where w'_def[simp]: "w' = map Input w''"
      using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by blast

    from 2(1)[OF fs _ _ lss[unfolded p'_def w'_def]]
    have "det_stepn n (p'', map Input w'', \<alpha>') = Some (p\<^sub>2, [], \<alpha>\<^sub>2)" by simp

    moreover from fs have "det_step\<^sub>1 (p\<^sub>1, map Input w, \<alpha>) = Some (p'', w', \<alpha>')"
      using end_check_dpda_input_det_step\<^sub>1 by simp

    ultimately show ?case by simp
  qed simp
qed

lemma end_check_dpda_in_P:
  assumes "dpda.det_step\<^sub>1 end_check_dpda (P p, w\<^sub>1, \<alpha>\<^sub>1) = Some (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
by (use assms end_check_dpda_def dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] in auto)

lemma end_check_dpda_ins_P:
  assumes "dpda.det_stepn end_check_dpda n (P p, w\<^sub>1, \<alpha>\<^sub>1) = Some (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
using assms proof (induction n "(P p, w\<^sub>1, \<alpha>\<^sub>1)" arbitrary: p w\<^sub>1 \<alpha>\<^sub>1 rule: dpda.det_stepn.induct[OF dpda_end_check])
  case (2 n w \<alpha>)
  from 2(2) obtain p' w' \<alpha>' where fs: "dpda.det_step\<^sub>1 end_check_dpda (P p, w, \<alpha>) = Some (p', w', \<alpha>')"
                              and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (q, w\<^sub>2, \<alpha>\<^sub>2)"
    by (auto split: option.splits)
  from fs obtain p'' where p'_def[simp]: "p' = P p''"
    using end_check_dpda_in_P by blast
  from 2(1)[OF fs _ _ lss[unfolded p'_def]] show ?case by simp
qed auto

lemma end_check_dpda_in_P_det_stepn:
  "dpda.det_stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) = Some (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    dpda.det_stepn end_check_dpda n (P p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) = Some (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" proof (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: det_stepn.induct)
    case (2 n p w \<alpha>)
    from 2(2) obtain p' w' \<alpha>' where fs: "det_step\<^sub>1 (p, w, \<alpha>) = Some (p', w', \<alpha>')"
                                and lss: "det_stepn n (p', w', \<alpha>') = Some (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      by (auto split: option.splits)

    from 2(1)[OF fs _ _ lss] 
    have "dpda.det_stepn end_check_dpda n (P p', w', \<alpha>') = Some (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by simp

    moreover from fs have "dpda.det_step\<^sub>1 end_check_dpda (P p, w, \<alpha>) = Some (P p', w', \<alpha>')"
      using end_check_dpda_P_det_step\<^sub>1 by blast

    ultimately show ?case by simp
  qed simp
next
  show "?r \<Longrightarrow> ?l" proof (induction n "(P p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: dpda.det_stepn.induct[OF dpda_end_check])
    case (2 n w \<alpha>)
    from 2(2) obtain p' w' \<alpha>' where fs: "dpda.det_step\<^sub>1 end_check_dpda (P p\<^sub>1, w, \<alpha>) = Some (p', w', \<alpha>')"
                                and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      by (auto split: option.splits)
    from fs obtain p'' where p'_def[simp]: "p' = P p''"
      using end_check_dpda_in_P by blast

    from 2(1)[OF fs _ _ lss[unfolded p'_def]]
    have "det_stepn n (p'', w', \<alpha>') = Some (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by simp

    moreover from fs have "det_step\<^sub>1 (p\<^sub>1, w, \<alpha>) = Some (p'', w', \<alpha>')"
      using end_check_dpda_P_det_step\<^sub>1 by simp

    ultimately show ?case by simp
  qed simp
qed

(* TODO: How to generalize these kind of lemmas to all lemmas in the locale? *)
lemmas det_stepn_reads_input = 
  stepn_reads_input[simplified stepn_det_stepn_some step\<^sub>1_det_step\<^sub>1_some]
  pda.stepn_reads_input[OF pda_end_check, simplified dpda.stepn_det_stepn_some[OF dpda_end_check] dpda.step\<^sub>1_det_step\<^sub>1_some[OF dpda_end_check]]

lemmas det_stepn_word_app =
  stepn_word_app[simplified stepn_det_stepn_some step\<^sub>1_det_step\<^sub>1_some]
  pda.stepn_word_app[OF pda_end_check, simplified dpda.stepn_det_stepn_some[OF dpda_end_check] dpda.step\<^sub>1_det_step\<^sub>1_some[OF dpda_end_check]]

lemmas det_stepn_split_last =
  stepn_split_last[simplified stepn_det_stepn_some step\<^sub>1_det_step\<^sub>1_some]
  pda.stepn_split_last[OF pda_end_check, simplified dpda.stepn_det_stepn_some[OF dpda_end_check] dpda.step\<^sub>1_det_step\<^sub>1_some[OF dpda_end_check]]

lemmas det_stepn_trans =
  stepn_trans[simplified stepn_det_stepn_some step\<^sub>1_det_step\<^sub>1_some]
  pda.stepn_trans[OF pda_end_check, simplified dpda.stepn_det_stepn_some[OF dpda_end_check] dpda.step\<^sub>1_det_step\<^sub>1_some[OF dpda_end_check]]

lemmas det_split_word =
  split_word[simplified stepn_det_stepn_some]
  pda.split_word[OF pda_end_check, simplified dpda.stepn_det_stepn_some[OF dpda_end_check]]

lemma end_check_dpda_marker_det_stepn:
  "dpda.det_stepn M n (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) = Some (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
    dpda.det_stepn end_check_dpda n (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where n_def: "n = Suc n'" and k_less: "k \<le> n'" and stepk: "det_stepn k (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) = Some (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    and step1: "det_step\<^sub>1 (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)" and stepn'k: "det_stepn (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using det_stepn_reads_input(1) by blast
  from stepk have "det_stepn k (p\<^sub>1, [], \<alpha>\<^sub>1) = Some (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using det_stepn_word_app(1)[of k p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1 "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  hence "dpda.det_stepn end_check_dpda k (N p\<^sub>1, [], \<alpha>\<^sub>1) = Some (N q\<^sub>1, [], \<gamma>\<^sub>1)"
    using end_check_dpda_input_in_N_det_stepn[where ?w = "[]"] by simp

  hence "dpda.det_stepn end_check_dpda k (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) = Some (N q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    using det_stepn_word_app(2)[of k "N p\<^sub>1" "[]" \<alpha>\<^sub>1 "N q\<^sub>1" "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp

  moreover from step1 have "dpda.det_step\<^sub>1 end_check_dpda (N q\<^sub>1, [End_marker], \<gamma>\<^sub>1) = Some (P q\<^sub>2, [], \<gamma>\<^sub>2)"
    using end_check_dpda_marker_det_step\<^sub>1 by simp

  ultimately have *: "dpda.det_stepn end_check_dpda (Suc k) (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) = Some (P q\<^sub>2, [], \<gamma>\<^sub>2)"
    using det_stepn_split_last(2) by blast

  from stepn'k have **: "dpda.det_stepn end_check_dpda (n' - k) (P q\<^sub>2, [], \<gamma>\<^sub>2) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)" 
    using end_check_dpda_in_P_det_stepn by simp

  from n_def k_less show ?r 
    using det_stepn_trans(2)[OF * **] by simp
next
  assume ?r
  then obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where n_def: "n = Suc n'" and k_less: "k \<le> n'" and 
          stepk: "dpda.det_stepn end_check_dpda k (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) = Some (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)" and
          step1: "dpda.det_step\<^sub>1 end_check_dpda (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)" and
          stepn'k: "dpda.det_stepn end_check_dpda (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using det_stepn_reads_input(2) by blast
  from stepk have stepk_emp: "dpda.det_stepn end_check_dpda k (N p\<^sub>1, [], \<alpha>\<^sub>1) = Some (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using det_stepn_word_app(2) by fastforce
  then obtain q\<^sub>1' where q1_def: "q\<^sub>1 = N q\<^sub>1'"
    using end_check_dpda_inputs_in_N[of k p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1 "[]" \<gamma>\<^sub>1] by auto
  with stepk_emp have "det_stepn k (p\<^sub>1, [], \<alpha>\<^sub>1) = Some (q\<^sub>1', [], \<gamma>\<^sub>1)"
    using end_check_dpda_input_in_N_det_stepn[where ?w = "[]"] by simp

  hence *: "det_stepn k (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) = Some (q\<^sub>1', [End_marker], \<gamma>\<^sub>1)"
    using det_stepn_word_app(1)[of k p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1' "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  from step1 q1_def obtain q\<^sub>2' where q2_def: "q\<^sub>2 = P q\<^sub>2'"
    using end_check_dpda_marker_in_N by blast

  with stepn'k have "det_stepn (n' - k) (q\<^sub>2', [], \<gamma>\<^sub>2) = Some (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_in_P_det_stepn by simp

  moreover from q1_def q2_def step1 have "det_step\<^sub>1 (q\<^sub>1', [End_marker], \<gamma>\<^sub>1) = Some (q\<^sub>2', [], \<gamma>\<^sub>2)"
    using end_check_dpda_marker_det_step\<^sub>1 by simp

  ultimately have **: "det_stepn (Suc (n' - k)) (q\<^sub>1', [End_marker], \<gamma>\<^sub>1) = Some (p\<^sub>2, [], \<alpha>\<^sub>2)" by simp

  from n_def k_less show ?l 
    using det_stepn_trans(1)[OF * **] by simp
qed

lemma end_check_dpda_det_stepn:
  "dpda.det_stepn M n (p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) = Some (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
     dpda.det_stepn end_check_dpda n (N p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain k q \<gamma> where k_less: "k \<le> n" and stepk: "dpda.det_stepn M k (p\<^sub>1, map Input w, \<alpha>\<^sub>1) = Some (q, [], \<gamma>)" 
                            and stepnk: "dpda.det_stepn M (n - k) (q, [End_marker], \<gamma>) = Some (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using det_split_word(1) by blast
  from stepk have "dpda.det_stepn end_check_dpda k (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) = Some (N q, [], \<gamma>)"
    using end_check_dpda_input_in_N_det_stepn by simp

  hence "dpda.det_stepn end_check_dpda k (N p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) = Some (N q, [End_marker], \<gamma>)"
    using det_stepn_word_app(2)[of k "N p\<^sub>1" "map Input w" "\<alpha>\<^sub>1" "N q" "[]" \<gamma> "[End_marker]"] by simp 

  moreover from stepnk have "dpda.det_stepn end_check_dpda (n - k) (N q, [End_marker], \<gamma>) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_marker_det_stepn by simp

  ultimately show ?r
    using k_less det_stepn_trans(2) by fastforce 
next
  assume ?r
  then obtain k q \<gamma> where k_less: "k \<le> n" and stepk: "dpda.det_stepn end_check_dpda k (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) = Some (q, [], \<gamma>)"
                      and stepnk: "dpda.det_stepn end_check_dpda (n - k) (q, [End_marker], \<gamma>) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using det_split_word(2) by blast
  from stepk obtain q' where q_def: "q = N q'" 
    using end_check_dpda_inputs_in_N by blast
  with stepk have "dpda.det_stepn M k (p\<^sub>1, map Input w, \<alpha>\<^sub>1) = Some (q', [], \<gamma>)"
    using end_check_dpda_input_in_N_det_stepn by simp

  hence "dpda.det_stepn M k (p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) = Some (q', [End_marker], \<gamma>)"
    using det_stepn_word_app(1)[of k p\<^sub>1 "map Input w" \<alpha>\<^sub>1 q' "[]" \<gamma> "[End_marker]"] by simp

  moreover from q_def stepnk have "dpda.det_stepn M (n-k) (q', [End_marker], \<gamma>) = Some (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_marker_det_stepn by simp

  ultimately show ?l
    using k_less det_stepn_trans(1) by fastforce
qed 

lemma accepted_end_check:
"(\<exists>q. q \<in> final_states M \<and> dpda.det_stepn M n (init_state M, word_with_end w, [init_symbol M]) = Some (q, [], \<gamma>)) \<longleftrightarrow>
  (\<exists>q. q \<in> final_states end_check_dpda \<and> dpda.det_stepn end_check_dpda n (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q, [], \<gamma>))"
(is "?l \<longleftrightarrow> ?r") proof
  assume ?l
  then obtain q where q_final: "q \<in> final_states M" and detstepn: "det_stepn n (init_state M, word_with_end w, [init_symbol M]) = Some (q, [], \<gamma>)" by blast
  from q_final have *: "P q \<in> final_states end_check_dpda"
    by (simp add: end_check_dpda_def end_check_final_states_def)
  from detstepn have "dpda.det_stepn end_check_dpda n (N (init_state M), word_with_end w, [init_symbol M]) = Some (P q, [], \<gamma>)"
    using end_check_dpda_det_stepn[where ?w = w and ?\<alpha>\<^sub>1 = "[init_symbol M]" and ?\<alpha>\<^sub>2 = \<gamma>] by simp
  hence **: "dpda.det_stepn end_check_dpda n (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (P q, [], \<gamma>)"
    by (simp add: end_check_dpda_def)
  from * ** show ?r by blast
next
  assume ?r
  then obtain q where q_final: "q \<in> final_states end_check_dpda" and detstepn: "dpda.det_stepn end_check_dpda n
         (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q, [], \<gamma>)" by blast
  from q_final[unfolded end_check_dpda_def end_check_final_states_def] obtain q' 
                                       where q_def: "q = P q'" and *: "q' \<in> final_states M" by auto
  from q_def detstepn have "dpda.det_stepn end_check_dpda n
                      (N (init_state M), word_with_end w, [init_symbol M]) = Some (P q', [], \<gamma>)" 
    by (simp add: end_check_dpda_def)
  hence **: "dpda.det_stepn M n (init_state M, word_with_end w, [init_symbol M]) = Some (q', [], \<gamma>)"
    using end_check_dpda_det_stepn[where ?w = w and ?\<alpha>\<^sub>1 = "[init_symbol M]" and ?\<alpha>\<^sub>2 = \<gamma>] by simp
  from * ** show ?l by blast 
qed

lemma lang_end_check_dpda:
  "dpda.det_final_accept end_check_dpda = dpda.det_final_accept M"
unfolding det_final_accept_def dpda.det_final_accept_def[OF dpda_end_check] using accepted_end_check by fast

lemma end_check_dpda_in_N_input:
  assumes "dpda.det_step\<^sub>1 end_check_dpda (N p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) = Some (N p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "w\<^sub>1 = w\<^sub>2 \<or> (\<exists>a. w\<^sub>1 = Input a # w\<^sub>2)" 
proof -
  from assms have rule: "w\<^sub>1 = w\<^sub>2 \<or> (\<exists>Z a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> (N p\<^sub>2, \<beta>) \<in> end_check_trans_fun (N p\<^sub>1) a Z)" (is "_ \<or> ?r")
    using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by (auto simp: end_check_dpda_def)
  show ?thesis proof (rule disjE[OF rule])
    assume ?r
    then obtain Z a \<beta> where w1_def: "w\<^sub>1 = a # w\<^sub>2" and trans: "(N p\<^sub>2, \<beta>) \<in> end_check_trans_fun (N p\<^sub>1) a Z" by blast
    from trans have "\<exists>a'. a = Input a'"
      by (induction "N p\<^sub>1" a Z rule: end_check_trans_fun.induct) auto
    with w1_def show ?thesis by blast
  qed simp
qed

lemma end_check_dpda_froms_N:
  assumes "dpda.det_stepn end_check_dpda n (p, w\<^sub>1, \<alpha>\<^sub>1) = Some (N q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>p'. p = N p'" 
proof (rule ccontr)
  assume "\<not>?thesis"
  then obtain p' where "p = P p'"
    using st_primed.exhaust[of p] by auto
  with assms have "\<exists>q'. N q = P q'"
    using end_check_dpda_ins_P by blast
  thus False by simp
qed

lemma end_check_dpda_in_N_inputs:
  assumes "dpda.det_stepn end_check_dpda n (N p\<^sub>1, w, \<alpha>\<^sub>1) = Some (N p\<^sub>2, [], \<alpha>\<^sub>2)"
  shows "\<exists>w'. w = map Input w'"
using assms proof (induction n "(N p\<^sub>1, w, \<alpha>\<^sub>1)"  arbitrary: p\<^sub>1 w \<alpha>\<^sub>1 rule: dpda.det_stepn.induct[OF dpda_end_check])
  case (2 n w \<alpha>)
  from 2(2) obtain p' w' \<alpha>' where fs: "dpda.det_step\<^sub>1 end_check_dpda (N p\<^sub>1, w, \<alpha>) = Some (p', w', \<alpha>')"
                              and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (N p\<^sub>2, [], \<alpha>\<^sub>2)"
    by (auto split: option.splits)
  from lss obtain p'' where p'_def[simp]: "p' = N p''"
    using end_check_dpda_froms_N by blast

  from 2(1)[OF fs _ _ lss[unfolded p'_def]] have "\<exists>w''. w' = map Input w''" by simp

  moreover from fs have "w = w' \<or> (\<exists>a. w = Input a # w')"
    using end_check_dpda_in_N_input by simp

  ultimately show ?case 
     using map_eq_Cons_conv[where ?f = Input] by metis
qed simp

lemmas det_decreasing_word =
  pda.decreasing_word[OF pda_end_check, simplified dpda.steps_det_stepn_some[OF dpda_end_check]]

lemma end_check_dpda_unread_marker:
  assumes "dpda.det_stepn end_check_dpda n (N p\<^sub>1, word_with_end w\<^sub>1, \<alpha>\<^sub>1) = Some (N p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>w\<^sub>2'. w\<^sub>2 = word_with_end w\<^sub>2'"
proof -
  from assms obtain w where w1_def: "word_with_end w\<^sub>1 = w @ w\<^sub>2"
    using det_decreasing_word by blast
  with assms have "dpda.det_stepn end_check_dpda n (N p\<^sub>1, w, \<alpha>\<^sub>1) = Some (N p\<^sub>2, [], \<alpha>\<^sub>2)"
    using det_stepn_word_app(2) by fastforce
  hence "\<exists>w'. w = map Input w'"
    using end_check_dpda_in_N_inputs by simp
  with w1_def show ?thesis
    by (metis (no_types, opaque_lifting) Cons_eq_map_conv append_eq_map_conv butlast_append input_with_marker.simps(3)
        last_appendR snoc_eq_iff_butlast)
qed

lemma end_check_dpda_N_to_P_marker:
  assumes "dpda.det_stepn end_check_dpda n (N p\<^sub>1, w, \<alpha>\<^sub>1) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)"
  shows "\<exists>w' w''. w = map Input w' @ End_marker # w''"
using assms proof (induction n "(N p\<^sub>1, w, \<alpha>\<^sub>1)" arbitrary: p\<^sub>1 w \<alpha>\<^sub>1 rule: dpda.det_stepn.induct[OF dpda_end_check])
  case (2 n w \<alpha>)
  from 2(2) obtain p' w' \<alpha>' where fs: "dpda.det_step\<^sub>1 end_check_dpda (N p\<^sub>1, w, \<alpha>) = Some (p', w', \<alpha>')"
                              and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    by (auto split: option.splits)
  from fs obtain Z where 
    rule: "(\<exists>\<beta>. w' = w \<and> (p', \<beta>) \<in> end_check_eps_fun (N p\<^sub>1) Z) \<or>
      (\<exists>a \<beta>. w = a # w' \<and> (p', \<beta>) \<in> end_check_trans_fun (N p\<^sub>1) a Z)" (is "?l \<or> ?r")
    using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by (fastforce simp: end_check_dpda_def)
  show ?case proof (rule disjE[OF rule])
    assume ?l
    then obtain \<beta> where w'_def: "w' = w" and eps: "(p', \<beta>) \<in> end_check_eps_fun (N p\<^sub>1) Z" by blast
    from eps obtain p'' where p'_def[simp]: "p' = N p''" by auto
    with 2(1)[OF fs _ _ lss[unfolded p'_def]] have "\<exists>w'' w'''. w' = map Input w'' @ End_marker # w'''" by simp
    with w'_def show ?case by simp
  next
    assume ?r
    then obtain a \<beta> where w1_def: "w = a # w'" and trans: "(p', \<beta>) \<in> end_check_trans_fun (N p\<^sub>1) a Z" by blast
    show ?case proof (cases a)
      case (Input a')
      with trans obtain p'' where p'_def[simp]: "p' = N p''" by auto
      with 2(1)[OF fs _ _ lss[unfolded p'_def]] obtain w'' w''' where "w' = map Input w'' @ End_marker # w'''" by blast
      with w1_def Input have "w = Input a' # map Input w'' @ End_marker # w'''" by simp
      hence "w = map Input (a' # w'') @ End_marker # w'''" by simp
      thus ?thesis by blast
    next
      case End_marker
      with w1_def show ?thesis by auto
    qed
  qed
qed simp

lemma end_check_dpda_read_marker:
  assumes "dpda.det_stepn end_check_dpda n (N p\<^sub>1, word_with_end w\<^sub>1, \<alpha>\<^sub>1) = Some (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "w\<^sub>2 = []"
proof - 
  from assms obtain w where w1_def: "word_with_end w\<^sub>1 = w @ w\<^sub>2"
    using det_decreasing_word by blast
  with assms have "dpda.det_stepn end_check_dpda n (N p\<^sub>1, w, \<alpha>\<^sub>1) = Some (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using det_stepn_word_app(2) by fastforce
  hence "\<exists>w' w''. w = map Input w' @ End_marker # w''"
    using end_check_dpda_N_to_P_marker by simp
  with w1_def show ?thesis
    by (metis Cons_eq_map_conv append.right_neutral butlast.simps(2) butlast_append
        input_with_marker.simps(3) map_eq_append_conv)
qed

abbreviation end_check_trans_fun' :: "'q st_primed \<Rightarrow> 'a input_with_marker \<Rightarrow> 's \<Rightarrow> ('q st_primed \<times> 's list) set" where
  "end_check_trans_fun' q a Z \<equiv> (if q \<in> final_states end_check_dpda then {} else trans_fun end_check_dpda q a Z)"

abbreviation end_check_eps_fun' :: "'q st_primed \<Rightarrow> 's \<Rightarrow> ('q st_primed \<times> 's list) set" where
  "end_check_eps_fun' q Z \<equiv> (if q \<in> final_states end_check_dpda then {(q, [Z])} else eps_fun end_check_dpda q Z)"

definition end_check_dpda' :: "('q st_primed, 'a input_with_marker, 's) pda" where
  "end_check_dpda' \<equiv> \<lparr> init_state = init_state end_check_dpda, init_symbol = init_symbol end_check_dpda, 
                      final_states = final_states end_check_dpda, trans_fun = end_check_trans_fun', eps_fun = end_check_eps_fun' \<rparr>"

lemma dpda_end_check': "dpda end_check_dpda'"
proof (standard, goal_cases)
  case (1 p a Z)
  show ?case
    using pda.finite_trans[OF pda_end_check] by (simp add: end_check_dpda'_def)
next
  case (2 p Z)
  show ?case
    using pda.finite_eps[OF pda_end_check] by (simp add: end_check_dpda'_def)
next
  case (3 q a Z)
  show ?case
    by (cases "q \<in> final_states end_check_dpda") (auto simp: end_check_dpda'_def dpda.det[OF dpda_end_check])
next
  case (4 q \<alpha> p a)
  thus ?case
    by (cases "p \<in> final_states end_check_dpda") (auto simp: end_check_dpda'_def dpda.init_trans[OF dpda_end_check])
next
  case (5 q \<alpha> p)
  thus ?case
    by (cases "p \<in> final_states end_check_dpda") (auto simp: end_check_dpda'_def dpda.init_eps[OF dpda_end_check])
qed

declare dpda.det_step\<^sub>1.simps[OF dpda_end_check', simp]
declare dpda.det_stepn.simps[OF dpda_end_check', simp]

lemma pda_end_check': "pda end_check_dpda'"
  using dpda_def dpda_end_check' by auto

lemma end_check_dpda'_in_N_det_step\<^sub>1:
  "dpda.det_step\<^sub>1 end_check_dpda (N p, w\<^sub>1, \<alpha>) = Some (q, w\<^sub>2, \<gamma>) \<longleftrightarrow>
    dpda.det_step\<^sub>1 end_check_dpda' (N p, w\<^sub>1, \<alpha>) = Some (q, w\<^sub>2, \<gamma>)"
using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check'] end_check_dpda_def end_check_dpda'_def end_check_final_states_def by (fastforce split: if_splits)

lemma end_check_dpda'_input_in_N_det_stepn:
  "dpda.det_stepn end_check_dpda n (N p, map Input w, \<alpha>) = Some (q, [], \<gamma>) \<longleftrightarrow> 
    dpda.det_stepn end_check_dpda' n (N p, map Input w, \<alpha>) = Some (q, [], \<gamma>)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" proof (induction n "(N p, map Input w, \<alpha>)" arbitrary: p w \<alpha> rule: dpda.det_stepn.induct[OF dpda_end_check])
    case (2 n \<alpha>)
    from 2(2) obtain p' w' \<alpha>' 
      where fs: "dpda.det_step\<^sub>1 end_check_dpda (N p, map Input w, \<alpha>) = Some (p', w', \<alpha>')"
        and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (q, [], \<gamma>)" by (auto split: option.splits)
    from fs obtain p'' where p'_def[simp]: "p' = N p''"
      using end_check_dpda_input_in_N by blast
    from fs obtain w'' where w'_def[simp]: "w' = map Input w''"
      using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by blast

    from 2(1)[OF fs _ _ lss[unfolded p'_def w'_def]]
    have "dpda.det_stepn end_check_dpda' n (p', w', \<alpha>') = Some (q, [], \<gamma>)" by simp

    moreover from fs have "dpda.det_step\<^sub>1 end_check_dpda' (N p, map Input w, \<alpha>) = Some (p', w', \<alpha>')"
      using end_check_dpda'_in_N_det_step\<^sub>1 by simp

    ultimately show ?case by simp
  qed simp
next
  show "?r \<Longrightarrow> ?l" proof (induction n "(N p, map Input w, \<alpha>)" arbitrary: p w \<alpha> rule: dpda.det_stepn.induct[OF dpda_end_check'])
    case (2 n \<alpha>)
    from 2(2) obtain p' w' \<alpha>' 
      where fs: "dpda.det_step\<^sub>1 end_check_dpda' (N p, map Input w, \<alpha>) = Some (p', w', \<alpha>')"
        and lss: "dpda.det_stepn end_check_dpda' n (p', w', \<alpha>') = Some (q, [], \<gamma>)" by (auto split: option.splits)
    from fs have *: "dpda.det_step\<^sub>1 end_check_dpda (N p, map Input w, \<alpha>) = Some (p', w', \<alpha>')"
      using end_check_dpda'_in_N_det_step\<^sub>1 by simp
    then obtain p'' where p'_def[simp]: "p' = N p''"
      using end_check_dpda_input_in_N by blast
    from * obtain w'' where w'_def[simp]: "w' = map Input w''"
      using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by blast
    from 2(1)[OF fs _ _ lss[unfolded p'_def w'_def]]
    have **: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (q, [], \<gamma>)" by simp
    from * ** show ?case by simp
  qed simp
qed

lemma end_check_dpda'_final_in_P:
  assumes "f \<in> final_states end_check_dpda"
  shows "dpda.det_step\<^sub>1 end_check_dpda' (f, w, Z#\<alpha>) = Some (f, w, Z#\<alpha>)"
using assms dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check'] by (auto simp: end_check_dpda'_def split: if_splits)

lemma end_check_dpda'_finals_in_P:
  assumes "f \<in> final_states end_check_dpda"
  shows "dpda.det_stepn end_check_dpda' n (f, w, Z#\<alpha>) = Some (f, w, Z#\<alpha>)"
by (induction n "(f, w, Z#\<alpha>)" rule: dpda.det_stepn.induct[OF dpda_end_check']) (use assms end_check_dpda'_final_in_P in auto) 

lemma end_check_dpda'_nonfinal_in_P:
  assumes "f \<notin> final_states end_check_dpda"
  shows "dpda.det_step\<^sub>1 end_check_dpda' (f, w\<^sub>1, \<alpha>) = Some (p, w\<^sub>2, \<beta>) \<longleftrightarrow> dpda.det_step\<^sub>1 end_check_dpda (f, w\<^sub>1, \<alpha>) = Some (p, w\<^sub>2, \<beta>)"
using assms dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check'] dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by (auto simp: end_check_dpda'_def split: if_splits)

lemma end_check_dpda_empty_in_P_end_check_dpda':
  assumes "dpda.det_stepn end_check_dpda n (P p, [], \<alpha>) = Some (q, [], \<gamma>)"
  shows "dpda.det_stepn end_check_dpda' n (P p, [], \<alpha>) = Some (q, [], \<gamma>) \<or>
  (\<exists>k f \<beta>. k < n \<and> f \<in> final_states end_check_dpda' \<and> dpda.det_stepn end_check_dpda' k (P p, [], \<alpha>) = Some (f, [], \<beta>))"
using assms proof (induction n "(P p, [] :: 'a input_with_marker list, \<alpha>)" arbitrary: p \<alpha> rule: dpda.det_stepn.induct[OF dpda_end_check])
  case (2 n \<alpha>)
  show ?case proof (cases "P p \<in> final_states end_check_dpda")
    case True

    hence "P p \<in> final_states end_check_dpda'"
      by (simp add: end_check_dpda'_def)

    moreover have "dpda.det_stepn end_check_dpda' 0 (P p, [], \<alpha>) = Some (P p, [], \<alpha>)" by simp

    ultimately show ?thesis by blast
  next
    case False
    from 2(2) obtain p' w' \<alpha>' where fs: "dpda.det_step\<^sub>1 end_check_dpda (P p, [], \<alpha>) = Some (p', w', \<alpha>')"
                                and lss: "dpda.det_stepn end_check_dpda n (p', w', \<alpha>') = Some (q, [], \<gamma>)" by (auto split: option.splits)
    from fs obtain p'' where p'_def[simp]: "p' = P p''"
      using end_check_dpda_in_P by blast
    from fs have w'_def[simp]: "w' = []"
      using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check] by auto
    from fs have *: "dpda.det_step\<^sub>1 end_check_dpda' (P p, [], \<alpha>) = Some (p', w', \<alpha>')"
      using end_check_dpda'_nonfinal_in_P[OF False] by simp
    from 2(1)[OF fs _ _ lss[unfolded p'_def w'_def]] have case_dist: 
    "dpda.det_stepn end_check_dpda' n (p', w', \<alpha>') = Some (q, [], \<gamma>) \<or>
      (\<exists>k f \<beta>. k < n \<and> f \<in> final_states end_check_dpda' \<and> dpda.det_stepn end_check_dpda' k (p', w', \<alpha>') = Some (f, [], \<beta>))" (is "?nh \<or> ?h") by simp
    show ?thesis proof (rule disjE[OF case_dist])
      assume nh: ?nh
      from * nh have "dpda.det_stepn end_check_dpda' (Suc n) (P p, [], \<alpha>) = Some (q, [], \<gamma>)" by simp
      then show ?thesis by blast
    next
      assume ?h
      then obtain k f \<beta> where k_less: "k < n" and f_final: "f \<in> final_states end_check_dpda'" and
         **: "dpda.det_stepn end_check_dpda' k (p', w', \<alpha>') = Some (f, [], \<beta>)" by blast

      from k_less have "Suc k < Suc n" by simp

      moreover from * ** have "dpda.det_stepn end_check_dpda' (Suc k) (P p, [], \<alpha>) = Some (f, [], \<beta>)" by simp

      ultimately show ?thesis
        using f_final by blast
    qed
  qed
qed simp

lemma end_check_dpda'_empty_in_P_end_check_dpda:
  assumes "dpda.det_stepn end_check_dpda' n (P p, [], \<alpha>) = Some (q, [], \<gamma>)"
  shows "\<exists>k \<le> n. dpda.det_stepn end_check_dpda k (P p, [], \<alpha>) = Some (q, [], \<gamma>)"
using assms proof (induction n "(P p, [] :: 'a input_with_marker list, \<alpha>)" arbitrary: p \<alpha> rule: dpda.det_stepn.induct[OF dpda_end_check'])
  case (2 n \<alpha>)
  from 2(2) obtain p' w' \<alpha>'' where fs: "dpda.det_step\<^sub>1 end_check_dpda' (P p, [], \<alpha>) = Some (p', w', \<alpha>'')"
                               and lss: "dpda.det_stepn end_check_dpda' n (p', w', \<alpha>'') = Some (q, [], \<gamma>)" by (auto split: option.splits)
  from fs obtain Z' \<alpha>' where [simp]: "\<alpha> = Z' # \<alpha>'"
    using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check'] by auto
  show ?case proof (cases "P p \<in> final_states end_check_dpda")
    case True
    from 2(2) have "q = P p \<and> \<gamma> = \<alpha>"
      using end_check_dpda'_finals_in_P[OF True] by simp
    hence "dpda.det_stepn end_check_dpda 0 (P p, [], \<alpha>) = Some (q, [], \<gamma>)" by simp
    then show ?thesis by blast
  next
    case False
    from fs have *: "dpda.det_step\<^sub>1 end_check_dpda (P p, [], \<alpha>) = Some (p', w', \<alpha>'')"
      using end_check_dpda'_nonfinal_in_P[OF False] by simp
    then obtain p'' where p'_def[simp]: "p' = P p''"
      using end_check_dpda_in_P by blast
    from fs have w'_def[simp]: "w' = []"
      using dpda.det_step\<^sub>1_rule_ext[OF dpda_end_check'] by simp
    from 2(1)[OF fs _ _ lss[unfolded p'_def w'_def]] obtain k where
    k_leq: "k \<le> n" and **: "dpda.det_stepn end_check_dpda k (p', w', \<alpha>'') = Some (q, [], \<gamma>)" by auto
    from * ** have "dpda.det_stepn end_check_dpda (Suc k) (P p, [], \<alpha>) = Some (q, [], \<gamma>)" by simp
    with k_leq show ?thesis by blast
  qed
qed simp

lemmas det_stepn_reads_input' =
  pda.stepn_reads_input[OF pda_end_check', simplified dpda.stepn_det_stepn_some[OF dpda_end_check'] dpda.step\<^sub>1_det_step\<^sub>1_some[OF dpda_end_check']]

lemmas det_stepn_word_app' =
  pda.stepn_word_app[OF pda_end_check', simplified dpda.stepn_det_stepn_some[OF dpda_end_check']]

lemmas det_stepn_split_last' =
  pda.stepn_split_last[OF pda_end_check', simplified dpda.stepn_det_stepn_some[OF dpda_end_check'] dpda.step\<^sub>1_det_step\<^sub>1_some[OF dpda_end_check']]

lemmas det_stepn_trans' =
  pda.stepn_trans[OF pda_end_check', simplified dpda.stepn_det_stepn_some[OF dpda_end_check']]

lemmas det_split_word' =
  pda.split_word[OF pda_end_check', simplified dpda.stepn_det_stepn_some[OF dpda_end_check']]

lemma end_check_dpda_marker_end_check_dpda':
  assumes "dpda.det_stepn end_check_dpda n (N p, [End_marker], \<alpha>) = Some (q, [], \<gamma>)"
  shows "dpda.det_stepn end_check_dpda' n (N p, [End_marker], \<alpha>) = Some (q, [], \<gamma>) \<or>
  (\<exists>k f \<beta>. k < n \<and> f \<in> final_states end_check_dpda' \<and> dpda.det_stepn end_check_dpda' k (N p, [End_marker], \<alpha>) = Some (f, [], \<beta>))"
proof -
  obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where n_def: "n = Suc n'" and k_less: "k \<le> n'" and 
   stepk: "dpda.det_stepn end_check_dpda k (N p, [End_marker], \<alpha>) = Some (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)" and
   step1: "dpda.det_step\<^sub>1 end_check_dpda (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)" and
   stepn'k: "dpda.det_stepn end_check_dpda (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (q, [], \<gamma>)"
    using det_stepn_reads_input(2)[OF assms] by blast
  from stepk have stepki: "dpda.det_stepn end_check_dpda k (N p, [], \<alpha>) = Some (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using det_stepn_word_app(2)[of k "N p" "[]" \<alpha> q\<^sub>1 "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  from stepki obtain q\<^sub>1' where [simp]: "q\<^sub>1 = N q\<^sub>1'"
    using end_check_dpda_inputs_in_N[where ?w\<^sub>1 = "[]"] by fastforce
  from stepki have "dpda.det_stepn end_check_dpda' k (N p, [], \<alpha>) = Some (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using end_check_dpda'_input_in_N_det_stepn[where ?w = "[]"] by simp

  hence "dpda.det_stepn end_check_dpda' k (N p, [End_marker], \<alpha>) = Some (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    using det_stepn_word_app'[of k "N p" "[]" \<alpha> q\<^sub>1 "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp

  moreover from step1 have "dpda.det_step\<^sub>1 end_check_dpda' (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)"
    using end_check_dpda'_in_N_det_step\<^sub>1 by simp

  ultimately have *: "dpda.det_stepn end_check_dpda' (Suc k) (N p, [End_marker], \<alpha>) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)"
    using det_stepn_split_last' by blast

  from step1 obtain q\<^sub>2' where q\<^sub>2_def[simp]: "q\<^sub>2 = P q\<^sub>2'"
    using end_check_dpda_marker_in_N by force
  have case_dist: "dpda.det_stepn end_check_dpda' (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (q, [], \<gamma>) \<or>
    (\<exists>k' f \<beta>. k' < n' - k \<and> f \<in> final_states end_check_dpda' \<and> dpda.det_stepn end_check_dpda' k' (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (f, [], \<beta>))" (is "?nh \<or> ?h")
    using end_check_dpda_empty_in_P_end_check_dpda'[OF stepn'k[unfolded q\<^sub>2_def]] by simp
  show ?thesis proof (rule disjE[OF case_dist])
    assume nh: ?nh
    from n_def k_less show ?thesis
      using det_stepn_trans'[OF * nh] by simp
  next
    assume h: ?h
    then obtain k' f \<beta> where k'_less: "k' < n' - k" and f_final: "f \<in> final_states end_check_dpda'" 
      and stepk': "dpda.det_stepn end_check_dpda' k' (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (f, [], \<beta>)" by blast

    from n_def k_less k'_less have "Suc k + k' < n" by simp

    moreover have "dpda.det_stepn end_check_dpda' (Suc k + k') (N p, [End_marker], \<alpha>) = Some (f, [], \<beta>)"
      using det_stepn_trans'[OF * stepk'] .

    ultimately show ?thesis 
      using f_final by blast
  qed
qed

lemma end_check_dpda'_marker_end_check_dpda:
  assumes "dpda.det_stepn end_check_dpda' n (N p, [End_marker], \<alpha>) = Some (q, [], \<gamma>)"
  shows "\<exists>k \<le> n. dpda.det_stepn end_check_dpda k (N p, [End_marker], \<alpha>) = Some (q, [], \<gamma>)"
proof -
  obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where n_def: "n = Suc n'" and k_less: "k \<le> n'" and 
   stepk': "dpda.det_stepn end_check_dpda' k (N p, [End_marker], \<alpha>) = Some (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)" and
   step1': "dpda.det_step\<^sub>1 end_check_dpda' (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)" and
   stepn'k': "dpda.det_stepn end_check_dpda' (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (q, [], \<gamma>)"
    using det_stepn_reads_input'[OF assms] by blast
  from stepk' have "dpda.det_stepn end_check_dpda' k (N p, [], \<alpha>) = Some (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using det_stepn_word_app'[of k "N p" "[]" \<alpha> q\<^sub>1 "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  hence stepki: "dpda.det_stepn end_check_dpda k (N p, [], \<alpha>) = Some (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using end_check_dpda'_input_in_N_det_stepn[where ?w = "[]"] by simp
  from stepki obtain q\<^sub>1' where [simp]: "q\<^sub>1 = N q\<^sub>1'"
    using end_check_dpda_inputs_in_N[where ?w\<^sub>1 = "[]"] by fastforce

  from stepki have "dpda.det_stepn end_check_dpda k (N p, [End_marker], \<alpha>) = Some (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    using det_stepn_word_app(2)[of k "N p" "[]" \<alpha> q\<^sub>1 "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp

  moreover from step1' have step1i: "dpda.det_step\<^sub>1 end_check_dpda (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)"
    using end_check_dpda'_in_N_det_step\<^sub>1 by simp

  ultimately have *: "dpda.det_stepn end_check_dpda (Suc k) (N p, [End_marker], \<alpha>) = Some (q\<^sub>2, [], \<gamma>\<^sub>2)"
    using det_stepn_split_last(2) by blast

  from step1i obtain q\<^sub>2' where [simp]: "q\<^sub>2 = P q\<^sub>2'"
    using end_check_dpda_marker_in_N by force
  from stepn'k' obtain k' where k'_less: "k' \<le> n' - k" and
    **: "dpda.det_stepn end_check_dpda k' (q\<^sub>2, [], \<gamma>\<^sub>2) = Some (q, [], \<gamma>)"
    using end_check_dpda'_empty_in_P_end_check_dpda by force
  from n_def k_less k'_less have "Suc k + k' \<le> n" by simp  
  thus ?thesis
    using det_stepn_trans(2)[OF * **] by blast
qed

lemma accepted_end_check':
"(\<exists>q \<gamma> n. q \<in> final_states end_check_dpda \<and> dpda.det_stepn end_check_dpda n (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q, [], \<gamma>)) \<longleftrightarrow>
  (\<exists>q \<gamma> n. q \<in> final_states end_check_dpda' \<and> dpda.det_stepn end_check_dpda' n (init_state end_check_dpda', word_with_end w, [init_symbol end_check_dpda']) = Some (q, [], \<gamma>))"
(is "?l \<longleftrightarrow> ?r") proof
  assume ?l
  then obtain q \<gamma> n where q_final: "q \<in> final_states end_check_dpda" and detstepn: "dpda.det_stepn end_check_dpda n
         (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q, [], \<gamma>)" by blast
  obtain k q' \<gamma>' where k_leq: "k \<le> n" and detstepk: "dpda.det_stepn end_check_dpda k 
   (init_state end_check_dpda, map Input w, [init_symbol end_check_dpda]) = Some (q', [], \<gamma>')" and
   detstepnk: "dpda.det_stepn end_check_dpda (n - k) (q', [End_marker], \<gamma>') = Some (q, [], \<gamma>)"
    using det_split_word(2)[OF detstepn] by blast
  from detstepk obtain q'n where q'_def[simp]: "q' = N q'n"
    using end_check_dpda_inputs_in_N by (force simp: end_check_dpda_def)
  from detstepk have "dpda.det_stepn end_check_dpda' k
      (init_state end_check_dpda, map Input w, [init_symbol end_check_dpda]) = Some (q', [], \<gamma>')"
    using end_check_dpda'_input_in_N_det_stepn by (simp add: end_check_dpda_def)
  hence detstepk': "dpda.det_stepn end_check_dpda' k
      (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q', [End_marker], \<gamma>')"
    using det_stepn_word_app'[of k "init_state end_check_dpda" "map Input w" "[init_symbol end_check_dpda]" q' "[]" \<gamma>' "[End_marker]"] by simp
  have case_dist: "dpda.det_stepn end_check_dpda' (n - k) (q', [End_marker], \<gamma>') = Some (q, [], \<gamma>) \<or>
  (\<exists>k' f \<beta>. k' < n - k \<and> f \<in> final_states end_check_dpda' \<and>
      dpda.det_stepn end_check_dpda' k' (q', [End_marker], \<gamma>') = Some (f, [], \<beta>))" (is "?nh \<or> ?h")
    using end_check_dpda_marker_end_check_dpda'[OF detstepnk[unfolded q'_def]] by simp
  show ?r proof (rule disjE[OF case_dist])
    assume nh: ?nh
    from k_leq have "dpda.det_stepn end_check_dpda' n
      (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q, [], \<gamma>)"
      using det_stepn_trans'[OF detstepk' nh] by simp
    with q_final show ?thesis
      by (auto simp: end_check_dpda'_def)
  next
    assume ?h
    then obtain k' f \<beta> where f_final: "f \<in> final_states end_check_dpda'" and
     detstepk'': "dpda.det_stepn end_check_dpda' k' (q', [End_marker], \<gamma>') = Some (f, [], \<beta>)" by blast
    have "dpda.det_stepn end_check_dpda' (k + k') 
      (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) =  Some (f, [], \<beta>)"
      using det_stepn_trans'[OF detstepk' detstepk''] .
    with f_final show ?thesis 
      by (auto simp: end_check_dpda'_def)
  qed
next
  assume ?r
  then obtain q \<gamma> n where q_final: "q \<in> final_states end_check_dpda'" and detstepn': "dpda.det_stepn end_check_dpda' n
      (init_state end_check_dpda', word_with_end w, [init_symbol end_check_dpda']) = Some (q, [], \<gamma>)" by blast
  obtain k q' \<gamma>' where k_leq: "k \<le> n" and detstepk': "dpda.det_stepn end_check_dpda' k 
   (init_state end_check_dpda', map Input w, [init_symbol end_check_dpda']) = Some (q', [], \<gamma>')" and
   detstepnk': "dpda.det_stepn end_check_dpda' (n - k) (q', [End_marker], \<gamma>') = Some (q, [], \<gamma>)"
    using det_split_word'[OF detstepn'] by blast
  from detstepk' have detstepi: "dpda.det_stepn end_check_dpda k 
    (init_state end_check_dpda, map Input w, [init_symbol end_check_dpda]) = Some (q', [], \<gamma>')"
    using end_check_dpda'_input_in_N_det_stepn by (simp add: end_check_dpda'_def end_check_dpda_def)
  then obtain q'n where q'_def[simp]: "q' = N q'n"
    using end_check_dpda_inputs_in_N by (force simp: end_check_dpda_def)
  from detstepi have detstepk: "dpda.det_stepn end_check_dpda k 
    (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q', [End_marker], \<gamma>')"
    using det_stepn_word_app(2)[of k "init_state end_check_dpda" "map Input w" "[init_symbol end_check_dpda]" q' "[]" \<gamma>' "[End_marker]"] by simp
  obtain k' where detstepk'': "dpda.det_stepn end_check_dpda k' (q', [End_marker], \<gamma>') = Some (q, [], \<gamma>)"
    using end_check_dpda'_marker_end_check_dpda[OF detstepnk'[unfolded q'_def]] by auto
  have "dpda.det_stepn end_check_dpda (k + k') 
      (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) = Some (q, [], \<gamma>)"
    using det_stepn_trans(2)[OF detstepk detstepk''] .
  with q_final show ?l
    by (auto simp: end_check_dpda'_def)
qed

lemma lang_end_check_dpda':
  "dpda.det_final_accept end_check_dpda' = dpda.det_final_accept end_check_dpda"
unfolding dpda.det_final_accept_def[OF dpda_end_check] dpda.det_final_accept_def[OF dpda_end_check'] using accepted_end_check' by fast

end
end