theory Complement_DPDA
  imports DPDA
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

lemma pda_end_check: "pda end_check_dpda"
  using dpda_def dpda_end_check by auto

lemma end_check_dpda_input_step\<^sub>1:
  "pda.step\<^sub>1 M (p\<^sub>1, map Input w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.step\<^sub>1 end_check_dpda (N p\<^sub>1, map Input w\<^sub>1, \<alpha>\<^sub>1) (N p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
by (use step\<^sub>1_rule_ext end_check_dpda_def pda.step\<^sub>1_rule_ext[OF pda_end_check] in auto)

lemma end_check_dpda_marker_step\<^sub>1:
  "pda.step\<^sub>1 M (p\<^sub>1, End_marker#w, \<alpha>\<^sub>1) (p\<^sub>2, w, \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.step\<^sub>1 end_check_dpda (N p\<^sub>1, End_marker#w, \<alpha>\<^sub>1) (P p\<^sub>2, w, \<alpha>\<^sub>2)"
by (use step\<^sub>1_rule_ext end_check_dpda_def pda.step\<^sub>1_rule_ext[OF pda_end_check] in auto)

lemma end_check_dpda_P_step\<^sub>1:
  "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.step\<^sub>1 end_check_dpda (P p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
by (use step\<^sub>1_rule_ext end_check_dpda_def pda.step\<^sub>1_rule_ext[OF pda_end_check] in auto)

lemma end_check_dpda_input_in_N:
  assumes "pda.step\<^sub>1 end_check_dpda (N p, map Input w\<^sub>1, \<alpha>\<^sub>1) (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = N q'"
by (use assms end_check_dpda_def pda.step\<^sub>1_rule_ext[OF pda_end_check] in auto)

lemma end_check_dpda_marker_in_N:
  assumes "pda.step\<^sub>1 end_check_dpda (N p, End_marker#w, \<alpha>\<^sub>1) (q, w, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
by (use assms end_check_dpda_def pda.step\<^sub>1_rule_ext[OF pda_end_check] in auto)

lemma end_check_dpda_inputs_in_N:
  assumes "pda.steps end_check_dpda (N p, map Input w\<^sub>1, \<alpha>\<^sub>1) (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = N q'"
  by (induction "(N p, map Input w\<^sub>1, \<alpha>\<^sub>1)" "(q, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p w\<^sub>1 \<alpha>\<^sub>1 rule: pda.steps_induct[OF pda_end_check])
       (use assms end_check_dpda_input_in_N pda.step\<^sub>1_rule_ext[OF pda_end_check] in blast)+

lemma end_check_dpda_input_in_N_stepn:
  "pda.stepn M n (p\<^sub>1, map Input w, \<alpha>\<^sub>1) (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.stepn end_check_dpda n (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) (N p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof 
  show "?l \<Longrightarrow> ?r" proof (induction n "(p\<^sub>1, map Input w, \<alpha>\<^sub>1)" "(p\<^sub>2, [] :: 'a input_with_marker list, \<alpha>\<^sub>2)" 
                            arbitrary: p\<^sub>1 w \<alpha>\<^sub>1 rule: stepn_induct)
    case (stepn n p\<^sub>1 \<alpha>\<^sub>1 p' w' \<alpha>')
    from stepn(1) obtain w'' where w'_def: "w' = map Input w''"
      using step\<^sub>1_rule_ext by auto

    with stepn(3) have "pda.stepn end_check_dpda n (N p', w', \<alpha>') (N p\<^sub>2, [], \<alpha>\<^sub>2)" by simp 

    moreover from stepn(1) have "pda.step\<^sub>1 end_check_dpda (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) (N p', w', \<alpha>')"
      using end_check_dpda_input_step\<^sub>1 by simp

    ultimately show ?case
      using pda.stepn_split_first[OF pda_end_check] by blast
  qed (simp add: pda.refl\<^sub>n[OF pda_end_check])
next
  assume r: ?r
  thus ?l proof (induction n "(N p\<^sub>1, map Input w, \<alpha>\<^sub>1)" "(N p\<^sub>2, [] :: 'a input_with_marker list, \<alpha>\<^sub>2)" 
                            arbitrary: p\<^sub>1 w \<alpha>\<^sub>1 rule: pda.stepn_induct[OF pda_end_check])
    case (3 n \<alpha>\<^sub>1 p' w' \<alpha>')
    from 3(1) obtain p'' where p'_def: "p' = N p''"
      using end_check_dpda_input_in_N by blast
    from 3(1) obtain w'' where w'_def: "w' = map Input w''"
      using pda.step\<^sub>1_rule_ext[OF pda_end_check] by blast

    from p'_def w'_def 3(2,3) have "stepn n (p'', w', \<alpha>') (p\<^sub>2, [], \<alpha>\<^sub>2)" by simp

    moreover from p'_def 3(1) have "step\<^sub>1 (p\<^sub>1, map Input w, \<alpha>\<^sub>1) (p'', w', \<alpha>')"
      using end_check_dpda_input_step\<^sub>1 by simp

    ultimately show ?case
      using stepn_split_first by blast
  qed (rule r, simp)
qed 

lemma end_check_dpda_in_P:
  assumes "pda.step\<^sub>1 end_check_dpda (P p, w\<^sub>1, \<alpha>\<^sub>1) (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
by (use assms end_check_dpda_def pda.step\<^sub>1_rule_ext[OF pda_end_check] in auto)

lemma end_check_dpda_in_P_stepn:
  "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.stepn end_check_dpda n (P p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
    from step\<^sub>n(3) have "pda.step\<^sub>1 end_check_dpda (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (P p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
      using end_check_dpda_P_step\<^sub>1 by simp
    with step\<^sub>n(2) show ?case
      using pda.step\<^sub>n[OF pda_end_check] by simp
  qed (simp add: pda.refl\<^sub>n[OF pda_end_check])
next
  assume r: ?r
  thus ?l
  proof (induction n "(P p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: pda.stepn_induct[OF pda_end_check])
    case (3 n w\<^sub>1 \<alpha>\<^sub>1 p' w' \<alpha>')
    from 3(1) obtain p'' where p'_def: "p' = P p''"
      using end_check_dpda_in_P by blast

    from p'_def 3(2,3) have "stepn n (p'', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by simp

    moreover from p'_def 3(1) have "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p'', w', \<alpha>')"
      using end_check_dpda_P_step\<^sub>1 by simp

    ultimately show ?case
      using stepn_split_first by blast
  qed (rule r, simp)
qed

lemma end_check_dpda_marker_stepn:
  "pda.stepn M n (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.stepn end_check_dpda n (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (P p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l
  obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where n_def: "n = Suc n'" and k_less: "k \<le> n'" and stepk: "stepn k (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    and step1: "step\<^sub>1 (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) (q\<^sub>2, [], \<gamma>\<^sub>2)" and stepn'k: "stepn (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using stepn_reads_input[OF l] by blast 
  from stepk have "stepn k (p\<^sub>1, [], \<alpha>\<^sub>1) (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using stepn_word_app[of k p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1 "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  hence "pda.stepn end_check_dpda k (N p\<^sub>1, [], \<alpha>\<^sub>1) (N q\<^sub>1, [], \<gamma>\<^sub>1)"
    using end_check_dpda_input_in_N_stepn[where ?w = "[]"] by simp

  hence *: "pda.stepn end_check_dpda k (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (N q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    using pda.stepn_word_app[OF pda_end_check, of k "N p\<^sub>1" "[]" \<alpha>\<^sub>1 "N q\<^sub>1" "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp

  from step1 have **: "pda.step\<^sub>1 end_check_dpda (N q\<^sub>1, [End_marker], \<gamma>\<^sub>1) (P q\<^sub>2, [], \<gamma>\<^sub>2)"
    using end_check_dpda_marker_step\<^sub>1 by simp

  from stepn'k have ***: "pda.stepn end_check_dpda (n' - k) (P q\<^sub>2, [], \<gamma>\<^sub>2) (P p\<^sub>2, [], \<alpha>\<^sub>2)" 
    using end_check_dpda_in_P_stepn by simp

  from n_def k_less show ?r 
    using pda.stepn_trans[OF pda_end_check pda.step\<^sub>n[OF pda_end_check * **] ***] by simp
next
  assume r: ?r
  obtain n' k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where n_def: "n = Suc n'" and k_less: "k \<le> n'" and 
          stepk: "pda.stepn end_check_dpda k (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)" and
          step1: "pda.step\<^sub>1 end_check_dpda (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) (q\<^sub>2, [], \<gamma>\<^sub>2)" and
          stepn'k: "pda.stepn end_check_dpda (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using pda.stepn_reads_input[OF pda_end_check r] by blast
  from stepk have stepk_emp: "pda.stepn end_check_dpda k (N p\<^sub>1, [], \<alpha>\<^sub>1) (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using pda.stepn_word_app[OF pda_end_check] by fastforce
  then obtain q\<^sub>1' where q1_def: "q\<^sub>1 = N q\<^sub>1'"
    using pda.stepn_steps[OF pda_end_check] end_check_dpda_inputs_in_N[of p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1 "[]" \<gamma>\<^sub>1] by fastforce
  with stepk_emp have "stepn k (p\<^sub>1, [], \<alpha>\<^sub>1) (q\<^sub>1', [], \<gamma>\<^sub>1)"
    using end_check_dpda_input_in_N_stepn[where ?w = "[]"] by simp

  hence *: "stepn k (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (q\<^sub>1', [End_marker], \<gamma>\<^sub>1)"
    using stepn_word_app[of k p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1' "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  from step1 q1_def obtain q\<^sub>2' where q2_def: "q\<^sub>2 = P q\<^sub>2'"
    using end_check_dpda_marker_in_N by blast

  with stepn'k have **: "stepn (n' - k) (q\<^sub>2', [], \<gamma>\<^sub>2) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_in_P_stepn by simp

  from q1_def q2_def step1 have ***: "step\<^sub>1 (q\<^sub>1', [End_marker], \<gamma>\<^sub>1) (q\<^sub>2', [], \<gamma>\<^sub>2)"
    using end_check_dpda_marker_step\<^sub>1 by simp

  from n_def k_less show ?l 
    using stepn_trans[OF step\<^sub>n[OF * ***] **] by simp
qed

lemma end_check_dpda_stepn:
  "pda.stepn M n (p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
     pda.stepn end_check_dpda n (N p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) (P p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l
  obtain k q \<gamma> where k_less: "k \<le> n" and stepk: "pda.stepn M k (p\<^sub>1, map Input w, \<alpha>\<^sub>1) (q, [], \<gamma>)" 
                            and stepnk: "pda.stepn M (n - k) (q, [End_marker], \<gamma>) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using split_word[OF l] by blast
  from stepk have "pda.stepn end_check_dpda k (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) (N q, [], \<gamma>)"
    using end_check_dpda_input_in_N_stepn by simp

  hence "pda.stepn end_check_dpda k (N p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) (N q, [End_marker], \<gamma>)"
    using pda.stepn_word_app[OF pda_end_check, of k "N p\<^sub>1" "map Input w" "\<alpha>\<^sub>1" "N q" "[]" \<gamma> "[End_marker]"] by simp 

  moreover from stepnk have "pda.stepn end_check_dpda (n - k) (N q, [End_marker], \<gamma>) (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_marker_stepn by simp

  ultimately show ?r
    using k_less pda.stepn_trans[OF pda_end_check] by fastforce 
next
  assume r: ?r
  obtain k q \<gamma> where k_less: "k \<le> n" and stepk: "pda.stepn end_check_dpda k (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) (q, [], \<gamma>)"
                      and stepnk: "pda.stepn end_check_dpda (n - k) (q, [End_marker], \<gamma>) (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using pda.split_word[OF pda_end_check r] by blast
  from stepk obtain q' where q_def: "q = N q'" 
    using pda.stepn_steps[OF pda_end_check] end_check_dpda_inputs_in_N by blast
  with stepk have "pda.stepn M k (p\<^sub>1, map Input w, \<alpha>\<^sub>1) (q', [], \<gamma>)"
    using end_check_dpda_input_in_N_stepn by simp

  hence "pda.stepn M k (p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) (q', [End_marker], \<gamma>)"
    using stepn_word_app[of k p\<^sub>1 "map Input w" \<alpha>\<^sub>1 q' "[]" \<gamma> "[End_marker]"] by simp

  moreover from q_def stepnk have "pda.stepn M (n-k) (q', [End_marker], \<gamma>) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_marker_stepn by simp

  ultimately show ?l
    using k_less stepn_trans by fastforce
qed

lemma accepted_end_check:
"(\<exists>q \<gamma>. q \<in> final_states M \<and> pda.steps M (init_state M, word_with_end w, [init_symbol M]) (q, [], \<gamma>)) \<longleftrightarrow>
  (\<exists>q \<gamma>. q \<in> final_states end_check_dpda \<and> pda.steps end_check_dpda (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) (q, [], \<gamma>))"
(is "?l \<longleftrightarrow> ?r") proof
  assume ?l
  then obtain q \<gamma> where q_final: "q \<in> final_states M" and steps: "steps (init_state M, word_with_end w, [init_symbol M]) (q, [], \<gamma>)" by blast
  from q_final have *: "P q \<in> final_states end_check_dpda"
    by (simp add: end_check_dpda_def end_check_final_states_def)
  from steps have "pda.steps end_check_dpda (N (init_state M), word_with_end w, [init_symbol M]) (P q, [], \<gamma>)"
    using stepn_steps end_check_dpda_stepn[where ?w = w and ?\<alpha>\<^sub>1 = "[init_symbol M]" and ?\<alpha>\<^sub>2 = \<gamma>] 
           pda.stepn_steps[OF pda_end_check] by blast
  hence **: "pda.steps end_check_dpda (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) (P q, [], \<gamma>)"
    by (simp add: end_check_dpda_def)
  from * ** show ?r by blast
next
  assume ?r
  then obtain q \<gamma> where q_final: "q \<in> final_states end_check_dpda" and steps: "pda.steps end_check_dpda
         (init_state end_check_dpda, word_with_end w, [init_symbol end_check_dpda]) (q, [], \<gamma>)" by blast
  from q_final[unfolded end_check_dpda_def end_check_final_states_def] obtain q' 
                                       where q_def: "q = P q'" and *: "q' \<in> final_states M" by auto
  from q_def steps have "pda.steps end_check_dpda 
                      (N (init_state M), word_with_end w, [init_symbol M]) (P q', [], \<gamma>)" 
    by (simp add: end_check_dpda_def)
  hence **: "pda.steps M (init_state M, word_with_end w, [init_symbol M]) (q', [], \<gamma>)"
    using pda.stepn_steps[OF pda_end_check] 
          end_check_dpda_stepn[where ?w = w and ?\<alpha>\<^sub>1 = "[init_symbol M]" and ?\<alpha>\<^sub>2 = \<gamma>] stepn_steps by blast
  from * ** show ?l by blast 
qed

lemma lang_end_check_dpda:
  "dpda.final_accept_det M = dpda.final_accept_det end_check_dpda"
unfolding final_accept_det_def dpda.final_accept_det_def[OF dpda_end_check] using accepted_end_check by simp

end
end