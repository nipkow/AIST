theory Complement_DPDA
  imports DPDA
begin

datatype 'q st_primed = N 'q | P 'q

context dpda begin

definition "end_check_states \<equiv> N ` states M \<union> P ` states M"

definition "end_check_final_states \<equiv> P ` final_states M"

fun end_check_trans_fun :: "'q st_primed \<Rightarrow> 'a input_with_marker \<Rightarrow> 's \<Rightarrow> ('q st_primed \<times> 's list) set" where
  "end_check_trans_fun (N q) (Input a) Z = (\<lambda>(p, \<alpha>). (N p, \<alpha>)) ` (trans_fun M q (Input a) Z)"
| "end_check_trans_fun (P q) a Z = (\<lambda>(p, \<alpha>). (P p, \<alpha>)) ` (trans_fun M q a Z)"
| "end_check_trans_fun (N q) End_marker Z = (\<lambda>(p, \<alpha>). (P p, \<alpha>)) ` (trans_fun M q End_marker Z)"

fun end_check_eps_fun :: "'q st_primed \<Rightarrow> 's \<Rightarrow> ('q st_primed \<times> 's list) set" where
  "end_check_eps_fun (N q) Z = (\<lambda>(p, \<alpha>). (N p, \<alpha>)) ` (eps_fun M q Z)"
| "end_check_eps_fun (P q) Z = (\<lambda>(p, \<alpha>). (P p, \<alpha>)) ` (eps_fun M q Z)"

definition end_check_dpda :: "('q st_primed, 'a input_with_marker, 's) pda" where
  "end_check_dpda \<equiv> \<lparr> states = end_check_states, init_state = N (init_state M), init_symbol = init_symbol M, 
                      final_states = end_check_final_states, trans_fun = end_check_trans_fun, eps_fun = end_check_eps_fun \<rparr>"

lemma end_check_card_trans_N: "card (end_check_trans_fun (N q) a Z) = card (trans_fun M q a Z)"
proof -
  have inj_on_N: "inj_on (\<lambda>(p, \<alpha>). (N p, \<alpha>)) (trans_fun M q a Z)"
    by (auto simp: inj_on_def)
  have inj_on_P: "inj_on (\<lambda>(p, \<alpha>). (P p, \<alpha>)) (trans_fun M q a Z)"
    by (auto simp: inj_on_def)
  show ?thesis
  using card_image[OF inj_on_N] card_image[OF inj_on_P]
  by (induction "N q" a Z rule: end_check_trans_fun.induct) auto
qed

lemma end_check_card_trans_P: "card (end_check_trans_fun (P q) a Z) = card (trans_fun M q a Z)"
proof -
  have inj_on_P: "inj_on (\<lambda>(p, \<alpha>). (P p, \<alpha>)) (trans_fun M q a Z)"
    by (auto simp: inj_on_def)
  show ?thesis
  using card_image[OF inj_on_P] by simp
qed

lemma end_check_card_eps_N: "card (end_check_eps_fun (N q) Z) = card (eps_fun M q Z)"
proof -
  have inj_on_N: "inj_on (\<lambda>(p, \<alpha>). (N p, \<alpha>)) (eps_fun M q Z)"
    by (auto simp: inj_on_def)
  show ?thesis
    using card_image[OF inj_on_N] by simp
qed

lemma end_check_card_eps_P: "card (end_check_eps_fun (P q) Z) = card (eps_fun M q Z)"
proof -
  have inj_on_P: "inj_on (\<lambda>(p, \<alpha>). (P p, \<alpha>)) (eps_fun M q Z)"
    by (auto simp: inj_on_def)
  show ?thesis
    using card_image[OF inj_on_P] by simp
qed

lemma dpda_end_check: "dpda end_check_dpda"
proof (standard, goal_cases)
  case 1
  then show ?case
    unfolding end_check_dpda_def end_check_states_def using init by simp
next
  case 2
  then show ?case
    unfolding end_check_dpda_def end_check_states_def end_check_final_states_def using final by auto
next
  case (3 p x z)
  from 3[unfolded end_check_dpda_def end_check_states_def]
  have "fst ` end_check_trans_fun p x z \<subseteq> N ` states M \<union> P ` states M"
    using trans by (induction p x z rule: end_check_trans_fun.induct) fastforce+
  then show ?case
    unfolding end_check_dpda_def end_check_states_def by simp
next
  case (4 p z)
  from 4[unfolded end_check_dpda_def end_check_states_def]
  have "fst ` end_check_eps_fun p z \<subseteq> N ` states M \<union> P ` states M"
    using eps by (induction p z rule: end_check_eps_fun.induct) fastforce+
  then show ?case
    unfolding end_check_dpda_def end_check_states_def by simp
next
  case 5
  then show ?case
    unfolding end_check_dpda_def end_check_states_def using finite_states by simp
next
  case (6 p x z)
  have "finite (end_check_trans_fun p x z)"
    by (induction p x z rule: end_check_trans_fun.induct) (auto simp: finite_trans)
  then show ?case
    unfolding end_check_dpda_def by simp
next
  case (7 p z)
  have "finite (end_check_eps_fun p z)"
    by (induction p z rule: end_check_eps_fun.induct) (auto simp: finite_eps)
  then show ?case
    unfolding end_check_dpda_def by simp
next
  case (8 q a Z)
  then show ?case 
    using det end_check_card_trans_N end_check_card_eps_N end_check_card_trans_P end_check_card_eps_P
    by (cases q) (auto simp: end_check_dpda_def)
next
  case (9 q \<alpha> p a)
  hence "(q, \<alpha>) \<in> end_check_trans_fun p a (init_symbol M)"
    unfolding end_check_dpda_def by simp
  hence "\<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
    by (induction p a "init_symbol M" rule: end_check_trans_fun.induct) (auto simp: init_trans)
  thus ?case
    unfolding end_check_dpda_def by simp
next
  case (10 q \<alpha> p)
  hence "(q, \<alpha>) \<in> end_check_eps_fun p (init_symbol M)"
    unfolding end_check_dpda_def by simp
  hence "\<exists>\<alpha>'. \<alpha> = \<alpha>' @ [init_symbol M]"
    by (induction p "init_symbol M" rule: end_check_eps_fun.induct) (auto simp: init_eps)
  thus ?case
    unfolding end_check_dpda_def by simp
qed

lemma pda_end_check: "pda end_check_dpda"
  by (auto simp: dpda_end_check dpda.pda)

lemma end_check_dpda_trans_N: 
"(p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 (Input a) Z \<longleftrightarrow> (N p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (N p\<^sub>1) (Input a) Z"
(is "?l \<longleftrightarrow> ?r")
proof 
  show "?l \<Longrightarrow> ?r" by (auto simp: end_check_dpda_def)
next
  have "(N p\<^sub>2, \<beta>) \<in> end_check_trans_fun (N p\<^sub>1) (Input a) Z \<Longrightarrow> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 (Input a) Z"
    by (induction "N p\<^sub>1" "Input a" Z rule: end_check_trans_fun.induct) auto
  thus "?r \<Longrightarrow> ?l"
    by (simp add: end_check_dpda_def)
qed

lemma end_check_dpda_eps_N: 
"(p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z \<longleftrightarrow> (N p\<^sub>2, \<beta>) \<in> eps_fun end_check_dpda (N p\<^sub>1) Z"
(is "?l \<longleftrightarrow> ?r")
proof 
  show "?l \<Longrightarrow> ?r" by (auto simp: end_check_dpda_def)
next
  have "(N p\<^sub>2, \<beta>) \<in> end_check_eps_fun (N p\<^sub>1) Z \<Longrightarrow> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z"
    by (induction "N p\<^sub>1" Z rule: end_check_eps_fun.induct) auto
  thus "?r \<Longrightarrow> ?l"
    by (simp add: end_check_dpda_def)
qed

lemma end_check_dpda_trans_marker_N:
"(p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 End_marker Z \<longleftrightarrow> (P p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (N p\<^sub>1) End_marker Z" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by (auto simp: end_check_dpda_def)
next
  have "(P p\<^sub>2, \<beta>) \<in> end_check_trans_fun (N p\<^sub>1) End_marker Z \<Longrightarrow> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 End_marker Z"
    by (induction "N p\<^sub>1" "End_marker :: 'a input_with_marker" Z rule: end_check_trans_fun.induct) auto
  thus "?r \<Longrightarrow> ?l"
    by (simp add: end_check_dpda_def)
qed

lemma end_check_dpda_eps_P:
"(p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z \<longleftrightarrow> (P p\<^sub>2, \<beta>) \<in> eps_fun end_check_dpda (P p\<^sub>1) Z" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by (auto simp: end_check_dpda_def)
next
  have "(P p\<^sub>2, \<beta>) \<in> end_check_eps_fun (P p\<^sub>1) Z \<Longrightarrow> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z"
    by (induction "P p\<^sub>1" Z rule: end_check_eps_fun.induct) auto
  thus "?r \<Longrightarrow> ?l"
    by (simp add: end_check_dpda_def)
qed

lemma end_check_dpda_trans_P:
"(p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 a Z \<longleftrightarrow> (P p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (P p\<^sub>1) a Z" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by (auto simp: end_check_dpda_def)
next
  have "(P p\<^sub>2, \<beta>) \<in> end_check_trans_fun (P p\<^sub>1) a Z \<Longrightarrow> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 a Z"
    by (induction "P p\<^sub>1" a Z rule: end_check_trans_fun.induct) auto
  thus "?r \<Longrightarrow> ?l"
    by (simp add: end_check_dpda_def)
qed

lemma end_check_dpda_input_step\<^sub>1:
  "pda.step\<^sub>1 M (p\<^sub>1, map Input w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.step\<^sub>1 end_check_dpda (N p\<^sub>1, map Input w\<^sub>1, \<alpha>\<^sub>1) (N p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain Z \<alpha> where \<alpha>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and rule:
       "(\<exists>\<beta>. w\<^sub>2 = map Input w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) \<or>
          (\<exists>a \<beta>. map Input w\<^sub>1 = Input a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 (Input a) Z)"
    using step\<^sub>1_rule_ext by auto
  from rule have "(\<exists>\<beta>. w\<^sub>2 = map Input w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (N p\<^sub>2, \<beta>) \<in> eps_fun end_check_dpda (N p\<^sub>1) Z) \<or>
     (\<exists>a \<beta>. map Input w\<^sub>1 = Input a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (N p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (N p\<^sub>1) (Input a) Z)"
    using end_check_dpda_trans_N end_check_dpda_eps_N by simp
  with \<alpha>1_def show ?r
    using pda.step\<^sub>1_rule[OF pda_end_check] by auto
next
  assume ?r
  then obtain Z \<alpha> where \<alpha>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and rule:
       "(\<exists>\<beta>. w\<^sub>2 = map Input w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (N p\<^sub>2, \<beta>) \<in> eps_fun end_check_dpda (N p\<^sub>1) Z) \<or>
          (\<exists>a \<beta>. map Input w\<^sub>1 = Input a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (N p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (N p\<^sub>1) (Input a) Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_end_check] by auto
  from rule have "(\<exists>\<beta>. w\<^sub>2 = map Input w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) \<or>
     (\<exists>a \<beta>. map Input w\<^sub>1 = Input a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 (Input a) Z)"
    using end_check_dpda_trans_N end_check_dpda_eps_N by simp
  with \<alpha>1_def show ?l
    using step\<^sub>1_rule by auto
qed

lemma end_check_dpda_marker_step\<^sub>1:
  "pda.step\<^sub>1 M (p\<^sub>1, End_marker#w, \<alpha>\<^sub>1) (p\<^sub>2, w, \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.step\<^sub>1 end_check_dpda (N p\<^sub>1, End_marker#w, \<alpha>\<^sub>1) (P p\<^sub>2, w, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain Z \<alpha> \<beta> where \<alpha>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and \<alpha>2_def: "\<alpha>\<^sub>2 = \<beta> @ \<alpha>" and trans: "(p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 End_marker Z"
    using step\<^sub>1_rule_ext by auto
  from trans have "(P p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (N p\<^sub>1) End_marker Z"
    using end_check_dpda_trans_marker_N by simp
  with \<alpha>1_def \<alpha>2_def show ?r
    using pda.step\<^sub>1_rule[OF pda_end_check] by simp
next 
  assume ?r
  then obtain Z \<alpha> \<beta> where \<alpha>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and \<alpha>2_def: "\<alpha>\<^sub>2 = \<beta> @ \<alpha>" and trans: "(P p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (N p\<^sub>1) End_marker Z"
    using pda.step\<^sub>1_rule_ext[OF pda_end_check] by auto
  from trans have "(p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 End_marker Z"
    using end_check_dpda_trans_marker_N by simp
  with \<alpha>1_def \<alpha>2_def show ?l
    using step\<^sub>1_rule by simp
qed

lemma end_check_dpda_input_in_N:
  assumes "pda.step\<^sub>1 end_check_dpda (N p, map Input w\<^sub>1, \<alpha>\<^sub>1) (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = N q'"
proof -
  from assms obtain Z \<alpha> where
  "(\<exists>\<beta>. w\<^sub>2 = map Input w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (q, \<beta>) \<in> end_check_eps_fun (N p) Z) \<or>
    (\<exists>a \<beta>. map Input w\<^sub>1 = Input a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (q, \<beta>) \<in> end_check_trans_fun (N p) (Input a) Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_end_check] by (fastforce simp: end_check_dpda_def)
  thus ?thesis
    by (induction "N p" Z rule: end_check_eps_fun.induct) auto
qed

lemma end_check_dpda_inputs_in_N:
  assumes "pda.steps end_check_dpda (N p, map Input w\<^sub>1, \<alpha>\<^sub>1) (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = N q'"
using assms proof (induction "(N p, map Input w\<^sub>1, \<alpha>\<^sub>1)" "(q, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p w\<^sub>1 \<alpha>\<^sub>1 rule: pda.steps_induct[OF pda_end_check])
  case (3 \<alpha>\<^sub>1 p' w' \<alpha>')
  from 3(1) obtain p'' where p'_def: "p' = N p''"
    using end_check_dpda_input_in_N by blast
  from 3(1) obtain w'' where w'_def: "w' = map Input w''"
    using pda.step\<^sub>1_rule_ext[OF pda_end_check] by blast
  from p'_def w'_def 3(2,3) show ?case by simp
qed (auto simp: assms)

lemma end_check_dpda_inputs_from_P:
  assumes "pda.steps end_check_dpda (p, map Input w\<^sub>1, \<alpha>\<^sub>1) (P q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>p'. p = P p'"
proof (rule ccontr)
  assume "\<nexists>p'. p = P p'"
  then obtain p' where "p = N p'"
    using st_primed.exhaust[of p] by auto
  with assms show False
    using end_check_dpda_inputs_in_N by blast
qed

lemma end_check_dpda_input_stepn:
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
  assume asm: ?r
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
  qed (simp_all add: asm)
qed

lemma end_check_dpda_P_step\<^sub>1:
  "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.step\<^sub>1 end_check_dpda (P p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (P p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain Z \<alpha> where \<alpha>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and rule: 
        "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) \<or>
            (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
    using step\<^sub>1_rule_ext by auto
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (P p\<^sub>2, \<beta>) \<in> eps_fun end_check_dpda (P p\<^sub>1) Z) \<or>
            (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (P p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (P p\<^sub>1) a Z)"
    using end_check_dpda_eps_P end_check_dpda_trans_P by simp
  with \<alpha>1_def show ?r
    using pda.step\<^sub>1_rule[OF pda_end_check] by simp
next
  assume ?r
  then obtain Z \<alpha> where \<alpha>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>" and rule: 
        "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (P p\<^sub>2, \<beta>) \<in> eps_fun end_check_dpda (P p\<^sub>1) Z) \<or>
            (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (P p\<^sub>2, \<beta>) \<in> trans_fun end_check_dpda (P p\<^sub>1) a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_end_check] by auto
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) \<or>
            (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
    using end_check_dpda_eps_P end_check_dpda_trans_P by simp
  with \<alpha>1_def show ?l
    using step\<^sub>1_rule by simp
qed

lemma end_check_dpda_in_P:
  assumes "pda.step\<^sub>1 end_check_dpda (P p, w\<^sub>1, \<alpha>\<^sub>1) (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
proof - 
  thm pda.step\<^sub>1_rule[OF pda_end_check]
  from assms obtain Z \<alpha> where 
    "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (q, \<beta>) \<in> end_check_eps_fun (P p) Z) \<or>
      (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (q, \<beta>) \<in> end_check_trans_fun (P p) a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_end_check] by (fastforce simp: end_check_dpda_def)
  thus ?thesis
    by (induction "P p" Z rule: end_check_eps_fun.induct) auto
qed

lemma end_check_dpda_ins_P:
  assumes "pda.steps end_check_dpda (P p, w\<^sub>1, \<alpha>\<^sub>1) (q, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
using assms by (induction "(P p, w\<^sub>1, \<alpha>\<^sub>1)" "(q, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p w\<^sub>1 \<alpha>\<^sub>1 rule: pda.steps_induct[OF pda_end_check])
                  (blast intro: assms dest: end_check_dpda_in_P)+

lemma end_check_dpda_marker_in_N:
  assumes "pda.step\<^sub>1 end_check_dpda (N p, [End_marker], \<alpha>\<^sub>1) (q, [], \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
proof -
  from assms obtain Z \<beta> where "(q, \<beta>) \<in> end_check_trans_fun (N p) End_marker Z"
    using pda.step\<^sub>1_rule_ext[OF pda_end_check] by (fastforce simp: end_check_dpda_def)
  thus ?thesis
    by (induction "N p" "End_marker :: 'a input_with_marker" Z rule: end_check_trans_fun.induct) auto
qed

lemma end_check_dpda_marker_ins_N:
  assumes "pda.steps end_check_dpda (N p, [End_marker], \<alpha>\<^sub>1) (q, [], \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
proof -
  thm pda.stepn_reads_input[OF pda_end_check]
  from assms obtain n where stepn: "pda.stepn end_check_dpda n (N p, [End_marker], \<alpha>\<^sub>1) (q, [], \<alpha>\<^sub>2)"
    using pda.stepn_steps[OF pda_end_check] by blast
  then obtain n' where "n = Suc n'"
    using pda.stepn_not_refl_split_first[OF pda_end_check] by blast
  with stepn obtain q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where 
          toq1: "pda.steps end_check_dpda (N p, [End_marker], \<alpha>\<^sub>1) (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)" and
          toq2: "pda.step\<^sub>1 end_check_dpda (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) (q\<^sub>2, [], \<gamma>\<^sub>2)" and 
          toq: "pda.steps end_check_dpda (q\<^sub>2, [], \<gamma>\<^sub>2) (q, [], \<alpha>\<^sub>2)"
    using pda.stepn_reads_input[OF pda_end_check] pda.stepn_steps[OF pda_end_check] by metis
  from toq1 have "pda.steps end_check_dpda (N p, [], \<alpha>\<^sub>1) (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using pda.steps_word_app[OF pda_end_check] by fastforce
  then obtain q\<^sub>1' where "q\<^sub>1 = N q\<^sub>1'"
    using end_check_dpda_inputs_in_N[of p "[]" \<alpha>\<^sub>1 q\<^sub>1 "[]" \<gamma>\<^sub>1] by auto
  with toq2 obtain q\<^sub>2' where "q\<^sub>2 = P q\<^sub>2'"
    using end_check_dpda_marker_in_N by blast
  with toq show ?thesis
    using end_check_dpda_ins_P by simp
qed

lemma end_check_dpda_P_stepn:
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
  assume asm: ?r
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
  qed (simp_all add: asm)
qed

lemma end_check_dpda_marker_stepn:
  "pda.stepn M n (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
    pda.stepn end_check_dpda n (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (P p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l
  then obtain n' where n_def: "n = Suc n'"
    using stepn_not_refl gr0_implies_Suc by blast
  with l obtain k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where k_less: "k \<le> n'" and stepk: "stepn k (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    and step1: "step\<^sub>1 (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) (q\<^sub>2, [], \<gamma>\<^sub>2)" and stepn'k: "stepn (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using stepn_reads_input[of n' p\<^sub>1 End_marker "[]" \<alpha>\<^sub>1 p\<^sub>2 \<alpha>\<^sub>2] by auto
  from stepk have "stepn k (p\<^sub>1, [], \<alpha>\<^sub>1) (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using stepn_word_app[of k p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1 "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  hence "pda.stepn end_check_dpda k (N p\<^sub>1, [], \<alpha>\<^sub>1) (N q\<^sub>1, [], \<gamma>\<^sub>1)"
    using end_check_dpda_input_stepn[where ?w = "[]"] by simp

  hence "pda.stepn end_check_dpda k (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (N q\<^sub>1, [End_marker], \<gamma>\<^sub>1)"
    using pda.stepn_word_app[OF pda_end_check, of k "N p\<^sub>1" "[]" \<alpha>\<^sub>1 "N q\<^sub>1" "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp

  moreover from step1 have "pda.step\<^sub>1 end_check_dpda (N q\<^sub>1, [End_marker], \<gamma>\<^sub>1) (P q\<^sub>2, [], \<gamma>\<^sub>2)"
    using end_check_dpda_marker_step\<^sub>1 by simp

  moreover from stepn'k have "pda.stepn end_check_dpda (n' - k) (P q\<^sub>2, [], \<gamma>\<^sub>2) (P p\<^sub>2, [], \<alpha>\<^sub>2)" 
    using end_check_dpda_P_stepn by simp

  ultimately show ?r 
    using n_def k_less pda.step\<^sub>n[OF pda_end_check] pda.stepn_trans[OF pda_end_check] by fastforce
next
  assume r: ?r
  then obtain n' where n_def: "n = Suc n'"
    using pda.stepn_not_refl[OF pda_end_check] gr0_implies_Suc by blast
  with r obtain k q\<^sub>1 q\<^sub>2 \<gamma>\<^sub>1 \<gamma>\<^sub>2 where k_less: "k \<le> n'" and 
          stepk: "pda.stepn end_check_dpda k (N p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (q\<^sub>1, [End_marker], \<gamma>\<^sub>1)" and
          step1: "pda.step\<^sub>1 end_check_dpda (q\<^sub>1, [End_marker], \<gamma>\<^sub>1) (q\<^sub>2, [], \<gamma>\<^sub>2)" and
          stepn'k: "pda.stepn end_check_dpda (n' - k) (q\<^sub>2, [], \<gamma>\<^sub>2) (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using pda.stepn_reads_input[OF pda_end_check] by blast
  from stepk have stepk_emp: "pda.stepn end_check_dpda k (N p\<^sub>1, [], \<alpha>\<^sub>1) (q\<^sub>1, [], \<gamma>\<^sub>1)"
    using pda.stepn_word_app[OF pda_end_check] by fastforce
  then obtain q\<^sub>1' where q1_def: "q\<^sub>1 = N q\<^sub>1'"
    using pda.stepn_steps[OF pda_end_check] end_check_dpda_inputs_in_N[of p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1 "[]" \<gamma>\<^sub>1] by fastforce
  with stepk_emp have "stepn k (p\<^sub>1, [], \<alpha>\<^sub>1) (q\<^sub>1', [], \<gamma>\<^sub>1)"
    using end_check_dpda_input_stepn[where ?w = "[]"] by simp
  hence *: "stepn k (p\<^sub>1, [End_marker], \<alpha>\<^sub>1) (q\<^sub>1', [End_marker], \<gamma>\<^sub>1)"
    using stepn_word_app[of k p\<^sub>1 "[]" \<alpha>\<^sub>1 q\<^sub>1' "[]" \<gamma>\<^sub>1 "[End_marker]"] by simp
  from stepn'k obtain q\<^sub>2' where q2_def: "q\<^sub>2 = P q\<^sub>2'"
    using pda.stepn_steps[OF pda_end_check] end_check_dpda_inputs_from_P[of q\<^sub>2 "[]" \<gamma>\<^sub>2 p\<^sub>2 "[]" \<alpha>\<^sub>2] by fastforce
  with stepn'k have **: "stepn (n' - k) (q\<^sub>2', [], \<gamma>\<^sub>2) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_P_stepn by simp
  from q1_def q2_def step1 have ***: "step\<^sub>1 (q\<^sub>1', [End_marker], \<gamma>\<^sub>1) (q\<^sub>2', [], \<gamma>\<^sub>2)"
    using end_check_dpda_marker_step\<^sub>1 by simp
  from n_def k_less show ?l 
    using stepn_trans[OF step\<^sub>n[OF * ***] **] by simp
qed

lemma end_check_dpda_stepn:
  "pda.stepn M n (p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) (p\<^sub>2, [], \<alpha>\<^sub>2) \<longleftrightarrow>
     pda.stepn end_check_dpda n (N p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) (P p\<^sub>2, [], \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain k q \<gamma> where k_less: "k \<le> n" and stepk: "pda.stepn M k (p\<^sub>1, map Input w, \<alpha>\<^sub>1) (q, [], \<gamma>)" 
                            and stepnk: "pda.stepn M (n-k) (q, [End_marker], \<gamma>) (p\<^sub>2, [], \<alpha>\<^sub>2)"
    using split_word by blast
  from stepk have "pda.stepn end_check_dpda k (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) (N q, [], \<gamma>)"
    using end_check_dpda_input_stepn by simp

  hence "pda.stepn end_check_dpda k (N p\<^sub>1, word_with_end w, \<alpha>\<^sub>1) (N q, [End_marker], \<gamma>)"
    using pda.stepn_word_app[OF pda_end_check, of k "N p\<^sub>1" "map Input w" "\<alpha>\<^sub>1" "N q" "[]" \<gamma> "[End_marker]"] by simp 

  moreover from stepnk have "pda.stepn end_check_dpda (n-k) (N q, [End_marker], \<gamma>) (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using end_check_dpda_marker_stepn by simp

  ultimately show ?r
    using k_less pda.stepn_trans[OF pda_end_check] by fastforce 
next
  assume ?r
  then obtain k q \<gamma> where k_less: "k \<le> n" and stepk: "pda.stepn end_check_dpda k (N p\<^sub>1, map Input w, \<alpha>\<^sub>1) (q, [], \<gamma>)"
                      and stepnk: "pda.stepn end_check_dpda (n-k) (q, [End_marker], \<gamma>) (P p\<^sub>2, [], \<alpha>\<^sub>2)"
    using pda.split_word[OF pda_end_check] by blast
  from stepk obtain q' where q_def: "q = N q'" 
    using pda.stepn_steps[OF pda_end_check] end_check_dpda_inputs_in_N by blast
  with stepk have "pda.stepn M k (p\<^sub>1, map Input w, \<alpha>\<^sub>1) (q', [], \<gamma>)"
    using end_check_dpda_input_stepn by simp

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
    unfolding end_check_dpda_def end_check_final_states_def by simp
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
unfolding final_accept_det_def dpda.final_accept_det_def[OF dpda_end_check] using accepted_end_check by blast

lemma finished_end_check_dpda:
  assumes "pda.steps end_check_dpda (p, word_with_end w\<^sub>1, \<alpha>\<^sub>1) (q, [], \<alpha>\<^sub>2)"
  shows "\<exists>q'. q = P q'"
proof (cases p)
  case (N p')
  with assms obtain q' \<gamma>' where toq': "pda.steps end_check_dpda (N p', map Input w\<^sub>1, \<alpha>\<^sub>1) (q', [], \<gamma>')" and
                                  toq: "pda.steps end_check_dpda (q', [End_marker], \<gamma>') (q, [], \<alpha>\<^sub>2)"
    using pda.stepn_steps[OF pda_end_check] pda.split_word[OF pda_end_check] by metis
  from toq' obtain q'' where "q' = N q''"
    using end_check_dpda_inputs_in_N by blast
  with toq show ?thesis
    using end_check_dpda_marker_ins_N by simp
next
  case (P p')
  with assms show ?thesis
    using end_check_dpda_ins_P by simp
qed

end
end