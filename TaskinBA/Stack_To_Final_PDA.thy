theory Stack_To_Final_PDA
  imports PDA 
begin

datatype 'q st_extended = Old_st 'q | New_init | New_final 
datatype 's sym_extended = Old_sym 's | New_sym

instance st_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = Old_st q} \<union> {New_init, New_final}"
    by auto (metis st_extended.exhaust)
  show "finite (UNIV :: 'a st_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

instance sym_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>s. t = Old_sym s} \<union> {New_sym}"
    by auto (metis sym_extended.exhaust)
  show "finite (UNIV :: 'a sym_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

context pda begin

fun stack_to_final_trans_fun :: "'q st_extended \<Rightarrow> 'a \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "stack_to_final_trans_fun (Old_st q) a (Old_sym Z) = (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (trans_fun M q a Z)"
| "stack_to_final_trans_fun _ _ _ = {}"

fun stack_to_final_eps_fun :: "'q st_extended \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "stack_to_final_eps_fun (Old_st q) (Old_sym Z) = (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (eps_fun M q Z)"
| "stack_to_final_eps_fun New_init New_sym = {(Old_st (init_state M), [Old_sym (init_symbol M), New_sym])}"
| "stack_to_final_eps_fun (Old_st q) New_sym = {(New_final, [])}"
| "stack_to_final_eps_fun _ _ = {}"

definition stack_to_final_pda :: "('q st_extended, 'a, 's sym_extended) pda" where
  "stack_to_final_pda \<equiv> \<lparr> init_state = New_init, init_symbol = New_sym, final_states = {New_final}, 
                    trans_fun = stack_to_final_trans_fun, eps_fun = stack_to_final_eps_fun \<rparr>"

lemma pda_stack_to_final: "pda stack_to_final_pda"
proof (standard, goal_cases)
  case (1 p x z)
  have "finite (stack_to_final_trans_fun p x z)"
    by (induction p x z rule: stack_to_final_trans_fun.induct) (auto simp: finite_trans)
  then show ?case
    by (simp add: stack_to_final_pda_def)
next
  case (2 p z)
  have "finite (stack_to_final_eps_fun p z)"
    by (induction p z rule: stack_to_final_eps_fun.induct) (auto simp: finite_eps)
  then show ?case
    by (simp add: stack_to_final_pda_def)
qed

lemma stack_to_final_pda_trans:
  "(p, \<beta>) \<in> trans_fun M q a Z \<longleftrightarrow> 
          (Old_st p, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st q) a (Old_sym Z)"
  apply (rule iffI)
   apply (auto simp: stack_to_final_pda_def)
  apply (metis list.inj_map_strong sym_extended.inject)
  done

lemma stack_to_final_pda_eps:
  "(p, \<beta>) \<in> eps_fun M q Z \<longleftrightarrow> (Old_st p, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st q) (Old_sym Z)"
  apply (rule iffI)
   apply (auto simp: stack_to_final_pda_def)
  apply (metis list.inj_map_strong sym_extended.inject)
  done

lemma stack_to_final_pda_step: 
  "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
      pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, map Old_sym \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain Z \<alpha> where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z # \<alpha>" and rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
    using step\<^sub>1_rule_ext by auto
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta> @ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta> @ map Old_sym \<alpha> \<and> 
                 (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z))"
    using stack_to_final_pda_trans stack_to_final_pda_eps by auto
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, \<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z))" 
    by blast
  with \<alpha>\<^sub>1_def show ?r
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by simp
next
  assume ?r
  then obtain Z \<alpha> where map_\<alpha>\<^sub>1_def: "map Old_sym \<alpha>\<^sub>1 = Old_sym Z # map Old_sym \<alpha>" and 
     rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
         \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta>@ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2,\<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z))"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by auto
  from map_\<alpha>\<^sub>1_def have \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z # \<alpha>"
    by (metis list.inj_map_strong list.simps(9) sym_extended.inject)
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta>@ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z)) 
     \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta>@ map Old_sym \<alpha> \<and> (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z))"
    using append_eq_map_conv[where ?f = Old_sym] by metis
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z)
    \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
    using stack_to_final_pda_trans stack_to_final_pda_eps by (metis list.inj_map_strong sym_extended.inject map_append)
  with \<alpha>\<^sub>1_def show ?l
    using step\<^sub>1_rule by simp
qed

abbreviation \<alpha>_with_new :: "'s list \<Rightarrow> 's sym_extended list" where
  "\<alpha>_with_new \<alpha> \<equiv> map Old_sym \<alpha> @ [New_sym]"

lemma stack_to_final_pda_step\<^sub>1_drop:
  assumes "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) 
                                            (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
    shows "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms obtain Z \<alpha> where \<alpha>\<^sub>1_with_new_def: "\<alpha>_with_new \<alpha>\<^sub>1 = Z # \<alpha>" and
    rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>_with_new \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (Old_st p\<^sub>2, \<beta>) \<in> stack_to_final_eps_fun (Old_st p\<^sub>1) Z) 
         \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>_with_new \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (Old_st p\<^sub>2,\<beta>) \<in> stack_to_final_trans_fun (Old_st p\<^sub>1) a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)
  from rule have "Z \<noteq> New_sym"
    by (induction "Old_st p\<^sub>1" Z rule: stack_to_final_eps_fun.induct) auto
  with \<alpha>\<^sub>1_with_new_def have "map Old_sym \<alpha>\<^sub>1 \<noteq> []" by auto
  with assms have "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, map Old_sym \<alpha>\<^sub>1) 
                                                (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2)"
    using pda.step\<^sub>1_stack_drop[OF pda_stack_to_final] by blast
  thus ?thesis
    using stack_to_final_pda_step by simp
qed

lemma stack_to_final_pda_from_old:
  assumes "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "(\<exists>p\<^sub>2'. p\<^sub>2 = Old_st p\<^sub>2') \<or> p\<^sub>2 = New_final"
proof -
  from assms obtain Z \<alpha> where 
            "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2, \<beta>) \<in> stack_to_final_eps_fun (Old_st p\<^sub>1) Z) 
              \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha> \<and> (p\<^sub>2,\<beta>) \<in> stack_to_final_trans_fun (Old_st p\<^sub>1) a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)+
  thus ?thesis 
    by (induction "Old_st p\<^sub>1" Z rule: stack_to_final_eps_fun.induct) auto
qed

lemma stack_to_final_pda_no_step_final:
  "\<not>pda.step\<^sub>1 stack_to_final_pda (New_final, w\<^sub>1, \<alpha>\<^sub>1) (p, w\<^sub>2, \<alpha>\<^sub>2)"
  apply (cases \<alpha>\<^sub>1)
   apply (simp add: pda.step\<^sub>1_empty_stack[OF pda_stack_to_final])
  apply (use pda.step\<^sub>1_rule[OF pda_stack_to_final] stack_to_final_pda_def in simp)
  done

lemma stack_to_final_pda_from_oldn:
  assumes "pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. p\<^sub>2 = Old_st q' \<or> p\<^sub>2 = New_final"
by (induction "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: pda.steps_induct2[OF pda_stack_to_final])
  (use assms stack_to_final_pda_from_old stack_to_final_pda_no_step_final in blast)+

lemma stack_to_final_pda_to_old:
  assumes "pda.step\<^sub>1 stack_to_final_pda (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "(\<exists>q'. p\<^sub>1 = Old_st q') \<or> p\<^sub>1 = New_init"
using assms stack_to_final_pda_no_step_final by (metis st_extended.exhaust)

lemma stack_to_final_pda_bottom_elem:
  assumes "pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)
                                         (Old_st p\<^sub>2, w\<^sub>2, \<gamma>)"
  shows "\<exists>\<alpha>. \<gamma> = \<alpha>_with_new \<alpha>"
using assms proof (induction "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)" "(Old_st p\<^sub>2, w\<^sub>2, \<gamma>)" arbitrary: p\<^sub>2 w\<^sub>2 \<gamma>
                          rule: pda.steps_induct2[OF pda_stack_to_final])
  case (3 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 w\<^sub>3 \<alpha>\<^sub>3 p\<^sub>3)
  obtain p\<^sub>2' where p\<^sub>2_def: "p\<^sub>2 = Old_st p\<^sub>2'"
    using stack_to_final_pda_from_oldn[OF 3(1)] stack_to_final_pda_to_old[OF 3(2)] by blast
  with 3(1,3) have \<alpha>\<^sub>2_def: "\<exists>\<alpha>. \<alpha>\<^sub>2 = \<alpha>_with_new \<alpha>" by simp
  from 3(2)[unfolded p\<^sub>2_def] obtain Z \<alpha> where \<alpha>\<^sub>2_split: "\<alpha>\<^sub>2 = Z # \<alpha>" and rule:
    "(\<exists>\<beta>. w\<^sub>3 = w\<^sub>2 \<and> \<alpha>\<^sub>3 = \<beta> @ \<alpha> \<and> (Old_st p\<^sub>3, \<beta>) \<in> stack_to_final_eps_fun (Old_st p\<^sub>2') Z) 
     \<or> (\<exists>a \<beta>. w\<^sub>2 = a # w\<^sub>3 \<and> \<alpha>\<^sub>3 = \<beta> @ \<alpha> \<and> (Old_st p\<^sub>3, \<beta>) \<in> stack_to_final_trans_fun (Old_st p\<^sub>2') a Z)"
      using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)
    from rule have "\<exists>Z'. Z = Old_sym Z'"
      by (induction "Old_st p\<^sub>2'" Z rule: stack_to_final_eps_fun.induct) auto
    with \<alpha>\<^sub>2_def \<alpha>\<^sub>2_split have "\<exists>\<gamma>. \<alpha> = \<alpha>_with_new \<gamma>"
      by (metis hd_append list.sel(1,3) map_tl sym_extended.simps(3) tl_append_if)
    with rule show ?case
      by (induction "Old_st p\<^sub>2'" Z rule: stack_to_final_eps_fun.induct, auto) (metis map_append)+
qed (rule assms, blast)

lemma stack_to_final_pda_stepn:
  "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> 
            pda.stepn stack_to_final_pda n (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
  proof (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
    from step\<^sub>n(3) have "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2) (Old_st p\<^sub>3, w\<^sub>3, map Old_sym \<alpha>\<^sub>3)"
      using stack_to_final_pda_step by simp
    hence "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2) (Old_st p\<^sub>3, w\<^sub>3, \<alpha>_with_new \<alpha>\<^sub>3)"
      using pda.step\<^sub>1_stack_app[OF pda_stack_to_final] by simp
    with step\<^sub>n(2) show ?case
      by (simp add: pda.step\<^sub>n[OF pda_stack_to_final])
  qed (simp add: pda.refl\<^sub>n[OF pda_stack_to_final])
next
  assume r: ?r thus ?l
  proof (induction n "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)" "(Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)" 
                 arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: pda.stepn.induct[OF pda_stack_to_final])
    case (3 n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 w\<^sub>3 p\<^sub>3 \<alpha>\<^sub>3)
    from 3(1) have steps_3_1: "pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      using pda.stepn_steps[OF pda_stack_to_final] by blast
    obtain p\<^sub>2' where p\<^sub>2_def: "p\<^sub>2 = Old_st p\<^sub>2'"
      using stack_to_final_pda_from_oldn[OF steps_3_1] stack_to_final_pda_to_old[OF 3(3)] by blast
    with steps_3_1 obtain \<gamma> where \<alpha>\<^sub>2_def: "\<alpha>\<^sub>2 = map Old_sym \<gamma> @ [New_sym]"
      using stack_to_final_pda_bottom_elem by blast

    with p\<^sub>2_def 3(1,2) have "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2', w\<^sub>2, \<gamma>)" by simp

    moreover from p\<^sub>2_def \<alpha>\<^sub>2_def 3(3) have "pda.step\<^sub>1 M (p\<^sub>2', w\<^sub>2, \<gamma>) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
      using stack_to_final_pda_step\<^sub>1_drop by simp

    ultimately show ?case by simp
  qed (rule r, metis refl\<^sub>n list.inj_map_strong sym_extended.inject)
qed

lemma stack_to_final_pda_steps:
  "pda.steps M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> 
            pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
using stack_to_final_pda_stepn pda.stepn_steps[OF pda_stack_to_final] stepn_steps by simp

lemma stack_to_final_pda_first_step:
  assumes "pda.step\<^sub>1 stack_to_final_pda (New_init, w\<^sub>1, [New_sym]) (p\<^sub>2, w\<^sub>2, \<alpha>)"
  shows "p\<^sub>2 = Old_st (init_state M) \<and> w\<^sub>2 = w\<^sub>1 \<and> \<alpha> = [Old_sym (init_symbol M), New_sym]"
using assms pda.step\<^sub>1_rule[OF pda_stack_to_final] by (simp add: stack_to_final_pda_def)

lemma stack_to_final_pda_last_step:
  assumes "pda.step\<^sub>1 stack_to_final_pda (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (New_final, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>q. p\<^sub>1 = Old_st q \<and> w\<^sub>1 = w\<^sub>2 \<and> \<alpha>\<^sub>1 = New_sym # \<alpha>\<^sub>2"
proof -
  from assms obtain Z \<alpha> where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z # \<alpha>" and rule: 
        "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (New_final, \<beta>) \<in> stack_to_final_eps_fun p\<^sub>1 Z) 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha> \<and> (New_final, \<beta>) \<in> stack_to_final_trans_fun p\<^sub>1 a Z)"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)
  from rule have "w\<^sub>2 = w\<^sub>1" and "\<alpha>\<^sub>2 = \<alpha>" and "\<exists>q. p\<^sub>1 = Old_st q \<and> Z = New_sym"
    by (induction p\<^sub>1 Z rule: stack_to_final_eps_fun.induct) auto
  with \<alpha>\<^sub>1_def show ?thesis by simp
qed

lemma stack_to_final_pda_split_path:
  assumes "pda.stepn stack_to_final_pda (Suc (Suc n)) (New_init, w\<^sub>1, [New_sym]) (New_final, w\<^sub>2, \<gamma>)"
    shows "\<exists>q. pda.step\<^sub>1 stack_to_final_pda (New_init, w\<^sub>1, [New_sym]) 
                                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym]) \<and>
           pda.stepn stack_to_final_pda n (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                                               (Old_st q, w\<^sub>2, [New_sym]) \<and>
           pda.step\<^sub>1 stack_to_final_pda (Old_st q, w\<^sub>2, [New_sym]) 
                                               (New_final, w\<^sub>2, \<gamma>) \<and> \<gamma> = []"
proof -
  from assms have fstep: "pda.step\<^sub>1 stack_to_final_pda (New_init, w\<^sub>1, [New_sym]) 
                                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])"
                 and stepn: "pda.stepn stack_to_final_pda (Suc n) 
                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                              (New_final, w\<^sub>2, \<gamma>)"
    using pda.stepn_split_first[OF pda_stack_to_final] stack_to_final_pda_first_step by blast+
  from stepn obtain q where lstep: "pda.step\<^sub>1 stack_to_final_pda (Old_st q, w\<^sub>2, New_sym # \<gamma>) (New_final, w\<^sub>2, \<gamma>)"
                        and stepn': "pda.stepn stack_to_final_pda n 
                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                              (Old_st q, w\<^sub>2, New_sym # \<gamma>)"
    using pda.stepn_split_last[OF pda_stack_to_final] stack_to_final_pda_last_step by blast
  from stepn' have "\<exists>\<alpha>. New_sym # \<gamma> = \<alpha>_with_new \<alpha>"
    using stack_to_final_pda_bottom_elem pda.stepn_steps[OF pda_stack_to_final]
    by (metis (no_types, opaque_lifting) Cons_eq_appendI append_Nil list.map_disc_iff list.simps(9))
  hence "\<gamma> = []"
    by (metis Nil_is_map_conv hd_append2 hd_map list.sel(1,3) sym_extended.simps(3) tl_append_if)
  with fstep lstep stepn' show ?thesis by auto
qed

lemma stack_to_final_pda_path_length:
  assumes "pda.stepn stack_to_final_pda n (New_init, w\<^sub>1, [New_sym]) (New_final, w\<^sub>2, \<gamma>)"
  shows "\<exists>n'. n = Suc (Suc (Suc n'))"
proof -
  from assms obtain n' where n_def: "n = Suc n'" and fstep: "pda.step\<^sub>1 stack_to_final_pda (New_init, w\<^sub>1, [New_sym]) 
                                                          (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])"
                                                  and stepn: "pda.stepn stack_to_final_pda n' 
                                                          (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                                                              (New_final, w\<^sub>2, \<gamma>)"
    using pda.stepn_not_refl_split_first[OF pda_stack_to_final] stack_to_final_pda_first_step by blast
  from stepn obtain n'' where n'_def: "n' = Suc n''"
    using pda.stepn_not_refl_split_last[OF pda_stack_to_final] by blast
  with n_def assms have "\<exists>q. pda.stepn stack_to_final_pda n'' 
                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym]) (Old_st q, w\<^sub>2, [New_sym])"
    using stack_to_final_pda_split_path by blast
  then obtain n''' where "n'' = Suc n'''"
    using pda.stepn_not_refl_split_last[OF pda_stack_to_final] by blast
  with n_def n'_def show ?thesis by simp
qed

lemma accepted_stack_to_final:  
"(\<exists>q. pda.steps M (init_state M, w, [init_symbol M]) (q, [], [])) \<longleftrightarrow> (\<exists>q \<gamma>. q \<in> final_states stack_to_final_pda \<and> 
  pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) (q, [], \<gamma>))" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain q where "pda.steps M (init_state M, w, [init_symbol M]) (q, [], [])" by blast
  hence "pda.steps stack_to_final_pda (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym]) (Old_st q, [], [New_sym])"
    using stack_to_final_pda_steps by simp

  moreover have "pda.step\<^sub>1 stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) 
                                         (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym])"
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by (simp add: stack_to_final_pda_def)

  moreover have "pda.step\<^sub>1 stack_to_final_pda (Old_st q, [], [New_sym]) (New_final, [], [])"
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by (simp add: stack_to_final_pda_def)

  ultimately have a1:
    "pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda ]) (New_final, [], [])"
    using pda.step\<^sub>1_steps[OF pda_stack_to_final] pda.steps_trans[OF pda_stack_to_final] by metis

  moreover have "New_final \<in> final_states stack_to_final_pda"
    by (simp add: stack_to_final_pda_def)

  ultimately show ?r by blast
next
  assume ?r
  then obtain q \<gamma> where q_final: "q \<in> final_states stack_to_final_pda" and
                steps: "pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) (q, [], \<gamma>)" by blast
  from q_final have q_def: "q = New_final"
    by (simp add: stack_to_final_pda_def)
  with steps obtain n where stepn: "pda.stepn stack_to_final_pda n (New_init, w, [New_sym]) (New_final, [], \<gamma>)"
    using pda.stepn_steps[OF pda_stack_to_final] by (fastforce simp add: stack_to_final_pda_def)
  then obtain n' where "n = Suc (Suc n')"
    using stack_to_final_pda_path_length by blast
  with stepn obtain p where "pda.stepn stack_to_final_pda n' (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym])
                                                                (Old_st p, [], [New_sym])"
    using stack_to_final_pda_split_path by blast
  hence "pda.stepn M n' (init_state M, w, [(init_symbol M)]) (p, [], [])"
    using stack_to_final_pda_stepn by simp
  thus ?l
    using stepn_steps by blast
qed

lemma stack_to_final: "pda.stack_accept M = pda.final_accept stack_to_final_pda"
  unfolding stack_accept_def pda.final_accept_def[OF pda_stack_to_final] using accepted_stack_to_final by blast

end
end