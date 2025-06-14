theory Stack_To_Final_PDA
  imports PDA 
begin

datatype 'q st_extended = Old_st 'q | New_init | New_final 
datatype 's sym_extended = Old_sym 's | New_sym

context pda begin

definition "stack_final_states \<equiv> Old_st ` states M \<union> {New_init, New_final}"

fun stack_to_final_trans_fun :: "'q st_extended \<Rightarrow> 'a \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "stack_to_final_trans_fun (Old_st q) a (Old_sym Z) = (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (trans_fun M q a Z)"
| "stack_to_final_trans_fun _ _ _ = {}"

fun stack_to_final_eps_fun :: "'q st_extended \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "stack_to_final_eps_fun (Old_st q) (Old_sym Z) = (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (eps_fun M q Z)"
| "stack_to_final_eps_fun New_init New_sym = {(Old_st (init_state M), [Old_sym (init_symbol M), New_sym])}"
| "stack_to_final_eps_fun (Old_st q) New_sym = {(New_final, [])}"
| "stack_to_final_eps_fun _ _ = {}"

definition stack_to_final_pda :: "('q st_extended, 'a, 's sym_extended) pda" where
  "stack_to_final_pda \<equiv> \<lparr> states = stack_final_states, init_state = New_init, init_symbol = New_sym, final_states = {New_final}, 
                    trans_fun = stack_to_final_trans_fun, eps_fun = stack_to_final_eps_fun \<rparr>"

lemma pda_stack_to_final: "pda stack_to_final_pda"
proof (standard, goal_cases)
  case 1
  then show ?case
    unfolding stack_to_final_pda_def stack_final_states_def by simp
next
  case 2
  then show ?case
    unfolding stack_to_final_pda_def stack_final_states_def by simp
next
  case (3 p x z)
  from 3[unfolded stack_to_final_pda_def stack_final_states_def] 
  have "fst ` stack_to_final_trans_fun p x z \<subseteq> Old_st ` states M \<union> {New_init, New_final}"
    using trans by (induction p x z rule: stack_to_final_trans_fun.induct) fastforce+
  then show ?case
    unfolding stack_to_final_pda_def stack_final_states_def by simp
next
  case (4 p z)
  from 4[unfolded stack_to_final_pda_def stack_final_states_def] 
  have "fst ` stack_to_final_eps_fun p z \<subseteq> Old_st ` states M \<union> {New_init, New_final}"
    using eps init by (induction p z rule: stack_to_final_eps_fun.induct) fastforce+ 
  then show ?case
    unfolding stack_to_final_pda_def stack_final_states_def by simp
next
  case 5
  then show ?case
    unfolding stack_to_final_pda_def stack_final_states_def using finite_states by simp
next
  case (6 p x z)
  have "finite (stack_to_final_trans_fun p x z)"
    by (induction p x z rule: stack_to_final_trans_fun.induct) (auto simp: finite_trans)
  then show ?case
    unfolding stack_to_final_pda_def by simp
next
  case (7 p z)
  have "finite (stack_to_final_eps_fun p z)"
    by (induction p z rule: stack_to_final_eps_fun.induct) (auto simp: finite_eps)
  then show ?case
    unfolding stack_to_final_pda_def by simp
qed

lemma stack_to_final_pda_trans:
  "(p, \<beta>) \<in> trans_fun M q a Z \<longleftrightarrow> 
          (Old_st p, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st q) a (Old_sym Z)"
proof
  assume "(p, \<beta>) \<in> trans_fun M q a Z"
  thus "(Old_st p, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st q) a (Old_sym Z)"
    unfolding stack_to_final_pda_def by auto
next
  assume "(Old_st p, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st q) a (Old_sym Z)"
  hence "(Old_st p, map Old_sym \<beta>) \<in> (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (trans_fun M q a Z)"
    unfolding stack_to_final_pda_def by simp
  then obtain p' \<alpha>' where old_eq: "(Old_st p, map Old_sym \<beta>) = (Old_st p', map Old_sym \<alpha>')" and elem: "(p', \<alpha>') \<in> (trans_fun M q a Z)" by auto
  from old_eq have p_eq: "p = p'" by simp
  from old_eq have \<beta>_eq: "\<beta> = \<alpha>'"
    by (metis list.inj_map_strong prod.inject sym_extended.inject)
  from p_eq \<beta>_eq elem show "(p, \<beta>) \<in> trans_fun M q a Z" by simp
qed

lemma stack_to_final_pda_eps:
  "(p, \<beta>) \<in> eps_fun M q Z \<longleftrightarrow> (Old_st p, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st q) (Old_sym Z)"
proof
  assume "(p, \<beta>) \<in> eps_fun M q Z"
  thus "(Old_st p, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st q) (Old_sym Z)"
    unfolding stack_to_final_pda_def by auto
next
  assume "(Old_st p, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st q) (Old_sym Z)"
  hence "(Old_st p, map Old_sym \<beta>) \<in> (\<lambda>(p, \<alpha>). (Old_st p, map Old_sym \<alpha>)) ` (eps_fun M q Z)"
    unfolding stack_to_final_pda_def by simp
  then obtain p' \<alpha>' where old_eq: "(Old_st p, map Old_sym \<beta>) = (Old_st p', map Old_sym \<alpha>')" and elem: "(p', \<alpha>') \<in> (eps_fun M q Z)" by auto
  from old_eq have p_eq: "p = p'" by simp
  from old_eq have \<beta>_eq: "\<beta> = \<alpha>'"
    by (metis list.inj_map_strong prod.inject sym_extended.inject)
  from p_eq \<beta>_eq elem show "(p, \<beta>) \<in> eps_fun M q Z" by simp
qed

lemma stack_to_final_pda_step: 
  "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow>
      pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, map Old_sym \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2)"
proof
  assume "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain Z' \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z' # \<alpha>'" and rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step\<^sub>1_rule_ext by auto
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta> @ map Old_sym \<alpha>' \<and> (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z')) 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta> @ map Old_sym \<alpha>' \<and> 
                 (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z'))"
    using stack_to_final_pda_trans stack_to_final_pda_eps by auto
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha>' \<and> (Old_st p\<^sub>2, \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z')) 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha>' \<and> (Old_st p\<^sub>2, \<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z'))" 
    by blast
  with \<alpha>\<^sub>1_def show "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, map Old_sym \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2)"
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by simp
next
  assume "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, map Old_sym \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2)"
  then obtain Z' \<alpha>' where map_\<alpha>\<^sub>1_def: "map Old_sym \<alpha>\<^sub>1 = Old_sym Z' # map Old_sym \<alpha>'" and 
     rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta> @ map Old_sym \<alpha>' \<and> (Old_st p\<^sub>2, \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z')) 
         \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = \<beta>@ map Old_sym \<alpha>' \<and> (Old_st p\<^sub>2,\<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z'))"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by auto
  from map_\<alpha>\<^sub>1_def have \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z' # \<alpha>'"
    by (metis list.inj_map_strong list.simps(9) sym_extended.inject)
  from rule have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta>@ map Old_sym \<alpha>' \<and> (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> eps_fun stack_to_final_pda (Old_st p\<^sub>1) (Old_sym Z')) 
     \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> map Old_sym \<alpha>\<^sub>2 = map Old_sym \<beta>@ map Old_sym \<alpha>' \<and> (Old_st p\<^sub>2, map Old_sym \<beta>) \<in> trans_fun stack_to_final_pda (Old_st p\<^sub>1) a (Old_sym Z'))"
    using append_eq_map_conv[where ?f = Old_sym] by metis
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z')
    \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using stack_to_final_pda_trans stack_to_final_pda_eps by (metis list.inj_map_strong sym_extended.inject map_append)
  with \<alpha>\<^sub>1_def show "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using step\<^sub>1_rule by simp
qed

abbreviation "\<alpha>_with_new \<alpha> \<equiv> map Old_sym \<alpha> @ [New_sym]"

lemma stack_to_final_pda_step\<^sub>1_drop:
  assumes "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) 
                                            (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
    shows "pda.step\<^sub>1 M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms obtain Z' \<alpha>' where map_\<alpha>\<^sub>1_def: "\<alpha>_with_new \<alpha>\<^sub>1 = Z' # \<alpha>'" and
    rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>_with_new \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (Old_st p\<^sub>2, \<beta>) \<in> stack_to_final_eps_fun (Old_st p\<^sub>1) Z') 
         \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>_with_new \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (Old_st p\<^sub>2,\<beta>) \<in> stack_to_final_trans_fun (Old_st p\<^sub>1) a Z')"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)
  from rule have "Z' \<noteq> New_sym"
    by (induction "Old_st p\<^sub>1" Z' rule: stack_to_final_eps_fun.induct) auto
  with map_\<alpha>\<^sub>1_def have "map Old_sym \<alpha>\<^sub>1 \<noteq> []" by auto
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
  from assms obtain Z' \<alpha>' where "\<alpha>\<^sub>1 = Z'#\<alpha>'" and 
            rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> stack_to_final_eps_fun (Old_st p\<^sub>1) Z') 
                      \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> stack_to_final_trans_fun (Old_st p\<^sub>1) a Z')"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)
  from rule show ?thesis by (induction "Old_st p\<^sub>1" Z' rule: stack_to_final_eps_fun.induct) auto
qed

lemma stack_to_final_pda_no_step_final:
  "\<not>pda.step\<^sub>1 stack_to_final_pda (New_final, w\<^sub>1, \<alpha>\<^sub>1) (p, w\<^sub>2, \<alpha>\<^sub>2)"
proof (cases \<alpha>\<^sub>1)
  case Nil
  thus ?thesis
    using pda.step\<^sub>1_empty_stack[OF pda_stack_to_final] by simp
next
  case (Cons Z' \<alpha>')
  have "(\<nexists>\<beta>. (p, \<beta>) \<in> stack_to_final_eps_fun New_final Z') 
                         \<or> (\<nexists>a \<beta>. (p,\<beta>) \<in> stack_to_final_trans_fun New_final a Z')"
    by simp
  with Cons show ?thesis
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by (simp add: stack_to_final_pda_def)
qed

lemma stack_to_final_pda_from_oldn:
  assumes "pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  shows "\<exists>q'. p\<^sub>2 = Old_st q' \<or> p\<^sub>2 = New_final"
using assms proof (induction "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: pda.steps_induct[OF pda_stack_to_final])
  case (3 w\<^sub>1 \<alpha>\<^sub>1 p' w' \<alpha>')
  from 3(1) have case_dist: "(\<exists>p''. p' = Old_st p'') \<or> p' = New_final"
    using stack_to_final_pda_from_old by simp
  then show ?case proof (cases)
    assume "\<exists>p''. p' = Old_st p''"
    then obtain p'' where "p' = Old_st p''" by blast
    with 3(2,3) show ?thesis by blast
  next
    assume "\<not>(\<exists>p''. p' = Old_st p'')"
    with case_dist have "p' = New_final" by simp
    with 3(2) show ?thesis
      using pda.steps_not_refl_split_first[OF pda_stack_to_final]
            stack_to_final_pda_no_step_final by blast
  qed
qed (blast intro: assms)+

lemma stack_to_final_pda_to_old:
  assumes "pda.step\<^sub>1 stack_to_final_pda (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "(\<exists>q'. p\<^sub>1 = Old_st q') \<or> p\<^sub>1 = New_init"
using assms stack_to_final_pda_no_step_final by (metis st_extended.exhaust)

lemma stack_to_final_pda_bottom_elem:
  assumes "pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)
                                         (Old_st p\<^sub>2, w\<^sub>2, \<gamma>)"
  shows "\<exists>\<alpha>. \<gamma> = \<alpha>_with_new \<alpha>"
proof -
  from assms obtain n where stepn: "pda.stepn stack_to_final_pda n (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)
                                                                   (Old_st p\<^sub>2, w\<^sub>2, \<gamma>)"
    using pda.stepn_steps[OF pda_stack_to_final] by blast
  thus ?thesis proof 
   (induction n "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)" "(Old_st p\<^sub>2, w\<^sub>2, \<gamma>)"
       arbitrary: p\<^sub>2 w\<^sub>2 \<gamma> rule: pda.stepn.induct[OF pda_stack_to_final])
    case (3 n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 w\<^sub>3 \<alpha>\<^sub>3 p\<^sub>3)
    from 3(1) have steps: "pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      using pda.stepn_steps[OF pda_stack_to_final] by blast
    obtain p\<^sub>2' where p\<^sub>2_def: "p\<^sub>2 = Old_st p\<^sub>2'"
      using stack_to_final_pda_from_oldn[OF steps] stack_to_final_pda_to_old[OF 3(3)] by blast
    with 3(1,2) have \<alpha>\<^sub>2_def: "\<exists>\<alpha>. \<alpha>\<^sub>2 = \<alpha>_with_new \<alpha>" by simp
    from p\<^sub>2_def 3(3) obtain Z' \<alpha>' where \<alpha>\<^sub>2_split: "\<alpha>\<^sub>2 = Z' # \<alpha>'" and rule:
    "(\<exists>\<beta>. w\<^sub>3 = w\<^sub>2 \<and> \<alpha>\<^sub>3 = \<beta> @ \<alpha>' \<and> (Old_st p\<^sub>3, \<beta>) \<in> stack_to_final_eps_fun (Old_st p\<^sub>2') Z') 
     \<or> (\<exists>a \<beta>. w\<^sub>2 = a # w\<^sub>3 \<and> \<alpha>\<^sub>3 = \<beta> @ \<alpha>' \<and> (Old_st p\<^sub>3, \<beta>) \<in> stack_to_final_trans_fun (Old_st p\<^sub>2') a Z')"
      using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)
    hence "\<exists>Z. Z' = Old_sym Z"
      by (induction "Old_st p\<^sub>2'" Z' rule: stack_to_final_eps_fun.induct) auto
    with \<alpha>\<^sub>2_def \<alpha>\<^sub>2_split have "\<exists>\<gamma>. \<alpha>' = \<alpha>_with_new \<gamma>"
      by (metis hd_append list.sel(1,3) map_tl sym_extended.simps(3) tl_append_if)
    with rule show ?case
      by (induction "Old_st p\<^sub>2'" Z' rule: stack_to_final_eps_fun.induct, auto) (metis map_append)+
  qed (auto simp: stepn)
qed

lemma stack_to_final_pda_stepn:
  "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> 
            pda.stepn stack_to_final_pda n (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
proof
  assume asm: "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  thus "pda.stepn stack_to_final_pda n (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
  proof (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case refl\<^sub>n
    then show ?case
      by (simp add: pda.refl\<^sub>n[OF pda_stack_to_final])
  next
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
    from step\<^sub>n(3) have "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>2, w\<^sub>2, map Old_sym \<alpha>\<^sub>2) (Old_st p\<^sub>3, w\<^sub>3, map Old_sym \<alpha>\<^sub>3)"
      using stack_to_final_pda_step by simp
    hence "pda.step\<^sub>1 stack_to_final_pda (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2) (Old_st p\<^sub>3, w\<^sub>3, \<alpha>_with_new \<alpha>\<^sub>3)"
      using pda.step\<^sub>1_stack_app[OF pda_stack_to_final] by simp
    with step\<^sub>n(2) show ?case
      by (simp add: pda.step\<^sub>n[OF pda_stack_to_final])
  qed
next
  assume asm: "pda.stepn stack_to_final_pda n (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
  thus "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  proof (induction n "(Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1)" "(Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)" 
                 arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: pda.stepn.induct[OF pda_stack_to_final])
    case 2
    from 2(1) have "\<alpha>\<^sub>1 = \<alpha>\<^sub>2"
      by (metis list.inj_map_strong sym_extended.inject)
    thus ?case by simp
  next
    case (3 n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 w\<^sub>3 p\<^sub>3 \<alpha>\<^sub>3)
    from 3(1) have steps: "pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      using pda.stepn_steps[OF pda_stack_to_final] by blast
    obtain p\<^sub>2' where p\<^sub>2_def: "p\<^sub>2 = Old_st p\<^sub>2'"
      using stack_to_final_pda_from_oldn[OF steps] stack_to_final_pda_to_old[OF 3(3)] by blast
    with steps obtain \<gamma> where \<alpha>\<^sub>2_def: "\<alpha>\<^sub>2 = map Old_sym \<gamma> @ [New_sym]"
      using stack_to_final_pda_bottom_elem by blast
    with p\<^sub>2_def 3(1,2) have *: "pda.stepn M n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2', w\<^sub>2, \<gamma>)" by simp
    from p\<^sub>2_def \<alpha>\<^sub>2_def 3(3) have **: "pda.step\<^sub>1 M (p\<^sub>2', w\<^sub>2, \<gamma>) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
      using stack_to_final_pda_step\<^sub>1_drop by simp
    from * ** show ?case by simp
  qed (simp add: asm)
qed

lemma stack_to_final_pda_steps:
  "pda.steps M (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> 
            pda.steps stack_to_final_pda (Old_st p\<^sub>1, w\<^sub>1, \<alpha>_with_new \<alpha>\<^sub>1) (Old_st p\<^sub>2, w\<^sub>2, \<alpha>_with_new \<alpha>\<^sub>2)"
  using stack_to_final_pda_stepn pda.stepn_steps[OF pda_stack_to_final] stepn_steps by simp

lemma stack_to_final_pda_first_step:
  assumes "pda.step\<^sub>1 stack_to_final_pda (New_init, w\<^sub>1, [New_sym]) (p\<^sub>2, w\<^sub>2, \<alpha>)"
  shows "p\<^sub>2 = Old_st (init_state M) \<and> w\<^sub>2 = w\<^sub>1 \<and> \<alpha> = [Old_sym (init_symbol M), New_sym]"
proof -
  from assms have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha> = \<beta> \<and> (p\<^sub>2, \<beta>) \<in> stack_to_final_eps_fun New_init New_sym) 
                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha> = \<beta> \<and> (p\<^sub>2, \<beta>) \<in> stack_to_final_trans_fun New_init a New_sym)"
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by (simp add: stack_to_final_pda_def)
  thus ?thesis by simp
qed

lemma stack_to_final_pda_last_step:
  assumes "pda.step\<^sub>1 stack_to_final_pda (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (New_final, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>q. p\<^sub>1 = Old_st q \<and> w\<^sub>1 = w\<^sub>2 \<and> \<alpha>\<^sub>1 = New_sym # \<alpha>\<^sub>2"
proof -
  from assms obtain Z' \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z' # \<alpha>'" and rule: 
        "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha>' \<and> (New_final, \<beta>) \<in> stack_to_final_eps_fun p\<^sub>1 Z') 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha>' \<and> (New_final, \<beta>) \<in> stack_to_final_trans_fun p\<^sub>1 a Z')"
    using pda.step\<^sub>1_rule_ext[OF pda_stack_to_final] by (auto simp: stack_to_final_pda_def)
  from rule have w_eq: "w\<^sub>2 = w\<^sub>1" and \<alpha>_eq: "\<alpha>\<^sub>2 = \<alpha>'" and elem: "\<exists>q. p\<^sub>1 = Old_st q \<and> Z' = New_sym"
    by (induction p\<^sub>1 Z' rule: stack_to_final_eps_fun.induct) auto
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
  from stepn' have steps': "pda.steps stack_to_final_pda 
                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                              (Old_st q, w\<^sub>2, New_sym # \<gamma>)"
    using pda.stepn_steps[OF pda_stack_to_final] by blast
  from steps' have "\<exists>\<alpha>. New_sym # \<gamma> = \<alpha>_with_new \<alpha>"
    using stack_to_final_pda_bottom_elem
    by (metis (no_types, opaque_lifting) Cons_eq_appendI append_Nil list.map_disc_iff list.simps(9))
  hence "\<gamma> = []"
    by (metis Nil_is_map_conv hd_append2 hd_map list.sel(1,3) sym_extended.simps(3) tl_append_if)
  with fstep lstep stepn' show ?thesis by auto
qed

lemma stack_to_final_pda_path_length:
  assumes "pda.stepn stack_to_final_pda n (New_init, w\<^sub>1, [New_sym]) (New_final, w\<^sub>2, \<gamma>)"
    shows "n > 2"
proof -
  from assms obtain n' where n_def: "n = Suc n'"
    using pda.stepn_not_refl[OF pda_stack_to_final] gr0_implies_Suc by blast
  with assms have fstep: "pda.step\<^sub>1 stack_to_final_pda (New_init, w\<^sub>1, [New_sym]) 
                        (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])"
                 and stepn: "pda.stepn stack_to_final_pda n' 
                         (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym])
                         (New_final, w\<^sub>2, \<gamma>)"
    using pda.stepn_split_first[OF pda_stack_to_final] stack_to_final_pda_first_step by blast+
  from stepn obtain n'' where n'_def: "n' = Suc n''"
    using pda.stepn_not_refl[OF pda_stack_to_final] gr0_implies_Suc by blast
  with n_def assms have "\<exists>q. pda.stepn stack_to_final_pda n'' 
                              (Old_st (init_state M), w\<^sub>1, [Old_sym (init_symbol M), New_sym]) (Old_st q, w\<^sub>2, [New_sym])"
    using stack_to_final_pda_split_path by blast
  then obtain n''' where "n'' = Suc n'''"
    using pda.stepn_not_refl[OF pda_stack_to_final] gr0_implies_Suc by blast
  with n_def n'_def show ?thesis by simp
qed

lemma accepted_stack_to_final:  
"(\<exists>q. pda.steps M (init_state M, w, [init_symbol M]) (q, [], [])) \<longleftrightarrow> (\<exists>q \<gamma>. q \<in> final_states stack_to_final_pda \<and> 
  pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) (q, [], \<gamma>))"
proof
  assume "\<exists>q. pda.steps M (init_state M, w, [init_symbol M]) (q, [], [])"
  then obtain q where "pda.steps M (init_state M, w, [init_symbol M]) (q, [], [])" by blast
  hence *: "pda.steps stack_to_final_pda (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym]) (Old_st q, [], [New_sym])"
    using stack_to_final_pda_steps by simp
  have **: "pda.step\<^sub>1 stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) 
                                         (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym])"
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by (simp add: stack_to_final_pda_def)
  have ***: "pda.step\<^sub>1 stack_to_final_pda (Old_st q, [], [New_sym]) (New_final, [], [])"
    using pda.step\<^sub>1_rule[OF pda_stack_to_final] by (simp add: stack_to_final_pda_def)
  from * ** *** have a1:
    "pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda ]) (New_final, [], [])"
    using pda.step\<^sub>1_stepn_one[OF pda_stack_to_final] pda.stepn_steps[OF pda_stack_to_final]
          pda.steps_trans[OF pda_stack_to_final] by metis
  have a2: "New_final \<in> final_states stack_to_final_pda"
    by (simp add: stack_to_final_pda_def)
  from a1 a2 show "\<exists>q \<gamma>. q \<in> final_states stack_to_final_pda \<and>
                    pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) (q, [], \<gamma>)" by blast
next
  assume "\<exists>q \<gamma>. q \<in> final_states stack_to_final_pda \<and>
          pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) (q, [], \<gamma>)"
  then obtain q \<gamma> where q_final: "q \<in> final_states stack_to_final_pda" and
                "pda.steps stack_to_final_pda (init_state stack_to_final_pda, w, [init_symbol stack_to_final_pda]) (q, [], \<gamma>)" by blast
  hence steps: "pda.steps stack_to_final_pda (New_init, w, [New_sym]) (q, [], \<gamma>)"
    by (simp add: stack_to_final_pda_def)
  from q_final have q_def: "q = New_final"
    by (simp add: stack_to_final_pda_def)
  with steps obtain n where stepn: "pda.stepn stack_to_final_pda n (New_init, w, [New_sym]) (New_final, [], \<gamma>)"
    using pda.stepn_steps[OF pda_stack_to_final] by fastforce
  then obtain n' where "n = Suc (Suc n')"
    using stack_to_final_pda_path_length Suc_less_eq2 numeral_2_eq_2 by fastforce
  with stepn obtain p where "pda.stepn stack_to_final_pda n' (Old_st (init_state M), w, [Old_sym (init_symbol M), New_sym])
                                                                (Old_st p, [], [New_sym])"
    using stack_to_final_pda_split_path by blast
  hence "pda.stepn M n' (init_state M, w, [(init_symbol M)]) (p, [], [])"
    using stack_to_final_pda_stepn by simp
  thus "\<exists>q. pda.steps M (init_state M, w, [init_symbol M]) (q, [], [])"
    using stepn_steps by blast
qed

lemma stack_to_final: "pda.stack_accept M = pda.final_accept stack_to_final_pda"
  unfolding stack_accept_def pda.final_accept_def[OF pda_stack_to_final] using accepted_stack_to_final by blast

end