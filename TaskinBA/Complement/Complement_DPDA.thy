theory Complement_DPDA
  imports Det_Pushdown_Automata
begin

datatype 'q st_extended = OST 'q | Q0' | D | F
datatype 's sym_extended = OSYM 's | X0

lemma inj_OSYM: "inj OSYM"
  by (simp add: inj_def)

instance st_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = OST q} \<union> {Q0', D, F}"
    by auto (metis st_extended.exhaust)
  show "finite (UNIV :: 'a st_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

instance sym_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = OSYM q} \<union> {X0}"
    by auto (metis sym_extended.exhaust)
  show "finite (UNIV :: 'a sym_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

locale dpda_scan = dpda M for M :: "('q :: finite, 'a :: finite, 's :: finite) pda" 
begin

text \<open>In the following we define a deterministic pushdown automata that scans the entire input according to Hopcroft and Ullman.\<close>

definition scan_dpda_final_states :: "'q st_extended set" where
  "scan_dpda_final_states \<equiv> OST ` final_states M \<union> {F}"

fun scan_dpda_delta :: "'q st_extended \<Rightarrow> 'a \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "scan_dpda_delta (OST q) a (OSYM X) = (if \<delta> M q a X = {} \<and> \<delta>\<epsilon> M q X = {} then {(D, [OSYM X])} 
                                            else (\<lambda>(q, \<alpha>). (OST q, map OSYM \<alpha>)) ` \<delta> M q a X)"
| "scan_dpda_delta (OST q) _ X0 = {(D, [X0])}"
| "scan_dpda_delta D _ X = {(D, [X])}"
| "scan_dpda_delta _ _ _ = {}"

definition eps_nonfinal :: "'q \<Rightarrow> 's \<Rightarrow> bool" where
  "eps_nonfinal q X \<equiv> (\<forall>i. \<exists>p \<alpha>. (q, [], [X]) \<leadsto>\<^sub>d(i) (p, [], \<alpha>) \<and> p \<notin> final_states M)"

definition eps_final :: "'q \<Rightarrow> 's \<Rightarrow> bool" where
  "eps_final q X \<equiv> (\<forall>i. \<exists>p \<alpha>. (q, [], [X]) \<leadsto>\<^sub>d(i) (p, [], \<alpha>)) \<and> (\<exists>i p \<alpha>. (q, [], [X]) \<leadsto>\<^sub>d(i) (p, [], \<alpha>) \<and> p \<in> final_states M)"

fun scan_dpda_delta_eps :: "'q st_extended \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "scan_dpda_delta_eps Q0' X0 = {(OST (init_state M), [OSYM (init_symbol M), X0])}"
| "scan_dpda_delta_eps (OST q) (OSYM X) = (if eps_nonfinal q X then {(D, [OSYM X])} else
                                            if eps_final q X then {(F, [OSYM X])} else
                                              (\<lambda>(q, \<alpha>). (OST q, map OSYM \<alpha>)) ` \<delta>\<epsilon> M q X)"
| "scan_dpda_delta_eps F X = {(D, [X])}"
| "scan_dpda_delta_eps _ _ = {}"

definition scan_dpda :: "('q st_extended, 'a, 's sym_extended) pda" where
  "scan_dpda \<equiv> \<lparr> init_state = Q0', init_symbol = X0, final_states = scan_dpda_final_states, 
                  delta = scan_dpda_delta, delta_eps = scan_dpda_delta_eps \<rparr>"

text \<open>The pushdown automaton @{const scan_dpda} is indeed deterministic.\<close>
lemma dpda_scan_dpda: "dpda scan_dpda"
proof (standard, goal_cases)
  case (1 p a Z)
  have "finite (scan_dpda_delta p a Z)" 
    by (induction p a Z rule: scan_dpda_delta.induct) (auto simp: finite_delta)
  then show ?case by (simp add: scan_dpda_def)
next
  case (2 p Z)
  have "finite (scan_dpda_delta_eps p Z)"
    by (induction p Z rule: scan_dpda_delta_eps.induct) (auto simp: finite_delta_eps)
  then show ?case by (simp add: scan_dpda_def)
next
  case (3 q a X)
  have "scan_dpda_delta q a X \<noteq> {} \<longrightarrow> scan_dpda_delta_eps q X = {}" 
  proof (induction q a X rule: scan_dpda_delta.induct)
    case (1 q a X)
    then show ?case proof
      assume a: "scan_dpda_delta (OST q) a (OSYM X) \<noteq> {}"
      have *: "\<delta>\<epsilon> M q X = {}" proof (rule ccontr)
        assume c: "\<delta>\<epsilon> M q X \<noteq> {}"
        from a c have "\<delta> M q a X \<noteq> {}" by simp
        hence "\<delta>\<epsilon> M q X = {}"
          using \<delta>_nonempty[of q a X] by satx
        with c show False by satx
      qed
      hence **: "(q, [], [X]) \<leadsto>\<^sub>d"
        by (simp add: det_step_def the_elem_opt_def)
      from ** have ***: "\<not>eps_final q X"
        unfolding eps_final_def using det_step\<^sub>1_det_stepn_one[of q "[]" "[X]"] by fastforce
      from ** have ****: "\<not>eps_nonfinal q X"
        unfolding eps_nonfinal_def using det_step\<^sub>1_det_stepn_one[of q "[]" "[X]"] by fastforce
      from * *** **** show "scan_dpda_delta_eps (OST q) (OSYM X) = {}" by simp
    qed
  qed simp_all
  then show ?case by (simp add: scan_dpda_def)
next
  case (4 q a X)
  have "scan_dpda_delta q a X = {} \<or> (\<exists>p \<alpha>. scan_dpda_delta q a X = {(p, \<alpha>)})"
    by (induction q a X rule: scan_dpda_delta.induct, auto) (use \<delta>_singleton in force)+
  then show ?case by (simp add: scan_dpda_def)
next
  case (5 q X)
  have "scan_dpda_delta_eps q X = {} \<or> (\<exists>p \<alpha>. scan_dpda_delta_eps q X = {(p, \<alpha>)})"
    by (induction q X rule: scan_dpda_delta_eps.induct, auto) (use \<delta>\<epsilon>_singleton in force)+
  then show ?case by (simp add: scan_dpda_def)
qed

sublocale scan: dpda scan_dpda
  using dpda_scan_dpda .

text \<open>We abbreviate step definitions for @{const scan_dpda} with the sub-index s.\<close>

notation scan.step\<^sub>1 ("(_ \<leadsto>\<^sub>s _)" [50, 50] 50)
notation scan.steps ("(_ \<leadsto>\<^sub>s* _)" [50, 50] 50)    
                                                           
abbreviation stack_with_X0 :: "'s list \<Rightarrow> 's sym_extended list" where 
  "stack_with_X0 \<alpha> \<equiv> map OSYM \<alpha> @ [X0]"

text \<open>Forced steps of @{const scan_dpda}}\<close>
lemma scan_dpda_first_step:
  assumes "(Q0', w, [X0]) \<leadsto>\<^sub>s (q, u, \<alpha>)"
  shows "q = OST (init_state M) \<and> u = w \<and> \<alpha> = [OSYM (init_symbol M), X0]"
  using assms scan.step\<^sub>1_rule by (simp add: scan_dpda_def)

text \<open>Deduction from steps of @{const scan_dpda}}\<close>
lemma scan_dpda_step_from_OST:
  assumes "(OST q, w, \<alpha>) \<leadsto>\<^sub>s (p, u, \<gamma>)"
  shows "(\<exists>p'. p = OST p') \<or> p = F \<or> p = D"
proof -
  from assms obtain X where
  "(\<exists>\<beta>. (p, \<beta>) \<in> scan_dpda_delta_eps (OST q) X) \<or> (\<exists>a \<beta>. (p,\<beta>) \<in> scan_dpda_delta (OST q) a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule_ext scan_dpda_def by fastforce
  then consider (a) ?a | (b) ?b by blast
  thus ?thesis
  proof cases
    case a
    then show ?thesis by (induction "OST q" X rule: scan_dpda_delta_eps.induct) (auto split: if_splits)
  next
    case b
    then obtain a where "\<exists>\<beta>. (p, \<beta>) \<in> scan_dpda_delta (OST q) a X" by blast
    then show ?thesis by (induction "OST q" a X rule: scan_dpda_delta.induct) (auto split: if_splits)
  qed
qed

lemma scan_dpda_step_from_F:
  assumes "(F, w, \<alpha>) \<leadsto>\<^sub>s (q, u, \<gamma>)"
  shows "q = D"
  using assms scan.step\<^sub>1_rule_ext[of F w \<alpha> q u \<gamma>] scan_dpda_def by auto

lemma scan_dpda_step_to_F:
  assumes "(q, w, X#\<alpha>) \<leadsto>\<^sub>s (F, u, \<gamma>)"
  shows "u = w \<and> (\<exists>q' X'. q = OST q' \<and> X = OSYM X' \<and> eps_final q' X')"
proof -
  from assms have cases: "(\<exists>\<beta>. u = w \<and> \<gamma> = \<beta> @ \<alpha> \<and> (F, \<beta>) \<in> scan_dpda_delta_eps q X) 
                      \<or> (\<exists>a \<beta>. w = a # u \<and> \<gamma> = \<beta> @ \<alpha> \<and> (F, \<beta>) \<in> scan_dpda_delta q a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule[of q w X \<alpha> F u \<gamma>] scan_dpda_def by simp
  from cases consider (a) ?a | (b) ?b by blast
  then show ?thesis
  proof cases
    case a
    then show ?thesis by (induction q X rule: scan_dpda_delta_eps.induct) (auto split: if_splits)
  next
    case b
    then obtain a where "\<exists>\<beta>. w = a # u \<and> \<gamma> = \<beta> @ \<alpha> \<and> (F, \<beta>) \<in> scan_dpda_delta q a X" by blast
    then show ?thesis by (induction q a X rule: scan_dpda_delta.induct) (auto split: if_splits)
  qed
qed

lemma scan_dpda_step_from_D:
  assumes "(D, w, \<alpha>) \<leadsto>\<^sub>s (q, u, \<gamma>)"
  shows "q = D"
using assms scan.step\<^sub>1_rule_ext[of D w \<alpha> q u \<gamma>] scan_dpda_def by auto

lemma scan_dpda_steps_from_OST:
  assumes "(OST q, w, \<alpha>) \<leadsto>\<^sub>s* (p, u, \<gamma>)"
  shows "(\<exists>p'. p = OST p') \<or> p = F \<or> p = D"
using assms by (induction "(OST q, w, \<alpha>)" "(p, u, \<gamma>)" arbitrary: p u \<gamma> rule: scan.steps_induct2_bw, simp) 
 (use scan_dpda_step_from_OST scan_dpda_step_from_F scan_dpda_step_from_D in blast)

lemma scan_dpda_step_to_OST:
  assumes "(q, w, \<alpha>) \<leadsto>\<^sub>s (OST p, u, \<gamma>)"
  shows "q = Q0' \<or> (\<exists>q'. q = OST q')"
using assms scan_dpda_step_from_F[of w \<alpha> "OST p" u \<gamma>] scan_dpda_step_from_D[of w \<alpha> "OST p" u \<gamma>]
  by (metis st_extended.exhaust st_extended.simps(5))

lemma scan_dpda_stack_with_X0:
  assumes "(OST q, w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (OST p, u, \<gamma>)"
  shows "\<exists>\<gamma>'. \<gamma> = stack_with_X0 \<gamma>'"
using assms proof (induction "(OST q, w, stack_with_X0 \<alpha>)" "(OST p, u, \<gamma>)" arbitrary: p u \<gamma> rule: scan.steps_induct2_bw)
  case (step r u \<gamma> v \<beta>)
  from step(1,2) obtain r' where r_OST[simp]: "r = OST r'"
    using scan_dpda_steps_from_OST[of q w "stack_with_X0 \<alpha>" r u \<gamma>] scan_dpda_step_to_OST[of r u \<gamma> p v \<beta>] by blast
  from step(3)[OF r_OST] obtain \<gamma>'' where \<gamma>_X0: "\<gamma> = stack_with_X0 \<gamma>''" by blast
  from step(2) obtain X \<gamma>' \<beta>' where \<gamma>_def: "\<gamma> = X#\<gamma>'" and \<beta>_def: "\<beta> = \<beta>' @ \<gamma>'" and
    cases: "(OST p, \<beta>') \<in> scan_dpda_delta_eps (OST r') X \<or> (\<exists>a. (OST p, \<beta>') \<in> scan_dpda_delta (OST r') a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule_ext[of r u \<gamma> "OST p" v \<beta>] scan_dpda_def by auto
  from cases consider (a) ?a | (b) ?b by blast
  then have X_and_\<beta>'_def: "(\<exists>X'. X = OSYM X') \<and> (\<exists>\<beta>''. \<beta>' = map OSYM \<beta>'')"
  proof cases
    case a
    then show ?thesis by (induction "OST r'" X rule: scan_dpda_delta_eps.induct) (auto split: if_splits)
  next
    case b
    then obtain a where "(OST p, \<beta>') \<in> scan_dpda_delta (OST r') a X" by blast
    then show ?thesis by (induction "OST r'" a X rule: scan_dpda_delta.induct) (auto split: if_splits)
  qed
  from X_and_\<beta>'_def[THEN conjunct1] \<gamma>_X0 \<gamma>_def have "\<exists>\<gamma>'''. \<gamma>' = stack_with_X0 \<gamma>'''"
    by (metis hd_append list.sel(1,3) map_tl sym_extended.distinct(1) tl_append_if)
  with X_and_\<beta>'_def[THEN conjunct2] \<beta>_def show ?case
    by (metis append.assoc map_append)
qed blast

text \<open>The original pushdown automaton can mimic the steps of @{const scan_dpda} assuming that it never leaves the old states.\<close>
lemma scan_dpda_trans:
  assumes "(OST q, map OSYM \<alpha>) \<in> \<delta> scan_dpda (OST p) a (OSYM X)"
  shows "(q, \<alpha>) \<in> \<delta> M p a X"
using assms by (auto simp: scan_dpda_def inj_map_eq_map[OF inj_OSYM] split: if_splits)

lemma scan_dpda_eps:
  assumes "(OST q, map OSYM \<alpha>) \<in> \<delta>\<epsilon> scan_dpda (OST p) (OSYM X)"
  shows "(q, \<alpha>) \<in> \<delta>\<epsilon> M p X"
using assms by (auto simp: scan_dpda_def inj_map_eq_map[OF inj_OSYM] split: if_splits)

lemma scan_dpda_step: 
  assumes "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s (OST p, u, map OSYM \<gamma>)"
  shows "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>)"
proof -
  from assms obtain X \<alpha>' where \<alpha>OSYM_def: "map OSYM \<alpha> = OSYM X # map OSYM \<alpha>'" and rule:
  "(\<exists>\<beta>. u = w \<and> map OSYM \<gamma> = \<beta> @ map OSYM \<alpha>' \<and> (OST p, \<beta>) \<in> \<delta>\<epsilon> scan_dpda (OST q) (OSYM X)) \<or>
         (\<exists>a \<beta>. w = a # u \<and> map OSYM \<gamma> = \<beta> @ map OSYM \<alpha>' \<and> (OST p, \<beta>) \<in> \<delta> scan_dpda (OST q) a (OSYM X))"
    using scan.step\<^sub>1_rule_ext[of "OST q" w "map OSYM \<alpha>" "OST p" u "map OSYM \<gamma>"] by auto
  from \<alpha>OSYM_def have \<alpha>_def: "\<alpha> = X#\<alpha>'"
    using inj_map_eq_map[OF inj_OSYM] by auto
  from rule have "(\<exists>\<beta>. u = w \<and> map OSYM \<gamma> = map OSYM \<beta> @ map OSYM \<alpha>' \<and> (OST p, map OSYM \<beta>) \<in> \<delta>\<epsilon> scan_dpda (OST q) (OSYM X)) \<or>
         (\<exists>a \<beta>. w = a # u \<and> map OSYM \<gamma> = map OSYM \<beta> @ map OSYM \<alpha>' \<and> (OST p, map OSYM \<beta>) \<in> \<delta> scan_dpda (OST q) a (OSYM X))"
    using append_eq_map_conv[where ?f = OSYM] by metis
  then have "(\<exists>\<beta>. u = w \<and> \<gamma> = \<beta>@\<alpha>' \<and> (p, \<beta>) \<in> \<delta>\<epsilon> M q X) \<or> (\<exists>a \<beta>. w = a#u \<and> \<gamma> = \<beta>@\<alpha>' \<and> (p, \<beta>) \<in> \<delta> M q a X)"
    using scan_dpda_trans scan_dpda_eps by (metis inj_OSYM inj_map_eq_map map_append)
  with \<alpha>_def show ?thesis
    using step\<^sub>1_rule by simp
qed  

lemma scan_dpda_stepX0:
  assumes "(OST q, w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s (OST p, u, stack_with_X0 \<gamma>)"
  shows "(q, w, \<alpha>) \<leadsto> (p, u, \<gamma>)"
proof -
  from assms obtain X \<alpha>' where \<alpha>_def: "stack_with_X0 \<alpha> = X#\<alpha>'" and
    cases: "(\<exists>\<beta>. (OST p, \<beta>) \<in> scan_dpda_delta_eps (OST q) X) \<or> (\<exists>a \<beta>. (OST p, \<beta>) \<in> scan_dpda_delta (OST q) a X)" (is "?a \<or> ?b")
    using scan.step\<^sub>1_rule_ext[of "OST q" w "stack_with_X0 \<alpha>" "OST p" u "stack_with_X0 \<gamma>"] scan_dpda_def by force
  from cases consider (a) ?a | (b) ?b by blast
  then have "\<exists>X'. X = OSYM X'"
  proof cases
    case a
    then show ?thesis by (induction "OST q" X rule: scan_dpda_delta_eps.induct) auto
  next
    case b
    then obtain a where "\<exists>\<beta>. (OST p, \<beta>) \<in> scan_dpda_delta (OST q) a X" by blast
    then show ?thesis by (induction "OST q" a X rule: scan_dpda_delta.induct) auto
  qed
  with \<alpha>_def have "map OSYM \<alpha> \<noteq> []" by auto
  then have "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s (OST p, u, map OSYM \<gamma>)"
    using scan.step\<^sub>1_stack_drop[OF assms] by simp
  then show ?thesis
    using scan_dpda_step by presburger
qed

lemma scan_dpda_stepsX0:
  assumes "(OST q, w, stack_with_X0 \<alpha>) \<leadsto>\<^sub>s* (OST p, u, stack_with_X0 \<gamma>)"
  shows "(q, w, \<alpha>) \<leadsto>* (p, u, \<gamma>)"
using assms proof (induction "(OST q, w, stack_with_X0 \<alpha>)" "(OST p, u, stack_with_X0 \<gamma>)" arbitrary: p u \<gamma> rule: scan.steps_induct2_bw)
  case base
  then show ?case
    by (simp add: inj_OSYM steps_refl)
next
  case (step r u \<beta> v)
  obtain r' where r_def: "r = OST r'"
    using scan_dpda_steps_from_OST[OF step(1)] scan_dpda_step_to_OST[OF step(2)] by blast
  obtain \<beta>' where \<beta>_def: "\<beta> = stack_with_X0 \<beta>'"
    using scan_dpda_stack_with_X0[OF step(1)[simplified r_def]] by blast
  from step(3)[OF r_def \<beta>_def] have *: "(q, w, \<alpha>) \<leadsto>* (r', u, \<beta>')" .
  have **: "(r', u, \<beta>') \<leadsto> (p, v, \<gamma>)"
    using scan_dpda_stepX0[OF step(2)[simplified r_def \<beta>_def]] .
  from * ** show ?case
    using step\<^sub>1_steps steps_trans by blast
qed   

text \<open>Before we move onto the converse direction, we need a helper lemma stating that if the pair (q, X) forces a cycle then the remaining part of the
      stack is irrelevant.\<close>    
                            
lemma stack_cycle_drop:    
  assumes "\<forall>i. \<exists>p \<alpha>. (q, [], [X]) \<leadsto>\<^sub>d(i) (p, [], \<alpha>)"
      and "(q, [], X#\<gamma>) \<leadsto>* (r, [], \<beta>)"
    shows "\<exists>Y \<beta>'. \<beta> = Y # \<beta>' @ \<gamma> \<and> (q, [], [X]) \<leadsto>* (r, [], Y#\<beta>')"
using assms(2) proof (induction "(q, [] :: 'a list, X#\<gamma>)" "(r, [] :: 'a list, \<beta>)" arbitrary: r \<beta> rule: steps_induct2_bw)  
  case base
  then show ?case  
    by (simp add: steps_refl)
next 
  case (step p w \<alpha> r \<beta>)                 
  have w_def: "w = []"
    using decreasing_word[OF step(1)] by simp
  from step(3)[OF w_def] obtain Y \<beta>' where \<alpha>_def: "\<alpha> = Y # \<beta>' @ \<gamma>" and p1: "(q, [], [X]) \<leadsto>* (p, [], Y # \<beta>')" by blast
  from step(2) \<alpha>_def obtain \<beta>'' where \<beta>_def: "\<beta> = \<beta>'' @ \<beta>' @ \<gamma>"          
    using step\<^sub>1_rule[of p w Y "\<beta>' @ \<gamma>" r "[]" \<beta>] by blast
  from step(2)[unfolded w_def \<alpha>_def \<beta>_def] have p2: "(p, [], Y # \<beta>') \<leadsto> (r, [], \<beta>'' @ \<beta>')" 
    using step\<^sub>1_stack_drop[of p "[]" "Y # \<beta>'" \<gamma> r "[]" "\<beta>'' @ \<beta>'"] by simp 
  have *: "(q, [], [X]) \<leadsto>* (r, [], \<beta>'' @ \<beta>')"             
    using steps_trans[OF p1 step\<^sub>1_steps[OF p2]] .  
  from * obtain n where d1: "(q, [], [X]) \<leadsto>\<^sub>d(n) (r, [], \<beta>'' @ \<beta>')"
    using stepn_steps[of q "[]" "[X]" r "[]" "\<beta>'' @ \<beta>'"] stepn_det_stepn\<^sub>1[of _  q "[]" "[X]" r "[]" "\<beta>'' @ \<beta>'"] by blast
  from assms(1) obtain s \<zeta> where d2: "(q, [], [X]) \<leadsto>\<^sub>d(Suc n) (s, [], \<zeta>)" by presburger
  from d1 d2 have "(r, [], \<beta>'' @ \<beta>') \<leadsto>\<^sub>d (s, [], \<zeta>)" by simp
  then have **: "\<exists>Z \<beta>'''. \<beta>''@\<beta>' = Z#\<beta>'''"
    using step\<^sub>1_det_step\<^sub>1[of r "[]" "\<beta>'' @ \<beta>'" s "[]" \<zeta>] step\<^sub>1_nonempty_stack[of r "[]" "\<beta>'' @ \<beta>'" s "[]" \<zeta>] by simp
  from \<beta>_def * ** show ?case by auto                                                                                          
qed                                 
                                                                     
text \<open>The automaton @{const scan_dpda} can either mimic the steps of the original automaton or detect a cycle\<close>
lemma scan_dpda_steps:
  assumes "(q, w, \<alpha>) \<leadsto>* (p, u, \<gamma>)"
  shows "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST p, u, map OSYM \<gamma>) \<or>     
            (\<exists>r X \<beta>. (OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST r, u, OSYM X # map OSYM \<beta>) \<and> (r, [], X#\<beta>) \<leadsto>* (p, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>\<^sub>d(i) (s, [], \<Delta>)))"
using assms proof (induction "(q, w, \<alpha>)" "(p, u, \<gamma>)" arbitrary: p u \<gamma> rule: steps_induct2_bw)
  case base
  then show ?case
    by (simp add: scan.steps_refl)
next
  case (step p u \<gamma> r v \<beta>)
  from step(2) obtain X \<gamma>' where \<gamma>_def: "\<gamma> = X#\<gamma>'" and 
      cases: "(\<exists>\<zeta>. v = u \<and> \<beta> = \<zeta> @ \<gamma>' \<and> (r, \<zeta>) \<in> \<delta>\<epsilon> M p X) \<or> (\<exists>a \<zeta>. u = a # v \<and> \<beta> = \<zeta> @ \<gamma>' \<and> (r, \<zeta>) \<in> \<delta> M p a X)" (is "?a \<or> ?b")
    using step\<^sub>1_rule_ext[of p u \<gamma> r v \<beta>] by blast
  from cases consider (a) ?a | (b) ?b by blast
  then show ?case
  proof cases
    case a    
    then obtain \<zeta> where v_def: "u = v" and \<beta>_def: "\<beta> = \<zeta> @ \<gamma>'" and elem: "(r, \<zeta>) \<in> \<delta>\<epsilon> M p X" by blast 
    from step(3) consider (a1) "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST p, u, map OSYM \<gamma>)" |  
                          (a2) "\<exists>r X \<beta>. (OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST r, u, OSYM X # map OSYM \<beta>) \<and> (r, [], X # \<beta>) \<leadsto>* (p, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>\<^sub>d(i) (s, [], \<Delta>))" by blast
    then show ?thesis
    proof cases    
      case a1     
      consider (a11) "\<forall>i. \<exists>s \<Delta>. (p, [], [X]) \<leadsto>\<^sub>d(i) (s, [], \<Delta>)" | (a12) "\<not>(\<forall>i. \<exists>s \<Delta>. (p, [], [X]) \<leadsto>\<^sub>d(i) (s, [], \<Delta>))" by blast
      then show ?thesis
      proof cases
        case a11     
        from a1[unfolded v_def \<gamma>_def] have *: "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST p, v, OSYM X # map OSYM \<gamma>')" by simp 
        from elem \<beta>_def have **: "(p, [], X # \<gamma>') \<leadsto>* (r, [], \<beta>)"
          using step\<^sub>1_rule[of p "[]" X \<gamma>' r "[]" \<beta>] step\<^sub>1_steps by blast 
        from * ** a11 show ?thesis by blast  
      next                  
        case a12                                                                  
        then have "\<not>eps_nonfinal p X \<and> \<not>eps_final p X"
          by (auto simp: eps_nonfinal_def eps_final_def)
        with elem have "(OST r, map OSYM \<zeta>) \<in> \<delta>\<epsilon> scan_dpda (OST p) (OSYM X)"
          by (auto simp: scan_dpda_def)
        with v_def \<gamma>_def \<beta>_def have "(OST p, u, map OSYM \<gamma>) \<leadsto>\<^sub>s (OST r, v, map OSYM \<beta>)"
          using scan.step\<^sub>1_rule[of "OST p" u "OSYM X" "map OSYM \<gamma>'" "OST r" u "map OSYM \<zeta> @ map OSYM \<gamma>'"] by simp
        with a1 show ?thesis     
          using scan.step\<^sub>1_steps scan.steps_trans by blast  
      qed               
    next                                               
      case a2                        
      then obtain s Y \<mu> where *: "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST s, u, OSYM Y # map OSYM \<mu>)" and spath: "(s, [], Y # \<mu>) \<leadsto>* (p, [], \<gamma>)"
                          and **: "\<forall>i. \<exists>t \<Delta>. (s, [], [Y]) \<leadsto>\<^sub>d(i) (t, [], \<Delta>)" by blast 
      from elem \<gamma>_def \<beta>_def have "(p, [], \<gamma>) \<leadsto> (r, [], \<beta>)"   
        using step\<^sub>1_rule[of p "[]" X \<gamma>' r "[]" \<beta>] by simp  
      with spath have ***: "(s, [], Y # \<mu>) \<leadsto>* (r, [], \<beta>)"
        using step\<^sub>1_steps steps_trans by blast
      from *[unfolded v_def] ** *** show ?thesis by blast           
    qed                               
  next    
    (* This is the only place we use determinism. *)
    case b  
    then obtain a \<zeta> where u_def: "u = a#v" and \<beta>_def: "\<beta> = \<zeta> @ \<gamma>'" and elem: "(r, \<zeta>) \<in> \<delta> M p a X" by blast
    from elem have eps_empty: "\<delta>\<epsilon> M p X = {}"               
      using \<delta>_nonempty[of p a X] by blast
    from step(3) consider (t) "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST p, u, map OSYM \<gamma>)" 
      | (f) "\<exists>r X \<beta>. (OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST r, u, OSYM X # map OSYM \<beta>) \<and> (r, [], X # \<beta>) \<leadsto>* (p, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>\<^sub>d(i) (s, [], \<Delta>))" by blast
    then have *: "(OST q, w, map OSYM \<alpha>) \<leadsto>\<^sub>s* (OST p, u, map OSYM \<gamma>)"         
    proof cases
      case t
      then show ?thesis .
    next
      case f     
      then obtain s Y \<mu> where f1: "(s, [], Y # \<mu>) \<leadsto>* (p, [], \<gamma>)" and f2: "\<forall>i. \<exists>s' \<mu>'. (s, [], [Y]) \<leadsto>\<^sub>d(i) (s', [], \<mu>')" by blast 
      with \<gamma>_def obtain \<gamma>'' where "(s, [], [Y]) \<leadsto>* (p, [], X#\<gamma>'')"  
        using stack_cycle_drop[OF f2 f1] by blast 
      then obtain n where f3: "(s, [], [Y]) \<leadsto>\<^sub>d(n) (p, [], X#\<gamma>'')"
        using stepn_steps[of s "[]" "[Y]" p "[]" "X#\<gamma>''"] stepn_det_stepn\<^sub>1[of _ s "[]" "[Y]" p "[]" "X#\<gamma>''"] by blast  
      from eps_empty have f4: "(p, [], X#\<gamma>'') \<leadsto>\<^sub>d" 
        by (simp add: det_step_def the_elem_opt_def) 
      from f3 f4 have "(s, [], [Y]) \<leadsto>\<^sub>d(Suc n)" by simp
      with f2 have False
        using not_None_eq by blast
      then show ?thesis by simp            
    qed     
    from eps_empty have "(p, [], [X]) \<leadsto>\<^sub>d(1)"
      by (simp add: det_step_def the_elem_opt_def) 
    then have "\<not>eps_nonfinal p X \<and> \<not>eps_final p X"   
      unfolding eps_nonfinal_def eps_final_def using not_None_eq by blast
    with elem have "(OST r, map OSYM \<zeta>) \<in> \<delta> scan_dpda (OST p) a (OSYM X)" 
      by (auto simp: scan_dpda_def)
    with u_def \<gamma>_def \<beta>_def have **: "(OST p, u, map OSYM \<gamma>) \<leadsto>\<^sub>s (OST r, v, map OSYM \<beta>)"
      using scan.step\<^sub>1_rule[of "OST p" u "OSYM X" "map OSYM \<gamma>'" "OST r" v "map OSYM \<beta>"] by simp  
    show ?thesis 
      using scan.steps_trans[OF * scan.step\<^sub>1_steps[OF **]] by simp  
  qed                           
qed

text \<open>The language of @{const scan_dpda} and the original pushdown automaton are the same.\<close>
lemma "scan.accept_final = accept_final"
proof
  show "scan.accept_final \<subseteq> accept_final"
  proof
    fix w
    assume "w \<in> scan.accept_final"
    then obtain q \<gamma> where q_final: "q \<in> scan_dpda_final_states" and scan_path: "(Q0', w, [X0]) \<leadsto>\<^sub>s* (q, [], \<gamma>)"
      unfolding scan.accept_final_def using scan_dpda_def by auto
    from q_final have cases: "(\<exists>q' \<in> final_states M. q = OST q') \<or> q = F" (is "?a \<or> ?b")
      unfolding scan_dpda_final_states_def by auto
    then have "\<exists>p u \<alpha>. (Q0', w, [X0]) \<leadsto>\<^sub>s (p, u, \<alpha>) \<and> (p, u, \<alpha>) \<leadsto>\<^sub>s* (q, [], \<gamma>)"
      using scan.steps_not_refl_split_first[OF scan_path] by blast
    then have p: "(OST (init_state M), w, [OSYM (init_symbol M), X0]) \<leadsto>\<^sub>s* (q, [], \<gamma>)"
      using scan_dpda_first_step by blast
    from cases consider (a) ?a | (b) ?b by blast
    then show "w \<in> accept_final"
    proof cases
      case a
      then obtain q' where q_def: "q = OST q'" and q'_final: "q' \<in> final_states M" by blast
      from p[simplified q_def] obtain \<gamma>' where \<gamma>_def: "\<gamma> = stack_with_X0 \<gamma>'"
        using scan_dpda_stack_with_X0[of "init_state M" w "[init_symbol M]" q' "[]" \<gamma>] by auto
      from p[simplified q_def \<gamma>_def] have "(init_state M, w, [init_symbol M]) \<leadsto>* (q', [], \<gamma>')"
        using scan_dpda_stepsX0[of "init_state M" w "[init_symbol M]" q' "[]" \<gamma>'] by simp
      with q'_final show ?thesis
        unfolding accept_final_def by blast
    next
      case b
      obtain p u \<alpha> where fss: "(OST (init_state M), w, [OSYM (init_symbol M), X0]) \<leadsto>\<^sub>s* (p, u, \<alpha>)" 
                                          and ls: "(p, u, \<alpha>) \<leadsto>\<^sub>s (F, [], \<gamma>)"
        using scan.steps_not_refl_split_last[OF p[simplified b]] by blast
      obtain X \<alpha>' where \<alpha>_def: "\<alpha> = X#\<alpha>'"
        using scan.step\<^sub>1_nonempty_stack[OF ls] by blast
      obtain p' X' where u_def: "u = []" and p_def: "p = OST p'" and X_def: "X = OSYM X'" and epath: "eps_final p' X'"
        using scan_dpda_step_to_F[OF ls[simplified \<alpha>_def]] by blast
      from fss[simplified p_def] obtain \<alpha>'' where \<alpha>_with_X0: "\<alpha> = stack_with_X0 \<alpha>''"
        using scan_dpda_stack_with_X0[of "init_state M" w "[init_symbol M]" p' u \<alpha>] by auto
      from fss[simplified p_def u_def \<alpha>_with_X0] have *: "(init_state M, w, [init_symbol M]) \<leadsto>* (p', [], \<alpha>'')"
        using scan_dpda_stepsX0[of "init_state M" w "[init_symbol M]" p' "[]" \<alpha>''] by simp
      from \<alpha>_def \<alpha>_with_X0 X_def obtain \<alpha>''' where \<alpha>''_def: "\<alpha>'' = X'#\<alpha>'''"
        by (metis Nil_is_map_conv append_Cons append_Nil hd_Cons_tl list.map_sel(1) list.sel(1) sym_extended.distinct(1) sym_extended.inject)
      from epath[unfolded eps_final_def] obtain i r \<beta> where dpath: "(p', [], [X']) \<leadsto>\<^sub>d(i) (r, [], \<beta>)" and r_final: "r \<in> final_states M" by blast
      from dpath have "(p', [], [X']) \<leadsto>* (r, [], \<beta>)"
        using stepn_det_stepn\<^sub>1[of i p' "[]" "[X']" r "[]" \<beta>] stepn_steps[of p' "[]" "[X']" r "[]" \<beta>] by auto
      with \<alpha>''_def have **: "(p', [], \<alpha>'') \<leadsto>* (r, [], \<beta>@\<alpha>''')"
        using steps_stack_app[of p' "[]" "[X']" r "[]" \<beta> \<alpha>'''] by simp
      from r_final show ?thesis
        unfolding accept_final_def using steps_trans[OF * **] by blast
    qed
  qed
next
  show "accept_final \<subseteq> scan.accept_final"
  proof
    fix w
    assume "w \<in> accept_final"
    then obtain q \<gamma> where q_final: "q \<in> final_states M" and p: "(init_state M, w, [init_symbol M]) \<leadsto>* (q, [], \<gamma>)" 
      unfolding accept_final_def by blast                                                        
    have fs: "(Q0', w, [X0]) \<leadsto>\<^sub>s (OST (init_state M), w, [OSYM (init_symbol M), X0])"
      using scan_dpda_def scan.step\<^sub>1_rule by auto
    from scan_dpda_steps[OF p] consider (a) "(OST (init_state M), w, [OSYM (init_symbol M)]) \<leadsto>\<^sub>s* (OST q, [], map OSYM \<gamma>)"
      | (b) "\<exists>r X \<beta>. (OST (init_state M), w, [OSYM (init_symbol M)]) \<leadsto>\<^sub>s* (OST r, [], OSYM X # map OSYM \<beta>) \<and>
                                (r, [], X # \<beta>) \<leadsto>* (q, [], \<gamma>) \<and> (\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>\<^sub>d(i) (s, [], \<Delta>))" by auto
    then show "w \<in> scan.accept_final"
    proof cases
      case a
      have "(OST (init_state M), w, [OSYM (init_symbol M), X0]) \<leadsto>\<^sub>s* (OST q, [], stack_with_X0 \<gamma>)"
        using scan.steps_stack_app[OF a] by simp
      then have "(Q0', w, [X0]) \<leadsto>\<^sub>s* (OST q, [], stack_with_X0 \<gamma>)"
        using scan.step\<^sub>1_steps[OF fs] scan.steps_trans[of Q0' w "[X0]" "OST (init_state M)" w "[OSYM (init_symbol M), X0]" "OST q" "[]" "stack_with_X0 \<gamma>"] by simp 
      with q_final show ?thesis
        unfolding scan.accept_final_def using scan_dpda_def scan_dpda_final_states_def by auto
    next
      case b
      then obtain r X \<beta> where pscan: "(OST (init_state M), w, [OSYM (init_symbol M)]) \<leadsto>\<^sub>s* (OST r, [], OSYM X # map OSYM \<beta>)" and
        pr: "(r, [], X # \<beta>) \<leadsto>* (q, [], \<gamma>)" and cycle: "\<forall>i. \<exists>s \<Delta>. (r, [], [X]) \<leadsto>\<^sub>d(i) (s, [], \<Delta>)" by blast
      have *: "(OST (init_state M), w, [OSYM (init_symbol M), X0]) \<leadsto>\<^sub>s* (OST r, [], stack_with_X0 (X # \<beta>))"
        using scan.steps_stack_app[OF pscan] by simp
      have r_final: "\<exists>\<gamma>'. (r, [], [X]) \<leadsto>* (q, [], \<gamma>')"
        using stack_cycle_drop[OF cycle pr] by auto
      from r_final q_final have e1: "\<not>eps_nonfinal r X"
        unfolding eps_nonfinal_def using stepn_steps[of r "[]" "[X]" q "[]"] stepn_det_stepn\<^sub>1[of _ r "[]" "[X]" q "[]"] by (metis option.inject prod.inject)
      from cycle r_final q_final have e2: "eps_final r X"
        unfolding eps_final_def using stepn_steps[of r "[]" "[X]" q "[]"] stepn_det_stepn\<^sub>1[of _ r "[]" "[X]" q "[]"] by blast
      from e1 e2 have "(OST r, [], OSYM X # map OSYM \<beta>) \<leadsto>\<^sub>s (F, [], OSYM X # map OSYM \<beta>)"
        using scan_dpda_def scan.step\<^sub>1_rule[of "OST r" "[]" "OSYM X" "map OSYM \<beta>" F "[]" "OSYM X # map OSYM \<beta>"] by simp
      then have **: "(OST r, [], stack_with_X0 (X#\<beta>)) \<leadsto>\<^sub>s (F, [], stack_with_X0 (X#\<beta>))"
        using scan.steps_stack_app[of "OST r" "[]" "OSYM X # map OSYM \<beta>" F "[]" "OSYM X # map OSYM \<beta>"] by simp
      from fs * ** have "(Q0', w, [X0]) \<leadsto>\<^sub>s* (F, [], stack_with_X0 (X # \<beta>))"
        using scan.step\<^sub>1_steps scan.steps_trans by metis
      then show ?thesis
        unfolding scan.accept_final_def using scan_dpda_def scan_dpda_final_states_def by auto 
    qed
  qed                                               
qed
                                                            
(* TODO: Properties of scan_dpda *)

end

datatype 'q st_num = S1 'q | S2 'q | S3 'q

instance st_num :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = S1 q} \<union> {t. \<exists>q. t = S2 q} \<union> {t. \<exists>q. t = S3 q}"
    by auto (metis st_num.exhaust)
  show "finite (UNIV :: 'a st_num set)"
    by (simp add: * full_SetCompr_eq)
qed

lemma inj_S1: "inj S1"
  by (simp add: inj_def)

lemma inj_S2: "inj S2"
  by (simp add: inj_def)

locale complement_dpda = dpda M for M :: "('q :: finite, 'a :: finite, 's :: finite) pda"
(* TODO: Assumptions about M *)
begin

definition comp_dpda_init_state :: "'q st_num" where
  "comp_dpda_init_state \<equiv> if init_state M \<in> final_states M then S1 (init_state M) else S2 (init_state M)"

definition comp_dpda_final_states :: "'q st_num set" where
  "comp_dpda_final_states \<equiv> range S3"

fun comp_dpda_delta :: "'q st_num \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('q st_num \<times> 's list) set" where
  "comp_dpda_delta (S1 q) a X = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` \<delta> M q a X"
| "comp_dpda_delta (S3 q) a X = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` \<delta> M q a X"
| "comp_dpda_delta _ _ _ = {}"

fun comp_dpda_delta_eps :: "'q st_num \<Rightarrow> 's \<Rightarrow> ('q st_num \<times> 's list) set" where
  "comp_dpda_delta_eps (S1 q) X = (\<lambda>(p, \<alpha>). (S1 p, \<alpha>)) ` \<delta>\<epsilon> M q X"
| "comp_dpda_delta_eps (S2 q) X = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` \<delta>\<epsilon> M q X 
                                    \<union> (if \<exists>a. \<delta> M q a X \<noteq> {} then {(S3 q, [X])} else {})"
| "comp_dpda_delta_eps _ _ = {}"

definition comp_dpda :: "('q st_num, 'a, 's) pda" where
  "comp_dpda \<equiv> \<lparr> init_state = comp_dpda_init_state, init_symbol = init_symbol M, final_states = comp_dpda_final_states,
                    delta = comp_dpda_delta, delta_eps = comp_dpda_delta_eps \<rparr>"

(* TODO *)
lemma image_singleton_if_inj:
  assumes "inj f"
  shows "(\<exists>x. A = {x}) \<longleftrightarrow> (\<exists>x. f ` A = {x})"
using assms by (metis image_empty image_insert image_inv_f_f)

lemma dpda_comp_dpda: "dpda comp_dpda"
proof (standard, goal_cases)
  case (1 p a Z)
  have "finite (comp_dpda_delta p a Z)"
    by (induction p a Z rule: comp_dpda_delta.induct) (auto simp: finite_delta)
  then show ?case
    by (simp add: comp_dpda_def)
next
  case (2 p Z)
  have "finite (comp_dpda_delta_eps p Z)"
    by (induction p Z rule: comp_dpda_delta_eps.induct) (auto simp: finite_delta_eps)
  then show ?case
    by (simp add: comp_dpda_def)
next
  case (3 q a X)
  then show ?case
  proof
    assume "\<delta> comp_dpda q a X \<noteq> {}"
    then have "comp_dpda_delta q a X \<noteq> {}"
      by (simp add: comp_dpda_def)
    then have "comp_dpda_delta_eps q X = {}"
      by (induction q a X rule: comp_dpda_delta.induct) (auto simp: \<delta>_nonempty)
    then show "\<delta>\<epsilon> comp_dpda q X = {}"
      by (simp add: comp_dpda_def)
  qed
next
  case (4 q a X)
  let ?f = "(\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>))"
  have *: "inj ?f"
    by (simp add: inj_def)
  have "comp_dpda_delta q a X = {} \<or> (\<exists>p \<gamma>. comp_dpda_delta q a X = {(p, \<gamma>)})"
  proof (induction q a X rule: comp_dpda_delta.induct)
    case (1 q a X)
    then show ?case
      using \<delta>_singleton[of q a X] image_singleton_if_inj[OF *, of "\<delta> M q a X"] by simp 
  next
    case (2 q a X)
    then show ?case 
      using \<delta>_singleton[of q a X] image_singleton_if_inj[OF *, of "\<delta> M q a X"] by simp 
  qed simp
  then show ?case
    by (simp add: comp_dpda_def)
next
  case (5 q X)
  have "comp_dpda_delta_eps q X = {} \<or> (\<exists>p \<gamma>. comp_dpda_delta_eps q X = {(p, \<gamma>)})"
  proof (induction q X rule: comp_dpda_delta_eps.induct)
    case (1 q X)
    then show ?case
      using \<delta>\<epsilon>_singleton[of q X] by auto
  next
    case (2 q X)
    consider (a) "\<exists>a. \<delta> M q a X \<noteq> {}" | (b) "\<not>(\<exists>a. \<delta> M q a X \<noteq> {})" by blast
    then show ?case
    proof cases
      case a
      then have "\<delta>\<epsilon> M q X = {}"
        using \<delta>_nonempty[of q _ X] by blast
      then show ?thesis by simp
    next
      case b
      let ?f = "(\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>))"
      have *: "inj ?f"
        by (simp add: inj_def)
      from b show ?thesis
        using \<delta>\<epsilon>_singleton[of q X] image_singleton_if_inj[OF *, of "\<delta>\<epsilon> M q X"] by simp
    qed
  qed simp
  then show ?case
    by (simp add: comp_dpda_def)
qed

sublocale comp: dpda comp_dpda
  using dpda_comp_dpda . 

lemma h1: "w \<notin> accept_final \<Longrightarrow> w \<in> comp.accept_final"
  sorry

lemma h2: "w \<in> accept_final \<Longrightarrow> w \<notin> comp.accept_final"
  sorry

lemma h3: "w \<in> comp.accept_final \<Longrightarrow> w \<notin> accept_final"
  sorry

lemma h4: "w \<notin> comp.accept_final \<Longrightarrow> w \<in> accept_final"
  sorry

(* Combinations 
                 h1 h2
                 h3 h4
                 h1 h3
                 h2 h4 *)

(* TODO *)
lemma "comp.accept_final = UNIV - accept_final"
  sorry

end
end