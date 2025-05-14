theory Two_way_DFA_HF
  imports "Finite_Automata_HF.Finite_Automata_HF"
    (*Should I use a different
                                                                  reflexive-transitive closure thy?*)
begin

datatype dir = Left | Right

datatype 'a symbol = Letter 'a | Marker dir (*Alternative: treat start/end of list as marker?*)

abbreviation left_marker :: "'a symbol" ("\<turnstile>") where
  "\<turnstile> \<equiv> Marker Left"

abbreviation right_marker :: "'a symbol" ("\<stileturn>") where
  "\<stileturn> \<equiv> Marker Right"

type_alias state = hf

record 'a dfa2 = states :: "state set"
                 init   :: "state"
                 acc    :: "state"
                 rej    :: "state"
                 nxt    :: "state \<Rightarrow> 'a symbol \<Rightarrow> state \<times> dir"

type_synonym 'a config = "'a symbol list \<times> state \<times> 'a symbol list"

locale dfa2 =
  fixes M :: "'a dfa2"
  assumes init:         "init M \<in> states M"
      and accept:       "acc M \<in> states M"
      and reject:       "rej M \<in> states M"
      and neq_final:    "acc M \<noteq> rej M"
      and finite:       "finite (states M)"
      and nxt:          "\<lbrakk>q \<in> states M; nxt M q x = (p, d)\<rbrakk> \<Longrightarrow> p \<in> states M"
      and left_nxt:     "\<lbrakk>q \<in> states M; nxt M q \<turnstile> = (p, d)\<rbrakk> \<Longrightarrow> d = Right"
      and right_nxt:    "\<lbrakk>q \<in> states M; nxt M q \<stileturn> = (p, d)\<rbrakk> \<Longrightarrow> d = Left"
      and final_nxt_r:  "\<lbrakk>x \<noteq> \<stileturn>; q = acc M \<or> q = rej M\<rbrakk> \<Longrightarrow> nxt M q x = (q, Right)"
      and final_nxt_l:  "q = acc M \<or> q = rej M \<Longrightarrow> nxt M q \<stileturn> = (q, Left)"
begin

abbreviation \<Sigma> :: "'a list \<Rightarrow>'a symbol list" where
  "\<Sigma> w \<equiv> map Letter w"

abbreviation marker_map :: "'a list \<Rightarrow> 'a symbol list" ("\<langle>_\<rangle>" 70) where
  "\<langle>w\<rangle> \<equiv> \<turnstile> # (\<Sigma> w) @ [\<stileturn>]"

abbreviation marker_mapl :: "'a list \<Rightarrow> 'a symbol list" ("\<langle>_\<langle>" 70) where
  "\<langle>w\<langle> \<equiv> \<turnstile> # (\<Sigma> w)"

abbreviation marker_mapr :: "'a list \<Rightarrow> 'a symbol list" ("\<rangle>_\<rangle>" 70) where
  "\<rangle>w\<rangle> \<equiv> (\<Sigma> w) @ [\<stileturn>]"

lemma mapl_app_mapr_eq_map [simp]: 
  "\<langle>u\<langle> @ \<rangle>v\<rangle> = \<langle>u @ v\<rangle>" by simp 

definition valid_input :: "'a symbol list \<Rightarrow> bool" where
  "valid_input xs \<equiv> \<exists>w. xs = \<langle>w\<rangle>" (*unused until now*)


inductive step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 55) where
  step_left[intro]:  "nxt M p a = (q, Left) \<Longrightarrow> (x # xs, p, a # ys) \<rightarrow> (xs, q, x # a # ys)" |
  step_right[intro]: "nxt M p a = (q, Right) \<Longrightarrow> (xs, p, a # ys) \<rightarrow> (a # xs, q, ys)"

inductive_cases step_foldedE[elim]: "a \<rightarrow> b"
inductive_cases step_leftE [elim]:  "(a#u, q, v) \<rightarrow> (u, p, a#v)"
inductive_cases step_rightE [elim]: "(u, q, a#v) \<rightarrow> (a#u, p, v)"

abbreviation stepn :: "nat \<Rightarrow> 'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
  "stepn n \<equiv> (step ^^ n)"

abbreviation steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

(*Induction rule analogous to rtranclp_induct2*)
lemmas config_induct = 
  rtranclp_induct[of _ "(ax, ay, az)" "(bx, by, bz)", split_rule, consumes 1, case_names refl step]

abbreviation reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>**\<close> 55) where
  "w \<rightarrow>** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>* c" 

definition language :: "'a list set" where
  "language \<equiv> {w. \<exists>u v.  w \<rightarrow>** (u, acc M, v)}" 

lemma unchanged_final:
  assumes "p = acc M \<or> p = rej M"
  shows "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> p = q"
proof (induction rule: config_induct)
  case (step a q' b c q'' d)
  then show ?case using assms
    by (smt (verit, ccfv_SIG) dfa2_axioms dfa2_def prod.inject step_foldedE)
qed simp

lemma unchanged_substrings:
  "(u, q, v) \<rightarrow>* (u', p, v') \<Longrightarrow> rev u @ v = rev u' @ v'"
proof (induction rule: config_induct) 
  case (step a q' b c q'' d)
  then obtain p' d' where qd_def: "nxt M q' (hd b) = (p', d')" by fastforce
  consider "d' = Left" | "d' = Right"
    using dir.exhaust by blast
  then show ?case
  proof cases
    case 1
    hence "(c, q'', d) = (tl a, p', hd a # b)"  
      using step(2) qd_def step.simps by force
    then show ?thesis
      using step.IH step.hyps(2) by fastforce
  next
    case 2
    hence "(c, q'', d) = (hd b # a, p', tl b)" using step(2) qd_def step.simps by force
    then show ?thesis using step step.cases by fastforce
  qed
qed simp

corollary unchanged_word:
  "([], init M, w) \<rightarrow>* (u, p, v) \<Longrightarrow> w = rev u @ v"
  using unchanged_substrings by force

lemma steps_app':
  assumes "(xs, q', v) \<rightarrow>* (ys, p, zs)"
  shows "(ws, q, u) \<rightarrow>* (xs, q', []) \<Longrightarrow> (ws, q, u @ v) \<rightarrow>* (ys, p, zs)"
   (*both config rules break here and raw rtranclp_induct does not work either
      (Solved below)*)
proof (induction arbitrary: ws q u rule: config_induct)
  oops

lemma steps_app:
  "(u, q, v) \<rightarrow>* (u', p, v') \<Longrightarrow> (u, q, v @ xs) \<rightarrow>* (u', p, v' @ xs)"
proof (induction rule: config_induct)
  case (step w q' x y p' z)
  from step(2) have "(w, q', x @ xs) \<rightarrow> (y, p', z @ xs)" by fastforce
  then show ?case using step(3) by simp
qed simp

corollary steps_extend:
  assumes "(ws, q, u) \<rightarrow>* (xs, q', [])"
      and "(xs, q', v) \<rightarrow>* (ys, p, zs)"
    shows "(ws, q, u @ v) \<rightarrow>* (ys, p, zs)"
  using assms steps_app by (metis (no_types, lifting) append_Nil rtranclp_trans)
  
end

locale dfa2_transition = dfa2 + (*there's probably a better alternative than a separate locale*)
  fixes x :: "'a list"
  assumes "x \<noteq> []"
begin 

inductive left_step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L\<close> 55) where
  lstep [intro]: "\<lbrakk>(ys, q, zs) \<rightarrow> (ys', p, zs')
                  ; length ys < length (\<langle>x\<langle>); length ys' < length (\<langle>x\<langle>)\<rbrakk> 
      \<Longrightarrow> (ys, q, zs) \<rightarrow>\<^sup>L (ys', p, zs')"

inductive_cases lstepE [elim]: "c1 \<rightarrow>\<^sup>L c2"

notation (ASCII) left_step (infix \<open>\<rightarrow>^L\<close> 55)

abbreviation left_steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L*\<close> 55) where
  "left_steps \<equiv> left_step\<^sup>*\<^sup>*" (*Possible problem: reflexive case holds 
                                  even when config is not in x*)

abbreviation left_reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L**\<close> 55) where
  "w \<rightarrow>\<^sup>L** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>L* c" 

inductive_cases lstepsE [elim]: "c1 \<rightarrow>\<^sup>L* c2"

lemma left_steps_impl_steps [elim]:
  assumes "c1 \<rightarrow>\<^sup>L* c2"
  obtains "c1 \<rightarrow>* c2" (*Is this bad usage of obtains? I
                       used it in order to be able to use this as an elim rule
                      if it is not: when in general to use elims?*)
proof 
  from assms show "c1 \<rightarrow>* c2"
  proof (induction rule: rtranclp_induct)
    case (step y z)
    from step(2) have "y \<rightarrow> z" by blast
    then show ?case using step(3) by simp
  qed simp
qed

lemma left_steps_impl_lt_x: 
  "\<lbrakk>(ys, q, zs) \<rightarrow>\<^sup>L* (ys', p, zs'); length ys < length (\<langle>x\<langle>)\<rbrakk> \<Longrightarrow> length ys' < length (\<langle>x\<langle>)"
  by (induction rule: config_induct) auto

lemma lt_len_app:
  assumes "m < length xs"
  obtains ys zs where "length ys = m" "ys @ zs = xs" using assms 
  by (metis add_diff_cancel_right' append_take_drop_id le_iff_add length_drop length_rev
      order_less_imp_le rev_eq_append_conv)

lemma star_lstar_impl_substring_x:
  assumes nsteps: "x @ z \<rightarrow>** (xs, q, zs)"
      and in_x:   "length xs < length (\<langle>x\<langle>)"
      and lsteps: "(xs, q, zs) \<rightarrow>\<^sup>L* (as, p, bs)"
  obtains u where " rev as @ u = \<langle>x\<langle>" "u @ \<rangle>z\<rangle> = bs" 
proof -
  from lsteps show thesis
  proof (induction arbitrary: xs q zs rule: config_induct)
    case refl 
    from unchanged_word nsteps lsteps have app: "\<langle>x @ z\<rangle> = rev as @ bs"
      by (metis left_steps_impl_steps unchanged_substrings)
    moreover from this left_steps_impl_lt_x[OF lsteps in_x]
    obtain x' where "rev as @ x' = \<langle>x\<langle>" "x' @ \<rangle>z\<rangle> = bs"
    proof -
      print_theorems
      from left_steps_impl_lt_x[OF lsteps in_x] lt_len_app
      obtain xs xs' where "length xs = length as" and xapp: "xs @ xs' = \<langle>x\<langle>" by blast
      moreover from this have "length (xs' @ \<rangle>z\<rangle>) = length bs" using app 
        by (smt (verit) append_assoc append_eq_append_conv length_rev
            mapl_app_mapr_eq_map) 
      ultimately have xs_is_rev: "xs = rev as" 
        by (smt (verit, ccfv_SIG) app append_assoc append_eq_append_conv
            dfa2.mapl_app_mapr_eq_map dfa2_axioms)
      then have "xs' @ \<rangle>z\<rangle> = bs" using xapp app 
        by (metis (no_types, lifting) append_assoc mapl_app_mapr_eq_map
            same_append_eq)
      thus thesis using that xs_is_rev xapp by presburger 
    qed
    ultimately show ?case using that by simp
  qed blast
qed

corollary init_lstar_impl_substring_x:
  assumes "x @ z \<rightarrow>\<^sup>L** (xs, q, zs)"
  obtains u where " rev xs @ u = \<langle>x\<langle>" "u @ \<rangle>z\<rangle> = zs"
  using star_lstar_impl_substring_x assms
  by (metis length_greater_0_conv list.discI list.size(3) rtranclp.rtrancl_refl)


inductive T :: "state option \<Rightarrow> state option \<Rightarrow> bool" where
  "\<lbrakk>\<langle>x\<rangle> = a # xs; x @ z \<rightarrow>\<^sup>L** (xs, q, a # \<rangle>z\<rangle>); (xs, q, a # \<rangle>z\<rangle>) \<rightarrow> (\<langle>x\<langle>, p, \<rangle>z\<rangle>)\<rbrakk>
    \<Longrightarrow> T None (Some q)" |
  "\<lbrakk>\<langle>x\<rangle> = a # xs;
    (\<langle>x\<langle>, q', \<rangle>z\<rangle>) \<rightarrow> (xs, q, a # \<rangle>z\<rangle>); 
    (xs, q, a # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (xs, p, a # \<rangle>z\<rangle>); 
    (xs, p, a # \<rangle>z\<rangle>) \<rightarrow> (\<langle>x\<langle>, q'', \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T (Some q) (Some p)"

(*TODO: Check/expand defs*)

end

theorem two_way_dfa_lang_regular:
  assumes "dfa2 M"
  shows "regular (dfa2.language M)"
  \<proof>

end
