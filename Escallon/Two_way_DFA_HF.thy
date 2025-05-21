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

      (*Needed?*)
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

lemma mapl_app_mapr_eq_map: 
  "\<langle>u\<langle> @ \<rangle>v\<rangle> = \<langle>u @ v\<rangle>" by simp

definition valid_input :: "'a symbol list \<Rightarrow> bool" where
  "valid_input xs \<equiv> \<exists>w. xs = \<langle>w\<rangle>" (*unused until now*)


inductive step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 55) where
  step_left[intro]:  "nxt M p a = (q, Left) \<Longrightarrow> (x # xs, p, a # ys) \<rightarrow> (xs, q, x # a # ys)" |
  step_right[intro]: "nxt M p a = (q, Right) \<Longrightarrow> (xs, p, a # ys) \<rightarrow> (a # xs, q, ys)"

inductive_cases step_foldedE[elim]: "a \<rightarrow> b"
inductive_cases step_leftE [elim]:  "(a#u, q, v) \<rightarrow> (u, p, a#v)"
inductive_cases step_rightE [elim]: "(u, q, a#v) \<rightarrow> (a#u, p, v)"

lemma step_impl_in_states[intro]: (*Should these be intros?*)
  assumes "q \<in> states M"
          "(u, q, v) \<rightarrow> (u', p, v')"
        shows "p \<in> states M"
  using assms dfa2_def dfa2_axioms
  by (smt (verit, del_insts) old.prod.inject step_foldedE)

abbreviation stepn :: "nat \<Rightarrow> 'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
  "stepn n \<equiv> (step ^^ n)"

abbreviation steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

(*Induction rule analogous to rtranclp_induct2*)
lemma rtranclp_induct3[consumes 1, case_names refl step]:
  "\<lbrakk>r\<^sup>*\<^sup>* (ax, ay, az) (bx, by, bz); P ax ay az;
     \<And>u q v x p z.
        \<lbrakk>r\<^sup>*\<^sup>* (ax, ay, az) (u, q, v); r (u, q, v) (x, p, z); P u q v\<rbrakk>
        \<Longrightarrow> P x p z\<rbrakk>
    \<Longrightarrow> P bx by bz"
  by (rule rtranclp_induct[of _ "(ax, ay, az)" "(bx, by, bz)", 
        split_rule])

abbreviation reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>**\<close> 55) where
  "w \<rightarrow>** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>* c" 

lemma steps_impl_in_states:
  assumes "p \<in> states M"
    shows "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> q \<in> states M"
    by (induction rule: rtranclp_induct3) (use assms in auto)

corollary reachable_impl_in_states:
  assumes "w \<rightarrow>** (u, q, v)"
  shows   "q \<in> states M"
  using assms dfa2_def dfa2_axioms by (blast intro: steps_impl_in_states)

definition language :: "'a list set" where
  "language \<equiv> {w. \<exists>u v.  w \<rightarrow>** (u, acc M, v)}" 

lemma unchanged_final:
  assumes "p = acc M \<or> p = rej M"
  shows "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> p = q"
proof (induction rule: rtranclp_induct3)
  case (step a q' b c q'' d)
  then show ?case using assms
    by (smt (verit, ccfv_SIG) dfa2_axioms dfa2_def prod.inject step_foldedE)
qed simp

lemma unchanged_substrings:
  "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> rev u @ v = rev u' @ v'"
proof (induction rule: rtranclp_induct3) 
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
  "([], p, w) \<rightarrow>* (u, q, v) \<Longrightarrow> w = rev u @ v"
  using unchanged_substrings by force


lemma steps_app [simp, intro]:
  "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> (u, p, v @ xs) \<rightarrow>* (u', q, v' @ xs)"
proof (induction rule: rtranclp_induct3)
  case (step w q' x y p' z)
  from step(2) have "(w, q', x @ xs) \<rightarrow> (y, p', z @ xs)" by fastforce
  then show ?case using step(3) by simp
qed simp

corollary steps_extend:
  assumes "(ws, p, u) \<rightarrow>* (xs, p', [])"
      and "(xs, p', v) \<rightarrow>* (ys, q, zs)"
    shows "(ws, p, u @ v) \<rightarrow>* (ys, q, zs)"
  using assms steps_app by (metis (no_types, lifting) append_Nil rtranclp_trans)
  
end


locale dfa2_transition = dfa2 + (*there's probably a better alternative than a separate locale*)
  fixes x :: "'a list"
  assumes "x \<noteq> []"
begin 

definition x_init :: "'a symbol list" where
  "x_init \<equiv> butlast (\<langle>x\<langle>)"

definition x_end :: "'a symbol" where
  "x_end \<equiv> last (\<langle>x\<langle>)"

lemmas x_defs = x_init_def x_end_def

lemma x_is_init_app_end:
  "\<langle>x\<langle> = x_init @ [x_end]" unfolding x_defs by simp

definition left_config :: "'a config \<Rightarrow> bool" where
  "left_config c \<equiv> \<exists>u q v. c = (u, q, v) \<and> length u < length (\<langle>x\<langle>)"

definition right_config :: "'a config \<Rightarrow> bool" where
  "right_config c \<equiv> \<exists>u q v. c = (u, q, v) \<and> length u \<ge> length (\<langle>x\<langle>)"

inductive left_step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L\<close> 55) where
  lstep [intro]: "\<lbrakk>x @ z \<rightarrow>** c1; c1 \<rightarrow> c2; left_config c1; left_config c2\<rbrakk> 
      \<Longrightarrow> c1 \<rightarrow>\<^sup>L c2"

inductive_cases lstepE [elim]: "c1 \<rightarrow>\<^sup>L c2"

(*A right_step definition seems to be necessary to define T*)
inductive right_step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>R\<close> 55) where
  rstep [intro]: "\<lbrakk>x @ z \<rightarrow>** c1; c1 \<rightarrow> c2;
                  right_config c1; right_config c2\<rbrakk> 
      \<Longrightarrow> c1 \<rightarrow>\<^sup>R c2"

inductive_cases rstepE [elim]: "c1 \<rightarrow>\<^sup>R c2"

notation (ASCII) left_step (infix \<open>\<rightarrow>^L\<close> 55)
notation (ASCII) right_step (infix \<open>\<rightarrow>^R\<close> 55)


abbreviation left_steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L*\<close> 55) where
  "left_steps \<equiv> left_step\<^sup>*\<^sup>*" (*Possible problem: reflexive case holds 
                                  even when config is not in x*)

abbreviation right_steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>R*\<close> 55) where
  "right_steps \<equiv> right_step\<^sup>*\<^sup>*"

abbreviation left_reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L**\<close> 55) where
  "w \<rightarrow>\<^sup>L** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>L* c" 

inductive right_reachable :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>R**\<close> 55) where
  "\<lbrakk>x @ z \<rightarrow>** c1; 
    c1 \<rightarrow>\<^sup>L* (rev x_init, p, x_end # \<rangle>z\<rangle>); (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>);
    (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<rightarrow>\<^sup>R* c2\<rbrakk> \<Longrightarrow> c1 \<rightarrow>\<^sup>R** c2"
 (*Right reachability: c1 is reachable and can reach c2 with a single boundary crossing
    (is reachability of c1 too weak?)*)


lemma left_steps_impl_steps [dest]:
  assumes "c1 \<rightarrow>\<^sup>L* c2"
    shows "c1 \<rightarrow>* c2"
proof -
  from assms show "c1 \<rightarrow>* c2"
    by (induction rule: rtranclp_induct) auto
qed

lemma right_steps_impl_steps [dest]:
  assumes "c1 \<rightarrow>\<^sup>R* c2"
    shows "c1 \<rightarrow>* c2"
proof -
  from assms show "c1 \<rightarrow>* c2"
    by (induction rule: rtranclp_induct) auto
qed

lemma left_steps_impl_left_config[dest]:
  "\<lbrakk>c1 \<rightarrow>\<^sup>L* c2; left_config c1\<rbrakk> 
    \<Longrightarrow> left_config c2"
  by (induction rule: rtranclp_induct) auto

lemma left_reachable_impl_left_config:
  "w \<rightarrow>\<^sup>L** c \<Longrightarrow> left_config c" 
  using left_config_def left_steps_impl_left_config by auto
  

lemma right_steps_impl_right_config[dest]: 
  "\<lbrakk>c1 \<rightarrow>\<^sup>R* c2; right_config c1\<rbrakk> 
    \<Longrightarrow> right_config c2"
  by (induction rule: rtranclp_induct) auto

proposition list_deconstruct1:
  assumes "m \<le> length xs"
  obtains ys zs where "length ys = m" "ys @ zs = xs" using assms 
  by (metis add_diff_cancel_right' append_take_drop_id le_iff_add length_drop 
      length_rev rev_eq_append_conv)


proposition list_deconstruct2:
  assumes "m \<le> length xs"
  obtains ys zs where "length zs = m" "ys @ zs = xs"
proof -
  from assms have "m \<le> length (rev xs)" by simp
  then obtain ys zs where yz_defs: "length ys = m" "ys @ zs = rev xs"
    using list_deconstruct1 by blast
  hence "rev zs @ rev ys = xs" by (simp add: append_eq_rev_conv)
  with yz_defs show thesis using that by auto
qed

lemmas list_deconstruct = list_deconstruct1 list_deconstruct2
  (*These propositions were necessary for the two following lemmas.*)


lemma star_lstar_impl_substring_x:
  assumes nsteps: "x @ z \<rightarrow>** (u, p, v)"
      and in_x:   "length u < length (\<langle>x\<langle>)"
      and lsteps: "(u, p, v) \<rightarrow>\<^sup>L* (u', q, v')"
  obtains y where " rev u' @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v'" 
proof -
  have leftconfig: "left_config (u, p, v)" unfolding left_config_def using in_x by blast
  hence u'_lt_x: "length u' < length (\<langle>x\<langle>)" using lsteps
    using left_config_def by force
  from lsteps show thesis
  proof (induction arbitrary: u p v rule: rtranclp_induct3)
    case refl 
    from unchanged_word nsteps lsteps have app: "\<langle>x @ z\<rangle> = rev u' @ v'"
      by (metis left_steps_impl_steps unchanged_substrings)
    moreover from this u'_lt_x
    obtain y where "rev u' @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v'"
    proof -
      from u'_lt_x list_deconstruct1
      obtain xs ys where "length xs = length u'" and xapp: "xs @ ys = \<langle>x\<langle>"
        using Nat.less_imp_le_nat by metis
      moreover from this have "length (ys @ \<rangle>z\<rangle>) = length v'" using app 
        by (smt (verit) append_assoc append_eq_append_conv length_rev
            mapl_app_mapr_eq_map) 
      ultimately have xs_is_rev: "xs = rev u'" 
        by (smt (verit, ccfv_SIG) app append_assoc append_eq_append_conv
            dfa2.mapl_app_mapr_eq_map dfa2_axioms)
      then have "ys @ \<rangle>z\<rangle> = v'" using xapp app 
        by (metis (no_types, lifting) append_assoc mapl_app_mapr_eq_map
            same_append_eq)
      thus thesis using that xs_is_rev xapp by presburger
    qed
    ultimately show ?case using that by simp
  qed blast
qed

corollary init_lstar_impl_substring_x:
  assumes "x @ z \<rightarrow>\<^sup>L** (u, q, v)"
  obtains y where " rev u @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v"
  using star_lstar_impl_substring_x assms left_config_def 
    left_reachable_impl_left_config by blast
  

lemma star_rstar_impl_substring_z:
  assumes nsteps: "x @ z \<rightarrow>** (u, p, v)"
      and not_in_x:   "length u \<ge> length (\<langle>x\<langle>)"
      and rsteps: "(u, p, v) \<rightarrow>\<^sup>R* (u', q, v')"
    obtains y where " rev (\<langle>x\<langle> @ y) = u'" "y @ v' = \<rangle>z\<rangle>"
proof -
  have "right_config (u, p, v)" using not_in_x right_config_def by simp
  with rsteps right_config_def have u'_ge_x: "length (\<langle>x\<langle>) \<le> length u'"
    using right_steps_impl_right_config by force
  from rsteps show thesis
  proof (induction arbitrary: u p v rule: rtranclp_induct3)
    case refl
    from unchanged_word nsteps rsteps have app: "\<langle>x @ z\<rangle> = rev u' @ v'"
      by (metis right_steps_impl_steps unchanged_substrings)
    moreover from this u'_ge_x
    obtain x' where "rev (\<langle>x\<langle> @ x') = u'" "x' @ v' = \<rangle>z\<rangle>"
    proof -
      have "length v' \<le> length (\<rangle>z\<rangle>)" 
      proof (rule ccontr)
        assume "\<not>?thesis"
        hence "length v' > length (\<rangle>z\<rangle>)" by simp
        with u'_ge_x
        have "length (rev u' @ v') > length (\<langle>x @ z\<rangle>)" by simp
        thus False using app by (metis nat_less_le)
      qed
      from list_deconstruct2[OF this]
      obtain xs ys where "length ys = length v'" and zapp: "xs @ ys = \<rangle>z\<rangle>"
        by metis
      moreover from this have "length (\<langle>x\<langle> @ xs) = length u'" using app
        by (metis (no_types, lifting) append.assoc append_eq_append_conv length_rev
            mapl_app_mapr_eq_map)
      ultimately have ys_is_v': "ys = v'"
        by (metis app append_assoc append_eq_append_conv mapl_app_mapr_eq_map)
      then have x_app_xs_eq_rev_u': "\<langle>x\<langle> @ xs = rev u'" using zapp app
        by (metis (no_types, lifting) append_assoc append_eq_append_conv
            dfa2.mapl_app_mapr_eq_map dfa2_axioms)
      hence "rev (\<langle>x\<langle> @ xs) = u'" by simp
      thus thesis using ys_is_v' zapp that by presburger
    qed
    ultimately show ?case using that by simp
  qed blast
qed

inductive T :: "state option \<Rightarrow> state option \<Rightarrow> bool" where
  init_tr[intro]: "\<lbrakk>x @ z \<rightarrow>\<^sup>L** (rev x_init, q, x_end # \<rangle>z\<rangle>); 
              (rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T None (Some q)" |

  init_no_tr[intro]: "\<nexists>q. x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<Longrightarrow> T None None" |

  some_tr[intro]: "\<lbrakk>x @ z \<rightarrow>** c; c \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>); 
              (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, p, x_end # \<rangle>z\<rangle>); 
              (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q, x_end # \<rangle>z\<rangle>); 
              (rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T (Some p) (Some q)" |

  no_tr[intro]:   "\<lbrakk>x @ z \<rightarrow>** c; c \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>); 
              (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q, x_end # \<rangle>z\<rangle>); 
              \<nexists>q'. (rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z\<rangle>) \<and>
              (rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T (Some q) None" 


inductive_cases init_trE[elim]: "T None q"
inductive_cases some_trE[elim]: "T (Some q) (Some p)"
inductive_cases no_trE[elim]:   "T (Some q) None"


lemma T_impl_in_states:
  assumes "T p q"
  shows "p = Some p' \<Longrightarrow> p' \<in> states M" 
        "q = Some q' \<Longrightarrow> q' \<in> states M"
  using assms
  by (smt (verit) T.cases init option.discI option.inject right_steps_impl_steps
      rtranclp_trans step_impl_in_states steps_impl_in_states left_steps_impl_steps)+

lemma T_p_Some_impl_reachable:
  assumes "T p (Some q)"
  obtains u v where "x @ z \<rightarrow>** (u, q, v)" sorry

lemma left_acc_impl_T_Some_acc:
  assumes "x @ z \<rightarrow>** (u, acc M, v)"
          "left_config (u, acc M, v)"
  obtains q where "T q (Some (acc M))" sorry

lemma in_lang_impl_acc_right_reachable:
  assumes "x @ z \<in> language"
  obtains u p v v' y where 
    "x @ z \<rightarrow>** (u, p, v)" "left_config (u, p, v)" "(u, p, v) \<rightarrow>\<^sup>R** (v', acc M, y)"
  sorry (*TODO: right-reachable implies left-reachable config that reaches end config*)




(*Needed?*)
lemma T_func:
  assumes "T p q"
          "T p q'"
        shows "q = q'" sorry (*TODO*)

lemma T_func_conv:
  assumes "T p q"
          "q \<noteq> q'"
        shows "\<not>T p q'" using assms T_func by auto 

lemma T_none_none_iff_not_none_some:
  "(\<exists>q. T None (Some q)) \<longleftrightarrow> \<not>T None None"
proof
  assume "\<exists>q. T None (Some q)"
  then show "\<not> T None None"
  proof 
    fix q
    assume "T None (Some q)"
    thus "\<not> T None None"
      using T_func by auto (*Can also be shown without T_func, although the proof is a bit more
                          complex*)
  qed
next
  assume "\<not> T None None"
  then obtain q z where "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by blast
  hence "T None (Some q)" sorry (*Infinite descent?*)
  thus "\<exists>q. T None (Some q)" by blast
qed

end


context dfa2_transition
begin

definition \<T> :: "(state option \<times> state option) set" where
  "\<T> \<equiv> {(q, p). T q p}"
(*TODO*)

lemma \<T>_subset_states_none:
  "\<T> \<subseteq> ({Some q | q. q \<in> states M} \<union> {None}) \<times> ({Some q | q. q \<in> states M} \<union> {None})"
    (is "_ \<subseteq> ?S \<times> _")
proof
    fix qp :: "state option \<times> state option"
    assume "qp \<in> \<T>"
    then obtain q p where qp_def: "qp = (q, p)" "(q, p) \<in> \<T>"
      by (metis surj_pair)
    have "(q, p) \<in> ?S \<times> ?S"
      using qp_def(2) dfa2_transition.T_impl_in_states[OF dfa2_transition_axioms] unfolding \<T>_def 
      by fast      
    thus "qp \<in> ?S \<times> ?S" using qp_def by simp
qed

lemma Tset_finite: "finite \<T>" 
proof -
  let ?S = "{Some q | q. q \<in> states M} \<union> {None}"
  have "finite ?S" using finite by simp
  then show ?thesis using Finite_Set.finite_subset \<T>_subset_states_none by auto
qed

lemma \<T>_card_upperbound:
  "card \<T> \<le> (card (states M) + 1) ^ 2"
proof -
  let ?S = "{Some q | q. q \<in> states M} \<union> {None}"
  have card_eq: "card ?S = card (states M) + 1" 
  proof -
    have "card (states M) = card {Some q | q. q \<in> states M}"
    proof (rule bij_betw_same_card)
      show "bij_betw Some (states M) {Some q | q. q \<in> states M}" 
        by (smt (verit) bij_betwI' mem_Collect_eq option.inject)
    qed
    thus ?thesis using finite by auto
  qed
  from finite have "finite ?S" by simp
  hence "card \<T> \<le> card (?S \<times> ?S)" using \<T>_subset_states_none 
    by (meson card_mono finite_SigmaI)
  with card_eq show ?thesis using Groups_Big.card_cartesian_product
    by (metis power2_eq_square)
qed


lemma \<T>_finite_index:
  "finite (UNIV // \<T>)" (*Nontrivial(?) and not proved in the book*)
    (*Try: define leftlang as in Finite_Automata_HF and apply the same rule*)
  sorry


end

lemma T_eq_is_\<T>_eq:
  assumes "dfa2_transition M x"
          "dfa2_transition M y"
    shows "dfa2_transition.T M x = dfa2_transition.T M y \<longleftrightarrow> dfa2_transition.\<T> M x = dfa2_transition.\<T> M y"
  unfolding dfa2_transition.\<T>_def[OF assms(1)] dfa2_transition.\<T>_def[OF assms(2)]
  by fastforce


context dfa2
begin

abbreviation "T \<equiv> dfa2_transition.T M" 
abbreviation "left_reachable \<equiv> dfa2_transition.left_reachable M"
abbreviation "right_reachable \<equiv> dfa2_transition.right_reachable M"
abbreviation "left_config \<equiv> dfa2_transition.left_config"
abbreviation "right_config \<equiv> dfa2_transition.right_config"

theorem two_way_dfa_lang_regular:
  "regular language"
proof -
  fix x y :: "'a list"
  assume x_nempty: "x \<noteq> []"
     and y_nempty: "y \<noteq> []"
  with dfa2_axioms have transition_axioms: "dfa2_transition M x" "dfa2_transition M y"
    using dfa2_transition_def unfolding dfa2_transition_axioms_def by auto
  have "T x = T y \<Longrightarrow> \<forall>z. x @ z \<in> language \<longleftrightarrow> y @ z \<in> language"
  proof
    fix z
    assume T_eq: "T x = T y"
    show "x @ z \<in> language \<longleftrightarrow> y @ z \<in> language"
    proof
      assume "x @ z \<in> language"
      then obtain u v where x_acc_reachable: "x @ z \<rightarrow>** (u, acc M, v)" 
        unfolding language_def by blast
      consider "left_config x (u, acc M, v)" | "right_config x (u, acc M, v)"
        unfolding dfa2_transition.left_config_def[OF transition_axioms(1)]
                  dfa2_transition.right_config_def[OF transition_axioms(1)] 
        by fastforce
      thus "y @ z \<in> language"
      proof cases
        case 1
        then show ?thesis
        proof -
          from 1 obtain q where "T x q (Some (acc M))"
            using dfa2_transition.left_acc_impl_T_Some_acc[OF transition_axioms(1) 
                                                           x_acc_reachable]
            by blast
          with T_eq have "T y q (Some (acc M))" by presburger
          then show ?thesis using language_def 
                dfa2_transition.T_p_Some_impl_reachable[OF transition_axioms(2)]
            by (metis (mono_tags, lifting) mem_Collect_eq)
        qed
      next
        case 2
        then show ?thesis sorry
      qed
    next
      assume "y @ z \<in> language"
      show "x @ z \<in> language" sorry
    qed
  qed
  have "(\<forall>z. x @ z \<in> language \<longleftrightarrow> y @ z \<in> language) 
             \<longleftrightarrow> (x, y) \<in> eq_app_right language" unfolding eq_app_right_def by simp
  have "finite (UNIV // eq_app_right language)" 
    using dfa2_transition.\<T>_finite_index sorry
  then show ?thesis using L3_1 by auto
qed
  
end
end
