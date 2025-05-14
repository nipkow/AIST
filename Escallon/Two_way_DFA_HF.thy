theory Two_way_DFA_HF
  imports "Finite_Automata_HF.Finite_Automata_HF" "HOL-IMP.Star" (*Should I use a different
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

abbreviation marker_map :: "'a list \<Rightarrow> 'a symbol list" ("\<langle>_\<rangle>" 60) where
  "\<langle>w\<rangle> \<equiv> \<turnstile> # (\<Sigma> w) @ [\<stileturn>]"

definition valid_input :: "'a symbol list \<Rightarrow> bool" where
  "valid_input xs \<equiv> \<exists>w. xs = \<langle>w\<rangle>"


inductive step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 55) where
  step_left[intro]:  "nxt M p a = (q, Left) \<Longrightarrow> (x # xs, p, a # ys) \<rightarrow> (xs, q, x # a # ys)" |
  step_right[intro]: "nxt M p a = (q, Right) \<Longrightarrow> (xs, p, a # ys) \<rightarrow> (a # xs, q, ys)"

inductive_cases step_foldedE[elim]: "a \<rightarrow> b"
inductive_cases step_leftE [elim]:  "(a#u, q, v) \<rightarrow> (u, p, a#v)"
inductive_cases step_rightE [elim]: "(u, q, a#v) \<rightarrow> (a#u, p, v)"

abbreviation steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55) where
  "steps \<equiv> star step"



definition language :: "'a list set" where
  "language \<equiv> {w. ([], init M, \<langle>w\<rangle>) \<rightarrow>* ( \<turnstile>#(\<Sigma> w), acc M, [\<stileturn>])}"

inductive nstep :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" where
  nstep_refl [intro]: "nstep c 0 c" |
  nstep_step [intro]: "\<lbrakk>c\<^sub>1 \<rightarrow> c\<^sub>2; nstep c\<^sub>2 n c\<^sub>3\<rbrakk> \<Longrightarrow> nstep c\<^sub>1 (Suc n) c\<^sub>3"

inductive_cases nstep_reflE [elim]: "nstep c\<^sub>1 0 c\<^sub>2"
inductive_cases nstep_stepSE [elim]: "nstep c\<^sub>1 (Suc n) c\<^sub>2"


lemma steps_equiv_nstep: "c\<^sub>1 \<rightarrow>* c\<^sub>2 \<longleftrightarrow> (\<exists>n. nstep c\<^sub>1 n c\<^sub>2)" 
proof
  show "\<exists>n. nstep c\<^sub>1 n c\<^sub>2 \<Longrightarrow> c\<^sub>1 \<rightarrow>* c\<^sub>2" 
  proof -
    assume "\<exists>n. nstep c\<^sub>1 n c\<^sub>2"
    then obtain n where "nstep c\<^sub>1 n c\<^sub>2" by blast
    thus "c\<^sub>1 \<rightarrow>* c\<^sub>2"
    by (induction rule: nstep.induct) (simp add: star.step)+
  qed     
qed (induction rule: star.induct, blast+)

lemma unchanged_final:
  assumes "p = acc M \<or> p = rej M"
  shows   "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> q = p" 
    by (induction "(u, p, v)" "(u', q, v')" arbitrary: u v rule: star.induct) 
     (simp, (smt (verit) assms final_nxt_l final_nxt_r prod.inject step.simps))

lemma unchanged_substrings:
  "(u, q, v) \<rightarrow>* (u', p, v') \<Longrightarrow> rev u @ v = rev u' @ v'"
proof (induction "(u, q, v)" "(u', p, v')" arbitrary: u q v rule: star.induct)
  case (step y)
  then obtain q' d where qd_def: "nxt M q (hd v) = (q', d)" by fastforce
  consider "d = Left" | "d = Right"
    using dir.exhaust by blast
  then show ?case 
  proof cases
    case 1
    hence y_eq: "y = (tl u, q', hd u # v)" 
      using step(1) qd_def step.simps by fastforce
    then show ?thesis
      using step.hyps(1,3) step.simps by auto
  next
    case 2
    hence "y = (hd v # u, q', tl v)" 
      using step(1) qd_def step.simps by fastforce
    then show ?thesis
      using step step.cases by fastforce
  qed
qed simp

corollary unchanged_word:
  "([], init M, w) \<rightarrow>* (u, p, v) \<Longrightarrow> w = rev u @ v"
  using unchanged_substrings by force

lemma steps_app:
  assumes "(xs, q', v) \<rightarrow>* (ys, p, zs)"
  shows "(ws, q, u) \<rightarrow>* (xs, q', []) \<Longrightarrow> (ws, q, u @ v) \<rightarrow>* (ys, p, zs)"
proof (induction "(ws, q, u)" "(xs, q', ([]::'a symbol list))"  arbitrary: ws q u rule: star.induct)
  case (step y)
  then obtain ws' q'' u' where y_def: "y = (ws', q'', u')" by auto
  from step(1) y_def have "(ws, q, u @ v) \<rightarrow> (ws', q'', u' @ v)" by force
  then show ?case by (simp add: star.step step.hyps(3) y_def)
qed (use assms in simp)

end

locale dfa2_transition = dfa2 + (*there's probably a better alternative than a separate locale*)
  fixes x :: "'a symbol list"
  assumes "x \<noteq> []"
begin 

inductive left_step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L\<close> 55) where
  lstep [intro]: "\<lbrakk>(ys, q, zs) \<rightarrow> (ys', p, zs'); length ys < length x; length ys' < length x\<rbrakk> 
      \<Longrightarrow> (ys, q, zs) \<rightarrow>\<^sup>L (ys', p, zs')"

inductive_cases lstepE [elim]: "c1 \<rightarrow>\<^sup>L c2"

notation (ASCII) left_step (infix \<open>\<rightarrow>^L\<close> 55)

abbreviation left_steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L*\<close> 55) where
  "left_steps \<equiv>   star left_step" (*Possible problem: reflexive case holds 
                                  even when config is not in x*)

inductive_cases lstepsE [elim]: "c1 \<rightarrow>\<^sup>L* c2"

lemma left_steps_impl_steps [elim]:
  assumes "c1 \<rightarrow>\<^sup>L* c2"
  obtains "c1 \<rightarrow>* c2" (*Is this bad usage of obtains? I
                       used it in order to be able to use this as an elim rule*)
proof 
  from assms show "c1 \<rightarrow>* c2"
  proof (induction c1 c2 rule: star.induct)
    case (step x y z)
    from step(1) have "x \<rightarrow> y" by blast
    then show ?case using step(3) by (metis star.simps)
  qed simp
qed

lemma left_steps_impl_lt_x: 
  "\<lbrakk>(ys, q, zs) \<rightarrow>\<^sup>L* (ys', p, zs'); length ys < length x\<rbrakk> \<Longrightarrow> length ys' < length x"
  by (induction "(ys, q, zs)" "(ys', p, zs')" arbitrary: ys q zs ys' rule: star.induct) auto

lemma star_lstar_impl_substring_x:
  assumes nsteps: "([], init M, x @ z) \<rightarrow>* (xs, q, zs)"
      and in_x:   "length xs < length x"
      and lsteps: "(xs, q, zs) \<rightarrow>\<^sup>L* (as, p, bs)"
  obtains u where " rev as @ u = x" "u @ z = bs" 
proof -
  from lsteps show ?thesis
  proof (induction "(xs, q, zs)" "(as, p, bs)" arbitrary: xs q zs rule: star.induct)
    case refl 
    from unchanged_word nsteps lsteps have app: "x @ z = rev as @ bs"
      by (metis left_steps_impl_steps unchanged_substrings)
    moreover from this  
    obtain x' where "rev as @ x' = x" "x' @ z = bs" 
    proof -
      have "length bs > length z"
      proof (rule ccontr)
        assume "\<not>?thesis"
        hence "length (rev as @ bs) < length (x @ z)" using left_steps_impl_lt_x[OF lsteps in_x]
          by simp
        thus False using app left_steps_impl_lt_x[OF lsteps in_x] by simp
      qed
      then obtain x' where "length bs = length x' + length z" "x' @ z = bs" 
        using app left_steps_impl_lt_x[OF lsteps in_x]
        by (metis append_eq_append_conv2 length_append not_add_less2)
      moreover from this have "rev as @ x' = x" using app by auto
      ultimately show thesis using that by simp
    qed
    ultimately show ?case using that by simp
  qed blast
qed

corollary init_lstar_impl_substring_x:
  assumes "([], init M, x @ z) \<rightarrow>\<^sup>L* (xs, q, zs)"
  obtains u where " rev xs @ u = x" "u @ z = zs"
  using star_lstar_impl_substring_x assms by blast


inductive T :: "state option \<Rightarrow> state option \<Rightarrow> bool" where
  "\<lbrakk>x = a # xs; ([], init M, x @ z) \<rightarrow>\<^sup>L* (xs, q, a # z); (xs, q, a # z) \<rightarrow> (x, p, z)\<rbrakk>
    \<Longrightarrow> T None (Some q)" |
  "\<lbrakk>x = a # xs;
    (x, q', z) \<rightarrow> (xs, q, a # z); 
    (xs, q, a # z) \<rightarrow>\<^sup>L* (xs, p, a # z); 
    (xs, p, a # z) \<rightarrow> (x, q'', z)\<rbrakk> \<Longrightarrow> T (Some q) (Some p)"

(*TODO: Check/expand defs*)

end

theorem two_way_dfa_lang_regular:
  assumes "dfa2 M"
  shows "regular (dfa2.language M)"
  \<proof>

end
