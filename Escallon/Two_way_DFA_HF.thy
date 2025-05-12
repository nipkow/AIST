theory Two_way_DFA_HF
  imports "HereditarilyFinite.Ordinal" "HOL-IMP.Star"
begin

datatype dir = Left | Right

datatype 'a symbol = Letter 'a | Marker dir

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


inductive step :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 55) where
  step_left[intro]:  "nxt M p a = (q, Left) \<Longrightarrow> (x # xs, p, a # ys) \<rightarrow> (xs, q, x # a # ys)" |
  step_right[intro]: "nxt M p a = (q, Right) \<Longrightarrow> (xs, p, a # ys) \<rightarrow> (a # xs, q, ys)"

inductive_cases step_foldedE[elim]: "a \<rightarrow> b"
inductive_cases step_leftE [elim]:  "(a#u, q, v) \<rightarrow> (u, p, a#v)"
inductive_cases step_rightE [elim]: "(u, q, a#v) \<rightarrow> (a#u, p, v)"

abbreviation steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55) where
  "steps \<equiv> star step"

abbreviation \<Sigma> :: "'a list \<Rightarrow>'a symbol list" where
  "\<Sigma> w \<equiv> map Letter w"

abbreviation marker_map :: "'a list \<Rightarrow> 'a symbol list" ("\<langle>_\<rangle>" 60) where
  "\<langle>w\<rangle> \<equiv> \<turnstile> # (\<Sigma> w) @ [\<stileturn>]"

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
  moreover from step(3)[OF y_def] have "(ws', q'', u' @ v) \<rightarrow>* (ys, p, zs)" .
  ultimately show ?case by (simp add: star.step)
qed (use assms in simp)
 
 
  
  

end