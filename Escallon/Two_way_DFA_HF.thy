theory Two_way_DFA_HF
  imports "Finite_Automata_HF.Finite_Automata_HF"
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

lemma \<Sigma>_distr:
  "\<Sigma> xs @ \<Sigma> ys = \<Sigma> (xs @ ys)" by simp

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

abbreviation steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

abbreviation stepn :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" where
  "stepn c n \<equiv> (step ^^ n) c"

notation stepn ("_ \<rightarrow>{_} _" 55)


(*Induction rule analogous to rtranclp_induct2*)
lemma rtranclp_induct3[consumes 1, case_names refl step]:
  "\<lbrakk>r\<^sup>*\<^sup>* (ax, ay, az) (bx, by, bz); P ax ay az;
     \<And>u p v x q z.
        \<lbrakk>r\<^sup>*\<^sup>* (ax, ay, az) (u, p, v); r (u, p, v) (x, q, z); P u p v\<rbrakk>
        \<Longrightarrow> P x q z\<rbrakk>
    \<Longrightarrow> P bx by bz"
  by (rule rtranclp_induct[of _ "(ax, ay, az)" "(bx, by, bz)", 
        split_rule])

abbreviation reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>**\<close> 55) where
  "w \<rightarrow>** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>* c" 

abbreviation nreachable :: "'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" where
  "nreachable w n c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>{n} c"

notation nreachable ("_ \<rightarrow>*{_} _" 55)

lemma steps_impl_in_states:
  assumes "p \<in> states M"
  shows "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> q \<in> states M"
  by (induction rule: rtranclp_induct3) (use assms nxt in auto)
 

corollary reachable_impl_in_states:
  assumes "w \<rightarrow>** (u, q, v)"
  shows   "q \<in> states M"
  using assms dfa2_def dfa2_axioms by (blast intro: steps_impl_in_states)

lemma step_length_diff:
  assumes "(u, p, v) \<rightarrow> (x, q, y)"
  shows "length v = Suc (length y) \<or> length y = Suc (length v)"
  using assms by force

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

lemma final_reaches_right_stepn:
  assumes "p = acc M \<or> p = rej M"
          "valid_input (ys @ zs)"
  shows "(xs, p, ys @ zs) \<rightarrow>{length ys} (rev ys @ xs, p, zs)"
  apply (induction ys arbitrary: xs)
   apply fastforce
  using assms unfolding valid_input_def 
  sorry

lemma step_butlast:
  assumes "(u, p, v) \<rightarrow> (u', q, v')"
          "v = a # b # cs"
    shows "(u, p, butlast v) \<rightarrow> (u', q, butlast v')" 
  using assms by cases auto

lemma steps_app [simp, intro]:
  "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> (u, p, v @ xs) \<rightarrow>* (u', q, v' @ xs)"
proof (induction rule: rtranclp_induct3) 
  case (step w q' x y p' z)
  from step(2) have "(w, q', x @ xs) \<rightarrow> (y, p', z @ xs)" by fastforce
  then show ?case using step(3) by simp
qed simp

lemma steps_prep: 
  "(u, p, v) \<rightarrow>* (u', q, v') \<Longrightarrow> (u @ xs, p, v) \<rightarrow>* (u' @ xs, q, v')"
proof (induction rule: rtranclp_induct3)
  case (step u' p' v' x q z)
  from step(2) have "(u' @ xs, p', v') \<rightarrow> (x @ xs, q, z)" by fastforce
  then show ?case using step(3) by simp
qed simp

corollary steps_extend:
  assumes "(ws, p, u) \<rightarrow>* (xs, p', [])"
      and "(xs, p', v) \<rightarrow>* (ys, q, zs)"
    shows "(ws, p, u @ v) \<rightarrow>* (ys, q, zs)"
  using assms steps_app by (metis (no_types, lifting) append_Nil rtranclp_trans)

lemma reachable_impl_notempty:
  assumes "w \<rightarrow>** (u, q, v)"
  shows "v \<noteq> []"
proof -
  from assms obtain n where "w \<rightarrow>*{n} (u, q, v)" 
    by (meson rtranclp_imp_relpowp)
  then show "v \<noteq> []"
  proof (induction n arbitrary: u q v)
    case (Suc n)
    from Suc(2) obtain x p y 
      where "w \<rightarrow>*{n} (x, p, y)" 
        and step: "(x, p, y) \<rightarrow> (u, q, v)" by auto
    with Suc(1) have "y \<noteq> []" by simp
    then consider a where "y = [a]" | a b ys where "y = a # b # ys" 
      by (meson remdups_adj.cases)
    then show "v \<noteq> []"
    proof cases
      case 1
      with unchanged_word have "a = \<stileturn>"
        by (metis \<open>((\<rightarrow>) ^^ n) ([], dfa2.init M, \<turnstile> # \<Sigma> w @ [\<stileturn>]) (x, p, y)\<close> append1_eq_conv append_Cons
            rtranclp_power)
      moreover from unchanged_word obtain b xs where "x = b # xs" 
        by (metis "1" \<open>((\<rightarrow>) ^^ n) ([], dfa2.init M, \<turnstile> # \<Sigma> w @ [\<stileturn>]) (x, p, y)\<close> append_Cons
            append_self_conv2 calculation list.exhaust rev.simps(1) rtranclp_power)
      ultimately have "(x, p, y) \<rightarrow> (xs, q, b # [a])" using right_nxt[of p q] 1 
        using \<open>((\<rightarrow>) ^^ n) ([], dfa2.init M, \<turnstile> # \<Sigma> w @ [\<stileturn>]) (x, p, y)\<close> init local.step
          relpowp_imp_rtranclp steps_impl_in_states by fastforce 
      then show ?thesis using step by fastforce
    next
      case 2
      then obtain n where "length y = Suc (Suc n)" by simp
      hence "length v = Suc (Suc (Suc n)) \<or> length v = Suc n" using step
        by force
      then show ?thesis by auto
    qed
  qed force
qed 


lemma acc_impl_reachable_substring:
  assumes "w \<rightarrow>** (u, acc M, v)"
          "xs \<noteq> []"
          "ys \<noteq> []"
  shows "v = xs @ ys \<Longrightarrow> (u, acc M, v) \<rightarrow>* (rev xs @ u, acc M, ys)"
  using assms 
proof (induction v arbitrary: u xs ys)
  case (Cons a v)
  consider b where "a = Letter b \<or> a = \<turnstile>" | "a = \<stileturn>"  by (metis dir.exhaust symbol.exhaust)
  then show ?case 
  proof cases
    case 1
    hence step: "(u, acc M, a # v) \<rightarrow> (a # u, acc M, v)" using final_nxt_r by auto
    with Cons(3) have reach: "w \<rightarrow>** (a # u, acc M, v)" by simp
    from this obtain xs' where xs'_def: "v = xs' @ ys" 
      by (metis Cons.prems(1,3) append_eq_Cons_conv)
    from xs'_def Cons(2) have "a # xs' = xs" by simp
    then show ?thesis using Cons Cons(1)[of xs' ys "a # u", OF xs'_def reach] step by fastforce
  next
    case 2
    note unchanged = unchanged_word[OF Cons(3)]
    have "v = []"
    proof -
      have "length u = length (\<langle>w\<langle>)"
      proof (rule ccontr)
        assume "length u \<noteq> length (\<langle>w\<langle>)"
        with unchanged obtain n where n_len: "n < length (\<langle>w\<langle>)"
                                  and n_idx: "(rev u @ a # v) ! n = \<stileturn>"
          using 2
          by (metis append_assoc length_Cons length_append length_append_singleton length_rev 
              length_tl linorder_neqE_nat list.sel(3) not_add_less1 nth_append_length)
        have "(\<langle>w\<rangle>) ! n \<noteq> \<stileturn>"
        proof -
          consider "n = 0" | "0 < n" by blast
          then show ?thesis
          proof cases
            case 1
            then show ?thesis by simp
          next
            case 2
            hence "(\<langle>w\<rangle>) ! n = (\<langle>w\<langle>) ! n" using n_len
              by (simp add: nth_append_left)
            also have "... = \<Sigma> w ! (n - 1)" using 2 by simp
            finally show ?thesis
              by (metis "2" One_nat_def Suc_less_eq Suc_pred length_Cons length_map n_len nth_map
                  symbol.distinct(1))
          qed
        qed
        with n_idx unchanged show False by argo 
      qed
      with unchanged have "length (a # v) = Suc 0" 
        by (metis add_left_cancel length_Cons length_append length_rev list.size(3,4))
      thus ?thesis by simp
    qed
    then show ?thesis using Cons 2 by (metis append_assoc snoc_eq_iff_butlast)
  qed
qed simp

end


locale dfa2_transition = dfa2 +
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
  lstep [intro]: "\<lbrakk>c1 \<rightarrow> c2; left_config c1; left_config c2\<rbrakk> 
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
  "left_steps \<equiv> left_step\<^sup>*\<^sup>*"

abbreviation left_stepn :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" where
  "left_stepn c1 n \<equiv> (left_step ^^ n) c1"

notation left_stepn ("_ \<rightarrow>\<^sup>L{_} _" 55)

abbreviation right_steps :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>R*\<close> 55) where
  "right_steps \<equiv> right_step\<^sup>*\<^sup>*"

abbreviation right_stepn :: "'a config \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" where
  "right_stepn c1 n \<equiv> (left_step ^^ n) c1"

notation right_stepn ("_ \<rightarrow>\<^sup>R{_} _" 55)

abbreviation left_reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>L**\<close> 55) where
  "w \<rightarrow>\<^sup>L** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>L* c" 

abbreviation left_nreachable :: "'a list \<Rightarrow> nat \<Rightarrow> 'a config \<Rightarrow> bool" where
  "left_nreachable w n c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>L{n} c" 

notation left_nreachable ("_ \<rightarrow>\<^sup>L*{_} _" 55) 

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
  then obtain ys zs where "length ys = m" "ys @ zs = rev xs"
    using list_deconstruct1 by blast
  then show thesis using list_deconstruct1 that by (auto simp: append_eq_rev_conv)
qed
  (*These propositions are necessary for the two following lemmas.*)


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


lemma left_reachable_indep:
  assumes "x @ y \<rightarrow>\<^sup>L** (u, q, v @ \<rangle>y\<rangle>)"
  shows "x @ z \<rightarrow>\<^sup>L** (u, q, v @ \<rangle>z\<rangle>)"
proof -
  from assms obtain n where "([], init M, \<langle>x @ y\<rangle>) \<rightarrow>\<^sup>L{n} (u, q, v @ \<rangle>y\<rangle>)"
    by (meson rtranclp_power)
  hence "([], init M, \<langle>x @ z\<rangle>) \<rightarrow>\<^sup>L{n} (u, q, v @ \<rangle>z\<rangle>)"
  proof (induction n arbitrary: u q v)
    case (Suc n)
    from Suc(2) obtain u' p v' 
      where stepn: "x @ y \<rightarrow>\<^sup>L*{n} (u', p, v' @ \<rangle>y\<rangle>)" 
        and "(u', p, v' @ \<rangle>y\<rangle>) \<rightarrow>\<^sup>L{1} (u, q, v @ \<rangle>y\<rangle>)"
    proof -
      from Suc(2) obtain u' p v'' 
        where "x @ y \<rightarrow>\<^sup>L*{n} (u', p, v'')"
              "(u', p, v'') \<rightarrow>\<^sup>L{1} (u, q, v @ \<rangle>y\<rangle>)" by auto
      moreover from this init_lstar_impl_substring_x obtain v' where "v'' = v' @ \<rangle>y\<rangle>" 
        using rtranclp_power by metis
      ultimately show thesis using that by blast
    qed
    from this have y_lstep: "(u', p, v' @ \<rangle>y\<rangle>) \<rightarrow>\<^sup>L (u, q, v @ \<rangle>y\<rangle>)" 
      by fastforce
    hence "(u', p, v' @ \<rangle>z\<rangle>) \<rightarrow>\<^sup>L (u, q, v @ \<rangle>z\<rangle>)"
    proof -
      from y_lstep have left_configs: 
        "left_config (u', p, v' @ \<rangle>y\<rangle>)" 
        "left_config (u, q, v @ \<rangle>y\<rangle>)" by blast+
      hence "left_config (u', p, v' @ \<rangle>z\<rangle>)" 
            "left_config (u, q, v @ \<rangle>z\<rangle>)"
        unfolding left_config_def by auto
      moreover have "(u', p, v' @ \<rangle>z\<rangle>) \<rightarrow> (u, q, v @ \<rangle>z\<rangle>)"
      proof -
        from y_lstep have y_step: "(u', p, v' @ \<rangle>y\<rangle>) \<rightarrow> (u, q, v @ \<rangle>y\<rangle>)" by blast
        obtain c vs where v'_def: "v' = c # vs"
        proof -
          from unchanged_word have "rev u' @ v' @ \<rangle>y\<rangle> = \<langle>x @ y\<rangle>"
            by (metis left_steps_impl_steps relpowp_imp_rtranclp stepn)
          hence rev_u'_app_v': "rev u' @ v' = \<langle>x\<langle>" by simp
          have "v' \<noteq> []"
            by (rule ccontr) (use rev_u'_app_v' left_config_def left_configs in auto)
          thus thesis using that list.exhaust by blast
        qed
        with y_step have "(u', p, c # vs @ \<rangle>y\<rangle>) \<rightarrow> (u, q, v @ \<rangle>y\<rangle>)" by simp
        hence "(u', p, c # vs @ \<rangle>z\<rangle>) \<rightarrow> (u, q, v @ \<rangle>z\<rangle>)" by fastforce
        with v'_def show ?thesis by simp
      qed 
      ultimately show ?thesis by blast
    qed
    moreover from Suc(1)[OF stepn] have "x @ z \<rightarrow>\<^sup>L*{n} (u', p, v' @ \<rangle>z\<rangle>)" .
    ultimately show ?case by auto
  qed simp
  then show ?thesis by (meson rtranclp_power)
qed


inductive T :: "'a list \<Rightarrow> state option \<Rightarrow> state option \<Rightarrow> bool" for z where
  init_tr[intro]: "\<lbrakk>x @ z \<rightarrow>\<^sup>L** (rev x_init, p, x_end # \<rangle>z\<rangle>); 
              (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T z None (Some p)" |

  init_no_tr[intro]: "\<nexists>q. x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<Longrightarrow> T z None None" |

  some_tr[intro]: "\<lbrakk>x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>); 
              (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q, x_end # \<rangle>z\<rangle>); 
              (rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, p', x_end # \<rangle>z\<rangle>); 
              (rev x_init, p', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T z (Some q) (Some p)" |
                                                       (*Following notation in Kozen, p. 124*)
  no_tr[intro]:   "\<lbrakk>x @ z \<rightarrow>**c; c \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>); 
              (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q, x_end # \<rangle>z\<rangle>); 
              \<nexists>q'. (rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z\<rangle>) \<and>
              (rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T z (Some q) None" 

inductive_cases init_trNoneE[elim]: "T z None None"
inductive_cases init_trSomeE[elim]: "T z  None (Some q)"
inductive_cases no_trE[elim]:   "T z (Some q) None"
inductive_cases some_trE[elim]: "T z (Some q) (Some p)"




lemma T_impl_in_states:
  assumes "T z p q"
  shows "p = Some p' \<Longrightarrow> p' \<in> states M" 
        "q = Some q' \<Longrightarrow> q' \<in> states M"
  using assms by (induction, auto) 
    ( meson init left_steps_impl_steps steps_impl_in_states r_into_rtranclp 
      right_steps_impl_steps dfa2_axioms dfa2_transition_axioms)+

 
lemma T_p_Some_impl_reachable:
  assumes "T z p (Some q)"
  obtains u v where "x @ z \<rightarrow>** (u, q, v)"
  using assms
proof -
  consider "p = None" | p' where "p = Some p'" by auto
  then show thesis
  proof cases
    case 1
    obtain q' where "x @ z \<rightarrow>\<^sup>L** (rev x_init, q, x_end # \<rangle>z\<rangle>)"
                               "(rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" 
      using assms 1 by auto
    hence "x @ z \<rightarrow>** (rev x_init, q, x_end # \<rangle>z\<rangle>)" by blast
    thus thesis using that by simp
  next
    case 2
    with assms obtain q' q'' where 
       "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" 
       "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, p', x_end # \<rangle>z\<rangle>)"
       "(rev x_init, p', x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q'', x_end # \<rangle>z\<rangle>)"
       "(rev x_init, q'', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by auto
    hence "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by fastforce            
    then show thesis using that by simp
  qed
qed

lemma boundary_cross_impl_T:
  assumes "x @ z \<rightarrow>** (rev x_init, p, x_end # \<rangle>z\<rangle>)"
          "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
  obtains q' where "T z q' (Some p)"
  \<proof>

lemma left_acc_impl_T_Some_acc:
  assumes reach: "x @ z \<rightarrow>** (u, acc M, v)"
      and left: "left_config (u, acc M, v)"
    obtains q where "T z q (Some (acc M))"
proof -
  from assms(2) star_lstar_impl_substring_x[OF assms(1)] 
  obtain y where y_defs: "rev u @ y = \<langle>x\<langle>" "y @ \<rangle>z\<rangle> = v"
    unfolding left_config_def by blast
  moreover obtain a as where "y = a # as" 
  proof -
    have "y \<noteq> []" using y_defs left left_config_def by auto
    thus thesis using list.exhaust that by blast
  qed
  ultimately have last_y: "last y = x_end" using x_defs left left_config_def
    by (metis last_appendR list.distinct(1))
  obtain ys where ys_def: "v = ys @ (x_end # \<rangle>z\<rangle>)"
  proof -
    from last_y obtain ys where "y = ys @ [x_end]" 
      by (metis \<open>y = a # as\<close> append_butlast_last_id list.distinct(1))
    with y_defs have "ys @ [x_end] @ \<rangle>z\<rangle> = v" by simp
    thus thesis using that by auto
  qed
  consider "ys = []" | b bs where "ys = b # bs" using list.exhaust by blast
  then show thesis
  proof cases
    case 1
    hence u_v_is_bound: "(u, acc M, v) = (rev x_init, acc M, x_end # \<rangle>z\<rangle>)" 
      using ys_def unchanged_word[OF reach] x_defs by simp
    have "(u, acc M, v) \<rightarrow> (rev (\<langle>x\<langle>), acc M, \<rangle>z\<rangle>)" 
    proof -
      have "x_end \<noteq> \<stileturn>" using x_defs(2) by (simp add: last_map)
      hence "(rev x_init, acc M, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), acc M, \<rangle>z\<rangle>)"
        using final_nxt_r x_defs 
        by (smt (verit, ccfv_SIG) rev_eq_Cons_iff rev_rev_ident step.simps x_is_init_app_end)
      with u_v_is_bound show ?thesis by blast
    qed
    then show thesis using that boundary_cross_impl_T u_v_is_bound reach by blast
  next
    case 2
    with acc_impl_reachable_substring[OF reach] 
      have bound_reach: "(u, acc M, v) \<rightarrow>* (rev ys @ u, acc M, x_end # \<rangle>z\<rangle>)"
        using ys_def by blast
      hence "(rev x_init, acc M, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), acc M, \<rangle>z\<rangle>)"
      proof -
        have "x_end \<noteq> \<stileturn>" using x_defs(2) by (simp add: last_map)
        thus ?thesis using final_nxt_r x_defs 
        by (smt (verit, ccfv_SIG) rev_eq_Cons_iff rev_rev_ident step.simps x_is_init_app_end)
    qed
    moreover have "x @ z \<rightarrow>** (rev ys @ u, acc M, x_end # \<rangle>z\<rangle>)" using reach bound_reach by simp
    moreover from this have "rev ys @ u = rev x_init" using unchanged_word x_defs
      by (metis append_eq_append_conv calculation(1) dfa2.mapl_app_mapr_eq_map
          dfa2.unchanged_substrings dfa2_axioms r_into_rtranclp rev_rev_ident)
    ultimately show thesis using that boundary_cross_impl_T by metis
  qed
qed

lemma right_substring_steps_impl_word_reachable:
  assumes "([], p, \<rangle>z\<rangle>) \<rightarrow>* (u, q, v)"
          "T z q' (Some p)"
        shows "x @ z \<rightarrow>** (u, q, v)"
  using assms \<proof>

lemma reachable_impl_right_substring_reachable:
  assumes "right_config (u, q, v)"
          "x @ z \<rightarrow>** (u, q, v)"
        obtains q' p where "T z q' (Some p)" "([], p, \<rangle>z\<rangle>) \<rightarrow>* (u, q, v)" 
  \<proof>



(*Needed? (All unused until now)*)
lemma T_func:
  assumes "T z p q"
          "T z p q'"
        shows "q = q'" sorry 

lemma T_func_conv:
  assumes "T z p q"
          "q \<noteq> q'"
        shows "\<not>T z p q'" using assms T_func by auto 

lemma T_none_none_iff_not_none_some:
  "(\<exists>q. T z None (Some q)) \<longleftrightarrow> \<not>T z None None"
proof
  assume "\<exists>q. T z None (Some q)"
  then show "\<not> T z None None"
  proof 
    fix q
    assume "T z None (Some q)"
    thus "\<not> T z None None"
      using T_func by auto (*Can also be shown without T_func, although the proof is a bit more
                          complex*)
  qed
next
  assume "\<not> T z None None"
  then obtain q where "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by blast
  hence "T z None (Some q)" sorry (*Infinite descent?*)
  thus "\<exists>q. T z None (Some q)" by blast
qed

end


context dfa2_transition
begin

definition \<T> :: "'a list \<Rightarrow> (state option \<times> state option) set" where
  "\<T> z \<equiv> {(q, p). T z q p}"

lemma \<T>_subset_states_none:
  "\<T> z \<subseteq> ({Some q | q. q \<in> states M} \<union> {None}) \<times> ({Some q | q. q \<in> states M} \<union> {None})"
    (is "_ \<subseteq> ?S \<times> _")
proof
    fix qp :: "state option \<times> state option"
    assume "qp \<in> \<T> z"
    then obtain q p where qp_def: "qp = (q, p)" "(q, p) \<in> \<T> z"
      by (metis surj_pair)
    have "(q, p) \<in> ?S \<times> ?S"
      using qp_def(2) dfa2_transition.T_impl_in_states[OF dfa2_transition_axioms] unfolding \<T>_def 
      by fast      
    thus "qp \<in> ?S \<times> ?S" using qp_def by simp
qed

lemma Tset_finite: "finite (\<T> z)" 
proof -
  let ?S = "{Some q | q. q \<in> states M} \<union> {None}"
  have "finite ?S" using finite by simp
  then show ?thesis using Finite_Set.finite_subset \<T>_subset_states_none by auto
qed

lemma \<T>_card_upperbound:
  "card (\<T> z) \<le> (card (states M) + 1) ^ 2"
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
  hence "card (\<T> z) \<le> card (?S \<times> ?S)" using \<T>_subset_states_none 
    by (meson card_mono finite_SigmaI)
  with card_eq show ?thesis using Groups_Big.card_cartesian_product
    by (metis power2_eq_square)
qed


lemma \<T>_finite_index:
  "finite (UNIV // (\<T> z))" (*Nontrivial(?) and not proved in the book*)
    (*Try: define leftlang as in Finite_Automata_HF and apply the same rule*)
  sorry


end

lemma T_eq_is_\<T>_eq:
  assumes "dfa2_transition M x"
          "dfa2_transition M y"
        shows "dfa2_transition.T M x z = dfa2_transition.T M y z 
           \<longleftrightarrow> dfa2_transition.\<T> M x z = dfa2_transition.\<T> M y z"
  unfolding dfa2_transition.\<T>_def[OF assms(1)] dfa2_transition.\<T>_def[OF assms(2)]
  by fastforce


context dfa2
begin

abbreviation "T \<equiv> dfa2_transition.T M" 
abbreviation "left_reachable \<equiv> dfa2_transition.left_reachable M"
abbreviation "right_reachable \<equiv> dfa2_transition.right_reachable M"
abbreviation "left_config \<equiv> dfa2_transition.left_config"
abbreviation "right_config \<equiv> dfa2_transition.right_config" (*Poor style?*)

theorem two_way_dfa_lang_regular:
  "regular language"
proof -
  obtain x y :: "'a list" where "x \<noteq> []" "y \<noteq> []" by blast
  (*Is this the best way to setup the proof? Fixing x and y under assms \<noteq> [] does not work*)
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
        then obtain q where "T x z q (Some (acc M))"
          using dfa2_transition.left_acc_impl_T_Some_acc[OF transition_axioms(1) 
                                                         x_acc_reachable]
          by blast
        with T_eq have "T y z q (Some (acc M))" by presburger
        then show ?thesis using language_def 
              dfa2_transition.T_p_Some_impl_reachable[OF transition_axioms(2)]
          by (metis (mono_tags, lifting) mem_Collect_eq)
      next
        case 2
        from dfa2_transition.reachable_impl_right_substring_reachable
              [OF transition_axioms(1) 2 x_acc_reachable]
        obtain q' p where Tq'p: "T x z q' (Some p)" 
                      and p_steps_acc:  "([], p, \<rangle>z\<rangle>) \<rightarrow>* (u, acc M, v)" .
        with dfa2_transition.right_substring_steps_impl_word_reachable
              [OF transition_axioms(2)] T_eq have "y @ z \<rightarrow>** (u, acc M, v)" by simp
        then show ?thesis using language_def by auto
      qed
    next
      (*The other direction is exactly the same thing but with x and y flipped.
        Any way to write it more compactly?*)
      assume "y @ z \<in> language"
      then obtain u v where y_acc_reachable: "y @ z \<rightarrow>** (u, acc M, v)" 
        unfolding language_def by blast
      consider "left_config y (u, acc M, v)" | "right_config y (u, acc M, v)"
        unfolding dfa2_transition.left_config_def[OF transition_axioms(2)]
                  dfa2_transition.right_config_def[OF transition_axioms(2)] 
        by fastforce
      thus "x @ z \<in> language"
      proof cases
        case 1
        then obtain q where "T y z q (Some (acc M))"
          using dfa2_transition.left_acc_impl_T_Some_acc[OF transition_axioms(2) 
                                                         y_acc_reachable]
          by blast
        with T_eq have "T x z q (Some (acc M))" by presburger
        then show ?thesis using language_def 
              dfa2_transition.T_p_Some_impl_reachable[OF transition_axioms(1)]
          by (metis (mono_tags, lifting) mem_Collect_eq)
      next
        case 2
        from dfa2_transition.reachable_impl_right_substring_reachable
              [OF transition_axioms(2) 2 y_acc_reachable]
        obtain q' p where Tq'p: "T y z q' (Some p)" 
                      and p_steps_acc:  "([], p, \<rangle>z\<rangle>) \<rightarrow>* (u, acc M, v)" .
        with dfa2_transition.right_substring_steps_impl_word_reachable
              [OF transition_axioms(1)] T_eq have "x @ z \<rightarrow>** (u, acc M, v)" by simp
        then show ?thesis using language_def by auto
      qed
    qed
  qed
  have "(\<forall>z. x @ z \<in> language \<longleftrightarrow> y @ z \<in> language) 
             \<longleftrightarrow> (x, y) \<in> eq_app_right language" unfolding eq_app_right_def by simp
  have "finite (UNIV // eq_app_right language)" sorry
  then show "regular language" using L3_1 by auto
qed
  
end
end
