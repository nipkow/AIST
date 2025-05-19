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
lemmas rtranclp_induct3 = 
  rtranclp_induct[of _ "(ax, ay, az)" "(bx, by, bz)", split_rule, consumes 1, case_names refl step]

abbreviation reachable :: "'a list \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>**\<close> 55) where
  "w \<rightarrow>** c \<equiv> ([], init M, \<langle>w\<rangle>) \<rightarrow>* c" 

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
  "(u, q, v) \<rightarrow>* (u', p, v') \<Longrightarrow> rev u @ v = rev u' @ v'"
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
  "([], init M, w) \<rightarrow>* (u, p, v) \<Longrightarrow> w = rev u @ v"
  using unchanged_substrings by force

lemma steps_app':
  assumes "(xs, q', v) \<rightarrow>* (ys, p, zs)"
  shows "(ws, q, u) \<rightarrow>* (xs, q', []) \<Longrightarrow> (ws, q, u @ v) \<rightarrow>* (ys, p, zs)"
   (*both config rules break here and raw rtranclp_induct does not work either
      (Solved below)*)
proof (induction arbitrary: ws q u rule: rtranclp_induct3)
  oops

lemma steps_app:
  "(u, q, v) \<rightarrow>* (u', p, v') \<Longrightarrow> (u, q, v @ xs) \<rightarrow>* (u', p, v' @ xs)"
proof (induction rule: rtranclp_induct3)
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


type_synonym transition = "state option \<Rightarrow> state option \<Rightarrow> bool"


locale dfa2_transition = dfa2 + (*there's probably a better alternative than a separate locale*)
  fixes x :: "'a list"
  assumes "x \<noteq> []"
begin 

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
  "w \<rightarrow>\<^sup>L** c \<equiv> \<exists>z. w = x @ z \<and>  ([], init M, \<langle>w\<rangle>) \<rightarrow>\<^sup>L* c" 
(*TODO: Check*)

inductive right_reachable :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" (infix \<open>\<rightarrow>\<^sup>R**\<close> 55) where
  "\<lbrakk>\<langle>x\<rangle> = a # xs; x @ z \<rightarrow>** c1; 
    c1 \<rightarrow>\<^sup>L* (rev xs, p, a # \<rangle>z\<rangle>); (rev xs, p, a # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>);
    (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow>\<^sup>R* c2\<rbrakk> \<Longrightarrow> c1 \<rightarrow>\<^sup>R** c2"
 (*Right reachability: c1 is reachable and can reach c2 with a single boundary crossing
    (is reachability of c1 too weak?)*)


lemma left_steps_impl_steps [elim]:
  assumes "c1 \<rightarrow>\<^sup>L* c2"
  obtains "c1 \<rightarrow>* c2" (*Is this bad usage of obtains? I
                       used it in order to be able to use this as an elim rule
                      if it is not: when in general to use elims?*)
proof
  from assms show "c1 \<rightarrow>* c2"
    by (induction rule: rtranclp_induct) auto
qed

lemma right_steps_impl_steps [elim]:
  assumes "c1 \<rightarrow>\<^sup>R* c2"
  obtains "c1 \<rightarrow>* c2"
proof 
  from assms show "c1 \<rightarrow>* c2"
    by (induction rule: rtranclp_induct) auto
qed

lemma left_steps_impl_lt_x: 
  "\<lbrakk>c1 \<rightarrow>\<^sup>L* c2; left_config c1\<rbrakk> 
    \<Longrightarrow> left_config c2"
  by (induction rule: rtranclp_induct) auto
  

lemma right_steps_impl_ge_x: 
  "\<lbrakk>c1 \<rightarrow>\<^sup>R* c2; right_config c1\<rbrakk> 
    \<Longrightarrow> right_config c2"
  by (induction rule: rtranclp_induct) auto

proposition list_deconstruct1:
  assumes "m \<le> length xs"
  obtains ys zs where "length ys = m" "ys @ zs = xs" using assms 
  by (metis add_diff_cancel_right' append_take_drop_id le_iff_add length_drop 
      length_rev rev_eq_append_conv)
(*This lemma was necessary for star_lstar_impl_substring_x but sledgehammer somehow was not able to 
prove it locally. How to deal with this?*)

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


lemma star_lstar_impl_substring_x:
  assumes nsteps: "x @ z \<rightarrow>** (xs, q, zs)"
      and in_x:   "length xs < length (\<langle>x\<langle>)"
      and lsteps: "(xs, q, zs) \<rightarrow>\<^sup>L* (as, p, bs)"
  obtains u where " rev as @ u = \<langle>x\<langle>" "u @ \<rangle>z\<rangle> = bs" 
proof -
  have leftconfig: "left_config (xs, q, zs)" unfolding left_config_def using in_x by blast
  hence as_lt_x: "length as < length (\<langle>x\<langle>)" using lsteps
    using left_config_def left_steps_impl_lt_x by force
  from lsteps show thesis
  proof (induction arbitrary: xs q zs rule: rtranclp_induct3)
    case refl 
    from unchanged_word nsteps lsteps have app: "\<langle>x @ z\<rangle> = rev as @ bs"
      by (metis left_steps_impl_steps unchanged_substrings)
    moreover from this as_lt_x
    obtain x' where "rev as @ x' = \<langle>x\<langle>" "x' @ \<rangle>z\<rangle> = bs"
    proof -
      from as_lt_x list_deconstruct1
      obtain xs xs' where "length xs = length as" and xapp: "xs @ xs' = \<langle>x\<langle>"
        using Nat.less_imp_le_nat by metis
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

lemma star_rstar_impl_substring_z:
  assumes nsteps: "x @ z \<rightarrow>** (xs, q, zs)"
      and not_in_x:   "length xs \<ge> length (\<langle>x\<langle>)"
      and rsteps: "(xs, q, zs) \<rightarrow>\<^sup>R* (as, p, bs)"
    obtains u where " rev (\<langle>x\<langle> @ u) = as" "u @ bs = \<rangle>z\<rangle>"
proof -
  have "right_config (xs, q, zs)" using not_in_x right_config_def by simp
  with rsteps right_config_def have as_ge_x: "length (\<langle>x\<langle>) \<le> length as"
    using right_steps_impl_ge_x by force
  from rsteps show thesis
  proof (induction arbitrary: xs q zs rule: rtranclp_induct3)
    case refl
    from unchanged_word nsteps rsteps have app: "\<langle>x @ z\<rangle> = rev as @ bs"
      by (metis right_steps_impl_steps unchanged_substrings)
    moreover from this as_ge_x
    obtain x' where "rev (\<langle>x\<langle> @ x') = as" "x' @ bs = \<rangle>z\<rangle>"
    proof -
      have "length bs \<le> length (\<rangle>z\<rangle>)" 
      proof (rule ccontr)
        assume "\<not>?thesis"
        hence "length bs > length (\<rangle>z\<rangle>)" by simp
        with as_ge_x
        have "length (rev as @ bs) > length (\<langle>x @ z\<rangle>)" by simp
        thus False using app by (metis nat_less_le)
      qed
      from list_deconstruct2[OF this]
      obtain xs xs' where "length xs' = length bs" and zapp: "xs @ xs' = \<rangle>z\<rangle>"
        by metis
      moreover from this have "length (\<langle>x\<langle> @ xs) = length as" using app
        by (metis (no_types, lifting) append.assoc append_eq_append_conv length_rev
            mapl_app_mapr_eq_map)
      ultimately have xs'_is_bs: "xs' = bs"
        by (metis app append_assoc append_eq_append_conv mapl_app_mapr_eq_map)
      then have x_app_xs_eq_rev_as: "\<langle>x\<langle> @ xs = rev as" using zapp app
        by (metis (no_types, lifting) append_assoc append_eq_append_conv
            dfa2.mapl_app_mapr_eq_map dfa2_axioms)
      hence "rev (\<langle>x\<langle> @ xs) = as" by simp
      thus thesis using xs'_is_bs zapp that by presburger
    qed
    ultimately show ?case using that by simp
  qed blast
qed

inductive T :: transition where
  init_tr: "\<lbrakk>\<langle>x\<rangle> = a # xs; x @ z \<rightarrow>\<^sup>L** (rev xs, q, a # \<rangle>z\<rangle>); (rev xs, q, a # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)\<rbrakk>
    \<Longrightarrow> T None (Some q)" |
  some_tr: "\<lbrakk>\<langle>x\<rangle> = a # xs; right_config c; x @ z \<rightarrow>** c; c \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>); 
    (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow> (rev xs, q, a # \<rangle>z\<rangle>); (rev xs, q, a # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev xs, p, a # \<rangle>z\<rangle>); 
    (rev xs, p, a # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T (Some q) (Some p)" |
  no_tr:  "\<lbrakk>\<langle>x\<rangle> = a # xs; right_config c; x @ z \<rightarrow>** c; \<nexists>q. c \<rightarrow>* (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)\<rbrakk>
    \<Longrightarrow> T None None" (*TODO: BOT*)

(*TODO: Set up automation for T*)

end

context dfa2
begin
abbreviation "T \<equiv> dfa2_transition.T M"

definition Tset :: "'a list \<Rightarrow> (state \<times> state) set" where
  "Tset x \<equiv> {(q, p). q \<in> states M \<and> p \<in> states M \<and> T x (Some q) (Some p)}"
(*TODO*)

lemma Tset_card_upperbound:
  shows "card (Tset x) \<le> card (states M) ^ 2"
proof -
  have "Tset x \<subseteq> states M \<times> states M" unfolding Tset_def by blast
  thus ?thesis using Groups_Big.card_cartesian_product 
    by (metis card_mono finite_cartesian_product local.finite power2_eq_square)
qed

lemma Tset_finite:
  "finite (Tset x)" 
proof -
  from finite have "finite (states M \<times> states M)" by simp
  moreover have "Tset x \<subseteq> states M \<times> states M" unfolding Tset_def by blast
  ultimately show ?thesis unfolding Tset_def 
    using rev_finite_subset by auto
qed

lemma Tset_finite_index:
  "finite (UNIV // Tset x)" (*Nontrivial(?) and not proved in the book*)
  sorry



theorem two_way_dfa_lang_regular: (*Should this be inside a locale/context?*)
  "regular language"
proof - (*Book proof is rather informal - formalization might be quite more complicated 
        than expected*)
  fix x y
  have imp: "Tset x = Tset y \<Longrightarrow> (\<forall>z. x @ z \<in> language \<longleftrightarrow> y @ z \<in> language)"
    unfolding Tset_def sorry
  moreover have "(\<forall>z. x @ z \<in> language \<longleftrightarrow> y @ z \<in> language) 
             \<longleftrightarrow> (x, y) \<in> eq_app_right language" unfolding eq_app_right_def by simp
  ultimately have "finite (UNIV // eq_app_right language)" using Tset_finite_index sorry
  then show ?thesis using L3_1 by auto
qed
  
end

(*TODO: formalize iff chain (Kozen, p. 126) top-down*)



end
