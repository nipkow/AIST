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

lemma step_unique:
  assumes "c1 \<rightarrow> c2"
          "c1 \<rightarrow> c3"
        shows "c2 = c3"
  using assms by fastforce

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
  then show ?case
  proof (cases d')
    case Left
    hence "(c, q'', d) = (tl a, p', hd a # b)"  
      using step(2) qd_def step.simps by force
    then show ?thesis
      using step.IH step.hyps(2) by fastforce
  next
    case Right
    hence "(c, q'', d) = (hd b # a, p', tl b)" using step(2) qd_def step.simps by force
    then show ?thesis using step step.cases by fastforce
  qed
qed simp

corollary unchanged_word:
  "([], p, w) \<rightarrow>* (u, q, v) \<Longrightarrow> w = rev u @ v"
  using unchanged_substrings by force

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

lemma reachable_impl_not_empty:
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

lemma stepn_decompose:
  assumes "k \<le> n"
          "c1 \<rightarrow>{k} c2"
          "c1 \<rightarrow>{n} c3"
        shows "c2 \<rightarrow>{n-k} c3"
  using assms proof (induction k arbitrary: c2)
  case (Suc k)
  then obtain c' where c'_defs: "c1 \<rightarrow>{k} c'" "c' \<rightarrow> c2" by auto
  with Suc have "c' \<rightarrow>{n-k} c3" by simp
  then show ?case using c'_defs
    by (metis Suc.prems(1) Suc_diff_le diff_Suc_Suc relpowp_Suc_D2 step_unique)
qed simp

lemma left_to_right_impl_reachable_substring:
  assumes "length bs > length z"
          "w \<rightarrow>** (u, p, as @ bs)"
          "(u, p, as @ bs) \<rightarrow>{n} (y, q, z)"
        obtains q' m k where "m + k = n" "(u, p, as @ bs) \<rightarrow>{m} (rev as @ u, q', bs)"
                             "(rev as @ u, q', bs) \<rightarrow>{k} (y, q, z)"
  using assms proof (induction n arbitrary: u p as bs thesis)
  case (Suc n)
  note asbs_not_empty = reachable_impl_not_empty[OF Suc(4)]
  consider x xs p' where "as = x # xs" "nxt M p x = (p', Left)" | 
           x xs p' where "as = x # xs" "nxt M p x = (p', Right)" |
                         "as = []"
    using list.exhaust dir.exhaust old.prod.exhaust by (metis (full_types)) 
  then show ?case
  proof cases
    case 1
    have "u \<noteq> []"
      by (rule ccontr)
      (metis "1"(1,2) Suc.prems(3) dir.distinct(1) init last_append rev.simps(2) rev_append 
        rev_rev_ident snoc_eq_iff_butlast steps_impl_in_states unchanged_word[OF Suc(4)] left_nxt)
    with 1 Suc(5) have u_step: "(u, p, as @ bs) \<rightarrow> (tl u, p', (hd u # as) @ bs)"
      using step.simps by force 
    from this Suc(5) have nsteps: "... \<rightarrow>{n} (y, q, z)"
      by (metis relpowp_Suc_D2 step_unique)
    moreover obtain m k q' where 
      "m + k = n" "(tl u, p', (hd u # as) @ bs) \<rightarrow>{m} (rev as @ u, q', bs)"
                  "(rev as @ u, q', bs) \<rightarrow>{k} (y, q, z)"
    proof -
      from Suc(1)[OF _ _ _ nsteps] Suc(4) u_step obtain m k q' where 
      "m + k = n" "(tl u, p', (hd u # as) @ bs) \<rightarrow>{m} (rev (hd u # as) @ tl u, q', bs)"
                  "(rev (hd u # as) @ tl u, q', bs) \<rightarrow>{k} (y, q, z)" 
        by (metis (mono_tags, lifting) Suc.prems(2) rtranclp.rtrancl_into_rtrancl)
      then show thesis using that \<open>u \<noteq> []\<close> by auto
    qed
    then show ?thesis using Suc(2)[of "Suc m" k q'] u_step by (meson add_Suc relpowp_Suc_I2)
  next
    case 2
    hence u_step: "(u, p, as @ bs) \<rightarrow> (x # u, p', xs @ bs)" by force
    then have nsteps: "... \<rightarrow>{n} (y, q, z)" using Suc(5) 
      by (metis relpowp_Suc_D2 step_unique)
    obtain m k q' where "m + k = n" "(x # u, p', xs @ bs) \<rightarrow>{m} (rev as @ u, q', bs)"
                        "(rev as @ u, q', bs) \<rightarrow>{k} (y, q, z)"
    proof -
      from Suc(1)[OF _ _ _ nsteps] Suc(4) u_step obtain m k q' where 
        "m + k = n" "(x # u, p', xs @ bs) \<rightarrow>{m} (rev xs @ x # u, q', bs)"
                    "(rev xs @ x # u, q', bs) \<rightarrow>{k} (y, q, z)"
          by (metis (mono_tags, lifting) Suc.prems(2) rtranclp.rtrancl_into_rtrancl)
      then show thesis using that 2(1) by auto
    qed
    then show ?thesis using Suc(2)[of "Suc m" k q'] u_step by (meson add_Suc relpowp_Suc_I2)
  qed (use Suc(2)[of 0 "Suc n" p] Suc(5) in simp)
qed auto

lemma right_to_left_impl_reachable_substring:
  assumes "length bs > length y"
          "w \<rightarrow>** (as @ bs, p, v)"
          "(as @ bs, p, v) \<rightarrow>{n} (y, q, z)"
        obtains q' m k where "m + k = n" "(as @ bs, p, v) \<rightarrow>{m} (bs, q', rev as @ v)"   
                         "(bs, q', rev as @ v) \<rightarrow>{k} (y, q, z)"
  using assms proof (induction n arbitrary: as bs p v thesis)
  case (Suc n)
  note v_not_empty = reachable_impl_not_empty[OF Suc(4)]
  consider x xs p' where "as = x # xs" "nxt M p (hd v) = (p', Left)" | 
           x xs p' where "as = x # xs" "nxt M p (hd v) = (p', Right)" |
                         "as = []" 
    using list.exhaust dir.exhaust old.prod.exhaust by (metis (full_types)) 
  then show ?case
  proof cases
    case 1
    have asbs_step: "(as @ bs, p, v) \<rightarrow> (xs @ bs, p', x # v)" using v_not_empty
      by (smt (verit) "1"(1,2) append_Cons hd_Cons_tl step.simps)
    hence xsbs_stepn: "... \<rightarrow>{n} (y, q, z)" using Suc(5)
      by (metis relpowp_Suc_D2 step_unique)
    from asbs_step Suc(4) have w_reach_xsbs: "w \<rightarrow>** (xs @ bs, p', x # v)" by simp
    from Suc(1)[of xs bs p' "x#v", OF _ Suc(3) this xsbs_stepn] obtain m k q' where 
      "m + k = n" "(xs @ bs, p', x # v) \<rightarrow>{m} (bs, q', rev xs @ x # v)" 
      "(bs, q', rev xs @ x # v) \<rightarrow>{k} (y, q, z)" by metis
    moreover from 1(1) have "rev xs @ [x] = rev as" by simp
    ultimately show thesis using Suc(2)[of "Suc m" k q'] asbs_step 
      by (metis (no_types, lifting) Cons_eq_appendI add_Suc append_eq_append_conv2 butlast.simps(2) butlast_snoc
          relpowp_Suc_I2 same_append_eq)
  next
    case 2
    with v_not_empty obtain as' where as'_def: "as' = hd v # as" by simp
    then have asbs_step: "(as @ bs, p, v) \<rightarrow> (as' @ bs, p', tl v)"
          and as'bs_stepn: "(as' @ bs, p', tl v) \<rightarrow>{n} (y, q, z)" using 2 v_not_empty Suc(5) 
      by (metis (no_types, lifting) Cons_eq_appendI hd_Cons_tl step_right,
          metis (no_types, lifting) as'_def dfa2.step_unique dfa2_axioms 
          relpowp_Suc_D2 Cons_eq_appendI hd_Cons_tl step_right)
    then have as'bs_reachable: "w \<rightarrow>** (as' @ bs, p', tl v)" using Suc(4) by simp
    with as'bs_stepn Suc(1)[of as' bs p' "tl v"] Suc(3)  as'bs_stepn obtain m k q' where
     "m + k = n" "(as' @ bs, p', tl v) \<rightarrow>{m} (bs, q', rev as' @ tl v)" 
                  "(bs, q', rev as' @ tl v) \<rightarrow>{k} (y, q, z)" by blast
    moreover from as'_def have "rev as' @ tl v = rev as @ v" by (simp add: v_not_empty)
    ultimately show thesis using Suc(2)[of "Suc m" k q'] asbs_step
      by (metis (no_types, lifting) add_Suc relpowp_Suc_I2)
  qed (use Suc(2)[of 0 "Suc n" p] Suc(5) in simp)
qed auto

lemma left_to_right_impl_substring:
  assumes "(u, p, v) \<rightarrow>* (w, q, y)"
          "length u \<le> length w"
        obtains us where "us @ u = w"
  using assms proof (induction arbitrary: thesis rule: rtranclp_induct3)
  case (step u' p' v' x q z)
  then consider "length u < length x" | "length u = length x" by linarith
  then show ?case
  proof cases
    case 1
    then have "length u \<le> length u'" using step by fastforce
    with step(3) obtain us where us_app_u: "us @ u = u'" by blast
    then show thesis by (cases us) (use step us_app_u in auto)
  next
    case 2
    with step(1,2) unchanged_substrings have "u = x"
      by (metis append_eq_append_conv r_into_rtranclp rev_append rev_rev_ident)
    then show thesis using step(4) by simp
  qed
qed simp

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

lemma all_geq_left_impl_left_indep:
  assumes upv_reachable: "w \<rightarrow>** (u, p, v)"
      and "(u, p, v) \<rightarrow>{n} (vs @ u, q, x)"
          "\<forall>i\<le>n. \<forall>u' p' v'. ((u, p, v) \<rightarrow>{i} (u', p', v')) \<longrightarrow> length u' \<ge> length u"
        shows "(u', p, v) \<rightarrow>{n} (vs @ u', q, x)"
  using assms(2,3) proof (induction n arbitrary: vs q x)
  case (Suc n)
  then obtain vs' q' x' where 
    nsteps: "(u, p, v) \<rightarrow>{n} (vs' @ u, q', x')" "(vs' @ u, q', x') \<rightarrow> (vs @ u, q, x)"
  proof -
    from Suc(2) obtain y q' x' where nstep: 
      "(u, p, v) \<rightarrow>{n} (y, q', x')" "(y, q', x') \<rightarrow> (vs @ u, q, x)" by auto
    moreover from this Suc(3) have y_gt_u: "length y \<ge> length u" by (meson Suc_leD order_refl)
    ultimately obtain vs' where "y = vs' @ u" using left_to_right_impl_substring 
      by (metis relpowp_imp_rtranclp)
    then show thesis using nstep that by blast
  qed
  with Suc(1) have "(u', p, v) \<rightarrow>{n} (vs' @ u', q', x')" 
    using Suc.prems(2) le_Suc_eq by blast
  moreover from nsteps(2) have "(vs' @ u', q', x') \<rightarrow> (vs @ u', q, x)" by force
  ultimately show ?case by auto
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

lemma left_config_is_not_right_config:
  "left_config c \<longleftrightarrow> \<not>right_config c"
  unfolding left_config_def right_config_def
  by (metis linorder_not_less prod.inject prod_cases3)

lemma left_config_lt_right_config:
  assumes "left_config (u, p, v)"
          "right_config (w, q, y)"
        shows "length u < length w"
  using assms left_config_def right_config_def by simp

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

lemma dir_step_impl_not_opposite:
      "c1 \<rightarrow>\<^sup>L c2 \<Longrightarrow> \<not>(c1 \<rightarrow>\<^sup>R c2)"
      "c1 \<rightarrow>\<^sup>R c2 \<Longrightarrow> \<not>(c1 \<rightarrow>\<^sup>L c2)"
  using left_config_is_not_right_config by blast+

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

lemma nsteps_lower_bound:
  assumes "length u \<ge> length y"
  shows "(u, p, v) \<rightarrow>{n} (y, q, z) \<Longrightarrow> length y \<ge> length u - n"
using assms proof (induction n arbitrary: u p v y q z)
  case (Suc n) 
  consider q' where "nxt M p (hd v) = (q', Left)" | q' where "nxt M p (hd v) = (q', Right)"
    by (metis (full_types) dir.exhaust old.prod.exhaust)
  then show ?case
  proof cases
    case 1
    with Suc(2) have steps: "(u, p, v) \<rightarrow> (tl u, q', hd u # v)" "(tl u, q', hd u # v) \<rightarrow>{n} (y, q, z)"
       apply (smt (verit) Pair_inject dir.distinct(1) list.sel(1,3) relpowp_Suc_E2 step.simps)
      using "1" Suc.prems(1) relpowp_Suc_D2' by fastforce
    consider "length (tl u) \<ge> length y" | "length (tl u) < length y" by linarith
    then show ?thesis by cases (use steps Suc in auto)
  next
    case 2
    with Suc(2) have steps: "(u, p, v) \<rightarrow> (hd v # u, q', tl v)" "(hd v # u, q', tl v) \<rightarrow>{n} (y, q, z)"
       apply (smt (verit) Pair_inject dir.distinct(1) list.sel(1,3) relpowp_Suc_E2 step.simps)
      using "2" Suc.prems(1) relpowp_Suc_D2' by fastforce
    then show ?thesis using Suc by force
  qed
qed simp

lemma chain_reachable:
  fixes f :: "nat \<Rightarrow> 'a config"
  assumes "c0 \<rightarrow>{n} cn"
          "n > 0"
          "f 0 = c0"
          "f n = cn"
          "\<forall>i < n. f i \<rightarrow> f (Suc i)"
          "k \<le> n" "j < k"
        shows "f j \<rightarrow>{k-j} f k"
  using assms(6,7) proof (induction k)
  case (Suc k)
  hence "f j \<rightarrow>{k-j} f k" using less_SucE by fastforce
  moreover from Suc(2) have "f k \<rightarrow> f (Suc k)" using assms(5) by simp
  ultimately have "f j \<rightarrow>{k-j+1} f (Suc k)" by auto
  thus ?case using Suc.prems(2) Suc_diff_le by fastforce
qed simp
 
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

  

lemma star_rconfig_impl_substring_z:
  assumes nsteps: "x @ z \<rightarrow>** (u, p, v)"
      and reach: "(u, p, v) \<rightarrow>* (u', q, v')"
      and rconf: "right_config (u', q, v')"
    obtains y where " rev (\<langle>x\<langle> @ y) = u'" "y @ v' = \<rangle>z\<rangle>"
proof -
  from right_config_def have u'_ge_x: "length (\<langle>x\<langle>) \<le> length u'"
    using rconf by force
  from reach show thesis
  proof (induction arbitrary: u p v rule: rtranclp_induct3)
    case refl
    from unchanged_word nsteps have app: "\<langle>x @ z\<rangle> = rev u' @ v'"
      by (metis reach unchanged_substrings)
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



corollary reachable_right_conf_impl_substring_z:
  assumes "x @ z \<rightarrow>** (u, q, v)"
          "right_config (u, q, v)"
        obtains y where "rev (\<langle>x\<langle> @ y) = u" "y @ v = \<rangle>z\<rangle>"
  using assms star_rconfig_impl_substring_z right_config_def by blast

lemma reachable_from_left_impl_reachable_without_loops:
  assumes "w \<rightarrow>** (u, p, v)"
          "(u, p, v) \<rightarrow>{n} (y, q, z)"
          "length u < length y"
obtains p' m where "m < n" "(u, p, v) \<rightarrow>{m} (u, p', v)"
               "\<forall>k \<le> n-m. \<forall>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<longrightarrow> length u < length u'"
proof - 
  have "\<exists>p' m. m < n \<and> ((u, p, v) \<rightarrow>{m} (u, p', v)) 
\<and> (\<forall>k \<le> n-m. \<forall>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<longrightarrow> length u < length u')"
    (is "?ex n p")
    using assms(1,2)
  proof (induction n arbitrary: p rule: infinite_descent0)
    case (smaller n)
    then obtain p where nsteps: "(u, p, v) \<rightarrow>{n} (y, q, z)" "w \<rightarrow>** (u, p, v)" "\<not>?ex n p" by blast
    from \<open>\<not>?ex n p\<close> have neg: "\<forall>p' m. m \<ge> n \<or> \<not>((u, p, v) \<rightarrow>{m} (u, p', v))
        \<or> (\<exists>k\<le>n-m. \<exists>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<and> length u \<ge> length u')" 
    by (metis diff_is_0_eq not_gr_zero zero_less_diff)
    then obtain p' m where msteps: "m < n" "(u, p, v) \<rightarrow>{m} (u, p', v)" "m \<noteq> 0"
      "\<exists>k\<le>n-m. \<exists>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<and> length u \<ge> length u'"  
    proof -
      from smaller(1) obtain p' m where mstep: "m < n" "(u, p, v) \<rightarrow>{m} (u, p', v)" by simp
      from this have loop: "\<exists>k\<le>n-m. \<exists>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) 
                                    \<and> k \<noteq> 0 \<and> length u \<ge> length u'" 
        using neg by fastforce
      then obtain k u' q' v' where kstep: "k\<le>n-m" "(u, p', v) \<rightarrow>{k} (u', q', v')" "k \<noteq> 0" 
                                          "length u \<ge> length u'"
        by blast
      with mstep have "k < n" 
        by (smt (verit, ccfv_SIG) assms(3) diff_diff_cancel less_imp_diff_less less_or_eq_imp_le neq0_conv nsteps(1)
            prod.inject relpowp_fun_conv relpowp_right_unique step_unique zero_less_diff)
      with nsteps stepn_decompose kstep mstep have 
        mk_step: "(u, p, v) \<rightarrow>{m+k} (u', q', v')" by (meson relpowp_trans) 
      then obtain w' where w'_def: "w' @ v = v'" using unchanged_substrings kstep
        by (smt (verit, ccfv_threshold) append.assoc append_eq_append_conv list_deconstruct2 relpowp_imp_rtranclp
          rev_append rev_rev_ident that)
      with mk_step kstep nsteps(1) have "(u', q', w' @ v) \<rightarrow>{n-(m+k)} (y, q, z)"
        using stepn_decompose by auto
      moreover have "length v > length z"
      proof -
        from unchanged_substrings nsteps(1) have "rev u @ v = rev y @ z" by (metis rtranclp_power)
        with assms(3) show ?thesis
          by (metis add_le_cancel_left add_le_cancel_right leD leI length_append length_rev)
      qed
      ultimately obtain q'' i j where ij_defs: 
        "i+j = n-(m+k)" "(u', q', w' @ v) \<rightarrow>{i} (u, q'', v)" "(u, q'', v) \<rightarrow>{j} (y, q, z)"
      proof -
        from mk_step nsteps(2) have "w \<rightarrow>** (u', q', w' @ v)" using w'_def 
          by (meson relpowp_imp_rtranclp rtranclp_trans)
        with left_to_right_impl_reachable_substring obtain q'' i j where
          "i+j = n-(m+k)" "(u', q', w' @ v) \<rightarrow>{i} (rev w' @ u', q'', v)" 
          "(rev w' @ u', q'', v) \<rightarrow>{j} (y, q, z)"
          by (metis \<open>((\<rightarrow>) ^^ (n - (m + k))) (u', q', w' @ v) (y, q, z)\<close> \<open>length z < length v\<close>)
        moreover have "rev w' @ u' = u" 
        proof -
          from mk_step unchanged_substrings have "rev u @ v = rev u' @ v'" by (meson rtranclp_power)
          also from w'_def have "... = rev u' @ w' @ v" by simp
          finally show ?thesis by (simp add: rev_eq_append_conv)
        qed
        ultimately show thesis using that by simp
      qed
      hence mki_reach: "(u, p, v) \<rightarrow>{m+k+i} (u, q'', v)" using w'_def mk_step by (simp add: relpowp_trans)
      moreover have mki_lt_n: "m+k+i < n" using ij_defs kstep(1,3) using assms(3) nat_neq_iff by fastforce
      ultimately have ex_mki: "\<exists>k'\<le>n-(m+k+i). \<exists>u' q' v'. ((\<rightarrow>) ^^ k') (u, q'', v) (u', q', v') \<and> k' \<noteq> 0 
                      \<and> length u \<ge> length u'" using neg kstep(3) by force
      have "m+k+i \<noteq> 0" using kstep(3) by simp
      then show thesis using that ex_mki mki_reach mki_lt_n by presburger 
    qed
    then obtain k u' q' v' where ksteps: "k \<le> n - m" "(u, p', v) \<rightarrow>{k} (u', q', v')" "k \<noteq> 0" 
                                        "length u \<ge> length u'"
      by blast
    from msteps nsteps stepn_decompose have p'_reach: "(u, p', v) \<rightarrow>{n-m} (y, q, z)" by simp
    have w_reaches_p': "w \<rightarrow>** (u, p', v)" using nsteps(2) msteps(2) 
      by (meson relpowp_imp_rtranclp rtranclp_trans)   
    have "\<forall>p'' j. j < n-m \<longrightarrow> ((u, p', v) \<rightarrow>{j} (u, p'', v)) 
          \<longrightarrow> (\<exists>i\<le>n-(m+j). \<exists>u' q' v'. ((u, p'', v) \<rightarrow>{i} (u', q', v')) \<and> i \<noteq> 0 \<and> length u' \<le> length u)"
    proof (rule allI | rule impI)+
      fix p'' j
      assume j_lt_diff: "j < n-m"
        and  jstep: "(u, p', v) \<rightarrow>{j} (u, p'', v)"
      with msteps(2) have mj_step: "(u, p, v) \<rightarrow>{m+j} (u, p'', v)" using relpowp_trans by metis
      then show "\<exists>i\<le>n-(m+j). \<exists>u' q' v'. ((u, p'', v) \<rightarrow>{i} (u', q', v')) \<and> i \<noteq> 0 \<and> length u' \<le> length u"
        using j_lt_diff neg by fastforce
    qed
    hence "\<not>?ex (n-m) p'" using Suc_diff_Suc Zero_not_Suc diff_is_0_eq 
      by (metis (no_types, lifting) diff_diff_eq)    
    then show ?case using msteps(3) p'_reach using diff_less smaller.hyps w_reaches_p' by blast 
  qed (use assms(3) in simp)
  then show thesis using that by blast
qed

lemma reachable_from_right_impl_reachable_without_loops:
  assumes "w \<rightarrow>** (u, p, v)"
          "(u, p, v) \<rightarrow>{n} (y, q, z)"
          "length u > length y"
        obtains p' m where "m < n" "(u, p, v) \<rightarrow>{m} (u, p', v)"
               "\<forall>k \<le> n-m. \<forall>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<longrightarrow> length u > length u'"
proof -
  have "\<exists>p' m. m < n \<and> ((u, p, v) \<rightarrow>{m} (u, p', v)) 
\<and> (\<forall>k \<le> n-m. \<forall>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<longrightarrow> length u > length u')"
    (is "?ex n p")
    using assms(1,2) 
  proof (induction n arbitrary: p rule: infinite_descent0)
    case (smaller n)
    then obtain p where nsteps: "(u, p, v) \<rightarrow>{n} (y, q, z)" "w \<rightarrow>** (u, p, v)" "\<not>?ex n p" by blast
    from \<open>\<not>?ex n p\<close> have neg: "\<forall>p' m. m \<ge> n \<or> \<not>((u, p, v) \<rightarrow>{m} (u, p', v))
        \<or> (\<exists>k\<le>n-m. \<exists>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<and> length u \<le> length u')" 
    by (metis diff_is_0_eq not_gr_zero zero_less_diff)
    then obtain p' m where msteps: "m < n" "(u, p, v) \<rightarrow>{m} (u, p', v)" "m \<noteq> 0"
      "\<exists>k\<le>n-m. \<exists>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) \<and> k \<noteq> 0 \<and> length u \<le> length u'"
    proof -
      from smaller(1) obtain p' m where mstep: "m < n" "(u, p, v) \<rightarrow>{m} (u, p', v)" by simp
      from this have loop: "\<exists>k\<le>n-m. \<exists>u' q' v'. ((u, p', v) \<rightarrow>{k} (u', q', v')) 
                                    \<and> k \<noteq> 0 \<and> length u \<le> length u'" 
        using neg by fastforce
      then obtain k u' q' v' where kstep: "k\<le>n-m" "(u, p', v) \<rightarrow>{k} (u', q', v')" "k \<noteq> 0" 
                                          "length u \<le> length u'"
        by blast
      with mstep have "k < n" 
        by (smt (verit, ccfv_SIG) assms(3) diff_diff_cancel less_imp_diff_less less_or_eq_imp_le neq0_conv nsteps(1)
            prod.inject relpowp_fun_conv relpowp_right_unique step_unique zero_less_diff)
      with nsteps stepn_decompose kstep mstep have 
        mk_step: "(u, p, v) \<rightarrow>{m+k} (u', q', v')" by (meson relpowp_trans) 
      then obtain w' where w'_def: "w' @ u = u'" using unchanged_substrings kstep
        by (smt (verit, ccfv_threshold) append.assoc append_eq_append_conv list_deconstruct2 relpowp_imp_rtranclp
          rev_append rev_rev_ident that)
      with mk_step kstep nsteps(1) have "(w' @ u, q', v') \<rightarrow>{n-(m+k)} (y, q, z)"
        using stepn_decompose by auto
      moreover from kstep(4) have "length (w' @ u) > length y" using assms(3) by simp
      ultimately obtain q'' i j where ij_defs: 
        "i+j = n-(m+k)" "(w' @ u, q', v') \<rightarrow>{i} (u, q'', v)" "(u, q'', v) \<rightarrow>{j} (y, q, z)"
      proof -
        from mk_step nsteps(2) have "w \<rightarrow>** (w' @ u, q', v')" using w'_def 
          by (meson relpowp_imp_rtranclp rtranclp_trans)
        with right_to_left_impl_reachable_substring obtain q'' i j where
          "i+j = n-(m+k)" "(w' @ u, q', v') \<rightarrow>{i} (u, q'', rev w' @ v')" 
          "(u, q'', rev w' @ v') \<rightarrow>{j} (y, q, z)" 
          by (metis \<open>((\<rightarrow>) ^^ (n - (m + k))) (w' @ u, q', v') (y, q, z)\<close> \<open>length y < length u\<close> nat_less_le)
        moreover from mk_step w'_def unchanged_substrings have "rev w' @ v' = v" 
          by (metis calculation(2) relpowp_imp_rtranclp same_append_eq)
        ultimately show thesis using that by simp
      qed
      hence mki_reach: "(u, p, v) \<rightarrow>{m+k+i} (u, q'', v)" using w'_def mk_step by (simp add: relpowp_trans)
      moreover have mki_lt_n: "m+k+i < n" using ij_defs kstep(1,3) using assms(3) nat_neq_iff by fastforce
      ultimately have ex_mki: "\<exists>k'\<le>n-(m+k+i). \<exists>u' q' v'. ((\<rightarrow>) ^^ k') (u, q'', v) (u', q', v') \<and> k' \<noteq> 0 
                      \<and> length u \<le> length u'" using neg kstep(3) by force
      have "m+k+i \<noteq> 0" using kstep(3) by simp
      then show thesis using that ex_mki mki_reach mki_lt_n by presburger 
    qed
    then obtain k u' q' v' where ksteps: "k \<le> n - m" "(u, p', v) \<rightarrow>{k} (u', q', v')" "k \<noteq> 0" 
                                        "length u \<le> length u'"
      by blast
    with unchanged_substrings obtain w'' where w''_def: "w'' @ u = u'"
      by (smt (verit, ccfv_threshold) append.assoc append_eq_append_conv list_deconstruct2 relpowp_imp_rtranclp
          rev_append rev_rev_ident that)
    from msteps nsteps stepn_decompose have p'_reach: "(u, p', v) \<rightarrow>{n-m} (y, q, z)" by simp
    have w_reaches_p': "w \<rightarrow>** (u, p', v)" using nsteps(2) msteps(2) 
      by (meson relpowp_imp_rtranclp rtranclp_trans)
    have "\<forall>p'' j. j < n-m \<longrightarrow> ((u, p', v) \<rightarrow>{j} (u, p'', v)) 
          \<longrightarrow> (\<exists>i\<le>n-(m+j). \<exists>u' q' v'. ((u, p'', v) \<rightarrow>{i} (u', q', v')) \<and> i \<noteq> 0 \<and> length u' \<ge> length u)"
    proof (rule allI | rule impI)+
      fix p'' j
      assume j_lt_diff: "j < n-m"
        and  jstep: "(u, p', v) \<rightarrow>{j} (u, p'', v)"
      with msteps(2) have mj_step: "(u, p, v) \<rightarrow>{m+j} (u, p'', v)" using relpowp_trans by metis
      then show "\<exists>i\<le>n-(m+j). \<exists>u' q' v'. ((u, p'', v) \<rightarrow>{i} (u', q', v')) \<and> i \<noteq> 0 \<and> length u \<le> length u'"
        using j_lt_diff neg by fastforce
    qed
    hence "\<not>?ex (n-m) p'" using Suc_diff_Suc Zero_not_Suc diff_is_0_eq 
      by (metis (no_types, lifting) diff_diff_eq)
    then show ?case using msteps(3) p'_reach using diff_less smaller.hyps w_reaches_p' by blast 
    qed (use assms(3) in simp)
  then show thesis using that by blast
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

lemma not_left_reachable_impl_right_boundary_cross:
  assumes reach: "x @ z \<rightarrow>** c"
      and left: "left_config c"
      and not_lr: "\<not>x @ z \<rightarrow>\<^sup>L** c"
      and c_def: "c = (u, q, v)"
        obtains p q where "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)"
                   "(rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q, x_end # \<rangle>z\<rangle>)"
                   "(rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* c"
proof -
  from reach obtain n where
    nsteps: "x @ z \<rightarrow>*{n} c" by (meson rtranclp_power)
  then obtain f where f_defs:
    "f 0 = ([], init M, \<langle>x @ z\<rangle>)"
    "f n = c"
    "\<forall>i<n. f i \<rightarrow> f (Suc i)" 
    using relpowp_fun_conv by metis
  then obtain k where k_leq_n: "k \<le> n" and fk_right: "right_config (f k)"
  proof -
    have "\<exists>k\<le>n. right_config (f k)"
    proof (rule ccontr)
      assume "\<not>(\<exists>k\<le>n. right_config (f k))"
      hence "\<forall>k\<le>n. left_config (f k)" using left_config_is_not_right_config by simp
      with f_defs have "\<forall>k<n. f k \<rightarrow>\<^sup>L f (Suc k)" by auto
      with f_defs  have "x @ z \<rightarrow>\<^sup>L*{n} c" using relpowp_fun_conv by metis
      with not_lr show False by (simp add: rtranclp_power)
    qed
    with that show thesis by blast
  qed
  then obtain w p y where wpy_def: "f k = (w, p, y)" by (metis surj_pair)
  have wpy_reachable: "x @ z \<rightarrow>** (w, p, y)"
  proof -
    from k_leq_n consider "k < n" | "k = n" by linarith
    thus ?thesis
    proof cases
      case 1
      then show ?thesis using wpy_def f_defs
        by (smt (verit, best) dfa2_transition.chain_reachable dfa2_transition_axioms diff_is_0_eq k_leq_n
            less_imp_diff_less nsteps rtranclp.simps rtranclp_power zero_less_iff_neq_zero)
    next
      case 2
      then show ?thesis using wpy_def f_defs(2) reach by simp 
    qed
  qed
  then obtain zs where zs_defs: "rev (\<langle>x\<langle> @ zs) = w" "zs @ y = \<rangle>z\<rangle>" 
    using star_rconfig_impl_substring_z[of z w p y w p y] that wpy_def fk_right by auto
  hence w_app_def: "w = rev zs @ rev (\<langle>x\<langle>)" by simp
  obtain m where m_def: "m = n-k" by simp
  hence fk_mstep_c: "f k \<rightarrow>{m} c" using k_leq_n 
  proof (induction k arbitrary: m)
      case (Suc k) 
      hence "Suc m = n - k" by simp 
      with Suc(1,3) have "f k \<rightarrow>{Suc m} c" by simp
      then show ?case using f_defs 
        by (metis Suc.prems(2) less_eq_Suc_le relpowp_Suc_D2 step_unique)
    qed (use f_defs nsteps in auto) 
  obtain q' j l where 
    jl_def: "j + l = m"
and wpy_jstep: "(w, p, y) \<rightarrow>{j} (rev (\<langle>x\<langle>), q', zs @ y)" 
and revx_lstep: "(rev (\<langle>x\<langle>), q', zs @ y) \<rightarrow>{l} (u, q, v)" 
  proof -
    from fk_right wpy_def w_app_def left have "length (rev zs @ rev (\<langle>x\<langle>)) > length u"
      by (metis c_def left_config_lt_right_config)
    moreover from fk_mstep_c wpy_def zs_defs have "(rev zs @ rev (\<langle>x\<langle>), p, y) \<rightarrow>{m} (u, q, v)"
      using c_def by simp
    moreover from left c_def left_config_def have "length u < length (\<langle>x\<langle>)" by simp

    ultimately  show thesis 
      using that right_to_left_impl_reachable_substring w_app_def rev_rev_ident nat_less_le 
      by (metis length_rev wpy_reachable)
  qed
  have bound_interm: "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', zs @ y)" 
    using wpy_jstep rtranclp_power wpy_reachable by (metis (no_types, lifting) rtranclp_trans)
  then have rev_zs_v_eq_z: "zs @ y = \<rangle>z\<rangle>" using unchanged_word by force
  with left c_def left_config_def have "length u < length (rev (\<langle>x\<langle>))" by simp 
  with reachable_from_right_impl_reachable_without_loops bound_interm revx_lstep c_def
  obtain q'' l' where q''_bound_defs:               
    "l' < l"
    "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>{l'} (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)"
    "(rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>) \<rightarrow>{l-l'} c"
    "\<forall>i\<le>l-l'. \<forall>u' q' v'. ((rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>) \<rightarrow>{i} (u', q', v')) \<and> i \<noteq> 0 \<longrightarrow> length u' < length (rev (\<langle>x\<langle>))"
    using rev_zs_v_eq_z stepn_decompose[of _ l "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" _ c]
    by (smt (verit, ccfv_threshold) less_or_eq_imp_le)
  then obtain g :: "nat \<Rightarrow> 'a config" where g_defs:
    "g 0 = (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)"
    "g (l-l') = c"
    "\<forall>i<l-l'. g i \<rightarrow> g (Suc i)" using relpowp_fun_conv rev_zs_v_eq_z by metis
  have g_gt_0_left: "\<forall>i\<le>l-l'. i \<noteq> 0 \<longrightarrow> left_config (g i)"
  proof (rule allI, rule impI, rule impI)
    fix i
    assume i_leq_diff: "i \<le> l - l'"
      and i_neq_0: "i \<noteq> 0"
    moreover have "(rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>) \<rightarrow>{i} g i"
    using i_leq_diff proof (induction i)
      case (Suc i)
      from Suc(2) consider "Suc i < l-l'" | "Suc i = l-l'" by linarith
      then show ?case using Suc g_defs q''_bound_defs(3) by cases force+ 
    qed (use g_defs in simp)
    moreover obtain u q v where "g  i = (u, q, v)" using prod_cases3 by blast
    ultimately show "left_config (g i)" using q''_bound_defs unfolding left_config_def by auto
  qed
  hence g_lstep_all: "\<forall>i<l-l'. i \<noteq> 0 \<longrightarrow> g i \<rightarrow>\<^sup>L g (Suc i)" using g_defs left_config_def left
    by (simp add: lstep)
  hence g_lstepn: "g (Suc 0) \<rightarrow>\<^sup>L{l-l'-1} g (l-l')"
  proof -
    obtain h where "\<forall>n. h n = g (Suc n)" by fast
    hence
      "h (l-l'-1) = g (l-l')"
      "\<forall>i<l-l'-1. h i \<rightarrow>\<^sup>L h (Suc i)"
      "h 0 = g (Suc 0)"
      using g_lstep_all Suc_pred' q''_bound_defs(1) zero_less_diff
      by (presburger, simp+)
    thus ?thesis using relpowp_fun_conv[where x="g (Suc 0)" and y="g (l-l')"] by auto
  qed
  obtain r where g1_def: "g (Suc 0) = (rev x_init, r, x_end # \<rangle>z\<rangle>)"
  proof -
    from g_gt_0_left have g_1_left: "left_config (g (Suc 0))" using q''_bound_defs(1) by simp
    then obtain r where r_def: "nxt M q'' (hd (\<rangle>z\<rangle>)) = (r, Left)"
    proof -
      have "\<exists>r. nxt M q'' (hd (\<rangle>z\<rangle>)) = (r, Left)"
      proof (rule ccontr)
        assume "\<not>?thesis"
        then obtain r where "nxt M q'' (hd (\<rangle>z\<rangle>)) = (r, Right)" using dir.exhaust
          by (metis (full_types) old.prod.exhaust)
        hence "(rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>) \<rightarrow> ((hd (\<rangle>z\<rangle>)) # rev (\<langle>x\<langle>), r, tl (\<rangle>z\<rangle>))"
          by (metis append_is_Nil_conv list.collapse not_Cons_self2 step_right)
        hence "g (Suc 0) = ..." using g_defs q''_bound_defs(1) by force
        thus False using g_1_left left_config_def by simp
      qed
      thus thesis using that by blast
    qed
    have "(rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, r, x_end # \<rangle>z\<rangle>)" 
    proof -
      from x_defs have "(rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>) = (x_end # rev x_init, q'', \<rangle>z\<rangle>)" by simp
      also from r_def have "... \<rightarrow> (rev x_init, r, x_end # \<rangle>z\<rangle>)" 
        by (metis (no_types, opaque_lifting) Nil_is_append_conv list.exhaust list.sel(1) step_left)
      finally show ?thesis .
    qed
    thus thesis using g_defs that q''_bound_defs(1) by fastforce
  qed
  hence "(rev x_init, r, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* c" using g_defs(2) g_lstepn by (metis rtranclp_power)
  moreover from g_defs(1,3) g1_def have "(rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, r, x_end # \<rangle>z\<rangle>)" 
    using q''_bound_defs(1) by fastforce
  moreover have "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)" using q''_bound_defs(2) bound_interm rev_zs_v_eq_z 
    rtranclp_power by (metis (no_types, opaque_lifting) g_defs(1) rtranclp_trans)
  ultimately show thesis using that by blast
qed


inductive T :: "'a list \<Rightarrow> state option \<Rightarrow> state option \<Rightarrow> bool" where
  init_tr[intro]: "\<lbrakk>x @ z \<rightarrow>\<^sup>L** (rev x_init, p, x_end # \<rangle>z\<rangle>); 
              (rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T z None (Some q)" |

  init_no_tr[intro]: "\<nexists>q. x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<Longrightarrow> T z None None" |

  some_tr[intro]: "\<lbrakk>x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>); 
              (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q', x_end # \<rangle>z\<rangle>); 
              (rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, p', x_end # \<rangle>z\<rangle>); 
              (rev x_init, p', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T z (Some q) (Some p)" |
                                                       (*Following notation in Kozen, p. 124*)
                                                       
  no_tr[intro]:   "\<lbrakk>x @ z \<rightarrow>**c; c \<rightarrow>\<^sup>R* (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>); 
              (rev (\<langle>x\<langle>), p, \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q, x_end # \<rangle>z\<rangle>); 
              \<nexists>q' q''. (rev x_init, q, x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q', x_end # \<rangle>z\<rangle>) \<and>
              (rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q'', \<rangle>z\<rangle>)\<rbrakk> \<Longrightarrow> T z (Some p) None" 

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
proof (cases p)
  case None
  obtain q' where "x @ z \<rightarrow>\<^sup>L** (rev x_init, q', x_end # \<rangle>z\<rangle>)"
                               "(rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" 
      using assms None by auto
    hence "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by auto
    thus thesis using that by simp
next
  case (Some p')
  with assms obtain q' q'' where
       "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>)" 
       "(rev (\<langle>x\<langle>), p', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q', x_end # \<rangle>z\<rangle>)"
       "(rev x_init, q', x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, q'', x_end # \<rangle>z\<rangle>)"
       "(rev x_init, q'', x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by auto
    hence "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)" by fastforce            
    then show thesis using that by simp
qed

lemma boundary_cross_impl_T:
  assumes "x @ z \<rightarrow>** (rev x_init, p, x_end # \<rangle>z\<rangle>)"
          "(rev x_init, p, x_end # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q, \<rangle>z\<rangle>)"
  obtains q' where "T z q' (Some q)"
proof (cases "x @ z \<rightarrow>\<^sup>L** (rev x_init, p, x_end # \<rangle>z\<rangle>)")
  case False
  then obtain q' q'' where "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" 
                           "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow> (rev x_init, q'', x_end # \<rangle>z\<rangle>)"
                           "(rev x_init, q'', x_end # \<rangle>z\<rangle>) \<rightarrow>\<^sup>L* (rev x_init, p, x_end # \<rangle>z\<rangle>)"
    by (metis assms(1) left_config_def length_append_singleton length_rev lessI
        not_left_reachable_impl_right_boundary_cross x_is_init_app_end)
  hence "T z (Some q') (Some q)" using assms by blast
  then show ?thesis using that by simp
qed (use that assms in blast)


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
  then show thesis
  proof (cases ys)
    case Nil
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
    case (Cons b bs)
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
  "card (\<T> z) \<le> (Suc (card (states M))) ^ 2"
proof -
  let ?S = "{Some q | q. q \<in> states M} \<union> {None}"
  have card_eq: "card ?S = Suc (card (states M))" 
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

lemma bij: "bij_betw (\<lambda>X. \<Union>(f ` X)) (A // {(x, y). f x = f y}) (f ` A)" sorry




context dfa2
begin

abbreviation "T \<equiv> dfa2_transition.T M" 
abbreviation "left_reachable \<equiv> dfa2_transition.left_reachable M"
abbreviation "left_config \<equiv> dfa2_transition.left_config"
abbreviation "right_config \<equiv> dfa2_transition.right_config" 
abbreviation "pf_init \<equiv> dfa2_transition.x_init"
abbreviation "pf_end \<equiv> dfa2_transition.x_end" (*Poor style?*)

definition T' :: "'a list \<Rightarrow> (state option \<times> state option) set" where
  "T' x = {(p, q). dfa2_transition.T M x [] p q}"

lemma "finite (T' ` UNIV)" sorry

lemma T_eq_impl_right_congr:
  assumes not_empty:  "x \<noteq> []" "y \<noteq> []"
      and T_eq:       "T x = T y"
      and xz_in_lang: "x @ z \<in> language"
        shows "y @ z \<in> language"
proof -
    from not_empty dfa2_axioms have transition_axioms: "dfa2_transition M x" "dfa2_transition M y"
    using dfa2_transition_def unfolding dfa2_transition_axioms_def by auto
  with xz_in_lang obtain u v where x_acc_reachable: "x @ z \<rightarrow>** (u, acc M, v)" 
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
    from x_acc_reachable have "([], init M, pf_init x @ pf_end x # \<rangle>z\<rangle>) \<rightarrow>* (u, acc M, v)"
      (is "?butlast_init \<rightarrow>* _")
      by (metis append.assoc append_Cons append_Nil dfa2_transition.x_is_init_app_end mapl_app_mapr_eq_map
          transition_axioms(1))
    then obtain n where "?butlast_init \<rightarrow>{n} (u, acc M, v)" by (meson rtranclp_imp_relpowp)
    moreover have "length v < length (pf_end x # \<rangle>z\<rangle>)"
    proof -
      from dfa2_transition.reachable_right_conf_impl_substring_z[of M x z u "acc M" v,
        OF transition_axioms(1) x_acc_reachable 2]
      obtain zs where "rev (\<langle>x\<langle> @ zs) = u" "zs @ v = \<rangle>z\<rangle>" by blast
      then show ?thesis by (metis length_Suc_conv length_append not_add_less2 not_less_eq)
    qed
    moreover have butlast_reachable: "x @ z \<rightarrow>** ?butlast_init" 
    proof -
      have "([], init M, \<langle>x @ z\<rangle>) = ([], init M, \<langle>x\<langle> @ \<rangle>z\<rangle>)" by simp
      also have "... = ([], init M, butlast (\<langle>x\<langle>) @ last (\<langle>x\<langle>) # \<rangle>z\<rangle>)" by simp
      finally have "([], init M, \<langle>x @ z\<rangle>) = ?butlast_init"
        using dfa2_transition.x_defs[OF transition_axioms(1)] by simp
      thus ?thesis by (metis rtranclp.rtrancl_refl)
    qed
    ultimately obtain p' m k where p'mk_defs:
      "m + k = n"
      "?butlast_init \<rightarrow>{m} (rev (pf_init x), p', pf_end x # \<rangle>z\<rangle>)" 
      "(rev (pf_init x), p', pf_end x # \<rangle>z\<rangle>) \<rightarrow>{k} (u, acc M, v)"
      using left_to_right_impl_reachable_substring
      by (metis self_append_conv)
    from 2 have "length (rev (pf_init x)) < length u"
      using dfa2_transition.right_config_def
      by (metis dfa2_transition.x_is_init_app_end length_append_singleton length_rev less_eq_Suc_le 
          prod.inject transition_axioms(1))
    moreover from p'mk_defs(2) butlast_reachable have x_init_reachable:
      "x @ z \<rightarrow>** (rev (pf_init x), p', pf_end x # \<rangle>z\<rangle>)"
      by (metis
          \<open>([], dfa2.init M, dfa2_transition.x_init x @ dfa2_transition.x_end x # \<Sigma> z @ [\<stileturn>]) 
          \<rightarrow>* (u, acc M, v)\<close>  relpowp_imp_rtranclp unchanged_word x_acc_reachable)
    ultimately obtain p j where x_init_loopless:
      "j < k"
      "(rev (pf_init x), p', pf_end x # \<rangle>z\<rangle>) \<rightarrow>{j} (rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>)"
      "\<forall>i\<le>k-j. \<forall>u' q' v'. ((rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>) \<rightarrow>{i} (u', q', v')) \<and> i \<noteq> 0 
        \<longrightarrow> length u' > length (rev (pf_init x))" 
      using p'mk_defs(3) dfa2_transition.reachable_from_left_impl_reachable_without_loops
                          [OF transition_axioms(1)] by metis
    with x_init_reachable have loopless_reachable:
      "x @ z \<rightarrow>** (rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>)" 
      by (meson relpowp_imp_rtranclp rtranclp_trans)
    have loopless_reaches_acc: "... \<rightarrow>{k-j} (u, acc M, v)"
      using x_init_loopless(1,2) p'mk_defs(3) stepn_decompose[of j k] 
      by (meson nat_less_le)
    obtain q' where loopless_step: "(rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>) \<rightarrow> (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)"
    proof -
      obtain q' where "nxt M p (pf_end x) = (q', Right)"
      proof -
        have "\<exists>q'. nxt M p (pf_end x) = (q', Right)"
        proof (rule ccontr)
          assume "\<not>?thesis"
          then obtain q' where q'_def: "nxt M p (pf_end x) = (q', Left)"
            by (metis (full_types) dir.exhaust old.prod.exhaust)
          let ?rev = "rev (pf_init x)"
          from q'_def have "(?rev, p, pf_end x # \<rangle>z\<rangle>) \<rightarrow> (tl ?rev, q', hd ?rev # pf_end x # \<rangle>z\<rangle>)" 
            by (metis (no_types, lifting) Nil_is_append_conv Nil_is_map_conv \<open>x \<noteq> []\<close> append_Nil
                dfa2_transition.x_is_init_app_end list.distinct(1) list.exhaust_sel list.sel(3) rev.simps(2) 
                step_left transition_axioms(1))
          hence "(?rev, p, pf_end x # \<rangle>z\<rangle>) \<rightarrow>{Suc 0} (tl ?rev, q', hd ?rev # pf_end x # \<rangle>z\<rangle>)" by auto
          moreover have "length (tl ?rev) \<le> length ?rev" by simp
          ultimately show False using x_init_loopless 
            by (metis Suc_leI linorder_not_less nat.distinct(1) zero_less_diff)
        qed
        thus thesis using that by blast
      qed
      hence "(rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>) \<rightarrow> (pf_end x # rev (pf_init x), q', \<rangle>z\<rangle>)" by blast
      moreover have "pf_end x # rev (pf_init x) = rev (\<langle>x\<langle>)" 
        using dfa2_transition.x_defs[OF transition_axioms(1)]
        by (metis dfa2_transition.x_is_init_app_end rev.simps(2) rev_rev_ident transition_axioms(1))
      ultimately show thesis using that by simp 
    qed
    hence x_reaches_acc: "... \<rightarrow>{k-j-1} (u, acc M, v)" 
      by (metis (no_types, lifting) diff_add_inverse less_iff_succ_less_eq less_imp_add_positive 
          loopless_reaches_acc nat_add_left_cancel_le relpowp_1 stepn_decompose x_init_loopless(1))
    then obtain us where u_app_def: "us @ rev (\<langle>x\<langle>) = u"
      using x_init_loopless(3) loopless_reaches_acc left_to_right_impl_substring
      by (metis "2" dfa2_transition.reachable_right_conf_impl_substring_z rev_append transition_axioms(1)
          x_acc_reachable)         
    from loopless_step dfa2_transition.boundary_cross_impl_T[OF transition_axioms(1)]
    obtain qopt where "T x z qopt (Some q')" using loopless_reachable by blast
    with T_eq have Ty: "T y z qopt (Some q')" by simp
    show ?thesis
    proof (cases rule: dfa2_transition.T.cases[OF transition_axioms(2) Ty])
      case (1 p' q)
      then have "y @ z \<rightarrow>** (rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)" using 
            dfa2_transition.left_steps_impl_steps[OF transition_axioms(2)] 1(3)
        sorry 
      also have "... \<rightarrow>* (us @ rev (\<langle>y\<langle>), acc M, v)"
      proof -
        have
          "\<forall>i\<le>k-j-1. \<forall>u' q'' v'. ((rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>{i} (u', q'', v'))
            \<longrightarrow> length (rev (\<langle>x\<langle>)) \<le> length u'"
        proof ((rule allI)+, rule impI)+
          fix i u' q'' v'
          assume i_leq_kj1: "i \<le> k-j-1"
             and stepi:  "((rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>{i} (u', q'', v'))"
          with 1(2) loopless_step have "(rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>) \<rightarrow>{Suc i} (u', q'', v')"
            by (meson relpowp_Suc_I2)
          with x_init_loopless(3) i_leq_kj1 have "length (rev (pf_init x)) < length u'"  
            by (metis Suc_diff_1 Suc_le_mono Zero_not_Suc x_init_loopless(1) zero_less_diff)
          then show "length (rev (\<langle>x\<langle>)) \<le> length u'" using 
              dfa2_transition.x_defs[OF transition_axioms(1)] 
            by (metis append_butlast_last_id length_append_singleton length_rev 
                linorder_le_less_linear list.discI not_less_eq)
        qed
        moreover from loopless_reachable loopless_step have
          "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" by auto
        moreover from x_reaches_acc u_app_def have
          "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>{k-j-1} (us @ rev (\<langle>x\<langle>), acc M, v)" by blast
        ultimately show ?thesis using u_app_def 
            x_reaches_acc all_geq_left_impl_left_indep relpowp_imp_rtranclp by metis
      qed
      finally show ?thesis unfolding language_def by blast
    next
      case (3 p' q p'')
      then have "y @ z \<rightarrow>** (rev (\<langle>y\<langle>), q', \<rangle>z\<rangle>)" using 
            dfa2_transition.left_steps_impl_steps sorry
      also have "... \<rightarrow>* (us @ rev (\<langle>y\<langle>), acc M, v)"
      proof -
        have
          "\<forall>i\<le>k-j-1. \<forall>u' q'' v'. ((rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>{i} (u', q'', v'))
            \<longrightarrow> length (rev (\<langle>x\<langle>)) \<le> length u'"
        proof ((rule allI)+, rule impI)+
          fix i u' q'' v'
          assume i_leq_kj1: "i \<le> k-j-1"
             and stepi:  "((rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>{i} (u', q'', v'))"
          with loopless_step have "(rev (pf_init x), p, pf_end x # \<rangle>z\<rangle>) \<rightarrow>{Suc i} (u', q'', v')"
            by (meson relpowp_Suc_I2)
          with x_init_loopless(3) i_leq_kj1 have "length (rev (pf_init x)) < length u'"  
            by (metis Suc_diff_1 Suc_le_mono Zero_not_Suc x_init_loopless(1) zero_less_diff)
          then show "length (rev (\<langle>x\<langle>)) \<le> length u'" using 
              dfa2_transition.x_defs[OF transition_axioms(1)] 
            by (metis append_butlast_last_id length_append_singleton length_rev 
                linorder_le_less_linear list.discI not_less_eq)
        qed
        moreover from loopless_reachable loopless_step have
          "x @ z \<rightarrow>** (rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>)" by auto
        moreover from x_reaches_acc u_app_def have
          "(rev (\<langle>x\<langle>), q', \<rangle>z\<rangle>) \<rightarrow>{k-j-1} (us @ rev (\<langle>x\<langle>), acc M, v)" by blast
        ultimately show ?thesis using u_app_def 
            x_reaches_acc all_geq_left_impl_left_indep relpowp_imp_rtranclp by metis
        qed
      finally show ?thesis unfolding language_def by blast
    qed simp+
  qed
qed
      




theorem two_way_dfa_lang_regular:
  "regular language"
proof -
  obtain x y :: "'a list" where not_empty: "x \<noteq> []" "y \<noteq> []" by blast
  hence "T x = T y \<Longrightarrow> \<forall>z. x @ z \<in> language \<longleftrightarrow> y @ z \<in> language" using T_eq_impl_right_congr
    by metis
  have "(\<forall>z. x @ z \<in> language \<longleftrightarrow> y @ z \<in> language) 
             \<longleftrightarrow> (x, y) \<in> eq_app_right language" unfolding eq_app_right_def by simp
  have "T' x = T' y \<Longrightarrow> (x, y) \<in> eq_app_right language" unfolding T'_def sorry
  have "finite (UNIV // eq_app_right language)" \<proof>
  then show "regular language" using L3_1 by auto
qed

find_theorems name: refine
  
end
end
