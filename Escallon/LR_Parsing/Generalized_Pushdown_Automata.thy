theory Generalized_Pushdown_Automata
  imports
    Auxiliary
    Pushdown_Automata.Pushdown_Automata 
begin

record ('q, 'a) gpda = states :: "'q set"
                       init   :: 'q
                       final  :: "'q set"
                       nxt    :: "('q list \<times> 'a \<times> 'q list) set"
                       eps    :: "('q list \<times> 'q list) set"
                      

type_synonym ('q, 'a) config = "'q list \<times> 'a list"

(* Placeholder, should be states M 
consts Q :: "'s::fresh0 set" *)

locale gpda =
  fixes M :: "('q, 'a) gpda"
  assumes init:       "init M \<in> states M"
      and final:      "final M \<subseteq> states M"
      and nxt:        "(ps, a, qs) \<in> nxt M \<Longrightarrow> ps \<noteq> [] \<and> qs \<noteq> [] 
        \<and> set ps \<subseteq> states M \<and> set qs \<subseteq> states M"
      and eps:        "(ps, qs) \<in> eps M \<Longrightarrow> ps \<noteq> [] \<and> qs \<noteq> [] 
        \<and> set ps \<subseteq> states M \<and> set qs \<subseteq> states M"
      and finite:     "finite (states M)"
      and finite_nxt: "finite (nxt M)"
      and finite_eps: "finite (eps M)"
begin

inductive step :: "('q,'a) config \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
step_nxt[intro]: "(ps, a, qs) \<in> nxt M \<Longrightarrow> (ps@rs, a#w) \<turnstile> (qs@rs, w)" |
step_eps[intro]: "(ps, qs) \<in> eps M \<Longrightarrow> (ps@rs, w) \<turnstile> (qs@rs, w)"

inductive_cases step_nxtE[elim]: "(ps, a#w) \<turnstile> (qs, w)"
inductive_cases step_epsE[elim]: "(ps, w) \<turnstile> (qs, w)"

lemma step_imp_Cons:
  assumes "(ps, u) \<turnstile> (qs, v)"
  obtains p ps' q qs' where "ps = p#ps'" "qs = q#qs'"
  using assms nxt eps by cases (metis list.exhaust Nil_is_append_conv)+

lemma step_states_imp_states:
  assumes "(ps, u) \<turnstile> (qs, v)"
    "set ps \<subseteq> states M"
  shows "set qs \<subseteq> states M"
  using assms nxt eps by cases auto


abbreviation steps :: "('q,'a) config \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

abbreviation stepn :: "('q,'a) config \<Rightarrow> nat \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (\<open>_ \<turnstile>'(_') _\<close> 55) where
  "c\<^sub>0 \<turnstile>(n) c\<^sub>1 \<equiv> (step ^^ n) c\<^sub>0 c\<^sub>1"

lemma reachable_imp_substring:
  assumes "(ps, w) \<turnstile>* (qs, v)"
  obtains u where "w = u @ v"
  using assms proof (induction "(qs, v)" arbitrary: qs v thesis rule: rtranclp_induct)
  case (step y)
  from step(2) show ?case proof cases
    case (step_nxt rs a ss ts)
    with step(3)[of _ "a # v"] step(4)[of "_ @ [a]"] show ?thesis by auto
  qed (use step in auto)
qed simp

lemma steps_states_imp_states:
  assumes "(ps, u) \<turnstile>* (qs, v)"
    "set ps \<subseteq> states M"
  shows "set qs \<subseteq> states M"
  using assms by (induction rule: rtranclp_induct2)
    (use step_states_imp_states in blast)+

corollary steps_init_imp_states:
  assumes "([init M], u) \<turnstile>* (qs, v)"
  shows "set qs \<subseteq> states M"
  using steps_states_imp_states[OF assms] init by auto


definition Lang :: "'a list set" where
  "Lang \<equiv> {w. \<exists>f \<in> final M. ([init M], w) \<turnstile>* ([f], [])}"

(*

Towards gpda \<Longrightarrow> pda

definition states_of_eps :: "('s list \<times> 's list) set \<Rightarrow> 's set" where
  "states_of_eps \<E> \<equiv> \<Union>(ps, qs) \<in> \<E>. set ps \<union> set qs"

popwrt_eps should turn 

  ps \<turnstile> qs for ps = p\<^sub>0#p\<^sub>1#...#p\<^sub>n 

into

  p\<^sub>0#p\<^sub>1#...#p\<^sub>n \<turnstile> p\<^sub>1#...#p\<^sub>n \<turnstile> ... \<turnstile> p\<^sub>n \<turnstile> qs

fun popwrt_eps :: "'s set \<Rightarrow> 's list \<Rightarrow> 's list \<Rightarrow> ('s \<times> 's) list" where
  "popwrt_eps Q qs \<gamma> = undefined"



definition List_pda :: "('q, 'a, 'q) pda" where
  "List_pda \<equiv> 
    \<lparr>pda.init_state = undefined, init_symbol = undefined, final_states = undefined, delta = undefined, delta_eps = undefined\<rparr>"

*)

end

section \<open>Equivalence with PDAs\<close>

datatype ('a, 'b, 'c) sum3 = Qtyp 'a | Styp 'b | Q'typ 'c

definition gpda_of_pda :: "('q, 'a, 's) pda \<Rightarrow> (('q, 's, 'r::fresh0) sum3, 'a) gpda" where
  "gpda_of_pda M \<equiv> let 
    Q\<^sub>M = UNIV :: 'q set;
    \<Gamma> = UNIV :: 's set; 
    q\<^sub>0 = fresh0 ({}::'r set);
    q\<^sub>f = fresh0 {q\<^sub>0};
    \<Delta> = {([Qtyp p, Styp Z], a, Qtyp q # map Styp \<gamma>)|p Z a q \<gamma>. (q, \<gamma>) \<in> delta M p a Z};
    \<E> = {([Qtyp p, Styp Z], Qtyp q # map Styp \<gamma>)|p Z q \<gamma>. 
        (q, \<gamma>) \<in> delta_eps M p Z} \<union> {([Q'typ q\<^sub>0], [Qtyp (init_state M), Styp (init_symbol M)])}
        \<union> {([Qtyp f], [Q'typ q\<^sub>f])|f. f \<in> final_states M}
  in \<lparr>states = Qtyp ` Q\<^sub>M \<union> Styp ` \<Gamma> \<union> Q'typ ` {q\<^sub>0, q\<^sub>f}, init = Q'typ q\<^sub>0, final = {Q'typ q\<^sub>f}, nxt = \<Delta>, eps = \<E>\<rparr> "

lemma states_gpda_of_pda [simp]:
  "states ((gpda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) gpda) 
    = (let  q\<^sub>0 = fresh0 ({}::'r set);
      q\<^sub>f = fresh0 {q\<^sub>0} in 
    (Qtyp ` (UNIV :: 'q set)) \<union> (Styp ` (UNIV :: 's set)) \<union> (Q'typ ` {q\<^sub>0, q\<^sub>f}))"
  unfolding gpda_of_pda_def by (meson gpda.select_convs(1))

lemma gpda_of_pda_states_contain_pda_states_stack:
  "Qtyp ` UNIV \<union> Styp ` UNIV \<subseteq> states (gpda_of_pda M)"
  using states_gpda_of_pda by (metis sup_ge1)

lemma init_gpda_of_pda [simp]:
  "init ((gpda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) gpda) 
    = Q'typ (fresh0 ({}::'r set))"
  unfolding gpda_of_pda_def by (meson gpda.select_convs(2))

lemma final_gpda_of_pda[simp]:
  "final ((gpda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) gpda)
    = {Q'typ (fresh0 {fresh0 ({}::'r set)})}"
  unfolding gpda_of_pda_def by (meson gpda.select_convs(3))

lemma nxt_gpda_of_pda[simp]:
  "nxt (gpda_of_pda M) = 
    {([Qtyp p, Styp Z], a, Qtyp q # map Styp \<gamma>)|p Z a q \<gamma>. (q, \<gamma>) \<in> delta M p a Z}"
  unfolding gpda_of_pda_def by (meson gpda.select_convs(4))

definition delta_rel :: "('q, 'a, 's) pda \<Rightarrow> ('q \<times> 's \<times> 'a \<times> 'q \<times> 's list) set" where
  "delta_rel M \<equiv> {(p, Z, a, q, \<gamma>)|p Z a q \<gamma>. (q, \<gamma>) \<in> delta M p a Z}"

lemma pda_imp_finite_delta_rel:
  assumes "pda M"
  shows "finite (delta_rel M)"
proof -
  have "delta_rel M \<subseteq> UNIV \<times> UNIV \<times> UNIV \<times> (\<Union>p a Z. delta M p a Z)"
    (is "_ \<subseteq> _ \<times> _ \<times> _ \<times> _ ?Un")
    unfolding delta_rel_def by fast
  moreover from pda.finite_delta[OF assms] have "finite ?Un"
    by simp
  ultimately show ?thesis 
    by (meson finite_SigmaI finite_UNIV finite_subset)
qed

lemma bij_betw_delta_rel_gpda_of_pda_nxt:
  "bij_betw (\<lambda>(p, Z, a, q, \<gamma>). ([Qtyp p, Styp Z], a, Qtyp q # map Styp \<gamma>)) 
    (delta_rel M) (nxt (gpda_of_pda M))"
  (is "bij_betw ?f _ _")
proof -
  have "inj_on ?f (delta_rel M)"
    by standard (auto, metis list.inj_map_strong sum3.inject(2))
  moreover have "?f ` (delta_rel M) = (nxt (gpda_of_pda M))"
    unfolding delta_rel_def nxt_gpda_of_pda by (standard; standard) force+
  ultimately show ?thesis unfolding bij_betw_def by presburger
qed


lemma eps_gpda_of_pda[simp]:
  "eps ((gpda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) gpda) = 
  (let  q\<^sub>0 = fresh0 ({}::'r set);
        q\<^sub>f = fresh0 {q\<^sub>0} in 
    {([Qtyp p, Styp Z], Qtyp q # map Styp \<gamma>)|p Z q \<gamma>. 
        (q, \<gamma>) \<in> delta_eps M p Z} \<union> {([Q'typ q\<^sub>0], [Qtyp (init_state M), Styp (init_symbol M)])}
        \<union> {([Qtyp f], [Q'typ q\<^sub>f])|f. f \<in> final_states M})"
  unfolding gpda_of_pda_def by (meson gpda.select_convs(5))


lemma gpda_of_pda_nxt_imp_two:
  assumes "(ps, a, qs) \<in> nxt (gpda_of_pda M)"
  shows "\<exists>p Z. ps = [Qtyp p, Styp Z]"
  using assms unfolding nxt_gpda_of_pda by blast


lemma gpda_of_pda_nxt_imp_pda_delta:
  assumes "(ps, a, qs) \<in> nxt (gpda_of_pda M)"
  obtains p Z q \<gamma> where "ps = [Qtyp p, Styp Z]" "qs = Qtyp q # map Styp \<gamma>" "(q, \<gamma>) \<in> delta M p a Z"
  using assms unfolding nxt_gpda_of_pda by blast

lemma
  assumes "pda P"
  shows "gpda (gpda_of_pda P)"
proof (unfold_locales, goal_cases)
  case 1
  then show ?case using init_gpda_of_pda states_gpda_of_pda
    by (metis Un_iff image_eqI insertCI)
next
  case 2
  then show ?case using states_gpda_of_pda final_gpda_of_pda 
    by (smt (verit, ccfv_threshold) Un_iff empty_iff image_eqI insert_iff subsetI)
next
  case (3 ps a qs)
  from gpda_of_pda_nxt_imp_pda_delta[OF this] obtain p Z q \<gamma> where ps_qs_defs:
    "ps = [Qtyp p, Styp Z]"
    "qs = Qtyp q # map Styp \<gamma>"
    by metis
  hence "set qs \<subseteq> Qtyp ` UNIV \<union> Styp ` UNIV" "set ps \<subseteq> Qtyp ` UNIV \<union> Styp ` UNIV"
    by auto
  with ps_qs_defs show ?case 
    using gpda_of_pda_states_contain_pda_states_stack by auto
next
  case (4 ps qs)
  then show ?case sorry
next
  case 5
  then show ?case unfolding states_gpda_of_pda 
    by (metis finite.simps finite_UNIV finite_Un finite_imageI)
next
  case 6
  then show ?case 
    using pda_imp_finite_delta_rel[OF assms] bij_betw_delta_rel_gpda_of_pda_nxt
      bij_betw_finite by auto
next
  case 7
  then show ?case sorry
qed


theorem Cfg_imp_gpda:
  fixes G :: "('n, 't) Cfg"
  obtains M :: "('q, 't) gpda" where "gpda.Lang M = LangS G" 
  sorry


end
