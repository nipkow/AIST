theory N_Pushdown_Automata
  imports
    Auxiliary
    Pushdown_Automata.Pushdown_Automata 
begin

record ('q, 'a) npda = states :: "'q set"
                       init   :: 'q
                       final  :: "'q set"
                       nxt    :: "('q list \<times> 'a \<times> 'q list) set"
                       eps    :: "('q list \<times> 'q list) set"

type_synonym ('q, 'a) config = "'q list \<times> 'a list"

locale npda =
  fixes M :: "('q, 'a) npda"
  assumes init:       "init M \<in> states M"
      and final:      "final M \<subseteq> states M"
      and nxt:        "(ps, a, qs) \<in> nxt M \<Longrightarrow> ps \<noteq> [] \<and> set ps \<subseteq> states M \<and> set qs \<subseteq> states M"
      and eps:        "(ps, qs) \<in> eps M \<Longrightarrow> ps \<noteq> [] \<and> set ps \<subseteq> states M \<and> set qs \<subseteq> states M"
      and finite:     "finite (states M)"
      and finite_nxt: "finite (nxt M)"
      and finite_eps: "finite (eps M)"
begin

inductive step :: "('q,'a) config \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
step_nxt[intro]: "(ps, a, qs) \<in> nxt M \<Longrightarrow> (ps@rs, a#w) \<turnstile> (qs@rs, w)" |
step_eps[intro]: "(ps, qs) \<in> eps M \<Longrightarrow> (ps@rs, w) \<turnstile> (qs@rs, w)"

inductive_cases step_nxtE[elim]: "(ps, a#w) \<turnstile> (qs, w)"
inductive_cases step_epsE[elim]: "(ps, w) \<turnstile> (qs, w)"

lemma step_imp_Cons[elim]:
  assumes "(ps, u) \<turnstile> (qs, v)"
  obtains p ps' where "ps = p#ps'"
  using assms nxt eps by cases (metis list.exhaust Nil_is_append_conv)+


abbreviation steps :: "('q,'a) config \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

abbreviation stepn :: "('q,'a) config \<Rightarrow> nat \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (\<open>_ \<turnstile>'(_') _\<close> 55) where
  "c\<^sub>0 \<turnstile>(n) c\<^sub>1 \<equiv> (step ^^ n) c\<^sub>0 c\<^sub>1"

definition Lang :: "'a list set" where
  "Lang \<equiv> {w. \<exists>f \<in> final M. ([init M], w) \<turnstile>* ([f], [])}"

end

datatype ('a, 'b, 'c) sum3 = Qtyp 'a | Styp 'b | Q'typ 'c

definition npda_of_pda :: "('q, 'a, 's) pda \<Rightarrow> (('q, 's, 'r::fresh0) sum3, 'a) npda" where
  "npda_of_pda M \<equiv> let 
    Q\<^sub>M = UNIV :: 'q set;
    \<Gamma> = UNIV :: 's set; 
    q\<^sub>0 = fresh0 ({}::'r set);
    q\<^sub>f = fresh0 {q\<^sub>0};
    \<Delta> = {([Qtyp p, Styp Z], a, Qtyp q # map Styp \<gamma>)|p Z a q \<gamma>. (q, \<gamma>) \<in> delta M p a Z};
    \<E> = {([Qtyp p, Styp Z], Qtyp q # map Styp \<gamma>)|p Z q \<gamma>. 
        (q, \<gamma>) \<in> delta_eps M p Z} \<union> {([Q'typ q\<^sub>0], [Qtyp (init_state M), Styp (init_symbol M)])}
        \<union> {([Qtyp f], [Q'typ q\<^sub>f])|f. f \<in> final_states M}
  in \<lparr>states = Qtyp ` Q\<^sub>M \<union> Styp ` \<Gamma> \<union> Q'typ ` {q\<^sub>0, q\<^sub>f}, init = Q'typ q\<^sub>0, final = {Q'typ q\<^sub>f}, nxt = \<Delta>, eps = \<E>\<rparr> "

lemma states_npda_of_pda [simp]:
  "states ((npda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) npda) 
    = (let  q\<^sub>0 = fresh0 ({}::'r set);
      q\<^sub>f = fresh0 {q\<^sub>0} in 
    (Qtyp ` (UNIV :: 'q set)) \<union> (Styp ` (UNIV :: 's set)) \<union> (Q'typ ` {q\<^sub>0, q\<^sub>f}))"
  unfolding npda_of_pda_def by (meson npda.select_convs(1))

lemma npda_of_pda_states_contain_pda_states_stack:
  "Qtyp ` UNIV \<union> Styp ` UNIV \<subseteq> states (npda_of_pda M)"
  using states_npda_of_pda by (metis sup_ge1)

lemma init_npda_of_pda [simp]:
  "init ((npda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) npda) 
    = Q'typ (fresh0 ({}::'r set))"
  unfolding npda_of_pda_def by (meson npda.select_convs(2))

lemma final_npda_of_pda[simp]:
  "final ((npda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) npda)
    = {Q'typ (fresh0 {fresh0 ({}::'r set)})}"
  unfolding npda_of_pda_def by (meson npda.select_convs(3))

lemma nxt_npda_of_pda[simp]:
  "nxt (npda_of_pda M) = 
    {([Qtyp p, Styp Z], a, Qtyp q # map Styp \<gamma>)|p Z a q \<gamma>. (q, \<gamma>) \<in> delta M p a Z}"
  unfolding npda_of_pda_def by (meson npda.select_convs(4))

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

lemma bij_betw_delta_rel_npda_of_pda_nxt:
  "bij_betw (\<lambda>(p, Z, a, q, \<gamma>). ([Qtyp p, Styp Z], a, Qtyp q # map Styp \<gamma>)) 
    (delta_rel M) (nxt (npda_of_pda M))"
  (is "bij_betw ?f _ _")
proof -
  have "inj_on ?f (delta_rel M)"
    by standard (auto, metis list.inj_map_strong sum3.inject(2))
  moreover have "?f ` (delta_rel M) = (nxt (npda_of_pda M))"
    unfolding delta_rel_def nxt_npda_of_pda by (standard; standard) force+
  ultimately show ?thesis unfolding bij_betw_def by presburger
qed


lemma eps_npda_of_pda[simp]:
  "eps ((npda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) npda) = 
  (let  q\<^sub>0 = fresh0 ({}::'r set);
        q\<^sub>f = fresh0 {q\<^sub>0} in 
    {([Qtyp p, Styp Z], Qtyp q # map Styp \<gamma>)|p Z q \<gamma>. 
        (q, \<gamma>) \<in> delta_eps M p Z} \<union> {([Q'typ q\<^sub>0], [Qtyp (init_state M), Styp (init_symbol M)])}
        \<union> {([Qtyp f], [Q'typ q\<^sub>f])|f. f \<in> final_states M})"
  unfolding npda_of_pda_def by (meson npda.select_convs(5))


lemma npda_of_pda_nxt_imp_two:
  assumes "(ps, a, qs) \<in> nxt (npda_of_pda M)"
  shows "\<exists>p Z. ps = [Qtyp p, Styp Z]"
  using assms unfolding nxt_npda_of_pda by blast


lemma npda_of_pda_nxt_imp_pda_delta:
  assumes "(ps, a, qs) \<in> nxt (npda_of_pda M)"
  obtains p Z q \<gamma> where "ps = [Qtyp p, Styp Z]" "qs = Qtyp q # map Styp \<gamma>" "(q, \<gamma>) \<in> delta M p a Z"
  using assms unfolding nxt_npda_of_pda by blast

lemma
  assumes "pda P"
  shows "npda (npda_of_pda P)"
proof (unfold_locales, goal_cases)
  case 1
  then show ?case using init_npda_of_pda states_npda_of_pda
    by (metis Un_iff image_eqI insertCI)
next
  case 2
  then show ?case using states_npda_of_pda final_npda_of_pda 
    by (smt (verit, ccfv_threshold) Un_iff empty_iff image_eqI insert_iff subsetI)
next
  case (3 ps a qs)
  from npda_of_pda_nxt_imp_pda_delta[OF this] obtain p Z q \<gamma> where ps_qs_defs:
    "ps = [Qtyp p, Styp Z]"
    "qs = Qtyp q # map Styp \<gamma>"
    by metis
  hence "set qs \<subseteq> Qtyp ` UNIV \<union> Styp ` UNIV" "set ps \<subseteq> Qtyp ` UNIV \<union> Styp ` UNIV"
    by auto
  with ps_qs_defs show ?case 
    using npda_of_pda_states_contain_pda_states_stack by auto
next
  case (4 ps qs)
  then show ?case sorry
next
  case 5
  then show ?case unfolding states_npda_of_pda 
    by (metis finite.simps finite_UNIV finite_Un finite_imageI)
next
  case 6
  then show ?case 
    using pda_imp_finite_delta_rel[OF assms] bij_betw_delta_rel_npda_of_pda_nxt
      bij_betw_finite by auto
next
  case 7
  then show ?case sorry
qed


theorem Cfg_imp_npda:
  fixes G :: "('n, 't) Cfg"
  obtains M :: "('q, 't) npda" where "npda.Lang M = LangS G" 
  sorry


end