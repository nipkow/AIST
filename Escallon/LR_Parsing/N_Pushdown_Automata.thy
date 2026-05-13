theory N_Pushdown_Automata
  imports
    Auxiliary
    Pushdown_Automata.Pushdown_Automata 
begin

record ('q, 'a) npda = states :: "'q set"
                       init   :: 'q
                       final  :: "'q set"
                       nxt  :: "'q list \<Rightarrow> 'a \<Rightarrow> 'q list set"
                       eps    :: "('q list \<times> 'q list) set"

type_synonym ('q, 'a) config = "'q list \<times> 'a list"

locale npda =
  fixes M :: "('q, 'a) npda"
  assumes init: "init M \<in> states M"
      and final: "final M \<subseteq> states M"
      and nxt: "\<lbrakk>set ps \<subseteq> states M; qs \<in> nxt M ps a\<rbrakk> \<Longrightarrow> set qs \<subseteq> states M"
      and eps: "(ps, qs) \<in> eps M \<Longrightarrow> set ps \<subseteq> states M \<and> set qs \<subseteq> states M"
      and finite: "finite (states M)"
begin

inductive step :: "('q,'a) config \<Rightarrow> ('q,'a) config \<Rightarrow> bool" (infix \<open>\<turnstile>\<close> 55) where
nxt[intro]: "qs \<in> nxt M (p#ps) a \<Longrightarrow> (p#ps@rs, a#w) \<turnstile> (qs@rs, w)" |
eps[intro]: "(p#ps, qs) \<in> eps M \<Longrightarrow> (p#ps@rs, w) \<turnstile> (qs@rs, w)"

inductive_cases step_nxtE[elim]: "(ps, a#w) \<turnstile> (qs, w)"
inductive_cases step_epsE[elim]: "(ps, w) \<turnstile> (qs, w)"

lemma step_imp_Cons[elim]:
  assumes "(ps, u) \<turnstile> (qs, v)"
  obtains p ps' where "ps = p#ps'"
  using assms by cases

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
    \<Delta> = (\<lambda>ps a. case ps of [Qtyp p, Styp Z]  \<Rightarrow> {Qtyp q # map Styp \<gamma> |q \<gamma>. (q, \<gamma>) \<in> delta M p a Z} | _ \<Rightarrow> {});
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
    (\<lambda>ps a. case ps of [Qtyp p, Styp Z]  \<Rightarrow> {Qtyp q # map Styp \<gamma> |q \<gamma>. (q, \<gamma>) \<in> delta M p a Z} | _ \<Rightarrow> {})"
  unfolding npda_of_pda_def by (meson npda.select_convs(4))

lemma eps_npda_of_pda[simp]:
  "eps ((npda_of_pda M)::(('q, 's, 'r::fresh0) sum3, 'a) npda) = 
  (let  q\<^sub>0 = fresh0 ({}::'r set);
        q\<^sub>f = fresh0 {q\<^sub>0} in 
    {([Qtyp p, Styp Z], Qtyp q # map Styp \<gamma>)|p Z q \<gamma>. 
        (q, \<gamma>) \<in> delta_eps M p Z} \<union> {([Q'typ q\<^sub>0], [Qtyp (init_state M), Styp (init_symbol M)])}
        \<union> {([Qtyp f], [Q'typ q\<^sub>f])|f. f \<in> final_states M})"
  unfolding npda_of_pda_def by (meson npda.select_convs(5))

lemma npda_of_pda_nxt_singleton:
  "nxt (npda_of_pda M) [p] a = {}"
  unfolding nxt_npda_of_pda 
  by (metis (mono_tags, lifting) list.simps(4,5) sum3.case(3) sum3.exhaust
      sum3.simps(10,11))

lemma npda_of_pda_3:
  "nxt (npda_of_pda M) (p#q#r#rs) a = {}"
  unfolding nxt_npda_of_pda 
  by (metis (mono_tags, lifting) list.simps(5) sum3.case(3) sum3.exhaust
      sum3.simps(10,11))

lemma npda_of_pda_nxt_snd_Q:
  "nxt (npda_of_pda M) (p#Qtyp q#ps) a = {}"
  unfolding nxt_npda_of_pda 
  by (metis (mono_tags, lifting) list.simps(5) sum3.case(3) sum3.exhaust
      sum3.simps(10,11))

lemma npda_of_pda_nxt_snd_Q':
  "nxt (npda_of_pda M) (p#Q'typ q#ps) a = {}"
  unfolding nxt_npda_of_pda 
  by (metis (mono_tags, lifting) list.simps(5) sum3.case(3) sum3.exhaust
      sum3.simps(10,11))

lemmas npda_of_pda_nxt_simps[simp] = npda_of_pda_nxt_singleton npda_of_pda_3 
  npda_of_pda_nxt_snd_Q npda_of_pda_nxt_snd_Q'


lemma npda_of_pda_nxt_imp_two:
  assumes "nxt (npda_of_pda M) ps a \<noteq> {}"
  shows "\<exists>p Z. ps = [Qtyp p, Styp Z]"
  using assms npda_of_pda_nxt_simps unfolding nxt_npda_of_pda 
  by (smt (verit, ccfv_SIG) list.exhaust list.simps(4,5) sum3.exhaust
      sum3.simps(10,11,12))


lemma npda_of_pda_nxt_imp_pda_delta:
  assumes "qs \<in> nxt (npda_of_pda M) ps a"
  obtains p Z q \<gamma> where "ps = [Qtyp p, Styp Z]" "qs = Qtyp q # map Styp \<gamma>" "(q, \<gamma>) \<in> delta M p a Z"
proof -
  from assms have "nxt (npda_of_pda M) ps a \<noteq> {}" by blast
  from npda_of_pda_nxt_imp_two[OF this] assms show thesis
    using that unfolding nxt_npda_of_pda by auto
qed

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
  case (3 ps qs a)
  from npda_of_pda_nxt_imp_pda_delta[OF this(2)] obtain q \<gamma> where "qs = Qtyp q # map Styp \<gamma>"
    by metis
  hence "set qs \<subseteq> Qtyp ` UNIV \<union> Styp ` UNIV"
    by auto
  then show ?case using states_npda_of_pda 
    by (metis sup.coboundedI1)
next
  case (4 ps qs)
  hence
    "(ps, qs) \<in> {([Qtyp p, Styp Z], Qtyp q # map Styp \<gamma>) |p Z q \<gamma>. (q, \<gamma>) \<in> delta_eps P p Z}
      \<union> {([Q'typ (fresh0 {})], [Qtyp (init_state P), Styp (init_symbol P)])}
      \<union> {([Qtyp f], [Q'typ (fresh0 {fresh0 {}})]) |f. f \<in> final_states P}"
    unfolding eps_npda_of_pda by meson
  then show ?case 
  proof (standard, goal_cases)
    case 1
    then show ?case 
      apply standard
      sorry
  next
    case 2
    then obtain f where "ps = [Qtyp f]" by blast
    moreover have "set qs \<subseteq> states (npda_of_pda P)" 
      using 2 unfolding states_npda_of_pda
      by (smt (verit, ccfv_threshold) Un_upper2 empty_set image_empty image_insert
          insert_subset list.simps(15) mem_Collect_eq prod.inject)
    ultimately show ?case using states_npda_of_pda  
      by (metis Un_iff empty_set empty_subsetI insert_subset list.simps(15) rangeI)
  qed
next
  case 5
  then show ?case unfolding states_npda_of_pda 
    by (metis finite.simps finite_UNIV finite_Un finite_imageI)
qed


theorem Cfg_imp_npda:
  fixes G :: "('n, 't) Cfg"
  obtains M :: "('q, 't) npda" where "npda.Lang M = LangS G" 
  sorry


end