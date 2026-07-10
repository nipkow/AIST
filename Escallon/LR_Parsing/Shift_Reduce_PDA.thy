theory Shift_Reduce_PDA
  imports 
    Extended_Cfg
    Generalized_Pushdown_Automata
begin

datatype ('n, 't) srpda_state = Sym "('n, 't) sym" | Init | Final

lemma map_Sym_inject_iff[simp]: "map Sym xs = map Sym ys \<longleftrightarrow> xs = ys" 
  by (metis list.inj_map_strong srpda_state.inject)

definition SRPDA :: "('n, 't) Cfg \<Rightarrow> (('n, 't) srpda_state, 't) gpda" where
  "SRPDA G \<equiv> \<lparr>gpda.states = UNIV, init = Init, final = {Final}, 
    nxt = range (\<lambda>(q, x). ([q], x, [Sym (Tm x), q])), 
    eps = {(map Sym (rev \<alpha>), [Sym (Nt A)])|A \<alpha>. (A, \<alpha>) \<in> Prods G} 
        \<union> {([Sym (Nt (Start G)), Init], [Final])}\<rparr>"

locale srpda = Extended_Cfg G for G :: "('n::fresh0, 't) Cfg" +
  fixes M :: "(('n, 't) srpda_state, 't) gpda"
  assumes srpda: "M = SRPDA G"
begin

lemma srpda_init [simp]:
  "gpda.init M = Init" using srpda unfolding SRPDA_def by simp

lemma srpda_nxt [simp]:
  "gpda.nxt M = range (\<lambda>(q, x). ([q], x, [Sym (Tm x), q]))" 
  using srpda unfolding SRPDA_def by simp

lemma srpda_eps [simp]:
  "gpda.eps M = {(map Sym (rev \<alpha>), [Sym (Nt A)])|A \<alpha>. (A, \<alpha>) \<in> Prods G} 
    \<union> {([Sym (Nt (Start G)), Init], [Final])}"
  using srpda unfolding SRPDA_def by simp

type_synonym ('nts, 'tms) config = "('nts, 'tms) srpda_state list \<times> 'tms list"

inductive step :: "('n, 't) config \<Rightarrow> ('n, 't) config \<Rightarrow> bool" 
  (infix \<open>\<turnstile>\<close> 55) where
step_nxt[intro]: "(xs, a, ys) \<in> nxt M \<Longrightarrow> (xs@zs, a#w) \<turnstile> (ys@zs, w)" |
step_eps[intro]: "(xs, ys) \<in> eps M \<Longrightarrow> (xs@zs, w) \<turnstile> (ys@zs, w)"

lemma step_cases [consumes 1, case_names shift reduce finish, cases set: srpda.step]:
  assumes "c0 \<turnstile> c1"
  obtains 
    x xs a w where "c0 = (x # xs, a # w)" "c1 = (Sym (Tm a) # x # xs, w)" |
    A \<alpha> xs w where "(A, \<alpha>) \<in> Prods G" "c0 = (map Sym (rev \<alpha>) @ xs, w)" "c1 = (Sym (Nt A) # xs, w)" |
        xs w where "c0 = (Sym (Nt (Start G)) # Init # xs, w)" "c1 = (Final # xs, w)"
  using assms by cases auto

lemma shifts [simp]:
  "(x # xs, a # w) \<turnstile> (Sym (Tm a) # x # xs, w)"
  using step_nxt by fastforce

lemma reduces [simp]:
  assumes "(A, \<alpha>) \<in> Prods G"
  shows "(map Sym (rev \<alpha>) @ \<beta>, w) \<turnstile> (Sym (Nt A) # \<beta>, w)"
  using assms step_eps by (metis (mono_tags, lifting) Un_insert_right append.simps(1,2) 
      insert_iff mem_Collect_eq srpda_eps sup_bot.right_neutral)

lemma finishes [simp]:
  "(Sym (Nt (Start G)) # Init # \<alpha>, w) \<turnstile> (Final # \<alpha>, w)"
  using step_eps by fastforce

abbreviation steps :: "('n, 't) config \<Rightarrow> ('n, 't) config \<Rightarrow> bool" (infix \<open>\<turnstile>*\<close> 55) where
  "steps \<equiv> step\<^sup>*\<^sup>*"

abbreviation stepn :: "('n, 't) config \<Rightarrow> nat \<Rightarrow> ('n, 't) config \<Rightarrow> bool" (\<open>_ \<turnstile>'(_') _\<close> 55) where
  "c\<^sub>0 \<turnstile>(n) c\<^sub>1 \<equiv> (step ^^ n) c\<^sub>0 c\<^sub>1"

lemma reachable_imp_substring:
  assumes "(xs, w) \<turnstile>* (ys, v)"
  obtains u where "w = u @ v"
  using assms proof (induction "(ys, v)" arbitrary: ys v thesis rule: rtranclp_induct)
  case (step y)
  from step(2) show ?case proof (cases rule: step.cases)
    case (step_nxt rs a ss ts)
    with step(3)[of _ "a # v"] step(4)[of "_ @ [a]"] show ?thesis by auto
  qed (use step in auto)
qed simp

lemma steps_len_dec:
  "(xs, w) \<turnstile>* (ys, v) \<Longrightarrow> length w \<ge> length v"
  using reachable_imp_substring by fastforce


lemma into_Init_impossible:
  assumes "c \<turnstile> (Init # xs, w)" 
  shows "False"
using assms by cases simp_all

lemma Init_not_Suc_reachable:
  assumes "c\<^sub>0 \<turnstile>(Suc n) (y # ys, v)"
  shows "y \<noteq> Init"
  using into_Init_impossible assms by auto

lemma reaches_Init_imp_refl:
  "c \<turnstile>* (Init # xs, w) \<Longrightarrow> c = (Init # xs, w)"
  using Init_not_Suc_reachable stepcnt_cases by metis

definition Lang :: "'t list set" where
  "Lang \<equiv> {w. ([Init], w) \<turnstile>* ([Final], [])}"

lemma in_Lang_imp_reaches_S:
  assumes "w \<in> Lang" 
  shows "([Init], w) \<turnstile>* ([Sym (Nt (Start G)), Init], [])"
proof -
  from assms have "([Init], w) \<turnstile>* ([Final], [])" unfolding Lang_def by simp
  thus ?thesis proof cases
    case (rtrancl_into_rtrancl c)
    from this(2) show ?thesis 
      by cases (use rtrancl_into_rtrancl(1) in blast)+
  qed
qed

lemma prefix_consumable:
  "(X # \<alpha>, u @ v) \<turnstile>* (map (Sym \<circ> Tm) (rev u) @ X # \<alpha>, v)"
proof (induction u arbitrary: X \<alpha>)
  case (Cons a u)
  have "(X # \<alpha>, (a # u) @ v) \<turnstile> (Sym (Tm a) # X # \<alpha>, u @ v)"
    by simp
  also from Cons.IH have "... \<turnstile>* (map (Sym \<circ> Tm) (rev u) @ (Sym \<circ> Tm) a # X # \<alpha>, v)"
    by fastforce
  finally show ?case 
    by (metis (no_types, lifting) append.assoc append_Cons append_Nil list.simps(9) rev.simps(2)
        rev_map)
qed auto

lemma Tm_top_of_stack_imp_consumed:
  assumes "c \<turnstile> (Sym (Tm a) # \<alpha>, w)" 
  shows "c = (\<alpha>, a # w)"
  using assms by cases auto

lemma eps_step_stack_indep:
  assumes "(\<alpha>, u) \<turnstile> (\<beta>, u)"
  shows "(\<alpha>, v) \<turnstile> (\<beta>, v)"
  using assms by cases 
    (simp, 
      (smt (verit, ccfv_threshold) assms not_Cons_self2 prod.inject srpda.step.cases 
        srpda.step_eps srpda_axioms)+)

lemma eps_stack_indep:
  "(\<alpha>, u) \<turnstile>* (\<beta>, u) \<Longrightarrow> (\<alpha>, v) \<turnstile>* (\<beta>, v)"
proof (induction "(\<alpha>, u)" arbitrary: \<alpha> rule: converse_rtranclp_induct)
  case (step c)
  then obtain \<gamma> w where "c = (\<gamma>, w)" using old.prod.exhaust by metis
  with step(1) have c_\<gamma>u: "c = (\<gamma>, u)"
    using steps_len_dec step.cases step.hyps(2) by fastforce
  with step(1) eps_step_stack_indep have "(\<alpha>, v) \<turnstile> (\<gamma>, v)" by blast
  with step(3) c_\<gamma>u show ?case by simp
qed simp

lemma tl_indep:
  "(\<alpha>, u @ v) \<turnstile>* (\<gamma>, v) \<Longrightarrow> (\<alpha>, u @ w) \<turnstile>* (\<gamma>, w)"
proof (induction "(\<alpha>, u @ v)" arbitrary: \<alpha> u rule: converse_rtranclp_induct)
  case (step c)
  show ?case proof (cases u)
    case Nil
    then show ?thesis using step(1,2) eps_stack_indep 
      by (metis append_Nil converse_rtranclp_into_rtranclp)
  next
    case (Cons a u')
    from step(1) show ?thesis 
      using step Cons by cases 
        (metis (no_types, lifting) append_Cons list.inject shifts converse_rtranclp_into_rtranclp 
          prod.inject,
         metis (no_types, lifting) reduces converse_rtranclp_into_rtranclp prod.inject,
         metis (no_types, lifting) finishes converse_rtranclp_into_rtranclp prod.inject)
  qed
qed simp

lemma Tms_on_stack_imp_consumed:
  "(\<alpha>, u @ v @ w) \<turnstile>* (map (Sym \<circ> Tm) (rev v) @ \<beta>, w) \<Longrightarrow> (\<alpha>, u @ v @ w) \<turnstile>* (\<beta>, v @ w)"
proof (induction v arbitrary: u w rule: rev_induct)
  case (snoc a v)
  from this(2) have 
    "(\<alpha>, u @ (v @ [a]) @ w) \<turnstile>* (map (Sym \<circ> Tm) (rev v) @ \<beta>, a # w)" (is "?steps")
    "(map (Sym \<circ> Tm) (rev v) @ \<beta>, a # w) \<turnstile> (map (Sym \<circ> Tm) (rev (v @ [a])) @ \<beta>, w)" (is "?step")
  proof -
    from snoc(2) have "?steps \<and> ?step" proof cases
      case (rtrancl_into_rtrancl c)
      then show ?thesis using Tm_top_of_stack_imp_consumed by simp
    qed simp
    thus ?steps ?step by auto
  qed
  with snoc.IH show ?case by fastforce
qed simp

lemma invariant:
  "Prods G \<turnstile> \<alpha> \<Rightarrow>r* map Tm w \<Longrightarrow> ([Init], w) \<turnstile>* (map Sym (rev \<alpha>) @ [Init], [])"
proof (induction \<alpha> rule: converse_rtranclp_induct)
  case base
  then show ?case using prefix_consumable[of _ _ w "[]"] 
    by (simp add: rev_map)
next
  case (step \<alpha> \<beta>)
  from step(1) show ?case proof cases
    case (1 A \<delta> \<gamma> v)
    from this(2) step(2) obtain u where "w = u @ v" 
      using derives_append_map_Tm[of _ "\<gamma> @ \<delta>" "map Tm v"] derivers_iff_derives 
      by (metis append.assoc derives_map_Tm_iff map_Tm_inject_iff)
    with 1 Tms_on_stack_imp_consumed[of _ _ _ "[]"] step 
      have "([Init], w) \<turnstile>* (map Sym (rev (\<gamma> @ \<delta>)) @ [Init], v)"
      by (simp add: rev_map)
    also have "... \<turnstile> (Sym (Nt A) # map Sym (rev \<gamma>) @ [Init], v)"
      using 1(3) by simp
    also have "... \<turnstile>* (map (Sym \<circ> Tm) (rev v) @ Sym (Nt A) # map Sym (rev \<gamma>) @ [Init], [])"
      using prefix_consumable[of _ _ v "[]"] by simp
    finally show ?thesis
      using 1(1) by (simp add: rev_map)
  qed
qed

lemma srpda_complete:
  "LangS G \<subseteq> Lang"
proof
  fix w
  assume "w \<in> LangS G"
  hence "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>r* map Tm w"
    unfolding Context_Free_Grammar.Lang_def using derivers_iff_derives by fast
  with invariant have "([Init], w) \<turnstile>* ([Sym (Nt (Start G)), Init], [])"
    by fastforce
  also have "... \<turnstile> ([Final], [])"
    using step_eps by fastforce
  finally show "w \<in> Lang"
    unfolding Lang_def by blast
qed

end
end
