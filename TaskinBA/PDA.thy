theory PDA
  imports "HOL-IMP.Star"
begin

record ('q,'a,'s) pda = states        :: "'q set"
                        init_state    :: 'q
                        init_symbol   :: 's 
                        final_states  :: "'q set"
                        trans_fun     :: "'q \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('q \<times> 's list) set"
                        eps_fun       :: "'q \<Rightarrow> 's \<Rightarrow> ('q \<times> 's list) set"

locale pda =
  fixes M :: "('q, 'a, 's) pda"
  assumes init: "init_state M \<in> states M"
      and final: "final_states M \<subseteq> states M"
      and trans: "p \<in> states M \<Longrightarrow> fst ` trans_fun M p x z \<subseteq> states M"
      and eps: "p \<in> states M \<Longrightarrow> fst ` eps_fun M p z \<subseteq> states M"
      and finite_states: "finite (states M)"
      and finite_trans: "finite (trans_fun M p x z)"
      and finite_eps: "finite (eps_fun M p z)"
begin

fun step :: "'q \<times> 'a list \<times> 's list \<Rightarrow> ('q \<times> 'a list \<times> 's list) set" where
  "step (p, a#w, Z#\<alpha>) = {(q, w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> trans_fun M p a Z}
                        \<union> {(q, a#w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> eps_fun M p Z}"
| "step (p, [], Z#\<alpha>) = {(q, [], \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> eps_fun M p Z}"
| "step (_, _, []) = {}"

fun step\<^sub>1 :: "'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool" where
  "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) = ((p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<in> step (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1))"

definition steps :: "'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool" where
  "steps \<equiv> star step\<^sub>1"

lemma steps_induct[consumes 1, case_names base step]:
  assumes "steps x1 x2"
      and "\<And>p w \<alpha>. P (p, w, \<alpha>) (p, w, \<alpha>)"
      and "\<And>p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> steps (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> 
                P (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> P (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
    shows "P x1 x2"
using assms[unfolded steps_def] star.induct[of step\<^sub>1] prod_cases3 by metis

lemma steps_refl: "steps (p, w, \<alpha>) (p, w, \<alpha>)"
  unfolding steps_def by simp

lemma steps_trans: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> steps (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
  unfolding steps_def using star_trans[where ?r = step\<^sub>1] by blast

inductive stepn :: "nat \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> 'q \<times> 'a list \<times> 's list \<Rightarrow> bool" where
refl\<^sub>n: "stepn 0 (p, w, \<alpha>) (p, w, \<alpha>)" |
step\<^sub>n: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> step\<^sub>1 (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"

inductive_cases stepn_zeroE[elim!]: "stepn 0 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
thm stepn_zeroE
inductive_cases stepn_sucE[elim!]: "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
thm stepn_sucE

thm stepn.induct
thm steps_induct

declare stepn.intros[simp, intro]

lemma step\<^sub>1_stepn_one: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> stepn 1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by auto

lemma stepn_split_last: "(\<exists>p' w' \<alpha>'. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> step\<^sub>1 (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) 
                                \<longleftrightarrow> stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
  by auto

lemma stepn_split_first: "(\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) 
                                \<longleftrightarrow> stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof
  assume "\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain p' w' \<alpha>' where r1: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>')" and rN: "stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by blast
  from rN r1 show "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
    by (induction rule: stepn.induct) auto
next
  assume "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  thus "\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
  proof (induction "Suc n" "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
    thus ?case 
      by (cases n) fastforce+
  qed
qed

lemma stepn_trans:
  assumes "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "stepn m (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
    shows "\<exists>k \<le> n + m. stepn k (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
using assms(2,1) by (induction rule: stepn.induct) auto

lemma stepn_steps: "(\<exists>n. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) \<longleftrightarrow> steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof 
  assume "\<exists>n. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain n where "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by blast
  thus "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
    proof (induction rule: stepn.induct)
      case (refl\<^sub>n p w \<alpha>)
      then show ?case
        by (rule steps_refl)
    next
      case (step\<^sub>n n p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
      from step\<^sub>n(2) have "steps (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
        by (simp add: steps_def)
      with step\<^sub>n(3) show ?case
        using steps_trans by blast
    qed
next
  assume "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  thus "\<exists>n. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    proof (induction rule: steps_induct)
      case (base p w \<alpha>)
      have "stepn 0 (p, w, \<alpha>) (p, w, \<alpha>)" by simp
      then show ?case by blast
    next
      case (step p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
      from step(3) obtain n where "stepn n (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)" by blast
      with step(1) have "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
        using stepn_split_first by blast
      thus ?case by metis
    qed
qed

lemma step\<^sub>1_nonempty_stack: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> \<exists>Z' \<alpha>'. \<alpha>\<^sub>1 = Z'#\<alpha>'"
  using neq_Nil_conv by fastforce

lemma steps_empty_stack: "steps (p\<^sub>1, w\<^sub>1, []) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> p\<^sub>1 = p\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2 \<and> \<alpha>\<^sub>2 = []"
  unfolding steps_def using star.cases by fastforce

lemma step\<^sub>1_rule: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, Z#\<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>\<^sub>1 \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>\<^sub>1 \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
  by (cases w\<^sub>1) auto

lemma step\<^sub>1_rule_ext: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (\<exists>Z' \<alpha>'. \<alpha>\<^sub>1 = Z'#\<alpha>' \<and> ((\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')))"
proof
  assume asm: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain Z' \<alpha>' where *: "\<alpha>\<^sub>1 = Z'#\<alpha>'"
    using step\<^sub>1_nonempty_stack by blast
  with asm have **: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                           \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step\<^sub>1_rule by simp
  from * ** show "\<exists>Z' \<alpha>'. \<alpha>\<^sub>1 = Z'#\<alpha>' \<and> ((\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z'))" by blast
next
  assume "\<exists>Z' \<alpha>'. \<alpha>\<^sub>1 = Z' # \<alpha>' \<and> ((\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') \<or>
                                    (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 a Z'))"
  then obtain Z' \<alpha>' where "\<alpha>\<^sub>1 = Z' # \<alpha>'" and "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') \<or>
                                                (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta> @ \<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 a Z')" by blast
  thus "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using step\<^sub>1_rule by simp
qed

lemma step\<^sub>1_word_app: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> step\<^sub>1 (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
proof
  assume "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain Z' \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z'#\<alpha>'" and step: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                                                      \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step\<^sub>1_rule_ext by auto
  from step have "(\<exists>\<beta>. w\<^sub>2@w = w\<^sub>1@w \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
              \<or> (\<exists>a \<beta>. w\<^sub>1@w = a # (w\<^sub>2@w) \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')" by simp
  with \<alpha>\<^sub>1_def show "step\<^sub>1 (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
    using step\<^sub>1_rule by simp
next
  assume "step\<^sub>1 (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  then obtain Z' \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z'#\<alpha>'" and step: "(\<exists>\<beta>. w\<^sub>2@w = w\<^sub>1@w \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                                                      \<or> (\<exists>a \<beta>. w\<^sub>1@w = a # (w\<^sub>2@w) \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step\<^sub>1_rule_ext by auto
  from step have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                      \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')" by simp
  with \<alpha>\<^sub>1_def show "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using step\<^sub>1_rule by simp
qed

lemma decreasing_word: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> \<exists>w. w\<^sub>1 = w @ w\<^sub>2"
proof (induction "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: steps_induct)
  case (step p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 p' w' \<alpha>')
  from step(1) have "w\<^sub>1 = w' \<or> (\<exists>a. w\<^sub>1 = a # w')"
    using step\<^sub>1_rule_ext by auto
  with step(3) show ?case by auto
qed simp

lemma stepn_word_app: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> stepn n (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
proof
  assume "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  thus "stepn n (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)" 
  proof (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
    from step\<^sub>n(3) have "step\<^sub>1 (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3 @ w, \<alpha>\<^sub>3)"
      using step\<^sub>1_word_app by simp
    with step\<^sub>n(2) show ?case by simp
  qed simp
next
  assume "stepn n (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  thus "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
  proof (induction n "(p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 \<alpha>\<^sub>3 w\<^sub>3)
    from step\<^sub>n(3) obtain w' where w\<^sub>2_def: "w\<^sub>2 = w' @ w\<^sub>3 @ w"
      using decreasing_word[unfolded steps_def] by blast
    with step\<^sub>n(2) have *: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w' @ w\<^sub>3, \<alpha>\<^sub>2)" by simp
    from step\<^sub>n(3) w\<^sub>2_def have **: "step\<^sub>1 (p\<^sub>2, w' @ w\<^sub>3, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
      using step\<^sub>1_word_app by force
    from * ** show ?case by simp
  qed simp
qed

lemma steps_word_app: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> steps (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  using stepn_steps stepn_word_app by metis

lemma stepn_not_refl:
  assumes "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "n > 0"
using assms by fastforce

lemma steps_not_refl_split_first:
  assumes "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> steps (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms(1) obtain n where n_step: "stepn n  (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using stepn_steps by blast
  with assms(2) obtain n' where "n = Suc n'"
    using stepn_not_refl not0_implies_Suc by blast
  with n_step have "\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> stepn n' (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using stepn_split_first by simp
  thus ?thesis
    using stepn_steps by blast
qed

lemma steps_not_refl_split_last:
  assumes "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "\<exists>p' w' \<alpha>'. steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> step\<^sub>1 (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms(1) obtain n where n_step: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using stepn_steps by blast
  with assms(2) obtain n' where "n = Suc n'"
    using stepn_not_refl not0_implies_Suc by blast
  with n_step have "\<exists>p' w' \<alpha>'. stepn n' (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> step\<^sub>1 (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using stepn_split_last by simp
  thus ?thesis
    using stepn_steps by blast
qed

lemma step\<^sub>1_empty_stack: "\<not>step\<^sub>1 (p\<^sub>1, w\<^sub>1, []) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by simp

lemma step\<^sub>1_stack_app: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<gamma>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<gamma>)"
proof -
  assume asm: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain Z' \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z' # \<alpha>'" and 
      rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step\<^sub>1_rule_ext by auto
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 @ \<gamma> = \<beta>@\<alpha>'@\<gamma> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
            \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 @ \<gamma> = \<beta>@\<alpha>'@\<gamma> \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    by simp
  with \<alpha>\<^sub>1_def show "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<gamma>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<gamma>)"
    using step\<^sub>1_rule by simp
qed

lemma stepn_stack_app: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<beta>)"
  by (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct) (fastforce intro: step\<^sub>1_stack_app)+

lemma steps_stack_app: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<beta>)"
  using stepn_steps stepn_stack_app by metis

lemma step\<^sub>1_stack_drop: 
  assumes "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<gamma>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<gamma>)"
      and "\<alpha>\<^sub>1 \<noteq> []"
    shows "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof -
  from assms(1) obtain Z' \<alpha>' where \<alpha>\<^sub>1_\<gamma>_def: "\<alpha>\<^sub>1 @ \<gamma> = Z' # \<alpha>'" and
           rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2@\<gamma> = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                     \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2@\<gamma> = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step\<^sub>1_rule_ext by auto
  with assms(2) obtain \<alpha>'' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z' # \<alpha>''"
    using Cons_eq_append_conv[of Z' \<alpha>' \<alpha>\<^sub>1 \<gamma>] by auto
  with rule \<alpha>\<^sub>1_\<gamma>_def have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>'' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
           \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>'' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')" by auto
  with \<alpha>\<^sub>1_def show ?thesis
    using step\<^sub>1_rule by simp
qed

lemma split_stack: 
"stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>\<^sub>1) (p\<^sub>2, [], []) \<Longrightarrow> \<exists>p' m\<^sub>1 m\<^sub>2 y y'. w\<^sub>1 = y @ y' \<and> m\<^sub>1 + m\<^sub>2 = n 
                                          \<and> stepn m\<^sub>1 (p\<^sub>1, y, \<alpha>\<^sub>1) (p', [], []) \<and> stepn m\<^sub>2 (p', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
proof (induction n arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 \<beta>\<^sub>1)
  case (Suc n)
  thus ?case proof (cases \<alpha>\<^sub>1)
    case Nil
    hence *: "stepn 0 (p\<^sub>1, [], \<alpha>\<^sub>1) (p\<^sub>1, [], [])" by simp
    from Suc.prems Nil have **: "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
    from * ** show ?thesis by force
  next
    case (Cons Z \<alpha>)
    with Suc.prems have "stepn (Suc n) (p\<^sub>1, w\<^sub>1, Z # \<alpha> @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
    then obtain p' w' \<alpha>' where r1: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, Z # \<alpha> @ \<beta>\<^sub>1) (p', w', \<alpha>')" and rN: "stepn n (p', w', \<alpha>') (p\<^sub>2, [], [])"
      using stepn_split_first[of p\<^sub>1 w\<^sub>1 "Z # \<alpha> @ \<beta>\<^sub>1" n p\<^sub>2 "[]" "[]"] by auto 
    from r1 have step: "(\<exists>\<beta>. w' = w\<^sub>1 \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p', \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                           \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w' \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p',\<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
      using step\<^sub>1_rule by blast
    show ?thesis proof (cases)
      assume "\<exists>\<beta>. w' = w\<^sub>1 \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p', \<beta>) \<in> eps_fun M p\<^sub>1 Z"
      then obtain \<beta> where w1_def: "w\<^sub>1 = w'" and \<alpha>'_def: "\<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1" and e: "(p',\<beta>) \<in> eps_fun M p\<^sub>1 Z" by blast
      from rN \<alpha>'_def have rN2: "stepn n (p', w', (\<beta> @ \<alpha>) @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
      obtain p'' m\<^sub>1 m\<^sub>2 y y' where w'_def: "w' = y @ y'" and m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" 
          and rm1: "stepn m\<^sub>1 (p', y, \<beta> @ \<alpha>) (p'', [], [])" and rm2: "stepn m\<^sub>2 (p'', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
        using Suc.IH[OF rN2] by blast
      from w1_def w'_def have *: "w\<^sub>1 = y @ y'" by simp
      from m1_m2_n have **: "Suc m\<^sub>1 + m\<^sub>2 = Suc n" by simp
      from e have "step\<^sub>1 (p\<^sub>1, y, Z#\<alpha>) (p', y, \<beta>@\<alpha>)"
        using step\<^sub>1_rule by blast
      with rm1 Cons have ***: "stepn (Suc m\<^sub>1) (p\<^sub>1, y, \<alpha>\<^sub>1) (p'', [], [])"
        using stepn_split_first by blast
      from * ** *** rm2 show ?thesis by metis
    next
      assume "\<not>(\<exists>\<beta>. w' = w\<^sub>1 \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p', \<beta>) \<in> eps_fun M p\<^sub>1 Z)"
      with step obtain a \<beta> where w1_def: "w\<^sub>1 = a # w'" and \<alpha>'_def: "\<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1" and tr: "(p',\<beta>) \<in> trans_fun M p\<^sub>1 a Z" by blast
      from rN \<alpha>'_def have rN2: "stepn n (p', w', (\<beta> @ \<alpha>) @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
      obtain p'' m\<^sub>1 m\<^sub>2 y y' where w'_def: "w' = y @ y'" and m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" 
          and rm1: "stepn m\<^sub>1 (p', y, \<beta> @ \<alpha>) (p'', [], [])" and rm2: "stepn m\<^sub>2 (p'', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
        using Suc.IH[OF rN2] by blast
      from w1_def w'_def have *: "w\<^sub>1 = (a # y) @ y'" by simp
      from m1_m2_n have **: "Suc m\<^sub>1 + m\<^sub>2 = Suc n" by simp
      from tr have "step\<^sub>1 (p\<^sub>1, a#y, Z#\<alpha>) (p', y, \<beta>@\<alpha>)" by simp
      with rm1 Cons have ***: "stepn (Suc m\<^sub>1) (p\<^sub>1, a#y, \<alpha>\<^sub>1) (p'', [], [])"
        using stepn_split_first by blast
      from * ** *** rm2 show ?thesis by metis
    qed
  qed
qed blast

lemma state_if_step\<^sub>1:
  "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> p\<^sub>1 \<in> states M \<Longrightarrow> p\<^sub>2 \<in> states M"
proof -
  assume step1: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" and p1: "p\<^sub>1 \<in> states M" 
  then obtain Z' \<alpha>' where "\<alpha>\<^sub>1 = Z'#\<alpha>'" and rule: "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                                          \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step\<^sub>1_rule_ext by auto
  from rule p1 show ?thesis 
    using trans eps by (metis fst_conv image_subset_iff)
qed

lemma state_if_steps:
  "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> p\<^sub>1 \<in> states M \<Longrightarrow> p\<^sub>2 \<in> states M"
by (induction "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: steps_induct) (auto simp: state_if_step\<^sub>1)

definition "stack_accept \<equiv> {w | w q. steps (init_state M, w, [init_symbol M]) (q, [], [])}"

definition "final_accept \<equiv> {w | w q \<gamma>. q \<in> final_states M \<and> steps (init_state M, w, [init_symbol M]) (q, [], \<gamma>)}"

end
end