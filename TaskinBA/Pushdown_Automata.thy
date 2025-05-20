theory Pushdown_Automata
imports
  HereditarilyFinite.Finitary "HOL-IMP.Star"
begin

record ('a,'s) pda = states        :: "hf set"
                     init_state    :: hf
                     init_symbol   :: 's 
                     final_states  :: "hf set"
                     trans_fun     :: "hf \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> (hf \<times> 's list) set"
                     eps_fun       :: "hf \<Rightarrow> 's \<Rightarrow> (hf \<times> 's list) set"

locale pda =
  fixes M :: "('a, 's) pda"
  assumes init[simp]: "init_state M \<in> states M"
      and final: "final_states M \<subseteq> states M"
      and trans: "p \<in> states M \<Longrightarrow> fst ` trans_fun M p x z \<subseteq> states M"
      and eps: "p \<in> states M \<Longrightarrow> fst ` eps_fun M p z \<subseteq> states M"
      and finite_states: "finite (states M)"
      and finite_trans: "finite (trans_fun M p x z)"
      and finite_eps: "finite (eps_fun M p z)"
begin

fun step :: "hf \<times> 'a list \<times> 's list \<Rightarrow> (hf \<times> 'a list \<times> 's list) set" where
  "step (p, a#w, Z#\<alpha>) = {(q, w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> trans_fun M p a Z}
                        \<union> {(q, a#w, \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> eps_fun M p Z}"
| "step (p, [], Z#\<alpha>) = {(q, [], \<beta>@\<alpha>) | q \<beta>. (q, \<beta>) \<in> eps_fun M p Z}"
| "step (_, _, []) = {}"

fun step\<^sub>1 :: "hf \<times> 'a list \<times> 's list \<Rightarrow> hf \<times> 'a list \<times> 's list \<Rightarrow> bool" where
  "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) = ((p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<in> step (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1))"

definition steps :: "hf \<times> 'a list \<times> 's list \<Rightarrow> hf \<times> 'a list \<times> 's list \<Rightarrow> bool" where
  "steps \<equiv> star step\<^sub>1"

lemma steps_refl[simp]: "steps (p, w, \<alpha>) (p, w, \<alpha>)"
  by (simp add: steps_def)

lemma steps_trans: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> steps (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
  unfolding steps_def by (fastforce simp: star_trans)

inductive stepn :: "nat \<Rightarrow> hf \<times> 'a list \<times> 's list \<Rightarrow> hf \<times> 'a list \<times> 's list \<Rightarrow> bool" where
refl\<^sub>n: "stepn 0 (p, w, \<alpha>) (p, w, \<alpha>)" |
step\<^sub>n: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> step\<^sub>1 (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3) \<Longrightarrow> stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"

inductive_cases stepn_zeroE[elim!]: "stepn 0 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
thm stepn_zeroE
inductive_cases stepn_sucE[elim!]: "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
thm stepn_sucE

declare stepn.intros[intro]

lemma stepn_refl[simp]: "stepn 0 (p, w, \<alpha>) (p, w, \<alpha>)"
  by auto

lemma step\<^sub>1_stepn_one: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> stepn 1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by auto

lemma stepn_split_last: "(\<exists>p' w' \<alpha>'. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> step\<^sub>1 (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) 
                                \<longleftrightarrow> stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by auto

lemma stepn_split_first: "(\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) 
                                \<longleftrightarrow> stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof
  assume "\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain p' w' \<alpha>' where r1: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>')" and rN: "stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by blast
  from rN r1 show "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
    by (induction rule: stepn.induct) fastforce+
next
  assume "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  thus "\<exists>p' w' \<alpha>'. step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w', \<alpha>') \<and> stepn n (p', w', \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
  proof (induction "Suc n" "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 p\<^sub>3 w\<^sub>3 \<alpha>\<^sub>3)
    thus ?case by (cases n) fastforce+
  qed
qed

lemma stepn_trans:
  assumes "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "stepn m (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
    shows "\<exists>k \<le> n + m. stepn k (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>3, w\<^sub>3, \<alpha>\<^sub>3)"
using assms(2,1) by (induction rule: stepn.induct) fastforce+

lemma stepn_steps: "(\<exists>n. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)) \<longleftrightarrow> steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
proof 
  assume "\<exists>n. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain n where "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" by blast
  thus "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" 
    using steps_def steps_trans by (induction rule: stepn.induct) fastforce+
next
  assume "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  thus "\<exists>n. stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    unfolding steps_def using stepn_split_first by (induction rule: star.induct) (auto, blast)
qed

lemma step\<^sub>1_nonempty_stack: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> \<exists>Z' \<alpha>'. \<alpha>\<^sub>1 = Z'#\<alpha>'"
  using neq_Nil_conv by fastforce

lemma steps_empty_stack: "steps (p\<^sub>1, w\<^sub>1, []) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> p\<^sub>1 = p\<^sub>2 \<and> w\<^sub>1 = w\<^sub>2 \<and> \<alpha>\<^sub>2 = []"
  unfolding steps_def using star.cases by fastforce

lemma step_rule: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, Z#\<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> (\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>\<^sub>1 \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>\<^sub>1 \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
  by (cases w\<^sub>1) fastforce+

lemma step\<^sub>1_word_app: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> step\<^sub>1 (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
proof
  assume asm: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain Z \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>'" 
    using step\<^sub>1_nonempty_stack by blast
  with asm have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                                      \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
    using step_rule by auto
  hence "(\<exists>\<beta>. w\<^sub>2@w = w\<^sub>1@w \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                                      \<or> (\<exists>a \<beta>. w\<^sub>1@w = a # (w\<^sub>2@w) \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z)" by simp
  with \<alpha>\<^sub>1_def show "step\<^sub>1 (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
    using step_rule by auto
next
  assume asm: "step\<^sub>1 (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  then obtain Z \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z#\<alpha>'" 
    using step\<^sub>1_nonempty_stack by blast
  with asm have "(\<exists>\<beta>. w\<^sub>2@w = w\<^sub>1@w \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                                      \<or> (\<exists>a \<beta>. w\<^sub>1@w = a # (w\<^sub>2@w) \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
    using step_rule by auto
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                                      \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z)" by simp
  with \<alpha>\<^sub>1_def show "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    using step_rule by auto
qed

lemma decreasing_word: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> \<exists>w. w\<^sub>1 = w @ w\<^sub>2"
  unfolding steps_def proof (induction "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: star.induct)
  case (step y)
  obtain p' w' \<alpha>' where y_def: "y = (p', w', \<alpha>')" 
    using prod_cases3 by blast
  with step(3) obtain w where w'_def: "w' = w @ w\<^sub>2" by blast
  from step(1) y_def obtain Z \<alpha>'' where "\<alpha>\<^sub>1 = Z#\<alpha>''"
    using step\<^sub>1_nonempty_stack by blast
  with step(1) y_def have "w' = w\<^sub>1 \<or> (\<exists>a. w\<^sub>1 = a # w')"
    using step_rule by blast
  with w'_def show ?case by auto
qed simp

lemma stepn_word_app: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> stepn n (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
proof
  assume "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  thus "stepn n (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)" 
    using step\<^sub>1_word_app by (induction n "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct) auto
next
  assume "stepn n (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  thus "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" proof (induction n "(p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)" arbitrary: p\<^sub>2 w\<^sub>2 \<alpha>\<^sub>2 rule: stepn.induct)
    case (step\<^sub>n n p' w' \<alpha>' p\<^sub>2 \<alpha>\<^sub>2)
    from step\<^sub>n(3) obtain w'' where w'_def: "w' = w'' @ w\<^sub>2 @ w"
      using decreasing_word[unfolded steps_def] by blast
    with step\<^sub>n(2) have *: "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p', w'' @ w\<^sub>2, \<alpha>')" by simp
    from step\<^sub>n(3) w'_def have **: "step\<^sub>1 (p', w'' @ w\<^sub>2, \<alpha>') (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      using step\<^sub>1_word_app by fastforce
    from * ** show ?case by auto
  qed simp
qed

lemma steps_append: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<longleftrightarrow> steps (p\<^sub>1, w\<^sub>1 @ w, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2 @ w, \<alpha>\<^sub>2)"
  using stepn_steps stepn_word_app by metis

lemma stepn_not_refl:
  assumes "stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
      and "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) \<noteq> (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
    shows "n > 0"
using assms by fastforce

lemma step\<^sub>1_empty_stack: "\<not>step\<^sub>1 (p\<^sub>1, w\<^sub>1, []) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  by simp

lemma step\<^sub>1_stack_app: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<gamma>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<gamma>)"
proof -
  assume asm: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)"
  then obtain Z' \<alpha>' where \<alpha>\<^sub>1_def: "\<alpha>\<^sub>1 = Z' # \<alpha>'"
    using step\<^sub>1_nonempty_stack by blast
  with asm have "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 = \<beta>@\<alpha>' \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    using step_rule by simp
  hence "(\<exists>\<beta>. w\<^sub>2 = w\<^sub>1 \<and> \<alpha>\<^sub>2 @ \<gamma> = \<beta>@\<alpha>'@\<gamma> \<and> (p\<^sub>2, \<beta>) \<in> eps_fun M p\<^sub>1 Z') 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w\<^sub>2 \<and> \<alpha>\<^sub>2 @ \<gamma> = \<beta>@\<alpha>'@\<gamma> \<and> (p\<^sub>2,\<beta>) \<in> trans_fun M p\<^sub>1 a Z')"
    by simp
  with \<alpha>\<^sub>1_def show "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<gamma>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<gamma>)"
    using step_rule by simp
qed

lemma steps_stack_app: "steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2) \<Longrightarrow> steps (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<beta>)"
unfolding steps_def proof (induction "(p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1)" "(p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2)" arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 rule: star.induct)
  case (step y)
  obtain p' w' \<alpha>' where y_def: "y = (p', w', \<alpha>')"
    using prod_cases3 by blast
  with step(3) have *: "star step\<^sub>1 (p', w', \<alpha>' @ \<beta>) (p\<^sub>2, w\<^sub>2, \<alpha>\<^sub>2 @ \<beta>)" by simp
  from step(1) y_def have **: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>) (p', w', \<alpha>' @ \<beta>)"
    using step\<^sub>1_stack_app by simp
  from * ** show ?case by (meson star.step)
qed auto

lemma split_stack: 
"stepn n (p\<^sub>1, w\<^sub>1, \<alpha>\<^sub>1 @ \<beta>\<^sub>1) (p\<^sub>2, [], []) \<Longrightarrow> \<exists>p' m\<^sub>1 m\<^sub>2 y y'. w\<^sub>1 = y @ y' \<and> m\<^sub>1 \<le> n \<and> m\<^sub>2 \<le> n 
                                          \<and> stepn m\<^sub>1 (p\<^sub>1, y, \<alpha>\<^sub>1) (p', [], []) \<and> stepn m\<^sub>2 (p', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
proof (induction n arbitrary: p\<^sub>1 w\<^sub>1 \<alpha>\<^sub>1 \<beta>\<^sub>1)
  case (Suc n)
  thus ?case proof (cases \<alpha>\<^sub>1)
    case Nil
    hence *: "stepn 0 (p\<^sub>1, [], \<alpha>\<^sub>1) (p\<^sub>1, [], [])" by simp
    from Suc.prems Nil have **: "stepn (Suc n) (p\<^sub>1, w\<^sub>1, \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
    from * ** show ?thesis by fastforce
  next
    case (Cons Z \<alpha>)
    with Suc.prems have "stepn (Suc n) (p\<^sub>1, w\<^sub>1, Z # \<alpha> @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
    then obtain p' w' \<alpha>' where r1: "step\<^sub>1 (p\<^sub>1, w\<^sub>1, Z # \<alpha> @ \<beta>\<^sub>1) (p', w', \<alpha>')" and rN:"stepn n (p', w', \<alpha>') (p\<^sub>2, [], [])"
      using stepn_split_first[of p\<^sub>1 w\<^sub>1 "Z # \<alpha> @ \<beta>\<^sub>1" n p\<^sub>2 "[]" "[]"] by auto 
    from r1 have step: "(\<exists>\<beta>. w' = w\<^sub>1 \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p', \<beta>) \<in> eps_fun M p\<^sub>1 Z) 
                                                   \<or> (\<exists>a \<beta>. w\<^sub>1 = a # w' \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p',\<beta>) \<in> trans_fun M p\<^sub>1 a Z)"
      using step_rule by blast
    show ?thesis proof (cases)
      assume "\<exists>\<beta>. w' = w\<^sub>1 \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p', \<beta>) \<in> eps_fun M p\<^sub>1 Z"
      then obtain \<beta> where w1_def: "w\<^sub>1 = w'" and \<alpha>'_def: "\<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1" and e: "(p',\<beta>) \<in> eps_fun M p\<^sub>1 Z"
        by blast
      from rN \<alpha>'_def have rN2: "stepn n (p', w', (\<beta> @ \<alpha>) @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
      obtain p'' m\<^sub>1 m\<^sub>2 y y' where w'_def: "w' = y @ y'" and  m1: "m\<^sub>1 \<le> n" and m2: "m\<^sub>2 \<le> n" 
                        and rm1: "stepn m\<^sub>1 (p', y, \<beta> @ \<alpha>) (p'', [], [])" and rm2: "stepn m\<^sub>2 (p'', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
        using Suc.IH[OF rN2] by blast
      from w1_def w'_def have *: "w\<^sub>1 = y @ y'" by simp
      from m1 have **: "Suc m\<^sub>1 \<le> Suc n" by simp
      from m2 have ***: "m\<^sub>2 \<le> Suc n" by simp
      from e have "step\<^sub>1 (p\<^sub>1, y, Z#\<alpha>) (p', y, \<beta>@\<alpha>)"
        using step_rule by blast
      with rm1 Cons have ****: "stepn (Suc m\<^sub>1) (p\<^sub>1, y, \<alpha>\<^sub>1) (p'', [], [])"
        using stepn_split_first by blast
      from * ** *** **** rm2 show ?thesis by fastforce
    next
      assume "\<not>(\<exists>\<beta>. w' = w\<^sub>1 \<and> \<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1 \<and> (p', \<beta>) \<in> eps_fun M p\<^sub>1 Z)"
      with step obtain a \<beta> where w1_def: "w\<^sub>1 = a # w'" and \<alpha>'_def: "\<alpha>' = \<beta> @ \<alpha> @ \<beta>\<^sub>1" and tr: "(p',\<beta>) \<in> trans_fun M p\<^sub>1 a Z"
        by blast
      from rN \<alpha>'_def have rN2: "stepn n (p', w', (\<beta> @ \<alpha>) @ \<beta>\<^sub>1) (p\<^sub>2, [], [])" by simp
      obtain p'' m\<^sub>1 m\<^sub>2 y y' where w'_def: "w' = y @ y'" and  m1: "m\<^sub>1 \<le> n" and m2: "m\<^sub>2 \<le> n" 
                        and rm1: "stepn m\<^sub>1 (p', y, \<beta> @ \<alpha>) (p'', [], [])" and rm2: "stepn m\<^sub>2 (p'', y', \<beta>\<^sub>1) (p\<^sub>2, [], [])"
        using Suc.IH[OF rN2] by blast
      from w1_def w'_def have *: "w\<^sub>1 = (a # y) @ y'" by simp
      from m1 have **: "Suc m\<^sub>1 \<le> Suc n" by simp
      from m2 have ***: "m\<^sub>2 \<le> Suc n" by simp
      from tr have "step\<^sub>1 (p\<^sub>1, a#y, Z#\<alpha>) (p', y, \<beta>@\<alpha>)" by simp
      with rm1 Cons have ****:  "stepn (Suc m\<^sub>1) (p\<^sub>1, a#y, \<alpha>\<^sub>1) (p'', [], [])"
        using stepn_split_first by blast
      from * ** *** **** rm2 show ?thesis by metis
    qed
  qed
qed blast 

definition "stack_accept \<equiv> {w | w q. steps (init_state M, w, [init_symbol M]) (q, [], [])}"

definition "final_accept \<equiv> {w | w q \<gamma>. q \<in> final_states M \<and> steps (init_state M, w, [init_symbol M]) (q, [], \<gamma>)}"

end

datatype 's sym_extended = Old 's | New

definition sfresh :: "hf set \<Rightarrow> hf" where
  "sfresh Q \<equiv> (SOME x. x \<notin> Q)"

definition t_fresh :: "('a, 's) pda \<Rightarrow> hf" where
  "t_fresh P \<equiv> sfresh (states P)"

definition u_fresh :: "('a, 's) pda \<Rightarrow> hf" where
  "u_fresh P \<equiv> sfresh (states P \<union> {t_fresh P})"

lemma t_new: "pda P \<Longrightarrow> t_fresh P \<notin> states P"
  unfolding t_fresh_def sfresh_def using pda.finite_states by (metis hmem_HF_iff hmem_not_refl someI_ex)

lemma t_finite: "pda P \<Longrightarrow> finite (states P \<union> {t_fresh P})" 
  using pda.finite_states by blast

lemma u_new_t: "pda P \<Longrightarrow> u_fresh P \<notin> states P \<union> {t_fresh P}"
  unfolding u_fresh_def sfresh_def using t_finite by (metis hmem_HF_iff hmem_not_refl verit_sko_ex')

abbreviation stack_final_states :: "('a, 's) pda \<Rightarrow> hf set" where
  "stack_final_states P \<equiv> states P \<union> {t_fresh P, u_fresh P}"

fun stack_to_final_trans_fun :: "('a, 's) pda \<Rightarrow> hf \<Rightarrow> 'a \<Rightarrow> 's sym_extended \<Rightarrow> (hf \<times> 's sym_extended list) set" where
  "stack_to_final_trans_fun P _ _ New = {}"
| "stack_to_final_trans_fun P q a (Old Z) = (if q \<in> states P then (\<lambda>(p, \<alpha>). (p, map (\<lambda>Z. Old Z) \<alpha>)) ` (trans_fun P q a Z) else {})"

fun stack_to_final_eps_fun :: "('a, 's) pda \<Rightarrow> hf \<Rightarrow> 's sym_extended \<Rightarrow> (hf \<times> 's sym_extended list) set" where
  "stack_to_final_eps_fun P q New = (if q = u_fresh P then {(init_state P, [Old (init_symbol P), New])} else 
                            if q \<in> states P then {(t_fresh P, [New])} else 
                              if q = t_fresh P then {(t_fresh P, [])} else {})"
| "stack_to_final_eps_fun P q (Old Z) = (if q \<in> states P then (\<lambda>(p, \<alpha>). (p, map (\<lambda>Z. Old Z) \<alpha>)) ` eps_fun P q Z else
                                          if q = t_fresh P then {(t_fresh P, [])} else {})"

abbreviation stack_to_final_pda :: "('a, 's) pda \<Rightarrow> ('a, 's sym_extended) pda" where
  "stack_to_final_pda P \<equiv> \<lparr> states = stack_final_states P, init_state = u_fresh P, init_symbol = New, final_states = {t_fresh P}, 
                    trans_fun = stack_to_final_trans_fun P, eps_fun = stack_to_final_eps_fun P\<rparr>"

lemma pda_stack_to_final: "pda P \<Longrightarrow> pda (stack_to_final_pda P)"
proof (standard, goal_cases)
  case (3 p x z)
  then show ?case 
    using t_new u_new_t pda.trans by (cases z, fastforce+)
next
  case (4 p z)
  then show ?case proof (cases z)
    case (Old Z)
    with 4(1) show ?thesis 
      using pda.eps by (cases "p \<in> states P", auto, fastforce)
  next
    case New
    with 4(1) show ?thesis 
      by (cases "p = u_fresh P", cases "p \<in> states P", cases "p = t_fresh P", auto simp: pda.init)
  qed
next
  case 5
  then show ?case by (auto simp: pda.finite_states)
next
  case (6 p x z)
  then show ?case by (cases z, auto simp: pda.finite_trans)
next
  case (7 p z)
  then show ?case by (cases z, auto simp: pda.finite_eps)
qed simp_all

lemma accepted_stack_to_final: 
  assumes "pda P" shows 
"(\<exists>q. pda.steps P (init_state P, w, [init_symbol P]) (q, [], [])) \<longleftrightarrow> (\<exists>q \<gamma>. q \<in> final_states (stack_to_final_pda P) \<and> 
  pda.steps (stack_to_final_pda P) (init_state (stack_to_final_pda P), w, [init_symbol (stack_to_final_pda P)]) (q, [], \<gamma>))"
  sorry

corollary stack_to_final: "pda P \<Longrightarrow> pda.stack_accept P = pda.final_accept (stack_to_final_pda P)"
  unfolding pda.stack_accept_def pda.final_accept_def[OF pda_stack_to_final] using accepted_stack_to_final by blast

end