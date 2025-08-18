section\<open>Applications\<close>

theory Applications
  imports Definition Finiteness
begin \<comment>\<open>begin-theory Applications\<close>

subsection\<open>Membership Problem\<close>

theorem (in CFG) "w \<in> Lang P S \<longleftrightarrow> [(Nt S)] \<in> pre_star {map_word w}"
  unfolding Lang_def pre_star_def by (simp add: derives_eq)

subsection\<open>Subset Problem\<close>

theorem (in CFG) "Lang P S \<subseteq> L \<longleftrightarrow> [(Nt S)] \<notin> pre_star (map_lang (-L))"
proof -
  have "Lang P S \<subseteq> L \<longleftrightarrow> Lang P S \<inter> -L = {}"
    by blast
  then show ?thesis
    by (simp add: pre_star_lang)
qed

subsection\<open>Disjointness Problem\<close>

theorem (in CFG) "Lang P S \<inter> L = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star (map_lang L)"
  by (simp add: pre_star_lang)

subsection\<open>Emptiness Problem\<close>

theorem (in CFG) "Lang P S = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star (map_lang UNIV)"
proof -
  have "Lang P S = {} \<longleftrightarrow> Lang P S \<subseteq> {}"
    by blast
  then have "Lang P S = {} \<longleftrightarrow> Lang P S \<inter> UNIV = {}"
    by blast
  then show ?thesis
    using pre_star_lang[of UNIV] by simp
qed

subsection\<open>Useless Variables\<close>

theorem (in CFG) "is_reachable X \<longleftrightarrow> [Nt S] \<in> pre_star { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. True }"
proof -
  define L where "L \<equiv> { (\<alpha>::('n, 't) syms)@[Nt X]@\<beta> | \<alpha> \<beta>. True }"
  have "[Nt S] \<in> pre_star L  \<longleftrightarrow> (\<exists>w. w \<in> L \<and> [Nt S] \<Rightarrow>\<^sup>* w)"
    by (simp add: pre_star_term)
  also have "... \<longleftrightarrow> (\<exists>\<alpha> \<beta>. [Nt S] \<Rightarrow>\<^sup>* (\<alpha>@[Nt X]@\<beta>))"
    unfolding L_def by blast
  finally show ?thesis
    by (simp add: is_reachable_def is_reachable_from_def L_def)
qed

theorem (in CFG) "is_productive X \<longleftrightarrow> [Nt X] \<in> pre_star { map_word w | w. True }"
proof -
  define L where "L \<equiv> { map_word w | w. True }"
  have "[Nt X] \<in> pre_star L \<longleftrightarrow> (\<exists>w. w \<in> L \<and> [Nt X] \<Rightarrow>\<^sup>* w)"
    by (simp add: pre_star_term)
  also have "... \<longleftrightarrow> (\<exists>w. [Nt X] \<Rightarrow>\<^sup>* map_word w)"
    unfolding L_def by blast
  finally show ?thesis
    by (simp add: is_productive_def L_def)
qed

subsection\<open>Nullable Variables\<close>

theorem (in CFG) "is_nullable X \<longleftrightarrow> [Nt X] \<in> pre_star {[]}"
proof -
  have "[Nt X] \<in> pre_star {[]} \<longleftrightarrow> (\<exists>w. w \<in> {[]} \<and> [Nt X] \<Rightarrow>\<^sup>* w)"
    by (simp add: pre_star_term)
  then show ?thesis
    by (simp add: is_nullable_def)
qed

subsection\<open>Finiteness Problem\<close>

lemma (in CFG) is_infinite_check:
  "is_infinite \<longleftrightarrow> (\<exists>X. [Nt X] \<in> pre_star { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. \<alpha>@\<beta> \<noteq> [] })"
  unfolding is_infinite_def is_reachable_step_def by (auto simp: pre_star_term)

theorem (in CFG) is_infinite_by_prestar:
  assumes "is_useful_all" and "is_non_nullable_all"
  shows "finite (Lang P S) \<longleftrightarrow> (\<forall>X. [Nt X] \<notin> pre_star { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. \<alpha>@\<beta> \<noteq> [] })"
  using assms is_infinite is_infinite_check by blast

end \<comment>\<open>end-theory Applications\<close>
