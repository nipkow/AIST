section\<open>Applications\<close>
text\<open>\label{sec:applications}\<close>

theory Applications
  imports Definition
begin \<comment>\<open>begin-theory Applications\<close>

subsection\<open>Membership Problem\<close>

locale CFG =
  fixes P :: "('n, 't) Prods"
    and S :: 'n
begin

theorem "w \<in> Lang P S \<longleftrightarrow> [(Nt S)] \<in> pre_star P {map_word w}"
  unfolding Lang_def pre_star_def by simp

subsection\<open>Subset Problem\<close>

theorem "Lang P S \<subseteq> L \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map_lang (-L))"
proof -
  have "Lang P S \<subseteq> L \<longleftrightarrow> Lang P S \<inter> -L = {}"
    by blast
  then show ?thesis
    by (simp add: pre_star_lang)
qed

subsection\<open>Disjointness Problem\<close>

theorem "Lang P S \<inter> L = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map_lang L)"
  by (simp add: pre_star_lang)

subsection\<open>Emptiness Problem\<close>

theorem "Lang P S = {} \<longleftrightarrow> [(Nt S)] \<notin> pre_star P (map_lang UNIV)"
proof -
  have "Lang P S = {} \<longleftrightarrow> Lang P S \<subseteq> {}"
    by blast
  then have "Lang P S = {} \<longleftrightarrow> Lang P S \<inter> UNIV = {}"
    by blast
  then show ?thesis
    using pre_star_lang[of P S UNIV] by simp
qed

subsection\<open>Useless Variables\<close>

theorem "(P \<turnstile> S \<Rightarrow>\<^sup>? X) \<longleftrightarrow> [Nt S] \<in> pre_star P { \<alpha>@[Nt X]@\<beta> | \<alpha> \<beta>. True }"
proof -
  define L where "L \<equiv> { (\<alpha>::('n, 't) syms)@[Nt X]@\<beta> | \<alpha> \<beta>. True }"
  have "[Nt S] \<in> pre_star P L  \<longleftrightarrow> (\<exists>w. w \<in> L \<and> P \<turnstile> [Nt S] \<Rightarrow>* w)"
    by (simp add: pre_star_term)
  also have "... \<longleftrightarrow> (\<exists>\<alpha> \<beta>. P \<turnstile> [Nt S] \<Rightarrow>* (\<alpha>@[Nt X]@\<beta>))"
    unfolding L_def by blast
  finally show ?thesis
    by (simp add: is_reachable_from_def L_def)
qed

theorem "is_productive P X \<longleftrightarrow> [Nt X] \<in> pre_star P { map_word w | w. True }"
proof -
  define L :: "('n, 't) sym list set" where "L \<equiv> { map_word w | w. True }"
  have "[Nt X] \<in> pre_star P L \<longleftrightarrow> (\<exists>w. w \<in> L \<and> P \<turnstile> [Nt X] \<Rightarrow>* w)"
    by (simp add: pre_star_term)
  also have "... \<longleftrightarrow> (\<exists>w. P \<turnstile> [Nt X] \<Rightarrow>* map_word w)"
    unfolding L_def by blast
  finally show ?thesis
    by (simp add: is_productive_def L_def)
qed

subsection\<open>Nullable Variables\<close>

theorem "is_nullable P X \<longleftrightarrow> [Nt X] \<in> pre_star P {[]}"
proof -
  have "[Nt X] \<in> pre_star P {[]} \<longleftrightarrow> (\<exists>w. w \<in> {[]} \<and> P \<turnstile> [Nt X] \<Rightarrow>* w)"
    by (simp add: pre_star_term)
  then show ?thesis
    by (simp add: is_nullable_def)
qed

end

end \<comment>\<open>end-theory Applications\<close>
