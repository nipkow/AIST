theory PumpingLemmaRe
  imports DFA_rlin2
begin

abbreviation repl :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<^sup>*/_")
  where "xs\<^sup>*n \<equiv> concat (replicate n xs)"

lemma nxts_cycle:
  assumes "rlin2 P"
      and "m = card (Nts P)"
      and "B \<in> nxts_rlin2_set P {A} w"
      and "length w \<ge> m"
    shows "\<exists>x y z C. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> m \<and>
              C \<in> nxts_rlin2_set P {A} x \<and> C \<in> nxts_rlin2_set P {C} y \<and> B \<in> nxts_rlin2_set P {C} z"
  sorry

lemma nxts_trans0:
  assumes "B \<in> nxts_rlin2_set P (nxts_rlin2_set P {A} x) z"
  shows "B \<in> nxts_rlin2_set P {A} (x@z)"
  by (metis assms foldl_append nxts_rlin2_set_def)

lemma nxt_mono:
  assumes "A \<subseteq> B"
  shows "nxt_rlin2_set P A a \<subseteq> nxt_rlin2_set P B a"
  unfolding nxt_rlin2_set_def using assms by blast

lemma nxts_mono:
  assumes "A \<subseteq> B"
  shows "nxts_rlin2_set P A w \<subseteq> nxts_rlin2_set P B w"
  unfolding nxts_rlin2_set_def proof (induction w rule:rev_induct)
  case Nil
  then show ?case by (simp add: assms)
next
  case (snoc x xs)
  then show ?case 
    using nxt_mono[of "foldl (nxt_rlin2_set P) A xs" "foldl (nxt_rlin2_set P) B xs" P x] by simp
qed

lemma nxts_trans1:
  assumes "M \<subseteq> nxts_rlin2_set P {A} x"
      and "B \<in> nxts_rlin2_set P M z"
  shows "B \<in> nxts_rlin2_set P {A} (x@z)"
  using assms nxts_trans0[of B P A x z] nxts_mono[of M "nxts_rlin2_set P {A} x" P z, OF assms(1)] by auto

lemma nxts_trans2:
  assumes "C \<in> nxts_rlin2_set P {A} x"
      and "B \<in> nxts_rlin2_set P {C} z"
    shows "B \<in> nxts_rlin2_set P {A} (x@z)"
  using assms nxts_trans1[of "{C}" P A x B z] by auto 

lemma pump_cycle:
  assumes "B \<in> nxts_rlin2_set P {A} x"
      and "B \<in> nxts_rlin2_set P {B} y"
    shows "B \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i))"
using assms proof (induction i)
  case 0
  then show ?case by (simp add: assms(1))
next
  case (Suc i)
  have "B \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i))"
    using Suc.IH[OF assms] .
  with assms(2) have "B \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i)@y)"
    using nxts_trans2[of B P A "x@(y\<^sup>*i)" B y] by simp
  then show ?case
    by (metis append.right_neutral concat.simps(1) concat.simps(2) concat_append replicate_Suc replicate_append_same)
qed

lemma pumping_aux:
  assumes "rlin2 P"
      and "m = card (Nts P)"
      and "accepted P A w"
      and "length w \<ge> m"
    shows "\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> m \<and> (\<forall>i. accepted P A (x@(y\<^sup>*i)@z))"
proof -
  from assms(3) obtain Z where Z_in:"Z \<in> nxts_rlin2_set P {A} w" and Z_eps:"(Z,[])\<in>P"
    by (auto simp: accepted_def)
  obtain x y z C where *: "w = x@y@z" and **: "length y \<ge> 1" and ***: "length (x@y) \<le> m" and
              1: "C \<in> nxts_rlin2_set P {A} x" and 2: "C \<in> nxts_rlin2_set P {C} y" and 3: "Z \<in> nxts_rlin2_set P {C} z"
    using nxts_cycle[OF assms(1) assms(2) Z_in assms(4)] by auto
  have "\<forall>i. C \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i))"
    using pump_cycle[OF 1 2] by auto
  with 3 have "\<forall>i. Z \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i)@z)"
    using nxts_trans2[of C P A] by fastforce
  with Z_eps have ****: "(\<forall>i. accepted P A (x@(y\<^sup>*i)@z))"
    by (auto simp: accepted_def)
  from * ** *** **** show ?thesis by auto
qed

theorem pumping_lemma_re:
  assumes "rlin2 P"
  shows "\<exists>n. \<forall>w \<in> Lang P A. length w \<ge> n \<longrightarrow>
          (\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<and> (\<forall>i. x@(y\<^sup>*i)@z \<in> Lang P A))" 
  using pumping_aux[of P "card (Nts P)", OF assms] Lang_iff_accepted_if_rlin2[OF assms] by metis

end