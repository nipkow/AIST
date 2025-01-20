theory PumpingLemmaRe
  imports DFA_rlin2
begin

abbreviation repl :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<^sup>*/_")
  where "xs\<^sup>*n \<equiv> concat (replicate n xs)"

(* not provable? *)
lemma card_set: "A \<in> M \<Longrightarrow> card M \<ge> 1"
  sorry

lemma not_distinct:
  assumes "m = card P"
      and "m \<ge> 1"
      and "\<forall>i < length w. w ! i \<in> P"
      and "length w \<ge> Suc m"
    shows "\<exists>xs ys zs y. w = xs @ [y] @ ys @ [y] @ zs \<and> length (xs @ [y] @ ys @ [y]) \<le> Suc m"
  sorry

fun nts_nxts :: "('n,'t)Prods \<Rightarrow> 'n \<Rightarrow> 't list \<Rightarrow> 'n list set" where
  "nts_nxts P A [] = {[]}"
| "nts_nxts P A (a#w) = (\<Union>B\<in>nxt_rlin2 P A a. (\<lambda>xs. B#xs)`nts_nxts P B w)"

definition nts_nxts_ext where
"nts_nxts_ext P A w \<equiv> (\<lambda>xs. A#xs)`nts_nxts P A w"

lemma nts_nxts_ext_i0:
  "\<forall>e \<in> nts_nxts_ext P A w. e!0 = A"
  unfolding nts_nxts_ext_def by auto

lemma nts_nxts_ext_shift:
  assumes "i < length w"
  shows "\<forall>e \<in> nts_nxts_ext P A w. \<exists>e' \<in> nts_nxts P A w. e ! (Suc i) = e' ! i"
  unfolding nts_nxts_ext_def by auto

lemma nts_nxts_ext_len:
  "\<forall>e \<in> nts_nxts_ext P A w. length e = Suc (length w)"
  unfolding nts_nxts_ext_def
  by (induction P A w rule: nts_nxts.induct) auto

lemma nts_nxts_ext_path:
  assumes "i1 \<le> length w"
      and "i2 \<le> length w"
      and "i1 \<le> i2"
  shows "\<forall>e \<in> nts_nxts_ext P A w. e!i2 \<in> nxts_rlin2_set P {e!i1} (drop i1 (take i2 w))"
  sorry

lemma nts_nxts_ext_path_start:
  assumes "i \<le> length w"
  shows "\<forall>e \<in> nts_nxts_ext P A w. e ! i \<in> nxts_rlin2_set P {A} (take i w)"
  using assms nts_nxts_ext_path[of 0 w i P A] by (simp add: nts_nxts_ext_def)

lemma nts_nxts_ext_path_full:
  "\<forall>e \<in> nts_nxts_ext P A w. last e \<in> nxts_rlin2_set P {A} w"
  using nts_nxts_ext_path_start[of "length w" w P A] nts_nxts_ext_len[of P A w]
  by (metis diff_Suc_1 dual_order.refl last_conv_nth linorder_not_less take_all_iff take_eq_Nil zero_less_Suc)

lemma nxt_rlin2_nts:
  assumes "B\<in>nxt_rlin2 P A a"
  shows "B \<in> Nts P"
  using assms nxt_rlin2_def Nts_def nts_of_syms_def by fastforce

lemma nts_nxts_elem:
  assumes "i < length w"
  shows "\<forall>e \<in> nts_nxts P A w. e ! i \<in> Nts P"
proof
  fix e
  assume "e \<in> nts_nxts P A w"
  thus "e ! i \<in> Nts P" using assms proof (induction P A w arbitrary: i rule: nts_nxts.induct)
    case (1 P A)
    then show ?case by simp
  next
    case (2 P A a w)
    then show ?case sorry
  qed
qed

lemma nts_nxts_ext_elem:
  assumes "A \<in> Nts P"
      and "i \<le> length w"
  shows "\<forall>e \<in> nts_nxts_ext P A w. e ! i \<in> Nts P"
proof (cases "i = 0")
  case True
  then show ?thesis
    by (simp add: assms(1) nts_nxts_ext_i0)
next
  case False
  show ?thesis proof
    fix e
    assume e_def: "e \<in> nts_nxts_ext P A w"
    from False e_def assms(2) have "\<exists>e' \<in> nts_nxts P A w. e ! i = e' ! (i-1)"
      using nts_nxts_ext_shift[of "i-1" w P A] by simp
    then obtain e' where e'_def: "e' \<in> nts_nxts P A w" and e_ind: "e ! i = e' ! (i-1)"
      by blast
    from False e'_def assms(2) have "e' ! (i-1) \<in> Nts P"
      using nts_nxts_elem[of "i-1" w P A] by simp
    with e_ind show "e ! i \<in> Nts P" by simp
  qed
qed

lemma nts_nxts_ext_pick:
  assumes "B \<in> nxts_rlin2_set P {A} w"
  shows "\<exists>e \<in> nts_nxts_ext P A w. last e = B"
  unfolding nts_nxts_ext_def using assms proof (induction P A w arbitrary: B rule: nts_nxts.induct)
  case (1 P A)
  then show ?case sorry
next
  case (2 P A a w)
  then show ?case sorry
qed


lemma nxts_split_cycle:
  assumes "A \<in> Nts P"
      and "m = card (Nts P)"
      and "B \<in> nxts_rlin2_set P {A} w"
      and "length w \<ge> m"
    shows "\<exists>x y z C. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> m \<and>
              C \<in> nxts_rlin2_set P {A} x \<and> C \<in> nxts_rlin2_set P {C} y \<and> B \<in> nxts_rlin2_set P {C} z"
proof -
  let ?nts = "nts_nxts_ext P A w"
  obtain e where e_def: "e \<in> ?nts" and e_last: "last e = B"
    using nts_nxts_ext_pick[of B P A w, OF assms(3)] by auto
  from e_def have e_len: "length e = Suc (length w)"
    using nts_nxts_ext_len[of P A w] by simp
  from e_len e_def have e_elem: "\<forall>i < length e. e!i \<in> Nts P"
    using nts_nxts_ext_elem[OF assms(1)] by (auto simp: less_Suc_eq_le)
  from assms(1) assms(2) have m_geq_1: "m \<ge> 1"
    using card_set[of A "Nts P"] by simp
  from assms(4) e_len have "\<exists>xs ys zs y. e = xs @ [y] @ ys @ [y] @ zs \<and> length (xs @ [y] @ ys @ [y]) \<le> Suc m"
    using not_distinct[OF assms(2) m_geq_1 e_elem] by simp
  then obtain xs ys zs C where e_split: "e = xs @ [C] @ ys @ [C] @ zs" and xy_len: "length (xs @ [C] @ ys @ [C]) \<le> Suc m"
    by blast
  let ?e1 = "xs @ [C]" let ?e2 = "ys @ [C]" let ?e3 = zs
  let ?x = "take (length ?e1 - 1) w" let ?y = "drop (length ?e1 - 1) (take (length ?e1+length ?e2 - 1) w)"
  let ?z = "drop (length ?e1+length ?e2 - 1) w"
  have *: "w = ?x@?y@?z"
    by (metis Nat.add_diff_assoc2 append_assoc append_take_drop_id diff_add_inverse drop_take le_add1 length_append_singleton plus_1_eq_Suc take_add)
  from e_len e_split have **: "length ?y \<ge> 1" by simp
  from xy_len have ***: "length (?x@?y) \<le> m" by simp
  have x_fac: "?x = take (length xs) w" by simp
  from ** have x_fac2: "length xs \<le> length w"  by simp
  from e_split have x_fac3: "e ! length xs = C" by simp
  from e_def x_fac x_fac3 have ****: "C \<in> nxts_rlin2_set P {A} ?x"
    using nts_nxts_ext_path_start[of "length xs" w P A, OF x_fac2] by auto
  have y_fac: "?y = drop (length xs) (take (length xs + length ys + 1) w)" by simp
  from e_len e_split have y_fac2: "length xs + length ys + 1 \<le> length w" by simp
  have y_fac3: "length xs \<le> length xs + length ys + 1" by simp
  have y_fac4: "e ! (length xs + length ys + 1) = C"
    by (metis add.right_neutral add_Suc_right append.assoc append_Cons e_split length_Cons length_append list.size(3) nth_append_length plus_1_eq_Suc)
  from e_def y_fac x_fac3 y_fac4 have *****: "C \<in> nxts_rlin2_set P {C} ?y"
    using nts_nxts_ext_path[of "length xs" w "length xs + length ys + 1" P A, OF x_fac2 y_fac2 y_fac3] by auto
  have z_fac: "?z = drop (length xs + length ys + 1) (take (length w) w)" by simp
  from e_last e_len have z_fac2: "e ! (length w) = B"
    by (metis Zero_not_Suc diff_Suc_1 last_conv_nth list.size(3))
  from e_def z_fac y_fac2 y_fac4 z_fac2 have ******: "B \<in> nxts_rlin2_set P {C} ?z"
    using nts_nxts_ext_path[of "length xs + length ys + 1" w "length w" P A] by auto
  from * ** *** **** ***** ****** show ?thesis by blast
qed

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
  thus ?case by (simp add: assms)
next
  case (snoc x xs)
  thus  ?case 
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
  thus ?case by (simp add: assms(1))
next
  case (Suc i)
  have "B \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i))"
    using Suc.IH[OF assms] .
  with assms(2) have "B \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i)@y)"
    using nxts_trans2[of B P A "x@(y\<^sup>*i)" B y] by simp
  thus ?case
    by (metis append.right_neutral concat.simps(1) concat.simps(2) concat_append replicate_Suc replicate_append_same)
qed

lemma pumping_aux:
  assumes "A \<in> Nts P"
      and "m = card (Nts P)"
      and "accepted P A w"
      and "length w \<ge> m"
    shows "\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> m \<and> (\<forall>i. accepted P A (x@(y\<^sup>*i)@z))"
proof -
  from assms(3) obtain Z where Z_in:"Z \<in> nxts_rlin2_set P {A} w" and Z_eps:"(Z,[])\<in>P"
    by (auto simp: accepted_def)
  obtain x y z C where *: "w = x@y@z" and **: "length y \<ge> 1" and ***: "length (x@y) \<le> m" and
              1: "C \<in> nxts_rlin2_set P {A} x" and 2: "C \<in> nxts_rlin2_set P {C} y" and 3: "Z \<in> nxts_rlin2_set P {C} z"
    using nxts_split_cycle[OF assms(1) assms(2) Z_in assms(4)] by auto
  have "\<forall>i. C \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i))"
    using pump_cycle[OF 1 2] by simp
  with 3 have "\<forall>i. Z \<in> nxts_rlin2_set P {A} (x@(y\<^sup>*i)@z)"
    using nxts_trans2[of C P A] by fastforce
  with Z_eps have ****: "(\<forall>i. accepted P A (x@(y\<^sup>*i)@z))"
    by (auto simp: accepted_def)
  from * ** *** **** show ?thesis by auto
qed

theorem pumping_lemma_re_aux:
  assumes "rlin2 P"
      and "A \<in> Nts P"
  shows "\<exists>n. \<forall>w \<in> Lang P A. length w \<ge> n \<longrightarrow>
          (\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<and> (\<forall>i. x@(y\<^sup>*i)@z \<in> Lang P A))" 
  using assms(2) pumping_aux[of A P "card (Nts P)"] Lang_iff_accepted_if_rlin2[OF assms(1)] by metis

theorem pumping_lemma_re:
  assumes "rlin2 P"
  shows "\<exists>n. \<forall>w \<in> Lang P A. length w \<ge> n \<longrightarrow>
          (\<exists>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<and> (\<forall>i. x@(y\<^sup>*i)@z \<in> Lang P A))" 
proof (cases "A \<in> Nts P")
  case True
  thus ?thesis
    using pumping_lemma_re_aux[OF assms True] by simp
next
  case False
  hence "Lang P A = {}"
    by (simp add: Lang_empty_if_notin_Lhss fresh_Lhss)
  thus ?thesis by simp
qed

end