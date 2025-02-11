theory UsingPumpingLemmaRe
  imports PumpingLemmaRe
begin

lemma repl_len: "length (xs\<^sup>*n) = length xs * n"
  by (simp add: length_concat sum_list_replicate)

lemma repl_mul: "((xs\<^sup>*n)\<^sup>*m) = (xs\<^sup>*(n*m))"
  by (induction m) (auto simp: replicate_add)

lemma repl_elem: "i < n \<Longrightarrow> ([y]\<^sup>*n)!i = y"
  by (induction n arbitrary: i) (auto simp: less_Suc_eq_0_disj)

lemma elem_repl: "\<forall>i<length xs. xs!i = x \<Longrightarrow> xs = ([x]\<^sup>*(length xs))"
  by (simp add: nth_equalityI repl_elem repl_len)

lemma repl_rest:
  assumes "(x\<^sup>*n) @ y = (x\<^sup>*m) @ z"
      and "n \<ge> m"
    shows "z = (x\<^sup>*(n-m)) @ y"
using assms by (smt (verit) append_assoc append_eq_append_conv concat_append le_add_diff_inverse replicate_add)

lemma repl_count: "count_list ([x]\<^sup>*n) x = n"
  by (induction n) auto

lemma repl_app: "(x\<^sup>*2) = x @x"
  by (metis One_nat_def Suc_1 append_Nil2 concat.simps(1) concat.simps(2) replicate_0 replicate_Suc)

lemma repl_dist: 
  assumes "x\<noteq>y"
      and "([x]\<^sup>*n) @ ([y]\<^sup>*m) = ([x]\<^sup>*k) @ ([y]\<^sup>*l)"
    shows "n = k \<and> m = l"
proof (rule ccontr)
  assume "\<not>(n = k \<and> m = l)"
  hence or: "n \<noteq> k \<or> m \<noteq> l" by simp
  show False proof (cases "n \<noteq> k")
    case True
    from assms(1) have x_not: "x \<notin> set [y]" by simp
    from True have "count_list (([x]\<^sup>*n)) x \<noteq> count_list (([x]\<^sup>*k)) x"
      using repl_count[of n x] repl_count[of k x] by simp
    with x_not have "count_list (([x]\<^sup>*n) @ ([y]\<^sup>*m)) x \<noteq> count_list (([x]\<^sup>*k) @ ([y]\<^sup>*l)) x" by simp
    with assms(2) show ?thesis by argo
  next
    case False
    with or have f: "m \<noteq> l" by simp
    from assms(1) have y_not: "y \<notin> set [x]" by simp
    from f have "count_list (([y]\<^sup>*m)) y \<noteq> count_list (([y]\<^sup>*l)) y"
      using repl_count[of m y] repl_count[of l y] by simp
    with y_not have "count_list (([x]\<^sup>*n) @ ([y]\<^sup>*m)) y \<noteq> count_list (([x]\<^sup>*k) @ ([y]\<^sup>*l)) y" by simp
    with assms(2) show ?thesis by argo
  qed
qed

theorem pumping_lemma_re_contr:
  assumes "finite P"
      and "\<forall>n. \<exists>w \<in> Lang P A. length w \<ge> n \<and> (\<forall>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<longrightarrow> (\<exists>i. x@(y\<^sup>*i)@z \<notin> Lang P A))" 
    shows "\<not>rlin2 P"
using assms pumping_lemma_re[of P A] by metis

theorem not_rlin2_ab:
  assumes "Lang P A = {([Tm a]\<^sup>*n)@([Tm b]\<^sup>*n)|n. n\<in>\<nat>}"
      and "a \<noteq> b" 
      and "finite P"
    shows "\<not>rlin2 P"
proof -
  have "\<forall>n. \<exists>w \<in> Lang P A. length w \<ge> n \<and> (\<forall>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<longrightarrow> (\<exists>i. x@(y\<^sup>*i)@z \<notin> Lang P A))" proof 
    fix n
    show "\<exists>w \<in> Lang P A. length w \<ge> n \<and> (\<forall>x y z. w = x@y@z \<and> length y \<ge> 1 \<and> length (x@y) \<le> n \<longrightarrow> (\<exists>i. x@(y\<^sup>*i)@z \<notin> Lang P A))" proof
        let ?w = "([Tm a]\<^sup>*n)@([Tm b]\<^sup>*n)"
        have *: "n \<le> length ?w" 
          by (simp add: repl_len)
        have **: "\<forall>x y z. ?w = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n \<longrightarrow> (\<exists>i. x @ (y\<^sup>*i) @ z \<notin> Lang P A)" proof 
          fix x
          show "\<forall>y z. ([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n \<longrightarrow> (\<exists>i. x @ (y\<^sup>*i) @ z \<notin> Lang P A)" proof
            fix y
            show "\<forall>z. ([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n \<longrightarrow> (\<exists>i. x @ (y\<^sup>*i) @ z \<notin> Lang P A)" proof 
              fix z
              show "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n \<longrightarrow> (\<exists>i. x @ (y\<^sup>*i)@ z \<notin> Lang P A)" proof 
                assume asm: "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n"
                from asm have asm1: "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = x @ y @ z" by blast
                from asm have asm2: "1 \<le> length y" by blast
                from asm have asm3: "length (x @ y) \<le> n" by blast
                let ?kx = "length x" let ?ky = "length y"
                have splitted: "x = ([Tm a]\<^sup>*?kx) \<and> y = ([Tm a]\<^sup>*?ky) \<and> z = ([Tm a]\<^sup>*(n - ?kx - ?ky)) @ ([Tm b]\<^sup>*n)" proof -
                  have "\<forall>i < n. (([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n))!i = Tm a"
                    by (metis One_nat_def length_Cons list.size(3) nat_mult_1 nth_append repl_len repl_elem)
                  with asm1 have xyz_tma: "\<forall>i < n. (x@y@z)!i = Tm a" by metis
                  with asm3 have xy_tma: "\<forall>i < length(x@y). (x@y)!i = Tm a"
                    by (metis append_assoc nth_append order_less_le_trans)
                  from xy_tma have "\<forall>i < ?kx. x!i = Tm a"
                    by (metis le_add1 length_append nth_append order_less_le_trans)
                  hence *: "x = ([Tm a]\<^sup>*?kx)"
                    using elem_repl[of x "Tm a"] by simp
                  from xy_tma have "\<forall>i < ?ky. y!i = Tm a"
                    by (metis length_append nat_add_left_cancel_less nth_append_length_plus)
                  hence **: "y = ([Tm a]\<^sup>*?ky)"
                    using elem_repl[of y "Tm a"] by simp
                  from * ** asm1 have "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = ([Tm a]\<^sup>*?kx) @ ([Tm a]\<^sup>*?ky) @ z" by simp
                  hence z_rest: "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = ([Tm a]\<^sup>*(?kx+?ky)) @ z"
                    by (simp add: replicate_add)
                  from asm3 have ***: "z = ([Tm a]\<^sup>*(n-?kx-?ky)) @ ([Tm b]\<^sup>*n)" 
                    using repl_rest[OF z_rest] by simp
                  from * ** *** show ?thesis by blast
                qed
               from splitted have "x @ (y\<^sup>*2) @ z = ([Tm a]\<^sup>*?kx) @ (([Tm a]\<^sup>*?ky)\<^sup>*2) @ ([Tm a]\<^sup>*(n - ?kx - ?ky)) @ ([Tm b]\<^sup>*n)" by simp
               also have "... = ([Tm a]\<^sup>*?kx) @ ([Tm a]\<^sup>*(?ky*2)) @ ([Tm a]\<^sup>*(n - ?kx - ?ky)) @ ([Tm b]\<^sup>*n)"
                 using repl_mul by auto
               also have "... = ([Tm a]\<^sup>*(?kx + ?ky*2 + (n - ?kx - ?ky))) @ ([Tm b]\<^sup>*n)"
                 using replicate_add append.assoc concat_append by metis
               also from asm3 have "... = ([Tm a]\<^sup>*(n+?ky)) @ ([Tm b]\<^sup>*n)"
                 by (simp add: add.commute)
               finally have wit: "x @ (y\<^sup>*2) @ z = ([Tm a]\<^sup>*(n+?ky)) @ ([Tm b]\<^sup>*n)" .
               from assms(2) have Tm_neq: "Tm a \<noteq> Tm b" by simp
               from asm2 have "([Tm a]\<^sup>*(n + ?ky)) @ ([Tm b]\<^sup>*n) \<notin> {([Tm a]\<^sup>*n)@([Tm b]\<^sup>*n)|n. n\<in>\<nat>}" 
                 using repl_dist[OF Tm_neq, of "n+?ky" n] by force
               with wit have "x @ (y\<^sup>*2) @ z \<notin> {([Tm a]\<^sup>*n)@([Tm b]\<^sup>*n)|n. n\<in>\<nat>}" by simp
               thus "\<exists>i. x @ (y\<^sup>*i) @ z \<notin> Lang P A" 
                 using assms(1) by blast
              qed
            qed
          qed
        qed
        from * ** show "n \<le> length ?w \<and> (\<forall>x y z. ?w = x @ y @ z \<and> 1 \<le> length y \<and> length (x @ y) \<le> n \<longrightarrow> (\<exists>i. x @ (y\<^sup>*i) @ z \<notin> Lang P A))" by simp
      next
        have "n \<in> \<nat>" 
          by (metis id_apply of_nat_eq_id of_nat_in_Nats)
        hence "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) \<in> {([Tm a]\<^sup>*n)@([Tm b]\<^sup>*n)|n. n\<in>\<nat>}" by blast
        thus "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) \<in> Lang P A" 
          by (simp add: assms(1)) 
      qed
   qed
  thus ?thesis 
    using pumping_lemma_re_contr[OF assms(3), of A] by simp
qed

end