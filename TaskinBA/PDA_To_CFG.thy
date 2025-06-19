theory PDA_To_CFG
  imports PDA Context_Free_Grammar.Context_Free_Language
begin

datatype ('q, 's) pda_nt = Start_sym | Single_sym 'q 's 'q | List_sym 'q "'s list" 'q

context pda begin

abbreviation empty_rule :: "'q \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "empty_rule q \<equiv> {(List_sym q [] q, [])}"

abbreviation trans_rule :: "'q \<Rightarrow> 'q \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "trans_rule q\<^sub>0 q\<^sub>1 a Z \<equiv> (\<lambda>(p, \<alpha>). (Single_sym q\<^sub>0 Z q\<^sub>1, [Tm a, Nt (List_sym p \<alpha> q\<^sub>1)])) ` trans_fun M q\<^sub>0 a Z"

abbreviation eps_rule :: "'q \<Rightarrow> 'q \<Rightarrow> 's \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "eps_rule q\<^sub>0 q\<^sub>1 Z \<equiv> (\<lambda>(p, \<alpha>). (Single_sym q\<^sub>0 Z q\<^sub>1, [Nt (List_sym p \<alpha> q\<^sub>1)])) ` eps_fun M q\<^sub>0 Z"

fun split_rule :: "'q \<Rightarrow> ('q, 's) pda_nt \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "split_rule q (List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1) = {(List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1, [Nt (Single_sym p\<^sub>0 Z q), Nt (List_sym q \<alpha> p\<^sub>1)])}"
| "split_rule _ _ = {}"

abbreviation start_rule :: "'q \<Rightarrow> (('q, 's) pda_nt, 'a) Prods" where
  "start_rule q \<equiv> {(Start_sym, [Nt (List_sym (init_state M) [init_symbol M] q)])}"

abbreviation rule_set :: "(('q, 's) pda_nt, 'a) Prods" where
  "rule_set \<equiv> (\<Union>q. empty_rule q) \<union> (\<Union>q p a Z. trans_rule q p a Z) \<union> (\<Union>q p Z. eps_rule q p Z) \<union> 
                 (\<Union>q nt. split_rule q nt) \<union> (\<Union>q. start_rule q)"

definition G :: "(('q, 's) pda_nt,'a) Cfg" where
  "G \<equiv> Cfg rule_set Start_sym"

lemma split_rule_simp:
  "(A, w) \<in> split_rule q nt \<longleftrightarrow> (\<exists>p\<^sub>0 Z \<alpha> p\<^sub>1. nt = (List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1) \<and> 
                                  A = List_sym p\<^sub>0 (Z#\<alpha>) p\<^sub>1 \<and> w = [Nt (Single_sym p\<^sub>0 Z q), Nt (List_sym q \<alpha> p\<^sub>1)])"
by (induction q nt rule: split_rule.induct) auto

lemma pda_to_cfg_derive_empty:
  "Prods G \<turnstile> [Nt (List_sym p\<^sub>1 [] p\<^sub>2)] \<Rightarrow> x \<longleftrightarrow> p\<^sub>2 = p\<^sub>1 \<and> x = []"
unfolding G_def using derive_singleton[of rule_set] split_rule_simp by auto

lemma pda_to_cfg_derive_split:
  "Prods G \<turnstile> [Nt (List_sym p\<^sub>1 (Z#\<alpha>) p\<^sub>2)] \<Rightarrow> w \<longleftrightarrow> (\<exists>q. w = [Nt (Single_sym p\<^sub>1 Z q), Nt (List_sym q \<alpha> p\<^sub>2)])"
unfolding G_def using derive_singleton[of rule_set] split_rule_simp by auto

lemma pda_to_cfg_derive_single:
"Prods G \<turnstile> [Nt (Single_sym q\<^sub>0 Z q\<^sub>1)] \<Rightarrow> w \<longleftrightarrow> 
   (\<exists>p \<alpha> a. (p, \<alpha>) \<in> trans_fun M q\<^sub>0 a Z \<and> w = [Tm a, Nt (List_sym p \<alpha> q\<^sub>1)]) \<or> 
      (\<exists>p \<alpha>. (p, \<alpha>) \<in> eps_fun M q\<^sub>0 Z  \<and> w = [Nt (List_sym p \<alpha> q\<^sub>1)])"
unfolding G_def using derive_singleton[of rule_set] split_rule_simp by fastforce

lemma pda_to_cfg_derive_start:
"Prods G \<turnstile> [Nt Start_sym] \<Rightarrow> w \<longleftrightarrow> (\<exists>q. w = [Nt (List_sym (init_state M) [init_symbol M] q)])"
unfolding G_def using derive_singleton[of rule_set] split_rule_simp by auto

lemma pda_to_cfg_derives_if_stepn:
  assumes "stepn n (q, x, \<gamma>) (p, [], [])"
  shows "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>* map Tm x"
using assms proof (induction n arbitrary: x p q \<gamma> rule: less_induct)
  case (less n)
  then show ?case proof (cases \<gamma>)
    case Nil
    from less(2) have "steps (q, x, \<gamma>) (p, [], [])"
      using stepn_steps by blast
    with Nil have "q = p \<and> x = []"
      using steps_empty_stack by simp
    with Nil show ?thesis
      using pda_to_cfg_derive_empty by auto
  next
    case (Cons Z \<alpha>)
    with less(2) obtain n' where n_def: "n = Suc n'"
      using stepn_not_refl gr0_conv_Suc by blast
    with less(2) obtain q' x' \<gamma>' where step1: "step\<^sub>1 (q, x, \<gamma>) (q', x', \<gamma>')" and 
                                        stepn: "stepn n' (q', x', \<gamma>') (p, [], [])"
      using stepn_split_first[of q x \<gamma> n' p "[]" "[]"] by auto
    from Cons step1 have rule: "(\<exists>\<beta>. x' = x \<and> \<gamma>' = \<beta>@\<alpha> \<and> (q', \<beta>) \<in> eps_fun M q Z) 
                            \<or> (\<exists>a \<beta>. x = a # x' \<and> \<gamma>' = \<beta>@\<alpha> \<and> (q',\<beta>) \<in> trans_fun M q a Z)" (is "?asm \<or> _")
      using step\<^sub>1_rule by simp
    show ?thesis proof (cases)
      assume ?asm
      then obtain \<beta> where x_def: "x' = x" and \<gamma>'_split: "\<gamma>' = \<beta>@\<alpha>" and eps: "(q', \<beta>) \<in> eps_fun M q Z" by blast
      from stepn \<gamma>'_split obtain p' m\<^sub>1 m\<^sub>2 y y' where x'_def: "x' = y @ y'" and m1_m2_n': "m\<^sub>1 + m\<^sub>2 = n'" 
                  and stepm1: "stepn m\<^sub>1 (q', y, \<beta>) (p', [], [])" and stepm2: "stepn m\<^sub>2 (p', y', \<alpha>) (p, [], [])"
        using split_stack[of n' q' x' \<beta> \<alpha> p] by blast
      from n_def m1_m2_n' have m1_less_n: "m\<^sub>1 < n" by simp
      from n_def m1_m2_n' have m2_less_n: "m\<^sub>2 < n" by simp

      from Cons have "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_split by simp

      moreover from eps have "Prods G \<turnstile> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow> 
                                  [Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_single derive_append[of "Prods G" "[Nt (Single_sym q Z p')]" "[Nt (List_sym q' \<beta> p')]"
                                                            "[Nt (List_sym p' \<alpha> p)]"] by simp
      
      moreover have "Prods G \<turnstile> [Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow>* map Tm y @ [Nt (List_sym p' \<alpha> p)]"
        using derives_append[OF less(1)[OF m1_less_n stepm1]] by simp

      moreover from x_def x'_def have "Prods G \<turnstile> map Tm y @ [Nt (List_sym p' \<alpha> p)] \<Rightarrow>* map Tm x"
        using derives_prepend[OF less(1)[OF m2_less_n stepm2]] by auto

      ultimately show ?thesis by simp
    next
      assume "\<not>?asm"
      with rule obtain a \<beta> where x_def: "x = a # x'" and \<gamma>'_split: "\<gamma>' = \<beta>@\<alpha>" and trans: "(q', \<beta>) \<in> trans_fun M q a Z" by blast
      from stepn \<gamma>'_split obtain p' m\<^sub>1 m\<^sub>2 y y' where x'_def: "x' = y @ y'" and m1_m2_n': "m\<^sub>1 + m\<^sub>2 = n'" 
                  and stepm1: "stepn m\<^sub>1 (q', y, \<beta>) (p', [], [])" and stepm2: "stepn m\<^sub>2 (p', y', \<alpha>) (p, [], [])"
        using split_stack[of n' q' x' \<beta> \<alpha> p] by blast
      from n_def m1_m2_n' have m1_less_n: "m\<^sub>1 < n" by simp
      from n_def m1_m2_n' have m2_less_n: "m\<^sub>2 < n" by simp

      from Cons have "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_split by simp

      moreover from trans have "Prods G \<turnstile> [Nt (Single_sym q Z p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow>
                                    [Tm a, Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)]"
        using pda_to_cfg_derive_single derive_append[of "Prods G" "[Nt (Single_sym q Z p')]" "[Tm a, Nt (List_sym q' \<beta> p')]"
                                                            "[Nt (List_sym p' \<alpha> p)]"] by simp

      moreover have "Prods G \<turnstile> [Tm a, Nt (List_sym q' \<beta> p'), Nt (List_sym p' \<alpha> p)] \<Rightarrow>*
                                      Tm a # map Tm y @ [Nt (List_sym p' \<alpha> p)]"
        using derives_append[OF less(1)[OF m1_less_n stepm1]] by (simp add: derives_Tm_Cons)

      moreover from x'_def x_def have "Prods G \<turnstile> Tm a # map Tm y @ [Nt (List_sym p' \<alpha> p)] \<Rightarrow>* map Tm x"
        using derives_prepend[OF less(1)[OF m2_less_n stepm2], of "Tm a # map Tm y"] by simp

      ultimately show ?thesis by simp
    qed
  qed
qed

(* TODO: CFG? *)
lemma derivel_append_decomp:
  "P \<turnstile> u@v \<Rightarrow>l w \<longleftrightarrow>
  (\<exists>u'. w = u'@v \<and> P \<turnstile> u \<Rightarrow>l u') \<or> (\<exists>u' v'. w = u@v' \<and> u = map Tm u' \<and> P \<turnstile> v \<Rightarrow>l v')"
(is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then obtain A r u1 u2
    where Ar: "(A,r) \<in> P"
      and uv: "u@v = map Tm u1 @ Nt A # u2"
      and w: "w = map Tm u1 @ r @ u2"
    by (auto simp: derivel_iff)
  from uv have case_dist: "(\<exists>s. u2 = s @ v \<and> u = map Tm u1 @ Nt A # s) \<or>
  (\<exists>s. map Tm u1 = u @ s  \<and> v = s @ Nt A # u2)" (is "?asm \<or> _")
    by (auto simp: append_eq_append_conv2 append_eq_Cons_conv)
  show "?r" proof (cases)
    assume ?asm
    with Ar w show ?thesis by (fastforce simp: derivel_iff)
  next
    assume "\<not>?asm"
    with case_dist obtain s where map_u1_def: "map Tm u1 = u @ s" and v_def: "v = s @ Nt A # u2" by blast
    from map_u1_def obtain u' s' where u_def: "u = map Tm u'" and s_def: "s = map Tm s'"
      using append_eq_map_conv[of u s Tm u1] by auto

    from w map_u1_def s_def have "w = u @ (map Tm s' @ r @ u2)" by simp

    moreover from Ar v_def s_def have "P \<turnstile> v \<Rightarrow>l map Tm s' @ r @ u2"
      using derivel_iff[of P] by blast

    ultimately show ?thesis
      using u_def by blast
  qed
next
  show "?r \<Longrightarrow> ?l"
    by (auto simp add: derivel_append derivel_map_Tm_append)
qed

(* TODO: CFG? *)
lemma split_derivel':
  assumes "P \<turnstile> x#v \<Rightarrow>l(n) u"
  shows "(\<exists>u'. u = u' @ v \<and> P \<turnstile> [x] \<Rightarrow>l(n) u') \<or> (\<exists>w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> u = map Tm w\<^sub>1 @ u\<^sub>2 
                                                    \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2)"
using assms proof (induction n arbitrary: u)
  case (Suc n)
  from Suc(2) obtain w where x_v_deriveln_w: "P \<turnstile> x # v \<Rightarrow>l(n) w" and w_derivel_u: "P \<turnstile> w \<Rightarrow>l u" by auto
  from Suc(1)[OF x_v_deriveln_w] have IH: "(\<exists>u'. w = u' @ v \<and> P \<turnstile> [x] \<Rightarrow>l(n) u') \<or>
  (\<exists>w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> w = map Tm w\<^sub>1 @ u\<^sub>2 \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2)" (is "?asm \<or> _") .
  then show ?case proof (cases)
    assume ?asm
    then obtain u' where w_def: "w = u' @ v" and x_deriveln_u': "P \<turnstile> [x] \<Rightarrow>l(n) u'" by blast
    from w_def w_derivel_u have "P \<turnstile> u' @ v \<Rightarrow>l u" by simp
    hence case_dist: "(\<exists>u\<^sub>0. u = u\<^sub>0 @ v \<and> P \<turnstile> u' \<Rightarrow>l u\<^sub>0) \<or>
                  (\<exists>u\<^sub>1 u\<^sub>2. u = u' @ u\<^sub>2 \<and> u' = map Tm u\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l u\<^sub>2)" (is "?asm' \<or> _")
      using derivel_append_decomp[of P u' v u] by simp
    then show ?thesis proof (cases)
      assume ?asm'
      then obtain u\<^sub>0 where u_def: "u = u\<^sub>0 @ v" and u'_derivel_u0: "P \<turnstile> u' \<Rightarrow>l u\<^sub>0" by blast
      from x_deriveln_u' u'_derivel_u0 have "P \<turnstile> [x] \<Rightarrow>l(Suc n) u\<^sub>0" by auto
      with u_def show ?thesis by blast
    next
      assume "\<not>?asm'"
      with case_dist obtain u\<^sub>1 u\<^sub>2 where u_def: "u = u' @ u\<^sub>2" and u'_def: "u' = map Tm u\<^sub>1" and v_derivel_u2: "P \<turnstile> v \<Rightarrow>l u\<^sub>2" by blast
      from x_deriveln_u' u'_def have "P \<turnstile> [x] \<Rightarrow>l(n) map Tm u\<^sub>1" by simp
      with u_def u'_def v_derivel_u2 show ?thesis by fastforce
    qed
  next
    assume "\<not>?asm"
    with IH obtain w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" and w_def: "w = map Tm w\<^sub>1 @ u\<^sub>2" and 
                                      x_derivelm1_w1: "P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" and v_derivelm2_u2: "P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2" by blast
    from w_def w_derivel_u have "P \<turnstile> map Tm w\<^sub>1 @ u\<^sub>2 \<Rightarrow>l u" by simp
    then obtain u' where u_def: "u = map Tm w\<^sub>1 @ u'" and u2_derivel_u': "P \<turnstile> u\<^sub>2 \<Rightarrow>l u'"
      using derivel_map_Tm_append by blast

    from m1_m2_n have "m\<^sub>1 + Suc m\<^sub>2 = Suc n" by simp

    moreover from v_derivelm2_u2 u2_derivel_u' have "P \<turnstile> v \<Rightarrow>l(Suc m\<^sub>2) u'" by auto

    ultimately show ?thesis
      using u_def x_derivelm1_w1 by blast
  qed
qed simp

(* TODO: CFG? *)
lemma split_derivel:
  assumes "P \<turnstile> x#v \<Rightarrow>l(n) map Tm w"
  shows "\<exists>w\<^sub>1 w\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> w = w\<^sub>1 @ w\<^sub>2 \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) map Tm w\<^sub>2"
proof -
  have case_dist: "(\<exists>u'. map Tm w = u' @ v \<and> P \<turnstile> [x] \<Rightarrow>l(n) u') \<or> (\<exists>w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2. m\<^sub>1 + m\<^sub>2 = n \<and> map Tm w = map Tm w\<^sub>1 @ u\<^sub>2 
                                                    \<and> P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1 \<and> P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2)" (is "?asm \<or> _")
    using split_derivel'[OF assms] by simp
  thus ?thesis proof (cases)
    assume ?asm
    then obtain u' where map_w_def: "map Tm w = u' @ v" and x_derives_u': "P \<turnstile> [x] \<Rightarrow>l(n) u'" by blast
    from map_w_def obtain w\<^sub>1 w\<^sub>2 where "w = w\<^sub>1 @ w\<^sub>2" and map_w\<^sub>1_def: "map Tm w\<^sub>1 = u'" and "map Tm w\<^sub>2 = v"
      using map_eq_append_conv[of Tm w u' v] by blast

    moreover from x_derives_u' map_w\<^sub>1_def have "P \<turnstile> [x] \<Rightarrow>l(n) map Tm w\<^sub>1" by simp

    moreover have "P \<turnstile> map Tm w\<^sub>2 \<Rightarrow>l(0) map Tm w\<^sub>2" by simp

    ultimately show ?thesis by force
  next
    assume "\<not>?asm"
    with case_dist obtain w\<^sub>1 u\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n: "m\<^sub>1 + m\<^sub>2 = n" and map_w_def: "map Tm w = map Tm w\<^sub>1 @ u\<^sub>2" 
                                               and x_derivelm1_w1: "P \<turnstile> [x] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" and v_derivelm2_u2: "P \<turnstile> v \<Rightarrow>l(m\<^sub>2) u\<^sub>2" by blast
    from map_w_def obtain w\<^sub>1' u\<^sub>2' where "w = w\<^sub>1' @ u\<^sub>2'" and "map (Tm :: 'c \<Rightarrow> ('b, 'c) sym) w\<^sub>1 = map Tm w\<^sub>1'" and "u\<^sub>2 = map (Tm :: 'c \<Rightarrow> ('b, 'c) sym) u\<^sub>2'"
      using map_eq_append_conv[of "Tm :: 'c \<Rightarrow> ('b, 'c) sym" w "map Tm w\<^sub>1" u\<^sub>2] by blast
    with m1_m2_n x_derivelm1_w1 v_derivelm2_u2 show ?thesis by auto
  qed                    
qed

lemma pda_to_cfg_steps_if_derivel:
  assumes "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>l(n) map Tm x"
  shows "steps (q, x, \<gamma>) (p, [], [])"
using assms proof (induction n arbitrary: x p q \<gamma> rule: less_induct)
  case (less n)
  then show ?case proof (cases \<gamma>)
    case Nil
    have derives: "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>* map Tm x"
      using derivels_imp_derives[OF relpowp_imp_rtranclp[OF less(2)]] .
    have "p = q \<and> x = []"
    proof -
      from derives_start1[OF derives] obtain \<alpha> where d1: "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow> \<alpha>" and 
                                                        ds: "Prods G \<turnstile> \<alpha> \<Rightarrow>* map Tm x"
        using derive_singleton by blast
      from Nil d1 have *: "p = q" and \<alpha>_def: "\<alpha> = []"
        using pda_to_cfg_derive_empty by simp_all
      from \<alpha>_def ds have **: "x = []" by simp
      from * ** show ?thesis by simp
    qed
    with Nil show ?thesis
      by (simp add: steps_refl)
  next
    case (Cons Z \<alpha>)
    from less(2) have "n > 0"
      using gr0I by fastforce
    then obtain n' where n_def: "n = Suc n'"
      using not0_implies_Suc by blast
    with less(2) obtain \<gamma>' where l1: "Prods G \<turnstile> [Nt (List_sym q \<gamma> p)] \<Rightarrow>l \<gamma>'" and ln': "Prods G \<turnstile> \<gamma>' \<Rightarrow>l(n') map Tm x"
      using relpowp_Suc_E2[of n' "derivel (Prods G)" "[Nt (List_sym q \<gamma> p)]" "map Tm x"] by blast
    from Cons obtain q' where \<gamma>'_def: "\<gamma>' = [Nt (Single_sym q Z q'), Nt (List_sym q' \<alpha> p)]"
      using pda_to_cfg_derive_split derivel_imp_derive[OF l1] by blast
    with ln' have "n' > 0"
      using gr0I by fastforce
    then obtain n'' where n'_def: "n' = Suc n''"
      using not0_implies_Suc by blast
    with ln' \<gamma>'_def obtain \<gamma>'' where l2: "Prods G \<turnstile> [Nt (Single_sym q Z q'), Nt (List_sym q' \<alpha> p)] \<Rightarrow>l \<gamma>''" and
                                      ln'': "Prods G \<turnstile> \<gamma>'' \<Rightarrow>l(n'') map Tm x"
      using relpowp_Suc_E2[of n'' "derivel (Prods G)" "[Nt (Single_sym q Z q'), Nt (List_sym q' \<alpha> p)]" "map Tm x"] by blast
    from l2 obtain \<gamma>''\<^sub>2 where l2': "Prods G \<turnstile> [Nt (Single_sym q Z q')] \<Rightarrow>l \<gamma>''\<^sub>2" and \<gamma>''_split: "\<gamma>'' = \<gamma>''\<^sub>2 @ [Nt (List_sym q' \<alpha> p)]"
      using derivel_Nt_Cons by (metis append.right_neutral) 
    have "(\<exists>q'' \<alpha>'' a. (q'', \<alpha>'') \<in> trans_fun M q a Z \<and> \<gamma>''\<^sub>2 = [Tm a, Nt (List_sym q'' \<alpha>'' q')]) \<or> 
                    (\<exists>q'' \<alpha>''. (q'', \<alpha>'') \<in> eps_fun M q Z  \<and> \<gamma>''\<^sub>2 = [Nt (List_sym q'' \<alpha>'' q')])"
      using pda_to_cfg_derive_single derivel_imp_derive[OF l2'] by simp
    with \<gamma>''_split have rule: "(\<exists>q'' \<alpha>'' a. (q'', \<alpha>'') \<in> trans_fun M q a Z \<and> 
                                  \<gamma>'' = [Tm a, Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]) \<or> 
                            (\<exists>q'' \<alpha>''. (q'', \<alpha>'') \<in> eps_fun M q Z  \<and> 
                                  \<gamma>'' = [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)])" (is "?asm \<or> _") by simp
    show ?thesis proof (cases)
      assume ?asm
      then obtain q'' \<alpha>'' a where trans: "(q'', \<alpha>'') \<in> trans_fun M q a Z" and 
                                     \<gamma>''_def: "\<gamma>'' = [Tm a, Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]" by blast
      from \<gamma>''_def ln'' obtain x' where x_def: "x = a#x'" and 
                               split: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(n'') map Tm x'"
        using deriveln_Tm_Cons[of n'' "Prods G" a "[Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]" "map Tm x"] by auto
      obtain w\<^sub>1 w\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n''': "m\<^sub>1 + m\<^sub>2 = n''" and x'_def: "x' = w\<^sub>1 @ w\<^sub>2" 
                                    and m1_path: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q')] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" 
                                    and m2_path: "Prods G \<turnstile> [Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(m\<^sub>2) map Tm w\<^sub>2" 
        using split_derivel[OF split] by blast
      from m1_m2_n''' n_def n'_def have m1_lessn: "m\<^sub>1 < n" by simp
      from m1_m2_n''' n_def n'_def have m2_lessn: "m\<^sub>2 < n" by simp

      from trans x_def Cons have "step\<^sub>1 (q, x, \<gamma>) (q'', x', \<alpha>'' @ \<alpha>)"
        using step\<^sub>1_rule by simp

      moreover from x'_def have "steps (q'', x', \<alpha>'' @ \<alpha>) (q', w\<^sub>2, \<alpha>)"
        using steps_stack_app[OF less(1)[OF m1_lessn m1_path], of \<alpha>] 
              steps_word_app[of q'' w\<^sub>1 "\<alpha>'' @ \<alpha>" q' "[]" \<alpha> w\<^sub>2] by simp

      moreover have "steps (q', w\<^sub>2, \<alpha>) (p, [], [])"
        using less(1)[OF m2_lessn m2_path] .

      ultimately show ?thesis
        unfolding steps_def by (meson star.step star_trans)
    next
      assume "\<not>?asm"
      with rule obtain q'' \<alpha>'' where eps: "(q'', \<alpha>'') \<in> eps_fun M q Z" and  
                                  \<gamma>''_def: "\<gamma>'' = [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)]" by blast
      from \<gamma>''_def ln'' have split: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q'), Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(n'') map Tm x" by simp
      obtain w\<^sub>1 w\<^sub>2 m\<^sub>1 m\<^sub>2 where m1_m2_n''': "m\<^sub>1 + m\<^sub>2 = n''" and x_def: "x = w\<^sub>1 @ w\<^sub>2" 
                             and m1_path: "Prods G \<turnstile> [Nt (List_sym q'' \<alpha>'' q')] \<Rightarrow>l(m\<^sub>1) map Tm w\<^sub>1" 
                             and m2_path: "Prods G \<turnstile> [Nt (List_sym q' \<alpha> p)] \<Rightarrow>l(m\<^sub>2) map Tm w\<^sub>2"
        using split_derivel[OF split] by blast
      from m1_m2_n''' n_def n'_def have m1_lessn: "m\<^sub>1 < n" by simp
      from m1_m2_n''' n_def n'_def have m2_lessn: "m\<^sub>2 < n" by simp

      from eps Cons have "step\<^sub>1 (q, x, \<gamma>) (q'', x, \<alpha>'' @ \<alpha>)"
        using step\<^sub>1_rule by simp

      moreover from x_def have "steps (q'', x, \<alpha>'' @ \<alpha>) (q', w\<^sub>2, \<alpha>)"
        using steps_stack_app[OF less(1)[OF m1_lessn m1_path], of \<alpha>] 
              steps_word_app[of q'' w\<^sub>1 "\<alpha>'' @ \<alpha>" q' "[]" \<alpha> w\<^sub>2] by simp

      moreover have "steps (q', w\<^sub>2, \<alpha>) (p, [], [])"
        using less(1)[OF m2_lessn m2_path] .

      ultimately show ?thesis
        unfolding steps_def by (meson star.step star_trans)
    qed
  qed
qed

lemma pda_to_cfg: "LangS G = stack_accept"
proof
  show "LangS G \<subseteq> stack_accept"
  proof
    fix x
    assume "x \<in> LangS G"
    hence derives: "Prods G \<turnstile> [Nt Start_sym] \<Rightarrow>* map Tm x"
      unfolding Lang_def by (simp add: G_def)
    then obtain \<gamma> where fs: "Prods G \<turnstile> [Nt Start_sym] \<Rightarrow> \<gamma>" and ls: "Prods G \<turnstile> \<gamma> \<Rightarrow>* map Tm x"
      using converse_rtranclpE[OF derives] by blast
    from fs obtain q where "\<gamma> = [Nt (List_sym (init_state M) [init_symbol M] q)]"
      using pda_to_cfg_derive_start[of \<gamma>] by blast
    with ls obtain n where "Prods G \<turnstile> [Nt (List_sym (init_state M) [init_symbol M] q)] \<Rightarrow>l(n) map Tm x"
      using derivels_iff_derives[of "Prods G" \<gamma> x] rtranclp_power[of "derivel (Prods G)" \<gamma> "map Tm x"] by blast
    hence "steps (init_state M, x, [init_symbol M]) (q, [], [])"
      using pda_to_cfg_steps_if_derivel by simp
    thus "x \<in> stack_accept"
      unfolding stack_accept_def by auto
  qed
next
  show "stack_accept \<subseteq> LangS G"
  proof
    fix x
    assume "x \<in> stack_accept"
    then obtain q where "steps (init_state M, x, [init_symbol M]) (q, [], [])"
      unfolding stack_accept_def by blast
    then obtain n where "stepn n (init_state M, x, [init_symbol M]) (q, [], [])"
      using stepn_steps by blast
    hence "Prods G \<turnstile> [Nt (List_sym (init_state M) [init_symbol M] q)] \<Rightarrow>* map Tm x"
      using pda_to_cfg_derives_if_stepn by simp
    moreover have "Prods G \<turnstile> [Nt Start_sym] \<Rightarrow> [Nt (List_sym (init_state M) [init_symbol M] q)]"
      using pda_to_cfg_derive_start by simp
    ultimately have "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* map Tm x"
      by (simp add: G_def)
    thus "x \<in> LangS G"
      unfolding Lang_def by simp
  qed
qed

end
end