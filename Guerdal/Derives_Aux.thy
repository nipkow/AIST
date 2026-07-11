theory Derives_Aux 
  imports 
    Main
     Context_Free_Grammar.Parse_Tree
    "List_Power.List_Power"
begin

section "Lemmas about derivations"

text "In this section, we prove some facts purely about the derivation relation"

subsection "1) Decomposing Derivations"

text "Given a concatenation of two lists, deriving a symbol \<open>Y\<close> in any position, 
      one of the two lists should be deriving \<open>Y\<close>"
lemma derive_decomp:
  assumes "P \<turnstile> \<alpha> @ \<beta> \<Rightarrow>* \<gamma> @ [Y] @ \<delta>"
  shows "\<exists>\<kappa> \<mu>. P \<turnstile> \<alpha> \<Rightarrow>* \<kappa> @ [Y] @ \<mu> \<or>  P \<turnstile> \<beta> \<Rightarrow>* \<kappa> @ [Y] @ \<mu>"
  using derives_appendD[of P \<alpha> \<beta> "\<gamma> @ [Y] @ \<delta>"]
        Un_iff append_Cons append_Nil assms in_set_conv_decomp_first
        set_append
  by metis

text "Given a concatenation of three lists, deriving a symbol \<open>Y\<close> in any position, 
      one of the three lists should be deriving \<open>Y\<close>"
lemma derive_decomp2:
  assumes "P \<turnstile> \<alpha> @ x @ \<beta> \<Rightarrow>* \<gamma> @ [Y] @ \<delta>"
  shows "\<exists>\<kappa> \<mu>. P \<turnstile> \<alpha> \<Rightarrow>* \<kappa> @ [Y] @ \<mu> 
             \<or> P \<turnstile> \<beta> \<Rightarrow>* \<kappa> @ [Y] @ \<mu> 
             \<or> P \<turnstile> x \<Rightarrow>* \<kappa> @ [Y] @ \<mu>"
  using derive_decomp[of P] assms 
  by meson

text "Usefulness definition, using list concatenation instead of sets"
lemma useful_def_list:
  assumes "useful P S X"
  obtains w z where "P \<turnstile> [Nt S] \<Rightarrow>* w @ [Nt X] @ z"
  using assms unfolding useful_def
  using split_list by fastforce

subsection "2) Derivations leading to terminals" 

text "We show that if a string \<open>\<beta>\<close> can be derived from a symbol \<open>A\<close> that comes up in the lhs of 
      at least one production, every symbol \<open>b\<close> in \<open>\<beta>\<close> is a terminal or a non-terminal listed 
      in \<open>Nts\<close> (i.e., is a reachable non-terminal)."
lemma derives_tms_nts:
  fixes G :: "('n, 't) Cfg"
  assumes "Prods G \<turnstile> [Nt X] \<Rightarrow>* \<beta>" "\<exists>(S, x)\<in>Prods G. S = X"
  shows "\<And>b. b \<in> set \<beta> \<Longrightarrow> (\<exists>t. b = Tm t) \<or> (\<exists>nt. b = Nt nt \<and> nt \<in> Nts (Prods G))"
using assms(1)
proof (induct rule: derives_induct)
  case base
  fix b 
  assume "b \<in> set [Nt X]"
  hence "b = Nt X" by simp
  with assms(2) show "(\<exists>t. b = Tm t) \<or> (\<exists>nt. b = Nt nt \<and> nt \<in> Nts (Prods G))"
    unfolding Nts_def by force
next
  case (step \<alpha> A \<beta> \<gamma>)
  fix b 
  assume "b \<in> set (\<alpha> @ \<gamma> @ \<beta>)"

  then consider (in_alpha) "b \<in> set \<alpha>" | (in_gamma) "b \<in> set \<gamma>" | (in_beta) "b \<in> set \<beta>" by auto
  
  then show "(\<exists>t. b = Tm t) \<or> (\<exists>nt. b = Nt nt \<and> nt \<in> Nts (Prods G))"
  proof cases
    case in_alpha
    then show ?thesis using step.hyps by auto
  next
    case in_beta
    then show ?thesis using step.hyps by auto
  next
    case in_gamma
    show ?thesis
    proof (cases b)
      case (Tm t)
      then show ?thesis by simp
    next
      case (Nt nt)
      have "nt \<in> Nts (Prods G)" 
        using step.hyps(3) \<open>b \<in> set \<gamma>\<close> Nt unfolding Nts_def Nts_syms_def by auto
      with Nt show ?thesis by blast
    qed
  qed
qed

text "Any symbol in a reachable string \<open>\<beta>\<close> can derive a terminal string, 
      if every reachable symbol is useful."
lemma derives_useful:
  fixes G :: "('n, 't) Cfg"
  assumes 
      "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<beta>"
      "\<exists>(S, x)\<in>Prods G. S = Start G" 
      "(\<forall>X. X \<in> Nts (Prods G) \<longrightarrow> useful (Prods G) (Start G) X)"
  shows "\<And>b. b \<in> set \<beta> \<Longrightarrow> \<exists>ww. Prods G \<turnstile> [b] \<Rightarrow>* map Tm ww"
proof -
  fix b 
  assume "b \<in> set \<beta>" 
  from this assms have "(\<exists>t. b = Tm t) \<or> (\<exists>nt. b = Nt nt \<and> useful (Prods G) (Start G) nt)" 
    using derives_tms_nts by metis

  then consider 
    (b_tm) "(\<exists>t. b = Tm t)" | (b_nt) "(\<exists>nt. b = Nt nt \<and> useful (Prods G) (Start G) nt)" 
    by fast
  then show "\<exists>ww. Prods G \<turnstile> [b] \<Rightarrow>* map Tm ww"
  proof cases
    case b_tm
    then show ?thesis using map_is_Nil_conv rtranclp.rtrancl_refl list.simps(9) by metis
   next
    case b_nt
    then obtain nt where nt_obtain: "b = Nt nt" "useful (Prods G) (Start G) nt" by blast
    then show ?thesis by (simp add: productive_if_useful)
  qed
qed

text "If every symbol in a string can derive a terminal string, the string can also derive a 
      terminal string"
lemma derives_list:
  fixes \<beta>  :: "('n, 't) syms" and
        P :: "('n, 't) Prods" 
  assumes 
      "\<And>b. b \<in> set \<beta> \<Longrightarrow> \<exists>ww. P \<turnstile> [b] \<Rightarrow>* map Tm ww"
    shows "\<exists>ww. P \<turnstile> \<beta> \<Rightarrow>* map Tm ww"
using assms
proof (induct \<beta>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<beta>)
  from Cons.prems obtain w_b where b_obtain: "P \<turnstile> [a] \<Rightarrow>* map Tm w_b" by fastforce
  from Cons.prems Cons.hyps obtain w_\<beta> where \<beta>_obtain: "P \<turnstile> \<beta> \<Rightarrow>* map Tm w_\<beta>" by force
 
  have "P \<turnstile> ([a] @ \<beta>) \<Rightarrow>* (map Tm w_b @ map Tm w_\<beta>)"
    using b_obtain \<beta>_obtain derives_append_append
    by blast
  then have "P \<turnstile> (a # \<beta>) \<Rightarrow>* (map Tm w_b @ map Tm w_\<beta>)" by auto
  hence "P \<turnstile> (a # \<beta>) \<Rightarrow>* map Tm (w_b @ w_\<beta>)" by simp
  thus ?case by blast
qed

text "Pulling together the two facts: if every reachable symbol is useful, 
      any reachable symbol list derives a word."
corollary derives_useful_list:
  fixes G :: "('n, 't) Cfg"
  assumes 
      "\<exists>(S, x)\<in>Prods G. S = Start G" 
      "(\<forall>X. X \<in> Nts (Prods G) \<longrightarrow> useful (Prods G) (Start G) X)"
       "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<beta>"
    shows "\<exists>ww. (Prods G) \<turnstile> \<beta> \<Rightarrow>* map Tm ww"
  using derives_list[OF derives_useful[OF assms(3,1,2)], of \<beta>] by auto

text "Any symbol in a reachable string \<open>\<beta> @ \<gamma>\<close> can derive a terminal string, 
      if every reachable symbol is useful."
lemma derives_useful_partial:
    fixes G :: "('n, 't) Cfg"
  assumes 
      "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<beta> @ \<gamma>"
      "\<exists>(S, x)\<in>Prods G. S = Start G" 
      "(\<forall>X. X \<in> Nts (Prods G) \<longrightarrow> useful (Prods G) (Start G) X)"
  shows "\<And>b c. b \<in> set \<beta> \<Longrightarrow> c \<in> set \<gamma> \<Longrightarrow> \<exists>ww zz. Prods G \<turnstile> [b] \<Rightarrow>* map Tm ww \<and> Prods G \<turnstile> [c] \<Rightarrow>* map Tm zz"
  using derives_useful[OF assms]
  by auto

text "Pulling together the two facts: if every reachable symbol is useful, 
      for any reachable concatenated symbol list concatenation, each one derives a word."
lemma derives_useful_list_partial:
  fixes \<beta>  :: "('n, 't) syms" and
        P :: "('n, 't) Prods" 
  assumes 
      "\<exists>(S, x)\<in>Prods G. S = Start G" 
      "(\<forall>X. X \<in> Nts (Prods G) \<longrightarrow> useful (Prods G) (Start G) X)"
      "Prods G \<turnstile> [Nt (Start G)] \<Rightarrow>* \<beta> @ \<gamma>"
    shows "\<exists>ww zz. (Prods G) \<turnstile> \<beta> \<Rightarrow>* map Tm ww \<and> (Prods G) \<turnstile> \<gamma> \<Rightarrow>* map Tm zz"
  using derives_useful_list derives_useful_partial[OF assms(3,1,2)] 
proof - 
  have "\<And>b. b \<in> set \<beta> \<Longrightarrow> \<exists>ww zz. Prods G \<turnstile> [b] \<Rightarrow>* map Tm ww"
    using derives_useful[OF assms(3,1,2)] by auto
  moreover have "\<And>c. c \<in> set \<gamma> \<Longrightarrow> \<exists>ww zz. Prods G \<turnstile> [c] \<Rightarrow>* map Tm ww"
    using derives_useful[OF assms(3,1,2)] by auto
  ultimately show ?thesis using derives_useful_list[OF assms] derives_append_map_Tm by meson
qed



subsection "3) Pumping using a derivation"

text "In this section, we show that if a derivation contains a non-terminal \<open>X\<close> that has a self-loop
     \<open>X \<Rightarrow>* xXy\<close> pumping non-empty \<open>x\<close>, \<open>y\<close> will allow any \<open>s({x}^n)t({y}^n)u \<in> L(G)\<close> to be derived."

text "If \<open>x\<close> derives \<open>y\<close>, the power of \<open>x\<close> derives the same power of \<open>y\<close>."
lemma derives_power:
  fixes P x y
  assumes "P \<turnstile> x \<Rightarrow>* y"
  shows "\<And>(k:: nat). P \<turnstile> x ^^ k \<Rightarrow>* y ^^ k" 
proof -
  fix k
  show "P \<turnstile> x ^^ k \<Rightarrow>* y ^^ k"
    by (induct k; auto simp add: derives_append_append[OF assms]) 
qed

text "We can repeat any such self-loop any \<open>k\<close> times."
lemma derives_forever:
  fixes P X x y
  assumes "P \<turnstile> [Nt X] \<Rightarrow>* x @ [Nt X] @ y"
  shows "\<And>k. P \<turnstile> [Nt X] \<Rightarrow>* x ^^ k @ [Nt X] @ y ^^ k"
proof -
  fix k
  show "P \<turnstile> [Nt X] \<Rightarrow>* x ^^ k @ [Nt X] @ y ^^ k"
  proof (induct k)
   case 0
   then show ?case by auto
  next
   case (Suc n)
   assume pr: "P \<turnstile> [Nt X] \<Rightarrow>* x ^^ n @ [Nt X] @ y ^^ n"
   have "P \<turnstile> x ^^ n @ [Nt X] @ y ^^ n \<Rightarrow>* x ^^ n @ x @ [Nt X] @ y @ y ^^ n"
     using derives_append[OF derives_prepend[OF assms, of "x ^^ n"], of "y ^^ n"] by simp
   then have "P \<turnstile> [Nt X] \<Rightarrow>* x ^^ n @ x @ [Nt X] @ y @ y ^^ n" 
     using pr by auto
   thus ?case using append.assoc pow_list.simps(2) pow_list_Suc2 by metis
 qed
qed

text "We show \<open>s({x}^n)t({y}^n)u \<in> L(G)\<close> for any \<open>n\<close>."
lemma derives_more:
  fixes G' :: "('n, 't) Cfg" and X :: "'n" and x y :: "'t list" 
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
          not_empty: "x @ y \<noteq> []" and
          der_assm: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y"
  shows "\<exists>ww zz xx. \<forall>n. (ww @ x ^^ n @ xx @ y ^^ n @ zz) \<in> LangS G'"
proof -
  text "Showing that \<open>X\<close> is useful"
  from not_empty have not_equal: "[Nt X] \<noteq> map Tm x @ [Nt X] @ map Tm y" 
    by (simp add: Cons_eq_append_conv)
  hence "\<exists>\<alpha>. (Prods G') \<turnstile> [Nt X] \<Rightarrow> \<alpha>" 
      using der_assm converse_rtranclpE by fastforce
  hence "\<exists>\<alpha>. (X, \<alpha>) \<in> (Prods G')" by (simp add: derive_singleton) 
  hence "X \<in> Nts (Prods G')" using Nts_def by fast
  hence useful: "useful (Prods G') (Start G') X" using usefulG' by blast      
  text "Here we stumble on the fact that w and z can be non-terminals: we need to prove that they all can derive a terminal string. 
         This is needed since we need to argue on the final terminal string, whether it is in the language."
  then obtain w z where w_z_obtain: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* w @ [Nt X] @ z" using useful_def_list by meson

  text "Each symbol in \<open>wXz\<close> is either a terminal, or a useful non-terminal: then we can derive terminal strings from them \<open>b \<Rightarrow>* w\<close>."
  have ders: "\<exists>ww. Prods G' \<turnstile> (w @ [Nt X] @ z) \<Rightarrow>* map Tm ww"
    using derives_useful_list[OF start_prod usefulG' w_z_obtain] by simp

  text "From the fact above, we can then say that \<open>wXz\<close> derives a terminal string too."
  then have "\<exists>ww. Prods G' \<turnstile> (w @ [Nt X] @ z) \<Rightarrow>* map Tm ww" 
    using derives_list by blast 

  text "The obtained terminal string can be split into \<open>ww\<close>, \<open>zz\<close> and \<open>xx\<close>:"
  then obtain ww zz xx 
    where ww_zz_xx: 
      "(Prods G') \<turnstile> w \<Rightarrow>* map Tm ww" 
      "(Prods G') \<turnstile> z \<Rightarrow>* map Tm zz"
      "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm xx"
    using derives_append_map_Tm by meson

  from w_z_obtain this have new_start: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ww @ [Nt X] @ map Tm zz"
     using derives_append derives_prepend rtranclp_trans
     by meson
      
  from der_assm this have x_deriv: "(Prods G') \<turnstile> map Tm ww @ [Nt X] @ map Tm zz \<Rightarrow>*  map Tm ww @ map Tm x @ [Nt X] @ map Tm y  @ map Tm zz"
    using derives_append[OF derives_prepend[OF der_assm, of "map Tm ww"], of "map Tm zz"] by simp

  from new_start this have starting:
     "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ww @ map Tm x @ [Nt X] @ map Tm y  @ map Tm zz"
    using rtranclp_trans[OF new_start x_deriv] by simp

  then have "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ww @ map Tm x @ map Tm xx @ map Tm y  @ map Tm zz" 
     using ww_zz_xx(3) derives_append derives_prepend rtranclp_trans by meson
  hence "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm (ww @ x @ xx @ y @ zz)" by auto
  hence "ww @ x @ xx @ y @ zz \<in> LangS G'" unfolding Lang_def by auto


  text "Showing: \<open>S \<Rightarrow>* wXz \<Rightarrow>* wxXyz \<Rightarrow>* wxxXyyz\<close>"
  from der_assm have alln: "\<And>n. (Prods G') \<turnstile> [Nt X] \<Rightarrow>* (map Tm x) ^^ n @ [Nt X] @ (map Tm y) ^^ n"
    using derives_forever[OF der_assm] by auto

  then have x_deriv: "\<And>n. (Prods G') \<turnstile> map Tm ww @ [Nt X] @ map Tm zz \<Rightarrow>*  map Tm ww @ (map Tm x) ^^ n @ [Nt X] @ (map Tm y) ^^ n  @ map Tm zz"
    using derives_append derives_prepend append.assoc by metis

  from new_start this have starting:
     "\<And>n. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ww @ (map Tm x) ^^ n @ [Nt X] @ (map Tm y) ^^ n  @ map Tm zz"
    using rtranclp_trans[OF new_start _] by presburger


  text "Showing that the \<open>S \<Rightarrow>* wxx|xx|yyz\<close> for some terminals \<open>w,xx,z\<close> where \<open>wxx|xx|yyz\<in>L\<close>"
  then have "\<And>n. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm ww @ (map Tm x) ^^ n @ map Tm xx @ (map Tm y) ^^ n @ map Tm zz"
    using ww_zz_xx(3) derives_append derives_prepend rtranclp_trans
    by meson
  then have "\<And>n. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm (ww @ x ^^ n @ xx @ y ^^ n @ zz)"
    by fastforce

  thus "\<exists>ww zz xx. \<forall>n. ww @ x ^^ n @ xx @ y ^^ n @ zz \<in> LangS G'" unfolding Lang_def by auto
qed

lemma tranclpD2: "R\<^sup>+\<^sup>+ x y \<Longrightarrow> \<exists>z. R\<^sup>*\<^sup>* x z \<and> R z y"
proof (induction rule: converse_tranclp_induct)
  case (step u v)
  then show ?case
    by (blast intro: rtranclp_trans)
qed auto


text "For some legacy proofs, we have the case with \<open>n=1,2\<close>."
lemma derives_two:
  fixes G' :: "('n, 't) Cfg" and X :: "'n" and x y :: "'t list" 
  assumes usefulG': "(\<forall>X. X \<in> Nts (Prods G') \<longrightarrow> useful (Prods G') (Start G') X)" and
          start_prod: "\<exists>(S,x)\<in>Prods G'. S = Start G'" and
          not_empty: "x @ y \<noteq> []" and
          der_assm: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm x @ [Nt X] @ map Tm y"
  shows "\<exists>ww zz xx. (ww @ x @ xx @ y @ zz) \<in> LangS G' 
         \<and> (ww @ x @ x @ xx @ y @ y @ zz) \<in> LangS G'"
  using derives_more[OF assms] 
proof - 
  let ?L = "LangS G'"
  assume "\<exists>ww zz xx. \<forall>n. (ww @ x ^^ n @ xx @ y ^^ n @ zz) \<in> ?L" 
  then obtain ww xx zz where forall:"\<forall>n. (ww @ x ^^ n @ xx @ y ^^ n @ zz) \<in> ?L" by blast
  then have "ww @ x ^^ 1 @ xx @ y ^^ 1 @ zz \<in> ?L" by presburger
  then have one: "ww @ x @ xx @ y @ zz \<in> ?L" by simp

  from forall have "ww @ x ^^ 2 @ xx @ y ^^ 2 @ zz \<in> ?L" by presburger
  then have two: "ww @ x @ x @ xx @ y @ y @ zz \<in> ?L" by simp
  from one two show "\<exists>ww zz xx. ww @ x @ xx @ y @ zz \<in> ?L \<and> (ww @ x @ x @ xx @ y @ y @ zz) \<in> ?L" by meson
qed

text "Another case we want: if a derivation contains the variable \<open>X\<close>, we can pump it inside the original word
      We note that both of these cases can be more generalized: may be a future work to do that. However, the two cases
      inherently show different things, in this case, we already are given that \<open>X\<close> is inside a derivation, in
      previous cases, it was just a reachable variable (and derived a word because it was useful). The both words
      were constructed in the same proof, here, one word is given, we pump the other."
lemma derives_pumps:
  fixes G' :: "('n, 't) Cfg" and X :: "'n" and w x y:: "'t list"  
  assumes start_prod: "\<exists>(S,x)\<in> Prods G'. S = Start G'" and
          prod: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* \<alpha> @ [Nt X] @ \<beta>" "(Prods G') \<turnstile> \<alpha> @ [Nt X] @ \<beta> \<Rightarrow>* map Tm w"  and
          pump: "Prods G' \<turnstile> [Nt X] \<Rightarrow>* map Tm x ^^ l @ [Nt X] @ map Tm y ^^ l" "l > 0 "
  shows "\<exists>aa xx bb. w = aa @ xx @ bb \<and> (\<forall>k. (aa @ x ^^ (l * k) @ xx @ y ^^ (l * k) @ bb) \<in> LangS G')"
proof - 
  let ?L = "LangS G'"
  from prod(2) obtain aa xx bb where
     aa: "(Prods G') \<turnstile> \<alpha> \<Rightarrow>* map Tm aa" and
     xx: "(Prods G') \<turnstile> [Nt X] \<Rightarrow>* map Tm xx" and
     bb: "(Prods G') \<turnstile> \<beta> \<Rightarrow>* map Tm bb" and
     w_axb: "w = aa @ xx @ bb"
    using derives_append_map_Tm[of "(Prods G')", THEN iffD1] by blast

  from derives_forever[OF pump(1)] have "\<And>k.  Prods G' \<turnstile> [Nt X] \<Rightarrow>* ((map Tm x ^^ l) ^^ k) @ [Nt X] @ ((map Tm y ^^ l) ^^ k)" by simp
  then have pumpk: "\<And>k.  Prods G' \<turnstile> [Nt X] \<Rightarrow>* (map Tm x ^^ (l * k)) @ [Nt X] @ (map Tm y ^^ (l * k))" by (simp add: pow_list_mult)

  have aabb: "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm aa @ [Nt X] @ map Tm bb"
    using rtranclp_trans[OF prod(1) derives_append_append[OF aa derives_prepend[OF bb, of "[Nt X]"]]] by simp
  have xlyl: "\<And>k. (Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm aa @ (map Tm x ^^ (l * k)) @ [Nt X] @ (map Tm y ^^ (l * k)) @ map Tm bb"
    using rtranclp_trans[OF aabb derives_append[OF pumpk, THEN derives_prepend, of "map Tm aa" "map Tm bb"]] by simp
  
  have "(Prods G') \<turnstile> [Nt (Start G')] \<Rightarrow>* map Tm (aa @  x ^^ (l * k) @ xx @ y ^^ (l * k) @ bb)" for k
    using rtranclp_trans[OF xlyl] derives_append[OF xx, THEN derives_prepend, of "map Tm aa @ map Tm x ^^ (l * k)" "map Tm y ^^ (l * k) @ map Tm bb"] by simp
  hence "\<And>k. (aa @  x ^^ (l * k) @ xx @ y ^^ (l * k) @ bb) \<in> LangS G'" unfolding Lang_def by blast
  thus ?thesis using w_axb by auto
qed





end