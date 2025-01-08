theory CFL_intersection
  imports  "../CFL" "../Stimpfle/CNF" HOL.Fun
begin

abbreviation repl :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<^sup>*/_")
  where "xs\<^sup>*n \<equiv> concat (replicate n xs)"

theorem pumping_lemma:
  assumes "cnf G"
  shows "\<exists>n. \<forall>word \<in> L G. length word \<ge> n \<longrightarrow>
     (\<exists>u v w x y. word = u@v@w@x@y \<and> length (v@w@x) \<le> n \<and> length (v@x) \<ge> 1 \<and> (\<forall>i. u@(v\<^sup>*i)@w@(x\<^sup>*i)@y \<in> L G))"
  sorry

(*From ../Philipp/anbncn.thy*)
abbreviation repl_one :: "'a  \<Rightarrow> nat \<Rightarrow> 'a list" ("_^*_")
  where "xs^*n \<equiv> replicate n xs"

section "CFL intersection is not closed"

section "auxiliaries"
abbreviation L :: "('n,'t) Cfg \<Rightarrow> 't list set" where
  "L G \<equiv> Lang (Prods G) (Start G)"

abbreviation Lang_concat :: "'t list set \<Rightarrow> 't list set \<Rightarrow> 't list set" where
  "Lang_concat L1 L2 \<equiv> {word. \<exists>w1 \<in> L1. \<exists>w2 \<in> L2. word = w1 @ w2}"

lemma repl_repl_one: "(a^*n) = ([a]\<^sup>*n)"
  apply(induction n)
  by(auto)
  
lemma repl_append: "a @ (a\<^sup>*n) = (a\<^sup>*(Suc n))"
  by simp

lemma repl_append2: "(a\<^sup>*n) @ a = (a\<^sup>*(Suc n))"
  by (metis append.right_neutral concat.simps concat_append replicate_Suc replicate_append_same)

lemma repl_nil: "([]\<^sup>*n) = []"
  by simp

lemma count_repl: "count_list (a^*x) a = x"
  apply(induction x)
  by auto

lemma derive_n_same:
  assumes "(A, u' @ [Nt A] @ v') \<in> P"
  shows "P \<turnstile> u @ [Nt A] @ v \<Rightarrow>(n) u @ (u'\<^sup>*n) @ [Nt A] @ (v'\<^sup>*n) @ v"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "P \<turnstile> u @ (u'\<^sup>*n) @ [Nt A] @ (v'\<^sup>*n) @ v \<Rightarrow> u @ (u'\<^sup>*n) @ u' @ [Nt A] @ v' @ (v'\<^sup>*n) @ v" 
    using assms derive.intros[of _ _ _ "u @ (u'\<^sup>*n)" "(v'\<^sup>*n) @ v"] by fastforce 
  then have "P \<turnstile> u @ (u'\<^sup>*n) @ [Nt A] @ (v'\<^sup>*n) @ v \<Rightarrow> u @ (u'\<^sup>*(Suc n)) @ [Nt A] @ (v'\<^sup>*(Suc n)) @ v" 
    using repl_append repl_append2 by (metis append.assoc) 
  then show ?case using Suc by auto
qed

fun map_Nt :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 't) sym \<Rightarrow> ('b, 't) sym" where
  "map_Nt f (Nt A) = Nt (f A)"
| "map_Nt _ (Tm a) = Tm a"

lemma map_Nt_comp: "((map_Nt g) o (map_Nt f)) = (map_Nt (g o f))"
proof
  fix x
  show "(map_Nt g \<circ> map_Nt f) (x::('a,'b)sym) = map_Nt (g \<circ> f) x"
    by (smt (verit, del_insts) comp_apply map_Nt.elims map_Nt.simps)
qed

lemma map_Nt_ident: "map_Nt (\<lambda>x. x) = (\<lambda>xs. xs)"
proof
  fix xs
  show "map_Nt (\<lambda>x. x) (xs::('a,'b)sym) = xs" by (metis map_Nt.elims) 
qed

fun map_Prods_Nt :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'t) Prods \<Rightarrow> ('b,'t) Prods" where
  "map_Prods_Nt f P = {r. \<exists>(A, \<alpha>) \<in> P. r = (f A, map (map_Nt f) \<alpha>)}"

lemma map_Prods_Nt_comp: "((map_Prods_Nt g) o (map_Prods_Nt f)) = (map_Prods_Nt (g o f))"
proof
  fix P
  have s1: "{r. \<exists>(A, \<alpha>) \<in> {r. \<exists>(A, \<alpha>) \<in> (P::('a,'b) Prods). r = (f A, map (map_Nt f) \<alpha>)}. r = (g A, map (map_Nt g) \<alpha>)} = {r. \<exists>(A, \<alpha>) \<in> P. r = (g (f A), map (map_Nt g) (map (map_Nt f) \<alpha>))}" by blast
  then have s2: "... = {r. \<exists>(A, \<alpha>) \<in> P. r = ((g o f) A, map (map_Nt g \<circ> map_Nt f) \<alpha>)}" using map_map[of "map_Nt g" "map_Nt f"] by auto  
  then have s3: "... = {r. \<exists>(A, \<alpha>) \<in> P. r = ((g o f) A, map (map_Nt (g o f)) \<alpha>)}" using map_Nt_comp[of g f] by metis
  from s1 s2 s3 show "(map_Prods_Nt g \<circ> map_Prods_Nt f) P= map_Prods_Nt (g \<circ> f) P" by simp
qed

lemma map_Prods_Nt_ident: "map_Prods_Nt (\<lambda>x. x) = (\<lambda>xs. xs)"
proof
  fix P
  show "map_Prods_Nt (\<lambda>x. x) (P::('a,'b) Prods) = P" by (simp add: map_Nt_ident) 
qed

lemma map_derive_equiv:
  assumes "inj f"
  shows "P \<turnstile> u \<Rightarrow> v \<longleftrightarrow> (map_Prods_Nt f P) \<turnstile> map (map_Nt f) u \<Rightarrow> map (map_Nt f) v"
proof
  assume "P \<turnstile> u \<Rightarrow> v"
  then obtain A \<alpha> u' v' where obt: "(A,\<alpha>) \<in> P \<and> u = u' @ Nt A # v' \<and> v = u' @ \<alpha> @ v'" using derive_iff[of P] by blast
  then show "map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow> map (map_Nt f) v" using derive_iff[of "map_Prods_Nt f P"] by auto
next
  let ?Pm = "map_Prods_Nt f P"
  let ?um = "(map (map_Nt f) u)"
  let ?vm = "(map (map_Nt f) v)"
  let ?g = "the_inv f"
  assume "?Pm \<turnstile> ?um \<Rightarrow> ?vm"
  then obtain A \<alpha> u' v' where obt: "(A,\<alpha>) \<in> ?Pm \<and> ?um = u' @ Nt A # v' \<and> ?vm = u' @ \<alpha> @ v'" using derive_iff[of ?Pm] by blast
  then have der: "map_Prods_Nt ?g ?Pm \<turnstile> map (map_Nt ?g) ?um \<Rightarrow> map (map_Nt ?g) ?vm" 
    using derive_iff[of "map_Prods_Nt ?g ?Pm" "map (map_Nt ?g) ?um" "map (map_Nt ?g) ?vm"] by fastforce
  have gf_ident: "(?g o f) = (\<lambda>x. x)" using assms the_inv_f_f by fastforce
  then have "((map_Nt ?g) o (map_Nt f)) = (\<lambda>x. x)" using map_Nt_comp map_Nt_ident by metis
  have "\<forall>y. map (map_Nt ?g) (map (map_Nt f) y) = y" using map_map[of "map_Nt (the_inv f)" "map_Nt f" u] by (simp add: \<open>map_Nt ?g \<circ> map_Nt f = (\<lambda>x. x)\<close>)
  then have uv_unmap: "map (map_Nt ?g) ?um = u \<and> map (map_Nt ?g) ?vm = v" by blast
  have "map_Prods_Nt ?g (map_Prods_Nt f P) = (map_Prods_Nt ?g o map_Prods_Nt f) P" by simp
  then have "map_Prods_Nt ?g (map_Prods_Nt f P) = map_Prods_Nt (?g o f) P" using map_Prods_Nt_comp[of ?g f] by metis
  then have "map_Prods_Nt ?g (map_Prods_Nt f P) = map_Prods_Nt (\<lambda>x. x) P" 
    using gf_ident by auto
  then have P_unmap: "map_Prods_Nt ?g (map_Prods_Nt f P) = P" using  map_Prods_Nt_ident by metis
  show "P \<turnstile> u \<Rightarrow> v" using der uv_unmap P_unmap by simp
qed

lemma map_derives_equiv:
  assumes "inj f"
  shows "P \<turnstile> u \<Rightarrow>* v \<longleftrightarrow> (map_Prods_Nt f P) \<turnstile> map (map_Nt f) u \<Rightarrow>* map (map_Nt f) v"
proof -
  show ?thesis using assms map_derive_equiv[of f P u v] sorry
qed

lemma map_Lang_equiv:
  assumes "inj f"
  shows "Lang P S = Lang (map_Prods_Nt f P) (f S)"
proof -
  have start: "[Nt (f S)] = map (map_Nt f) [Nt S]" by simp
  have word: "\<forall>w. map Tm w = map (map_Nt f) (map Tm w)" by simp
  have "{w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w} = {w. (map_Prods_Nt f P) \<turnstile> [Nt (f S)] \<Rightarrow>* map Tm w}" 
    using assms start word map_derives_equiv[of f P] by metis 
  then show ?thesis using CFG.Lang_def by metis
qed

section "main proof"
thm derive.induct
thm rtrancl_derive_induct
thm derives_induct'

thm list.induct

lemma an_cfl:
  assumes "Lan = {word. \<exists>n \<ge> 0. word = (a^*n)}"
  shows "cfl TYPE('n) Lan"
proof  -
  obtain P X where P_def: "(P::('n, 'a) Prods) = {(X, [Tm a, Nt X]), (X, [])}" by simp
  let ?G = "Cfg P X"
  have "L ?G = Lan" 
  proof
    show "L ?G \<subseteq> Lan" 
    proof
      fix w
      assume "w \<in> L ?G"
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using CFG.Lang_def by fastforce
      then have "\<exists>im. P \<turnstile> [Nt X] \<Rightarrow>* im \<and> im = map Tm w"
        using rtranclp.cases by fastforce 
      then obtain im where im_src: "P \<turnstile> [Nt X] \<Rightarrow>* im \<and> im = map Tm w" by blast
      then have "P \<turnstile> [Nt X] \<Rightarrow>* im" by blast
      then have ex_n: "\<exists>n. im = ([Tm a]\<^sup>*n) @ [Nt X] \<or> im = ([Tm a]\<^sup>*n)" 
      proof(induction rule: rtrancl_derive_induct)
        case base
        then show ?case by auto
      next
        case (step u A v w')
        then have "P \<turnstile> u @ [Nt A] @ v \<Rightarrow> u @ w' @ v" using derive.intros by fast
        obtain n where n_src: "u @ [Nt A] @ v = ([Tm a]\<^sup>*n) @ [Nt X] \<or> u @ [Nt A] @ v = ([Tm a]\<^sup>*n)" using step by auto 
        then have eq_ax:"A = X" using P_def step.hyps(2) by auto
        have notin: "Nt X \<notin> set (([Tm a]\<^sup>*n))" by simp
        then have "u @ [Nt A] @ v = ([Tm a]\<^sup>*n) @ [Nt X]" using eq_ax n_src
          by (metis append_Cons in_set_conv_decomp)
        then have uv_eq: "u = ([Tm a]\<^sup>*n) \<and> v = []" using notin n_src eq_ax
          by (metis Cons_eq_appendI append_Cons_eq_iff append_Nil in_set_insert insert_Nil snoc_eq_iff_butlast)
        from eq_ax have "w' = [Tm a, Nt X] \<or> w' = []" using step P_def by simp
        then show ?case
        proof
          assume "w' = [Tm a, Nt X]"
          then have "u @ w' @ v = ([Tm a]\<^sup>*n) @ [Tm a, Nt X] @ []" using uv_eq by simp
          then have "u @ w' @ v = ([Tm a]\<^sup>*(n+1)) @ [Nt X]" by (simp add: repl_append2) 
          then show ?case by fastforce
        next
          assume "w' = []"
          then have "u @ w' @ v = ([Tm a]\<^sup>*n)" using uv_eq by simp
          then show ?case by fastforce
        qed
      qed
      then obtain n' where n'_src: "im = ([Tm a]\<^sup>*n') @ [Nt X] \<or> im = ([Tm a]\<^sup>*n')" by blast
      have "im = map Tm w" using im_src by blast
      then have map_tm: "map Tm w = ([Tm a]\<^sup>*n') @ [Nt X] \<or> map Tm w = ([Tm a]\<^sup>*n')" using n'_src sorry (*I cannot figure out why this unification does not wrok*)
      have "Nt X \<notin> set (map Tm w)" by auto 
      then have "map Tm w = ([Tm a]\<^sup>*n')" using map_tm by fastforce
      have "map Tm ([a]\<^sup>*n') = ([Tm a]\<^sup>*n')" by (simp add: map_concat)
      then have "w = (a^*n')" using \<open>map Tm w = ([Tm a]\<^sup>*n')\<close> repl_repl_one by (metis list.inj_map_strong sym.inject(2))
      then show "w \<in> Lan" using assms repl_repl_one by auto
    qed
  next
    show "Lan \<subseteq> L ?G" 
    proof
      fix w
      assume "w \<in> Lan"
      then obtain n where n_src: "n \<ge> 0 \<and> w = (a^*n)" using assms by blast
      (*"X \<Rightarrow>* a^n"*)
      have Xa: "P \<turnstile> [Nt X] \<Rightarrow>(n) ([Tm a]\<^sup>*n) @ [Nt X]"
        using P_def derive_n_same[of "X" "[Tm a]" "[]" _ _ "[]" ] by simp
      have X\<epsilon>: "P \<turnstile> ([Tm a]\<^sup>*n) @ [Nt X] \<Rightarrow> ([Tm a]\<^sup>*n)" using P_def derive.intros[of "X" "[]" _ "[Tm a]\<^sup>*n" "[]"] by fastforce
      have "([Tm a]\<^sup>*n) = map Tm w" using n_src by (metis concat_map_singleton map_replicate)
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Xa X\<epsilon> relpowp_imp_rtranclp
        by (smt (verit, best) rtranclp.simps) 
      then show "w \<in> L ?G" using CFG.Lang_def by fastforce
    qed
  qed
  then show ?thesis unfolding cfl_def by blast
qed

lemma anbn_cfl:  
  assumes "Lan = {word. \<exists>n \<ge> 0. word = (a^*n)@(b^*n)}"
  shows "cfl TYPE('n) Lan"
proof  -
  obtain P X where P_def: "(P::('n, 'a) Prods) = {(X, [Tm a, Nt X, Tm b]), (X, [])}" by simp
  let ?G = "Cfg P X"
  have "L ?G = Lan" 
  proof
    show "L ?G \<subseteq> Lan" sorry
  next
    show "Lan \<subseteq> L ?G" 
    proof
      fix w
      assume "w \<in> Lan"
      then obtain n where n_src: "n \<ge> 0 \<and> w = (a^*n)@(b^*n)" using assms by blast
      (*"X \<Rightarrow>* a^nb^n"*)
      have Xa: "P \<turnstile> [Nt X] \<Rightarrow>(n) ([Tm a]\<^sup>*n) @ [Nt X] @ ([Tm b]\<^sup>*n)"
        using P_def derive_n_same[of "X" "[Tm a]" "[Tm b]" _ _ "[]" "[]"] by simp
      have X\<epsilon>: "P \<turnstile> ([Tm a]\<^sup>*n) @ [Nt X] @ ([Tm b]\<^sup>*n) \<Rightarrow> ([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n)" 
        using P_def derive.intros[of "X" "[]" _ "[Tm a]\<^sup>*n" "[Tm b]\<^sup>*n"] by fastforce
      have "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = (map Tm (a^*n)) @ (map Tm (b^*n))" by (metis concat_map_singleton map_replicate)
      then have "([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n) = map Tm w" using n_src by simp
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using Xa X\<epsilon> relpowp_imp_rtranclp
        by (smt (verit, best) rtranclp.simps) 
      then show "w \<in> L ?G" using CFG.Lang_def by fastforce
    qed
  qed
  then show ?thesis unfolding cfl_def by blast
qed

lemma concat_closed: 
  assumes "cfl TYPE('n) L1"
  and "cfl TYPE('m) L2"
  and "Lconcat = {word. \<exists>w1 \<in> L1. \<exists>w2 \<in> L2. word = w1 @ w2}"
shows "cfl TYPE(('n option \<times> 'm option)) Lconcat"
proof -
  obtain P1 S1 where L1_def: "L1 = Lang P1 (S1::'n)" using assms(1) cfl_def[of L1] by auto 
  obtain P2 S2 where L2_def: "L2 = Lang P2 (S2::'m)" using assms(2) cfl_def[of L2] by auto
  let ?P1r = "map_Prods_Nt (\<lambda>A. (Some A, None)) P1"
  let ?P2r = "map_Prods_Nt (\<lambda>A. (None, Some A)) P2"
  let ?P = "{((None, None), [Nt (Some S1, None), Nt (None, Some S2)])} \<union> ?P1r \<union> ?P2r"
  let ?G = "Cfg ?P (None, None)"
  have "inj (\<lambda>A. (Some A, None))" by (simp add: inj_on_def) 
  then have L1r_def: "L1 = Lang ?P1r (Some S1, None)" 
    using L1_def map_Lang_equiv by fastforce
  have "inj (\<lambda>A. (None, Some A))" by (simp add: inj_on_def) 
  then have L2r_def: "L2 = Lang ?P2r ((None, Some S2))" 
    using L2_def map_Lang_equiv by fastforce

  have "L ?G = Lconcat"
  proof
    show "L ?G \<subseteq> Lconcat" sorry
  next
    show "Lconcat \<subseteq> L ?G" 
    proof
      fix w
      assume "w \<in> Lconcat"
      then obtain w1 w2 where w12_src: "(w1 \<in> L1) \<and> (w2 \<in> L2) \<and> w = w1 @ w2" using assms by blast
      from w12_src have "?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* map Tm w1" using L1r_def CFG.Lang_def by fast
      then have der_w1: "?P \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* map Tm w1" sorry 
      from w12_src have "?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* map Tm w2" using L2r_def CFG.Lang_def by fast
      then have der_w2: "?P \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* map Tm w2" sorry 
      have "?P \<turnstile> [Nt (None, None)] \<Rightarrow> [Nt (Some S1, None), Nt (None, Some S2)]" 
        using derive.intros[of "(None, None)" "[Nt (Some S1, None), Nt (None, Some S2)]" ?P "[]"] by auto
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w1 @ [Nt (None, Some S2)]" 
        using derives_append[of ?P "[Nt (Some S1, None)]" "map Tm w1" "[Nt (None, Some S2)]"] der_w1 by simp
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w1 @ map Tm w2"
        using derives_prepend[of ?P "[Nt (None, Some S2)]" "map Tm w2" "map Tm w1"] der_w2 by simp
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w" using w12_src by simp
      then show "w \<in> L ?G" using CFG.Lang_def by fastforce
    qed
  qed
  then show ?thesis unfolding cfl_def by blast
qed

section "try to formalize goal"

lemma anbncn_not_cfl: 
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"  "(Lan = {word. \<exists>n. word= (a^*n)@ (b^*n) @(c^*n) })"
  shows "\<not>(\<exists>G. L G = Lan)"
  sorry
(* proven in ../Philipp/anbncn.thy*)


(*this seems very tedious and unnecessary, there is likely a better way to do this*)
lemma intersection_eq: 
  assumes "a\<noteq>b" 
  and "b\<noteq>c" 
  and "c\<noteq>a"
  and "(\<exists>x y z. w = (a^*x)@(b^*y)@(c^*z) \<and> x = y)"
  and "(\<exists>x y z. w = (a^*x)@(b^*y)@(c^*z) \<and> y = z)"
  shows "(\<exists>x y z. w = (a^*x)@(b^*y)@(c^*z) \<and> x = y \<and> y = z)"
proof -
  obtain x1 y1 z1 where src1: "w = (a^*x1)@(b^*y1)@(c^*z1) \<and> x1 = y1" using assms by blast
  obtain x2 y2 z2 where src2: "w = (a^*x2)@(b^*y2)@(c^*z2) \<and> y2 = z2" using assms by blast
  have "(a^*x1)@(b^*y1)@(c^*z1) = (a^*x2)@(b^*y2)@(c^*z2)" using src1 src2 by simp
  have "count_list ((b^*y1)@(c^*z1)) a = 0" using assms by auto
  then have cx1: "count_list w a = x1" using src1 count_repl by fastforce
  have "count_list ((b^*y2)@(c^*z2)) a = 0" using assms by auto
  then have cx2: "count_list w a = x2" using src2 count_repl by fastforce
  from cx1 cx2 have eqx: "x1 = x2" by simp

  have "count_list ((a^*x1)@(c^*z1)) b = 0" using assms by auto
  then have cy1: "count_list w b = y1" using src1 count_repl by fastforce
  have "count_list ((a^*x2)@(c^*z2)) b = 0" using assms by auto
  then have cy2: "count_list w b = y2" using src2 count_repl by fastforce
  from cy1 cy2 have eqy: "y1 = y2" by simp

  have "count_list ((a^*x1)@(b^*y1)) c = 0" using assms by auto
  then have cz1: "count_list w c = z1" using src1 count_repl by fastforce
  have "count_list ((a^*x2)@(b^*y2)) c = 0" using assms by auto
  then have cz2: "count_list w c = z2" using src2 count_repl by fastforce
  from cz1 cz2 have eqz: "z1 = z2" by simp

  have "w = (a^*x1)@(b^*y1)@(c^*z1) \<and> x1 = y1 \<and> y1 = z1" using eqx eqy eqz src1 src2 by blast
  then show ?thesis by blast
qed

lemma not_closed: 
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows "\<exists>(L1::'t list set) L2. cfl TYPE('a option \<times> 'a option) L1 \<and> cfl TYPE('b option \<times> 'b option) L2 \<and> \<not>(\<exists>GI. L GI = (L1 \<inter> L2))"
proof -
  let ?anbn = "{word. \<exists>n \<ge> 0. word = (a^*n)@(b^*n)}"
  let ?cm = "{word. \<exists>m \<ge> 0. word = (c^*m)}"
  let ?an = "{word. \<exists>n \<ge> 0. word = (a^*n)}"
  let ?bmcm = "{word. \<exists>m \<ge> 0. word = (b^*m)@(c^*m)}"
  let ?anbncm = "{word. \<exists>n \<ge> 0. \<exists>m \<ge> 0. word = (a^*n)@(b^*n)@(c^*m)}"
  let ?anbmcm = "{word. \<exists>n \<ge> 0. \<exists>m \<ge> 0. word = (a^*n)@(b^*m)@(c^*m)}"
  have anbn: "cfl TYPE('a) ?anbn" using anbn_cfl by metis
  have cm: "cfl TYPE('a) ?cm" using an_cfl by metis
  have an: "cfl TYPE('b) ?an" using an_cfl by metis
  have bmcm: "cfl TYPE('b) ?bmcm" using anbn_cfl by metis
  have "?anbncm = (Lang_concat ?anbn ?cm)" by fastforce
  then have anbncm: "cfl TYPE('a option \<times> 'a option) ?anbncm" using anbn cm concat_closed by blast
  have "?anbmcm = (Lang_concat ?an ?bmcm)" by fastforce
  then have anbmcm: "cfl TYPE('b option \<times> 'b option) ?anbmcm" using an bmcm concat_closed by blast
  have "?anbncm \<inter> ?anbmcm = {word. \<exists>n \<ge> 0. word = (a^*n)@(b^*n)@(c^*n)}" 
    using assms intersection_eq by fast
  then have "cfl TYPE('a option \<times> 'a option) ?anbncm \<and> 
        cfl TYPE('b option \<times> 'b option) ?anbmcm \<and> 
        (\<nexists>GI. L GI = ?anbncm \<inter> ?anbmcm)" 
    using assms anbncn_not_cfl[of a b c "(?anbncm \<inter> ?anbmcm)"] anbncm anbmcm by auto
  (* this should be a simple unification, but maybe the TYPE in cfl causes issues*)
  then show ?thesis sorry 
qed

end