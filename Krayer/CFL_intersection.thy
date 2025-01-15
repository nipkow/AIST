theory CFL_intersection
  imports  "../CFL" "../Stimpfle/CNF" HOL.Fun
begin

abbreviation repl :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" ("_\<^sup>*/_")
  where "xs\<^sup>*n \<equiv> concat (replicate n xs)"

(*From ../Philipp/anbncn.thy*)
abbreviation repl_one :: "'a  \<Rightarrow> nat \<Rightarrow> 'a list" ("_^*_")
  where "xs^*n \<equiv> replicate n xs"

section "CFL intersection is not closed"

section "auxiliaries"
abbreviation L :: "('n,'t) Cfg \<Rightarrow> 't list set" where
  "L G \<equiv> Lang (Prods G) (Start G)"

abbreviation Lang_concat :: "'t list set \<Rightarrow> 't list set \<Rightarrow> 't list set" where
  "Lang_concat L1 L2 \<equiv> {word. \<exists>w1 \<in> L1. \<exists>w2 \<in> L2. word = w1 @ w2}"

lemma repl_repl_one: "([a]\<^sup>*n) = (a^*n)"
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

lemma deriven_same_repl:
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

(*this is just a consequence of CFG.deriven_start1 *) 
thm CFG.deriven_start1
lemma derives_start1: 
  assumes "P \<turnstile> [Nt A] \<Rightarrow>* map Tm w"
  shows "\<exists>\<alpha>. P \<turnstile> \<alpha> \<Rightarrow>* (map Tm w) \<and> (A,\<alpha>) \<in> P"
proof -
  from assms obtain n where "P \<turnstile> [Nt A] \<Rightarrow>(n) map Tm w" using rtranclp_imp_relpowp by fast
  then obtain \<alpha> m where "n = Suc m \<and> P \<turnstile> \<alpha> \<Rightarrow>(m) map Tm w \<and> (A, \<alpha>) \<in> P" using deriven_start1 by fast
  then have "P \<turnstile> \<alpha> \<Rightarrow>* map Tm w \<and> (A, \<alpha>) \<in> P" by (auto simp add: relpowp_imp_rtranclp) 
  then show ?thesis by auto
qed  

subsection "Mapping over Nts + lemmas"
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

lemma map_inv_Prods: 
  assumes "inj f"
  shows "map_Prods_Nt (the_inv f) (map_Prods_Nt f P) = P"
proof -
  have ident: "((the_inv f) o f) = (\<lambda>x. x)" using assms the_inv_f_f by fastforce
  have "map_Prods_Nt (the_inv f) (map_Prods_Nt f P) = (map_Prods_Nt (the_inv f) o map_Prods_Nt f) P" by simp
  then have "map_Prods_Nt (the_inv f) (map_Prods_Nt f P) = map_Prods_Nt ((the_inv f) o f) P" 
    using map_Prods_Nt_comp by metis
  then have "map_Prods_Nt (the_inv f) (map_Prods_Nt f P) = map_Prods_Nt (\<lambda>x. x) P" 
    using ident by auto
  then show "map_Prods_Nt (the_inv f) (map_Prods_Nt f P) = P" using map_Prods_Nt_ident by metis
qed

lemma map_inv_syms: 
  assumes "inj f"
  shows "map (map_Nt (the_inv f)) (map (map_Nt f) w) = w"
proof -
  have "((the_inv f) o f) = (\<lambda>x. x)" using assms the_inv_f_f by fastforce
  then have "((map_Nt (the_inv f)) o (map_Nt f)) = (\<lambda>x. x)" using map_Nt_comp map_Nt_ident by metis
  have "\<forall>y. map (map_Nt (the_inv f)) (map (map_Nt f) y) = y" by (simp add: \<open>map_Nt (the_inv f) o map_Nt f = (\<lambda>x. x)\<close>)
  then show uv_unmap: "map (map_Nt (the_inv f)) (map (map_Nt f) w) = w" by blast
qed

lemma notin_range_imp_notin_map:
  assumes "x \<notin> range f"
  shows "Nt x \<notin> set (map (map_Nt f) w)"
proof -
  have "Nt x \<notin> range (map_Nt f)" using assms
    by (smt (verit) image_iff map_Nt.elims rangeI sym.distinct(1) sym.inject(1))
  then show "Nt x \<notin> set (map (map_Nt f) w)" by auto
qed

subsubsection "Equivalences after mapping a injective function over all Nts"
lemma map_derive_equiv:
  assumes "inj f"
  shows "P \<turnstile> u \<Rightarrow> v \<longleftrightarrow> (map_Prods_Nt f P) \<turnstile> map (map_Nt f) u \<Rightarrow> map (map_Nt f) v"
proof
  assume "P \<turnstile> u \<Rightarrow> v"
  then obtain A \<alpha> u' v' where obt: "(A,\<alpha>) \<in> P \<and> u = u' @ Nt A # v' \<and> v = u' @ \<alpha> @ v'" using derive_iff[of P] by blast
  then show "map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow> map (map_Nt f) v" using derive_iff[of "map_Prods_Nt f P"] by auto
next
  let ?Pm = "map_Prods_Nt f P"
  let ?um = "map (map_Nt f) u"
  let ?vm = "map (map_Nt f) v"
  let ?g = "the_inv f"
  assume "?Pm \<turnstile> ?um \<Rightarrow> ?vm"
  then obtain A \<alpha> u' v' where "(A,\<alpha>) \<in> ?Pm \<and> ?um = u' @ Nt A # v' \<and> ?vm = u' @ \<alpha> @ v'" 
    using derive_iff[of ?Pm] by blast
  then have "map_Prods_Nt ?g ?Pm \<turnstile> map (map_Nt ?g) ?um \<Rightarrow> map (map_Nt ?g) ?vm" 
    using derive_iff[of "map_Prods_Nt ?g ?Pm" "map (map_Nt ?g) ?um" "map (map_Nt ?g) ?vm"] by fastforce
  then show "P \<turnstile> u \<Rightarrow> v" using assms map_inv_syms map_inv_Prods by metis
qed

(* similar to CFG.relpowp_mono - necessary for map_derives_equiv *)
thm CFG.relpowp_mono
lemma relpowp_mono_fun: 
  fixes x y :: 'a
  shows "(\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow> (R ^^ n) x y \<Longrightarrow> (S ^^ n) (f x) (f y)"
    apply (induction n arbitrary: y) 
  by auto

lemma map_derives_imp_map:
  assumes "(map_Prods_Nt f P) \<turnstile> map (map_Nt f) u \<Rightarrow>* fv"
  shows "\<exists>v. fv = map (map_Nt f) v"
  using assms
proof(induction rule: rtrancl_derive_induct)
  case base
  then show ?case by auto
next
  case (step u A v w)
  then obtain A' where A'_src: "map (map_Nt f) [Nt A'] = [Nt A]" by auto
  from step obtain drvW where "map (map_Nt f) drvW = u @ [Nt A] @ v" by auto
  then have uAv_split: "u @ (map (map_Nt f) [Nt A']) @ v = map (map_Nt f) drvW" using A'_src by simp
  from uAv_split obtain u' where u'_src: "map (map_Nt f) u' = u" by (metis map_eq_append_conv)
  from uAv_split obtain v' where v'_src: "map (map_Nt f) v' = v" by (metis map_eq_append_conv)
  from step obtain w' where "map (map_Nt f) w' = w" by auto
  then have "u @ w @ v = map (map_Nt f) (u' @ w' @ v')" using u'_src v'_src by auto
  then show ?case by fast
qed

lemma map_derives_equiv:
  assumes "inj f"
  shows "P \<turnstile> u \<Rightarrow>* v \<longleftrightarrow> (map_Prods_Nt f P) \<turnstile> map (map_Nt f) u \<Rightarrow>* map (map_Nt f) v"
proof
  assume "P \<turnstile> u \<Rightarrow>* v"
  then obtain n where "P \<turnstile> u \<Rightarrow>(n) v" using rtranclp_imp_relpowp by fast
  then have "map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow>(n) map (map_Nt f) v" 
    using assms map_derive_equiv[of f P] relpowp_mono_fun[of "\<lambda>x y. P \<turnstile> x \<Rightarrow> y" "\<lambda> x y. (map_Prods_Nt f P) \<turnstile> x \<Rightarrow> y"] by blast
  then show "map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow>* map (map_Nt f) v"
    using relpowp_imp_rtranclp by fast
next
  assume "map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow>* map (map_Nt f) v"
  then obtain n where n_src: "map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow>(n) map (map_Nt f) v" 
    using rtranclp_imp_relpowp by fast
  then have "P \<turnstile> u \<Rightarrow>(n) v" 
  proof(induction n arbitrary: v)
    case 0
    then have "map (map_Nt f) u = map (map_Nt f) v" by simp
    then have "u = v" using assms map_inv_syms by metis 
    then show ?case by simp
  next
    case (Suc n v)
    then have "\<exists>w. map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow>(n) map (map_Nt f) w \<and> map_Prods_Nt f P \<turnstile> map (map_Nt f) w \<Rightarrow> map (map_Nt f) v"
      using relpowp_imp_rtranclp map_derives_imp_map by fastforce
    then obtain w where "map_Prods_Nt f P \<turnstile> map (map_Nt f) u \<Rightarrow>(n) map (map_Nt f) w \<and> map_Prods_Nt f P \<turnstile> map (map_Nt f) w \<Rightarrow> map (map_Nt f) v"
      by fast
    then have "P \<turnstile> u \<Rightarrow>(n) w \<and> P \<turnstile> w \<Rightarrow> v" using Suc(1) map_derive_equiv assms by blast
    then show ?case by auto
  qed
  then show "P \<turnstile> u \<Rightarrow>* v" using relpowp_imp_rtranclp by fast
qed

lemma map_Lang_equiv:
  assumes "inj f"
  shows "Lang P S = Lang (map_Prods_Nt f P) (f S)"
proof -
  have start: "[Nt (f S)] = map (map_Nt f) [Nt S]" by simp
  have word: "\<forall>w. map Tm w = map (map_Nt f) (map Tm w)" by simp
  have "{w. P \<turnstile> [Nt S] \<Rightarrow>* map Tm w} = {w. (map_Prods_Nt f P) \<turnstile> [Nt (f S)] \<Rightarrow>* map Tm w}" 
    using assms start word map_derives_equiv by metis 
  then show ?thesis using CFG.Lang_def by metis
qed

section "main proof"

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
      then have "\<exists>n. map Tm w = ([Tm a]\<^sup>*n) @ [Nt X] \<or> (map Tm w::('n, 'a)syms) = ([Tm a]\<^sup>*n)"
      proof(induction rule: rtrancl_derive_induct)
        case base
        then show ?case by auto
      next
        case (step u A v w')
        then have "A=X" using P_def by auto
        have "P \<turnstile> u @ [Nt X] @ v \<Rightarrow> u @ w' @ v" using \<open>A=X\<close> derive.intros step by fast
        obtain n where n_src: "u @ [Nt X] @ v = ([Tm a]\<^sup>*n) @ [Nt X] \<or> u @ [Nt X] @ v = ([Tm a]\<^sup>*n)" 
          using \<open>A=X\<close> step by auto 
        have notin: "Nt X \<notin> set ([Tm a]\<^sup>*n)" by simp
        then have "u @ [Nt X] @ v = ([Tm a]\<^sup>*n) @ [Nt X]" 
          using n_src append_Cons in_set_conv_decomp by metis
        then have uv_eq: "u = ([Tm a]\<^sup>*n) \<and> v = []" 
          using notin n_src Cons_eq_appendI append_Cons_eq_iff append_Nil in_set_insert insert_Nil snoc_eq_iff_butlast by metis
        have "w' = [Tm a, Nt X] \<or> w' = []" using step(2) P_def by auto
        then show ?case
        proof
          assume "w' = [Tm a, Nt X]"
          then have "u @ w' @ v = ([Tm a]\<^sup>*(Suc n)) @ [Nt X]" using uv_eq by (simp add: repl_append2) 
          then show ?case by blast
        next
          assume "w' = []"
          then show ?case using uv_eq by blast
        qed
      qed
      then obtain n' where n'_src: "(map Tm w) = ([Tm a]\<^sup>*n') @ [Nt X] \<or> ((map Tm w)::('n, 'a)syms) = ([Tm a]\<^sup>*n')" by auto
      have "Nt X \<notin> set (map Tm w)" by auto
      then have "((map Tm w)::('n, 'a)syms) = ([Tm a]\<^sup>*n')" using n'_src by fastforce
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
        using P_def deriven_same_repl[of "X" "[Tm a]" "[]" _ _ "[]" ] by simp
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
    show "L ?G \<subseteq> Lan" proof
      fix w
      assume "w \<in> L ?G"
      then have "P \<turnstile> [Nt X] \<Rightarrow>* map Tm w" using CFG.Lang_def by fastforce
      then have "\<exists>n. map Tm w = ([Tm a]\<^sup>*n) @ [Nt X] @ ([Tm b]\<^sup>*n) \<or> (map Tm w::('n, 'a)syms) = ([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n)"
      proof(induction rule: rtrancl_derive_induct)
        case base
        have "[Nt X] = ([Tm a]\<^sup>*0) @ [Nt X] @ ([Tm b]\<^sup>*0)" by auto
        then show ?case by fast
      next
        case (step u A v w')
        then have "A=X" using P_def by auto
        have "P \<turnstile> u @ [Nt X] @ v \<Rightarrow> u @ w' @ v" using \<open>A=X\<close> derive.intros step by fast
        obtain n where n_src: "u @ [Nt X] @ v = ([Tm a]\<^sup>*n) @ [Nt X] @ ([Tm b]\<^sup>*n) \<or> u @ [Nt X] @ v = ([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n)" 
          using \<open>A=X\<close> step by auto 
        have notin2: "Nt X \<notin> set ([Tm a]\<^sup>*n) \<and> Nt X \<notin> set ([Tm b]\<^sup>*n)" by simp
        have notin: "Nt X \<notin> set (([Tm a]\<^sup>*n) @ ([Tm b]\<^sup>*n))" by simp
        then have uv_split: "u @ [Nt X] @ v = ([Tm a]\<^sup>*n) @ [Nt X] @ ([Tm b]\<^sup>*n)" 
          by (metis n_src append_Cons in_set_conv_decomp)
        have u_eq: "u = ([Tm a]\<^sup>*n)"
          by (metis (no_types, lifting) uv_split notin2 Cons_eq_appendI append_Cons_eq_iff eq_Nil_appendI) 
        then have v_eq: "v = ([Tm b]\<^sup>*n)" 
           by (metis (no_types, lifting) uv_split notin2 Cons_eq_appendI append_Cons_eq_iff eq_Nil_appendI)
        have "w' = [Tm a, Nt X, Tm b] \<or> w' = []" using step(2) P_def by auto
        then show ?case
        proof
          assume "w' = [Tm a, Nt X, Tm b]"
          then have "u @ w' @ v = ([Tm a]\<^sup>*n) @ [Tm a, Nt X, Tm b] @ ([Tm b]\<^sup>*n)"  using u_eq v_eq by simp
          then have "u @ w' @ v = ([Tm a]\<^sup>*(Suc n)) @ [Nt X] @ ([Tm b]\<^sup>*(Suc n)) "
            by (smt (z3)repl_append repl_append2 append_Cons append_self_conv2 repl_repl_one replicate_app_Cons_same) 
          then show ?case by blast
        next
          assume "w' = []"
          then show ?case using u_eq v_eq by blast
        qed
      qed
      then obtain n' where n'_src: "(map Tm w) = ([Tm a]\<^sup>*n') @ [Nt X] @ ([Tm b]\<^sup>*n') \<or> ((map Tm w)::('n, 'a)syms) = ([Tm a]\<^sup>*n') @ ([Tm b]\<^sup>*n')" by auto
      have "Nt X \<notin> set (map Tm w)" by auto
      then have w_ab: "((map Tm w)::('n, 'a)syms) = ([Tm a]\<^sup>*n') @ ([Tm b]\<^sup>*n')" using n'_src by fastforce
      have map_a: "([Tm a]\<^sup>*n') = map Tm ([a]\<^sup>*n')" by (simp add: map_concat)
      have map_b: "([Tm b]\<^sup>*n') = map Tm ([b]\<^sup>*n')" by (simp add: map_concat)
      from w_ab map_a map_b have "((map Tm w)::('n, 'a)syms) = map Tm ([a]\<^sup>*n') @  map Tm ([b]\<^sup>*n')" by metis
      then have "((map Tm w)::('n, 'a)syms) = map Tm (([a]\<^sup>*n') @ ([b]\<^sup>*n'))" by simp
      then have "w = (a^*n')@(b^*n')" using repl_repl_one by (metis list.inj_map_strong sym.inject(2))
      then show "w \<in> Lan" using assms repl_repl_one by auto
    qed
  next
    show "Lan \<subseteq> L ?G" 
    proof
      fix w
      assume "w \<in> Lan"
      then obtain n where n_src: "n \<ge> 0 \<and> w = (a^*n)@(b^*n)" using assms by blast
      (*"X \<Rightarrow>* a^nb^n"*)
      have Xa: "P \<turnstile> [Nt X] \<Rightarrow>(n) ([Tm a]\<^sup>*n) @ [Nt X] @ ([Tm b]\<^sup>*n)"
        using P_def deriven_same_repl[of "X" "[Tm a]" "[Tm b]" _ _ "[]" "[]"] by simp
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
  let ?f1 = "(\<lambda>A. (Some A, None))"
  let ?f2 = "(\<lambda>A. (None, Some A))"
  let ?P1r = "map_Prods_Nt ?f1 P1"
  let ?P2r = "map_Prods_Nt ?f2 P2"
  let ?P = "{((None, None), [Nt (Some S1, None), Nt (None, Some S2)])} \<union> ?P1r \<union> ?P2r"
  let ?G = "Cfg ?P (None, None)"
  have "inj ?f1" by (simp add: inj_on_def) 
  then have L1r_def: "L1 = Lang ?P1r (Some S1, None)" 
    using L1_def map_Lang_equiv by fastforce
  have "inj ?f2" by (simp add: inj_on_def) 
  then have L2r_def: "L2 = Lang ?P2r ((None, Some S2))" 
    using L2_def map_Lang_equiv by fastforce

  have "L ?G = Lconcat"
  proof
    show "L ?G \<subseteq> Lconcat" 
    proof
      fix w
      assume "w \<in> L ?G"
      then have "?P \<turnstile> [Nt (None, None)] \<Rightarrow>* map Tm w" using CFG.Lang_def by fastforce
      then obtain \<alpha> where "?P \<turnstile> \<alpha> \<Rightarrow>* map Tm w \<and> ((None, None), \<alpha>) \<in> ?P" using derives_start1 by fast
      then have dervs: "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>* map Tm w" by auto
      then obtain n where "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) map Tm w" using rtranclp_imp_relpowp by fast
      then obtain Tmw where Tmw_src: "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) Tmw \<and> map Tm w = Tmw" by blast
      then have "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) Tmw" by simp
      then have "\<exists>n1 w1 n2 w2. n = n1 + n2 \<and> ?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>(n1) w1 \<and> ?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>(n2) w2 \<and> Tmw = w1@w2"
      proof(induction n arbitrary: Tmw)
        case (0 w')
        then show ?case by simp
      next
        case (Suc n w')
        then obtain im where im_src: "?P \<turnstile> [Nt (Some S1, None), Nt (None, Some S2)] \<Rightarrow>(n) im \<and> ?P \<turnstile> im \<Rightarrow> w'" by auto
        then obtain n1 w1 n2 w2 where nw_src: "n = n1 + n2 \<and> ?P1r \<turnstile> map (map_Nt ?f1)[Nt S1] \<Rightarrow>(n1) w1 \<and>
           ?P2r \<turnstile> map (map_Nt ?f2)[Nt S2] \<Rightarrow>(n2) w2 \<and> im = w1 @ w2" using Suc by fastforce
        obtain w1o where w1o_src: "w1 = map (map_Nt ?f1) w1o" using nw_src map_derives_imp_map relpowp_imp_rtranclp by meson
        obtain w2o where w2o_src: "w2 = map (map_Nt ?f2) w2o" using nw_src map_derives_imp_map relpowp_imp_rtranclp by meson
        have "(None, None) \<notin> range ?f1 \<and> (None, None) \<notin> range ?f2" by blast
        then have "Nt (None, None) \<notin> set w1 \<and> Nt (None, None) \<notin> set w2" 
          using notin_range_imp_notin_map w1o_src w2o_src by metis
        then have notin_im: "Nt (None, None) \<notin> set im" using nw_src by simp
        have "{((None, None), [Nt (Some S1, None), Nt (None, Some S2)])} \<turnstile> im \<Rightarrow> w' \<or> ?P1r \<turnstile> im \<Rightarrow> w' \<or> ?P2r \<turnstile> im \<Rightarrow> w'"
          using Un_derive im_src by blast
        then have "?P1r \<turnstile> im \<Rightarrow> w' \<or> ?P2r \<turnstile> im \<Rightarrow> w'" using notin_im derive.cases by fastforce
        then have "?P1r \<turnstile> w1@w2 \<Rightarrow> w' \<or> ?P2r \<turnstile> w1@w2 \<Rightarrow> w'" using nw_src by fast
        then show ?case
        proof
          assume "?P1r \<turnstile> w1@w2 \<Rightarrow> w'"
          then obtain A w u1 u2 where Awu_src: "(A, w) \<in> ?P1r \<and> w1 @ w2 = u1 @ Nt A # u2 \<and> w' = u1 @ w @ u2" 
            using derive_iff[of ?P1r] by blast
          then have pre_split: "w1 @ w2 = u1 @ [Nt A] @ u2" by simp
          then have in_either: "set w1 \<union> set w2 = set (u1 @ [Nt A] @ u2)" using set_append by metis
          from Awu_src have "A \<notin> range ?f2" by auto
          then have notin_2: "Nt A \<notin> set w2" using notin_range_imp_notin_map w2o_src by fast
          then obtain Au21 where Au21_src: "[Nt A] @ u2 = Au21@w2" using pre_split
            by (smt (verit, ccfv_SIG) append_Cons append_eq_append_conv2 in_set_conv_decomp) 
          then have "hd Au21 = Nt A" using notin_2
            by (metis append_Cons hd_append list.sel(1) list.set_sel(1))
          then obtain u21 where u21_src: "u21 = tl Au21 \<and> u2 = u21@w2" using Au21_src
            by (metis Cons_eq_appendI list.sel(3) list.set_intros(1) notin_2 self_append_conv2 tl_append2)
          then have cond4: "w' = u1 @ w @ u21 @ w2" using Awu_src by simp
          have "w1 = u1 @ [Nt A] @ u21" using u21_src pre_split by simp
          then have "?P1r \<turnstile> w1 \<Rightarrow> u1 @ w @ u21" using Awu_src derive.intros by fast
          then have cond2: "?P1r \<turnstile> map (map_Nt ?f1)[Nt S1] \<Rightarrow>(Suc n1) u1 @ w @ u21" using nw_src by auto
          have "Suc n = Suc n1 + n2" using nw_src by simp  
          then show ?case using cond4 cond2 nw_src by fastforce
        next
          assume "?P2r \<turnstile> w1@w2 \<Rightarrow> w'"
          then obtain A w u1 u2 where Awu_src: "(A, w) \<in> ?P2r \<and> w1 @ w2 = u1 @ Nt A # u2 \<and> w' = u1 @ w @ u2" 
            using derive_iff[of ?P2r] by blast
          then have pre_split: "w1 @ w2 = u1 @ [Nt A] @ u2" by simp
          then have in_either: "set w1 \<union> set w2 = set (u1 @ [Nt A] @ u2)" using set_append by metis
          from Awu_src have "A \<notin> range ?f1" by auto
          then have notin_1: "Nt A \<notin> set w1" using notin_range_imp_notin_map w1o_src by fast
          then have rev_notin_1: "Nt A \<notin> set (rev w1)" by simp
          have rev_pre_split: "rev w2 @ rev w1 = rev u2 @ rev [Nt A] @ rev u1" using pre_split
            by (metis append_assoc rev_append) 
          then have rev_pre_split: "rev w2 @ rev w1 = rev u2 @ [Nt A] @ rev u1" by simp
          (*there has to be a better way than reversing the list, but otherwise this proof step does not work*)
          (*this part of the proof is wanky anyways. It feels really hard reasoning about lists when knowing that something is or is not an element of the list *)
          obtain u12Ar where u12Ar_src: "[Nt A] @ rev u1 = u12Ar @ rev w1" using rev_notin_1 rev_pre_split 
            by (smt (verit, ccfv_SIG) append_Cons append_eq_append_conv2 in_set_conv_decomp) 
          then have "hd u12Ar = Nt A" using rev_notin_1
            by (metis append_Cons hd_append list.sel(1) list.set_sel(1))
          then obtain u12r where "u12r = tl u12Ar \<and> rev u1 = u12r @ rev w1" using u12Ar_src
            by (metis Cons_eq_appendI list.sel(3) list.set_intros(1) rev_notin_1 self_append_conv2 tl_append2)
          then have u12_src: "u1 = w1 @ rev u12r"
            by (simp add: rev_eq_append_conv) 
          then have cond4: "w' = w1 @ (rev u12r) @ w @ u2" using Awu_src by simp
          have "w2 = rev u12r @ [Nt A] @ u2" using u12_src pre_split by simp
          then have "?P2r \<turnstile> w2 \<Rightarrow> rev u12r @ w @ u2" using Awu_src derive.intros by fast
          then have cond2: "?P2r \<turnstile> map (map_Nt ?f2)[Nt S2] \<Rightarrow>(Suc n2) rev u12r @ w @ u2" using nw_src by auto
          have "Suc n = n1 + Suc n2" using nw_src by simp  
          then show ?case using cond4 cond2 nw_src by fastforce
        qed
      qed
      then obtain n1 n2 w1 w2 where nw_src: "n = n1 + n2 \<and> ?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>(n1) w1 \<and> ?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>(n2) w2 \<and> Tmw = w1@w2" by fast
      from nw_src have "map Tm w = w1@w2" using Tmw_src by auto
      then obtain w1' w2' where w12'_src: "((map Tm w1')::('n option \<times> 'm option, 'a)syms) = w1 \<and> 
        ((map Tm w2')::('n option \<times> 'm option, 'a)syms) = w2 \<and> w1'@w2' = w"
        by (metis append_eq_map_conv) 
      from w12'_src have "?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* ((map Tm w1')::('n option \<times> 'm option, 'a)syms)" using nw_src relpowp_imp_rtranclp by fast
      then have "w1' \<in> L1" using CFG.Lang_def by (metis L1r_def mem_Collect_eq)
      from w12'_src have "?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* ((map Tm w2')::('n option \<times> 'm option, 'a)syms)" using nw_src relpowp_imp_rtranclp by fast
      then have "w2' \<in> L2" using CFG.Lang_def by (metis L2r_def mem_Collect_eq)
      show "w \<in> Lconcat" using \<open>w1' \<in> L1\<close> \<open>w2' \<in> L2\<close> w12'_src assms(3) by blast
    qed
  next
    show "Lconcat \<subseteq> L ?G" 
    proof
      fix w
      assume "w \<in> Lconcat"
      then obtain w1 w2 where w12_src: "(w1 \<in> L1) \<and> (w2 \<in> L2) \<and> w = w1 @ w2" using assms by blast
      have P1r_sub: "?P1r \<subseteq> ?P" by auto
      from w12_src have "?P1r \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* map Tm w1" using L1r_def CFG.Lang_def by fast
      then have der_w1: "?P \<turnstile> [Nt (Some S1, None)] \<Rightarrow>* map Tm w1" using P1r_sub psubRtcDeriv by blast
      have P2r_sub: "?P2r \<subseteq> ?P" by auto 
      from w12_src have "?P2r \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* map Tm w2" using L2r_def CFG.Lang_def by fast
      then have der_w2: "?P \<turnstile> [Nt (None, Some S2)] \<Rightarrow>* map Tm w2" using P2r_sub psubRtcDeriv by blast
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

section "formalize goal"

lemma anbncn_not_cfl: 
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"  "(Lan = {word. \<exists>n. word= (a^*n)@ (b^*n) @(c^*n) })"
  shows "\<not>(\<exists>G. L G = Lan)"
  sorry
(* proven in ../Philipp/anbncn.thy*)


(*this seems very tedious and unnecessary, there is likely a better way to do this*)
lemma intersection_anbncn: 
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

lemma intersection_not_closed: 
  assumes "a\<noteq>b" "b\<noteq>c" "c\<noteq>a"
  shows "\<exists>L1 L2. cfl TYPE('a option \<times> 'a option) L1 \<and> cfl TYPE('b option \<times> 'b option) L2 \<and> (\<nexists>GI. L GI = (L1 \<inter> L2))"
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
    using assms intersection_anbncn by fast
  then have "cfl TYPE('a option \<times> 'a option) ?anbncm \<and> 
        cfl TYPE('b option \<times> 'b option) ?anbmcm \<and> 
        (\<nexists>GI. L GI = ?anbncm \<inter> ?anbmcm)" 
    using assms anbncn_not_cfl[of a b c] anbncm anbmcm by auto
  (* this should be a simple unification, but maybe the TYPE in cfl causes issues*)
  then show ?thesis sorry
qed

end