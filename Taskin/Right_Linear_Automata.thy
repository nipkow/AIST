theory Right_Linear_Automata
imports
  DFA_rlin2
  "$AFP/Finite_Automata_HF/Finite_Automata_HF"
  HereditarilyFinite.Finitary
begin

subsection \<open>From Right-Linear Grammar to NFA\<close>

definition nfa_rlin2 :: "('n,'t)prods \<Rightarrow> ('n::finitary) \<Rightarrow> 't nfa" where
"nfa_rlin2 ps S =
  \<lparr> states = hf_of  ` ({S} \<union> nts ps),
    init = {hf_of S},
    final = hf_of ` {A \<in> nts ps. (A,[]) \<in> set ps},
    nxt = \<lambda>q a. hf_of ` nxt_rlin2 (set ps) (inv hf_of q) a,
    eps = Id \<rparr>"               

interpretation NFA_rlin2: nfa "nfa_rlin2 ps S"
unfolding nfa_rlin2_def proof (standard, goal_cases)
  case 1
  then show ?case by(simp)
next
  case 2
  then show ?case by auto
next
  case (3 q x)
  then show ?case by(auto simp add: nxt_rlin2_nts)
next
  case 4
  then show ?case by (simp add: Nts_def finite_nts_of_syms split_def)
qed
print_theorems

lemma nfa_init_nfa_rlin2: "nfa.init (nfa_rlin2 ps S) = hf_of ` {S}"
by (simp add: nfa_rlin2_def)

lemma nfa_final_nfa_rlin2: "nfa.final (nfa_rlin2 ps S) = hf_of ` {A \<in> nts ps. (A,[]) \<in> set ps}"
by (simp add: nfa_rlin2_def)

lemma nfa_nxt_nfa_rlin2: "nfa.nxt (nfa_rlin2 ps S) (hf_of A) a = hf_of ` nxt_rlin2 (set ps) A a"
by (simp add: nfa_rlin2_def inj)

lemma rtrancl_Id[simp]: "Id\<^sup>* = Id"
by (metis rtrancl_empty rtrancl_idemp)

lemma nfa_epsclo_nfa_rlin2: "M \<subseteq> {hf_of S} \<union> hf_of ` nts ps \<Longrightarrow> nfa.epsclo (nfa_rlin2 ps S) M = M"
unfolding NFA_rlin2.epsclo_def unfolding nfa_rlin2_def by(auto)

lemma nfa_nextl_nfa_rlin2: "M \<subseteq> {S} \<union> nts ps
  \<Longrightarrow> nfa.nextl (nfa_rlin2 ps S) (hf_of ` M) xs = hf_of ` nxts_rlin2_set (set ps) M xs"
proof(induction xs arbitrary: M)
  case Nil
  then show ?case
    by (simp add: nxts_rlin2_set_def)(fastforce intro!: nfa_epsclo_nfa_rlin2)
next
  case (Cons a xs)
  let ?epsclo = "nfa.epsclo (nfa_rlin2 ps S)"
  let ?nxt = "nfa.nxt (nfa_rlin2 ps S)"
  let ?nxts = "nfa.nextl (nfa_rlin2 ps S)"
  have "?nxts (hf_of ` M) (a # xs) = ?nxts (\<Union>x\<in>?epsclo (hf_of ` M). ?nxt x a) xs"
    by simp
  also have "\<dots> = ?nxts (\<Union>x\<in>hf_of ` M. ?nxt x a) xs"
    using Cons.prems by(subst nfa_epsclo_nfa_rlin2) auto
  also have "\<dots> = ?nxts (\<Union>m\<in>M. ?nxt (hf_of m) a) xs" by simp
  also have "\<dots> = ?nxts (\<Union>m\<in>M. hf_of ` nxt_rlin2 (set ps) m a) xs"
    by (simp add: nfa_nxt_nfa_rlin2)
  also have "\<dots> = ?nxts (hf_of ` (\<Union>m\<in>M. nxt_rlin2 (set ps) m a)) xs"
    by (metis image_UN)
  also have "\<dots> = hf_of ` nxts_rlin2_set (set ps) (\<Union>m\<in>M. nxt_rlin2 (set ps) m a) xs"
    using Cons.prems by(subst Cons.IH)(auto simp add: nxt_rlin2_nts)
  also have "\<dots> = hf_of ` nxts_rlin2_set (set ps) M (a # xs)"
    by (simp add: nxt_rlin2_set_def nxts_rlin2_set_def)
  finally show ?case .
qed

lemma lang_pres_nfa_rlin2: assumes "rlin2 (set ps)"
shows "nfa.language (nfa_rlin2 ps S) = CFG.lang ps S"
proof -
  have 1: "\<And>A xs. \<lbrakk> A \<in> nxts_rlin2_set (set ps) {S} xs; A \<in> nts ps; (A, []) \<in> set ps\<rbrakk> \<Longrightarrow>
    set ps \<turnstile> [Nt S] \<Rightarrow>* map Tm xs"
    using nxts_to_mult_derive by (metis (no_types, opaque_lifting) append.right_neutral derive.intros
      r_into_rtranclp rtranclp_trans singletonD)
 have 2: "\<And>xs. rlin2 (set ps) \<Longrightarrow> set ps \<turnstile> [Nt S] \<Rightarrow>* map Tm xs \<Longrightarrow>
          nxts_rlin2_set (set ps) {S} xs \<inter> {A \<in> nts ps. (A, []) \<in> set ps}  \<noteq> {}"
   using mult_derive_to_nxts rlin2_tms_eps
   by (metis (no_types, lifting) Nts_syms_equI disjoint_iff_not_equal mem_Collect_eq
      singletonI syms_not_eq)
  show ?thesis
    unfolding NFA_rlin2.language_def Lang_def nfa_init_nfa_rlin2 nfa_final_nfa_rlin2
      nfa_nextl_nfa_rlin2[OF Un_upper1]
    using 2[OF assms] by (auto simp: 1)
qed

subsection \<open>From DFA to Right-Linear Grammar\<close>

context dfa
begin
(* at the end: \<open>hf \<rightarrow> 'n::finitary\<close>, add \<open>hf_of \<dots>\<close> where needed *)
definition Prods_dfa :: "(hf, 'a) Prods" where
"Prods_dfa =
  (\<Union>q \<in> dfa.states M. \<Union>x. {(q,[Tm x, Nt(dfa.nxt M q x)])}) \<union> (\<Union>q \<in> dfa.final M. {(q,[])})"

lemma Prods_dfa_iff_dfa:
  "q \<in> dfa.states M \<Longrightarrow> Prods_dfa \<turnstile> [Nt q] \<Rightarrow>* map Tm w \<longleftrightarrow> nextl q w \<in> dfa.final M"
sorry

lemma "dfa.language M = Lang Prods_dfa (dfa.init M)"
unfolding language_def Lang_def by (simp add: Prods_dfa_iff_dfa)

end

end