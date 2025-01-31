theory map_tms
  imports "../CFG"
begin

(* Functions mapping terminals to nonterminals which carry the same payload. *)


fun map_tms_sym :: "('t \<Rightarrow> 'n) \<Rightarrow> ('n,'t) sym \<Rightarrow> ('n,'tnew) sym" where
  "map_tms_sym f (Nt n) = Nt n" |
  "map_tms_sym f (Tm t) = Nt (f t)"

abbreviation "map_tms_syms f \<equiv> map (map_tms_sym f)"

fun map_tms_prod :: "('t \<Rightarrow> 'n) \<Rightarrow> ('n,'t) prod \<Rightarrow> ('n,'tnew) prod" where
  "map_tms_prod f (lhs,rhs) = (lhs, map_tms_syms f rhs)"

abbreviation "map_tms_Prods f ps \<equiv> (map_tms_prod f) ` ps"


(* Lhss are unaffected *)
lemma map_tms_Prods_Lhss: "Lhss (map_tms_Prods f ps) = Lhss ps" unfolding Lhss_def
proof
  show "(\<Union>(A, w)\<in>map_tms_Prods f ps. {A}) \<subseteq> (\<Union>(A, w)\<in>ps. {A})"
  proof
    fix x
    assume    "x \<in> (\<Union>(A, w)\<in>map_tms_Prods f ps. {A})"
    then have "x \<in> (\<Union>(A, w)\<in>map_tms_Prods f ps. {A})"
      by (smt (verit) UN_iff case_prod_conv image_iff map_tms_prod.elims map_tms_prod.simps) (* ? ? *)
    then show "x \<in> (\<Union>(A, w)\<in>ps. {A})"
      by fastforce
  qed
next
  show "(\<Union>(A, w)\<in>ps. {A}) \<subseteq> (\<Union>(A, w)\<in>map_tms_Prods f ps. {A})"
  proof
    fix x
    assume "x \<in> (\<Union>(A, w)\<in>ps. {A})"
    then show "x \<in> (\<Union>(A, w)\<in>map_tms_Prods f ps. {A})"
      by (smt (verit, ccfv_threshold) UN_iff image_iff map_tms_prod.elims old.prod.case)
  qed
qed


(* Derivation steps are unaffected as long as the terminals in the words are mapped accordingly.
   Note that additional derivations might be possible, though.
*)
lemma map_tms_Prods_map_tms_syms_derive:
  assumes "P \<turnstile> a \<Rightarrow> b"
  shows "map_tms_Prods f P \<turnstile> map_tms_syms f a \<Rightarrow> map_tms_syms f b"
proof -
  from assms obtain A w u1 u2
    where in_P: "(A,w) \<in> P"
      and a: "a = u1 @ Nt A # u2"
      and b: "b = u1 @ w @ u2"
    unfolding derive_iff by fast

  from in_P have "(A, map_tms_syms f w) \<in> map_tms_Prods f P"
    by force
  moreover from a have "map_tms_syms f a = map_tms_syms f u1 @ Nt A # map_tms_syms f u2"
    by auto
  moreover from b have "map_tms_syms f b = map_tms_syms f u1 @ map_tms_syms f w @ map_tms_syms f u2"
    by auto
  ultimately show ?thesis unfolding derive_iff by blast
qed


(* Sequences of derivation steps are unaffected as long as the terminals in the words are mapped accordingly.
   Note that additional derivations might be possible, though.
*)
lemma map_tms_Prods_map_tms_syms_deriven: "P \<turnstile> a \<Rightarrow>(n) b \<Longrightarrow> map_tms_Prods f P \<turnstile> map_tms_syms f a \<Rightarrow>(n) map_tms_syms f b"
proof (induction n arbitrary: b)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc(2) obtain c where a_c: "P \<turnstile> a \<Rightarrow>(n) c" and c_b: "P \<turnstile> c \<Rightarrow> b"
    by (rule relpowp_Suc_E)
  from Suc(1)[where b=c,OF a_c] map_tms_Prods_map_tms_syms_derive[where f=f,OF c_b]
  show ?case by (rule relpowp_Suc_I)
qed

(* Derivations are unaffected as long as the terminals in the words are mapped accordingly.
   Note that additional derivations might be possible, though.
*)
lemma map_tms_Prods_map_tms_syms_derives: "P \<turnstile> a \<Rightarrow>* b \<Longrightarrow> map_tms_Prods f P \<turnstile> map_tms_syms f a \<Rightarrow>* map_tms_syms f b"
  by (metis rtranclp_power map_tms_Prods_map_tms_syms_deriven)

(* auxiliary lemmas about map_tms_syms *)
lemma map_tms_syms_map_Nt: "map_tms_syms f (map Nt x) = map Nt x"
  by simp
lemma map_tms_syms_map_Tm: "map_tms_syms f (map Tm x) = map Nt (map f x)"
  by simp

(* specialization of map_tms_Prods_map_tms_syms_deriven for derivations yielding terminals *)
lemma map_tms_Prods_deriven: "P \<turnstile> map Nt a \<Rightarrow>(n) map Tm b \<Longrightarrow> map_tms_Prods f P \<turnstile> map Nt a \<Rightarrow>(n) map Nt (map f b)"
  by (metis map_tms_Prods_map_tms_syms_deriven map_tms_syms_map_Nt map_tms_syms_map_Tm)

(* specialization of map_tms_Prods_map_tms_syms_derives for derivations yielding terminals *)
lemma map_tms_Prods_derives: "P \<turnstile> map Nt a \<Rightarrow>* map Tm b \<Longrightarrow> map_tms_Prods f P \<turnstile> map Nt a \<Rightarrow>* map Nt (map f b)"
  by (metis map_tms_Prods_map_tms_syms_derives map_tms_syms_map_Nt map_tms_syms_map_Tm)

end