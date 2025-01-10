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


end