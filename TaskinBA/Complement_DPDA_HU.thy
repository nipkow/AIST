theory Complement_DPDA_HU
  imports DPDA_HU
begin

datatype 'q st_extended = OST 'q | Q0' | D | F

instance st_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = OST q} \<union> {Q0', D, F}"
    by auto (metis st_extended.exhaust)
  show "finite (UNIV :: 'a st_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

datatype 's sym_extended = OSYM 's | X0

instance sym_extended :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = OSYM q} \<union> {X0}"
    by auto (metis sym_extended.exhaust)
  show "finite (UNIV :: 'a sym_extended set)"
    by (simp add: * full_SetCompr_eq)
qed

context dpda begin

definition scan_dpda_final_states :: "'q st_extended set" where
  "scan_dpda_final_states \<equiv> OST ` final_states M \<union> {F}"

definition epath_nonfinal :: "'q \<Rightarrow> 's \<Rightarrow> bool" where
  "epath_nonfinal p Z \<equiv> \<forall>i. \<exists>q \<gamma>. det_stepn i (p, [], [Z]) = Some (q, [], \<gamma>) \<and> q \<notin> final_states M"

definition epath_final :: "'q \<Rightarrow> 's \<Rightarrow> bool" where
  "epath_final p Z \<equiv> (\<forall>i. \<exists>q \<gamma>. det_stepn i (p, [], [Z]) = Some (q, [], \<gamma>)) \<and> 
                      (\<exists>i q \<gamma>. det_stepn i (p, [], [Z]) = Some (q, [], \<gamma>) \<and> q \<in> final_states M)"

fun scan_dpda_trans_fun :: "'q st_extended \<Rightarrow> 'a \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "scan_dpda_trans_fun (OST q) _ X0 = {(D, [X0])}"
| "scan_dpda_trans_fun (OST q) a (OSYM Z) = (if trans_fun M q a Z = {} \<and> eps_fun M q Z = {} then {(D, [OSYM Z])} else
                                              (\<lambda>(p, \<alpha>). (OST p, map OSYM \<alpha>)) ` trans_fun M q a Z)"
| "scan_dpda_trans_fun D a Z = {(D, [Z])}"
| "scan_dpda_trans_fun _ _ _ = {}"

fun scan_dpda_eps_fun :: "'q st_extended \<Rightarrow> 's sym_extended \<Rightarrow> ('q st_extended \<times> 's sym_extended list) set" where
  "scan_dpda_eps_fun Q0' X0 = {(OST (init_state M), [OSYM (init_symbol M), X0])}" 
| "scan_dpda_eps_fun (OST q) (OSYM Z) = (if epath_nonfinal q Z then {(D, [OSYM Z])} else
                                          if epath_final q Z then {(F, [OSYM Z])} else
                                            (\<lambda>(p, \<alpha>). (OST p, map OSYM \<alpha>)) ` eps_fun M q Z)"
| "scan_dpda_eps_fun F Z = {(D, [Z])}"
| "scan_dpda_eps_fun _ _ = {}"

definition scan_dpda :: "('q st_extended, 'a, 's sym_extended) pda" where
  "scan_dpda \<equiv> \<lparr> init_state = Q0', init_symbol = X0, final_states = scan_dpda_final_states,
                  trans_fun = scan_dpda_trans_fun, eps_fun = scan_dpda_eps_fun \<rparr>"

lemma dpda_scan: "dpda scan_dpda"
proof (standard, goal_cases)
  case (1 p a Z)
  have "finite (scan_dpda_trans_fun p a Z)"
    by (induction p a Z rule: scan_dpda_trans_fun.induct) (auto simp: finite_trans)
  then show ?case
    by (simp add: scan_dpda_def)
next
  case (2 p Z)
  have "finite (scan_dpda_eps_fun p Z)"
    by (induction p Z rule: scan_dpda_eps_fun.induct) (auto simp: finite_eps)
  then show ?case
    by (simp add: scan_dpda_def)
next
  case (3 q a Z)
  have "scan_dpda_trans_fun q a Z = {} \<or> (\<exists>p \<gamma>. scan_dpda_trans_fun q a Z = {(p, \<gamma>)})"
    by (induction q a Z rule: scan_dpda_trans_fun.induct, auto) (use true_sgn in force)+
  then show ?case
    by (simp add: scan_dpda_def)
next
  case (4 q Z)
  have "scan_dpda_eps_fun q Z = {} \<or> (\<exists>p \<gamma>. scan_dpda_eps_fun q Z = {(p, \<gamma>)})"
    by (induction q Z rule: scan_dpda_eps_fun.induct, auto) (use eps_sgn in force)
  then show ?case
    by (simp add: scan_dpda_def)
next
  case (5 q a Z)
  hence "scan_dpda_trans_fun q a Z \<noteq> {}"
    by (simp add: scan_dpda_def)
  then show ?case proof (induction q a Z rule: scan_dpda_trans_fun.induct)
    case (2 q a Z)
    hence eps: "eps_fun M q Z = {}" proof (cases)
      assume "\<not>(trans_fun M q a Z = {} \<and> eps_fun M q Z = {})"
      with 2 have "trans_fun M q a Z \<noteq> {}" by simp
      then show ?thesis
        by (simp add: true_or_eps)
    qed simp
    from eps have "det_step\<^sub>1 (q, [], [Z]) = None"
      using det_step\<^sub>1_op_rule by blast
    hence "det_stepn 1 (q, [], [Z]) = None" by simp
    hence "\<not>epath_nonfinal q Z \<and> \<not>epath_final q Z"
      unfolding epath_nonfinal_def epath_final_def using not_None_eq by blast
    with eps show ?case
      by (simp add: scan_dpda_def)
  qed (simp_all add: scan_dpda_def)
qed

lemma lang_scan_dpda: "pda.final_accept scan_dpda = pda.final_accept M"
  sorry

lemma scan_dpda_scans: 
"\<exists>q n \<gamma>. dpda.det_stepn scan_dpda n (init_state scan_dpda, w, [init_symbol scan_dpda]) = Some (q, [], \<gamma>)"
  sorry

end

datatype 'q st_num = S1 'q | S2 'q | S3 'q

instance st_num :: (finite) finite
proof
  have *: "UNIV = {t. \<exists>q. t = S1 q} \<union> {t. \<exists>q. t = S2 q} \<union> {t. \<exists>q. t = S3 q}"
    by auto (metis st_num.exhaust)
  show "finite (UNIV :: 'a st_num set)"
    by (simp add: * full_SetCompr_eq)
qed

locale complement_dpda =
  fixes M :: "('q :: finite, 'a :: finite, 's :: finite) pda"
  assumes "dpda M" 
      and "\<exists>q n \<gamma>. dpda.det_stepn M n (init_state M, w, [init_symbol M]) = Some (q, [], \<gamma>)"
begin

definition complement_dpda_init_state :: "'q st_num" where
  "complement_dpda_init_state \<equiv> if init_state M \<in> final_states M then S1 (init_state M) else S2 (init_state M)"

definition complement_dpda_final_states :: "'q st_num set" where
  "complement_dpda_final_states \<equiv> S3 ` final_states M"

fun complement_dpda_trans_fun :: "'q st_num \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('q st_num \<times> 's list) set" where
  "complement_dpda_trans_fun (S1 q) a Z = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` trans_fun M q a Z"
| "complement_dpda_trans_fun (S3 q) a Z = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` trans_fun M q a Z"
| "complement_dpda_trans_fun (S2 q) _ _ = {}"

fun complement_dpda_eps_fun :: "'q st_num \<Rightarrow> 's \<Rightarrow> ('q st_num \<times> 's list) set" where
  "complement_dpda_eps_fun (S1 q) Z = (\<lambda>(p, \<alpha>). (S1 p, \<alpha>)) ` eps_fun M q Z"
| "complement_dpda_eps_fun (S2 q) Z = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` eps_fun M q Z \<union>
                                        (if \<exists>a. trans_fun M q a Z \<noteq> {} then {(S3 q, [Z])} else {})"
| "complement_dpda_eps_fun (S3 q) Z = {}"

definition complement_dpda :: "('q st_num, 'a, 's) pda" where
  "complement_dpda \<equiv> \<lparr> init_state = complement_dpda_init_state, init_symbol = init_symbol M, final_states = complement_dpda_final_states,
                        trans_fun = complement_dpda_trans_fun, eps_fun = complement_dpda_eps_fun \<rparr>"

lemma dpda_M: "dpda M"
  using Complement_DPDA_HU.complement_dpda_def complement_dpda_axioms by blast

lemma pda_M: "pda M"
  using dpda_M dpda_def by blast

lemma finite_trans_M: "finite (trans_fun M q a Z)"
  using dpda_M dpda_def pda.finite_trans by blast

lemma finite_eps_M: "finite (eps_fun M q Z)"
  using dpda_M dpda_def pda.finite_eps by blast

lemma true_sgn_M: "trans_fun M q a Z = {} \<or> (\<exists>p \<gamma>. trans_fun M q a Z = {(p, \<gamma>)})"
  using dpda_M dpda.true_sgn by blast

lemma eps_sgn_M: "eps_fun M q Z = {} \<or> (\<exists>p \<gamma>. eps_fun M q Z = {(p, \<gamma>)})"
  using dpda_M dpda.eps_sgn by blast

lemma true_or_eps_M: "trans_fun M q a Z \<noteq> {} \<Longrightarrow> eps_fun M q Z = {}"
  using dpda_M dpda.true_or_eps by blast

lemma dpda_complement: "dpda complement_dpda"
proof (standard, goal_cases)
  case (1 p a Z)
  have "finite (complement_dpda_trans_fun p a Z)"
    by (induction p a Z rule: complement_dpda_trans_fun.induct) (auto simp: finite_trans_M)
  then show ?case
    by (simp add: complement_dpda_def)
next
  case (2 p Z)
  have "finite (complement_dpda_eps_fun p Z)"
    by (induction p Z rule: complement_dpda_eps_fun.induct) (auto simp: finite_eps_M)
  then show ?case
    by (simp add: complement_dpda_def)
next
  case (3 q a Z)
  have "complement_dpda_trans_fun q a Z = {} \<or> (\<exists>p \<gamma>. complement_dpda_trans_fun q a Z = {(p, \<gamma>)})"
    by (induction q a Z rule: complement_dpda_trans_fun.induct, auto) (metis (lifting) empty_iff image_empty image_insert surj_pair true_sgn_M)+
  then show ?case
    by (simp add: complement_dpda_def)
next
  case (4 q Z)
  have "complement_dpda_eps_fun q Z = {} \<or> (\<exists>p \<gamma>. complement_dpda_eps_fun q Z = {(p, \<gamma>)})"
  proof (induction q Z rule: complement_dpda_eps_fun.induct)
    case (1 q Z)
    then show ?case
      using eps_sgn_M by fastforce
  next
    case (2 q Z)
    let ?rh = "(\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` eps_fun M q Z \<union>
                                        (if \<exists>a. trans_fun M q a Z \<noteq> {} then {(S3 q, [Z])} else {})"
    have "?rh = {} \<or> (\<exists>p \<gamma>. ?rh = {(p, \<gamma>)})" proof (cases)
      assume a: "\<exists>a. trans_fun M q a Z \<noteq> {}" 
      hence "eps_fun M q Z = {}"
        using true_or_eps_M by blast
      with a have "?rh = {(S3 q, [Z])}" by simp
      then show ?thesis by blast 
    next
      assume "\<nexists>a. trans_fun M q a Z \<noteq> {}"
      hence "?rh = (\<lambda>(p, \<alpha>). if p \<in> final_states M then (S1 p, \<alpha>) else (S2 p, \<alpha>)) ` eps_fun M q Z" by simp
      then show ?thesis
        by (metis (lifting) image_empty image_insert surj_pair eps_sgn_M)
    qed
    then show ?case by simp
  qed simp
  then show ?case
    by (simp add: complement_dpda_def)
next
  case (5 q a Z)
  hence "complement_dpda_trans_fun q a Z \<noteq> {}"
    by (simp add: complement_dpda_def)
  then show ?case proof (induction q a Z rule: complement_dpda_trans_fun.induct)
    case (1 q a Z)
    hence "trans_fun M q a Z \<noteq> {}" by simp
    hence "eps_fun M q Z = {}"
      by (simp add: true_or_eps_M)
    then show ?case
      by (simp add: complement_dpda_def)
  qed (simp_all add: complement_dpda_def)
qed

declare dpda.det_step\<^sub>1.simps[OF dpda_M, simp]
declare dpda.det_stepn.simps[OF dpda_M, simp]
declare dpda.det_step\<^sub>1.simps[OF dpda_complement, simp]
declare dpda.det_stepn.simps[OF dpda_complement, simp]

lemma pda_complement: "pda complement_dpda"
  using dpda_complement dpda_def by blast

lemma lang_complement_dpda: "pda.final_accept complement_dpda = UNIV - pda.final_accept M"
  sorry

end

lemma complement_dpda_ex:
  assumes "dpda (M :: ('q :: finite, 'a :: finite, 's :: finite) pda)"
  shows "\<exists>(M' :: ('q st_extended st_num, 'a, 's sym_extended) pda). dpda M' \<and> pda.final_accept M' = UNIV - pda.final_accept M"
proof -
  let ?SM = "dpda.scan_dpda M :: ('q st_extended, 'a, 's sym_extended) pda"
  have dpda_sm: "dpda ?SM"
    using dpda.dpda_scan[OF assms] .
  have *: "\<And>w. \<exists>q n \<gamma>. dpda.det_stepn ?SM n (init_state ?SM, w, [init_symbol ?SM]) = Some (q, [], \<gamma>)"
    using dpda.scan_dpda_scans[OF assms] .
  have L1: "pda.final_accept ?SM = pda.final_accept M"
    using dpda.lang_scan_dpda[OF assms] .
  let ?CM = "complement_dpda.complement_dpda ?SM :: ('q st_extended st_num, 'a, 's sym_extended) pda"
  from dpda_sm * have dpda_cm: "dpda ?CM"
    using complement_dpda_def complement_dpda.dpda_complement by blast
  from dpda_sm * have L2: "pda.final_accept ?CM = UNIV - pda.final_accept ?SM"
    using complement_dpda_def complement_dpda.lang_complement_dpda by blast
  from dpda_cm L1 L2 show ?thesis by blast
qed

end