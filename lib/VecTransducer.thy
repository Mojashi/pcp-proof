theory VecTransducer
  imports Main HOL.Option lin_terms Transducer
begin

abbreviation transduce_vec::"('in, 'v LinComb, 'state) Trans \<Rightarrow> 'in list \<Rightarrow> 'v LinComb set" where
  "transduce_vec t ins \<equiv> agg_lincomb ` (transduce t ins)"

fun none_then_zero::"'v LinComb option \<Rightarrow> 'v LinComb" where
  "none_then_zero None = zero" |
  "none_then_zero (Some l) = l"

fun sub_vec_trans::"('in, 'v LinComb, 'state) Trans \<Rightarrow> ('in, 'v LinComb, 'state2) Trans \<Rightarrow> ('in, 'v LinComb, ('state\<times>'state2)) Trans" where
  "sub_vec_trans t1 t2 = (let p = parallel_trans t1 t2 in(
  Trans (initial p)
    ((\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) ` (transition p))
  (accepting p)
))"

lemma agg_lincomb_agg_output_simp[simp]:
  "agg_lincomb (agg_output (Move s i e r)) = add_lincomb (none_then_zero e) (agg_lincomb (agg_output r))"
  apply(cases e) apply simp by simp

lemma sub_lincomb_agg_exc: "agg_input r1 = agg_input r2 \<Longrightarrow> 
    coeff (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2))) =
    coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))"
  sorry

lemma diff_vec_trans_sanity:
  fixes t1::"('in, 'v LinComb, 'state) Trans" and
        t2::"('in, 'v LinComb, 'state2) Trans"
      shows "e1\<in>transduce_vec t1 ins \<Longrightarrow> e2\<in>transduce_vec t2 ins \<Longrightarrow> 
              coeff (sub_lincomb e1 e2) \<in> coeff ` (transduce_vec (sub_vec_trans t1 t2) ins)"
  sorry

fun edges_used_count::"('in, 'out, 'state) Run \<Rightarrow> (('in, 'out, 'state) Edge) LinComb" where
  "edges_used_count r = map (\<lambda>e. (e,1)) (run_to_edges_list r)"

fun calc_output_from_euc::"('in, 'v LinComb, 'state) Edge LinComb \<Rightarrow> 'v LinComb" where
  "calc_output_from_euc euc = concat (map (\<lambda>(t, v). mult_lincomb (none_then_zero (out t)) v) euc)"

lemma calc_output_from_euc_add_1:
  shows "coeff (calc_output_from_euc ((new_edge, 1) # old)) =
         coeff (add_lincomb (calc_output_from_euc old) (none_then_zero (out new_edge)))"
  by auto

definition is_relax_constraint::"('in, 'out, 'state) Trans \<Rightarrow> (('in, 'out, 'state) Edge) Constraint \<Rightarrow> bool" where
  "is_relax_constraint t c \<equiv> \<forall>r. is_initial_accept_run t r \<and> length (agg_input r)>0 \<longrightarrow> assign_constraint (coeff (edges_used_count r)) c"

definition is_relax_mip::"('in, 'out, 'state) Trans \<Rightarrow> (('in, 'out, 'state) Edge) MIP \<Rightarrow> bool" where
  "is_relax_mip t c \<equiv> \<forall>r. is_initial_accept_run t r \<and> length (agg_input r)>0 \<longrightarrow> assign_mip (coeff (edges_used_count r)) c"

lemma relax_cons_relax:
  fixes t::"('in, 'out, 'state) Trans"
  assumes "is_relax_constraint t c1" and "is_relax_mip t c2"
  shows "is_relax_mip t (c1#c2)"
  using assms is_relax_constraint_def is_relax_mip_def 
  by (metis assign_mip.elims(2) assign_mip.elims(3) list_all_simps(1))

lemma relax_concat_relax:
  fixes t::"('in, 'out, 'state) Trans"
  assumes "is_relax_mip t c1" and "is_relax_mip t c2"
  shows "is_relax_mip t (c1@c2)"
  using assms apply(induct c1) apply (simp add: assms(2)) using relax_cons_relax
  by (simp add: assign_mip.elims(3) is_relax_mip_def)

lemma relax_output:
  fixes t::"('in, 'v LinComb, 'state) Trans"
  shows "has_correspond_edges t r \<Longrightarrow>
         coeff (calc_output_from_euc (edges_used_count r)) = coeff (agg_lincomb (agg_output r))"
proof(induct r)
  case (End x)
  then show ?case by simp
next
  case (Move x1a x2 x3 r)
  then have "has_correspond_edges t r" by simp
  then have IH: "coeff (calc_output_from_euc (edges_used_count r)) = 
             coeff (agg_lincomb (agg_output r))"
    using Move by blast
  define new_edge where "new_edge = Edge x1a x2 x3 (get_head_state r)"
  then have A:"edges_used_count (Move x1a x2 x3 r) = (new_edge, 1)#edges_used_count r" by simp
  
  show ?case apply(simp only:A calc_output_from_euc_add_1 agg_output.simps) apply(cases x3) 
    using IH new_edge_def apply auto[1] proof -
    fix a
    assume "x3 = Some a"
    have 1:"coeff (add_lincomb (calc_output_from_euc (edges_used_count r)) (none_then_zero (out new_edge))) =
          coeff (add_lincomb (agg_lincomb (agg_output r)) (none_then_zero (out new_edge)))"
      using IH add_coeff_same by blast
    then have "coeff (add_lincomb (calc_output_from_euc (edges_used_count r)) (none_then_zero (out new_edge))) = 
         coeff (agg_lincomb ((none_then_zero x3)#(agg_output r)))" using new_edge_def by auto
    then show "coeff (add_lincomb (calc_output_from_euc (edges_used_count r)) (none_then_zero (out new_edge))) =
         coeff (agg_lincomb (option_to_list x3 @ agg_output r))" by (simp add: \<open>x3 = Some a\<close>)
  qed
qed 

end