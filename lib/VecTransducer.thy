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
proof(induct r1 r2 rule:parallel_run.induct)
  case (1 s1 s2)
  then show ?case by simp
  next case (2 e1s e1i e1o r1 e2s e2i e2o r2)
      then have IH: "coeff (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2))) =
        coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))" by fastforce
      have A:"coeff (sub_lincomb (agg_lincomb (agg_output (Move e1s (Some e1i) e1o r1))) (agg_lincomb (agg_output (Move e2s (Some e2i) e2o r2)))) = 
            coeff (sub_lincomb (add_lincomb (none_then_zero e1o) (agg_lincomb (agg_output r1))) (add_lincomb (none_then_zero e2o) (agg_lincomb (agg_output r2))))"
        using agg_lincomb_agg_output_simp by metis
      have B:"... = coeff (add_lincomb (sub_lincomb (none_then_zero e1o) (none_then_zero e2o)) (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2))))"
        using sub_add_exc by auto
      have "\<And>s. ... s = 
                coeff (add_lincomb (sub_lincomb (none_then_zero e1o) (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))) s"
        using IH by (simp only:add_coeff)
      then have C:"coeff (add_lincomb (sub_lincomb (none_then_zero e1o) (none_then_zero e2o)) (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2)))) = 
                  coeff (add_lincomb (sub_lincomb (none_then_zero e1o) (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2)))))"
        by blast
      have "... = coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move e1s (Some e1i) e1o r1) (Move e2s (Some e2i) e2o r2)))))"
        by simp
      then show ?case using A B C by simp
    next
  case (3 e1s e1o r1 r2)
      then have IH: "coeff (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2))) =
        coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))" by fastforce
      have A:"coeff (sub_lincomb (agg_lincomb (agg_output (Move e1s None e1o r1))) (agg_lincomb (agg_output r2))) = 
            coeff (sub_lincomb (add_lincomb (none_then_zero e1o) (agg_lincomb (agg_output r1))) (agg_lincomb (agg_output r2)))"
        using agg_lincomb_agg_output_simp by metis
      have B:"... = coeff (add_lincomb (sub_lincomb (none_then_zero e1o) zero) (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2))))"
        using sub_add_exc by auto
      have "\<forall>s. ... s = coeff (add_lincomb (sub_lincomb (none_then_zero e1o) zero) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))) s"
        using IH by (metis add_coeff)
      then have C:"coeff (add_lincomb (sub_lincomb (none_then_zero e1o) zero) (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2)))) =
               coeff (add_lincomb (sub_lincomb (none_then_zero e1o) zero) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2)))))"
         by auto
      have "... = coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move e1s None e1o r1) r2))))"
        by simp
      then show ?case using A B C by simp
  next
case ("4_1" v e2s e2o r2)
      then have IH: "coeff (sub_lincomb (agg_lincomb (agg_output (End v))) (agg_lincomb (agg_output r2))) =
        coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (End v) r2))))" by fastforce
      have A:"coeff (sub_lincomb (agg_lincomb (agg_output (End v))) (agg_lincomb (agg_output (Move e2s None e2o r2)))) = 
            coeff (sub_lincomb (agg_lincomb (agg_output (End v))) (add_lincomb (none_then_zero e2o) (agg_lincomb (agg_output r2))))"
        using agg_lincomb_agg_output_simp by (metis agg_output.simps(1)) 
      then have B:"coeff (sub_lincomb (agg_lincomb (agg_output (End v))) (agg_lincomb (agg_output (Move e2s None e2o r2)))) = 
                  coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (sub_lincomb zero (agg_lincomb (agg_output r2))))"
        using sub_add_exc by auto
      have "\<forall>s. ... s = coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (End v) r2))))) s"
        apply (simp only:add_coeff) using IH by auto
      then have C:"coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (sub_lincomb zero (agg_lincomb (agg_output r2)))) = 
            coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (End v) r2)))))"
        using IH by auto
      have "... = coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (End v) (Move e2s None e2o r2)))))"
        by simp
      then show ?case using A B C by simp
    next
      case ("4_2" v vd vb vc e2s e2o r2)
      then have IH: "coeff(sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output r2))) =
        coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move v (Some vd) vb vc) r2))))" by fastforce
      have A:"coeff (sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output (Move e2s None e2o r2)))) = 
            coeff (sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (add_lincomb (none_then_zero e2o) (agg_lincomb (agg_output r2))))"
        using agg_lincomb_agg_output_simp by metis
      have B:"... = coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output r2))))"
        using sub_add_exc by auto
      have "\<forall>s. coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output r2))))s =
             coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move v (Some vd) vb vc) r2))))) s"
        apply (simp only:add_coeff) using IH by auto
      then have C:"coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output r2)))) = coeff (add_lincomb (sub_lincomb zero (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move v (Some vd) vb vc) r2)))))"
        by blast
      have "... = coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move v (Some vd) vb vc) (Move e2s None e2o r2)))))"
        by simp
      then show ?case using A B C by simp
   next
  case (5 e1s e1i e1o r1 v)
  then show ?case by simp
next
  case (6 v e2s e2i e2o r2)
  then show ?case by simp
qed 

lemma diff_vec_trans_sanity:
  fixes t1::"('in, 'v LinComb, 'state) Trans" and
        t2::"('in, 'v LinComb, 'state2) Trans"
      shows "e1\<in>transduce_vec t1 ins \<Longrightarrow> e2\<in>transduce_vec t2 ins \<Longrightarrow> 
              coeff (sub_lincomb e1 e2) \<in> coeff ` (transduce_vec (sub_vec_trans t1 t2) ins)"
proof -
  assume ASM1:"e1\<in>transduce_vec t1 ins" and ASM2:"e2\<in>transduce_vec t2 ins"
  obtain r1 where R1:"is_initial_accept_run t1 r1 \<and> agg_input r1 = ins \<and> agg_lincomb (agg_output r1) = e1" using ASM1 by blast
  obtain r2 where R2:"is_initial_accept_run t2 r2 \<and> agg_input r2 = ins \<and> agg_lincomb (agg_output r2) = e2" using ASM2 by blast
  have "agg_input (parallel_run r1 r2) = ins" using parallel_run_input R1 by auto
  define r where R:"r = parallel_run r1 r2"
  define e where E:"e = agg_output r"
  have "agg_lincomb (options_to_list (map fst e)) = agg_lincomb (agg_output r1)"
    by (simp add: R E parallel_run_output_l)
  have "agg_lincomb (options_to_list (map snd e)) = agg_lincomb (agg_output r2)"
    by (simp add: R E parallel_run_output_r)
  have A:"sub_lincomb e1 e2 = sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2))" 
    using R1 R2 by fastforce
  define r' where "r' = map_run (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) r"
  have CC:"has_correspond_edges (parallel_trans t1 t2) r \<Longrightarrow> has_correspond_edges (sub_vec_trans t1 t2) r'" 
    apply(simp only: r'_def)
    proof(induct "(\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r))::((('v LinComb option)\<times>('v LinComb option)) \<Rightarrow> 'v LinComb)" 
               "r" rule: map_run.induct)
      case (1 v)
      then show ?case by auto
    next
      case (2 s i r)
      then show ?case by auto
    next
      case (3 s i e r)
      then have IH:"has_correspond_edges (sub_vec_trans t1 t2) (map_run (\<lambda>(l, r). sub_lincomb (none_then_zero l) (none_then_zero r)) r)" by auto
      then have "Edge s i (Some e) (get_head_state r) \<in> transition (parallel_trans t1 t2)" using 3 by auto
      then have "(\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) (Edge s i (Some e) (get_head_state r)) \<in> ((\<lambda>t. Edge (src t) (input t)
                    (case out t of None \<Rightarrow> Some zero | Some (l, r) \<Rightarrow> Some (sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) `
              transition (parallel_trans t1 t2))" by blast
      then have A:"(\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) (Edge s i (Some e) (get_head_state r)) \<in> transition (sub_vec_trans t1 t2)"
        apply (simp only: sub_vec_trans.simps) by simp
      
      show ?case proof(cases e)
        case (Pair a b)
        then have "(\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) (Edge s i (Some e) (get_head_state r))
               = Edge s i (Some(sub_lincomb (none_then_zero a) (none_then_zero b))) (get_head_state r)" by simp
        then have K:"Edge s i (Some(sub_lincomb (none_then_zero a) (none_then_zero b))) (get_head_state r) \<in> transition (sub_vec_trans t1 t2)"
          using A by auto
        show ?thesis apply(simp only:map_run.simps) apply(simp only: Pair has_correspond_edges.simps) apply(rule conjI) using K IH 
          apply (simp add: map_run_head) using K IH by (simp add: map_run_head)
      qed
    qed
  have K:"has_correspond_edges (parallel_trans t1 t2) r" using R parallel_run_has_correspond_edges R1 R2 by metis

  have "get_head_state r' = get_head_state (parallel_run r1 r2)"
    using r'_def R map_run_head[of "(\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r))" r] by blast
  then have R'HEAD:"get_head_state r' = initial (sub_vec_trans t1 t2)"
    using R1 R2 by (simp add: parallel_run_head)

  have "get_last_state r' = get_last_state (parallel_run r1 r2)"
    using r'_def R map_run_last[of "(\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r))" r] by blast
  then have R'LAST:"get_last_state r' = accepting (sub_vec_trans t1 t2)"
    using R1 R2 by (simp add:parallel_run_last)

  have C:"is_initial_accept_run (sub_vec_trans t1 t2) r'" using r'_def R R1 R2 R'HEAD R'LAST
    using CC[OF K] by blast

  then have I:"agg_input r' = ins" using r'_def map_run_input 
    using R \<open>agg_input (parallel_run r1 r2) = ins\<close> by blast
  have O':"agg_output r' = map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))"
    using r'_def map_run_output R by blast
  then have "coeff (sub_lincomb e1 e2) = 
    coeff (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))"
    using sub_lincomb_agg_exc using R1 R2 by metis
  then have "coeff(sub_lincomb e1 e2) = coeff(agg_lincomb (agg_output r'))"
    using r'_def using O' by presburger

  then show ?thesis using C I by blast
qed

fun edges_used_count::"('in, 'out, 'state) Run \<Rightarrow> (('in, 'out, 'state) Edge) LinComb" where
  "edges_used_count r = map (\<lambda>e. (e,1)) (run_to_edges_list r)"

fun calc_output_from_euc::"('in, 'v LinComb, 'state) Edge LinComb \<Rightarrow> 'v LinComb" where
  "calc_output_from_euc euc = concat (map (\<lambda>(t, v). mult_lincomb (none_then_zero (out t)) v) euc)"

lemma calc_output_from_euc_add_1:
  shows "coeff (calc_output_from_euc ((new_edge, 1) # old)) =
         coeff (add_lincomb (calc_output_from_euc old) (none_then_zero (out new_edge)))"
  by auto

lemma calc_output_from_euc_add_n:
  shows "coeff (calc_output_from_euc ((new_edge, n) # old)) =
         coeff (add_lincomb (calc_output_from_euc old) (mult_lincomb (none_then_zero (out new_edge)) n))"
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


definition is_zerovec_relax_constraint::"('in, 'v LinComb, 'state) Trans \<Rightarrow> (('in, 'v LinComb, 'state) Edge) Constraint \<Rightarrow> bool" where
  "is_zerovec_relax_constraint t c \<equiv> 
    \<forall>r. is_initial_accept_run t r \<and> length (agg_input r)>0 \<and> (coeff (agg_lincomb (agg_output r)) = coeff zero) \<longrightarrow> 
      assign_constraint (coeff (edges_used_count r)) c"

lemma "is_relax_constraint t c \<Longrightarrow> is_zerovec_relax_constraint t c"
  by (simp add: is_relax_constraint_def is_zerovec_relax_constraint_def)

definition is_zerovec_relax_mip::"('in, 'v LinComb, 'state) Trans \<Rightarrow> (('in, 'v LinComb, 'state) Edge) MIP \<Rightarrow> bool" where
  "is_zerovec_relax_mip t c \<equiv> 
    \<forall>r. is_initial_accept_run t r \<and> length (agg_input r)>0 \<and> (coeff (agg_lincomb (agg_output r)) = coeff zero) \<longrightarrow> 
      assign_mip (coeff (edges_used_count r)) c"

lemma "is_relax_mip t c \<Longrightarrow> is_zerovec_relax_mip t c"
  by (simp add: is_zerovec_relax_mip_def is_relax_mip_def)



end