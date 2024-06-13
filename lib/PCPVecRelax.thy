theory PCPVecRelax
    imports Main PCPTransducer lin VecTransducer
begin

locale pcp_vec_relax_locale =
  fixes ts::"pcp" and relax_trans::"(PCP.alphabet, 'v lin.LinComb, nat) Trans"
  assumes TOTAL:"is_total_trans relax_trans"
begin

interpretation p: pcp_locale ts by simp?

abbreviation VU::"((nat, 'v lin.LinComb, nat×nat) Trans)" where
  "VU ≡ compose_trans p.UT relax_trans"
abbreviation VD::"((nat, 'v lin.LinComb, nat×nat) Trans)" where
  "VD ≡ compose_trans p.DT relax_trans"

abbreviation diff_vec_trans::"(nat, 'v lin.LinComb, (nat×nat)×nat×nat) Trans" where
  "diff_vec_trans ≡ sub_vec_trans VU VD"

lemma transduce_runs_then_initial:
  "r ∈ transduce_runs t ins ⟹ get_head_state r = initial t"
  by blast

lemma solution_get_diff_0:
  assumes "is_solution ts ans"
  shows "zero ∈ (agg_lincomb ` (transduce diff_vec_trans (rev (map (λi. length ts - i - 1) ans))))"
proof -
  define ans' where "ans' = (rev (map (λi. length ts - i - 1) ans))"
  obtain e where E:"e ∈ transduce p.UT ans' ∩ transduce p.DT ans'" using ans'_def p.solution_trans[OF assms(1)] by auto
  obtain r1 where R1:"r1 ∈ transduce_runs p.UT ans' ∧ agg_output r1 = e" using E by auto
  obtain r2 where R2:"r2 ∈ transduce_runs p.DT ans' ∧ agg_output r2 = e" using E by auto
  obtain p  where P:"p ∈ transduce_runs relax_trans e" using TOTAL by auto
  have r1_p_valid:"agg_output r1 = agg_input p" using P using R1 by blast
  have r2_p_valid:"agg_output r2 = agg_input p" using P using R2 by blast
  obtain p1 where P1:"p1 = compose_run r1 p" by auto
  obtain p2 where P2:"p2 = compose_run r2 p" by auto
  have O1:"agg_output p1 = agg_output p" using compose_run_output P1 R1 P by auto
  have O2:"agg_output p2 = agg_output p" using compose_run_output P2 R2 P by auto
  have O:"agg_output p2 = agg_output p1" using O1 O2 by simp
  have "is_accept_run VU p1" using compose_run_accept P P1 R1 by blast
  then have "is_initial_accept_run VU p1" 
    apply(simp add: P1 compose_trans_def)
    using transduce_runs_then_initial[of r1 p.UT ans'] transduce_runs_then_initial[of p relax_trans e] P R1 by simp
  then have "agg_output p ∈ transduce VU ans'" using P1 compose_run_input[OF r1_p_valid] R1 O1 by force
  then have P1_VALID:"agg_lincomb (agg_output p) ∈ transduce_vec VU ans'" by blast

  have "is_accept_run VD p2" using compose_run_accept P P2 R2 by blast
  then have "is_initial_accept_run VD p2"
    apply(simp add: P2 compose_trans_def)
    using transduce_runs_then_initial[of r2 p.DT ans'] transduce_runs_then_initial[of p relax_trans e] P R2 by simp
  then have "agg_output p ∈ transduce VD ans'" using P2 compose_run_input[OF r2_p_valid] R2 O2 by force
  then have P2_VALID:"agg_lincomb (agg_output p) ∈ transduce_vec VD  ans'" by blast

  define pp where PP:"pp = parallel_run p1 p2"  
  have "agg_input pp = ans'" apply(simp only:PP) using parallel_run_input[of p1 p2] apply simp using P1 R1 r1_p_valid by auto
  have "sub_lincomb (agg_lincomb (agg_output p)) (agg_lincomb (agg_output p)) ∈ transduce_vec (sub_vec_trans VU VD) ans'"
    using diff_vec_trans_sanity[OF P1_VALID P2_VALID] by blast
  then have "zero ∈ transduce_vec (sub_vec_trans VU VD) ans'" by simp
  then show ?thesis using ans'_def by blast
qed

lemma unable_zero_then_no_solution:
  assumes "⋀i. length i > 0 ⟹ zero ∉ transduce_vec diff_vec_trans i"
  shows "¬have_solution ts"
  using assms solution_get_diff_0 have_solution_def is_solution_def by auto

theorem relax_unable_zero_then_no_solution:
  assumes "is_relax_mip diff_vec_trans cs" and "finite (transition diff_vec_trans)" and
          "⋀a. assign_mip a cs ⟹ zero ≠ calc_output_from_euc (transition diff_vec_trans) a"
  shows "¬have_solution ts"
proof -
  have "have_solution ts ⟹ False" proof -
    assume "have_solution ts"
    then obtain sol where SOL:"is_solution ts sol" using have_solution_def by blast
    define rsol where "rsol = (rev (map (λi. length ts - i - 1) sol))"
    obtain r where R:"r ∈ transduce_runs diff_vec_trans rsol ∧ agg_lincomb (agg_output r) = zero"
      using solution_get_diff_0[OF SOL] rsol_def by auto
    have VALID_R:"is_initial_accept_run diff_vec_trans r" 
      using ‹r ∈ transduce_runs diff_vec_trans rsol ∧ agg_lincomb (agg_output r) = zero› by blast
    then have HCE:"has_correspond_edges diff_vec_trans r" by blast
    have "agg_input r = (rev (map (λi. length ts - i - 1) sol))" using R rsol_def by force
    then have LEN_R:"0 < length (agg_input r)" using SOL using is_solution_def by force
    have ZERO:"calc_output_from_euc (transition diff_vec_trans) (edges_used_count r) = zero"
      using relax_output[OF assms (2) HCE] R by argo
    have "assign_mip (edges_used_count r) cs" 
      using is_relax_mip_def[of diff_vec_trans cs] VALID_R LEN_R assms(1) by blast
    then have NONZERO:"zero ≠ calc_output_from_euc (transition diff_vec_trans) (edges_used_count r)"
      using assms(3) by blast
    show ?thesis using NONZERO ZERO by argo
  qed
  then show "¬ have_solution ts" by blast
qed
end
end