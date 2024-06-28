theory AP
  imports mip_16074980106164510715 vt_01J1BZYC0NVH5937MFG9VEVJGR 
    "PCPLib.PCPVecRelax" "PCPLib.RelaxConstraints"
begin   

lemma "outgoing_edges mip ''((q2,q20),(q7,q20))'' = 
  {t_8772263929918217322, t_14858959524001828173, t_10588468385882600509}
"

theorem mip_zero_relax:
  "is_zerovec_relax_mip vt mip"
proof -

  have "is_relax_constraint vt c_bound_t_9973769699937430397"
    using positive_constraint_is_relax[of t_9973769699937430397 vt]
    unfolding c_bound_t_9973769699937430397_def vt_def by force


  have "is_relax_constraint vt c01J1BZYBY69S1WN8RH2XGC2R51" proof -
    have "is_euler_constraint vt ''((q6,q20),(q7,q18))'' c01J1BZYBY69S1WN8RH2XGC2R51" 
      unfolding c01J1BZYBY69S1WN8RH2XGC2R51_def vt_def 
      apply(simp only:is_euler_constraint_def, rule, simp, rule, simp)
  qed
qed
end