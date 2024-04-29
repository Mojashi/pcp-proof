theory accept_init_inv
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "pcp_instance" "inv" "accept_aut1_conf_UP_110" 
begin


lemma accept_init_0:
  "init_conf_0 \<in> inv"
  apply (simp only: init_conf_0_def inv_def)
  using accept_aut1_conf_UP_110 by simp



lemma accept_init_inv:
  "(pcp_init_set pcp_instance) \<subseteq> inv"
  apply (simp only: init_eq)
  apply auto
  by (simp_all only: accept_init_0 )

end