theory invariant
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "accept_init_inv" "closed"
begin

lemma non_empty_up:
  "(PCPTrans.UP []) \<notin> inv"
  apply (simp only:inv_def)
  apply auto
  apply (simp_all only: aut1_conf_def aut2_conf_def )
    apply (simp_all only: aut1_def aut2_def )
  by auto

lemma non_empty_dn:
  "(PCPTrans.DN []) \<notin> inv"
  apply (simp only:inv_def)
  apply auto
  apply (simp_all only: aut1_conf_def aut2_conf_def )
    apply (simp_all only: aut1_def aut2_def )
  by auto


lemma this_is_invariant:
  "is_invariant pcp_instance inv"
using accept_init_inv non_empty_up non_empty_dn closed is_invariant_def by auto


theorem pcp_no_solution:
  "\<not> have_solution pcp_instance"
using this_is_invariant no_solution_if_exists_invariant by auto

end