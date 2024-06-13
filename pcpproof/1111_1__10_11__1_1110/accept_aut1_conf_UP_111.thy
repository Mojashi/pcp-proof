theory accept_aut1_conf_UP_111
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "aut1_conf"
begin

lemma lang_l:"[C1,C1,C1] \<in> lang aut1"
proof -
  have A:"rev [C1,C1,C1] = [C1,C1,C1]" by auto
  have "[C1,C1,C1] \<in> lang_rev aut1"
    by (simp add: aut1_conf_def aut1_def)
  then show ?thesis using A by (metis image_eqI)
qed

lemma accept_aut1_conf_UP_111:"PCPTrans.UP [C1,C1,C1] \<in> lang_autconf aut1_conf"
  using lang_l by (simp add: aut1_conf_def)

end