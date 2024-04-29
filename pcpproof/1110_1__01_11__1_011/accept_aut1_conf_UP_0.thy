theory accept_aut1_conf_UP_0
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "aut1_conf"
begin

lemma lang_l:"[C0] \<in> lang aut1"
proof -
  have A:"rev [C0] = [C0]" by auto
  have "[C0] \<in> lang_rev aut1"
    by (simp add: aut1_conf_def aut1_def)
  then show ?thesis using A by (metis image_eqI)
qed

lemma accept_aut1_conf_UP_0:"PCPTrans.UP [C0] \<in> lang_autconf aut1_conf"
  using lang_l by (simp add: aut1_conf_def)

end