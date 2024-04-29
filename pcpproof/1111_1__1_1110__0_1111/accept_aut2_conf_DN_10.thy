theory accept_aut2_conf_DN_10
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "aut2_conf"
begin

lemma lang_l:"[C1,C0] \<in> lang aut2"
proof -
  have A:"rev [C0,C1] = [C1,C0]" by auto
  have "[C0,C1] \<in> lang_rev aut2"
    by (simp add: aut2_conf_def aut2_def)
  then show ?thesis using A by (metis image_eqI)
qed

lemma accept_aut2_conf_DN_10:"PCPTrans.DN [C1,C0] \<in> lang_autconf aut2_conf"
  using lang_l by (simp add: aut2_conf_def)

end