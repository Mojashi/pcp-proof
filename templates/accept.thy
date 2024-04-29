theory {{theory_name}}
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "{{conf_path}}"
begin

lemma lang_l:"{{seq}} \<in> lang {{aut_name}}"
proof -
  have A:"rev {{rev_seq}} = {{seq}}" by auto
  have "{{rev_seq}} \<in> lang_rev {{aut_name}}"
    by (simp add: {{conf_name}}_def {{aut_name}}_def)
  then show ?thesis using A by (metis image_eqI)
qed

lemma {{theory_name}}:"PCPTrans.{{dir}} {{seq}} \<in> lang_autconf {{conf_name}}"
  using lang_l by (simp add: {{conf_name}}_def)

end