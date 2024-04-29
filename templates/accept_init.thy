theory {{theory_name}}
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "{{instance_path}}" "{{autset_path}}" {{#each accept_paths}}"{{this}}" {{/each}}
begin

{{#each accepts}}
lemma accept_init_{{@index}}:
  "{{conf_name}} \<in> {{@root.autset_name}}"
  apply (simp only: {{conf_name}}_def {{@root.autset_name}}_def)
  using {{accept_lemma}} by simp
{{/each}}


lemma {{theory_name}}:
  "(pcp_init_set {{instance_name}}) \<subseteq> {{autset_name}}"
  apply (simp only: {{init_eq_lemma}})
  apply auto
  by (simp_all only:{{#each accepts}} accept_init_{{@index}} {{/each}})

end