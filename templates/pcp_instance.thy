theory {{theory_name}}
  imports Main "PCPLib.PCP" "PCPLib.PCPTrans"
begin

{{{tile_def_string}}}

definition {{theory_name}}::"pcp" where
  "{{theory_name}} \<equiv> [ {{tile_names}} ]"

{{{initial_defs}}}

lemma {{init_eq_lemma_name}}: "pcp_init_set {{theory_name}} = { {{{init_names_union}}} }"
  apply (simp only: {{theory_name}}_def {{init_names_defs}} {{ tile_relevant_defs }})
  using starts_with_def by auto
end