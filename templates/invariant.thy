theory {{theory_name}}
  imports Main "PCPLib.PCPTrans" "PCPLib.PCPAutomata" "{{accept_init_path}}" "{{closed_lemma_path}}"
begin

lemma non_empty_up:
  "(PCPTrans.UP []) \<notin> {{invariant}}"
  apply (simp only:{{invariant}}_def)
  apply auto
  apply (simp_all only: {{#each members}}{{this}}_def {{/each}})
    apply (simp_all only: {{#each member_auts}}{{this}}_def {{/each}})
  by auto

lemma non_empty_dn:
  "(PCPTrans.DN []) \<notin> {{invariant}}"
  apply (simp only:{{invariant}}_def)
  apply auto
  apply (simp_all only: {{#each members}}{{this}}_def {{/each}})
    apply (simp_all only: {{#each member_auts}}{{this}}_def {{/each}})
  by auto


lemma this_is_invariant:
  "is_invariant {{instance}} {{invariant}}"
using {{accept_init_lemma}} non_empty_up non_empty_dn {{closed_lemma}} is_invariant_def by auto


theorem pcp_no_solution:
  "\<not> have_solution {{instance}}"
using this_is_invariant no_solution_if_exists_invariant by auto

end