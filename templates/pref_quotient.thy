theory {{theory_name}} 
  imports Main "{{src_aut_path}}" "{{dest_aut_path}}" "{{mid_aut_path}}" "{{eq_lemma_path}}"
begin
lemma pref_eq: "pref_quotient {{src_aut_name}} {{s}} = {{mid_aut_name}}"
  by (simp add: {{src_aut_name}}_def {{mid_aut_name}}_def)

lemma "{{theory_name}}": "lang (pref_quotient {{src_aut_name}} {{s}}) = lang {{dest_aut_name}}"
  using {{eq_lemma_name}} pref_eq by simp
end