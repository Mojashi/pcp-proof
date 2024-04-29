theory {{theory_name}} 
  imports Main "{{ab_contains_path}}" "{{ba_contains_path}}" "{{aut_a_path}}" "{{aut_b_path}}"
begin
  lemma "{{theory_name}}": "lang {{aut_a}} = lang {{aut_b}}"
    using {{ab_contains_lemma_name}} {{ba_contains_lemma_name}} by auto
end