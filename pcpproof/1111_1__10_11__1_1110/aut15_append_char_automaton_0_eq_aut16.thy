theory aut15_append_char_automaton_0_eq_aut16 
  imports Main "aut15_append_char_automaton_0_contains_aut16" "aut16_contains_aut15_append_char_automaton_0" "aut15_append_char_automaton_0" "aut16"
begin
  lemma "aut15_append_char_automaton_0_eq_aut16": "lang aut15_append_char_automaton_0 = lang aut16"
    using aut15_append_char_automaton_0_contains_aut16 aut16_contains_aut15_append_char_automaton_0 by auto
end