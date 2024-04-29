theory aut2_append_char_automaton_0_eq_aut16 
  imports Main "aut2_append_char_automaton_0_contains_aut16" "aut16_contains_aut2_append_char_automaton_0" "aut2_append_char_automaton_0" "aut16"
begin
  lemma "aut2_append_char_automaton_0_eq_aut16": "lang aut2_append_char_automaton_0 = lang aut16"
    using aut2_append_char_automaton_0_contains_aut16 aut16_contains_aut2_append_char_automaton_0 by auto
end