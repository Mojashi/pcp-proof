theory aut16_append_char_automaton_1_eq_aut17 
  imports Main "aut16_append_char_automaton_1_contains_aut17" "aut17_contains_aut16_append_char_automaton_1" "aut16_append_char_automaton_1" "aut17"
begin
  lemma "aut16_append_char_automaton_1_eq_aut17": "lang aut16_append_char_automaton_1 = lang aut17"
    using aut16_append_char_automaton_1_contains_aut17 aut17_contains_aut16_append_char_automaton_1 by auto
end