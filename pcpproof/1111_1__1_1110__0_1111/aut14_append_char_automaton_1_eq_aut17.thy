theory aut14_append_char_automaton_1_eq_aut17 
  imports Main "aut14_append_char_automaton_1_contains_aut17" "aut17_contains_aut14_append_char_automaton_1" "aut14_append_char_automaton_1" "aut17"
begin
  lemma "aut14_append_char_automaton_1_eq_aut17": "lang aut14_append_char_automaton_1 = lang aut17"
    using aut14_append_char_automaton_1_contains_aut17 aut17_contains_aut14_append_char_automaton_1 by auto
end