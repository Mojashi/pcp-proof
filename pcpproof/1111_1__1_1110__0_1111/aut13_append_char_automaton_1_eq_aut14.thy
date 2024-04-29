theory aut13_append_char_automaton_1_eq_aut14 
  imports Main "aut13_append_char_automaton_1_contains_aut14" "aut14_contains_aut13_append_char_automaton_1" "aut13_append_char_automaton_1" "aut14"
begin
  lemma "aut13_append_char_automaton_1_eq_aut14": "lang aut13_append_char_automaton_1 = lang aut14"
    using aut13_append_char_automaton_1_contains_aut14 aut14_contains_aut13_append_char_automaton_1 by auto
end