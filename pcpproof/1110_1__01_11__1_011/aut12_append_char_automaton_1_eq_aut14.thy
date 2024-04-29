theory aut12_append_char_automaton_1_eq_aut14 
  imports Main "aut12_append_char_automaton_1_contains_aut14" "aut14_contains_aut12_append_char_automaton_1" "aut12_append_char_automaton_1" "aut14"
begin
  lemma "aut12_append_char_automaton_1_eq_aut14": "lang aut12_append_char_automaton_1 = lang aut14"
    using aut12_append_char_automaton_1_contains_aut14 aut14_contains_aut12_append_char_automaton_1 by auto
end