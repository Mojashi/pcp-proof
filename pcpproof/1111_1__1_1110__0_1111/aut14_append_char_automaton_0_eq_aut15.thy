theory aut14_append_char_automaton_0_eq_aut15 
  imports Main "aut14_append_char_automaton_0_contains_aut15" "aut15_contains_aut14_append_char_automaton_0" "aut14_append_char_automaton_0" "aut15"
begin
  lemma "aut14_append_char_automaton_0_eq_aut15": "lang aut14_append_char_automaton_0 = lang aut15"
    using aut14_append_char_automaton_0_contains_aut15 aut15_contains_aut14_append_char_automaton_0 by auto
end