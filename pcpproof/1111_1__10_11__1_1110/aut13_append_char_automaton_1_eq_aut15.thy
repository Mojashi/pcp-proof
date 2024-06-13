theory aut13_append_char_automaton_1_eq_aut15 
  imports Main "aut13_append_char_automaton_1_contains_aut15" "aut15_contains_aut13_append_char_automaton_1" "aut13_append_char_automaton_1" "aut15"
begin
  lemma "aut13_append_char_automaton_1_eq_aut15": "lang aut13_append_char_automaton_1 = lang aut15"
    using aut13_append_char_automaton_1_contains_aut15 aut15_contains_aut13_append_char_automaton_1 by auto
end