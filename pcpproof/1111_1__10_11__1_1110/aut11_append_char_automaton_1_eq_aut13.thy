theory aut11_append_char_automaton_1_eq_aut13 
  imports Main "aut11_append_char_automaton_1_contains_aut13" "aut13_contains_aut11_append_char_automaton_1" "aut11_append_char_automaton_1" "aut13"
begin
  lemma "aut11_append_char_automaton_1_eq_aut13": "lang aut11_append_char_automaton_1 = lang aut13"
    using aut11_append_char_automaton_1_contains_aut13 aut13_contains_aut11_append_char_automaton_1 by auto
end