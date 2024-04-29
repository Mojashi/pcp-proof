theory aut5_append_char_automaton_1_eq_aut6 
  imports Main "aut5_append_char_automaton_1_contains_aut6" "aut6_contains_aut5_append_char_automaton_1" "aut5_append_char_automaton_1" "aut6"
begin
  lemma "aut5_append_char_automaton_1_eq_aut6": "lang aut5_append_char_automaton_1 = lang aut6"
    using aut5_append_char_automaton_1_contains_aut6 aut6_contains_aut5_append_char_automaton_1 by auto
end