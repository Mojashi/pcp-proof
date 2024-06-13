theory aut4_append_char_automaton_1_eq_aut5 
  imports Main "aut4_append_char_automaton_1_contains_aut5" "aut5_contains_aut4_append_char_automaton_1" "aut4_append_char_automaton_1" "aut5"
begin
  lemma "aut4_append_char_automaton_1_eq_aut5": "lang aut4_append_char_automaton_1 = lang aut5"
    using aut4_append_char_automaton_1_contains_aut5 aut5_contains_aut4_append_char_automaton_1 by auto
end