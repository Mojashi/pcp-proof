theory aut3_append_char_automaton_1_eq_aut4 
  imports Main "aut3_append_char_automaton_1_contains_aut4" "aut4_contains_aut3_append_char_automaton_1" "aut3_append_char_automaton_1" "aut4"
begin
  lemma "aut3_append_char_automaton_1_eq_aut4": "lang aut3_append_char_automaton_1 = lang aut4"
    using aut3_append_char_automaton_1_contains_aut4 aut4_contains_aut3_append_char_automaton_1 by auto
end