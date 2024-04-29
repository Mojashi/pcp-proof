theory aut1_append_char_automaton_1_eq_aut3 
  imports Main "aut1_append_char_automaton_1_contains_aut3" "aut3_contains_aut1_append_char_automaton_1" "aut1_append_char_automaton_1" "aut3"
begin
  lemma "aut1_append_char_automaton_1_eq_aut3": "lang aut1_append_char_automaton_1 = lang aut3"
    using aut1_append_char_automaton_1_contains_aut3 aut3_contains_aut1_append_char_automaton_1 by auto
end