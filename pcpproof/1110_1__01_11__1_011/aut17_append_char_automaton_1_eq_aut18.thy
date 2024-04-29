theory aut17_append_char_automaton_1_eq_aut18 
  imports Main "aut17_append_char_automaton_1_contains_aut18" "aut18_contains_aut17_append_char_automaton_1" "aut17_append_char_automaton_1" "aut18"
begin
  lemma "aut17_append_char_automaton_1_eq_aut18": "lang aut17_append_char_automaton_1 = lang aut18"
    using aut17_append_char_automaton_1_contains_aut18 aut18_contains_aut17_append_char_automaton_1 by auto
end