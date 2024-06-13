theory aut2_append_char_automaton_1_eq_aut11 
  imports Main "aut2_append_char_automaton_1_contains_aut11" "aut11_contains_aut2_append_char_automaton_1" "aut2_append_char_automaton_1" "aut11"
begin
  lemma "aut2_append_char_automaton_1_eq_aut11": "lang aut2_append_char_automaton_1 = lang aut11"
    using aut2_append_char_automaton_1_contains_aut11 aut11_contains_aut2_append_char_automaton_1 by auto
end