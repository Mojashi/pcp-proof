theory aut2_append_char_automaton_1_eq_aut12 
  imports Main "aut2_append_char_automaton_1_contains_aut12" "aut12_contains_aut2_append_char_automaton_1" "aut2_append_char_automaton_1" "aut12"
begin
  lemma "aut2_append_char_automaton_1_eq_aut12": "lang aut2_append_char_automaton_1 = lang aut12"
    using aut2_append_char_automaton_1_contains_aut12 aut12_contains_aut2_append_char_automaton_1 by auto
end