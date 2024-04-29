theory aut8_append_char_automaton_1_eq_aut9 
  imports Main "aut8_append_char_automaton_1_contains_aut9" "aut9_contains_aut8_append_char_automaton_1" "aut8_append_char_automaton_1" "aut9"
begin
  lemma "aut8_append_char_automaton_1_eq_aut9": "lang aut8_append_char_automaton_1 = lang aut9"
    using aut8_append_char_automaton_1_contains_aut9 aut9_contains_aut8_append_char_automaton_1 by auto
end