theory aut1_append_char_automaton_0_eq_aut8 
  imports Main "aut1_append_char_automaton_0_contains_aut8" "aut8_contains_aut1_append_char_automaton_0" "aut1_append_char_automaton_0" "aut8"
begin
  lemma "aut1_append_char_automaton_0_eq_aut8": "lang aut1_append_char_automaton_0 = lang aut8"
    using aut1_append_char_automaton_0_contains_aut8 aut8_contains_aut1_append_char_automaton_0 by auto
end