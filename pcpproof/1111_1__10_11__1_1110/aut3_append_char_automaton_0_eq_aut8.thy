theory aut3_append_char_automaton_0_eq_aut8 
  imports Main "aut3_append_char_automaton_0_contains_aut8" "aut8_contains_aut3_append_char_automaton_0" "aut3_append_char_automaton_0" "aut8"
begin
  lemma "aut3_append_char_automaton_0_eq_aut8": "lang aut3_append_char_automaton_0 = lang aut8"
    using aut3_append_char_automaton_0_contains_aut8 aut8_contains_aut3_append_char_automaton_0 by auto
end