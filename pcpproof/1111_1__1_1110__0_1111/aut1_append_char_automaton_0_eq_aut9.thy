theory aut1_append_char_automaton_0_eq_aut9 
  imports Main "aut1_append_char_automaton_0_contains_aut9" "aut9_contains_aut1_append_char_automaton_0" "aut1_append_char_automaton_0" "aut9"
begin
  lemma "aut1_append_char_automaton_0_eq_aut9": "lang aut1_append_char_automaton_0 = lang aut9"
    using aut1_append_char_automaton_0_contains_aut9 aut9_contains_aut1_append_char_automaton_0 by auto
end