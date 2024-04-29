theory aut15_pref_quotient_automata_1_eq_aut16 
  imports Main "aut15_pref_quotient_automata_1_contains_aut16" "aut16_contains_aut15_pref_quotient_automata_1" "aut15_pref_quotient_automata_1" "aut16"
begin
  lemma "aut15_pref_quotient_automata_1_eq_aut16": "lang aut15_pref_quotient_automata_1 = lang aut16"
    using aut15_pref_quotient_automata_1_contains_aut16 aut16_contains_aut15_pref_quotient_automata_1 by auto
end