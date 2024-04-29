theory aut3_pref_quotient_automata_1110_eq_aut8 
  imports Main "aut3_pref_quotient_automata_1110_contains_aut8" "aut8_contains_aut3_pref_quotient_automata_1110" "aut3_pref_quotient_automata_1110" "aut8"
begin
  lemma "aut3_pref_quotient_automata_1110_eq_aut8": "lang aut3_pref_quotient_automata_1110 = lang aut8"
    using aut3_pref_quotient_automata_1110_contains_aut8 aut8_contains_aut3_pref_quotient_automata_1110 by auto
end