theory aut3_pref_quotient_automata_1110_eq_aut10 
  imports Main "aut3_pref_quotient_automata_1110_contains_aut10" "aut10_contains_aut3_pref_quotient_automata_1110" "aut3_pref_quotient_automata_1110" "aut10"
begin
  lemma "aut3_pref_quotient_automata_1110_eq_aut10": "lang aut3_pref_quotient_automata_1110 = lang aut10"
    using aut3_pref_quotient_automata_1110_contains_aut10 aut10_contains_aut3_pref_quotient_automata_1110 by auto
end