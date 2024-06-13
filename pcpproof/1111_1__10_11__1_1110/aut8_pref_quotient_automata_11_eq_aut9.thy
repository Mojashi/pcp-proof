theory aut8_pref_quotient_automata_11_eq_aut9 
  imports Main "aut8_pref_quotient_automata_11_contains_aut9" "aut9_contains_aut8_pref_quotient_automata_11" "aut8_pref_quotient_automata_11" "aut9"
begin
  lemma "aut8_pref_quotient_automata_11_eq_aut9": "lang aut8_pref_quotient_automata_11 = lang aut9"
    using aut8_pref_quotient_automata_11_contains_aut9 aut9_contains_aut8_pref_quotient_automata_11 by auto
end