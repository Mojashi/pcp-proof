theory aut3_pref_quotient_automata_011_eq_aut11 
  imports Main "aut3_pref_quotient_automata_011_contains_aut11" "aut11_contains_aut3_pref_quotient_automata_011" "aut3_pref_quotient_automata_011" "aut11"
begin
  lemma "aut3_pref_quotient_automata_011_eq_aut11": "lang aut3_pref_quotient_automata_011 = lang aut11"
    using aut3_pref_quotient_automata_011_contains_aut11 aut11_contains_aut3_pref_quotient_automata_011 by auto
end