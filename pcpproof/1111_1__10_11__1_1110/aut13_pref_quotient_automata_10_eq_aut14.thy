theory aut13_pref_quotient_automata_10_eq_aut14 
  imports Main "aut13_pref_quotient_automata_10_contains_aut14" "aut14_contains_aut13_pref_quotient_automata_10" "aut13_pref_quotient_automata_10" "aut14"
begin
  lemma "aut13_pref_quotient_automata_10_eq_aut14": "lang aut13_pref_quotient_automata_10 = lang aut14"
    using aut13_pref_quotient_automata_10_contains_aut14 aut14_contains_aut13_pref_quotient_automata_10 by auto
end