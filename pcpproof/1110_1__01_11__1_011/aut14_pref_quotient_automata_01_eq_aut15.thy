theory aut14_pref_quotient_automata_01_eq_aut15 
  imports Main "aut14_pref_quotient_automata_01_contains_aut15" "aut15_contains_aut14_pref_quotient_automata_01" "aut14_pref_quotient_automata_01" "aut15"
begin
  lemma "aut14_pref_quotient_automata_01_eq_aut15": "lang aut14_pref_quotient_automata_01 = lang aut15"
    using aut14_pref_quotient_automata_01_contains_aut15 aut15_contains_aut14_pref_quotient_automata_01 by auto
end