theory aut9_pref_quotient_automata_1111_eq_aut10 
  imports Main "aut9_pref_quotient_automata_1111_contains_aut10" "aut10_contains_aut9_pref_quotient_automata_1111" "aut9_pref_quotient_automata_1111" "aut10"
begin
  lemma "aut9_pref_quotient_automata_1111_eq_aut10": "lang aut9_pref_quotient_automata_1111 = lang aut10"
    using aut9_pref_quotient_automata_1111_contains_aut10 aut10_contains_aut9_pref_quotient_automata_1111 by auto
end