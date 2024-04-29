theory aut6_pref_quotient_automata_1_eq_aut7 
  imports Main "aut6_pref_quotient_automata_1_contains_aut7" "aut7_contains_aut6_pref_quotient_automata_1" "aut6_pref_quotient_automata_1" "aut7"
begin
  lemma "aut6_pref_quotient_automata_1_eq_aut7": "lang aut6_pref_quotient_automata_1 = lang aut7"
    using aut6_pref_quotient_automata_1_contains_aut7 aut7_contains_aut6_pref_quotient_automata_1 by auto
end