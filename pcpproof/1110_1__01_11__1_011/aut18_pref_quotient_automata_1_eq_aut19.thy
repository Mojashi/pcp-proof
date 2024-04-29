theory aut18_pref_quotient_automata_1_eq_aut19 
  imports Main "aut18_pref_quotient_automata_1_contains_aut19" "aut19_contains_aut18_pref_quotient_automata_1" "aut18_pref_quotient_automata_1" "aut19"
begin
  lemma "aut18_pref_quotient_automata_1_eq_aut19": "lang aut18_pref_quotient_automata_1 = lang aut19"
    using aut18_pref_quotient_automata_1_contains_aut19 aut19_contains_aut18_pref_quotient_automata_1 by auto
end