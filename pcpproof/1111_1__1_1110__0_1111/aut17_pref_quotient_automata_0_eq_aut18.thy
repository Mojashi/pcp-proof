theory aut17_pref_quotient_automata_0_eq_aut18 
  imports Main "aut17_pref_quotient_automata_0_contains_aut18" "aut18_contains_aut17_pref_quotient_automata_0" "aut17_pref_quotient_automata_0" "aut18"
begin
  lemma "aut17_pref_quotient_automata_0_eq_aut18": "lang aut17_pref_quotient_automata_0 = lang aut18"
    using aut17_pref_quotient_automata_0_contains_aut18 aut18_contains_aut17_pref_quotient_automata_0 by auto
end