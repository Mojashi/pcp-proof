theory aut12_pref_quotient_1110 
  imports Main "aut12" "aut13" "aut12_pref_quotient_automata_1110" "aut12_pref_quotient_automata_1110_eq_aut13"
begin
lemma pref_eq: "pref_quotient aut12 [C1,C1,C1,C0] = aut12_pref_quotient_automata_1110"
  by (simp add: aut12_def aut12_pref_quotient_automata_1110_def)

lemma "aut12_pref_quotient_1110": "lang (pref_quotient aut12 [C1,C1,C1,C0]) = lang aut13"
  using aut12_pref_quotient_automata_1110_eq_aut13 pref_eq by simp
end