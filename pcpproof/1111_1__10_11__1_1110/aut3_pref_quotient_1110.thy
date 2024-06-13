theory aut3_pref_quotient_1110 
  imports Main "aut3" "aut10" "aut3_pref_quotient_automata_1110" "aut3_pref_quotient_automata_1110_eq_aut10"
begin
lemma pref_eq: "pref_quotient aut3 [C1,C1,C1,C0] = aut3_pref_quotient_automata_1110"
  by (simp add: aut3_def aut3_pref_quotient_automata_1110_def)

lemma "aut3_pref_quotient_1110": "lang (pref_quotient aut3 [C1,C1,C1,C0]) = lang aut10"
  using aut3_pref_quotient_automata_1110_eq_aut10 pref_eq by simp
end