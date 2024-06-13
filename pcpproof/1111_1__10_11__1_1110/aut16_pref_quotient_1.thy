theory aut16_pref_quotient_1 
  imports Main "aut16" "aut17" "aut16_pref_quotient_automata_1" "aut16_pref_quotient_automata_1_eq_aut17"
begin
lemma pref_eq: "pref_quotient aut16 [C1] = aut16_pref_quotient_automata_1"
  by (simp add: aut16_def aut16_pref_quotient_automata_1_def)

lemma "aut16_pref_quotient_1": "lang (pref_quotient aut16 [C1]) = lang aut17"
  using aut16_pref_quotient_automata_1_eq_aut17 pref_eq by simp
end