theory aut15_pref_quotient_1 
  imports Main "aut15" "aut16" "aut15_pref_quotient_automata_1" "aut15_pref_quotient_automata_1_eq_aut16"
begin
lemma pref_eq: "pref_quotient aut15 [C1] = aut15_pref_quotient_automata_1"
  by (simp add: aut15_def aut15_pref_quotient_automata_1_def)

lemma "aut15_pref_quotient_1": "lang (pref_quotient aut15 [C1]) = lang aut16"
  using aut15_pref_quotient_automata_1_eq_aut16 pref_eq by simp
end