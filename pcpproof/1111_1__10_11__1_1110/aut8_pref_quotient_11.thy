theory aut8_pref_quotient_11 
  imports Main "aut8" "aut9" "aut8_pref_quotient_automata_11" "aut8_pref_quotient_automata_11_eq_aut9"
begin
lemma pref_eq: "pref_quotient aut8 [C1,C1] = aut8_pref_quotient_automata_11"
  by (simp add: aut8_def aut8_pref_quotient_automata_11_def)

lemma "aut8_pref_quotient_11": "lang (pref_quotient aut8 [C1,C1]) = lang aut9"
  using aut8_pref_quotient_automata_11_eq_aut9 pref_eq by simp
end