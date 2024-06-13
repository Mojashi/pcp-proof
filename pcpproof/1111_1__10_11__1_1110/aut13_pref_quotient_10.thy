theory aut13_pref_quotient_10 
  imports Main "aut13" "aut14" "aut13_pref_quotient_automata_10" "aut13_pref_quotient_automata_10_eq_aut14"
begin
lemma pref_eq: "pref_quotient aut13 [C1,C0] = aut13_pref_quotient_automata_10"
  by (simp add: aut13_def aut13_pref_quotient_automata_10_def)

lemma "aut13_pref_quotient_10": "lang (pref_quotient aut13 [C1,C0]) = lang aut14"
  using aut13_pref_quotient_automata_10_eq_aut14 pref_eq by simp
end