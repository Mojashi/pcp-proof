theory aut14_pref_quotient_01 
  imports Main "aut14" "aut15" "aut14_pref_quotient_automata_01" "aut14_pref_quotient_automata_01_eq_aut15"
begin
lemma pref_eq: "pref_quotient aut14 [C0,C1] = aut14_pref_quotient_automata_01"
  by (simp add: aut14_def aut14_pref_quotient_automata_01_def)

lemma "aut14_pref_quotient_01": "lang (pref_quotient aut14 [C0,C1]) = lang aut15"
  using aut14_pref_quotient_automata_01_eq_aut15 pref_eq by simp
end