theory aut3_pref_quotient_011 
  imports Main "aut3" "aut11" "aut3_pref_quotient_automata_011" "aut3_pref_quotient_automata_011_eq_aut11"
begin
lemma pref_eq: "pref_quotient aut3 [C0,C1,C1] = aut3_pref_quotient_automata_011"
  by (simp add: aut3_def aut3_pref_quotient_automata_011_def)

lemma "aut3_pref_quotient_011": "lang (pref_quotient aut3 [C0,C1,C1]) = lang aut11"
  using aut3_pref_quotient_automata_011_eq_aut11 pref_eq by simp
end