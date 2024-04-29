theory aut18_pref_quotient_1 
  imports Main "aut18" "aut19" "aut18_pref_quotient_automata_1" "aut18_pref_quotient_automata_1_eq_aut19"
begin
lemma pref_eq: "pref_quotient aut18 [C1] = aut18_pref_quotient_automata_1"
  by (simp add: aut18_def aut18_pref_quotient_automata_1_def)

lemma "aut18_pref_quotient_1": "lang (pref_quotient aut18 [C1]) = lang aut19"
  using aut18_pref_quotient_automata_1_eq_aut19 pref_eq by simp
end