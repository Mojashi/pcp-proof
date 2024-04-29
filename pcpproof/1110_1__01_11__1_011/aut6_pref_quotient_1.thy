theory aut6_pref_quotient_1 
  imports Main "aut6" "aut7" "aut6_pref_quotient_automata_1" "aut6_pref_quotient_automata_1_eq_aut7"
begin
lemma pref_eq: "pref_quotient aut6 [C1] = aut6_pref_quotient_automata_1"
  by (simp add: aut6_def aut6_pref_quotient_automata_1_def)

lemma "aut6_pref_quotient_1": "lang (pref_quotient aut6 [C1]) = lang aut7"
  using aut6_pref_quotient_automata_1_eq_aut7 pref_eq by simp
end