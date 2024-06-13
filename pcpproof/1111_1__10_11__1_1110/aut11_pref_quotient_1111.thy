theory aut11_pref_quotient_1111 
  imports Main "aut11" "aut12" "aut11_pref_quotient_automata_1111" "aut11_pref_quotient_automata_1111_eq_aut12"
begin
lemma pref_eq: "pref_quotient aut11 [C1,C1,C1,C1] = aut11_pref_quotient_automata_1111"
  by (simp add: aut11_def aut11_pref_quotient_automata_1111_def)

lemma "aut11_pref_quotient_1111": "lang (pref_quotient aut11 [C1,C1,C1,C1]) = lang aut12"
  using aut11_pref_quotient_automata_1111_eq_aut12 pref_eq by simp
end