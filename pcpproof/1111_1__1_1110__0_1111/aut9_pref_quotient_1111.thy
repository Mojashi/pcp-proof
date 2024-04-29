theory aut9_pref_quotient_1111 
  imports Main "aut9" "aut10" "aut9_pref_quotient_automata_1111" "aut9_pref_quotient_automata_1111_eq_aut10"
begin
lemma pref_eq: "pref_quotient aut9 [C1,C1,C1,C1] = aut9_pref_quotient_automata_1111"
  by (simp add: aut9_def aut9_pref_quotient_automata_1111_def)

lemma "aut9_pref_quotient_1111": "lang (pref_quotient aut9 [C1,C1,C1,C1]) = lang aut10"
  using aut9_pref_quotient_automata_1111_eq_aut10 pref_eq by simp
end