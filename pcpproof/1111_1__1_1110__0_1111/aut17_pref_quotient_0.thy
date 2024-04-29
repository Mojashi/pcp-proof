theory aut17_pref_quotient_0 
  imports Main "aut17" "aut18" "aut17_pref_quotient_automata_0" "aut17_pref_quotient_automata_0_eq_aut18"
begin
lemma pref_eq: "pref_quotient aut17 [C0] = aut17_pref_quotient_automata_0"
  by (simp add: aut17_def aut17_pref_quotient_automata_0_def)

lemma "aut17_pref_quotient_0": "lang (pref_quotient aut17 [C0]) = lang aut18"
  using aut17_pref_quotient_automata_0_eq_aut18 pref_eq by simp
end