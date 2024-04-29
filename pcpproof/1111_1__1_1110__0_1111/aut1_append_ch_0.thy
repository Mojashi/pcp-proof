theory aut1_append_ch_0 
  imports Main "aut1" "aut9" "aut1_append_char_automaton_0" "aut1_append_char_automaton_0_eq_aut9"
begin

lemma transition_eq: "Automata.transition(append_ch aut1 C0) = Automata.transition aut1_append_char_automaton_0"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut1 C0) x c = aut1_append_char_automaton_0.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut1 C0) x c = aut1_append_char_automaton_0.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut1_def)
        apply (cases rule:aut1_append_char_automaton_0_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut1_def)
        apply (cases rule:aut1_append_char_automaton_0_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut1_append_char_automaton_0_def)
qed

lemma append_ch_eq:"append_ch aut1 C0 = aut1_append_char_automaton_0"
  using transition_eq apply (simp only:aut1_def aut1_append_char_automaton_0_def) by auto

lemma "aut1_append_ch_0": "lang (append_ch aut1 C0) = lang aut9"
  using aut1_append_char_automaton_0_eq_aut9 append_ch_eq by simp
end