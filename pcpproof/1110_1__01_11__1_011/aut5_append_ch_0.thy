theory aut5_append_ch_0 
  imports Main "aut5" "aut6" "aut5_append_char_automaton_0" "aut5_append_char_automaton_0_eq_aut6"
begin

lemma transition_eq: "Automata.transition(append_ch aut5 C0) = Automata.transition aut5_append_char_automaton_0"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut5 C0) x c = aut5_append_char_automaton_0.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut5 C0) x c = aut5_append_char_automaton_0.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut5_def)
        apply (cases rule:aut5_append_char_automaton_0_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut5_def)
        apply (cases rule:aut5_append_char_automaton_0_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut5_append_char_automaton_0_def)
qed

lemma append_ch_eq:"append_ch aut5 C0 = aut5_append_char_automaton_0"
  using transition_eq apply (simp only:aut5_def aut5_append_char_automaton_0_def) by auto

lemma "aut5_append_ch_0": "lang (append_ch aut5 C0) = lang aut6"
  using aut5_append_char_automaton_0_eq_aut6 append_ch_eq by simp
end