theory aut2_append_ch_0 
  imports Main "aut2" "aut16" "aut2_append_char_automaton_0" "aut2_append_char_automaton_0_eq_aut16"
begin

lemma transition_eq: "Automata.transition(append_ch aut2 C0) = Automata.transition aut2_append_char_automaton_0"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut2 C0) x c = aut2_append_char_automaton_0.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut2 C0) x c = aut2_append_char_automaton_0.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut2_def)
        apply (cases rule:aut2_append_char_automaton_0_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut2_def)
        apply (cases rule:aut2_append_char_automaton_0_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut2_append_char_automaton_0_def)
qed

lemma append_ch_eq:"append_ch aut2 C0 = aut2_append_char_automaton_0"
  using transition_eq apply (simp only:aut2_def aut2_append_char_automaton_0_def) by auto

lemma "aut2_append_ch_0": "lang (append_ch aut2 C0) = lang aut16"
  using aut2_append_char_automaton_0_eq_aut16 append_ch_eq by simp
end