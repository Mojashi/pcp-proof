theory aut4_append_ch_1 
  imports Main "aut4" "aut5" "aut4_append_char_automaton_1" "aut4_append_char_automaton_1_eq_aut5"
begin

lemma transition_eq: "Automata.transition(append_ch aut4 C1) = Automata.transition aut4_append_char_automaton_1"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut4 C1) x c = aut4_append_char_automaton_1.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut4 C1) x c = aut4_append_char_automaton_1.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut4_def)
        apply (cases rule:aut4_append_char_automaton_1_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut4_def)
        apply (cases rule:aut4_append_char_automaton_1_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut4_append_char_automaton_1_def)
qed

lemma append_ch_eq:"append_ch aut4 C1 = aut4_append_char_automaton_1"
  using transition_eq apply (simp only:aut4_def aut4_append_char_automaton_1_def) by auto

lemma "aut4_append_ch_1": "lang (append_ch aut4 C1) = lang aut5"
  using aut4_append_char_automaton_1_eq_aut5 append_ch_eq by simp
end