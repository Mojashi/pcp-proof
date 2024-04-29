theory aut12_append_ch_1 
  imports Main "aut12" "aut14" "aut12_append_char_automaton_1" "aut12_append_char_automaton_1_eq_aut14"
begin

lemma transition_eq: "Automata.transition(append_ch aut12 C1) = Automata.transition aut12_append_char_automaton_1"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut12 C1) x c = aut12_append_char_automaton_1.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut12 C1) x c = aut12_append_char_automaton_1.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut12_def)
        apply (cases rule:aut12_append_char_automaton_1_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut12_def)
        apply (cases rule:aut12_append_char_automaton_1_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut12_append_char_automaton_1_def)
qed

lemma append_ch_eq:"append_ch aut12 C1 = aut12_append_char_automaton_1"
  using transition_eq apply (simp only:aut12_def aut12_append_char_automaton_1_def) by auto

lemma "aut12_append_ch_1": "lang (append_ch aut12 C1) = lang aut14"
  using aut12_append_char_automaton_1_eq_aut14 append_ch_eq by simp
end