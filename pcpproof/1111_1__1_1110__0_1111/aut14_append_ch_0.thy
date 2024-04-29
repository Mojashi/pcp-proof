theory aut14_append_ch_0 
  imports Main "aut14" "aut15" "aut14_append_char_automaton_0" "aut14_append_char_automaton_0_eq_aut15"
begin

lemma transition_eq: "Automata.transition(append_ch aut14 C0) = Automata.transition aut14_append_char_automaton_0"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut14 C0) x c = aut14_append_char_automaton_0.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut14 C0) x c = aut14_append_char_automaton_0.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut14_def)
        apply (cases rule:aut14_append_char_automaton_0_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut14_def)
        apply (cases rule:aut14_append_char_automaton_0_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut14_append_char_automaton_0_def)
qed

lemma append_ch_eq:"append_ch aut14 C0 = aut14_append_char_automaton_0"
  using transition_eq apply (simp only:aut14_def aut14_append_char_automaton_0_def) by auto

lemma "aut14_append_ch_0": "lang (append_ch aut14 C0) = lang aut15"
  using aut14_append_char_automaton_0_eq_aut15 append_ch_eq by simp
end