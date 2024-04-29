theory aut3_append_ch_1 
  imports Main "aut3" "aut4" "aut3_append_char_automaton_1" "aut3_append_char_automaton_1_eq_aut4"
begin

lemma transition_eq: "Automata.transition(append_ch aut3 C1) = Automata.transition aut3_append_char_automaton_1"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut3 C1) x c = aut3_append_char_automaton_1.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut3 C1) x c = aut3_append_char_automaton_1.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut3_def)
        apply (cases rule:aut3_append_char_automaton_1_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut3_def)
        apply (cases rule:aut3_append_char_automaton_1_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut3_append_char_automaton_1_def)
qed

lemma append_ch_eq:"append_ch aut3 C1 = aut3_append_char_automaton_1"
  using transition_eq apply (simp only:aut3_def aut3_append_char_automaton_1_def) by auto

lemma "aut3_append_ch_1": "lang (append_ch aut3 C1) = lang aut4"
  using aut3_append_char_automaton_1_eq_aut4 append_ch_eq by simp
end