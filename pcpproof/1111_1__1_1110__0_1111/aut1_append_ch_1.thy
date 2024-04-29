theory aut1_append_ch_1 
  imports Main "aut1" "aut3" "aut1_append_char_automaton_1" "aut1_append_char_automaton_1_eq_aut3"
begin

lemma transition_eq: "Automata.transition(append_ch aut1 C1) = Automata.transition aut1_append_char_automaton_1"
proof -
  have "\<forall>x c. Automata.transition(append_ch aut1 C1) x c = aut1_append_char_automaton_1.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch aut1 C1) x c = aut1_append_char_automaton_1.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: aut1_def)
        apply (cases rule:aut1_append_char_automaton_1_state_split[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: aut1_def)
        apply (cases rule:aut1_append_char_automaton_1_state_split[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:aut1_append_char_automaton_1_def)
qed

lemma append_ch_eq:"append_ch aut1 C1 = aut1_append_char_automaton_1"
  using transition_eq apply (simp only:aut1_def aut1_append_char_automaton_1_def) by auto

lemma "aut1_append_ch_1": "lang (append_ch aut1 C1) = lang aut3"
  using aut1_append_char_automaton_1_eq_aut3 append_ch_eq by simp
end