theory {{theory_name}} 
  imports Main "{{src_aut_path}}" "{{dest_aut_path}}" "{{mid_aut_path}}" "{{eq_lemma_path}}"
begin

lemma transition_eq: "Automata.transition(append_ch {{src_aut_name}} {{ch}}) = Automata.transition {{mid_aut_name}}"
proof -
  have "\<forall>x c. Automata.transition(append_ch {{src_aut_name}} {{ch}}) x c = {{mid_aut_name}}.transition x c"
  proof (rule allI, rule allI) 
    fix x
    fix c
    show " da.transition (append_ch {{src_aut_name}} {{ch}}) x c = {{mid_aut_name}}.transition x c "
    proof (cases c)
      case C0 then show ?thesis 
        apply (simp add: {{src_aut_name}}_def)
        apply (cases rule:{{mid_aut_state_split_lemma}}[of x])
        by simp_all
    next
      case C1 then show ?thesis 
        apply (simp add: {{src_aut_name}}_def)
        apply (cases rule:{{mid_aut_state_split_lemma}}[of x])
        by simp_all
    qed
qed
then show ?thesis by (simp add:{{mid_aut_name}}_def)
qed

lemma append_ch_eq:"append_ch {{src_aut_name}} {{ch}} = {{mid_aut_name}}"
  using transition_eq apply (simp only:{{src_aut_name}}_def {{mid_aut_name}}_def) by auto

lemma "{{theory_name}}": "lang (append_ch {{src_aut_name}} {{ch}}) = lang {{dest_aut_name}}"
  using {{eq_lemma_name}} append_ch_eq by simp
end