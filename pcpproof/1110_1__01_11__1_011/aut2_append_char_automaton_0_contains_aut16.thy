theory aut2_append_char_automaton_0_contains_aut16 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut2_append_char_automaton_0" "aut16" "PCPLib.AutomataUtil" begin

definition aut2_append_char_automaton_0_aut16_Intersection::"(PCP.alphabet,(aut2_append_char_automaton_0.State\<times>aut16.State)) da" where
  "aut2_append_char_automaton_0_aut16_Intersection \<equiv> intersect (complement aut2_append_char_automaton_0) aut16" 
definition aut2_append_char_automaton_0_aut16_Invariant::"(aut2_append_char_automaton_0.State\<times>aut16.State) set" where
  "aut2_append_char_automaton_0_aut16_Invariant \<equiv> { ((state_r (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))), (aut16.State_L aut16.state_level1_Leaf)), ((state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))), aut16.State_Leaf), ((state_l (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))), (aut16.State_L aut16.state_level1_Leaf)), ((state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))), (aut16.State_L aut16.state_level1_Leaf)), ((state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))), (aut16.State_R aut16.state_level1_Leaf)), ((state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))), (aut16.State_R aut16.state_level1_Leaf)) }"

lemma "step_state_set a s = Set.bind s (step_state_set' a)"
  apply auto
    apply (metis alphabet.exhaust)
   apply blast
  by blast

definition covered :: "['a \<Rightarrow> 'a set, 'a set, 'a set] \<Rightarrow> bool" where
"covered f A S \<equiv> (\<forall>x \<in> A. f x \<subseteq> S)"

lemma [simp]: "covered f (insert x A) S =
       ((f x \<subseteq> S) \<and> covered f A S)"
  by (simp add: covered_def)

lemma [simp]: "covered f {} S"
  by (simp add: covered_def)

lemma inv_covered: "(step_state_set a r \<subseteq> r) = covered (step_state_set' a) r r"
  apply auto
   apply (simp add: UN_subset_iff covered_def range_subsetD)
  by (metis (full_types) alphabet.exhaust covered_def insert_subset step_state_set'.elims)

lemma INV:"inv aut2_append_char_automaton_0_aut16_Intersection aut2_append_char_automaton_0_aut16_Invariant" 
proof -
  have CLOSED:"step_state_set aut2_append_char_automaton_0_aut16_Intersection aut2_append_char_automaton_0_aut16_Invariant \<subseteq> aut2_append_char_automaton_0_aut16_Invariant"
   by (simp only: aut2_append_char_automaton_0_aut16_Intersection_def step_complement, simp only: inv_covered aut2_append_char_automaton_0_aut16_Invariant_def, simp add: intersect_def aut2_append_char_automaton_0_def aut16_def)
  
  have INIT:"initial aut2_append_char_automaton_0_aut16_Intersection \<in> aut2_append_char_automaton_0_aut16_Invariant"
    apply (simp add: aut2_append_char_automaton_0_aut16_Invariant_def aut2_append_char_automaton_0_aut16_Intersection_def aut2_append_char_automaton_0_def aut16_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut2_append_char_automaton_0_aut16_Intersection)\<inter>aut2_append_char_automaton_0_aut16_Invariant = {}"
  proof (simp add:aut2_append_char_automaton_0_aut16_Invariant_def aut2_append_char_automaton_0_def aut16_def intersect_def aut2_append_char_automaton_0_aut16_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut2_append_char_automaton_0_aut16_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut2_append_char_automaton_0_contains_aut16_rev:"(lang_rev aut16) \<subseteq> (lang_rev aut2_append_char_automaton_0)" 
  using INV INT_LANG_REV_EMPTY aut2_append_char_automaton_0_aut16_Intersection_def comp_intersect_emp_then_includes[of aut2_append_char_automaton_0 aut16]
  by auto

theorem aut2_append_char_automaton_0_contains_aut16:"(lang aut16) \<subseteq> (lang aut2_append_char_automaton_0)" 
  using aut2_append_char_automaton_0_contains_aut16_rev by auto

end
