theory aut4_append_char_automaton_1_contains_aut5 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut4_append_char_automaton_1" "aut5" "PCPLib.AutomataUtil" begin

definition aut4_append_char_automaton_1_aut5_Intersection::"(PCP.alphabet,(aut4_append_char_automaton_1.State\<times>aut5.State)) da" where
  "aut4_append_char_automaton_1_aut5_Intersection \<equiv> intersect (complement aut4_append_char_automaton_1) aut5" 
definition aut4_append_char_automaton_1_aut5_Invariant::"(aut4_append_char_automaton_1.State\<times>aut5.State) set" where
  "aut4_append_char_automaton_1_aut5_Invariant \<equiv> { ((state_l (aut4.State_L (aut4.state_level1_L aut4.state_level2_Leaf))), (aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf))), ((state_l (aut4.State_R (aut4.state_level1_L aut4.state_level2_Leaf))), (aut5.State_R (aut5.state_level1_R aut5.state_level2_Leaf))), ((state_r (aut4.State_R (aut4.state_level1_R aut4.state_level2_Leaf))), aut5.State_Leaf), ((state_r (aut4.State_L (aut4.state_level1_R aut4.state_level2_Leaf))), (aut5.State_R (aut5.state_level1_L aut5.state_level2_Leaf))), ((state_r (aut4.State_R (aut4.state_level1_L aut4.state_level2_Leaf))), (aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf))), ((state_r (aut4.State_L (aut4.state_level1_L aut4.state_level2_Leaf))), (aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf))) }"

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

lemma INV:"inv aut4_append_char_automaton_1_aut5_Intersection aut4_append_char_automaton_1_aut5_Invariant" 
proof -
  have CLOSED:"step_state_set aut4_append_char_automaton_1_aut5_Intersection aut4_append_char_automaton_1_aut5_Invariant \<subseteq> aut4_append_char_automaton_1_aut5_Invariant"
   by (simp only: aut4_append_char_automaton_1_aut5_Intersection_def step_complement, simp only: inv_covered aut4_append_char_automaton_1_aut5_Invariant_def, simp add: intersect_def aut4_append_char_automaton_1_def aut5_def)
  
  have INIT:"initial aut4_append_char_automaton_1_aut5_Intersection \<in> aut4_append_char_automaton_1_aut5_Invariant"
    apply (simp add: aut4_append_char_automaton_1_aut5_Invariant_def aut4_append_char_automaton_1_aut5_Intersection_def aut4_append_char_automaton_1_def aut5_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut4_append_char_automaton_1_aut5_Intersection)\<inter>aut4_append_char_automaton_1_aut5_Invariant = {}"
  proof (simp add:aut4_append_char_automaton_1_aut5_Invariant_def aut4_append_char_automaton_1_def aut5_def intersect_def aut4_append_char_automaton_1_aut5_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut4_append_char_automaton_1_aut5_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut4_append_char_automaton_1_contains_aut5_rev:"(lang_rev aut5) \<subseteq> (lang_rev aut4_append_char_automaton_1)" 
  using INV INT_LANG_REV_EMPTY aut4_append_char_automaton_1_aut5_Intersection_def comp_intersect_emp_then_includes[of aut4_append_char_automaton_1 aut5]
  by auto

theorem aut4_append_char_automaton_1_contains_aut5:"(lang aut5) \<subseteq> (lang aut4_append_char_automaton_1)" 
  using aut4_append_char_automaton_1_contains_aut5_rev by auto

end
