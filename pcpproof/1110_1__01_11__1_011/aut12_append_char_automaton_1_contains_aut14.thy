theory aut12_append_char_automaton_1_contains_aut14 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut12_append_char_automaton_1" "aut14" "PCPLib.AutomataUtil" begin

definition aut12_append_char_automaton_1_aut14_Intersection::"(PCP.alphabet,(aut12_append_char_automaton_1.State\<times>aut14.State)) da" where
  "aut12_append_char_automaton_1_aut14_Intersection \<equiv> intersect (complement aut12_append_char_automaton_1) aut14" 
definition aut12_append_char_automaton_1_aut14_Invariant::"(aut12_append_char_automaton_1.State\<times>aut14.State) set" where
  "aut12_append_char_automaton_1_aut14_Invariant \<equiv> { ((state_l (aut12.State_L aut12.state_level1_Leaf)), (aut14.State_L (aut14.state_level1_L aut14.state_level2_Leaf))), ((state_r (aut12.State_L aut12.state_level1_Leaf)), (aut14.State_R (aut14.state_level1_L aut14.state_level2_Leaf))), ((state_r (aut12.State_R aut12.state_level1_Leaf)), (aut14.State_L (aut14.state_level1_R aut14.state_level2_Leaf))), ((state_r aut12.State_Leaf), (aut14.State_R (aut14.state_level1_R aut14.state_level2_Leaf))), ((state_l (aut12.State_R aut12.state_level1_Leaf)), (aut14.State_R (aut14.state_level1_L aut14.state_level2_Leaf))) }"

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

lemma INV:"inv aut12_append_char_automaton_1_aut14_Intersection aut12_append_char_automaton_1_aut14_Invariant" 
proof -
  have CLOSED:"step_state_set aut12_append_char_automaton_1_aut14_Intersection aut12_append_char_automaton_1_aut14_Invariant \<subseteq> aut12_append_char_automaton_1_aut14_Invariant"
   by (simp only: aut12_append_char_automaton_1_aut14_Intersection_def step_complement, simp only: inv_covered aut12_append_char_automaton_1_aut14_Invariant_def, simp add: intersect_def aut12_append_char_automaton_1_def aut14_def)
  
  have INIT:"initial aut12_append_char_automaton_1_aut14_Intersection \<in> aut12_append_char_automaton_1_aut14_Invariant"
    apply (simp add: aut12_append_char_automaton_1_aut14_Invariant_def aut12_append_char_automaton_1_aut14_Intersection_def aut12_append_char_automaton_1_def aut14_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut12_append_char_automaton_1_aut14_Intersection)\<inter>aut12_append_char_automaton_1_aut14_Invariant = {}"
  proof (simp add:aut12_append_char_automaton_1_aut14_Invariant_def aut12_append_char_automaton_1_def aut14_def intersect_def aut12_append_char_automaton_1_aut14_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut12_append_char_automaton_1_aut14_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut12_append_char_automaton_1_contains_aut14_rev:"(lang_rev aut14) \<subseteq> (lang_rev aut12_append_char_automaton_1)" 
  using INV INT_LANG_REV_EMPTY aut12_append_char_automaton_1_aut14_Intersection_def comp_intersect_emp_then_includes[of aut12_append_char_automaton_1 aut14]
  by auto

theorem aut12_append_char_automaton_1_contains_aut14:"(lang aut14) \<subseteq> (lang aut12_append_char_automaton_1)" 
  using aut12_append_char_automaton_1_contains_aut14_rev by auto

end
