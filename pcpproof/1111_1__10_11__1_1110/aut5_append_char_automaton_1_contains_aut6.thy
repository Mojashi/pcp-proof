theory aut5_append_char_automaton_1_contains_aut6 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut5_append_char_automaton_1" "aut6" "PCPLib.AutomataUtil" begin

definition aut5_append_char_automaton_1_aut6_Intersection::"(PCP.alphabet,(aut5_append_char_automaton_1.State\<times>aut6.State)) da" where
  "aut5_append_char_automaton_1_aut6_Intersection \<equiv> intersect (complement aut5_append_char_automaton_1) aut6" 
definition aut5_append_char_automaton_1_aut6_Invariant::"(aut5_append_char_automaton_1.State\<times>aut6.State) set" where
  "aut5_append_char_automaton_1_aut6_Invariant \<equiv> { ((state_l aut5.State_Leaf), (aut6.State_L aut6.state_level1_Leaf)), ((state_r (aut5.State_R (aut5.state_level1_L aut5.state_level2_Leaf))), (aut6.State_L (aut6.state_level1_L aut6.state_level2_Leaf))), ((state_r (aut5.State_R (aut5.state_level1_R aut5.state_level2_Leaf))), (aut6.State_R (aut6.state_level1_R aut6.state_level2_Leaf))), ((state_r aut5.State_Leaf), (aut6.State_R aut6.state_level1_Leaf)), ((state_r (aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf))), (aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf))), ((state_r (aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf))), (aut6.State_L aut6.state_level1_Leaf)), ((state_l (aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf))), (aut6.State_R (aut6.state_level1_L aut6.state_level2_Leaf))) }"

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

lemma INV:"inv aut5_append_char_automaton_1_aut6_Intersection aut5_append_char_automaton_1_aut6_Invariant" 
proof -
  have CLOSED:"step_state_set aut5_append_char_automaton_1_aut6_Intersection aut5_append_char_automaton_1_aut6_Invariant \<subseteq> aut5_append_char_automaton_1_aut6_Invariant"
   by (simp only: aut5_append_char_automaton_1_aut6_Intersection_def step_complement, simp only: inv_covered aut5_append_char_automaton_1_aut6_Invariant_def, simp add: intersect_def aut5_append_char_automaton_1_def aut6_def)
  
  have INIT:"initial aut5_append_char_automaton_1_aut6_Intersection \<in> aut5_append_char_automaton_1_aut6_Invariant"
    apply (simp add: aut5_append_char_automaton_1_aut6_Invariant_def aut5_append_char_automaton_1_aut6_Intersection_def aut5_append_char_automaton_1_def aut6_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut5_append_char_automaton_1_aut6_Intersection)\<inter>aut5_append_char_automaton_1_aut6_Invariant = {}"
  proof (simp add:aut5_append_char_automaton_1_aut6_Invariant_def aut5_append_char_automaton_1_def aut6_def intersect_def aut5_append_char_automaton_1_aut6_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut5_append_char_automaton_1_aut6_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut5_append_char_automaton_1_contains_aut6_rev:"(lang_rev aut6) \<subseteq> (lang_rev aut5_append_char_automaton_1)" 
  using INV INT_LANG_REV_EMPTY aut5_append_char_automaton_1_aut6_Intersection_def comp_intersect_emp_then_includes[of aut5_append_char_automaton_1 aut6]
  by auto

theorem aut5_append_char_automaton_1_contains_aut6:"(lang aut6) \<subseteq> (lang aut5_append_char_automaton_1)" 
  using aut5_append_char_automaton_1_contains_aut6_rev by auto

end
