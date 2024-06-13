theory aut3_append_char_automaton_0_contains_aut8 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut3_append_char_automaton_0" "aut8" "PCPLib.AutomataUtil" begin

definition aut3_append_char_automaton_0_aut8_Intersection::"(PCP.alphabet,(aut3_append_char_automaton_0.State\<times>aut8.State)) da" where
  "aut3_append_char_automaton_0_aut8_Intersection \<equiv> intersect (complement aut3_append_char_automaton_0) aut8" 
definition aut3_append_char_automaton_0_aut8_Invariant::"(aut3_append_char_automaton_0.State\<times>aut8.State) set" where
  "aut3_append_char_automaton_0_aut8_Invariant \<equiv> { ((state_r (aut3.State_L aut3.state_level1_Leaf)), (aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf))), ((state_r (aut3.State_R aut3.state_level1_Leaf)), (aut8.State_R (aut8.state_level1_R aut8.state_level2_Leaf))), ((state_r aut3.State_Leaf), (aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf))), ((state_l (aut3.State_L aut3.state_level1_Leaf)), (aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))), ((state_l aut3.State_Leaf), (aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf))), ((state_l (aut3.State_R aut3.state_level1_Leaf)), (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf))) }"

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

lemma INV:"inv aut3_append_char_automaton_0_aut8_Intersection aut3_append_char_automaton_0_aut8_Invariant" 
proof -
  have CLOSED:"step_state_set aut3_append_char_automaton_0_aut8_Intersection aut3_append_char_automaton_0_aut8_Invariant \<subseteq> aut3_append_char_automaton_0_aut8_Invariant"
   by (simp only: aut3_append_char_automaton_0_aut8_Intersection_def step_complement, simp only: inv_covered aut3_append_char_automaton_0_aut8_Invariant_def, simp add: intersect_def aut3_append_char_automaton_0_def aut8_def)
  
  have INIT:"initial aut3_append_char_automaton_0_aut8_Intersection \<in> aut3_append_char_automaton_0_aut8_Invariant"
    apply (simp add: aut3_append_char_automaton_0_aut8_Invariant_def aut3_append_char_automaton_0_aut8_Intersection_def aut3_append_char_automaton_0_def aut8_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut3_append_char_automaton_0_aut8_Intersection)\<inter>aut3_append_char_automaton_0_aut8_Invariant = {}"
  proof (simp add:aut3_append_char_automaton_0_aut8_Invariant_def aut3_append_char_automaton_0_def aut8_def intersect_def aut3_append_char_automaton_0_aut8_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut3_append_char_automaton_0_aut8_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut3_append_char_automaton_0_contains_aut8_rev:"(lang_rev aut8) \<subseteq> (lang_rev aut3_append_char_automaton_0)" 
  using INV INT_LANG_REV_EMPTY aut3_append_char_automaton_0_aut8_Intersection_def comp_intersect_emp_then_includes[of aut3_append_char_automaton_0 aut8]
  by auto

theorem aut3_append_char_automaton_0_contains_aut8:"(lang aut8) \<subseteq> (lang aut3_append_char_automaton_0)" 
  using aut3_append_char_automaton_0_contains_aut8_rev by auto

end
