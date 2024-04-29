theory aut16_contains_aut2_append_char_automaton_0 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut16" "aut2_append_char_automaton_0" "PCPLib.AutomataUtil" begin

definition aut16_aut2_append_char_automaton_0_Intersection::"(PCP.alphabet,(aut16.State\<times>aut2_append_char_automaton_0.State)) da" where
  "aut16_aut2_append_char_automaton_0_Intersection \<equiv> intersect (complement aut16) aut2_append_char_automaton_0" 
definition aut16_aut2_append_char_automaton_0_Invariant::"(aut16.State\<times>aut2_append_char_automaton_0.State) set" where
  "aut16_aut2_append_char_automaton_0_Invariant \<equiv> { ((aut16.State_R aut16.state_level1_Leaf), (state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))), ((aut16.State_R aut16.state_level1_Leaf), (state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))), ((aut16.State_L aut16.state_level1_Leaf), (state_r (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)))), ((aut16.State_L aut16.state_level1_Leaf), (state_l (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)))), ((aut16.State_L aut16.state_level1_Leaf), (state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))), (aut16.State_Leaf, (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))) }"

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

lemma INV:"inv aut16_aut2_append_char_automaton_0_Intersection aut16_aut2_append_char_automaton_0_Invariant" 
proof -
  have CLOSED:"step_state_set aut16_aut2_append_char_automaton_0_Intersection aut16_aut2_append_char_automaton_0_Invariant \<subseteq> aut16_aut2_append_char_automaton_0_Invariant"
   by (simp only: aut16_aut2_append_char_automaton_0_Intersection_def step_complement, simp only: inv_covered aut16_aut2_append_char_automaton_0_Invariant_def, simp add: intersect_def aut16_def aut2_append_char_automaton_0_def)
  
  have INIT:"initial aut16_aut2_append_char_automaton_0_Intersection \<in> aut16_aut2_append_char_automaton_0_Invariant"
    apply (simp add: aut16_aut2_append_char_automaton_0_Invariant_def aut16_aut2_append_char_automaton_0_Intersection_def aut16_def aut2_append_char_automaton_0_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut16_aut2_append_char_automaton_0_Intersection)\<inter>aut16_aut2_append_char_automaton_0_Invariant = {}"
  proof (simp add:aut16_aut2_append_char_automaton_0_Invariant_def aut16_def aut2_append_char_automaton_0_def intersect_def aut16_aut2_append_char_automaton_0_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut16_aut2_append_char_automaton_0_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut16_contains_aut2_append_char_automaton_0_rev:"(lang_rev aut2_append_char_automaton_0) \<subseteq> (lang_rev aut16)" 
  using INV INT_LANG_REV_EMPTY aut16_aut2_append_char_automaton_0_Intersection_def comp_intersect_emp_then_includes[of aut16 aut2_append_char_automaton_0]
  by auto

theorem aut16_contains_aut2_append_char_automaton_0:"(lang aut2_append_char_automaton_0) \<subseteq> (lang aut16)" 
  using aut16_contains_aut2_append_char_automaton_0_rev by auto

end
