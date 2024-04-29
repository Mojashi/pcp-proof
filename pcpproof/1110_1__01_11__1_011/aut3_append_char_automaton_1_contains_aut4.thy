theory aut3_append_char_automaton_1_contains_aut4 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut3_append_char_automaton_1" "aut4" "PCPLib.AutomataUtil" begin

definition aut3_append_char_automaton_1_aut4_Intersection::"(PCP.alphabet,(aut3_append_char_automaton_1.State\<times>aut4.State)) da" where
  "aut3_append_char_automaton_1_aut4_Intersection \<equiv> intersect (complement aut3_append_char_automaton_1) aut4" 
definition aut3_append_char_automaton_1_aut4_Invariant::"(aut3_append_char_automaton_1.State\<times>aut4.State) set" where
  "aut3_append_char_automaton_1_aut4_Invariant \<equiv> { ((state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf))), (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_r (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf))), (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf))), (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_R aut3.state_level1_Leaf)), (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf))), (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_L aut3.state_level1_Leaf)), (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), ((state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), ((state_r (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf))), (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))) }"

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

lemma INV:"inv aut3_append_char_automaton_1_aut4_Intersection aut3_append_char_automaton_1_aut4_Invariant" 
proof -
  have CLOSED:"step_state_set aut3_append_char_automaton_1_aut4_Intersection aut3_append_char_automaton_1_aut4_Invariant \<subseteq> aut3_append_char_automaton_1_aut4_Invariant"
   by (simp only: aut3_append_char_automaton_1_aut4_Intersection_def step_complement, simp only: inv_covered aut3_append_char_automaton_1_aut4_Invariant_def, simp add: intersect_def aut3_append_char_automaton_1_def aut4_def)
  
  have INIT:"initial aut3_append_char_automaton_1_aut4_Intersection \<in> aut3_append_char_automaton_1_aut4_Invariant"
    apply (simp add: aut3_append_char_automaton_1_aut4_Invariant_def aut3_append_char_automaton_1_aut4_Intersection_def aut3_append_char_automaton_1_def aut4_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut3_append_char_automaton_1_aut4_Intersection)\<inter>aut3_append_char_automaton_1_aut4_Invariant = {}"
  proof (simp add:aut3_append_char_automaton_1_aut4_Invariant_def aut3_append_char_automaton_1_def aut4_def intersect_def aut3_append_char_automaton_1_aut4_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut3_append_char_automaton_1_aut4_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut3_append_char_automaton_1_contains_aut4_rev:"(lang_rev aut4) \<subseteq> (lang_rev aut3_append_char_automaton_1)" 
  using INV INT_LANG_REV_EMPTY aut3_append_char_automaton_1_aut4_Intersection_def comp_intersect_emp_then_includes[of aut3_append_char_automaton_1 aut4]
  by auto

theorem aut3_append_char_automaton_1_contains_aut4:"(lang aut4) \<subseteq> (lang aut3_append_char_automaton_1)" 
  using aut3_append_char_automaton_1_contains_aut4_rev by auto

end
