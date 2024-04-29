theory aut4_contains_aut3_append_char_automaton_1 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut4" "aut3_append_char_automaton_1" "PCPLib.AutomataUtil" begin

definition aut4_aut3_append_char_automaton_1_Intersection::"(PCP.alphabet,(aut4.State\<times>aut3_append_char_automaton_1.State)) da" where
  "aut4_aut3_append_char_automaton_1_Intersection \<equiv> intersect (complement aut4) aut3_append_char_automaton_1" 
definition aut4_aut3_append_char_automaton_1_Invariant::"(aut4.State\<times>aut3_append_char_automaton_1.State) set" where
  "aut4_aut3_append_char_automaton_1_Invariant \<equiv> { ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))), ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_R aut3.state_level1_Leaf))), ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))), ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))), ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))), ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))), ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))), ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))), ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf)))), ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)))), ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))), ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf)))), ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))), ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))), ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))), ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), (state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))), ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))), ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))), ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), (state_r (aut3.State_L aut3.state_level1_Leaf))) }"

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

lemma INV:"inv aut4_aut3_append_char_automaton_1_Intersection aut4_aut3_append_char_automaton_1_Invariant" 
proof -
  have CLOSED:"step_state_set aut4_aut3_append_char_automaton_1_Intersection aut4_aut3_append_char_automaton_1_Invariant \<subseteq> aut4_aut3_append_char_automaton_1_Invariant"
   by (simp only: aut4_aut3_append_char_automaton_1_Intersection_def step_complement, simp only: inv_covered aut4_aut3_append_char_automaton_1_Invariant_def, simp add: intersect_def aut4_def aut3_append_char_automaton_1_def)
  
  have INIT:"initial aut4_aut3_append_char_automaton_1_Intersection \<in> aut4_aut3_append_char_automaton_1_Invariant"
    apply (simp add: aut4_aut3_append_char_automaton_1_Invariant_def aut4_aut3_append_char_automaton_1_Intersection_def aut4_def aut3_append_char_automaton_1_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut4_aut3_append_char_automaton_1_Intersection)\<inter>aut4_aut3_append_char_automaton_1_Invariant = {}"
  proof (simp add:aut4_aut3_append_char_automaton_1_Invariant_def aut4_def aut3_append_char_automaton_1_def intersect_def aut4_aut3_append_char_automaton_1_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut4_aut3_append_char_automaton_1_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut4_contains_aut3_append_char_automaton_1_rev:"(lang_rev aut3_append_char_automaton_1) \<subseteq> (lang_rev aut4)" 
  using INV INT_LANG_REV_EMPTY aut4_aut3_append_char_automaton_1_Intersection_def comp_intersect_emp_then_includes[of aut4 aut3_append_char_automaton_1]
  by auto

theorem aut4_contains_aut3_append_char_automaton_1:"(lang aut3_append_char_automaton_1) \<subseteq> (lang aut4)" 
  using aut4_contains_aut3_append_char_automaton_1_rev by auto

end
