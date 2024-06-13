theory aut13_contains_aut11_append_char_automaton_1 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut13" "aut11_append_char_automaton_1" "PCPLib.AutomataUtil" begin

definition aut13_aut11_append_char_automaton_1_Intersection::"(PCP.alphabet,(aut13.State\<times>aut11_append_char_automaton_1.State)) da" where
  "aut13_aut11_append_char_automaton_1_Intersection \<equiv> intersect (complement aut13) aut11_append_char_automaton_1" 
definition aut13_aut11_append_char_automaton_1_Invariant::"(aut13.State\<times>aut11_append_char_automaton_1.State) set" where
  "aut13_aut11_append_char_automaton_1_Invariant \<equiv> { ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))), (state_r (aut11.State_R aut11.state_level1_Leaf))), ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf))), (state_r (aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf))), (state_l (aut11.State_R (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_l (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_l (aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf))), (state_r (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))), (state_r (aut11.State_L (aut11.state_level1_R aut11.state_level2_Leaf)))), ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf))), (state_r (aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_l (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_L aut11.state_level2_Leaf)))), ((aut13.State_L aut13.state_level1_Leaf), (state_r (aut11.State_L aut11.state_level1_Leaf))), ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf))), (state_r (aut11.State_L (aut11.state_level1_L aut11.state_level2_Leaf)))), ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf))), (state_l (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_L (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L aut13.state_level4_Leaf)))), (state_r (aut11.State_L (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_L aut11.state_level4_Leaf)))))), ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R aut13.state_level4_Leaf)))), (state_r (aut11.State_R (aut11.state_level1_R aut11.state_level2_Leaf)))), ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))), (state_l (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_R aut11.state_level4_Leaf)))))), ((aut13.State_R aut13.state_level1_Leaf), (state_r (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_R aut11.state_level4_Leaf)))))) }"

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

lemma INV:"inv aut13_aut11_append_char_automaton_1_Intersection aut13_aut11_append_char_automaton_1_Invariant" 
proof -
  have CLOSED:"step_state_set aut13_aut11_append_char_automaton_1_Intersection aut13_aut11_append_char_automaton_1_Invariant \<subseteq> aut13_aut11_append_char_automaton_1_Invariant"
   by (simp only: aut13_aut11_append_char_automaton_1_Intersection_def step_complement, simp only: inv_covered aut13_aut11_append_char_automaton_1_Invariant_def, simp add: intersect_def aut13_def aut11_append_char_automaton_1_def)
  
  have INIT:"initial aut13_aut11_append_char_automaton_1_Intersection \<in> aut13_aut11_append_char_automaton_1_Invariant"
    apply (simp add: aut13_aut11_append_char_automaton_1_Invariant_def aut13_aut11_append_char_automaton_1_Intersection_def aut13_def aut11_append_char_automaton_1_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut13_aut11_append_char_automaton_1_Intersection)\<inter>aut13_aut11_append_char_automaton_1_Invariant = {}"
  proof (simp add:aut13_aut11_append_char_automaton_1_Invariant_def aut13_def aut11_append_char_automaton_1_def intersect_def aut13_aut11_append_char_automaton_1_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut13_aut11_append_char_automaton_1_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut13_contains_aut11_append_char_automaton_1_rev:"(lang_rev aut11_append_char_automaton_1) \<subseteq> (lang_rev aut13)" 
  using INV INT_LANG_REV_EMPTY aut13_aut11_append_char_automaton_1_Intersection_def comp_intersect_emp_then_includes[of aut13 aut11_append_char_automaton_1]
  by auto

theorem aut13_contains_aut11_append_char_automaton_1:"(lang aut11_append_char_automaton_1) \<subseteq> (lang aut13)" 
  using aut13_contains_aut11_append_char_automaton_1_rev by auto

end
