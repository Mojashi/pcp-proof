theory aut9_contains_aut1_append_char_automaton_0 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut9" "aut1_append_char_automaton_0" "PCPLib.AutomataUtil" begin

definition aut9_aut1_append_char_automaton_0_Intersection::"(PCP.alphabet,(aut9.State\<times>aut1_append_char_automaton_0.State)) da" where
  "aut9_aut1_append_char_automaton_0_Intersection \<equiv> intersect (complement aut9) aut1_append_char_automaton_0" 
definition aut9_aut1_append_char_automaton_0_Invariant::"(aut9.State\<times>aut1_append_char_automaton_0.State) set" where
  "aut9_aut1_append_char_automaton_0_Invariant \<equiv> { ((aut9.State_L aut9.state_level1_Leaf), (state_r (aut1.State_L (aut1.state_level1_R aut1.state_level2_Leaf)))), ((aut9.State_L aut9.state_level1_Leaf), (state_r (aut1.State_R (aut1.state_level1_L aut1.state_level2_Leaf)))), ((aut9.State_R aut9.state_level1_Leaf), (state_l (aut1.State_L (aut1.state_level1_R aut1.state_level2_Leaf)))), ((aut9.State_R aut9.state_level1_Leaf), (state_r (aut1.State_R (aut1.state_level1_R aut1.state_level2_Leaf)))), (aut9.State_Leaf, (state_l (aut1.State_R (aut1.state_level1_R aut1.state_level2_Leaf)))), ((aut9.State_L aut9.state_level1_Leaf), (state_r (aut1.State_L aut1.state_level1_Leaf))), ((aut9.State_R aut9.state_level1_Leaf), (state_l aut1.State_Leaf)), ((aut9.State_L aut9.state_level1_Leaf), (state_r aut1.State_Leaf)), ((aut9.State_R aut9.state_level1_Leaf), (state_l (aut1.State_R (aut1.state_level1_L aut1.state_level2_Leaf)))), ((aut9.State_L aut9.state_level1_Leaf), (state_r (aut1.State_L (aut1.state_level1_L aut1.state_level2_Leaf)))), ((aut9.State_R aut9.state_level1_Leaf), (state_l (aut1.State_L aut1.state_level1_Leaf))), ((aut9.State_L aut9.state_level1_Leaf), (state_r (aut1.State_R aut1.state_level1_Leaf))) }"

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

lemma INV:"inv aut9_aut1_append_char_automaton_0_Intersection aut9_aut1_append_char_automaton_0_Invariant" 
proof -
  have CLOSED:"step_state_set aut9_aut1_append_char_automaton_0_Intersection aut9_aut1_append_char_automaton_0_Invariant \<subseteq> aut9_aut1_append_char_automaton_0_Invariant"
   by (simp only: aut9_aut1_append_char_automaton_0_Intersection_def step_complement, simp only: inv_covered aut9_aut1_append_char_automaton_0_Invariant_def, simp add: intersect_def aut9_def aut1_append_char_automaton_0_def)
  
  have INIT:"initial aut9_aut1_append_char_automaton_0_Intersection \<in> aut9_aut1_append_char_automaton_0_Invariant"
    apply (simp add: aut9_aut1_append_char_automaton_0_Invariant_def aut9_aut1_append_char_automaton_0_Intersection_def aut9_def aut1_append_char_automaton_0_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut9_aut1_append_char_automaton_0_Intersection)\<inter>aut9_aut1_append_char_automaton_0_Invariant = {}"
  proof (simp add:aut9_aut1_append_char_automaton_0_Invariant_def aut9_def aut1_append_char_automaton_0_def intersect_def aut9_aut1_append_char_automaton_0_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut9_aut1_append_char_automaton_0_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut9_contains_aut1_append_char_automaton_0_rev:"(lang_rev aut1_append_char_automaton_0) \<subseteq> (lang_rev aut9)" 
  using INV INT_LANG_REV_EMPTY aut9_aut1_append_char_automaton_0_Intersection_def comp_intersect_emp_then_includes[of aut9 aut1_append_char_automaton_0]
  by auto

theorem aut9_contains_aut1_append_char_automaton_0:"(lang aut1_append_char_automaton_0) \<subseteq> (lang aut9)" 
  using aut9_contains_aut1_append_char_automaton_0_rev by auto

end
