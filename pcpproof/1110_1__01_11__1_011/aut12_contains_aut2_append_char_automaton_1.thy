theory aut12_contains_aut2_append_char_automaton_1 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut12" "aut2_append_char_automaton_1" "PCPLib.AutomataUtil" begin

definition aut12_aut2_append_char_automaton_1_Intersection::"(PCP.alphabet,(aut12.State\<times>aut2_append_char_automaton_1.State)) da" where
  "aut12_aut2_append_char_automaton_1_Intersection \<equiv> intersect (complement aut12) aut2_append_char_automaton_1" 
definition aut12_aut2_append_char_automaton_1_Invariant::"(aut12.State\<times>aut2_append_char_automaton_1.State) set" where
  "aut12_aut2_append_char_automaton_1_Invariant \<equiv> { ((aut12.State_L aut12.state_level1_Leaf), (state_l (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))), ((aut12.State_R aut12.state_level1_Leaf), (state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))), ((aut12.State_L aut12.state_level1_Leaf), (state_l (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)))), ((aut12.State_R aut12.state_level1_Leaf), (state_r (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)))), ((aut12.State_R aut12.state_level1_Leaf), (state_l (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))), (aut12.State_Leaf, (state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))), (aut12.State_Leaf, (state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))) }"

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

lemma INV:"inv aut12_aut2_append_char_automaton_1_Intersection aut12_aut2_append_char_automaton_1_Invariant" 
proof -
  have CLOSED:"step_state_set aut12_aut2_append_char_automaton_1_Intersection aut12_aut2_append_char_automaton_1_Invariant \<subseteq> aut12_aut2_append_char_automaton_1_Invariant"
   by (simp only: aut12_aut2_append_char_automaton_1_Intersection_def step_complement, simp only: inv_covered aut12_aut2_append_char_automaton_1_Invariant_def, simp add: intersect_def aut12_def aut2_append_char_automaton_1_def)
  
  have INIT:"initial aut12_aut2_append_char_automaton_1_Intersection \<in> aut12_aut2_append_char_automaton_1_Invariant"
    apply (simp add: aut12_aut2_append_char_automaton_1_Invariant_def aut12_aut2_append_char_automaton_1_Intersection_def aut12_def aut2_append_char_automaton_1_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut12_aut2_append_char_automaton_1_Intersection)\<inter>aut12_aut2_append_char_automaton_1_Invariant = {}"
  proof (simp add:aut12_aut2_append_char_automaton_1_Invariant_def aut12_def aut2_append_char_automaton_1_def intersect_def aut12_aut2_append_char_automaton_1_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut12_aut2_append_char_automaton_1_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut12_contains_aut2_append_char_automaton_1_rev:"(lang_rev aut2_append_char_automaton_1) \<subseteq> (lang_rev aut12)" 
  using INV INT_LANG_REV_EMPTY aut12_aut2_append_char_automaton_1_Intersection_def comp_intersect_emp_then_includes[of aut12 aut2_append_char_automaton_1]
  by auto

theorem aut12_contains_aut2_append_char_automaton_1:"(lang aut2_append_char_automaton_1) \<subseteq> (lang aut12)" 
  using aut12_contains_aut2_append_char_automaton_1_rev by auto

end
