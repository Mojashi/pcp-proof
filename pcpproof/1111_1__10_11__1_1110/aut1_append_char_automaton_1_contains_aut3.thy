theory aut1_append_char_automaton_1_contains_aut3 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut1_append_char_automaton_1" "aut3" "PCPLib.AutomataUtil" begin

definition aut1_append_char_automaton_1_aut3_Intersection::"(PCP.alphabet,(aut1_append_char_automaton_1.State\<times>aut3.State)) da" where
  "aut1_append_char_automaton_1_aut3_Intersection \<equiv> intersect (complement aut1_append_char_automaton_1) aut3" 
definition aut1_append_char_automaton_1_aut3_Invariant::"(aut1_append_char_automaton_1.State\<times>aut3.State) set" where
  "aut1_append_char_automaton_1_aut3_Invariant \<equiv> { ((state_l (aut1.State_R (aut1.state_level1_L aut1.state_level2_Leaf))), aut3.State_Leaf), ((state_r (aut1.State_R aut1.state_level1_Leaf)), aut3.State_Leaf), ((state_r (aut1.State_R (aut1.state_level1_R aut1.state_level2_Leaf))), (aut3.State_R aut3.state_level1_Leaf)), ((state_l (aut1.State_L (aut1.state_level1_L aut1.state_level2_Leaf))), aut3.State_Leaf), ((state_r (aut1.State_L (aut1.state_level1_L aut1.state_level2_Leaf))), (aut3.State_R aut3.state_level1_Leaf)), ((state_r (aut1.State_L aut1.state_level1_Leaf)), (aut3.State_R aut3.state_level1_Leaf)), ((state_l (aut1.State_R aut1.state_level1_Leaf)), (aut3.State_L aut3.state_level1_Leaf)), ((state_r (aut1.State_L (aut1.state_level1_R aut1.state_level2_Leaf))), (aut3.State_R aut3.state_level1_Leaf)), ((state_r (aut1.State_R (aut1.state_level1_L aut1.state_level2_Leaf))), (aut3.State_R aut3.state_level1_Leaf)) }"

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

lemma INV:"inv aut1_append_char_automaton_1_aut3_Intersection aut1_append_char_automaton_1_aut3_Invariant" 
proof -
  have CLOSED:"step_state_set aut1_append_char_automaton_1_aut3_Intersection aut1_append_char_automaton_1_aut3_Invariant \<subseteq> aut1_append_char_automaton_1_aut3_Invariant"
   by (simp only: aut1_append_char_automaton_1_aut3_Intersection_def step_complement, simp only: inv_covered aut1_append_char_automaton_1_aut3_Invariant_def, simp add: intersect_def aut1_append_char_automaton_1_def aut3_def)
  
  have INIT:"initial aut1_append_char_automaton_1_aut3_Intersection \<in> aut1_append_char_automaton_1_aut3_Invariant"
    apply (simp add: aut1_append_char_automaton_1_aut3_Invariant_def aut1_append_char_automaton_1_aut3_Intersection_def aut1_append_char_automaton_1_def aut3_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut1_append_char_automaton_1_aut3_Intersection)\<inter>aut1_append_char_automaton_1_aut3_Invariant = {}"
  proof (simp add:aut1_append_char_automaton_1_aut3_Invariant_def aut1_append_char_automaton_1_def aut3_def intersect_def aut1_append_char_automaton_1_aut3_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut1_append_char_automaton_1_aut3_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut1_append_char_automaton_1_contains_aut3_rev:"(lang_rev aut3) \<subseteq> (lang_rev aut1_append_char_automaton_1)" 
  using INV INT_LANG_REV_EMPTY aut1_append_char_automaton_1_aut3_Intersection_def comp_intersect_emp_then_includes[of aut1_append_char_automaton_1 aut3]
  by auto

theorem aut1_append_char_automaton_1_contains_aut3:"(lang aut3) \<subseteq> (lang aut1_append_char_automaton_1)" 
  using aut1_append_char_automaton_1_contains_aut3_rev by auto

end
