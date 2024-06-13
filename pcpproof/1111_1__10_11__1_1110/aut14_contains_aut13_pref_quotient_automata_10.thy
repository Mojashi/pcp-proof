theory aut14_contains_aut13_pref_quotient_automata_10 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut14" "aut13_pref_quotient_automata_10" "PCPLib.AutomataUtil" begin

definition aut14_aut13_pref_quotient_automata_10_Intersection::"(PCP.alphabet,(aut14.State\<times>aut13_pref_quotient_automata_10.State)) da" where
  "aut14_aut13_pref_quotient_automata_10_Intersection \<equiv> intersect (complement aut14) aut13_pref_quotient_automata_10" 
definition aut14_aut13_pref_quotient_automata_10_Invariant::"(aut14.State\<times>aut13_pref_quotient_automata_10.State) set" where
  "aut14_aut13_pref_quotient_automata_10_Invariant \<equiv> { ((aut14.State_L (aut14.state_level1_L (aut14.state_level2_L aut14.state_level3_Leaf))), (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R aut13.state_level4_Leaf))))), ((aut14.State_L (aut14.state_level1_R (aut14.state_level2_R aut14.state_level3_Leaf))), (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L aut13.state_level4_Leaf))))), ((aut14.State_R (aut14.state_level1_L (aut14.state_level2_L aut14.state_level3_Leaf))), (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))), ((aut14.State_L (aut14.state_level1_R (aut14.state_level2_L aut14.state_level3_Leaf))), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L aut13.state_level4_Leaf))))), ((aut14.State_R (aut14.state_level1_L (aut14.state_level2_R aut14.state_level3_Leaf))), (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L aut13.state_level4_Leaf))))), ((aut14.State_R (aut14.state_level1_R (aut14.state_level2_L aut14.state_level3_Leaf))), (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf)))), ((aut14.State_L (aut14.state_level1_R aut14.state_level2_Leaf)), (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))), ((aut14.State_R (aut14.state_level1_R (aut14.state_level2_R aut14.state_level3_Leaf))), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R aut13.state_level4_Leaf))))), ((aut14.State_R (aut14.state_level1_L aut14.state_level2_Leaf)), (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf)))), ((aut14.State_L (aut14.state_level1_L aut14.state_level2_Leaf)), (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf)))), ((aut14.State_L (aut14.state_level1_L (aut14.state_level2_R aut14.state_level3_Leaf))), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L aut13.state_level4_Leaf))))), ((aut14.State_R (aut14.state_level1_R aut14.state_level2_Leaf)), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf)))) }"

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

lemma INV:"inv aut14_aut13_pref_quotient_automata_10_Intersection aut14_aut13_pref_quotient_automata_10_Invariant" 
proof -
  have CLOSED:"step_state_set aut14_aut13_pref_quotient_automata_10_Intersection aut14_aut13_pref_quotient_automata_10_Invariant \<subseteq> aut14_aut13_pref_quotient_automata_10_Invariant"
   by (simp only: aut14_aut13_pref_quotient_automata_10_Intersection_def step_complement, simp only: inv_covered aut14_aut13_pref_quotient_automata_10_Invariant_def, simp add: intersect_def aut14_def aut13_pref_quotient_automata_10_def)
  
  have INIT:"initial aut14_aut13_pref_quotient_automata_10_Intersection \<in> aut14_aut13_pref_quotient_automata_10_Invariant"
    apply (simp add: aut14_aut13_pref_quotient_automata_10_Invariant_def aut14_aut13_pref_quotient_automata_10_Intersection_def aut14_def aut13_pref_quotient_automata_10_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut14_aut13_pref_quotient_automata_10_Intersection)\<inter>aut14_aut13_pref_quotient_automata_10_Invariant = {}"
  proof (simp add:aut14_aut13_pref_quotient_automata_10_Invariant_def aut14_def aut13_pref_quotient_automata_10_def intersect_def aut14_aut13_pref_quotient_automata_10_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut14_aut13_pref_quotient_automata_10_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut14_contains_aut13_pref_quotient_automata_10_rev:"(lang_rev aut13_pref_quotient_automata_10) \<subseteq> (lang_rev aut14)" 
  using INV INT_LANG_REV_EMPTY aut14_aut13_pref_quotient_automata_10_Intersection_def comp_intersect_emp_then_includes[of aut14 aut13_pref_quotient_automata_10]
  by auto

theorem aut14_contains_aut13_pref_quotient_automata_10:"(lang aut13_pref_quotient_automata_10) \<subseteq> (lang aut14)" 
  using aut14_contains_aut13_pref_quotient_automata_10_rev by auto

end
