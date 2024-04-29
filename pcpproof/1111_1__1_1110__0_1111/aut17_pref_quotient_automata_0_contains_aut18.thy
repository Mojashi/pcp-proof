theory aut17_pref_quotient_automata_0_contains_aut18 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut17_pref_quotient_automata_0" "aut18" "PCPLib.AutomataUtil" begin

definition aut17_pref_quotient_automata_0_aut18_Intersection::"(PCP.alphabet,(aut17_pref_quotient_automata_0.State\<times>aut18.State)) da" where
  "aut17_pref_quotient_automata_0_aut18_Intersection \<equiv> intersect (complement aut17_pref_quotient_automata_0) aut18" 
definition aut17_pref_quotient_automata_0_aut18_Invariant::"(aut17_pref_quotient_automata_0.State\<times>aut18.State) set" where
  "aut17_pref_quotient_automata_0_aut18_Invariant \<equiv> { ((aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf)), (aut18.State_R (aut18.state_level1_R aut18.state_level2_Leaf))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_L aut17.state_level5_Leaf))))), (aut18.State_R (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_L (aut17.state_level4_L aut17.state_level5_Leaf))))), (aut18.State_R (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf))))), ((aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)), (aut18.State_L (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_R (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf))))), ((aut17.State_L aut17.state_level1_Leaf), (aut18.State_R (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_L (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_R aut17.state_level1_Leaf), (aut18.State_L (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_R (aut18.state_level1_L aut18.state_level2_Leaf))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf))), (aut18.State_R (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_L aut17.state_level5_Leaf))))), (aut18.State_R (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_L (aut18.state_level1_R aut18.state_level2_Leaf))), (aut17.State_Leaf, (aut18.State_L (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf))), (aut18.State_R (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf))))), ((aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)), (aut18.State_L (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_L (aut18.state_level1_L aut18.state_level2_Leaf))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_R aut17.state_level3_Leaf))), (aut18.State_L (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_L (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_R (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_R (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut18.State_L (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf))))) }"

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

lemma INV:"inv aut17_pref_quotient_automata_0_aut18_Intersection aut17_pref_quotient_automata_0_aut18_Invariant" 
proof -
  have CLOSED:"step_state_set aut17_pref_quotient_automata_0_aut18_Intersection aut17_pref_quotient_automata_0_aut18_Invariant \<subseteq> aut17_pref_quotient_automata_0_aut18_Invariant"
   by (simp only: aut17_pref_quotient_automata_0_aut18_Intersection_def step_complement, simp only: inv_covered aut17_pref_quotient_automata_0_aut18_Invariant_def, simp add: intersect_def aut17_pref_quotient_automata_0_def aut18_def)
  
  have INIT:"initial aut17_pref_quotient_automata_0_aut18_Intersection \<in> aut17_pref_quotient_automata_0_aut18_Invariant"
    apply (simp add: aut17_pref_quotient_automata_0_aut18_Invariant_def aut17_pref_quotient_automata_0_aut18_Intersection_def aut17_pref_quotient_automata_0_def aut18_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut17_pref_quotient_automata_0_aut18_Intersection)\<inter>aut17_pref_quotient_automata_0_aut18_Invariant = {}"
  proof (simp add:aut17_pref_quotient_automata_0_aut18_Invariant_def aut17_pref_quotient_automata_0_def aut18_def intersect_def aut17_pref_quotient_automata_0_aut18_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut17_pref_quotient_automata_0_aut18_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut17_pref_quotient_automata_0_contains_aut18_rev:"(lang_rev aut18) \<subseteq> (lang_rev aut17_pref_quotient_automata_0)" 
  using INV INT_LANG_REV_EMPTY aut17_pref_quotient_automata_0_aut18_Intersection_def comp_intersect_emp_then_includes[of aut17_pref_quotient_automata_0 aut18]
  by auto

theorem aut17_pref_quotient_automata_0_contains_aut18:"(lang aut18) \<subseteq> (lang aut17_pref_quotient_automata_0)" 
  using aut17_pref_quotient_automata_0_contains_aut18_rev by auto

end
