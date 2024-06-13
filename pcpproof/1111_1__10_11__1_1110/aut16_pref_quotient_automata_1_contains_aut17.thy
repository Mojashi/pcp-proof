theory aut16_pref_quotient_automata_1_contains_aut17 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut16_pref_quotient_automata_1" "aut17" "PCPLib.AutomataUtil" begin

definition aut16_pref_quotient_automata_1_aut17_Intersection::"(PCP.alphabet,(aut16_pref_quotient_automata_1.State\<times>aut17.State)) da" where
  "aut16_pref_quotient_automata_1_aut17_Intersection \<equiv> intersect (complement aut16_pref_quotient_automata_1) aut17" 
definition aut16_pref_quotient_automata_1_aut17_Invariant::"(aut16_pref_quotient_automata_1.State\<times>aut17.State) set" where
  "aut16_pref_quotient_automata_1_aut17_Invariant \<equiv> { ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf)))), ((aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_L aut17.state_level1_Leaf)), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_R aut17.state_level3_Leaf)))), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), aut17.State_Leaf), ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_L aut17.state_level3_Leaf)))), ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_R aut17.state_level3_Leaf)))), ((aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R aut17.state_level1_Leaf)), ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf))), ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf))), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_L aut17.state_level3_Leaf)))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_R aut17.state_level3_Leaf)))), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf))), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf)))), ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf))))), ((aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf))))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_R aut17.state_level3_Leaf)))) }"

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

lemma INV:"inv aut16_pref_quotient_automata_1_aut17_Intersection aut16_pref_quotient_automata_1_aut17_Invariant" 
proof -
  have CLOSED:"step_state_set aut16_pref_quotient_automata_1_aut17_Intersection aut16_pref_quotient_automata_1_aut17_Invariant \<subseteq> aut16_pref_quotient_automata_1_aut17_Invariant"
   by (simp only: aut16_pref_quotient_automata_1_aut17_Intersection_def step_complement, simp only: inv_covered aut16_pref_quotient_automata_1_aut17_Invariant_def, simp add: intersect_def aut16_pref_quotient_automata_1_def aut17_def)
  
  have INIT:"initial aut16_pref_quotient_automata_1_aut17_Intersection \<in> aut16_pref_quotient_automata_1_aut17_Invariant"
    apply (simp add: aut16_pref_quotient_automata_1_aut17_Invariant_def aut16_pref_quotient_automata_1_aut17_Intersection_def aut16_pref_quotient_automata_1_def aut17_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut16_pref_quotient_automata_1_aut17_Intersection)\<inter>aut16_pref_quotient_automata_1_aut17_Invariant = {}"
  proof (simp add:aut16_pref_quotient_automata_1_aut17_Invariant_def aut16_pref_quotient_automata_1_def aut17_def intersect_def aut16_pref_quotient_automata_1_aut17_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut16_pref_quotient_automata_1_aut17_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut16_pref_quotient_automata_1_contains_aut17_rev:"(lang_rev aut17) \<subseteq> (lang_rev aut16_pref_quotient_automata_1)" 
  using INV INT_LANG_REV_EMPTY aut16_pref_quotient_automata_1_aut17_Intersection_def comp_intersect_emp_then_includes[of aut16_pref_quotient_automata_1 aut17]
  by auto

theorem aut16_pref_quotient_automata_1_contains_aut17:"(lang aut17) \<subseteq> (lang aut16_pref_quotient_automata_1)" 
  using aut16_pref_quotient_automata_1_contains_aut17_rev by auto

end
