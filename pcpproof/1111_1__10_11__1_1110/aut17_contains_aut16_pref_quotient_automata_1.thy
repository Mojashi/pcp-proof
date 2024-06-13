theory aut17_contains_aut16_pref_quotient_automata_1 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut17" "aut16_pref_quotient_automata_1" "PCPLib.AutomataUtil" begin

definition aut17_aut16_pref_quotient_automata_1_Intersection::"(PCP.alphabet,(aut17.State\<times>aut16_pref_quotient_automata_1.State)) da" where
  "aut17_aut16_pref_quotient_automata_1_Intersection \<equiv> intersect (complement aut17) aut16_pref_quotient_automata_1" 
definition aut17_aut16_pref_quotient_automata_1_Invariant::"(aut17.State\<times>aut16_pref_quotient_automata_1.State) set" where
  "aut17_aut16_pref_quotient_automata_1_Invariant \<equiv> { ((aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf)), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_R (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_L aut17.state_level1_Leaf), (aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_R aut17.state_level1_Leaf), (aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_R (aut17.state_level2_L aut17.state_level3_Leaf))), (aut16.State_R (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf))), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_R aut17.state_level3_Leaf))), (aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_L aut17.state_level3_Leaf))), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_R (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_R aut17.state_level3_Leaf))), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf))), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))), (aut17.State_Leaf, (aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_L (aut17.state_level2_R aut17.state_level3_Leaf))), (aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_R (aut17.state_level1_R (aut17.state_level2_R aut17.state_level3_Leaf))), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_L aut17.state_level4_Leaf)))), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_R aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf)), (aut16.State_L (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_L (aut16.state_level4_L aut16.state_level5_Leaf)))))), ((aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R aut17.state_level4_Leaf)))), (aut16.State_R (aut16.state_level1_L (aut16.state_level2_L (aut16.state_level3_L (aut16.state_level4_R aut16.state_level5_Leaf)))))) }"

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

lemma INV:"inv aut17_aut16_pref_quotient_automata_1_Intersection aut17_aut16_pref_quotient_automata_1_Invariant" 
proof -
  have CLOSED:"step_state_set aut17_aut16_pref_quotient_automata_1_Intersection aut17_aut16_pref_quotient_automata_1_Invariant \<subseteq> aut17_aut16_pref_quotient_automata_1_Invariant"
   by (simp only: aut17_aut16_pref_quotient_automata_1_Intersection_def step_complement, simp only: inv_covered aut17_aut16_pref_quotient_automata_1_Invariant_def, simp add: intersect_def aut17_def aut16_pref_quotient_automata_1_def)
  
  have INIT:"initial aut17_aut16_pref_quotient_automata_1_Intersection \<in> aut17_aut16_pref_quotient_automata_1_Invariant"
    apply (simp add: aut17_aut16_pref_quotient_automata_1_Invariant_def aut17_aut16_pref_quotient_automata_1_Intersection_def aut17_def aut16_pref_quotient_automata_1_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut17_aut16_pref_quotient_automata_1_Intersection)\<inter>aut17_aut16_pref_quotient_automata_1_Invariant = {}"
  proof (simp add:aut17_aut16_pref_quotient_automata_1_Invariant_def aut17_def aut16_pref_quotient_automata_1_def intersect_def aut17_aut16_pref_quotient_automata_1_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut17_aut16_pref_quotient_automata_1_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut17_contains_aut16_pref_quotient_automata_1_rev:"(lang_rev aut16_pref_quotient_automata_1) \<subseteq> (lang_rev aut17)" 
  using INV INT_LANG_REV_EMPTY aut17_aut16_pref_quotient_automata_1_Intersection_def comp_intersect_emp_then_includes[of aut17 aut16_pref_quotient_automata_1]
  by auto

theorem aut17_contains_aut16_pref_quotient_automata_1:"(lang aut16_pref_quotient_automata_1) \<subseteq> (lang aut17)" 
  using aut17_contains_aut16_pref_quotient_automata_1_rev by auto

end