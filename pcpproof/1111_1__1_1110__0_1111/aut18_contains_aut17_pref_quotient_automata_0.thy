theory aut18_contains_aut17_pref_quotient_automata_0 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut18" "aut17_pref_quotient_automata_0" "PCPLib.AutomataUtil" begin

definition aut18_aut17_pref_quotient_automata_0_Intersection::"(PCP.alphabet,(aut18.State\<times>aut17_pref_quotient_automata_0.State)) da" where
  "aut18_aut17_pref_quotient_automata_0_Intersection \<equiv> intersect (complement aut18) aut17_pref_quotient_automata_0" 
definition aut18_aut17_pref_quotient_automata_0_Invariant::"(aut18.State\<times>aut17_pref_quotient_automata_0.State) set" where
  "aut18_aut17_pref_quotient_automata_0_Invariant \<equiv> { ((aut18.State_L (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf))), ((aut18.State_L (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf)))), (aut17.State_R aut17.state_level1_Leaf)), ((aut18.State_L (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf)))), aut17.State_Leaf), ((aut18.State_R (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_L aut17.state_level5_Leaf)))))), ((aut18.State_R (aut18.state_level1_L aut18.state_level2_Leaf)), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_L (aut18.state_level1_L aut18.state_level2_Leaf)), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_L (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf)))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_L (aut18.state_level1_R aut18.state_level2_Leaf)), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_R (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_R (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf)))), ((aut18.State_R (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_L aut18.state_level4_Leaf)))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_L (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf))), ((aut18.State_R (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_L (aut17.state_level4_L aut17.state_level5_Leaf)))))), ((aut18.State_L (aut18.state_level1_L (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_R (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_L aut17.state_level3_Leaf)))), ((aut18.State_L (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_R (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf)))))), ((aut18.State_R (aut18.state_level1_R aut18.state_level2_Leaf)), (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf))), ((aut18.State_R (aut18.state_level1_R (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_L aut17.state_level1_Leaf)), ((aut18.State_L (aut18.state_level1_L (aut18.state_level2_R (aut18.state_level3_R aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_R aut17.state_level3_Leaf)))), ((aut18.State_R (aut18.state_level1_R (aut18.state_level2_L (aut18.state_level3_L aut18.state_level4_Leaf)))), (aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_L aut17.state_level5_Leaf)))))) }"

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

lemma INV:"inv aut18_aut17_pref_quotient_automata_0_Intersection aut18_aut17_pref_quotient_automata_0_Invariant" 
proof -
  have CLOSED:"step_state_set aut18_aut17_pref_quotient_automata_0_Intersection aut18_aut17_pref_quotient_automata_0_Invariant \<subseteq> aut18_aut17_pref_quotient_automata_0_Invariant"
   by (simp only: aut18_aut17_pref_quotient_automata_0_Intersection_def step_complement, simp only: inv_covered aut18_aut17_pref_quotient_automata_0_Invariant_def, simp add: intersect_def aut18_def aut17_pref_quotient_automata_0_def)
  
  have INIT:"initial aut18_aut17_pref_quotient_automata_0_Intersection \<in> aut18_aut17_pref_quotient_automata_0_Invariant"
    apply (simp add: aut18_aut17_pref_quotient_automata_0_Invariant_def aut18_aut17_pref_quotient_automata_0_Intersection_def aut18_def aut17_pref_quotient_automata_0_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut18_aut17_pref_quotient_automata_0_Intersection)\<inter>aut18_aut17_pref_quotient_automata_0_Invariant = {}"
  proof (simp add:aut18_aut17_pref_quotient_automata_0_Invariant_def aut18_def aut17_pref_quotient_automata_0_def intersect_def aut18_aut17_pref_quotient_automata_0_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut18_aut17_pref_quotient_automata_0_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut18_contains_aut17_pref_quotient_automata_0_rev:"(lang_rev aut17_pref_quotient_automata_0) \<subseteq> (lang_rev aut18)" 
  using INV INT_LANG_REV_EMPTY aut18_aut17_pref_quotient_automata_0_Intersection_def comp_intersect_emp_then_includes[of aut18 aut17_pref_quotient_automata_0]
  by auto

theorem aut18_contains_aut17_pref_quotient_automata_0:"(lang aut17_pref_quotient_automata_0) \<subseteq> (lang aut18)" 
  using aut18_contains_aut17_pref_quotient_automata_0_rev by auto

end
