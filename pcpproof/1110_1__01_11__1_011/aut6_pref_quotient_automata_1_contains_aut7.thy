theory aut6_pref_quotient_automata_1_contains_aut7 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut6_pref_quotient_automata_1" "aut7" "PCPLib.AutomataUtil" begin

definition aut6_pref_quotient_automata_1_aut7_Intersection::"(PCP.alphabet,(aut6_pref_quotient_automata_1.State\<times>aut7.State)) da" where
  "aut6_pref_quotient_automata_1_aut7_Intersection \<equiv> intersect (complement aut6_pref_quotient_automata_1) aut7" 
definition aut6_pref_quotient_automata_1_aut7_Invariant::"(aut6_pref_quotient_automata_1.State\<times>aut7.State) set" where
  "aut6_pref_quotient_automata_1_aut7_Invariant \<equiv> { ((aut6.State_L (aut6.state_level1_R (aut6.state_level2_R (aut6.state_level3_L aut6.state_level4_Leaf)))), (aut7.State_L (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf)))), ((aut6.State_L (aut6.state_level1_R (aut6.state_level2_L (aut6.state_level3_R aut6.state_level4_Leaf)))), (aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf))), ((aut6.State_R (aut6.state_level1_R (aut6.state_level2_L (aut6.state_level3_L aut6.state_level4_Leaf)))), (aut7.State_R (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))), ((aut6.State_L (aut6.state_level1_L (aut6.state_level2_L (aut6.state_level3_R aut6.state_level4_Leaf)))), (aut7.State_R (aut7.state_level1_L aut7.state_level2_Leaf))), ((aut6.State_R (aut6.state_level1_L (aut6.state_level2_R (aut6.state_level3_R aut6.state_level4_Leaf)))), (aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf))), ((aut6.State_R (aut6.state_level1_R (aut6.state_level2_R (aut6.state_level3_R aut6.state_level4_Leaf)))), (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))), ((aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf)), (aut7.State_R (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf)))), ((aut6.State_L (aut6.state_level1_R (aut6.state_level2_L (aut6.state_level3_L aut6.state_level4_Leaf)))), (aut7.State_L (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))), ((aut6.State_R (aut6.state_level1_R (aut6.state_level2_L (aut6.state_level3_R aut6.state_level4_Leaf)))), aut7.State_Leaf), ((aut6.State_L aut6.state_level1_Leaf), (aut7.State_L aut7.state_level1_Leaf)), ((aut6.State_L (aut6.state_level1_L (aut6.state_level2_R (aut6.state_level3_R aut6.state_level4_Leaf)))), (aut7.State_L (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf)))), ((aut6.State_L (aut6.state_level1_L (aut6.state_level2_R (aut6.state_level3_L aut6.state_level4_Leaf)))), (aut7.State_R (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf)))), ((aut6.State_R (aut6.state_level1_L (aut6.state_level2_L (aut6.state_level3_L aut6.state_level4_Leaf)))), (aut7.State_R (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf)))), ((aut6.State_L (aut6.state_level1_R (aut6.state_level2_R (aut6.state_level3_R aut6.state_level4_Leaf)))), (aut7.State_R aut7.state_level1_Leaf)), ((aut6.State_R (aut6.state_level1_R (aut6.state_level2_R (aut6.state_level3_L aut6.state_level4_Leaf)))), (aut7.State_L (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf)))) }"

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

lemma INV:"inv aut6_pref_quotient_automata_1_aut7_Intersection aut6_pref_quotient_automata_1_aut7_Invariant" 
proof -
  have CLOSED:"step_state_set aut6_pref_quotient_automata_1_aut7_Intersection aut6_pref_quotient_automata_1_aut7_Invariant \<subseteq> aut6_pref_quotient_automata_1_aut7_Invariant"
   by (simp only: aut6_pref_quotient_automata_1_aut7_Intersection_def step_complement, simp only: inv_covered aut6_pref_quotient_automata_1_aut7_Invariant_def, simp add: intersect_def aut6_pref_quotient_automata_1_def aut7_def)
  
  have INIT:"initial aut6_pref_quotient_automata_1_aut7_Intersection \<in> aut6_pref_quotient_automata_1_aut7_Invariant"
    apply (simp add: aut6_pref_quotient_automata_1_aut7_Invariant_def aut6_pref_quotient_automata_1_aut7_Intersection_def aut6_pref_quotient_automata_1_def aut7_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut6_pref_quotient_automata_1_aut7_Intersection)\<inter>aut6_pref_quotient_automata_1_aut7_Invariant = {}"
  proof (simp add:aut6_pref_quotient_automata_1_aut7_Invariant_def aut6_pref_quotient_automata_1_def aut7_def intersect_def aut6_pref_quotient_automata_1_aut7_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut6_pref_quotient_automata_1_aut7_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut6_pref_quotient_automata_1_contains_aut7_rev:"(lang_rev aut7) \<subseteq> (lang_rev aut6_pref_quotient_automata_1)" 
  using INV INT_LANG_REV_EMPTY aut6_pref_quotient_automata_1_aut7_Intersection_def comp_intersect_emp_then_includes[of aut6_pref_quotient_automata_1 aut7]
  by auto

theorem aut6_pref_quotient_automata_1_contains_aut7:"(lang aut7) \<subseteq> (lang aut6_pref_quotient_automata_1)" 
  using aut6_pref_quotient_automata_1_contains_aut7_rev by auto

end
