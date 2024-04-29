theory aut11_pref_quotient_automata_1111_contains_aut12 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut11_pref_quotient_automata_1111" "aut12" "PCPLib.AutomataUtil" begin

definition aut11_pref_quotient_automata_1111_aut12_Intersection::"(PCP.alphabet,(aut11_pref_quotient_automata_1111.State\<times>aut12.State)) da" where
  "aut11_pref_quotient_automata_1111_aut12_Intersection \<equiv> intersect (complement aut11_pref_quotient_automata_1111) aut12" 
definition aut11_pref_quotient_automata_1111_aut12_Invariant::"(aut11_pref_quotient_automata_1111.State\<times>aut12.State) set" where
  "aut11_pref_quotient_automata_1111_aut12_Invariant \<equiv> { ((aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))), ((aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))), ((aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_R aut11.state_level2_Leaf)), (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_L (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_R (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))), ((aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))), ((aut11.State_L aut11.state_level1_Leaf), (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_L (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_L aut11.state_level2_Leaf)), (aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_L (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))), ((aut11.State_R (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_R (aut11.state_level4_R aut11.state_level5_Leaf))))), aut12.State_Leaf), ((aut11.State_R (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))) }"

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

lemma INV:"inv aut11_pref_quotient_automata_1111_aut12_Intersection aut11_pref_quotient_automata_1111_aut12_Invariant" 
proof -
  have CLOSED:"step_state_set aut11_pref_quotient_automata_1111_aut12_Intersection aut11_pref_quotient_automata_1111_aut12_Invariant \<subseteq> aut11_pref_quotient_automata_1111_aut12_Invariant"
   by (simp only: aut11_pref_quotient_automata_1111_aut12_Intersection_def step_complement, simp only: inv_covered aut11_pref_quotient_automata_1111_aut12_Invariant_def, simp add: intersect_def aut11_pref_quotient_automata_1111_def aut12_def)
  
  have INIT:"initial aut11_pref_quotient_automata_1111_aut12_Intersection \<in> aut11_pref_quotient_automata_1111_aut12_Invariant"
    apply (simp add: aut11_pref_quotient_automata_1111_aut12_Invariant_def aut11_pref_quotient_automata_1111_aut12_Intersection_def aut11_pref_quotient_automata_1111_def aut12_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut11_pref_quotient_automata_1111_aut12_Intersection)\<inter>aut11_pref_quotient_automata_1111_aut12_Invariant = {}"
  proof (simp add:aut11_pref_quotient_automata_1111_aut12_Invariant_def aut11_pref_quotient_automata_1111_def aut12_def intersect_def aut11_pref_quotient_automata_1111_aut12_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut11_pref_quotient_automata_1111_aut12_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut11_pref_quotient_automata_1111_contains_aut12_rev:"(lang_rev aut12) \<subseteq> (lang_rev aut11_pref_quotient_automata_1111)" 
  using INV INT_LANG_REV_EMPTY aut11_pref_quotient_automata_1111_aut12_Intersection_def comp_intersect_emp_then_includes[of aut11_pref_quotient_automata_1111 aut12]
  by auto

theorem aut11_pref_quotient_automata_1111_contains_aut12:"(lang aut12) \<subseteq> (lang aut11_pref_quotient_automata_1111)" 
  using aut11_pref_quotient_automata_1111_contains_aut12_rev by auto

end
