theory aut12_contains_aut11_pref_quotient_automata_1111 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut12" "aut11_pref_quotient_automata_1111" "PCPLib.AutomataUtil" begin

definition aut12_aut11_pref_quotient_automata_1111_Intersection::"(PCP.alphabet,(aut12.State\<times>aut11_pref_quotient_automata_1111.State)) da" where
  "aut12_aut11_pref_quotient_automata_1111_Intersection \<equiv> intersect (complement aut12) aut11_pref_quotient_automata_1111" 
definition aut12_aut11_pref_quotient_automata_1111_Invariant::"(aut12.State\<times>aut11_pref_quotient_automata_1111.State) set" where
  "aut12_aut11_pref_quotient_automata_1111_Invariant \<equiv> { ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_R aut12.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_L aut11.state_level2_Leaf))), ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_R aut12.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_L aut11.state_level4_Leaf))))), ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_L aut12.state_level3_Leaf))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf))))), ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_R aut12.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_L aut11.state_level4_Leaf))))), ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_L aut12.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R aut11.state_level4_Leaf))))), ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_L aut12.state_level3_Leaf))), (aut11.State_R aut11.state_level1_Leaf)), ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_L aut12.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_L aut11.state_level4_Leaf))))), ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_R aut12.state_level3_Leaf))), (aut11.State_L (aut11.state_level1_R aut11.state_level2_Leaf))) }"

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

lemma INV:"inv aut12_aut11_pref_quotient_automata_1111_Intersection aut12_aut11_pref_quotient_automata_1111_Invariant" 
proof -
  have CLOSED:"step_state_set aut12_aut11_pref_quotient_automata_1111_Intersection aut12_aut11_pref_quotient_automata_1111_Invariant \<subseteq> aut12_aut11_pref_quotient_automata_1111_Invariant"
   by (simp only: aut12_aut11_pref_quotient_automata_1111_Intersection_def step_complement, simp only: inv_covered aut12_aut11_pref_quotient_automata_1111_Invariant_def, simp add: intersect_def aut12_def aut11_pref_quotient_automata_1111_def)
  
  have INIT:"initial aut12_aut11_pref_quotient_automata_1111_Intersection \<in> aut12_aut11_pref_quotient_automata_1111_Invariant"
    apply (simp add: aut12_aut11_pref_quotient_automata_1111_Invariant_def aut12_aut11_pref_quotient_automata_1111_Intersection_def aut12_def aut11_pref_quotient_automata_1111_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut12_aut11_pref_quotient_automata_1111_Intersection)\<inter>aut12_aut11_pref_quotient_automata_1111_Invariant = {}"
  proof (simp add:aut12_aut11_pref_quotient_automata_1111_Invariant_def aut12_def aut11_pref_quotient_automata_1111_def intersect_def aut12_aut11_pref_quotient_automata_1111_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut12_aut11_pref_quotient_automata_1111_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut12_contains_aut11_pref_quotient_automata_1111_rev:"(lang_rev aut11_pref_quotient_automata_1111) \<subseteq> (lang_rev aut12)" 
  using INV INT_LANG_REV_EMPTY aut12_aut11_pref_quotient_automata_1111_Intersection_def comp_intersect_emp_then_includes[of aut12 aut11_pref_quotient_automata_1111]
  by auto

theorem aut12_contains_aut11_pref_quotient_automata_1111:"(lang aut11_pref_quotient_automata_1111) \<subseteq> (lang aut12)" 
  using aut12_contains_aut11_pref_quotient_automata_1111_rev by auto

end
