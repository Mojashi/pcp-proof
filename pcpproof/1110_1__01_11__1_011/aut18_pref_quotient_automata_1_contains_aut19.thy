theory aut18_pref_quotient_automata_1_contains_aut19 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut18_pref_quotient_automata_1" "aut19" "PCPLib.AutomataUtil" begin

definition aut18_pref_quotient_automata_1_aut19_Intersection::"(PCP.alphabet,(aut18_pref_quotient_automata_1.State\<times>aut19.State)) da" where
  "aut18_pref_quotient_automata_1_aut19_Intersection \<equiv> intersect (complement aut18_pref_quotient_automata_1) aut19" 
definition aut18_pref_quotient_automata_1_aut19_Invariant::"(aut18_pref_quotient_automata_1.State\<times>aut19.State) set" where
  "aut18_pref_quotient_automata_1_aut19_Invariant \<equiv> { (aut18.State_Leaf, (aut19.State_R (aut19.state_level1_R aut19.state_level2_Leaf))), ((aut18.State_L (aut18.state_level1_R aut18.state_level2_Leaf)), (aut19.State_L (aut19.state_level1_R aut19.state_level2_Leaf))), ((aut18.State_L (aut18.state_level1_L aut18.state_level2_Leaf)), (aut19.State_L (aut19.state_level1_L aut19.state_level2_Leaf))), ((aut18.State_R (aut18.state_level1_L aut18.state_level2_Leaf)), (aut19.State_R (aut19.state_level1_L aut19.state_level2_Leaf))) }"

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

lemma INV:"inv aut18_pref_quotient_automata_1_aut19_Intersection aut18_pref_quotient_automata_1_aut19_Invariant" 
proof -
  have CLOSED:"step_state_set aut18_pref_quotient_automata_1_aut19_Intersection aut18_pref_quotient_automata_1_aut19_Invariant \<subseteq> aut18_pref_quotient_automata_1_aut19_Invariant"
   by (simp only: aut18_pref_quotient_automata_1_aut19_Intersection_def step_complement, simp only: inv_covered aut18_pref_quotient_automata_1_aut19_Invariant_def, simp add: intersect_def aut18_pref_quotient_automata_1_def aut19_def)
  
  have INIT:"initial aut18_pref_quotient_automata_1_aut19_Intersection \<in> aut18_pref_quotient_automata_1_aut19_Invariant"
    apply (simp add: aut18_pref_quotient_automata_1_aut19_Invariant_def aut18_pref_quotient_automata_1_aut19_Intersection_def aut18_pref_quotient_automata_1_def aut19_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut18_pref_quotient_automata_1_aut19_Intersection)\<inter>aut18_pref_quotient_automata_1_aut19_Invariant = {}"
  proof (simp add:aut18_pref_quotient_automata_1_aut19_Invariant_def aut18_pref_quotient_automata_1_def aut19_def intersect_def aut18_pref_quotient_automata_1_aut19_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut18_pref_quotient_automata_1_aut19_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut18_pref_quotient_automata_1_contains_aut19_rev:"(lang_rev aut19) \<subseteq> (lang_rev aut18_pref_quotient_automata_1)" 
  using INV INT_LANG_REV_EMPTY aut18_pref_quotient_automata_1_aut19_Intersection_def comp_intersect_emp_then_includes[of aut18_pref_quotient_automata_1 aut19]
  by auto

theorem aut18_pref_quotient_automata_1_contains_aut19:"(lang aut19) \<subseteq> (lang aut18_pref_quotient_automata_1)" 
  using aut18_pref_quotient_automata_1_contains_aut19_rev by auto

end
