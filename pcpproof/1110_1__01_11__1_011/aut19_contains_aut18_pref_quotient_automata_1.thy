theory aut19_contains_aut18_pref_quotient_automata_1 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut19" "aut18_pref_quotient_automata_1" "PCPLib.AutomataUtil" begin

definition aut19_aut18_pref_quotient_automata_1_Intersection::"(PCP.alphabet,(aut19.State\<times>aut18_pref_quotient_automata_1.State)) da" where
  "aut19_aut18_pref_quotient_automata_1_Intersection \<equiv> intersect (complement aut19) aut18_pref_quotient_automata_1" 
definition aut19_aut18_pref_quotient_automata_1_Invariant::"(aut19.State\<times>aut18_pref_quotient_automata_1.State) set" where
  "aut19_aut18_pref_quotient_automata_1_Invariant \<equiv> { ((aut19.State_L (aut19.state_level1_L aut19.state_level2_Leaf)), (aut18.State_L (aut18.state_level1_L aut18.state_level2_Leaf))), ((aut19.State_L (aut19.state_level1_R aut19.state_level2_Leaf)), (aut18.State_L (aut18.state_level1_R aut18.state_level2_Leaf))), ((aut19.State_R (aut19.state_level1_R aut19.state_level2_Leaf)), aut18.State_Leaf), ((aut19.State_R (aut19.state_level1_L aut19.state_level2_Leaf)), (aut18.State_R (aut18.state_level1_L aut18.state_level2_Leaf))) }"

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

lemma INV:"inv aut19_aut18_pref_quotient_automata_1_Intersection aut19_aut18_pref_quotient_automata_1_Invariant" 
proof -
  have CLOSED:"step_state_set aut19_aut18_pref_quotient_automata_1_Intersection aut19_aut18_pref_quotient_automata_1_Invariant \<subseteq> aut19_aut18_pref_quotient_automata_1_Invariant"
   by (simp only: aut19_aut18_pref_quotient_automata_1_Intersection_def step_complement, simp only: inv_covered aut19_aut18_pref_quotient_automata_1_Invariant_def, simp add: intersect_def aut19_def aut18_pref_quotient_automata_1_def)
  
  have INIT:"initial aut19_aut18_pref_quotient_automata_1_Intersection \<in> aut19_aut18_pref_quotient_automata_1_Invariant"
    apply (simp add: aut19_aut18_pref_quotient_automata_1_Invariant_def aut19_aut18_pref_quotient_automata_1_Intersection_def aut19_def aut18_pref_quotient_automata_1_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut19_aut18_pref_quotient_automata_1_Intersection)\<inter>aut19_aut18_pref_quotient_automata_1_Invariant = {}"
  proof (simp add:aut19_aut18_pref_quotient_automata_1_Invariant_def aut19_def aut18_pref_quotient_automata_1_def intersect_def aut19_aut18_pref_quotient_automata_1_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut19_aut18_pref_quotient_automata_1_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut19_contains_aut18_pref_quotient_automata_1_rev:"(lang_rev aut18_pref_quotient_automata_1) \<subseteq> (lang_rev aut19)" 
  using INV INT_LANG_REV_EMPTY aut19_aut18_pref_quotient_automata_1_Intersection_def comp_intersect_emp_then_includes[of aut19 aut18_pref_quotient_automata_1]
  by auto

theorem aut19_contains_aut18_pref_quotient_automata_1:"(lang aut18_pref_quotient_automata_1) \<subseteq> (lang aut19)" 
  using aut19_contains_aut18_pref_quotient_automata_1_rev by auto

end
