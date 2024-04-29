theory aut15_contains_aut14_pref_quotient_automata_01 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut15" "aut14_pref_quotient_automata_01" "PCPLib.AutomataUtil" begin

definition aut15_aut14_pref_quotient_automata_01_Intersection::"(PCP.alphabet,(aut15.State\<times>aut14_pref_quotient_automata_01.State)) da" where
  "aut15_aut14_pref_quotient_automata_01_Intersection \<equiv> intersect (complement aut15) aut14_pref_quotient_automata_01" 
definition aut15_aut14_pref_quotient_automata_01_Invariant::"(aut15.State\<times>aut14_pref_quotient_automata_01.State) set" where
  "aut15_aut14_pref_quotient_automata_01_Invariant \<equiv> { ((aut15.State_R aut15.state_level1_Leaf), (aut14.State_R (aut14.state_level1_L aut14.state_level2_Leaf))), ((aut15.State_L aut15.state_level1_Leaf), (aut14.State_L (aut14.state_level1_R aut14.state_level2_Leaf))), (aut15.State_Leaf, (aut14.State_R (aut14.state_level1_R aut14.state_level2_Leaf))) }"

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

lemma INV:"inv aut15_aut14_pref_quotient_automata_01_Intersection aut15_aut14_pref_quotient_automata_01_Invariant" 
proof -
  have CLOSED:"step_state_set aut15_aut14_pref_quotient_automata_01_Intersection aut15_aut14_pref_quotient_automata_01_Invariant \<subseteq> aut15_aut14_pref_quotient_automata_01_Invariant"
   by (simp only: aut15_aut14_pref_quotient_automata_01_Intersection_def step_complement, simp only: inv_covered aut15_aut14_pref_quotient_automata_01_Invariant_def, simp add: intersect_def aut15_def aut14_pref_quotient_automata_01_def)
  
  have INIT:"initial aut15_aut14_pref_quotient_automata_01_Intersection \<in> aut15_aut14_pref_quotient_automata_01_Invariant"
    apply (simp add: aut15_aut14_pref_quotient_automata_01_Invariant_def aut15_aut14_pref_quotient_automata_01_Intersection_def aut15_def aut14_pref_quotient_automata_01_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut15_aut14_pref_quotient_automata_01_Intersection)\<inter>aut15_aut14_pref_quotient_automata_01_Invariant = {}"
  proof (simp add:aut15_aut14_pref_quotient_automata_01_Invariant_def aut15_def aut14_pref_quotient_automata_01_def intersect_def aut15_aut14_pref_quotient_automata_01_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut15_aut14_pref_quotient_automata_01_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut15_contains_aut14_pref_quotient_automata_01_rev:"(lang_rev aut14_pref_quotient_automata_01) \<subseteq> (lang_rev aut15)" 
  using INV INT_LANG_REV_EMPTY aut15_aut14_pref_quotient_automata_01_Intersection_def comp_intersect_emp_then_includes[of aut15 aut14_pref_quotient_automata_01]
  by auto

theorem aut15_contains_aut14_pref_quotient_automata_01:"(lang aut14_pref_quotient_automata_01) \<subseteq> (lang aut15)" 
  using aut15_contains_aut14_pref_quotient_automata_01_rev by auto

end
