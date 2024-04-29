theory aut7_contains_aut6_pref_quotient_automata_1 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut7" "aut6_pref_quotient_automata_1" "PCPLib.AutomataUtil" begin

definition aut7_aut6_pref_quotient_automata_1_Intersection::"(PCP.alphabet,(aut7.State\<times>aut6_pref_quotient_automata_1.State)) da" where
  "aut7_aut6_pref_quotient_automata_1_Intersection \<equiv> intersect (complement aut7) aut6_pref_quotient_automata_1" 
definition aut7_aut6_pref_quotient_automata_1_Invariant::"(aut7.State\<times>aut6_pref_quotient_automata_1.State) set" where
  "aut7_aut6_pref_quotient_automata_1_Invariant \<equiv> { (aut7.State_Leaf, (aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf))), ((aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf)), (aut6.State_L aut6.state_level1_Leaf)), ((aut7.State_R (aut7.state_level1_L aut7.state_level2_Leaf)), (aut6.State_R (aut6.state_level1_R aut6.state_level2_Leaf))), ((aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf)), (aut6.State_R (aut6.state_level1_L aut6.state_level2_Leaf))), ((aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf)), (aut6.State_R aut6.state_level1_Leaf)) }"

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

lemma INV:"inv aut7_aut6_pref_quotient_automata_1_Intersection aut7_aut6_pref_quotient_automata_1_Invariant" 
proof -
  have CLOSED:"step_state_set aut7_aut6_pref_quotient_automata_1_Intersection aut7_aut6_pref_quotient_automata_1_Invariant \<subseteq> aut7_aut6_pref_quotient_automata_1_Invariant"
   by (simp only: aut7_aut6_pref_quotient_automata_1_Intersection_def step_complement, simp only: inv_covered aut7_aut6_pref_quotient_automata_1_Invariant_def, simp add: intersect_def aut7_def aut6_pref_quotient_automata_1_def)
  
  have INIT:"initial aut7_aut6_pref_quotient_automata_1_Intersection \<in> aut7_aut6_pref_quotient_automata_1_Invariant"
    apply (simp add: aut7_aut6_pref_quotient_automata_1_Invariant_def aut7_aut6_pref_quotient_automata_1_Intersection_def aut7_def aut6_pref_quotient_automata_1_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut7_aut6_pref_quotient_automata_1_Intersection)\<inter>aut7_aut6_pref_quotient_automata_1_Invariant = {}"
  proof (simp add:aut7_aut6_pref_quotient_automata_1_Invariant_def aut7_def aut6_pref_quotient_automata_1_def intersect_def aut7_aut6_pref_quotient_automata_1_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut7_aut6_pref_quotient_automata_1_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut7_contains_aut6_pref_quotient_automata_1_rev:"(lang_rev aut6_pref_quotient_automata_1) \<subseteq> (lang_rev aut7)" 
  using INV INT_LANG_REV_EMPTY aut7_aut6_pref_quotient_automata_1_Intersection_def comp_intersect_emp_then_includes[of aut7 aut6_pref_quotient_automata_1]
  by auto

theorem aut7_contains_aut6_pref_quotient_automata_1:"(lang aut6_pref_quotient_automata_1) \<subseteq> (lang aut7)" 
  using aut7_contains_aut6_pref_quotient_automata_1_rev by auto

end
