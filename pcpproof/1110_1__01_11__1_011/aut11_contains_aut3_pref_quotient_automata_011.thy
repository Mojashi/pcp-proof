theory aut11_contains_aut3_pref_quotient_automata_011 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut11" "aut3_pref_quotient_automata_011" "PCPLib.AutomataUtil" begin

definition aut11_aut3_pref_quotient_automata_011_Intersection::"(PCP.alphabet,(aut11.State\<times>aut3_pref_quotient_automata_011.State)) da" where
  "aut11_aut3_pref_quotient_automata_011_Intersection \<equiv> intersect (complement aut11) aut3_pref_quotient_automata_011" 
definition aut11_aut3_pref_quotient_automata_011_Invariant::"(aut11.State\<times>aut3_pref_quotient_automata_011.State) set" where
  "aut11_aut3_pref_quotient_automata_011_Invariant \<equiv> { ((aut11.State_L (aut11.state_level1_R (aut11.state_level2_R aut11.state_level3_Leaf))), (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), ((aut11.State_R (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf))), (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), ((aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf))), (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), ((aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf))), (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), ((aut11.State_R (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf))), (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), ((aut11.State_L (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf))), (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf))), ((aut11.State_L (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf))), (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf))), (aut11.State_Leaf, (aut3.State_R aut3.state_level1_Leaf)), ((aut11.State_R (aut11.state_level1_R (aut11.state_level2_R aut11.state_level3_Leaf))), (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))) }"

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

lemma INV:"inv aut11_aut3_pref_quotient_automata_011_Intersection aut11_aut3_pref_quotient_automata_011_Invariant" 
proof -
  have CLOSED:"step_state_set aut11_aut3_pref_quotient_automata_011_Intersection aut11_aut3_pref_quotient_automata_011_Invariant \<subseteq> aut11_aut3_pref_quotient_automata_011_Invariant"
   by (simp only: aut11_aut3_pref_quotient_automata_011_Intersection_def step_complement, simp only: inv_covered aut11_aut3_pref_quotient_automata_011_Invariant_def, simp add: intersect_def aut11_def aut3_pref_quotient_automata_011_def)
  
  have INIT:"initial aut11_aut3_pref_quotient_automata_011_Intersection \<in> aut11_aut3_pref_quotient_automata_011_Invariant"
    apply (simp add: aut11_aut3_pref_quotient_automata_011_Invariant_def aut11_aut3_pref_quotient_automata_011_Intersection_def aut11_def aut3_pref_quotient_automata_011_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut11_aut3_pref_quotient_automata_011_Intersection)\<inter>aut11_aut3_pref_quotient_automata_011_Invariant = {}"
  proof (simp add:aut11_aut3_pref_quotient_automata_011_Invariant_def aut11_def aut3_pref_quotient_automata_011_def intersect_def aut11_aut3_pref_quotient_automata_011_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut11_aut3_pref_quotient_automata_011_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut11_contains_aut3_pref_quotient_automata_011_rev:"(lang_rev aut3_pref_quotient_automata_011) \<subseteq> (lang_rev aut11)" 
  using INV INT_LANG_REV_EMPTY aut11_aut3_pref_quotient_automata_011_Intersection_def comp_intersect_emp_then_includes[of aut11 aut3_pref_quotient_automata_011]
  by auto

theorem aut11_contains_aut3_pref_quotient_automata_011:"(lang aut3_pref_quotient_automata_011) \<subseteq> (lang aut11)" 
  using aut11_contains_aut3_pref_quotient_automata_011_rev by auto

end
