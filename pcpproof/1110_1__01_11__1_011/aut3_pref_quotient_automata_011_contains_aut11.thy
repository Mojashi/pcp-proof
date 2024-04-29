theory aut3_pref_quotient_automata_011_contains_aut11 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut3_pref_quotient_automata_011" "aut11" "PCPLib.AutomataUtil" begin

definition aut3_pref_quotient_automata_011_aut11_Intersection::"(PCP.alphabet,(aut3_pref_quotient_automata_011.State\<times>aut11.State)) da" where
  "aut3_pref_quotient_automata_011_aut11_Intersection \<equiv> intersect (complement aut3_pref_quotient_automata_011) aut11" 
definition aut3_pref_quotient_automata_011_aut11_Invariant::"(aut3_pref_quotient_automata_011.State\<times>aut11.State) set" where
  "aut3_pref_quotient_automata_011_aut11_Invariant \<equiv> { ((aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf)), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut3.State_R aut3.state_level1_Leaf), aut11.State_Leaf), ((aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_R aut11.state_level3_Leaf)))) }"

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

lemma INV:"inv aut3_pref_quotient_automata_011_aut11_Intersection aut3_pref_quotient_automata_011_aut11_Invariant" 
proof -
  have CLOSED:"step_state_set aut3_pref_quotient_automata_011_aut11_Intersection aut3_pref_quotient_automata_011_aut11_Invariant \<subseteq> aut3_pref_quotient_automata_011_aut11_Invariant"
   by (simp only: aut3_pref_quotient_automata_011_aut11_Intersection_def step_complement, simp only: inv_covered aut3_pref_quotient_automata_011_aut11_Invariant_def, simp add: intersect_def aut3_pref_quotient_automata_011_def aut11_def)
  
  have INIT:"initial aut3_pref_quotient_automata_011_aut11_Intersection \<in> aut3_pref_quotient_automata_011_aut11_Invariant"
    apply (simp add: aut3_pref_quotient_automata_011_aut11_Invariant_def aut3_pref_quotient_automata_011_aut11_Intersection_def aut3_pref_quotient_automata_011_def aut11_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut3_pref_quotient_automata_011_aut11_Intersection)\<inter>aut3_pref_quotient_automata_011_aut11_Invariant = {}"
  proof (simp add:aut3_pref_quotient_automata_011_aut11_Invariant_def aut3_pref_quotient_automata_011_def aut11_def intersect_def aut3_pref_quotient_automata_011_aut11_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut3_pref_quotient_automata_011_aut11_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut3_pref_quotient_automata_011_contains_aut11_rev:"(lang_rev aut11) \<subseteq> (lang_rev aut3_pref_quotient_automata_011)" 
  using INV INT_LANG_REV_EMPTY aut3_pref_quotient_automata_011_aut11_Intersection_def comp_intersect_emp_then_includes[of aut3_pref_quotient_automata_011 aut11]
  by auto

theorem aut3_pref_quotient_automata_011_contains_aut11:"(lang aut11) \<subseteq> (lang aut3_pref_quotient_automata_011)" 
  using aut3_pref_quotient_automata_011_contains_aut11_rev by auto

end
