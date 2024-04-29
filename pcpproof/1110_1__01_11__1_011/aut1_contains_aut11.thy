theory aut1_contains_aut11 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut1" "aut11" "PCPLib.AutomataUtil" begin

definition aut1_aut11_Intersection::"(PCP.alphabet,(aut1.State\<times>aut11.State)) da" where
  "aut1_aut11_Intersection \<equiv> intersect (complement aut1) aut11" 
definition aut1_aut11_Invariant::"(aut1.State\<times>aut11.State) set" where
  "aut1_aut11_Invariant \<equiv> { ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), aut11.State_Leaf), ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), aut11.State_Leaf), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R aut1.state_level1_Leaf), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_L (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_L (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_L (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_L (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_R (aut1.state_level1_R (aut1.state_level2_R (aut1.state_level3_R (aut1.state_level4_L aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))), ((aut1.State_L aut1.state_level1_Leaf), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R aut11.state_level3_Leaf)))), ((aut1.State_L (aut1.state_level1_R (aut1.state_level2_L (aut1.state_level3_R (aut1.state_level4_R aut1.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L aut11.state_level3_Leaf)))) }"

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

lemma INV:"inv aut1_aut11_Intersection aut1_aut11_Invariant" 
proof -
  have CLOSED:"step_state_set aut1_aut11_Intersection aut1_aut11_Invariant \<subseteq> aut1_aut11_Invariant"
   by (simp only: aut1_aut11_Intersection_def step_complement, simp only: inv_covered aut1_aut11_Invariant_def, simp add: intersect_def aut1_def aut11_def)
  
  have INIT:"initial aut1_aut11_Intersection \<in> aut1_aut11_Invariant"
    apply (simp add: aut1_aut11_Invariant_def aut1_aut11_Intersection_def aut1_def aut11_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut1_aut11_Intersection)\<inter>aut1_aut11_Invariant = {}"
  proof (simp add:aut1_aut11_Invariant_def aut1_def aut11_def intersect_def aut1_aut11_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut1_aut11_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut1_contains_aut11_rev:"(lang_rev aut11) \<subseteq> (lang_rev aut1)" 
  using INV INT_LANG_REV_EMPTY aut1_aut11_Intersection_def comp_intersect_emp_then_includes[of aut1 aut11]
  by auto

theorem aut1_contains_aut11:"(lang aut11) \<subseteq> (lang aut1)" 
  using aut1_contains_aut11_rev by auto

end
