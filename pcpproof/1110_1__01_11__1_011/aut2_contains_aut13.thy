theory aut2_contains_aut13 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut2" "aut13" "PCPLib.AutomataUtil" begin

definition aut2_aut13_Intersection::"(PCP.alphabet,(aut2.State\<times>aut13.State)) da" where
  "aut2_aut13_Intersection \<equiv> intersect (complement aut2) aut13" 
definition aut2_aut13_Invariant::"(aut2.State\<times>aut13.State) set" where
  "aut2_aut13_Invariant \<equiv> { ((aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)), (aut13.State_R aut13.state_level1_Leaf)), ((aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)), (aut13.State_L aut13.state_level1_Leaf)), ((aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)), (aut13.State_R aut13.state_level1_Leaf)), ((aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)), (aut13.State_R aut13.state_level1_Leaf)) }"

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

lemma INV:"inv aut2_aut13_Intersection aut2_aut13_Invariant" 
proof -
  have CLOSED:"step_state_set aut2_aut13_Intersection aut2_aut13_Invariant \<subseteq> aut2_aut13_Invariant"
   by (simp only: aut2_aut13_Intersection_def step_complement, simp only: inv_covered aut2_aut13_Invariant_def, simp add: intersect_def aut2_def aut13_def)
  
  have INIT:"initial aut2_aut13_Intersection \<in> aut2_aut13_Invariant"
    apply (simp add: aut2_aut13_Invariant_def aut2_aut13_Intersection_def aut2_def aut13_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut2_aut13_Intersection)\<inter>aut2_aut13_Invariant = {}"
  proof (simp add:aut2_aut13_Invariant_def aut2_def aut13_def intersect_def aut2_aut13_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut2_aut13_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut2_contains_aut13_rev:"(lang_rev aut13) \<subseteq> (lang_rev aut2)" 
  using INV INT_LANG_REV_EMPTY aut2_aut13_Intersection_def comp_intersect_emp_then_includes[of aut2 aut13]
  by auto

theorem aut2_contains_aut13:"(lang aut13) \<subseteq> (lang aut2)" 
  using aut2_contains_aut13_rev by auto

end
