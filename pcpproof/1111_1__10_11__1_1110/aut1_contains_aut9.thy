theory aut1_contains_aut9 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut1" "aut9" "PCPLib.AutomataUtil" begin

definition aut1_aut9_Intersection::"(PCP.alphabet,(aut1.State\<times>aut9.State)) da" where
  "aut1_aut9_Intersection \<equiv> intersect (complement aut1) aut9" 
definition aut1_aut9_Invariant::"(aut1.State\<times>aut9.State) set" where
  "aut1_aut9_Invariant \<equiv> { ((aut1.State_R (aut1.state_level1_L aut1.state_level2_Leaf)), (aut9.State_R aut9.state_level1_Leaf)), ((aut1.State_R (aut1.state_level1_R aut1.state_level2_Leaf)), aut9.State_Leaf), ((aut1.State_R aut1.state_level1_Leaf), aut9.State_Leaf), ((aut1.State_L (aut1.state_level1_R aut1.state_level2_Leaf)), aut9.State_Leaf), ((aut1.State_L aut1.state_level1_Leaf), aut9.State_Leaf), ((aut1.State_L (aut1.state_level1_L aut1.state_level2_Leaf)), (aut9.State_L aut9.state_level1_Leaf)) }"

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

lemma INV:"inv aut1_aut9_Intersection aut1_aut9_Invariant" 
proof -
  have CLOSED:"step_state_set aut1_aut9_Intersection aut1_aut9_Invariant \<subseteq> aut1_aut9_Invariant"
   by (simp only: aut1_aut9_Intersection_def step_complement, simp only: inv_covered aut1_aut9_Invariant_def, simp add: intersect_def aut1_def aut9_def)
  
  have INIT:"initial aut1_aut9_Intersection \<in> aut1_aut9_Invariant"
    apply (simp add: aut1_aut9_Invariant_def aut1_aut9_Intersection_def aut1_def aut9_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut1_aut9_Intersection)\<inter>aut1_aut9_Invariant = {}"
  proof (simp add:aut1_aut9_Invariant_def aut1_def aut9_def intersect_def aut1_aut9_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut1_aut9_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut1_contains_aut9_rev:"(lang_rev aut9) \<subseteq> (lang_rev aut1)" 
  using INV INT_LANG_REV_EMPTY aut1_aut9_Intersection_def comp_intersect_emp_then_includes[of aut1 aut9]
  by auto

theorem aut1_contains_aut9:"(lang aut9) \<subseteq> (lang aut1)" 
  using aut1_contains_aut9_rev by auto

end
