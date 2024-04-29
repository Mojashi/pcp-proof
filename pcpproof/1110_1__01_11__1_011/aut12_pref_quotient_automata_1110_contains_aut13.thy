theory aut12_pref_quotient_automata_1110_contains_aut13 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut12_pref_quotient_automata_1110" "aut13" "PCPLib.AutomataUtil" begin

definition aut12_pref_quotient_automata_1110_aut13_Intersection::"(PCP.alphabet,(aut12_pref_quotient_automata_1110.State\<times>aut13.State)) da" where
  "aut12_pref_quotient_automata_1110_aut13_Intersection \<equiv> intersect (complement aut12_pref_quotient_automata_1110) aut13" 
definition aut12_pref_quotient_automata_1110_aut13_Invariant::"(aut12_pref_quotient_automata_1110.State\<times>aut13.State) set" where
  "aut12_pref_quotient_automata_1110_aut13_Invariant \<equiv> { ((aut12.State_R aut12.state_level1_Leaf), (aut13.State_R aut13.state_level1_Leaf)), (aut12.State_Leaf, (aut13.State_L aut13.state_level1_Leaf)) }"

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

lemma INV:"inv aut12_pref_quotient_automata_1110_aut13_Intersection aut12_pref_quotient_automata_1110_aut13_Invariant" 
proof -
  have CLOSED:"step_state_set aut12_pref_quotient_automata_1110_aut13_Intersection aut12_pref_quotient_automata_1110_aut13_Invariant \<subseteq> aut12_pref_quotient_automata_1110_aut13_Invariant"
   by (simp only: aut12_pref_quotient_automata_1110_aut13_Intersection_def step_complement, simp only: inv_covered aut12_pref_quotient_automata_1110_aut13_Invariant_def, simp add: intersect_def aut12_pref_quotient_automata_1110_def aut13_def)
  
  have INIT:"initial aut12_pref_quotient_automata_1110_aut13_Intersection \<in> aut12_pref_quotient_automata_1110_aut13_Invariant"
    apply (simp add: aut12_pref_quotient_automata_1110_aut13_Invariant_def aut12_pref_quotient_automata_1110_aut13_Intersection_def aut12_pref_quotient_automata_1110_def aut13_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut12_pref_quotient_automata_1110_aut13_Intersection)\<inter>aut12_pref_quotient_automata_1110_aut13_Invariant = {}"
  proof (simp add:aut12_pref_quotient_automata_1110_aut13_Invariant_def aut12_pref_quotient_automata_1110_def aut13_def intersect_def aut12_pref_quotient_automata_1110_aut13_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut12_pref_quotient_automata_1110_aut13_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut12_pref_quotient_automata_1110_contains_aut13_rev:"(lang_rev aut13) \<subseteq> (lang_rev aut12_pref_quotient_automata_1110)" 
  using INV INT_LANG_REV_EMPTY aut12_pref_quotient_automata_1110_aut13_Intersection_def comp_intersect_emp_then_includes[of aut12_pref_quotient_automata_1110 aut13]
  by auto

theorem aut12_pref_quotient_automata_1110_contains_aut13:"(lang aut13) \<subseteq> (lang aut12_pref_quotient_automata_1110)" 
  using aut12_pref_quotient_automata_1110_contains_aut13_rev by auto

end
