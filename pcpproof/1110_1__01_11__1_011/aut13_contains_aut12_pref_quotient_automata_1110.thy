theory aut13_contains_aut12_pref_quotient_automata_1110 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut13" "aut12_pref_quotient_automata_1110" "PCPLib.AutomataUtil" begin

definition aut13_aut12_pref_quotient_automata_1110_Intersection::"(PCP.alphabet,(aut13.State\<times>aut12_pref_quotient_automata_1110.State)) da" where
  "aut13_aut12_pref_quotient_automata_1110_Intersection \<equiv> intersect (complement aut13) aut12_pref_quotient_automata_1110" 
definition aut13_aut12_pref_quotient_automata_1110_Invariant::"(aut13.State\<times>aut12_pref_quotient_automata_1110.State) set" where
  "aut13_aut12_pref_quotient_automata_1110_Invariant \<equiv> { ((aut13.State_R aut13.state_level1_Leaf), (aut12.State_R aut12.state_level1_Leaf)), ((aut13.State_L aut13.state_level1_Leaf), aut12.State_Leaf) }"

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

lemma INV:"inv aut13_aut12_pref_quotient_automata_1110_Intersection aut13_aut12_pref_quotient_automata_1110_Invariant" 
proof -
  have CLOSED:"step_state_set aut13_aut12_pref_quotient_automata_1110_Intersection aut13_aut12_pref_quotient_automata_1110_Invariant \<subseteq> aut13_aut12_pref_quotient_automata_1110_Invariant"
   by (simp only: aut13_aut12_pref_quotient_automata_1110_Intersection_def step_complement, simp only: inv_covered aut13_aut12_pref_quotient_automata_1110_Invariant_def, simp add: intersect_def aut13_def aut12_pref_quotient_automata_1110_def)
  
  have INIT:"initial aut13_aut12_pref_quotient_automata_1110_Intersection \<in> aut13_aut12_pref_quotient_automata_1110_Invariant"
    apply (simp add: aut13_aut12_pref_quotient_automata_1110_Invariant_def aut13_aut12_pref_quotient_automata_1110_Intersection_def aut13_def aut12_pref_quotient_automata_1110_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut13_aut12_pref_quotient_automata_1110_Intersection)\<inter>aut13_aut12_pref_quotient_automata_1110_Invariant = {}"
  proof (simp add:aut13_aut12_pref_quotient_automata_1110_Invariant_def aut13_def aut12_pref_quotient_automata_1110_def intersect_def aut13_aut12_pref_quotient_automata_1110_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut13_aut12_pref_quotient_automata_1110_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut13_contains_aut12_pref_quotient_automata_1110_rev:"(lang_rev aut12_pref_quotient_automata_1110) \<subseteq> (lang_rev aut13)" 
  using INV INT_LANG_REV_EMPTY aut13_aut12_pref_quotient_automata_1110_Intersection_def comp_intersect_emp_then_includes[of aut13 aut12_pref_quotient_automata_1110]
  by auto

theorem aut13_contains_aut12_pref_quotient_automata_1110:"(lang aut12_pref_quotient_automata_1110) \<subseteq> (lang aut13)" 
  using aut13_contains_aut12_pref_quotient_automata_1110_rev by auto

end
