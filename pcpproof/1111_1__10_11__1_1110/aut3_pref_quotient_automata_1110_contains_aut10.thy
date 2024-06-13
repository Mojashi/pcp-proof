theory aut3_pref_quotient_automata_1110_contains_aut10 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut3_pref_quotient_automata_1110" "aut10" "PCPLib.AutomataUtil" begin

definition aut3_pref_quotient_automata_1110_aut10_Intersection::"(PCP.alphabet,(aut3_pref_quotient_automata_1110.State\<times>aut10.State)) da" where
  "aut3_pref_quotient_automata_1110_aut10_Intersection \<equiv> intersect (complement aut3_pref_quotient_automata_1110) aut10" 
definition aut3_pref_quotient_automata_1110_aut10_Invariant::"(aut3_pref_quotient_automata_1110.State\<times>aut10.State) set" where
  "aut3_pref_quotient_automata_1110_aut10_Invariant \<equiv> { (aut3.State_Leaf, (aut10.State_L aut10.state_level1_Leaf)), ((aut3.State_R aut3.state_level1_Leaf), (aut10.State_R aut10.state_level1_Leaf)) }"

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

lemma INV:"inv aut3_pref_quotient_automata_1110_aut10_Intersection aut3_pref_quotient_automata_1110_aut10_Invariant" 
proof -
  have CLOSED:"step_state_set aut3_pref_quotient_automata_1110_aut10_Intersection aut3_pref_quotient_automata_1110_aut10_Invariant \<subseteq> aut3_pref_quotient_automata_1110_aut10_Invariant"
   by (simp only: aut3_pref_quotient_automata_1110_aut10_Intersection_def step_complement, simp only: inv_covered aut3_pref_quotient_automata_1110_aut10_Invariant_def, simp add: intersect_def aut3_pref_quotient_automata_1110_def aut10_def)
  
  have INIT:"initial aut3_pref_quotient_automata_1110_aut10_Intersection \<in> aut3_pref_quotient_automata_1110_aut10_Invariant"
    apply (simp add: aut3_pref_quotient_automata_1110_aut10_Invariant_def aut3_pref_quotient_automata_1110_aut10_Intersection_def aut3_pref_quotient_automata_1110_def aut10_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut3_pref_quotient_automata_1110_aut10_Intersection)\<inter>aut3_pref_quotient_automata_1110_aut10_Invariant = {}"
  proof (simp add:aut3_pref_quotient_automata_1110_aut10_Invariant_def aut3_pref_quotient_automata_1110_def aut10_def intersect_def aut3_pref_quotient_automata_1110_aut10_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut3_pref_quotient_automata_1110_aut10_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut3_pref_quotient_automata_1110_contains_aut10_rev:"(lang_rev aut10) \<subseteq> (lang_rev aut3_pref_quotient_automata_1110)" 
  using INV INT_LANG_REV_EMPTY aut3_pref_quotient_automata_1110_aut10_Intersection_def comp_intersect_emp_then_includes[of aut3_pref_quotient_automata_1110 aut10]
  by auto

theorem aut3_pref_quotient_automata_1110_contains_aut10:"(lang aut10) \<subseteq> (lang aut3_pref_quotient_automata_1110)" 
  using aut3_pref_quotient_automata_1110_contains_aut10_rev by auto

end
