theory aut10_contains_aut9_pref_quotient_automata_1111 imports Main  "PCPLib.PCP" "PCPLib.Automata" "aut10" "aut9_pref_quotient_automata_1111" "PCPLib.AutomataUtil" begin

definition aut10_aut9_pref_quotient_automata_1111_Intersection::"(PCP.alphabet,(aut10.State\<times>aut9_pref_quotient_automata_1111.State)) da" where
  "aut10_aut9_pref_quotient_automata_1111_Intersection \<equiv> intersect (complement aut10) aut9_pref_quotient_automata_1111" 
definition aut10_aut9_pref_quotient_automata_1111_Invariant::"(aut10.State\<times>aut9_pref_quotient_automata_1111.State) set" where
  "aut10_aut9_pref_quotient_automata_1111_Invariant \<equiv> { ((aut10.State_L aut10.state_level1_Leaf), (aut9.State_R aut9.state_level1_Leaf)), ((aut10.State_R aut10.state_level1_Leaf), (aut9.State_L aut9.state_level1_Leaf)) }"

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

lemma INV:"inv aut10_aut9_pref_quotient_automata_1111_Intersection aut10_aut9_pref_quotient_automata_1111_Invariant" 
proof -
  have CLOSED:"step_state_set aut10_aut9_pref_quotient_automata_1111_Intersection aut10_aut9_pref_quotient_automata_1111_Invariant \<subseteq> aut10_aut9_pref_quotient_automata_1111_Invariant"
   by (simp only: aut10_aut9_pref_quotient_automata_1111_Intersection_def step_complement, simp only: inv_covered aut10_aut9_pref_quotient_automata_1111_Invariant_def, simp add: intersect_def aut10_def aut9_pref_quotient_automata_1111_def)
  
  have INIT:"initial aut10_aut9_pref_quotient_automata_1111_Intersection \<in> aut10_aut9_pref_quotient_automata_1111_Invariant"
    apply (simp add: aut10_aut9_pref_quotient_automata_1111_Invariant_def aut10_aut9_pref_quotient_automata_1111_Intersection_def aut10_def aut9_pref_quotient_automata_1111_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting aut10_aut9_pref_quotient_automata_1111_Intersection)\<inter>aut10_aut9_pref_quotient_automata_1111_Invariant = {}"
  proof (simp add:aut10_aut9_pref_quotient_automata_1111_Invariant_def aut10_def aut9_pref_quotient_automata_1111_def intersect_def aut10_aut9_pref_quotient_automata_1111_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev aut10_aut9_pref_quotient_automata_1111_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma aut10_contains_aut9_pref_quotient_automata_1111_rev:"(lang_rev aut9_pref_quotient_automata_1111) \<subseteq> (lang_rev aut10)" 
  using INV INT_LANG_REV_EMPTY aut10_aut9_pref_quotient_automata_1111_Intersection_def comp_intersect_emp_then_includes[of aut10 aut9_pref_quotient_automata_1111]
  by auto

theorem aut10_contains_aut9_pref_quotient_automata_1111:"(lang aut9_pref_quotient_automata_1111) \<subseteq> (lang aut10)" 
  using aut10_contains_aut9_pref_quotient_automata_1111_rev by auto

end
