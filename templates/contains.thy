theory {{theory_name}} imports Main  "PCPLib.PCP" "PCPLib.Automata" "{{aut_a_path}}" "{{aut_b_path}}" "PCPLib.AutomataUtil" begin

definition {{aut_a}}_{{aut_b}}_Intersection::"(PCP.alphabet,({{aut_a}}.State\<times>{{aut_b}}.State)) da" where
  "{{aut_a}}_{{aut_b}}_Intersection \<equiv> intersect (complement {{aut_a}}) {{aut_b}}" 
definition {{aut_a}}_{{aut_b}}_Invariant::"({{aut_a}}.State\<times>{{aut_b}}.State) set" where
  "{{aut_a}}_{{aut_b}}_Invariant \<equiv> { {{invariant_set}} }"

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

lemma INV:"inv {{aut_a}}_{{aut_b}}_Intersection {{aut_a}}_{{aut_b}}_Invariant" 
proof -
  have CLOSED:"step_state_set {{aut_a}}_{{aut_b}}_Intersection {{aut_a}}_{{aut_b}}_Invariant \<subseteq> {{aut_a}}_{{aut_b}}_Invariant"
   by (simp only: {{aut_a}}_{{aut_b}}_Intersection_def step_complement, simp only: inv_covered {{aut_a}}_{{aut_b}}_Invariant_def, simp add: intersect_def {{aut_a}}_def {{aut_b}}_def)
  
  have INIT:"initial {{aut_a}}_{{aut_b}}_Intersection \<in> {{aut_a}}_{{aut_b}}_Invariant"
    apply (simp add: {{aut_a}}_{{aut_b}}_Invariant_def {{aut_a}}_{{aut_b}}_Intersection_def {{aut_a}}_def {{aut_b}}_def intersect_def) 
    by simp?
  then show ?thesis using CLOSED INIT by auto
qed

lemma NOT_ACCEPT:"(accepting {{aut_a}}_{{aut_b}}_Intersection)\<inter>{{aut_a}}_{{aut_b}}_Invariant = {}"
  proof (simp add:{{aut_a}}_{{aut_b}}_Invariant_def {{aut_a}}_def {{aut_b}}_def intersect_def {{aut_a}}_{{aut_b}}_Intersection_def)
qed

lemma INT_LANG_REV_EMPTY: "lang_rev {{aut_a}}_{{aut_b}}_Intersection = {}"
  using INV NOT_ACCEPT if_invariant_exists_lang_empty by blast

lemma {{theory_name}}_rev:"(lang_rev {{aut_b}}) \<subseteq> (lang_rev {{aut_a}})" 
  using INV INT_LANG_REV_EMPTY {{aut_a}}_{{aut_b}}_Intersection_def comp_intersect_emp_then_includes[of {{aut_a}} {{aut_b}}]
  by auto

theorem {{theory_name}}:"(lang {{aut_b}}) \<subseteq> (lang {{aut_a}})" 
  using {{theory_name}}_rev by auto

end
