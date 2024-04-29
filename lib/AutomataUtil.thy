theory AutomataUtil
    imports Main Automata PCP
begin

lemma step_complement: "step_state_set (intersect (complement a1) a2) s =
       step_state_set (intersect a1 a2) s"
  by (simp add: intersect_def)

fun step_state_set'::"(alphabet,'s) da \<Rightarrow> 's \<Rightarrow> 's set" where
  "step_state_set' a k = {transition a k C0,  transition a k C1}"

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

end