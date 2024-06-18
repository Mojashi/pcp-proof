theory RelaxConstraints
  imports PCPVecRelax
begin

fun incoming_edges::"('in, 'out, 'state) Trans \<Rightarrow> 'state \<Rightarrow> ('in, 'out, 'state) Edge set" where
  "incoming_edges t s = {e | e. e\<in>transition t \<and> dest e = s}"

fun outgoing_edges::"('in, 'out, 'state) Trans \<Rightarrow> 'state \<Rightarrow> ('in, 'out, 'state) Edge set" where
  "outgoing_edges t s = {e | e. e\<in>transition t \<and> src e = s}"


definition is_euler_constraint::"('in, 'out, 'state) Trans \<Rightarrow> 'state \<Rightarrow> (('in, 'out, 'state) Edge) Constraint \<Rightarrow> bool" where
  "is_euler_constraint t s c \<equiv> (
    (op c = EQ) \<and>
    (rhs c = (if s = initial t then -1 else 0) + (if s = accepting t then 1 else 0)) \<and>
    (\<exists> i_list o_list . 
      set i_list = incoming_edges t s \<and> distinct i_list \<and> set o_list = outgoing_edges t s \<and> distinct o_list \<and>
      coeff (lhs c) = coeff ((map (\<lambda>i. (i, 1)) i_list)@(map (\<lambda>i. (i, -1)) o_list)) )
  )"

lemma euc_decompose:
  "coeff (edges_used_count (Move x1a x2 x3 r)) = 
   coeff ((Edge x1a x2 x3 (get_head_state r), 1)#(edges_used_count r))"
  by auto

lemma distinct_member_filter:
  assumes "distinct l" and "List.member l a"
  shows "filter (\<lambda>i. i = a) l = [a]"
  using assms proof(induct l)
  case Nil
  then show ?case by (simp add: member_rec(2))
next
  case (Cons b l)
  then show ?case proof (cases "List.member l a")
    case True
    have A:"a \<noteq> b" using Cons(2) using True member_def by fastforce
    have "filter (\<lambda>i. i = a) l = [a]" using True Cons by auto
    then show ?thesis using A by simp
  next
    case False
    then have F:"filter (\<lambda>i. i = a) l = []" using Cons by (metis (full_types) filter_False member_def)
    then show ?thesis proof(cases "a=b")
      case True
      then show ?thesis apply(simp only:filter.simps) using F by simp
    next
      case F2:False
      then show ?thesis by (metis Cons.prems(2) F2 False member_rec(1))
    qed
  qed
qed

lemma run_euc_per_state:
  fixes t::"('in, 'out, 'state) Trans"
  assumes "has_correspond_edges t r"
      and "is_euler_constraint t s ec"
    shows "assign_lincomb (coeff (edges_used_count r)) (lhs ec) = 
           (if s = get_head_state r then -1 else 0) + (if s = get_last_state r then 1 else 0)"
using assms(1) proof (induct r)
  case (End x)
  then show ?case using assms is_euler_constraint_def by (simp add: cond_case_prod_eta)
next
  case (Move x1a x2 x3 r)
  then have HCE:"has_correspond_edges t r" by simp
  then have IH:"assign_lincomb (coeff (edges_used_count r)) (lhs ec) = 
           (if s = get_head_state r then -1 else 0) + (if s = get_last_state r then 1 else 0)" using Move by blast

  then have IH':"assign_lincomb (coeff (lhs ec)) (edges_used_count r) =
             (if s = get_head_state r then -1 else 0) + (if s = get_last_state r then 1 else 0)"
    using assign_lincomb_comm by metis

  define new_edge where "new_edge = Edge x1a x2 x3 (get_head_state r)"
  have new_edge_exists:"new_edge \<in> transition t" using Move(2) new_edge_def by auto

  obtain i_list and o_list where coeff_ec: "set i_list = incoming_edges t s \<and> distinct i_list \<and> set o_list = outgoing_edges t s \<and> distinct o_list \<and>
      coeff (lhs ec) = coeff ((map (\<lambda>i. (i, 1)) i_list)@(map (\<lambda>i. (i, -1)) o_list))"
    using assms is_euler_constraint_def by fast

  
  have 1:"assign_lincomb (coeff (edges_used_count (Move x1a x2 x3 r))) (lhs ec) = 
           assign_lincomb (coeff ((new_edge, 1)#(edges_used_count r))) (lhs ec)"
    unfolding new_edge_def euc_decompose by auto
  have 2:"... = 
        assign_lincomb (coeff (lhs ec)) ((new_edge, 1)#(edges_used_count r))"
    using assign_lincomb_comm by blast
  have 3:"... = 
        (assign_lincomb (coeff (lhs ec)) [(new_edge, 1)]) + (assign_lincomb (coeff (lhs ec)) (edges_used_count r))"
    by auto
  have 4:"... = (assign_lincomb (coeff (lhs ec)) [(new_edge, 1)]) + 
              (if s = get_head_state r then -1 else 0) + (if s = get_last_state r then 1 else 0)"
    using IH' by auto
  have A:"assign_lincomb (coeff (lhs ec)) [(new_edge, 1)] =
        assign_lincomb (coeff (map (\<lambda>i. (i, 1)) i_list @ map (\<lambda>i. (i, - 1)) o_list)) [(new_edge, 1)]"
   using coeff_ec by simp

  have "... = (if x1a = s then -1 else 0) + (if get_head_state r = s then 1 else 0)"
  proof(cases "x1a = s")
    case T1:True
    then have OUC:"List.member o_list new_edge" using new_edge_def new_edge_exists coeff_ec by (simp add: member_def)
    have "filter (\<lambda>i. i = new_edge) o_list = [new_edge]" using OUC distinct_member_filter by (metis coeff_ec)
    then have B':"sum_list (map (\<lambda>i. if i = new_edge then -1 else 0) o_list) = -1"
        apply(simp only:sum_list_map_filter'[symmetric]) using OUC by simp
    have B:"sum_list (map ((\<lambda>sa. if fst sa = new_edge then snd sa else 0) \<circ> (\<lambda>i. (i, - 1))) o_list) = -1"
        apply(simp only:comp_def) apply simp apply(simp only:snd_conv) using B' by blast
    show ?thesis proof(cases "get_head_state r = s")
    case T2:True
      then have INC:"List.member i_list new_edge" using new_edge_def new_edge_exists coeff_ec by (simp add: member_def)
      
      have "filter (\<lambda>i. i = new_edge) i_list = [new_edge]" using INC distinct_member_filter by (metis coeff_ec)
      then have A':"sum_list (map (\<lambda>i. if i = new_edge then 1 else 0) i_list) = 1"
        apply(simp only:sum_list_map_filter'[symmetric]) using INC by simp
      have A:"sum_list (map ((\<lambda>sa. if fst sa = new_edge then snd sa else 0) \<circ> (\<lambda>i. (i, 1))) i_list) = 1" 
        apply(simp only:comp_def) apply simp apply(simp only:snd_conv) using A' by blast

      then show ?thesis using OUC  using T1 T2 apply simp by(simp only:A B)
    next
      case False
      then have NINC:"\<not>List.member i_list new_edge" using new_edge_def new_edge_exists coeff_ec by (simp add: member_def)
      then have "filter (\<lambda>i. i = new_edge) i_list = []" using filter_empty_conv member_def by fastforce
      then have A':"sum_list (map (\<lambda>i. if i = new_edge then 1 else 0) i_list) = 0"
        apply(simp only:sum_list_map_filter'[symmetric]) using NINC by simp
      have A:"sum_list (map ((\<lambda>sa. if fst sa = new_edge then snd sa else 0) \<circ> (\<lambda>i. (i, 1))) i_list) = 0" 
        apply(simp only:comp_def) apply simp apply(simp only:snd_conv) using A' by blast

      then show ?thesis using OUC  using T1 False apply simp by(simp only:A B)
    qed 
  next
    case F1:False
    then have NOUC:"\<not>List.member o_list new_edge" using new_edge_def new_edge_exists coeff_ec by (simp add: member_def)
    have "filter (\<lambda>i. i = new_edge) o_list = []" using NOUC by (metis (full_types) empty_filter_conv member_def)
    then have B':"sum_list (map (\<lambda>i. if i = new_edge then -1 else 0) o_list) = 0"
        apply(simp only:sum_list_map_filter'[symmetric]) using NOUC by simp
    have B:"sum_list (map ((\<lambda>sa. if fst sa = new_edge then snd sa else 0) \<circ> (\<lambda>i. (i, - 1))) o_list) = 0"
        apply(simp only:comp_def) apply simp apply(simp only:snd_conv) using B' by blast
    then show ?thesis proof(cases "get_head_state r = s")
      case True
      then have INC:"List.member i_list new_edge" using new_edge_def new_edge_exists coeff_ec by (simp add: member_def)
      
      have "filter (\<lambda>i. i = new_edge) i_list = [new_edge]" using INC distinct_member_filter by (metis coeff_ec)
      then have A':"sum_list (map (\<lambda>i. if i = new_edge then 1 else 0) i_list) = 1"
        apply(simp only:sum_list_map_filter'[symmetric]) using INC by simp
      have A:"sum_list (map ((\<lambda>sa. if fst sa = new_edge then snd sa else 0) \<circ> (\<lambda>i. (i, 1))) i_list) = 1" 
        apply(simp only:comp_def) apply simp apply(simp only:snd_conv) using A' by blast

      then show ?thesis using NOUC  using F1 True apply simp by(simp only:A B)
    next
      case False
      then have NINC:"\<not>List.member i_list new_edge" using new_edge_def new_edge_exists coeff_ec by (simp add: member_def)
      then have "filter (\<lambda>i. i = new_edge) i_list = []" using filter_empty_conv member_def by fastforce
      then have A':"sum_list (map (\<lambda>i. if i = new_edge then 1 else 0) i_list) = 0"
        apply(simp only:sum_list_map_filter'[symmetric]) using NINC by simp
      have A:"sum_list (map ((\<lambda>sa. if fst sa = new_edge then snd sa else 0) \<circ> (\<lambda>i. (i, 1))) i_list) = 0" 
        apply(simp only:comp_def) apply simp apply(simp only:snd_conv) using A' by blast

      then show ?thesis using NOUC  using F1 False apply simp by(simp only:A B)
    qed
  qed

  then have "assign_lincomb (coeff (edges_used_count (Move x1a x2 x3 r))) (lhs ec) = 
              (if x1a = s then -1 else 0) + (if get_head_state r = s then 1 else 0) + 
              (if s = get_head_state r then -1 else 0) + (if s = get_last_state r then 1 else 0)"
    using 1 2 3 4 A by argo

  then show "assign_lincomb (coeff (edges_used_count (Move x1a x2 x3 r))) (lhs ec) =
           (if s = get_head_state (Move x1a x2 x3 r) then -1 else 0) + (if s = get_last_state (Move x1a x2 x3 r) then 1 else 0)"
    by auto
qed

lemma euler_constraint_is_relax:
  fixes t::"('in, 'out, 'state) Trans"
  assumes "is_euler_constraint t s ec"
  shows "is_relax_constraint t ec"
unfolding is_relax_constraint_def proof (rule, rule)
  fix r
  assume "is_initial_accept_run t r \<and> length (agg_input r)>0"
  then have LHS:"assign_lincomb (coeff (edges_used_count r)) (lhs ec) = 
          ((if s = initial t then -1 else 0) + (if s = accepting t then 1 else 0))"
    using run_euc_per_state[of t r _ ec] assms by simp
  have OP:"op ec = EQ" using assms is_euler_constraint_def by metis
  have RHS:"rhs ec = ((if s = initial t then -1 else 0) + (if s = accepting t then 1 else 0))"
    using assms is_euler_constraint_def by metis
  show "assign_constraint (coeff (edges_used_count r)) ec"
    using LHS OP RHS
    by (metis Constraint.collapse assign_constraint.simps(3))
qed                  
end