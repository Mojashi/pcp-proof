theory VecTransducer
  imports Main HOL.Option lin Transducer
begin

abbreviation transduce_vec::"('in, 'v lin.LinComb, 'state) Trans \<Rightarrow> 'in list \<Rightarrow> 'v lin.LinComb set" where
  "transduce_vec t ins \<equiv> agg_lincomb ` (transduce t ins)"

fun none_then_zero::"'v lin.LinComb option \<Rightarrow> 'v lin.LinComb" where
  "none_then_zero None = lin.zero" |
  "none_then_zero (Some l) = l"

fun sub_vec_trans::"('in, 'v lin.LinComb, 'state) Trans \<Rightarrow> ('in, 'v lin.LinComb, 'state2) Trans \<Rightarrow> ('in, 'v lin.LinComb, ('state\<times>'state2)) Trans" where
  "sub_vec_trans t1 t2 = (let p = parallel_trans t1 t2 in(
  Trans (initial p)
    ((\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some lin.zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) ` (transition p))
  (accepting p)
))"

lemma agg_lincomb_agg_output_simp[simp]:
  "agg_lincomb (agg_output (Move s i e r)) = add_lincomb (none_then_zero e) (agg_lincomb (agg_output r))"
  apply(cases e) apply simp by simp

lemma sub_lincomb_agg_exc: "agg_input r1 = agg_input r2 \<Longrightarrow> sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2)) = 
    agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2)))"
    proof(induct r1 r2 rule: parallel_run.induct)
      case (1 s1 s2)
      then show ?case by simp
    next
      case (2 e1s e1i e1o r1 e2s e2i e2o r2)
      then have IH: "sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2)) =
        agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2)))" by simp
      have A:"sub_lincomb (agg_lincomb (agg_output (Move e1s (Some e1i) e1o r1))) (agg_lincomb (agg_output (Move e2s (Some e2i) e2o r2))) = 
            sub_lincomb (add_lincomb (none_then_zero e1o) (agg_lincomb (agg_output r1))) (add_lincomb (none_then_zero e2o) (agg_lincomb (agg_output r2)))"
        using agg_lincomb_agg_output_simp by metis
      have B:"... = add_lincomb (sub_lincomb (none_then_zero e1o) (none_then_zero e2o)) (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2)))"
        using sub_add_exc by auto
      have C:"... = add_lincomb (sub_lincomb (none_then_zero e1o) (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))"
        using IH by auto
      have "... = agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move e1s (Some e1i) e1o r1) (Move e2s (Some e2i) e2o r2))))"
        by simp
      then show ?case using A B C by simp
    next
      case (3 e1s e1o r1 r2)
      then have IH: "sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2)) =
        agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2)))" by simp
      have A:"sub_lincomb (agg_lincomb (agg_output (Move e1s None e1o r1))) (agg_lincomb (agg_output r2)) = 
            sub_lincomb (add_lincomb (none_then_zero e1o) (agg_lincomb (agg_output r1))) (agg_lincomb (agg_output r2))"
        using agg_lincomb_agg_output_simp by metis
      have B:"... = add_lincomb (sub_lincomb (none_then_zero e1o) zero) (sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2)))"
        using sub_add_exc by auto
      have C:"... = add_lincomb (sub_lincomb (none_then_zero e1o) zero) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))))"
        using IH by auto
      have "... = agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move e1s None e1o r1) r2)))"
        by simp
      then show ?case using A B C by simp
    next
      case ("4_1" v e2s e2o r2)
      then have IH: "sub_lincomb (agg_lincomb (agg_output (End v))) (agg_lincomb (agg_output r2)) =
        agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (End v) r2)))" by simp
      have A:"sub_lincomb (agg_lincomb (agg_output (End v))) (agg_lincomb (agg_output (Move e2s None e2o r2))) = 
            sub_lincomb (agg_lincomb (agg_output (End v))) (add_lincomb (none_then_zero e2o) (agg_lincomb (agg_output r2)))"
        using agg_lincomb_agg_output_simp by (metis agg_output.simps(1)) 
      then have B:"sub_lincomb (agg_lincomb (agg_output (End v))) (agg_lincomb (agg_output (Move e2s None e2o r2))) = add_lincomb (sub_lincomb zero (none_then_zero e2o)) (sub_lincomb zero (agg_lincomb (agg_output r2)))"
        using sub_add_exc by auto
      have C:"... = add_lincomb (sub_lincomb zero (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (End v) r2))))"
        using IH by auto
      have "... = agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (End v) (Move e2s None e2o r2))))"
        by simp
      then show ?case using A B C by simp
    next
      case ("4_2" v vd vb vc e2s e2o r2)
      then have IH: "sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output r2)) =
        agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move v (Some vd) vb vc) r2)))" by simp
      have A:"sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output (Move e2s None e2o r2))) = 
            sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (add_lincomb (none_then_zero e2o) (agg_lincomb (agg_output r2)))"
        using agg_lincomb_agg_output_simp by metis
      have B:"... = add_lincomb (sub_lincomb zero (none_then_zero e2o)) (sub_lincomb (agg_lincomb (agg_output (Move v (Some vd) vb vc))) (agg_lincomb (agg_output r2)))"
        using sub_add_exc by auto
      have C:"... = add_lincomb (sub_lincomb zero (none_then_zero e2o)) (agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move v (Some vd) vb vc) r2))))"
        using IH by auto
      have "... = agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run (Move v (Some vd) vb vc) (Move e2s None e2o r2))))"
        by simp
      then show ?case using A B C by simp
    next
      case (5 e1s e1i e1o r1 v)
      then show ?case by simp
    next
      case (6 v e2s e2i e2o r2)
      then show ?case by simp
    qed 

lemma diff_vec_trans_sanity:
  fixes t1::"('in, 'v LinComb, 'state) Trans" and
        t2::"('in, 'v LinComb, 'state2) Trans"
  shows "e1\<in>transduce_vec t1 ins \<Longrightarrow> e2\<in>transduce_vec t2 ins \<Longrightarrow> sub_lincomb e1 e2 \<in> transduce_vec (sub_vec_trans t1 t2) ins"
proof -
  assume ASM1:"e1\<in>transduce_vec t1 ins" and ASM2:"e2\<in>transduce_vec t2 ins"
  obtain r1 where R1:"is_initial_accept_run t1 r1 \<and> agg_input r1 = ins \<and> agg_lincomb (agg_output r1) = e1" using ASM1 by blast
  obtain r2 where R2:"is_initial_accept_run t2 r2 \<and> agg_input r2 = ins \<and> agg_lincomb (agg_output r2) = e2" using ASM2 by blast
  have "agg_input (parallel_run r1 r2) = ins" using parallel_run_input R1 by auto
  define r where R:"r = parallel_run r1 r2"
  define e where E:"e = agg_output r"
  have "agg_lincomb (options_to_list (map fst e)) = agg_lincomb (agg_output r1)"
    by (simp add: R E parallel_run_output_l)
  have "agg_lincomb (options_to_list (map snd e)) = agg_lincomb (agg_output r2)"
    by (simp add: R E parallel_run_output_r)
  have A:"sub_lincomb e1 e2 = sub_lincomb (agg_lincomb (agg_output r1)) (agg_lincomb (agg_output r2))" 
    using R1 R2 by fastforce
  define r' where "r' = map_run (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) r"
  have CC:"has_correspond_edges (parallel_trans t1 t2) r \<Longrightarrow> has_correspond_edges (sub_vec_trans t1 t2) r'" 
    apply(simp only: r'_def)
    proof(induct "(\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r))::((('v lin.LinComb option)\<times>('v lin.LinComb option)) \<Rightarrow> 'v lin.LinComb)" 
               "r" rule: map_run.induct)
      case (1 v)
      then show ?case by auto
    next
      case (2 s i r)
      then show ?case by auto
    next
      case (3 s i e r)
      then have IH:"has_correspond_edges (sub_vec_trans t1 t2) (map_run (\<lambda>(l, r). sub_lincomb (none_then_zero l) (none_then_zero r)) r)" by auto
      then have "Edge s i (Some e) (get_head_state r) \<in> transition (parallel_trans t1 t2)" using 3 by auto
      then have "(\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some lin.zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) (Edge s i (Some e) (get_head_state r)) \<in> ((\<lambda>t. Edge (src t) (input t)
                    (case out t of None \<Rightarrow> Some zero | Some (l, r) \<Rightarrow> Some (sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) `
              transition (parallel_trans t1 t2))" by blast
      then have A:"(\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some lin.zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) (Edge s i (Some e) (get_head_state r)) \<in> transition (sub_vec_trans t1 t2)"
        apply (simp only: sub_vec_trans.simps) by simp
      
      show ?case proof(cases e)
        case (Pair a b)
        then have "(\<lambda>t. Edge (src t) (input t) (case (out t) of None \<Rightarrow> (Some lin.zero) | Some (l,r) \<Rightarrow> Some(sub_lincomb (none_then_zero l) (none_then_zero r))) (dest t)) (Edge s i (Some e) (get_head_state r))
               = Edge s i (Some(sub_lincomb (none_then_zero a) (none_then_zero b))) (get_head_state r)" by simp
        then have K:"Edge s i (Some(sub_lincomb (none_then_zero a) (none_then_zero b))) (get_head_state r) \<in> transition (sub_vec_trans t1 t2)"
          using A by auto
        show ?thesis apply(simp only:map_run.simps) apply(simp only: Pair has_correspond_edges.simps) apply(rule conjI) using K IH 
          apply (simp add: map_run_head) using K IH by (simp add: map_run_head)
      qed
    qed
  have K:"has_correspond_edges (parallel_trans t1 t2) r" using R parallel_run_has_correspond_edges R1 R2 by metis

  have "get_head_state r' = get_head_state (parallel_run r1 r2)"
    using r'_def R map_run_head[of "(\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r))" r] by blast
  then have R'HEAD:"get_head_state r' = initial (sub_vec_trans t1 t2)"
    using R1 R2 by (simp add: parallel_run_head)

  have "get_last_state r' = get_last_state (parallel_run r1 r2)"
    using r'_def R map_run_last[of "(\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r))" r] by blast
  then have R'LAST:"get_last_state r' = accepting (sub_vec_trans t1 t2)"
    using R1 R2 by (simp add:parallel_run_last)

  have C:"is_initial_accept_run (sub_vec_trans t1 t2) r'" using r'_def R R1 R2 R'HEAD R'LAST
    using CC[OF K] by blast

  then have I:"agg_input r' = ins" using r'_def map_run_input 
    using R \<open>agg_input (parallel_run r1 r2) = ins\<close> by blast
  have O':"agg_output r' = map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2))"
    using r'_def map_run_output R by blast
  then have "sub_lincomb e1 e2 = 
    agg_lincomb (map (\<lambda>(l,r). sub_lincomb (none_then_zero l) (none_then_zero r)) (agg_output (parallel_run r1 r2)))"
    using sub_lincomb_agg_exc using R1 R2 by metis
  then have "sub_lincomb e1 e2 = agg_lincomb (agg_output r')"
    using r'_def using O' by presburger

  then show ?thesis using C I by blast
qed

fun edges_used_count::"('in, 'out, 'state) Run \<Rightarrow> (('in, 'out, 'state) Edge \<Rightarrow> rat)" where
  "edges_used_count r = (\<lambda>e. rat_of_nat (count_list (run_to_edges_list r) e))"

abbreviation mult_time::"(('in, 'v LinComb, 'state) Edge \<Rightarrow> rat) \<Rightarrow> ('in, 'v LinComb, 'state) Edge \<Rightarrow> 'v LinComb \<Rightarrow> 'v LinComb" where
  "mult_time euc e s \<equiv> add_lincomb s (mult_lincomb (none_then_zero (out e)) (euc e))"

interpretation mult_time_comm: comp_fun_commute_on UNIV "mult_time euc" using comp_fun_commute_on_def by force

fun calc_output_from_euc::"('in, 'v LinComb, 'state) Edge set \<Rightarrow> (('in, 'v LinComb, 'state) Edge \<Rightarrow> rat) \<Rightarrow> ('v LinComb)" where
  "calc_output_from_euc es euc = Finite_Set.fold (\<lambda>e s. add_lincomb s (mult_lincomb (none_then_zero (out e)) (euc e))) zero es"

fun calc_output_from_euc_list::"('in, 'v LinComb, 'state) Edge list \<Rightarrow> (('in, 'v LinComb, 'state) Edge \<Rightarrow> rat) \<Rightarrow> ('v LinComb)" where
  "calc_output_from_euc_list es euc = fold (\<lambda>e s. add_lincomb s (mult_lincomb (none_then_zero (out e)) (euc e))) es zero"

lemma calc_output_from_euc_e:
  shows "calc_output_from_euc (set es) euc = calc_output_from_euc_list (remdups es) euc"
  using mult_time_comm.fold_set_fold_remdups[of es] by simp

lemma calc_output_from_euc_e':
  assumes "distinct es"
  shows "calc_output_from_euc (set es) euc = calc_output_from_euc_list es euc"
  apply (simp only:calc_output_from_euc_e) using assms by (metis distinct_remdups_id)

lemma calc_output_from_euc_insert:
  assumes "e\<notin>set es"
  shows "calc_output_from_euc (insert e (set es)) euc = add_lincomb (calc_output_from_euc (set es) euc) (mult_lincomb (none_then_zero (out e)) (euc e))"
  apply (simp only:calc_output_from_euc_e)
  using assms 
  by (metis (mono_tags, lifting) List.finite_set calc_output_from_euc.simps calc_output_from_euc_e mult_time_comm.fold_insert top_greatest)

lemma calc_output_from_euc_insert':
  assumes "e\<notin>es" and "finite es"
  shows "calc_output_from_euc (insert e es) euc = add_lincomb (calc_output_from_euc es euc) (mult_lincomb (none_then_zero (out e)) (euc e))"
proof -
  obtain esl where "es = set esl \<and> distinct esl" using finite_distinct_list[OF assms(2)] by blast
  then show ?thesis using assms(1) calc_output_from_euc_insert by blast
qed

lemma calc_output_from_euc_list_hd:
  assumes "distinct (e#es)"   
  shows "calc_output_from_euc_list (e#es) euc = add_lincomb (calc_output_from_euc_list es euc) (mult_lincomb (none_then_zero (out e)) (euc e))"
  using assms
  by (metis calc_output_from_euc_e' calc_output_from_euc_insert distinct.simps(2) list.simps(15))

lemma calc_output_from_euc_no_contain:
  fixes es::"(('in, 'v LinComb, 'state) Edge) set" and new_edge::"('in, 'v LinComb, 'state) Edge"
  assumes "new_edge \<notin> es" and "finite es"
  shows "calc_output_from_euc es (\<lambda>e. if e = new_edge then (old e + 1) else old e) = calc_output_from_euc es old"
using assms(1) proof(induct es rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case (insert x F)
  define new_euc where "new_euc = (\<lambda>e. if e = new_edge then (old e + 1) else old e)"
  then have IH:"calc_output_from_euc F new_euc = calc_output_from_euc F old"
    using insert by auto
  have NC:"x \<noteq> new_edge" using insert assms by blast
  then have A:"calc_output_from_euc (insert x F) new_euc = mult_time new_euc x (calc_output_from_euc F old)"
    using calc_output_from_euc_insert'[OF insert(2) insert(1), of new_euc] IH by simp
  have B:"calc_output_from_euc (insert x F) old = mult_time new_euc x (calc_output_from_euc F old)" 
     using calc_output_from_euc_insert' insert.hyps(1) insert.hyps(2) new_euc_def NC by auto
  then show ?case using A B using new_euc_def by fastforce
qed 

lemma calc_output_from_euc_add_1':
  assumes "distinct (new_edge#es')"
  shows "calc_output_from_euc_list (new_edge#es') (\<lambda>e. if e = new_edge then (old e + 1) else old e) =
         add_lincomb (calc_output_from_euc_list (new_edge#es') old) (none_then_zero (out new_edge))"
proof -
  have "calc_output_from_euc_list (new_edge#es') (\<lambda>e. if e = new_edge then (old e + 1) else old e) =
        add_lincomb (calc_output_from_euc_list es' (\<lambda>e. if e = new_edge then (old e + 1) else old e))
                    (mult_lincomb (none_then_zero (out new_edge)) (if new_edge = new_edge then old new_edge + 1 else old new_edge))
        "  apply (rule calc_output_from_euc_list_hd) using assms by simp
  
  have "calc_output_from_euc (set es') (\<lambda>e. if e = new_edge then (old e + 1) else old e) = calc_output_from_euc (set es') old"
    using calc_output_from_euc_no_contain[of new_edge "set es'"] using assms by auto
  have A:"calc_output_from_euc_list es' (\<lambda>e. if e = new_edge then (old e + 1) else old e) = calc_output_from_euc_list es' old"
    using assms calc_output_from_euc_e' 
    using \<open>calc_output_from_euc (set es') (\<lambda>e. if e = new_edge then old e + 1 else old e) = calc_output_from_euc (set es') old\<close> by fastforce
  then have "calc_output_from_euc_list (new_edge#es') (\<lambda>e. if e = new_edge then (old e + 1) else old e) = 
            add_lincomb (calc_output_from_euc_list es' old)
                        (mult_lincomb (none_then_zero (out new_edge)) (old new_edge + 1))"
    using calc_output_from_euc_list_hd A 
    using \<open>calc_output_from_euc_list (new_edge # es') (\<lambda>e. if e = new_edge then old e + 1 else old e) = add_lincomb (calc_output_from_euc_list es' (\<lambda>e. if e = new_edge then old e + 1 else old e)) (mult_lincomb (none_then_zero (out new_edge)) (if new_edge = new_edge then old new_edge + 1 else old new_edge))\<close> by presburger
  
  have "\<forall>v. ((old new_edge) * (none_then_zero (out new_edge)) v + none_then_zero (out new_edge) v) = 
            ((old new_edge + 1) * none_then_zero (out new_edge) v)" 
    by (metis (no_types, opaque_lifting) diff_eq_eq left_diff_distrib mult_1)
  then have K:"\<forall>v. ( fold (\<lambda>e s v. s v + old e * none_then_zero (out e) v) es' zero v + old new_edge * none_then_zero (out new_edge) v +
         none_then_zero (out new_edge) v) =
    ( fold (\<lambda>e s v. s v + old e * none_then_zero (out e) v) es' zero v +
         (old new_edge + 1) * none_then_zero (out new_edge) v)" by simp
  have "add_lincomb (calc_output_from_euc_list (new_edge#es') old) (none_then_zero (out new_edge)) =
        add_lincomb (calc_output_from_euc_list es' old)
                    (mult_lincomb (none_then_zero (out new_edge)) (old new_edge + 1))"
    apply(simp only:calc_output_from_euc_list_hd[OF assms]) by (simp add:K)
  then show ?thesis
    using \<open>calc_output_from_euc_list (new_edge # es') (\<lambda>e. if e = new_edge then old e + 1 else old e) = add_lincomb (calc_output_from_euc_list es' old) (mult_lincomb (none_then_zero (out new_edge)) (old new_edge + 1))\<close> by force
qed


lemma calc_output_from_euc_add_1:
  assumes "new_edge \<in> es" and "finite es"
  shows "calc_output_from_euc es (\<lambda>e. if e = new_edge then (old e + 1) else old e) =
         add_lincomb (calc_output_from_euc es old) (none_then_zero (out new_edge))"
proof -
  obtain esl' where ESL':"set esl'= (es - {new_edge}) \<and>distinct esl'" using finite_distinct_list assms by auto
  define esl where "esl = new_edge#esl'"
  then have D:"distinct (new_edge#esl')" using ESL' by auto
  have U:"set (new_edge#esl') = es" using ESL' using assms(1) by force
  have "calc_output_from_euc_list esl (\<lambda>e. if e = new_edge then (old e + 1) else old e) =
         add_lincomb (calc_output_from_euc_list esl old) (none_then_zero (out new_edge))"
    unfolding esl_def using calc_output_from_euc_add_1'[OF D] by blast
  then show ?thesis using calc_output_from_euc_e'[OF D] using esl_def U by simp
qed

definition is_relax_constraint::"('in, 'out, 'state) Trans \<Rightarrow> (('in, 'out, 'state) Edge) Constraint \<Rightarrow> bool" where
  "is_relax_constraint t c \<equiv> \<forall>r. is_initial_accept_run t r \<and> length (agg_input r)>0 \<longrightarrow> assign_constraint (edges_used_count r) c"

definition is_relax_mip::"('in, 'out, 'state) Trans \<Rightarrow> (('in, 'out, 'state) Edge) MIP \<Rightarrow> bool" where
  "is_relax_mip t c \<equiv> \<forall>r. is_initial_accept_run t r \<and> length (agg_input r)>0 \<longrightarrow> assign_mip (edges_used_count r) c"

lemma relax_cons_relax:
  fixes t::"('in, 'out, 'state) Trans"
  assumes "is_relax_constraint t c1" and "is_relax_mip t c2"
  shows "is_relax_mip t (c1#c2)"
  using assms is_relax_constraint_def is_relax_mip_def 
  by (metis assign_mip.elims(2) assign_mip.elims(3) list_all_simps(1))

lemma relax_concat_relax:
  fixes t::"('in, 'out, 'state) Trans"
  assumes "is_relax_mip t c1" and "is_relax_mip t c2"
  shows "is_relax_mip t (c1@c2)"
  using assms apply(induct c1) apply (simp add: assms(2)) using relax_cons_relax
  by (simp add: assign_mip.elims(3) is_relax_mip_def)

lemma relax_output:
  fixes t::"('in, 'v LinComb, 'state) Trans"
  assumes "finite (transition t)"
  shows "has_correspond_edges t r \<Longrightarrow> calc_output_from_euc (transition t) (edges_used_count r) = agg_lincomb (agg_output r)"
proof(induct r)
  case (End x)
  obtain es where ES:"set es = (transition t) \<and> distinct es" using assms finite_distinct_list by auto
  have "calc_output_from_euc (set es) zero = zero" apply (simp only:calc_output_from_euc_e) apply(induct es) by simp_all
  then have "calc_output_from_euc (transition t) zero = zero" using ES by simp
  then show ?case by simp
next
  case (Move x1a x2 x3 r)
  define prev where "prev = agg_lincomb (agg_output r)" 
  have "agg_lincomb (agg_output (Move x1a x2 x3 r)) = add_lincomb prev (none_then_zero x3)"
    unfolding prev_def 
  proof -
    have "add_lincomb (none_then_zero x3) (agg_lincomb (agg_output r)) = add_lincomb (agg_lincomb (agg_output r)) (none_then_zero x3)"
      by (simp add: add.commute)
    then show "agg_lincomb (agg_output (Move x1a x2 x3 r)) = add_lincomb (agg_lincomb (agg_output r)) (none_then_zero x3)"
      by (metis (no_types) agg_lincomb_agg_output_simp)
  qed
  define new_edge where "new_edge = Edge x1a x2 x3 (get_head_state r)"
  have IN:"new_edge \<in> transition t" using Move using new_edge_def by fastforce
  have EUC:"edges_used_count (Move x1a x2 x3 r) = (\<lambda>e. if e = new_edge then (edges_used_count r e + 1) else edges_used_count r e)"
    using new_edge_def by fastforce
  have A:"calc_output_from_euc (transition t) (edges_used_count (Move x1a x2 x3 r)) = 
              add_lincomb (calc_output_from_euc (transition t) (edges_used_count r)) (none_then_zero (out new_edge))"
    unfolding EUC using calc_output_from_euc_add_1[OF IN assms(1), of "edges_used_count r"] by simp
  have "... = agg_lincomb (agg_output (Move x1a x2 x3 r))"
    using Move.hyps Move.prems \<open>agg_lincomb (agg_output (Move x1a x2 x3 r)) = add_lincomb prev (none_then_zero x3)\<close> new_edge_def prev_def by fastforce
  then show ?case using A by simp
qed 

end