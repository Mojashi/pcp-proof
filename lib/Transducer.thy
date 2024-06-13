theory Transducer
  imports Main HOL.Option
begin

datatype ('in, 'out, 'state) Edge = Edge 
  (src: "'state") 
  (input:"'in option") 
  (out:"'out option") 
  (dest: "'state")

datatype ('in, 'out, 'state) Run = End 'state | Move 'state "'in option" "'out option" "('in, 'out, 'state) Run"

datatype ('in, 'out, 'state) Trans = Trans
    (initial: "'state")
    (transition: "(('in, 'out, 'state) Edge) set")
    (accepting: "'state")

fun get_head_state::"('in, 'out, 'state) Run \<Rightarrow> 'state" where
  "get_head_state (End s) = s" |
  "get_head_state (Move s i e r) = s"
fun get_last_state::"('in, 'out, 'state) Run \<Rightarrow> 'state" where
  "get_last_state (End s) = s" |
  "get_last_state (Move s i e r) = get_last_state r"

fun has_correspond_edges::"('in, 'out, 'state) Trans \<Rightarrow> ('in, 'out, 'state) Run \<Rightarrow> bool" where
  "has_correspond_edges t (End s) = True" |
  "has_correspond_edges t (Move s i e r) = (((Edge s i e (get_head_state r)) \<in> (transition t)) \<and> (has_correspond_edges t r))"

fun run_to_edges_list::"('in, 'out, 'state) Run \<Rightarrow> (('in, 'out, 'state) Edge) list" where
  "run_to_edges_list (End s) = []" |
  "run_to_edges_list (Move s i e r) = ((Edge s i e (get_head_state r)) # (run_to_edges_list r))"

abbreviation is_accept_run::"('in, 'out, 'state) Trans \<Rightarrow> ('in, 'out, 'state) Run \<Rightarrow> bool" where
  "is_accept_run t r \<equiv> (get_last_state r) = accepting t \<and> has_correspond_edges t r"

abbreviation is_initial_accept_run::"('in, 'out, 'state) Trans \<Rightarrow> ('in, 'out, 'state) Run \<Rightarrow> bool" where
  "is_initial_accept_run t r \<equiv> is_accept_run t r \<and> (get_head_state r = initial t)"

fun option_to_list::"'a option \<Rightarrow> 'a list" where
  "option_to_list None = []"|
  "option_to_list (Some a) = [a]"

fun options_to_list::"'a option list \<Rightarrow> 'a list" where
  "options_to_list [] = []" |
  "options_to_list (a#as) = (option_to_list a)@(options_to_list as)"

fun agg_input::"('in, 'out, 'state) Run \<Rightarrow> 'in list" where
  "agg_input (End s) = []" |
  "agg_input (Move s i e r) = (option_to_list i)@(agg_input r)"

fun agg_output::"('in, 'out, 'state) Run \<Rightarrow> 'out list" where
  "agg_output (End s) = []" |
  "agg_output (Move s i e r) = (option_to_list e)@(agg_output r)"

abbreviation transduce_runs::"('in, 'out, 'state) Trans \<Rightarrow> 'in list \<Rightarrow> ('in, 'out, 'state) Run set" where
  "transduce_runs t is \<equiv> {r | r. is_initial_accept_run t r \<and> agg_input r = is}"
                                          
abbreviation transduce::"('in, 'out, 'state) Trans \<Rightarrow> 'in list \<Rightarrow> ('out list) set" where
  "transduce t is \<equiv> {agg_output p | p. p \<in> transduce_runs t is}"

definition compose_trans::"('in, 'mid, 'state) Trans \<Rightarrow> ('mid, 'out, 'state2) Trans \<Rightarrow> ('in, 'out, 'state\<times>'state2) Trans" where
  "compose_trans t1 t2 \<equiv> Trans (initial t1, initial t2) (
    {Edge (src e1, src e2) (input e1) (out e2) (dest e1, dest e2) | e1 e2. e1\<in>transition t1 \<and> e2\<in>transition t2 \<and> out e1 = input e2} \<union>
    {Edge (s1, src e2) None (out e2) (s1, dest e2) | (s1::'state) e2. e2\<in>transition t2 \<and> input e2 = None} \<union>
    {Edge (src e1, s2) (input e1) None (dest e1, s2) | (s2::'state2) e1. e1\<in>transition t1 \<and> out e1 = None} 
  )
  (accepting t1, accepting t2)"

fun compose_run::"('in, 'mid, 'state) Run \<Rightarrow> ('mid, 'out, 'state2) Run \<Rightarrow> ('in, 'out, 'state\<times>'state2) Run" where
  "compose_run (End s1) (End s2) = End (s1, s2)" |
  "compose_run (Move e1s e1i None r1) r2 = Move (e1s, get_head_state r2) e1i None (compose_run r1 r2)" |
  "compose_run r1 (Move e2s None e2o r2) =  Move (get_head_state r1, e2s) None e2o (compose_run r1 r2)" |
  "compose_run (Move e1s e1i (Some e1o) r1) (Move e2s (Some e2i) e2o r2) =
      Move (e1s,e2s) e1i e2o (compose_run r1 r2)" |
  "compose_run (End s1) (Move e2s (Some e2i) e2o r2) =  End (s1, e2s)" |
  "compose_run (Move e1s e1i (Some e1o) r1) (End s2) = End (e1s, s2)"
  

lemma compose_run_head[simp]:
  fixes r1::"('in, 'mid, 'state) Run" and
        r2::"('mid, 'out, 'state2) Run"
  shows "get_head_state (compose_run r1 r2) = (get_head_state r1, get_head_state r2)"
  by(cases  rule:compose_run.cases[of "(r1,r2)"], simp_all)

lemma compose_run_input[simp]:
  shows "agg_output r1 = agg_input r2 \<Longrightarrow>
         agg_input (compose_run r1 r2) = agg_input r1"
  apply (induct r1 r2 rule:compose_run.induct) by simp_all

lemma compose_run_output[simp]:
  shows "agg_output r1 = agg_input r2 \<Longrightarrow>
         agg_output (compose_run r1 r2) = agg_output r2"
  apply (induct r1 r2 rule:compose_run.induct) by simp_all

lemma compose_run_accept:
  assumes "t = compose_trans t1 t2"
  shows "agg_output r1 = agg_input r2 \<Longrightarrow>
         is_accept_run t1 r1 \<Longrightarrow>
         is_accept_run t2 r2 \<Longrightarrow>
         is_accept_run t (compose_run r1 r2)"
proof (induct r1 r2 rule:compose_run.induct)
  case (1 s1 s2)
  have A1:"s1 = accepting t1" using 1 by simp
  have A2:"s2 = accepting t2" using 1 by simp
  have "(s1, s2) = accepting t" apply(simp only: A1 A2) apply(simp only: assms) apply(simp only:compose_trans_def) by simp
  have "get_last_state (End (s1, s2)) = accepting t" using assms A1 A2 \<open>(s1, s2) = accepting t\<close> by force
  then show ?case by simp
next
  case (2 e1s e1i r1 r2)
  then have IH:"is_accept_run t (compose_run r1 r2)" by simp
  have LAST:"get_last_state (Move (e1s, get_head_state r2) e1i None (compose_run r1 r2)) = accepting t" 
    using IH by auto

  have HEAD:"(get_head_state r1, get_head_state r2) = (get_head_state (compose_run r1 r2)) "
    using compose_run_head by auto
  have "Edge e1s e1i None (get_head_state r1) \<in> transition t1" using 2 by simp
  then have "(Edge (e1s, get_head_state r2) e1i None (get_head_state (compose_run r1 r2)) ) \<in> transition t"
    using assms compose_trans_def[of t1 t2] HEAD by fastforce

  then have EDGES:"has_correspond_edges t (Move (e1s, get_head_state r2) e1i None (compose_run r1 r2))" 
    using IH by simp
  show "is_accept_run t (compose_run (Move e1s e1i None r1) r2)"
    apply(simp only: compose_run.simps) using 2 LAST using EDGES by simp
next
  case ("3_1" v e2s e2o r2)
  then have IH:"is_accept_run t (compose_run (End v) r2)" by simp

  have HEAD:"(v, e2s) = get_head_state (compose_run (End v) (Move e2s None e2o r2))"
    using compose_run_head[of "End v" r2] by simp

  have "Edge (v, e2s) None e2o (v, get_head_state r2) \<in> transition t"
    apply(simp only: assms compose_trans_def) apply(simp) using "3_1"(3) "3_1"(4) apply auto 
      by (metis Edge.sel(1) Edge.sel(2) Edge.sel(3) Edge.sel(4))

  then have "has_correspond_edges t (Move (get_head_state (End v), e2s) None e2o (compose_run (End v) r2))"
    using IH by (metis (no_types, lifting) compose_run_head get_head_state.simps(1) has_correspond_edges.simps(2))

  then show ?case apply(simp only: compose_run.simps) using IH by force
next 
  case ("3_2" v va vd vc e2s e2o r2)

  then have IH:"is_accept_run t (compose_run (Move v va (Some vd) vc) r2)" by simp

  have HEAD:"(v, e2s) = get_head_state (compose_run (Move v va (Some vd) vc) (Move e2s None e2o r2))"
    using compose_run_head[of "(Move v va (Some vd) vc)" r2] by simp

  have "Edge (v, e2s) None e2o (v, get_head_state r2) \<in> transition t"
    apply(simp only: assms compose_trans_def) apply(simp) using "3_2"(3) "3_2"(4) apply auto 
      by (metis Edge.sel(1) Edge.sel(2) Edge.sel(3) Edge.sel(4))

  then have "has_correspond_edges t (Move (get_head_state (Move v va (Some vd) vc), e2s) None e2o (compose_run (Move v va (Some vd) vc) r2))"
    using IH by (metis (mono_tags, lifting) compose_run_head get_head_state.simps(2) has_correspond_edges.simps(2))
  then show ?case apply(simp only: compose_run.simps) using IH by force
next
  case (4 e1s e1i e1o r1 e2s e2i e2o r2)
  assume "agg_output (Move e1s e1i (Some e1o) r1) = agg_input (Move e2s (Some e2i) e2o r2)"
  then have IEQ:"e2i = e1o" by simp
  have IH:"is_accept_run t (compose_run r1 r2)" using 4 by simp
  have HEAD:"(e1s, e2s) = get_head_state (compose_run (Move e1s e1i (Some e1o) r1) (Move e2s (Some e2i) e2o r2))"
    using compose_run_head by simp
  have "Edge (e1s, e2s) e1i e2o (get_head_state r1, get_head_state r2) \<in> transition t"
    apply(simp only: assms compose_trans_def) apply(simp) using 4(3) 4(4) apply auto apply(simp only:IEQ)
    by (metis Edge.sel(1) Edge.sel(2) Edge.sel(3) Edge.sel(4))

  then have "has_correspond_edges t (Move (e1s,e2s) e1i e2o (compose_run r1 r2))"
    using IH by (metis (mono_tags, lifting) compose_run_head  has_correspond_edges.simps(2))
  then show ?case apply(simp only: compose_run.simps) using IH by force
next
  case (5 s1 e2s e2i e2o r2)
  then show ?case by simp
next
  case (6 e1s e1i e1o r1 s2)
  then show ?case by simp
qed 

fun concat_run::"('in, 'out, 'state) Run \<Rightarrow> ('in, 'out, 'state) Run \<Rightarrow> ('in, 'out, 'state) Run" where
  "concat_run (End s) r2 = r2" |
  "concat_run (Move f i e r) r2 = Move f i e (concat_run r r2)"

lemma concat_agg_input:
  "agg_input (concat_run r1 r2) = (agg_input r1) @ (agg_input r2)"
  apply (induct r1) by simp_all

lemma concat_agg_output:
  "agg_output (concat_run r1 r2) = (agg_output r1) @ (agg_output r2)"
apply (induct r1) by simp_all

lemma concat_run_head:
  "get_last_state r1 = get_head_state r2 \<Longrightarrow> get_head_state (concat_run r1 r2) = get_head_state r1"
  apply(induct r1) apply simp by simp

lemma concat_run_last:
  "get_last_state r1 = get_head_state r2 \<Longrightarrow> get_last_state (concat_run r1 r2) = get_last_state r2"
  apply(induct r1) apply simp by simp

lemma concat_run_ex:
  "has_correspond_edges t r1 \<Longrightarrow> has_correspond_edges t r2 \<Longrightarrow> get_last_state r1 = get_head_state r2 \<Longrightarrow> has_correspond_edges t (concat_run r1 r2)"
proof(induct r1)
  case (End x)
  then show ?case by simp
next
  case (Move x1a x2 x3 r1)
  then have IH: "has_correspond_edges t (concat_run r1 r2)" by simp
  then have "has_correspond_edges t r1" using Move by simp
  have H:"get_head_state (concat_run r1 r2) = get_head_state r1" 
    using  concat_run_head  Move.prems(3) by auto
  show "has_correspond_edges t (concat_run (Move x1a x2 x3 r1) r2)"
    apply(simp only: concat_run.simps has_correspond_edges.simps)
    apply(rule conjI) using H Move.prems(1) apply fastforce using IH by blast
qed

fun parallel_trans::"('in, 'out, 'state) Trans \<Rightarrow> ('in, 'out2, 'state2) Trans \<Rightarrow> ('in, ('out option \<times> ('out2 option)), ('state\<times>'state2)) Trans" where
  "parallel_trans t1 t2 = (
    Trans ((initial t1), (initial t2))  
    ({Edge (src e1, src e2) (input e1) (Some(out e1, out e2)) (dest e1, dest e2) | e1 e2. e1\<in>transition t1 \<and> e2\<in>transition t2 \<and> input e1 = input e2} \<union>
    {Edge (s1, src e2) None (Some(None, out e2)) (s1, dest e2) | (s1::'state) e2. e2\<in>transition t2 \<and> input e2 = None} \<union>
    {Edge (src e1, s2) None (Some(out e1, None)) (dest e1, s2) | (s2::'state2) e1. e1\<in>transition t1 \<and> input e1 = None}
  )
  ((accepting t1), (accepting t2))
)"


abbreviation is_total_trans::"('in, 'out, 'state) Trans \<Rightarrow> bool" where
  "is_total_trans t \<equiv> \<forall>ins. transduce_runs t ins \<noteq> {}"

fun parallel_run::"('in,  'out, 'state) Run \<Rightarrow> ('in, 'out2, 'state2) Run \<Rightarrow> ('in, ('out option)\<times>('out2 option), 'state\<times>'state2) Run" where
  "parallel_run (End s1) (End s2) = End (s1, s2)" |
  "parallel_run (Move e1s (Some e1i) e1o r1) (Move e2s (Some e2i) e2o r2) =
      Move (e1s,e2s) (Some e1i) (Some(e1o, e2o)) (parallel_run r1 r2)" |
  "parallel_run (Move e1s None e1o r1) r2 =
      Move (e1s, get_head_state r2) None (Some (e1o, None)) (parallel_run r1 r2)" |
  "parallel_run r1 (Move e2s None e2o r2) =
      Move (get_head_state r1, e2s) None (Some (None, e2o)) (parallel_run r1 r2)" |
  "parallel_run (Move e1s (Some e1i) e1o r1) r2 =
      Move (e1s, get_head_state r2) (Some e1i) (Some (e1o, None)) (parallel_run r1 r2)" |
  "parallel_run r1 (Move e2s (Some e2i) e2o r2) =
      Move (get_head_state r1, e2s) None (Some (None, e2o)) (parallel_run r1 r2)"

lemma parallel_run_input: "agg_input (parallel_run r1 r2) = agg_input r1"
  apply(induct r1 r2 rule:parallel_run.induct) by simp_all

lemma parallel_run_output_l: "options_to_list (map fst (agg_output (parallel_run r1 r2))) = agg_output r1"
  apply(induct r1 r2 rule:parallel_run.induct) by simp_all

lemma parallel_run_output_r: "options_to_list (map snd (agg_output (parallel_run r1 r2))) = agg_output r2"
  apply(induct r1 r2 rule:parallel_run.induct) by simp_all

lemma parallel_run_head:"get_head_state (parallel_run r1 r2) = (get_head_state r1, get_head_state r2)"
  apply(cases r1 r2 rule:parallel_run.elims) by simp_all

lemma parallel_run_last:"get_last_state (parallel_run r1 r2) = (get_last_state r1, get_last_state r2)"
  apply(induct r1 r2 rule:parallel_run.induct) by simp_all

lemma parallel_run_has_correspond_edges: "agg_input r1 = agg_input r2 \<Longrightarrow> has_correspond_edges t1 r1 \<Longrightarrow> has_correspond_edges t2 r2 \<Longrightarrow>
  has_correspond_edges (parallel_trans t1 t2) (parallel_run r1 r2)"
proof(induct r1 r2 rule:parallel_run.induct)
  case (1 s1 s2)
  then show ?case by simp
next
  case (2 e1s e1i e1o r1 e2s e2i e2o r2)
  then have IH:"has_correspond_edges (parallel_trans t1 t2) (parallel_run r1 r2)" by auto
  have E1:"Edge e1s (Some e1i) e1o (get_head_state r1) \<in> transition t1" using 2 by auto
  have "e1i = e2i" using 2 by auto
  have E2:"Edge e2s (Some e1i) e2o (get_head_state r2) \<in> transition t2" using 2 by auto
  have E:"Edge (e1s, e2s) (Some e1i) (Some(e1o, e2o)) (get_head_state r1, get_head_state r2) \<in> transition (parallel_trans t1 t2)"
    using E1 E2 by force
  show ?case apply(simp only: parallel_run.simps) apply(simp only:has_correspond_edges.simps) apply(rule conjI)
    using E parallel_run_head apply metis using IH by simp
next
  case (3 e1s e1o r1 r2)
  have "Edge e1s None e1o (get_head_state r1) \<in> transition t1" using 3 by simp
  then have E:"Edge (e1s, get_head_state r2) None (Some(e1o, None)) (get_head_state r1, get_head_state r2) \<in> transition (parallel_trans t1 t2)"
    by force
  then show ?case apply(simp only: parallel_run.simps) apply(simp only:has_correspond_edges.simps) apply(rule conjI)
    using E parallel_run_head apply metis using 3 by simp
next
  case ("4_1" v e2s e2o r2)
  then have "Edge e2s None e2o (get_head_state r2) \<in> transition t2" by simp
  then have E:"Edge (v, e2s) None (Some(None, e2o)) (v, get_head_state r2) \<in> transition (parallel_trans t1 t2)"
    by force
  show ?case apply(simp only: parallel_run.simps) apply(simp only:has_correspond_edges.simps) apply(rule conjI) 
    using E apply (simp add: parallel_run_head) using "4_1" by simp
next
  case ("4_2" v vd vb vc e2s e2o r2)
  then have "Edge e2s None e2o (get_head_state r2) \<in> transition t2" by simp
  then have E:"Edge (v, e2s) None (Some(None, e2o)) (v, get_head_state r2) \<in> transition (parallel_trans t1 t2)"
    by force
  show ?case apply(simp only: parallel_run.simps) apply(simp only:has_correspond_edges.simps) apply(rule conjI) 
    using E apply (simp add: parallel_run_head) using "4_2" by simp
next
  case (5 e1s e1i e1o r1 v)
  then show ?case by simp
next
  case (6 v e2s e2i e2o r2)
  then show ?case by simp
qed 

fun map_run::"('out \<Rightarrow> 'out2) \<Rightarrow> ('in, 'out, 'state) Run \<Rightarrow> ('in, 'out2, 'state) Run" where
  "map_run f (End v) = End v" |
  "map_run f (Move s i None r) = Move s i None (map_run f r)" |
  "map_run f (Move s i (Some e) r) = Move s i (Some (f e)) (map_run f r)"

lemma map_run_head: 
  shows "get_head_state (map_run f r) = get_head_state r"
  apply(cases "(f, r)" rule:map_run.cases) by simp_all

lemma map_run_last: 
  shows "get_last_state (map_run f r) = get_last_state r"
  apply(induct f r rule: map_run.induct) by simp_all

lemma map_run_input: "agg_input (map_run f r) = agg_input r" apply(induct f r rule: map_run.induct) by simp_all

lemma map_run_output: "agg_output (map_run f r) = map f (agg_output r)" apply(induct f r rule: map_run.induct) by simp_all


end