theory PCP
  imports Main
begin

datatype alphabet = C0 | C1
type_synonym string = "alphabet list"

type_synonym tile = "string \<times> string"
type_synonym pcp = "tile list"


fun all_lower :: "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "all_lower ss u = list_all (\<lambda>x. x < u) ss"

value "all_lower [3,5,1,2,3] 6"

fun reverse_tile :: "tile \<Rightarrow> tile" where
"reverse_tile (s1, s2) = ((rev s1), (rev s2))"

fun reverse_pcp :: "pcp => pcp" where
"reverse_pcp ts = (map reverse_tile ts)"

value "(reverse_tile (([C0,C1,C0,C0], [C1,C1,C0])))"
value "reverse_pcp [([C0,C1,C0,C0], [C1,C1,C0]), ([C0,C1,C0,C0], [C1,C0])]"

fun get_tiles :: "pcp \<Rightarrow> nat list \<Rightarrow> tile list" where
  "get_tiles ts s = map (nth ts) s"

value "[(''0100'', ''1102''), (''0100'', ''110'')] ! 1"


fun concatenate_strings_seq :: "alphabet list list \<Rightarrow> nat list \<Rightarrow> string" where
"concatenate_strings_seq _ [] = ''''" |
"concatenate_strings_seq ss (i # is) = 
     (concatenate_strings_seq ss is) @ (ss ! i)"

lemma concatenate_strings_seq_m:
  "(concatenate_strings_seq ss is)@(concatenate_strings_seq ss js) = concatenate_strings_seq ss (js@is)"
  apply(induct js) apply simp by simp

fun concatenate_tiles_seq_upper :: "tile list \<Rightarrow> nat list \<Rightarrow> string" where
"concatenate_tiles_seq_upper _ [] = ''''" |
"concatenate_tiles_seq_upper ts (i # is) = 
     (concatenate_tiles_seq_upper ts is) @ fst (ts ! i)"

value "concatenate_tiles_seq_upper [([C0,C1,C0,C0], [C1,C1,C0]), ([C0,C0,C0], [C1,C1,C0])] [1,0,0,0]"

lemma concatenate_tiles_seq_upper_eq:
  shows "all_lower is (length ts) \<Longrightarrow> concatenate_tiles_seq_upper ts is = concatenate_strings_seq (map fst ts) is"
proof(induct "is")
  case Nil
  then show ?case by auto
next
  case (Cons a "is")
  then have "(map fst ts) ! a = fst(ts !a)" by auto
  then show ?case using Cons.hyps Cons.prems by auto
qed

fun swap_tile :: "tile \<Rightarrow> tile" where
  "swap_tile (a,b) = (b,a)"

fun swap_pcp :: "pcp \<Rightarrow> pcp" where
"swap_pcp ts = map swap_tile ts"

value "swap_pcp [([C0,C1,C0,C0], [C1,C1,C0]), ([C0,C1], [C0])]"


fun concatenate_tiles_seq_bottom :: "tile list \<Rightarrow> nat list \<Rightarrow> string" where
"concatenate_tiles_seq_bottom _ [] = []" |
"concatenate_tiles_seq_bottom ts (i # is) = 
     (concatenate_tiles_seq_bottom ts is) @ snd (ts ! i)"


lemma concatenate_tiles_seq_bottom_eq:
  shows "all_lower is (length ts) \<Longrightarrow> concatenate_tiles_seq_bottom ts is = concatenate_strings_seq (map snd ts) is"
proof(induct "is")
  case Nil
  then show ?case by auto
next
  case (Cons a "is")
  then have "(map snd ts) ! a = snd(ts !a)" by auto
  then show ?case using Cons.hyps Cons.prems by auto
qed

lemma map_swap_tile: "\<forall>i < length ts. (map swap_tile ts) ! i = swap_tile (ts ! i)"
  using nth_map [of _ ts reverse_tile] by auto

lemma concat_swap_eq: 
  fixes s::"nat list"
  shows "all_lower s (length ts) \<Longrightarrow> concatenate_tiles_seq_bottom ts s = concatenate_tiles_seq_upper (swap_pcp ts) s"
proof (induct s)
  case Nil
  then show ?case by auto
next
  case (Cons a s)
  then have IH: "concatenate_tiles_seq_bottom ts s = concatenate_tiles_seq_upper (swap_pcp ts) s" by auto
  then have "concatenate_tiles_seq_upper (swap_pcp ts) (a#s) = 
    (concatenate_tiles_seq_upper (swap_pcp ts) s) @ fst(((swap_pcp ts)!a))" using map_swap_tile by auto
  then have "a < (length ts) \<Longrightarrow> concatenate_tiles_seq_upper (swap_pcp ts) (a#s) = 
    (concatenate_tiles_seq_upper (swap_pcp ts) s) @ fst(swap_tile (ts!a))" using map_swap_tile by auto

  then show ?case 
    by (metis Cons.prems IH all_lower.elims(2) concatenate_tiles_seq_bottom.simps(2) fst_swap list_all_simps(1) prod.exhaust_sel snd_swap swap_tile.simps)
qed


definition is_solution :: "pcp \<Rightarrow> nat list \<Rightarrow> bool" where
"is_solution p l \<equiv>  all_lower l (length p) \<and> (length l) > 0 \<and>  (concatenate_tiles_seq_upper p l) = (concatenate_tiles_seq_bottom p l)"

value "is_solution [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])] [0,2,0,0,2,1,1]"
value "is_solution (reverse_pcp [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])]) (rev [0,2,0,0,2,1,1])"

value "let ts= [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])] in let is=[0,2,1] in 
  (rev (concatenate_tiles_seq_upper ts is) = (concatenate_tiles_seq_upper (reverse_pcp ts) (rev is)))"

lemma concat_head_tile: "concatenate_tiles_seq_upper ts (i # rest) = (concatenate_tiles_seq_upper ts rest) @ (fst (ts ! i))" 
  proof (cases "ts!i", auto)
  qed

lemma concat_head_tile_btm: "concatenate_tiles_seq_bottom ts (i # rest) = (concatenate_tiles_seq_bottom ts rest) @ (snd (ts ! i))" 
  proof (cases "ts!i", auto)
  qed

lemma concat_tail_tile: "concatenate_tiles_seq_upper ts (a @ [b]) = (fst (ts ! b)) @ (concatenate_tiles_seq_upper ts a)"
proof (induct a rule: list.induct)
  case Nil
  then show ?case
    by (metis append.right_neutral append_Nil concat_head_tile concatenate_tiles_seq_upper.simps(1))
next
  case (Cons a as)
  have "concatenate_tiles_seq_upper ts ((a # as) @ [b]) = (concatenate_tiles_seq_upper ts (as @ [b])) @ (fst (ts ! a))" 
    using concat_head_tile by auto
  then show ?case using concat_head_tile local.Cons by auto
qed


value "hd ([33,3,4] :: nat list)"

lemma rev_concat_tile: "concatenate_tiles_seq_upper ts (rev (a#ss)) = (fst (ts ! a)) @ (concatenate_tiles_seq_upper ts (rev ss))"
  using concat_tail_tile by auto

lemma map_reverse_tile: "\<forall>i < length ts. (map reverse_tile ts) ! i = reverse_tile (ts ! i)"
  using nth_map [of _ ts reverse_tile] by auto

lemma C: "\<forall>i < length ts. (reverse_pcp ts) ! i = reverse_tile (ts ! i)"
  using map_reverse_tile by auto

lemma swap_reverse:  "(swap_pcp (reverse_pcp ts)) = reverse_pcp(swap_pcp ts)"
proof (induct ts)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then show ?case
    by (metis list.simps(9) prod.exhaust_sel reverse_pcp.elims reverse_tile.simps swap_pcp.elims swap_tile.simps)
qed
lemma reverse_u: 
  fixes ts::pcp
  shows "all_lower ans (length ts) \<Longrightarrow>
    rev (concatenate_tiles_seq_upper ts ans) = concatenate_tiles_seq_upper (reverse_pcp ts) (rev ans)"
proof (induct ans rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons i rest)
  have PREM: "all_lower rest (length ts)" using Cons by auto
  have IPREM: "i < (length ts)" using Cons by simp
  have B: "(fst (reverse_pcp ts ! i)) @ (concatenate_tiles_seq_upper (reverse_pcp ts) (rev rest)) = (concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest)))" using rev_concat_tile by auto
  then have "... = rev (fst (ts ! i)) @ (concatenate_tiles_seq_upper (reverse_pcp ts) (rev rest))" using C IPREM by (metis old.prod.exhaust prod.sel(1) reverse_tile.simps)
  then have "(concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest))) =  rev (fst (ts ! i)) @ rev(concatenate_tiles_seq_upper ts rest)"using Cons B  by auto
  then have "(concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest))) = rev((concatenate_tiles_seq_upper ts rest) @ (fst (ts ! i)))" by auto
  then have "(concatenate_tiles_seq_upper (reverse_pcp ts) (rev (i # rest))) = rev(concatenate_tiles_seq_upper ts (i # rest))" using concat_head_tile by presburger
  then show ?case by auto
qed

lemma swap_pcp_length_identiy: "length (swap_pcp ts) = length ts"
  apply (induction ts)
   apply (simp)
  apply(auto)
  done

lemma rev_pcp_length_identiy: "length (reverse_pcp ts) = length ts"
   by auto

lemma rev_all_lower: "all_lower ans (length ts) = all_lower (rev ans) (length ts)"
  by auto

lemma reverse_d: 
  fixes ts::pcp
  shows "all_lower ans (length ts) \<Longrightarrow>
  rev (concatenate_tiles_seq_bottom ts ans) = concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)"
proof -
  assume ASM:"all_lower ans (length ts)"
  then show "rev (concatenate_tiles_seq_bottom ts ans) = concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)"
  proof -
    have A:"concatenate_tiles_seq_bottom ts ans = concatenate_tiles_seq_upper (swap_pcp ts) ans" using ASM concat_swap_eq by auto
    then have "rev (concatenate_tiles_seq_bottom ts ans) = concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)" 
      using reverse_u swap_reverse swap_pcp_length_identiy concat_swap_eq ASM 
      by (metis rev_all_lower rev_pcp_length_identiy)
    then show ?thesis by auto
  qed
qed

lemma reverse_equivalence: 
  fixes ts::pcp
  assumes "all_lower ans (length ts)"
  shows "is_solution ts ans = is_solution (reverse_pcp ts) (rev ans)"
proof -
  have "all_lower (rev ans) (length ts)" using assms by auto

  have "is_solution (reverse_pcp ts) (rev ans) = ((all_lower (rev ans) (length ts)) \<and> (length ans) > 0 \<and>  concatenate_tiles_seq_upper (reverse_pcp ts) (rev ans) = (concatenate_tiles_seq_bottom (reverse_pcp ts) (rev ans)))" 
      using rev_pcp_length_identiy is_solution_def assms by auto
  then have "is_solution (reverse_pcp ts) (rev ans) = ((all_lower (rev ans) (length ts))\<and> (length ans) > 0 \<and> rev (concatenate_tiles_seq_upper ts ans) = rev (concatenate_tiles_seq_bottom ts ans))" 
    using swap_pcp_length_identiy rev_pcp_length_identiy reverse_u reverse_d assms by auto
  then have "is_solution (reverse_pcp ts) (rev ans) = ((all_lower (rev ans) (length ts))\<and> (length ans) > 0 \<and> rev (concatenate_tiles_seq_upper ts ans) = rev (concatenate_tiles_seq_bottom ts ans))" 
      using swap_pcp_length_identiy rev_pcp_length_identiy reverse_u reverse_d assms by fastforce
  then show ?thesis using is_solution_def assms reverse_d reverse_u by auto
qed

definition have_solution:: "pcp \<Rightarrow> bool" where
  "have_solution ts \<equiv> \<exists>ans. is_solution ts ans"

lemma rev_rev_tile_ident[simp]: "reverse_tile(reverse_tile t) = t"
proof (cases t)
  case (Pair a b)
  then show ?thesis using rev_rev_ident by auto
qed

lemma rev_rev_pcp_ident[simp]: "reverse_pcp(reverse_pcp ts) = ts"
proof simp
  have "reverse_tile \<circ> reverse_tile = id" by auto
  then have "(map (reverse_tile \<circ> reverse_tile)) = (map id)" by auto
  then show "map (reverse_tile \<circ> reverse_tile) ts = ts" by auto
qed

lemma reverse_answer_existance_partial:"have_solution ts \<Longrightarrow> have_solution (reverse_pcp ts)"
proof - 
  assume ASM: "have_solution ts"
  then show ?thesis 
  proof -
    obtain ans where ans_cond:"is_solution ts ans" using have_solution_def ASM by auto
    then have A:"all_lower ans (length ts)" using ASM is_solution_def by auto
    then have "all_lower (rev ans) (length (reverse_pcp ts))" using ASM rev_pcp_length_identiy is_solution_def by auto
    then have "is_solution (reverse_pcp ts) (rev ans)" 
      using reverse_equivalence A ans_cond by blast
    then show "have_solution (reverse_pcp ts)" using have_solution_def by auto
  qed
qed

lemma reverse_answer_existance: "have_solution ts = have_solution (reverse_pcp ts)"
proof -
  have LR: "have_solution ts \<Longrightarrow> have_solution (reverse_pcp ts)" using reverse_answer_existance_partial by auto
  have RL: "have_solution (reverse_pcp ts) \<Longrightarrow> have_solution ts"
  proof -
    have "have_solution (reverse_pcp ts) \<Longrightarrow> have_solution (reverse_pcp(reverse_pcp ts))"
      using reverse_answer_existance_partial by force
    then show "have_solution (reverse_pcp ts) \<Longrightarrow> have_solution ts"
      using rev_rev_pcp_ident by force
  qed
  then show ?thesis using LR RL by auto
qed

lemma "have_solution[([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])]"
proof -
  have "is_solution [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])] (rev[0,2,0,0,2,1,1])"
    using is_solution_def by auto
  then show ?thesis using have_solution_def by auto 
qed
end
