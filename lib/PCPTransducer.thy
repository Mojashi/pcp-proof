theory PCPTransducer
  imports Main PCP Transducer
begin

fun max_state::"(nat, PCP.alphabet, nat) Trans \<Rightarrow> nat" where
  "max_state t = Max ({(initial t), (accepting t)}\<union>((\<lambda>t. src t) ` transition t)\<union>((\<lambda>t. dest t) ` transition t))"

definition add_string_to_trans::"(nat, PCP.alphabet, nat) Trans \<Rightarrow> nat \<Rightarrow> PCP.alphabet list \<Rightarrow> (nat, PCP.alphabet, nat) Trans" where
  "add_string_to_trans t i s \<equiv> let ss = max_state t + 1 in 
    Trans (initial t) (
      transition t \<union> 
      (set (map (\<lambda> (j,c). (Edge (ss+j) None (Some c) (ss+j+1))) (enumerate 0 s))) \<union>
      {Edge (initial t) (Some i) None ss, Edge (ss + length s) None None (accepting t)}
    ) (accepting t)"

lemma transitions_run_monotone:
  assumes "transition t \<subseteq> transition t'" and "initial t = initial t'" and "accepting t = accepting t'"
  shows "is_initial_accept_run t r \<Longrightarrow> is_initial_accept_run t' r"
proof -
  assume A:"is_initial_accept_run t r"
  have "get_head_state r = initial t'" using add_string_to_trans_def assms A by auto
  have "get_last_state r = accepting t'" using add_string_to_trans_def assms A by auto
  have E:"\<And>e. e \<in> transition t \<Longrightarrow> e \<in> transition t'" using assms by auto
  have "has_correspond_edges t r" using add_string_to_trans_def assms A E by blast
  then have "has_correspond_edges t' r" apply(induct r) apply simp using E by simp
  then show ?thesis using add_string_to_trans_def assms using A by presburger
qed

lemma add_string_to_trans_monotone:
  shows "transduce_runs t ins \<subseteq> transduce_runs (add_string_to_trans t i s) ins"
proof -
  have I:"initial t = initial (add_string_to_trans t i s)" using add_string_to_trans_def by auto
  have A:"accepting t = accepting (add_string_to_trans t i s)" using add_string_to_trans_def by auto
  have T:"transition t \<subseteq> transition (add_string_to_trans t i s)" using add_string_to_trans_def by auto
  then have "\<And>r. is_initial_accept_run t r \<Longrightarrow> is_initial_accept_run (add_string_to_trans t i s) r"
    using transitions_run_monotone[OF T I A] by simp
  then show ?thesis by blast
qed

lemma add_string_to_trans_sanity:
  assumes "t' = add_string_to_trans t i s"
  shows "s \<in> transduce t' [i]"
proof -
  define ss where "ss \<equiv> max_state t + 1"
  
  have FIN:"has_correspond_edges t' (Move (ss + length s) None None (End (accepting t')))" using ss_def
    by (simp add: add_string_to_trans_def assms)

  have "\<forall>l. \<exists>r. l\<le>length s \<longrightarrow> has_correspond_edges t' r \<and> agg_input r = [] \<and> agg_output r = drop (length s - l) s \<and> get_head_state r = (ss + length s - l) \<and> get_last_state r = (accepting t')"
  proof (rule allI)
    fix l
    show "\<exists>r. l \<le> length s \<longrightarrow>
             has_correspond_edges t' r \<and> agg_input r = [] \<and> agg_output r = drop (length s - l) s \<and> get_head_state r = (ss + length s - l) \<and> get_last_state r = (accepting t')"
    proof (induct l)
      case 0
      then show ?case  using FIN by fastforce
    next
      case (Suc l)
      then show ?case apply(cases "(Suc l) \<le> length s") apply simp_all proof -
      assume ASM:"Suc l \<le> length s"
      then obtain r where R:"has_correspond_edges t' r \<and> agg_input r = [] \<and> agg_output r = drop (length s - l) s \<and> get_head_state r = (ss + length s - l) \<and> get_last_state r = (accepting t')" 
        using Suc by auto

      define c where "c = s!(length s - (Suc l))" 
      have "((length s - (Suc l)), c) \<in> set (enumerate 0 s)" using Cons ASM c_def
        by (simp add: in_set_enumerate_eq)
      have "Edge (ss + length s - (Suc l)) None (Some c) (ss + length s - l) = ((\<lambda>(j, c). Edge (ss + j) None (Some c) (ss + j + 1)) ((length s - (Suc l)), c))"
        apply(simp) apply(rule conjI) 
        using ASM Nat.add_diff_assoc apply presburger
        by (metis ASM Nat.add_diff_assoc Suc_diff_Suc Suc_le_lessD add_Suc_right add_leD2 plus_1_eq_Suc)
      then have A:"Edge (ss + length s - (Suc l)) None (Some c) (ss + length s - l) \<in> (((\<lambda>(j, c). Edge (ss + j) None (Some c) (ss + j + 1)) ` (set (enumerate 0 s))))"
        using \<open>(length s - Suc l, c) \<in> set (enumerate 0 s)\<close> by blast
      have "Edge (ss + length s - (Suc l)) None (Some c) (ss + length s - l) \<in> transition t'"
        apply(simp add:assms add_string_to_trans_def) apply(rule disjI2) using A ss_def by auto
        
      then have CO:"has_correspond_edges t' (Move (ss + length s - (Suc l)) None (Some c) r)"
        apply(simp only:has_correspond_edges.simps) by(simp only:R)
      show "\<exists>r. has_correspond_edges t' r \<and> agg_input r = [] \<and> agg_output r = drop (length s - (Suc l)) s \<and> get_head_state r = (ss + length s - (Suc l)) \<and> get_last_state r = (accepting t')"
        apply(rule_tac x="(Move (ss + length s - (Suc l)) None (Some c) r)" in exI)  apply (simp add:CO R)
        apply(rule conjI) 
        using \<open>Edge (ss + length s - Suc l) None (Some c) (ss + length s - l) \<in> transition t'\<close> apply blast 
        by (metis ASM Cons_nth_drop_Suc Suc_diff_Suc Suc_le_lessD c_def diff_less drop_Nil length_drop length_greater_0_conv zero_less_Suc)
    qed
  qed
qed
  then obtain r where R:"has_correspond_edges t' r \<and> agg_input r = [] \<and> agg_output r = s \<and> get_head_state r = ss \<and> get_last_state r = (accepting t')"
    by force

  have "has_correspond_edges t' (Move (initial t') (Some i) None (End ss))" using ss_def
    by (simp add: add_string_to_trans_def assms)
  then have "has_correspond_edges t' (Move (initial t') (Some i) None r)" using R by simp
  then have I:"is_initial_accept_run t' (Move (initial t') (Some i) None r)" using R by simp
  have I2:"agg_input (Move (initial t') (Some i) None r) = [i]" using R by simp
  then have RUNOK:"(Move (initial t') (Some i) None r) \<in> transduce_runs t' [i]" using I I2 by blast
  have "agg_output (Move (initial t') (Some i) None r) = s" using R by simp
  then show ?thesis using RUNOK by blast
qed

fun strs_concat_trans::"PCP.alphabet list list \<Rightarrow> (nat, PCP.alphabet, nat) Trans" where
  "strs_concat_trans [] = Trans 0 {} 0" |
  "strs_concat_trans (s#ts) = add_string_to_trans (strs_concat_trans ts) (length ts) s"

abbreviation pcp_trans::"pcp \<Rightarrow> ((nat, PCP.alphabet, nat) Trans) \<times> ((nat, PCP.alphabet, nat) Trans)" where
  "pcp_trans ts \<equiv> (strs_concat_trans (map fst ts), strs_concat_trans (map snd ts))"
value "pcp_trans [([C0,C1,C0,C0], [C1,C1,C0]), ([C0,C0,C0], [C1,C1,C0])]"


lemma strs_concat_trans_initial_0:
  shows "initial (strs_concat_trans ss) = 0" apply(induct ss) apply simp 
  by (simp add: add_string_to_trans_def)

lemma strs_concat_trans_accepting_0:
  shows "accepting (strs_concat_trans ss) = 0" apply(induct ss) apply simp 
    by (simp add: add_string_to_trans_def)

lemma strs_concat_trans_accept_empty:
  shows "[] \<in> transduce (strs_concat_trans ss) []"
proof -
  have R:"End 0 \<in> transduce_runs (strs_concat_trans ss) []" using strs_concat_trans_accepting_0 strs_concat_trans_initial_0 by simp
  have "agg_output (End 0) = []" by simp
  then show ?thesis using R
    by (metis (mono_tags, lifting) CollectI)
qed

lemma strs_concat_trans_onestep:
  "i < length ss \<Longrightarrow> ss!(length ss - i - 1) \<in> transduce (strs_concat_trans ss) [i]"
proof(induct ss arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a ss)
  have N:"a \<in> transduce (strs_concat_trans (a#ss)) [length ss]"
    apply(simp only:strs_concat_trans.simps)
      using add_string_to_trans_sanity by simp
    then show ?case proof(cases "i = length ss")
    case True
    then show ?thesis using N by simp
  next
    case False
    then have S:"ss!(length ss - i - 1) \<in> transduce (strs_concat_trans ss) [i]" using Cons by auto
    have "i < length ss" using False Cons(2) by simp
    then have I:"(a # ss) ! (length (a # ss) - i - 1) = ss!(length ss - i - 1)" by simp
    show ?thesis apply(simp only:I) apply(simp only:strs_concat_trans.simps) 
      using add_string_to_trans_monotone[of "strs_concat_trans ss" "[i]" "length ss" a] S by blast
  qed
qed 

lemma strs_concat_trans_sanity:
  shows "all_lower is (length ss) \<Longrightarrow> (concatenate_strings_seq ss (rev(map (\<lambda>i. length ss - i - 1) is))) \<in> transduce (strs_concat_trans ss) is"
proof (induct "is" arbitrary: ss)
  case Nil
  have C:"concatenate_strings_seq ss [] = []" by simp
  then have "[] \<in> transduce (strs_concat_trans ss) []" using strs_concat_trans_accept_empty by auto
  have "concatenate_strings_seq ss [] \<in> transduce (strs_concat_trans ss) []" 
    apply(simp only:strs_concat_trans.simps Nil C)  
    using \<open>[] \<in> transduce (strs_concat_trans ss) []\<close> by blast
  then show ?case by simp
next
  case (Cons i "is")
  then have IH: " (concatenate_strings_seq ss (rev(map (\<lambda>i. length ss - i - 1) is))) \<in> transduce (strs_concat_trans ss) is" by fastforce
  then obtain r where R:"r \<in> transduce_runs (strs_concat_trans ss) is \<and> agg_output r =  (concatenate_strings_seq ss (rev(map (\<lambda>i. length ss - i - 1) is)))"
    by auto
  assume "all_lower (i # is) (length ss)"
  then have I:"i < length ss" by simp
  then have "ss ! (length ss - i - 1) \<in> transduce (strs_concat_trans ss) [i]"
    using strs_concat_trans_onestep[OF I] by blast
  then obtain p where P:"p \<in> transduce_runs (strs_concat_trans ss) [i] \<and> agg_output p = concatenate_strings_seq ss [length ss - i - 1]"
    by auto
  then have RH:"get_head_state r = 0" using R using strs_concat_trans_initial_0 by auto
  then have PL:"get_last_state p = 0" using P using strs_concat_trans_accepting_0 by auto
  then have CONC_VALID:"get_head_state r = get_last_state p" using RH by presburger
  define pr where "pr = concat_run p r"
  have PI:"agg_input p = [i]"using P by blast
  have RI:"agg_input r = is"using R by blast
  have IN:"agg_input pr = i#is" using concat_agg_input[of p r] RI PI pr_def by simp
  have "agg_output pr = (concatenate_strings_seq ss [length ss - i - 1])@(concatenate_strings_seq ss (rev(map (\<lambda>i. length ss - i - 1) (is))))"
    using concat_agg_output[of p r] pr_def R P by argo
  then have "agg_output pr = ((concatenate_strings_seq ss [length ss - i - 1]) @ (concatenate_strings_seq ss (rev (map (\<lambda>i. length ss - i - 1) is))))"
    by blast
  then have "agg_output pr = (concatenate_strings_seq ss ( (rev (map (\<lambda>i. length ss - i - 1) is)) @ ([length ss - i - 1])   ))"
    using concatenate_strings_seq_m by presburger
  then have OUT:"agg_output pr = (concatenate_strings_seq ss ( (rev (map (\<lambda>i. length ss - i - 1) (i#is)))   ))"
    by simp
  have "get_head_state pr = get_head_state p" using concat_run_head pr_def CONC_VALID by metis
  then have PR_INI:"get_head_state pr = accepting (strs_concat_trans ss)" using P R RH strs_concat_trans_accepting_0 by auto
  have "get_last_state pr = get_last_state r" using concat_run_last pr_def CONC_VALID by metis
  then have PR_ACC:"get_last_state pr = initial (strs_concat_trans ss)" using P R PL strs_concat_trans_initial_0 by auto
  have "has_correspond_edges (strs_concat_trans ss) pr" using concat_run_ex R P pr_def CONC_VALID by force
  then have "is_initial_accept_run (strs_concat_trans ss) pr" using PR_INI PR_ACC
    using strs_concat_trans_accepting_0 strs_concat_trans_initial_0 by presburger
  then show ?case using IN OUT by force
qed

lemma strs_concat_trans_sanity':
  shows "all_lower is (length ss) \<Longrightarrow> (concatenate_strings_seq ss is) \<in> transduce (strs_concat_trans ss) (rev(map (\<lambda>i. length ss - i - 1) is))"
proof -
  have rev_idd: "all_lower is (length ss) \<Longrightarrow> (rev(map (\<lambda>i. length ss - i - 1) (rev(map (\<lambda>i. length ss - i - 1) is)))) = is"
  proof -
    have mapmap_length_id:"all_lower is (length ss) \<Longrightarrow> ((map (\<lambda>i. length ss - i - 1) ((map (\<lambda>i. length ss - i - 1) is)))) = is"
    proof -
    assume ASM:"all_lower is (length ss)"
    then have A:"((map (\<lambda>i. length ss - i - 1) ((map (\<lambda>i. length ss - i - 1) is)))) = (map ((\<lambda>i. length ss - i - 1) o (\<lambda>i. length ss - i - 1)) is)"
      by auto
    show "((map (\<lambda>i. length ss - i - 1) ((map (\<lambda>i. length ss - i - 1) is)))) = is"
      apply(simp only:A)
      using ASM apply(induct "is") apply simp by auto
  qed

    assume "all_lower is (length ss)"
    have "rev(map (\<lambda>i. length ss - i - 1) (rev(map (\<lambda>i. length ss - i - 1) is))) = rev(rev(map (\<lambda>i. length ss - i - 1) (map (\<lambda>i. length ss - i - 1) is)))"
    by (simp add: rev_map)
    then show ?thesis using mapmap_length_id using \<open>all_lower is (length ss)\<close> by auto
  qed

  assume ASM:"all_lower is (length ss)"
  then have B:"all_lower (rev (map (\<lambda>i. length ss - i - 1) is)) (length ss)"
    apply(induct "is") apply simp by auto

  show ?thesis using strs_concat_trans_sanity[of "(rev (map (\<lambda>i. length ss - i - 1) is))" ss, OF B] rev_idd
    using ASM by fastforce
qed

locale pcp_locale =
  fixes ts::pcp
begin
  
abbreviation UT::"(nat, PCP.alphabet, nat) Trans" where
  "UT \<equiv> strs_concat_trans (map fst ts)"

abbreviation DT::"(nat, PCP.alphabet, nat) Trans" where
  "DT \<equiv> strs_concat_trans (map snd ts)"

lemma solution_trans:
  assumes "is_solution ts sol"
  shows "\<exists>e. e \<in> transduce UT (rev(map (\<lambda>i. length ts - i - 1) sol)) \<inter> transduce DT (rev(map (\<lambda>i. length ts - i - 1) sol))"
proof -
  have LOWER:"all_lower sol (length ts)" using assms using is_solution_def by blast
  then have LOWERF:"all_lower sol (length (map fst ts))" by simp
  then have LOWERS:"all_lower sol (length (map snd ts))" by simp
  have FLENEQ:"length (map fst ts) = length ts" by simp
  have U:"concatenate_tiles_seq_upper ts sol \<in> transduce UT (rev(map (\<lambda>i. length ts - i - 1) sol))"
    using strs_concat_trans_sanity'[OF LOWERF] LOWER assms concatenate_tiles_seq_upper_eq[OF LOWER] by simp
  have D:"concatenate_tiles_seq_bottom ts sol \<in> transduce DT (rev(map (\<lambda>i. length ts - i - 1) sol))"
    using strs_concat_trans_sanity'[OF LOWERS] LOWER assms concatenate_tiles_seq_bottom_eq[OF LOWER] by simp
  have "concatenate_tiles_seq_upper ts sol = concatenate_tiles_seq_bottom ts sol"
    using assms is_solution_def by simp
  then have "concatenate_tiles_seq_upper ts sol \<in> transduce UT (rev(map (\<lambda>i. length ts - i - 1) sol)) \<inter> transduce DT (rev(map (\<lambda>i. length ts - i - 1) sol))" 
    using U D by simp
  then show ?thesis by blast
qed

lemma if_trans_has_no_intersection_then_no_solution:
  assumes "\<forall>ins. {} = transduce UT (rev(map (\<lambda>i. length ts - i - 1) ins)) \<inter> transduce DT (rev(map (\<lambda>i. length ts - i - 1) ins))"
  shows "\<not>have_solution ts"
  using assms have_solution_def solution_trans by force
end


end