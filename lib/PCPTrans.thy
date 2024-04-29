theory PCPTrans
  imports Main PCP
begin

definition starts_with :: "string \<Rightarrow> string \<Rightarrow> bool"
  where "starts_with s1 s2 \<equiv> (s2 = take (length s2) s1)"

lemma starts_with_prefix: 
  fixes a::string
  fixes b::nat
  shows "starts_with a (take b a)"
  by (metis append_eq_conv_conj append_take_drop_id starts_with_def)

lemma non_common_prefix_monotone:
  fixes a::string
  fixes b::string
  fixes s::string
  fixes t::string
  shows "\<not>starts_with a b \<and> \<not>starts_with b a \<Longrightarrow> \<not>starts_with (a@s) (b@t)"
proof -
  assume "\<not>starts_with a b \<and> \<not>starts_with b a"
  then show ?thesis using starts_with_def 
    by (metis append.assoc append_eq_append_conv_if append_take_drop_id)
qed


datatype config = UP string | DN string

fun measure_config :: "config\<Rightarrow>nat" where
"measure_config (UP s) = length s" |
"measure_config (DN s) = 1 + (length s)"

fun swap_config :: "config \<Rightarrow> config" where
  "swap_config (UP s) = DN s"|
  "swap_config (DN s) = UP s"

fun step_config :: "tile \<Rightarrow> config \<Rightarrow> config set" where
  "step_config (u,d) (UP s) = (
    if (starts_with (s @ u) d ) 
      then {(UP (drop (length d) (s @ u)))}
    else(
      if (starts_with d (s @ u)) 
        then {(DN (drop (length (s @ u)) d))}
      else {}
    ))" | 
  "step_config (u,d)  (DN s)=  (
      if (starts_with u (s @ d)) 
        then {(UP (drop (length (s @ d)) u))}
    else(
    if (starts_with (s @ d) u ) 
      then {(DN (drop (length u) (s @ d)))}
      else {}
    ))"

lemma step_configs_upper_str:
  assumes "(PCPTrans.UP c') \<in> step_config (up,dn) (PCPTrans.UP c)"
  shows "dn@c' = c@up"
  by (metis append_take_drop_id assms config.inject(1) config.simps(4) empty_iff singletonD starts_with_def step_config.simps(1))

lemma step_configs_upper_to_lower_str:
  assumes "(PCPTrans.DN c') \<in> step_config (up,dn) (PCPTrans.UP c)"
  shows "dn = c@up@c'"
  by (metis append.assoc append_take_drop_id assms config.inject(2) config.simps(4) insertCI singletonD starts_with_def step_config.simps(1))

lemma step_configs_lower_str:
  assumes "(PCPTrans.DN c') \<in> step_config (up,dn) (PCPTrans.DN c)"
  shows "up@c' = c@dn"
  by (metis all_not_in_conv append_eq_conv_conj assms config.distinct(1) config.inject(2) insertE starts_with_def step_config.simps(2))

lemma step_configs_lower_to_upper_str:
  assumes "(PCPTrans.UP c') \<in> step_config (up,dn) (PCPTrans.DN c)"
  shows "up = c@dn@c'"
  by (metis append.assoc append_take_drop_id assms config.distinct(1) config.inject(1) insertCI singletonD starts_with_def step_config.simps(2))

lemma step_config_finite: 
  "finite (step_config t c)"
proof (cases t)
  case (Pair u d)
  then show ?thesis 
proof (cases c)
  case (UP s)
  then show ?thesis proof (cases "starts_with (s @ u) d")
    case True
    then show ?thesis using UP True Pair by auto
  next
    case False
    then show ?thesis using UP False Pair by auto
  qed
next
  case (DN s)
  then show ?thesis proof (cases "starts_with u (s @ d)")
    case True
    then show ?thesis using DN True Pair by auto
  next
    case False
    then show ?thesis using DN False Pair by auto
  qed
qed
qed
lemma step_config_card: 
  "card (step_config t c) \<le> 1"
proof (cases t)
  case (Pair u d)
  then show ?thesis 
proof (cases c)
  case (UP s)
  then show ?thesis proof (cases "starts_with (s @ u) d")
    case True
    then show ?thesis using UP True Pair by auto
  next
    case False
    then show ?thesis using UP False Pair by auto
  qed
next
  case (DN s)
  then show ?thesis proof (cases "starts_with u (s @ d)")
    case True
    then show ?thesis using DN True Pair by auto
  next
    case False
    then show ?thesis using DN False Pair by auto
  qed
qed
qed

lemma "finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> card s > 0"
proof -
  assume A:"finite s"
  assume "s \<noteq> {}"
  then have "card s \<noteq> 0"
    using card_0_eq A by blast
  thus "card s > 0"
    by simp
qed


lemma step_config_is_deterministic:
  "a\<in>(step_config t c) \<Longrightarrow> {a}=(step_config t c)"
proof (cases "card (step_config t c) = 0")
  case True
  assume A:"a\<in>(step_config t c)"
  then have "\<not>(a\<in>(step_config t c))" using True step_config_finite by auto 
  then show ?thesis using A by auto
next
  case False
  assume A:"a\<in>(step_config t c)"
  have "card (step_config t c) = 1" using step_config_card[of t c] False by auto
  then show ?thesis by (metis A card_1_singletonE singletonD)
qed

lemma step_config_no_DN_empty:
  shows "DN [] \<notin> step_config (u, d) c"
proof (cases c)
  case (UP x1)
  then show ?thesis 
  proof (cases "(starts_with (x1 @ u) d )")
    case True
    then show ?thesis using UP by auto
  next
    case False
    then show ?thesis
      by (metis UP append.right_neutral empty_iff step_config.simps(1) step_configs_upper_to_lower_str)
  qed
next
  case (DN x2)
  then show ?thesis
  proof (cases "starts_with u (x2 @ d)")
    case True
    then show ?thesis using DN by auto
  next
    case False
    then show ?thesis using DN
    proof (cases "starts_with (x2 @ d) u")
      case True
      then show ?thesis 
        by (metis DN False append.right_neutral step_configs_lower_str)
    next
      case False
      then show ?thesis using DN by auto
    qed
    
  qed
  
qed


fun step_configs ::"tile \<Rightarrow> config set \<Rightarrow> config set" where
  "step_configs t cs = \<Union> ((step_config t) ` cs)"

fun pcp_step_config :: "pcp \<Rightarrow> config \<Rightarrow> config set" where
 "pcp_step_config ts c = \<Union> ( ((\<lambda>t. step_config t c) ` (set ts)))"

fun pcp_step_configs :: "pcp \<Rightarrow> config set \<Rightarrow> config set" where
 "pcp_step_configs ts cs = \<Union> ((pcp_step_config ts) ` cs)"

fun pcp_step_configs' :: "pcp \<Rightarrow> config set \<Rightarrow> config set" where
 "pcp_step_configs' ts cs = \<Union> ((\<lambda>t. step_configs t cs) ` (set ts))"

lemma pcp_step_configs_eq: "pcp_step_configs' ts cs = pcp_step_configs ts cs"
  by auto

fun pcp_init_set :: "pcp \<Rightarrow> config set" where
 "pcp_init_set ts = (pcp_step_config ts (UP []))"

value "pcp_init_set [([C1,C0,C0], [C1]), ([C0], [C1,C0,C0]), ([C1], [C0,C0])]"

definition is_invariant :: "pcp \<Rightarrow> config set \<Rightarrow> bool" where
  "is_invariant ts confs \<equiv> (
    (pcp_init_set ts) \<subseteq> confs \<and>
    pcp_step_configs ts confs \<subseteq> confs \<and>
    (UP []) \<notin> confs\<and>
    (DN []) \<notin> confs
  )"

fun multi_step_pcp :: "pcp \<Rightarrow> config set \<Rightarrow> nat list \<Rightarrow> config set" where
  "multi_step_pcp _ c [] = c" |
  "multi_step_pcp ts c (i#s) = step_configs (ts!i) (multi_step_pcp ts c s)"

lemma all_resulting_conf_is_in_inv_1:
  fixes ts::pcp
  fixes inv::"config set"
  assumes "is_invariant ts inv"
  fixes i::"nat"
  assumes "i < length ts"
  shows "(multi_step_pcp ts {UP []} [i]) \<subseteq> inv"
proof -
  have "(ts ! i) \<in> set ts" using assms by auto
  then have "(step_config (ts ! i) (UP [])) \<subseteq> \<Union> ( ((\<lambda>t. step_config t (UP [])) ` (set ts)))"
    using assms by blast
  then have "(step_config (ts ! i) (UP [])) \<subseteq> (pcp_init_set ts)" by auto
  then show ?thesis using assms(1) is_invariant_def by auto
qed

lemma inv_closed_forward_pcp:
  fixes ts::pcp
  fixes inv
  assumes "is_invariant ts inv"
  fixes s::"config set"
  shows "s \<subseteq> inv \<Longrightarrow> (pcp_step_configs ts s) \<subseteq> inv"
proof -
  have A:"pcp_step_configs ts inv \<subseteq> inv" 
    using is_invariant_def assms by simp
  assume "s \<subseteq> inv"
  then have "pcp_step_configs ts s \<subseteq> pcp_step_configs ts inv" by auto
  then show "(pcp_step_configs ts s) \<subseteq> inv" using A by blast
qed

lemma step_configs_is_part_of_pcp_step_configs: "a < length ts \<Longrightarrow> step_configs (ts!a) c \<subseteq> pcp_step_configs ts c"
proof -
  assume "a < length ts"
  then show "step_configs (ts!a) c \<subseteq> pcp_step_configs ts c" using nth_mem by auto
qed

lemma all_resulting_conf_is_in_inv:
  fixes ts::pcp
  fixes inv::"config set"
  assumes "is_invariant ts inv"
  fixes s::"nat list"
  shows "all_lower s (length ts) \<Longrightarrow> s\<noteq>[] \<Longrightarrow> (multi_step_pcp ts {UP []} s) \<subseteq> inv"
using is_invariant_def proof (induct s)
  case Nil
  then show ?case by auto
next
  case (Cons a ss)
  assume "all_lower (Cons a ss) (length ts)"
  then have AL: "a < length ts" using assms Cons by auto
  then show ?case  proof (cases "ss\<noteq>[]")
    case True
    then have IH: "all_lower ss (length ts) \<Longrightarrow> ss\<noteq>[] \<Longrightarrow> (multi_step_pcp ts {UP []} ss) \<subseteq> inv" using Cons by auto
    then have B:"multi_step_pcp ts {UP []} (a#ss) = step_configs (ts!a) (multi_step_pcp ts {UP []} ss)" 
      by auto
    have "(multi_step_pcp ts {UP []} ss) \<subseteq> inv" using Cons AL True by auto
    then have "pcp_step_configs ts (multi_step_pcp ts {UP []} ss) \<subseteq> inv"
      using inv_closed_forward_pcp[of "ts" inv "(multi_step_pcp ts {UP []} ss)" ] Cons True assms by fastforce
    then have "multi_step_pcp ts {UP []} (a#ss) \<subseteq> inv" 
      using is_invariant_def AL inv_closed_forward_pcp[of "ts" inv "(multi_step_pcp ts {UP []} ss)" ]
        step_configs_is_part_of_pcp_step_configs B by (metis subset_trans)
    then show ?thesis using is_invariant_def by auto
  next
    case False
    then have "(multi_step_pcp ts {UP []} [a]) \<subseteq> inv" using is_invariant_def 
      using AL all_resulting_conf_is_in_inv_1 assms by presburger
    then show "(multi_step_pcp ts {UP []} (a # ss)) \<subseteq> inv" using False by auto
  qed
qed


fun diff_conf :: "string \<Rightarrow> string \<Rightarrow> config set" where
  "diff_conf up dn = (
    if(starts_with up dn) 
      then {UP (drop (length dn) up)}
      else (
        if(starts_with dn up)
        then {DN (drop (length up) dn)}
        else {}
      ))"

lemma starts_with_concat_diff:
  assumes "length a \<ge> length b" and "length a + length c \<ge> length b + length d"
  shows "drop (length (b@d)) (a@c) = drop (length d) ((drop (length b) a)@c)"
proof -
  show ?thesis by (simp add: add.commute assms(1))
qed

lemma starts_with_concat_diff_opp:
  assumes "length a \<ge> length b" and "length a + length c \<le> length b + length d"
  shows "drop (length (a@c)) (b@d) = drop (length ((drop (length b) a)@c)) d"
proof -
  show ?thesis using assms(1) by auto
qed

lemma take_decompose:
  assumes "length a \<ge> s" and "length a + length b \<ge> s + t" 
  shows "take (s + t) (a@c) = (take s a) @ (take t ((drop s a)@c))"
  by (simp add: add.commute assms(1) take_add)

lemma starts_with_concat:
  assumes "starts_with a b"
  shows "starts_with (a@c) (b@d) = starts_with ((drop (length b) a)@c) d"
proof (cases "starts_with ((drop (length b) a)@c) d")
  case True
  then show ?thesis using assms by (metis (no_types, lifting) assms(1) append.assoc append_eq_conv_conj starts_with_def)
next
  case F1:False
  then show ?thesis proof (cases "length (a@c) \<ge> length (b@d)")
    case True
    have "take (length (b@d)) (a@c) = (take (length b) a) @ (take (length d) ((drop (length b) a)@c) )"
      using take_decompose by (metis True assms(1) length_append nat_le_linear starts_with_def take_all_iff)
    then show ?thesis using F1 starts_with_def by (metis assms(1) same_append_eq)
  next
    case False
    then show ?thesis using starts_with_def F1 by (metis nat_le_linear take_all)
  qed
qed


lemma starts_with_concat_opp:
  assumes "starts_with a b"
  shows "starts_with (b@d) (a@c) = starts_with d ((drop (length b) a)@c)"
proof (cases "starts_with d ((drop (length b) a)@c)")
  case True
  then show ?thesis using assms starts_with_def by (metis (no_types, opaque_lifting) append.assoc append_eq_conv_conj)
next
  case F1:False
  then show ?thesis  using assms starts_with_def 
  proof (cases "length (b@d) \<ge> length (a@c)")
    case True
    have "(take (length b) a) @ (take (length ((drop (length b) a)@c)) d ) = take (length (a@c)) (b@d)"
      apply simp
      by (metis (no_types, lifting) Nat.add_diff_assoc2 add.commute assms nat_le_linear starts_with_def take_all_iff trans_le_add2)
    then show ?thesis using F1 starts_with_def 
      by (metis (no_types, opaque_lifting) append.assoc append_eq_conv_conj assms)
  next
    case False
    then show ?thesis using starts_with_def F1 by (metis nat_le_linear take_all)
  qed
qed


lemma starts_with_then_length_larger:
  assumes "starts_with a b"
  shows "length a \<ge> length b"
  by (metis assms nat_le_linear starts_with_def take_all_iff)

lemma multi_step_conf_eq':
  fixes ts::pcp
  fixes s::"nat list"
  assumes "all_lower s (length ts)"
  shows "(diff_conf (concatenate_tiles_seq_upper ts s) (concatenate_tiles_seq_bottom ts s)) = (multi_step_pcp ts {UP []} s)"
proof (induct s)
  case Nil
  then show ?case by (simp add: starts_with_def)
next
  case (Cons a s)
  then show ?case proof (cases "(multi_step_pcp ts {UP []} s) = {}")
    case True
    then have "(multi_step_pcp ts {UP []} (a#s)) = {}" by simp
    then show ?thesis by (metis True card.empty card_1_singleton_iff concat_head_tile_btm concatenate_tiles_seq_upper.simps(2) diff_conf.elims local.Cons n_not_Suc_n non_common_prefix_monotone)
  next
    case False
    then obtain w where W:"(multi_step_pcp ts {UP []} s) = {w}" by (metis diff_conf.simps local.Cons)
    obtain t where T:"t = ts!a" by auto
    have 1:"multi_step_pcp ts {UP []} (a#s) = step_configs t (multi_step_pcp ts {UP []} s)" 
      using T multi_step_pcp.simps(2) by presburger
    have 2:"step_configs t (multi_step_pcp ts {UP []} s) = step_configs t {w}" using W by auto
    have 3:"step_configs t {w} = step_config t w" by auto
    have A:"multi_step_pcp ts {UP []} (a#s) = step_config t w" using 1 2 3 by auto

    have K:"diff_conf (concatenate_tiles_seq_upper ts s) (concatenate_tiles_seq_bottom ts s) = {w}"
      using W local.Cons by blast

    show ?thesis proof (cases t) case (Pair u d) then show ?thesis
    proof (cases w)
    case (UP x1)
      have 4:"drop (length (concatenate_tiles_seq_bottom ts s)) (concatenate_tiles_seq_upper ts s) = x1"
        by (metis K False UP config.distinct(1) config.inject(1) diff_conf.simps local.Cons the_elem_eq)
      have 5:"starts_with  (concatenate_tiles_seq_upper ts s) (concatenate_tiles_seq_bottom ts s)"
        using K by (metis False UP config.distinct(1) diff_conf.simps local.Cons the_elem_eq)

      then show ?thesis proof (cases "starts_with (x1@u) d")
        case True

        then have "step_config t w = {(UP (drop (length d) (x1 @ u)))}"
          using Pair UP step_config.simps(1) True by presburger
        then have "multi_step_pcp ts {UP []} (a#s) = {(UP (drop (length d) (x1 @ u)))}"
          using A by presburger

        have 6:"starts_with ((concatenate_tiles_seq_upper ts s)@u) ((concatenate_tiles_seq_bottom ts s)@d)"
          using True 4 5 by (metis append.assoc append_eq_conv_conj starts_with_def)
        then have "drop (length((concatenate_tiles_seq_bottom ts s)@d)) ((concatenate_tiles_seq_upper ts s)@u) = (drop (length d) (x1 @ u))"
          using 
              starts_with_then_length_larger[OF 6]
              starts_with_concat_diff[OF starts_with_then_length_larger[OF 5] , of d u] 4  
          by simp
        then have "diff_conf (concatenate_tiles_seq_upper ts (a#s)) (concatenate_tiles_seq_bottom ts (a#s)) = {(UP (drop (length d) (x1 @ u)))}"
          by (metis "6" Pair T concat_head_tile concatenate_tiles_seq_bottom.simps(2) diff_conf.simps fst_conv snd_eqD)
          
        then show ?thesis using \<open>multi_step_pcp ts {UP []} (a # s) = {UP (drop (length d) (x1 @ u))}\<close> by presburger
      next
        case F1:False
        then show ?thesis proof (cases "starts_with d (x1 @ u)")
          case True
          then have "multi_step_pcp ts {UP []} (a # s) = {(DN (drop (length (x1 @ u)) d))}" using UP F1 A Pair by force
          then have "starts_with (concatenate_tiles_seq_bottom ts (a#s)) (concatenate_tiles_seq_upper ts (a#s))"
            using starts_with_concat_diff_opp[OF starts_with_then_length_larger[OF 5], of u d]
            by (metis "4" "5" Pair T True concat_head_tile_btm concatenate_tiles_seq_upper.simps(2) fst_eqD snd_eqD starts_with_concat_opp)
          then have "diff_conf (concatenate_tiles_seq_upper ts (a#s)) (concatenate_tiles_seq_bottom ts (a#s)) = {(DN (drop (length (x1 @ u)) d))}"
            by (metis "4" "5" F1 Pair T concat_head_tile concatenate_tiles_seq_bottom.simps(2) diff_conf.simps fst_conv length_append snd_conv starts_with_concat starts_with_concat_diff_opp starts_with_then_length_larger)
          then show ?thesis 
            using \<open>multi_step_pcp ts {UP []} (a # s) = {DN (drop (length (x1 @ u)) d)}\<close> by presburger
        next
          case False
          then have "multi_step_pcp ts {UP []} (a # s) = {}" using UP F1 A Pair by force
          then have "\<not>starts_with (concatenate_tiles_seq_upper ts (a#s)) (concatenate_tiles_seq_bottom ts (a#s))" 
            using starts_with_concat_diff[OF starts_with_then_length_larger[OF 5], of d u]
            by (metis "4" "5" F1 Pair T concat_head_tile concatenate_tiles_seq_bottom.simps(2) fst_conv snd_conv starts_with_concat)
          then have "diff_conf (concatenate_tiles_seq_upper ts (a#s)) (concatenate_tiles_seq_bottom ts (a#s)) = {}" 
            using "4" "5" False Pair T starts_with_concat_opp by auto
          then show ?thesis 
            using \<open>multi_step_pcp ts {UP []} (a # s) = {}\<close> by presburger
        qed
      qed
    next
      case (DN x1)
      have 4:"drop (length (concatenate_tiles_seq_upper ts s)) (concatenate_tiles_seq_bottom ts s) = x1"
        using False DN K by (metis config.distinct(1) config.inject(2) diff_conf.simps local.Cons singleton_inject)
      have 5:"starts_with  (concatenate_tiles_seq_bottom ts s) (concatenate_tiles_seq_upper ts s)"
        using K by (metis False DN config.distinct(1) diff_conf.simps local.Cons the_elem_eq)

      then show ?thesis proof (cases "starts_with u (x1 @ d)")
        case True
        then show ?thesis 
          by (metis "4" "5" A DN Pair T concat_head_tile concatenate_tiles_seq_bottom.simps(2) diff_conf.simps fst_conv length_append snd_conv starts_with_concat_diff_opp starts_with_concat_opp starts_with_then_length_larger step_config.simps(2))
      next
        case False
        then show ?thesis 
          by (metis "4" "5" A DN Pair T concat_head_tile concatenate_tiles_seq_bottom.simps(2) diff_conf.simps fst_conv length_append snd_conv starts_with_concat starts_with_concat_diff starts_with_concat_opp starts_with_then_length_larger step_config.simps(2))
      qed
    qed
    qed 
  qed
qed

lemma multi_step_conf_eq: 
  fixes ts::pcp
  fixes s::"nat list"
  assumes "all_lower s (length ts)"
  shows "multi_step_pcp ts {UP []} s = 
          diff_conf (concatenate_tiles_seq_upper ts s)  (concatenate_tiles_seq_bottom ts s)"
  using assms multi_step_conf_eq' by auto

lemma multi_step_conf_eq_sol: 
  fixes ts::pcp
  fixes s::"nat list"
  assumes "is_solution ts s"
  shows "(UP []) \<in> multi_step_pcp ts {UP []} s"
proof -
  have A:"multi_step_pcp ts {UP []} s= diff_conf (concatenate_tiles_seq_upper ts s)  (concatenate_tiles_seq_bottom ts s)" 
    using assms multi_step_conf_eq is_solution_def by auto
  have "(concatenate_tiles_seq_upper ts s) = (concatenate_tiles_seq_bottom ts s)" 
    using assms multi_step_conf_eq is_solution_def by auto
  then have "(UP []) \<in> diff_conf (concatenate_tiles_seq_upper ts s) (concatenate_tiles_seq_bottom ts s)" 
    using assms multi_step_conf_eq is_solution_def starts_with_def by auto
  then show ?thesis using A by auto
qed

lemma no_solution_if_exists_invariant:
  fixes ts::pcp
  assumes "\<exists>inv. is_invariant ts inv"
  shows "\<not> have_solution ts"
proof (cases "have_solution ts")
case True
  then obtain ans where sol_cond:"is_solution ts ans" using have_solution_def by auto
  then have contain_emp: "(UP '''') \<in> multi_step_pcp ts {(UP '''')} ans" using multi_step_conf_eq_sol by auto
  have nonempty: "length ans > 0" using is_solution_def sol_cond by auto
  obtain inv where inv_cond:"is_invariant ts inv" using assms by auto
  have False
  proof -
    have "(multi_step_pcp ts {(UP '''')} ans) \<subseteq> inv" 
        using all_resulting_conf_is_in_inv nonempty inv_cond sol_cond is_solution_def by auto
    then have "(UP '''') \<in> inv" using contain_emp by auto
    then show ?thesis using inv_cond is_invariant_def by auto
  qed
  then show ?thesis by auto
next
  case False
qed



end