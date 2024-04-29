theory pcp_instance
  imports Main "PCPLib.PCP" "PCPLib.PCPTrans"
begin

definition tile_0_up::"alphabet list" where"tile_0_up \<equiv> [C1,C1,C1,C1]"
definition tile_0_dn::"alphabet list" where"tile_0_dn \<equiv> [C1]"
definition tile_0::"tile" where"tile_0 \<equiv> (tile_0_up,tile_0_dn)"
definition tile_1_up::"alphabet list" where"tile_1_up \<equiv> [C1]"
definition tile_1_dn::"alphabet list" where"tile_1_dn \<equiv> [C1,C1,C1,C0]"
definition tile_1::"tile" where"tile_1 \<equiv> (tile_1_up,tile_1_dn)"
definition tile_2_up::"alphabet list" where"tile_2_up \<equiv> [C0]"
definition tile_2_dn::"alphabet list" where"tile_2_dn \<equiv> [C1,C1,C1,C1]"
definition tile_2::"tile" where"tile_2 \<equiv> (tile_2_up,tile_2_dn)"

definition pcp_instance::"pcp" where
  "pcp_instance \<equiv> [ tile_0, tile_1, tile_2 ]"

definition init_conf_0::"config" where"init_conf_0 \<equiv> UP [C1,C1,C1]"
definition init_conf_1::"config" where"init_conf_1 \<equiv> DN [C1,C1,C0]"

lemma init_eq: "pcp_init_set pcp_instance = { init_conf_0, init_conf_1 }"
  apply (simp only: pcp_instance_def init_conf_0_def init_conf_1_def tile_0_up_def tile_0_dn_def tile_0_def tile_1_up_def tile_1_dn_def tile_1_def tile_2_up_def tile_2_dn_def tile_2_def)
  using starts_with_def by auto
end