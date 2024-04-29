theory {{theory_name}}
  imports Main "PCPLib.PCP" "PCPLib.PCPTrans" {{{member_paths}}} {{{stepped_paths}}}  "{{pcp_instance_path}}" {{{contain_lemma_paths}}} {{autset_path}}
begin

theorem {{theory_name}}:
  "pcp_step_configs pcp_instance {{autset_name}} \<subseteq> {{autset_name}}"
proof -
  have "\<forall>s t. s \<in> {{autset_name}} \<longrightarrow> List.member pcp_instance t \<longrightarrow> (step_config t s) \<subseteq> {{autset_name}}"
  proof (rule allI, rule allI, rule impI, rule impI)
    fix s t
    assume ASM: "s \<in> {{autset_name}}" "List.member pcp_instance t"

    consider {{#each tiles}} (t{{@index}}) "t={{this}}" {{#unless @last}}|{{/unless}} {{/each}}
      using ASM(2) pcp_instance_def member_rec(1) member_rec(2) by metis

    then show "(step_config t s) \<subseteq> {{autset_name}}"
    proof (cases)
    {{#each tiles}}
      case t{{@index}}
      
      consider {{#each @root.members}} (s{{@index}}) "s\<in>lang_autconf {{this.name}}" {{#unless @last}}|{{/unless}} {{/each}}
        using {{@root.autset_name}}_def ASM(1) by auto
      then show ?thesis proof (cases)
      {{#each @root.members}}
        case s{{@index}}
        have A1:"lang_autconf (fst (step_autconf_tile {{name}} t)) = lang_autconf {{lookup stepped_autconf @../index}}"
          by (simp only: {{lookup stepped_autconf_lemma @../index}} t{{@../index}} )

        then have A2:"... \<subseteq> lang_autconf {{lookup stepped_autconf_covering_autconf @../index}}"
          apply (simp only: {{lookup stepped_autconf_covering_autconf @../index}}_def {{lookup stepped_autconf @../index}}_def )
          using  {{lookup stepped_autconf_covering_lemma @../index}} by auto

        have B1:"snd (step_autconf_tile {{name}} t) = {{lookup stepped_configs @../index}}" 
          by (simp only: {{lookup stepped_configs_lemma @../index}} t{{@../index}} )
        
        then have B2:"... \<subseteq> {{{(lookup stepped_configs_covering_autconfs @../index)}}}" 
          by (simp add: {{lookup stepped_configs_covering_lemmas @../index}} {{lookup stepped_configs @../index}}_def)
        
        then show ?thesis 
          using step_autconf_tile_eq_l[of {{name}} t "lang_autconf (fst (step_autconf_tile {{name}} t))" "snd (step_autconf_tile {{name}} t)" ]  
            A1 B1 A2 B2  {{@root.autset_name}}_def s{{@index}} by fastforce
        next
      {{/each}}
      qed

      next
      {{/each}}
    qed
  qed
  then have "\<forall>s \<in> {{autset_name}}. (pcp_step_config pcp_instance s) \<subseteq> {{autset_name}}"
    using member_def by fastforce
  then show ?thesis by auto
qed


end