theory {{theory_name}}
  imports Main {{{member_paths}}}
begin

definition {{autset_name}} :: "PCPTrans.config set" where
  "{{autset_name}} \<equiv> {{#each members}} (lang_autconf {{this}}) {{#unless @last}}\<union>{{/unless}}{{/each}}"

end