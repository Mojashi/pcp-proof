theory {{theory_name}}
  imports Main "PCPLib.PCPAutomata" "{{src_autconf_path}}" "{{stepped_autconf_path}}" "{{instance_path}}" "{{pref_quotient_path}}" "{{append_word_path}}"
begin

lemma pref_quotient_lemma:
  "lang {{stepped_aut_name}} = lang (pref_quotient (append_word {{src_aut_name}} {{tile_samedir_name}}) {{tile_oppdir_name}})"
proof -
  have "lang (append_word {{src_aut_name}} {{tile_samedir_name}}) = lang {{appended_aut_name}}"
    by (simp only: {{append_word_lemma}} {{tile_samedir_name}}_def )

  then have A:"lang (pref_quotient (append_word {{src_aut_name}} {{tile_samedir_name}}) {{tile_oppdir_name}}) = lang (pref_quotient {{appended_aut_name}} {{tile_oppdir_name}})"
    by (simp only: pref_quotient_hom[of "append_word {{src_aut_name}} {{tile_samedir_name}}" {{appended_aut_name}}] )

  have "lang (pref_quotient {{appended_aut_name}} {{tile_oppdir_name}}) = lang {{stepped_aut_name}}"
    by (simp only: {{pref_quotient_lemma}} {{tile_oppdir_name}}_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf {{stepped_autconf_name}} = lang_autconf (fst (step_autconf_tile {{src_autconf_name}} {{tile}}))"
  apply (simp only: {{stepped_autconf_name}}_def {{src_autconf_name}}_def {{tile}}_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> { {{~stepped_confs~}} }"


lemma is_stepped_configs:
  "snd (step_autconf_tile {{src_autconf_name}} {{tile}}) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' {{src_aut_name}} s \<and> starts_with p {{tile_samedir_name}}) ({{enumerate_splits_fun_name}} {{tile_oppdir_name}})) = { {{~stepped_strings_in_splits~}} }"
     apply (simp only: {{tile_oppdir_name}}_def)
     apply auto
     apply (simp_all only: {{src_aut_name}}_def starts_with_def {{tile_samedir_name}}_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length {{tile_samedir_name}}) p)) ` ... = { {{~stepped_strings~}} }"
     apply (simp only: {{tile_samedir_name}}_def)
     by auto

   have "(\<lambda> (s,p). (drop (length {{tile_samedir_name}}) p)) ` (Set.filter (\<lambda>(s,p). accept' {{src_aut_name}} s \<and> starts_with p {{tile_samedir_name}}) ({{enumerate_splits_fun_name}} {{tile_oppdir_name}})) = { {{~stepped_strings~}} }"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile {{src_autconf_name}} {{tile}}) = stepped_confs"
     by (simp add: {{src_autconf_name}}_def {{tile}}_def stepped_confs_def)
 qed

end