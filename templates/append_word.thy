theory {{theory_name}} 
  imports Main "{{src_aut_path}}" "{{dest_aut_path}}" {{{eq_lemma_paths}}}
begin

lemma "{{theory_name}}": "lang (append_word {{src_aut_name}} {{w}}) = lang {{dest_aut_name}}"
proof -
  have L0:"lang (append_word_rev {{src_aut_name}} []) = lang {{src_aut_name}}"
    by (simp only: empty_app_word_rev[of {{src_aut_name}}] )

{{#each ch_steps}}
  have "lang (append_word_rev {{@root.src_aut_name}} {{cur_w}}) = lang (append_ch (append_word_rev {{@root.src_aut_name}} {{prev_w}}) {{cur_ch}})"
    by (simp only: append_word_lang_rev_to_ch[of "{{@root.src_aut_name}}" {{cur_ch}} "{{prev_w}}"] )
  then have "lang (append_word_rev {{@root.src_aut_name}} {{cur_w}}) = lang (append_ch {{prev_aut_name}} {{cur_ch}})"
    by (simp only: {{prev_lemma_name}} append_ch_hom[of "append_word_rev {{@root.src_aut_name}} {{prev_w}}" {{prev_aut_name}} {{cur_ch}}] )
  then have {{cur_lemma_name}}:"lang (append_word_rev {{@root.src_aut_name}} {{cur_w}}) = lang {{next_aut_name}}"
    by (simp only: {{prev_eq_nex_lemma}} )
{{/each}}

  have "rev {{w}} = {{rev_w}}" by simp
  then have "append_word {{src_aut_name}} {{w}} = append_word_rev {{src_aut_name}} {{rev_w}}" 
    by (simp only: append_word_rev_is_rev[of {{src_aut_name}} "{{w}}"])
  then show ?thesis using {{last_lemma_name}} by presburger
qed
end