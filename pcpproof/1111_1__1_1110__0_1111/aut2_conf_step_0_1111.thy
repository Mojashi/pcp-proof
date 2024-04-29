theory aut2_conf_step_0_1111
  imports Main "PCPLib.PCPAutomata" "aut2_conf" "aut18_conf" "pcp_instance" "aut17_pref_quotient_0" "aut2_append_word_1111"
begin

lemma pref_quotient_lemma:
  "lang aut18 = lang (pref_quotient (append_word aut2 tile_2_dn) tile_2_up)"
proof -
  have "lang (append_word aut2 tile_2_dn) = lang aut17"
    by (simp only: aut2_append_word_1111 tile_2_dn_def )

  then have A:"lang (pref_quotient (append_word aut2 tile_2_dn) tile_2_up) = lang (pref_quotient aut17 tile_2_up)"
    by (simp only: pref_quotient_hom[of "append_word aut2 tile_2_dn" aut17] )

  have "lang (pref_quotient aut17 tile_2_up) = lang aut18"
    by (simp only: aut17_pref_quotient_0 tile_2_up_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut18_conf = lang_autconf (fst (step_autconf_tile aut2_conf tile_2))"
  apply (simp only: aut18_conf_def aut2_conf_def tile_2_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> {}"


lemma is_stepped_configs:
  "snd (step_autconf_tile aut2_conf tile_2) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' aut2 s \<and> starts_with p tile_2_dn) (enumerate_splits_all tile_2_up)) = {}"
     apply (simp only: tile_2_up_def)
     apply auto
     apply (simp_all only: aut2_def starts_with_def tile_2_dn_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length tile_2_dn) p)) ` ... = {}"
     apply (simp only: tile_2_dn_def)
     by auto

   have "(\<lambda> (s,p). (drop (length tile_2_dn) p)) ` (Set.filter (\<lambda>(s,p). accept' aut2 s \<and> starts_with p tile_2_dn) (enumerate_splits_all tile_2_up)) = {}"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile aut2_conf tile_2) = stepped_confs"
     by (simp add: aut2_conf_def tile_2_def stepped_confs_def)
 qed

end