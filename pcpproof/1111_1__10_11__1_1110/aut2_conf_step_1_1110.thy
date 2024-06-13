theory aut2_conf_step_1_1110
  imports Main "PCPLib.PCPAutomata" "aut2_conf" "aut17_conf" "pcp_instance" "aut16_pref_quotient_1" "aut2_append_word_1110"
begin

lemma pref_quotient_lemma:
  "lang aut17 = lang (pref_quotient (append_word aut2 tile_2_dn) tile_2_up)"
proof -
  have "lang (append_word aut2 tile_2_dn) = lang aut16"
    by (simp only: aut2_append_word_1110 tile_2_dn_def )

  then have A:"lang (pref_quotient (append_word aut2 tile_2_dn) tile_2_up) = lang (pref_quotient aut16 tile_2_up)"
    by (simp only: pref_quotient_hom[of "append_word aut2 tile_2_dn" aut16] )

  have "lang (pref_quotient aut16 tile_2_up) = lang aut17"
    by (simp only: aut16_pref_quotient_1 tile_2_up_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut17_conf = lang_autconf (fst (step_autconf_tile aut2_conf tile_2))"
  apply (simp only: aut17_conf_def aut2_conf_def tile_2_def)
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