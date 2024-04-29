theory aut2_conf_step_01_11
  imports Main "PCPLib.PCPAutomata" "aut2_conf" "aut15_conf" "pcp_instance" "aut14_pref_quotient_01" "aut2_append_word_11"
begin

lemma pref_quotient_lemma:
  "lang aut15 = lang (pref_quotient (append_word aut2 tile_1_dn) tile_1_up)"
proof -
  have "lang (append_word aut2 tile_1_dn) = lang aut14"
    by (simp only: aut2_append_word_11 tile_1_dn_def )

  then have A:"lang (pref_quotient (append_word aut2 tile_1_dn) tile_1_up) = lang (pref_quotient aut14 tile_1_up)"
    by (simp only: pref_quotient_hom[of "append_word aut2 tile_1_dn" aut14] )

  have "lang (pref_quotient aut14 tile_1_up) = lang aut15"
    by (simp only: aut14_pref_quotient_01 tile_1_up_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut15_conf = lang_autconf (fst (step_autconf_tile aut2_conf tile_1))"
  apply (simp only: aut15_conf_def aut2_conf_def tile_1_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> {}"


lemma is_stepped_configs:
  "snd (step_autconf_tile aut2_conf tile_1) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' aut2 s \<and> starts_with p tile_1_dn) (enumerate_splits_all tile_1_up)) = {}"
     apply (simp only: tile_1_up_def)
     apply auto
     apply (simp_all only: aut2_def starts_with_def tile_1_dn_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length tile_1_dn) p)) ` ... = {}"
     apply (simp only: tile_1_dn_def)
     by auto

   have "(\<lambda> (s,p). (drop (length tile_1_dn) p)) ` (Set.filter (\<lambda>(s,p). accept' aut2 s \<and> starts_with p tile_1_dn) (enumerate_splits_all tile_1_up)) = {}"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile aut2_conf tile_1) = stepped_confs"
     by (simp add: aut2_conf_def tile_1_def stepped_confs_def)
 qed

end