theory aut1_conf_step_0_1111
  imports Main "PCPLib.PCPAutomata" "aut1_conf" "aut10_conf" "pcp_instance" "aut9_pref_quotient_1111" "aut1_append_word_0"
begin

lemma pref_quotient_lemma:
  "lang aut10 = lang (pref_quotient (append_word aut1 tile_2_up) tile_2_dn)"
proof -
  have "lang (append_word aut1 tile_2_up) = lang aut9"
    by (simp only: aut1_append_word_0 tile_2_up_def )

  then have A:"lang (pref_quotient (append_word aut1 tile_2_up) tile_2_dn) = lang (pref_quotient aut9 tile_2_dn)"
    by (simp only: pref_quotient_hom[of "append_word aut1 tile_2_up" aut9] )

  have "lang (pref_quotient aut9 tile_2_dn) = lang aut10"
    by (simp only: aut9_pref_quotient_1111 tile_2_dn_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut10_conf = lang_autconf (fst (step_autconf_tile aut1_conf tile_2))"
  apply (simp only: aut10_conf_def aut1_conf_def tile_2_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> {}"


lemma is_stepped_configs:
  "snd (step_autconf_tile aut1_conf tile_2) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_2_up) (enumerate_splits tile_2_dn)) = {}"
     apply (simp only: tile_2_dn_def)
     apply auto
     apply (simp_all only: aut1_def starts_with_def tile_2_up_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length tile_2_up) p)) ` ... = {}"
     apply (simp only: tile_2_up_def)
     by auto

   have "(\<lambda> (s,p). (drop (length tile_2_up) p)) ` (Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_2_up) (enumerate_splits tile_2_dn)) = {}"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile aut1_conf tile_2) = stepped_confs"
     by (simp add: aut1_conf_def tile_2_def stepped_confs_def)
 qed

end