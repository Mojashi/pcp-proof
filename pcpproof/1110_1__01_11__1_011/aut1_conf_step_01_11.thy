theory aut1_conf_step_01_11
  imports Main "PCPLib.PCPAutomata" "aut1_conf" "aut10_conf" "pcp_instance" "aut9_pref_quotient_11" "aut1_append_word_01"
begin

lemma pref_quotient_lemma:
  "lang aut10 = lang (pref_quotient (append_word aut1 tile_1_up) tile_1_dn)"
proof -
  have "lang (append_word aut1 tile_1_up) = lang aut9"
    by (simp only: aut1_append_word_01 tile_1_up_def )

  then have A:"lang (pref_quotient (append_word aut1 tile_1_up) tile_1_dn) = lang (pref_quotient aut9 tile_1_dn)"
    by (simp only: pref_quotient_hom[of "append_word aut1 tile_1_up" aut9] )

  have "lang (pref_quotient aut9 tile_1_dn) = lang aut10"
    by (simp only: aut9_pref_quotient_11 tile_1_dn_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut10_conf = lang_autconf (fst (step_autconf_tile aut1_conf tile_1))"
  apply (simp only: aut10_conf_def aut1_conf_def tile_1_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> {}"


lemma is_stepped_configs:
  "snd (step_autconf_tile aut1_conf tile_1) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_1_up) (enumerate_splits tile_1_dn)) = {}"
     apply (simp only: tile_1_dn_def)
     apply auto
     apply (simp_all only: aut1_def starts_with_def tile_1_up_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length tile_1_up) p)) ` ... = {}"
     apply (simp only: tile_1_up_def)
     by auto

   have "(\<lambda> (s,p). (drop (length tile_1_up) p)) ` (Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_1_up) (enumerate_splits tile_1_dn)) = {}"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile aut1_conf tile_1) = stepped_confs"
     by (simp add: aut1_conf_def tile_1_def stepped_confs_def)
 qed

end