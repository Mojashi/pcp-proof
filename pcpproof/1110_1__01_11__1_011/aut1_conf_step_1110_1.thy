theory aut1_conf_step_1110_1
  imports Main "PCPLib.PCPAutomata" "aut1_conf" "aut7_conf" "pcp_instance" "aut6_pref_quotient_1" "aut1_append_word_1110"
begin

lemma pref_quotient_lemma:
  "lang aut7 = lang (pref_quotient (append_word aut1 tile_0_up) tile_0_dn)"
proof -
  have "lang (append_word aut1 tile_0_up) = lang aut6"
    by (simp only: aut1_append_word_1110 tile_0_up_def )

  then have A:"lang (pref_quotient (append_word aut1 tile_0_up) tile_0_dn) = lang (pref_quotient aut6 tile_0_dn)"
    by (simp only: pref_quotient_hom[of "append_word aut1 tile_0_up" aut6] )

  have "lang (pref_quotient aut6 tile_0_dn) = lang aut7"
    by (simp only: aut6_pref_quotient_1 tile_0_dn_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut7_conf = lang_autconf (fst (step_autconf_tile aut1_conf tile_0))"
  apply (simp only: aut7_conf_def aut1_conf_def tile_0_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> {}"


lemma is_stepped_configs:
  "snd (step_autconf_tile aut1_conf tile_0) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_0_up) (enumerate_splits tile_0_dn)) = {}"
     apply (simp only: tile_0_dn_def)
     apply auto
     apply (simp_all only: aut1_def starts_with_def tile_0_up_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length tile_0_up) p)) ` ... = {}"
     apply (simp only: tile_0_up_def)
     by auto

   have "(\<lambda> (s,p). (drop (length tile_0_up) p)) ` (Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_0_up) (enumerate_splits tile_0_dn)) = {}"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile aut1_conf tile_0) = stepped_confs"
     by (simp add: aut1_conf_def tile_0_def stepped_confs_def)
 qed

end