theory aut1_conf_step_1_011
  imports Main "PCPLib.PCPAutomata" "aut1_conf" "aut11_conf" "pcp_instance" "aut3_pref_quotient_011" "aut1_append_word_1"
begin

lemma pref_quotient_lemma:
  "lang aut11 = lang (pref_quotient (append_word aut1 tile_2_up) tile_2_dn)"
proof -
  have "lang (append_word aut1 tile_2_up) = lang aut3"
    by (simp only: aut1_append_word_1 tile_2_up_def )

  then have A:"lang (pref_quotient (append_word aut1 tile_2_up) tile_2_dn) = lang (pref_quotient aut3 tile_2_dn)"
    by (simp only: pref_quotient_hom[of "append_word aut1 tile_2_up" aut3] )

  have "lang (pref_quotient aut3 tile_2_dn) = lang aut11"
    by (simp only: aut3_pref_quotient_011 tile_2_dn_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut11_conf = lang_autconf (fst (step_autconf_tile aut1_conf tile_2))"
  apply (simp only: aut11_conf_def aut1_conf_def tile_2_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> {(PCPTrans.DN [C1])}"


lemma is_stepped_configs:
  "snd (step_autconf_tile aut1_conf tile_2) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_2_up) (enumerate_splits tile_2_dn)) = {([C0], [C1,C1])}"
     apply (simp only: tile_2_dn_def)
     apply auto
     apply (simp_all only: aut1_def starts_with_def tile_2_up_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length tile_2_up) p)) ` ... = {[C1]}"
     apply (simp only: tile_2_up_def)
     by auto

   have "(\<lambda> (s,p). (drop (length tile_2_up) p)) ` (Set.filter (\<lambda>(s,p). accept' aut1 s \<and> starts_with p tile_2_up) (enumerate_splits tile_2_dn)) = {[C1]}"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile aut1_conf tile_2) = stepped_confs"
     by (simp add: aut1_conf_def tile_2_def stepped_confs_def)
 qed

end