theory aut2_conf_step_1111_1
  imports Main "PCPLib.PCPAutomata" "aut2_conf" "aut12_conf" "pcp_instance" "aut11_pref_quotient_1111" "aut2_append_word_1"
begin

lemma pref_quotient_lemma:
  "lang aut12 = lang (pref_quotient (append_word aut2 tile_0_dn) tile_0_up)"
proof -
  have "lang (append_word aut2 tile_0_dn) = lang aut11"
    by (simp only: aut2_append_word_1 tile_0_dn_def )

  then have A:"lang (pref_quotient (append_word aut2 tile_0_dn) tile_0_up) = lang (pref_quotient aut11 tile_0_up)"
    by (simp only: pref_quotient_hom[of "append_word aut2 tile_0_dn" aut11] )

  have "lang (pref_quotient aut11 tile_0_up) = lang aut12"
    by (simp only: aut11_pref_quotient_1111 tile_0_up_def )
  then show ?thesis using A by simp
qed


lemma is_stepped_autconf:
  "lang_autconf aut12_conf = lang_autconf (fst (step_autconf_tile aut2_conf tile_0))"
  apply (simp only: aut12_conf_def aut2_conf_def tile_0_def)
  using pref_quotient_lemma by auto


definition stepped_confs::"PCPTrans.config set" where
  "stepped_confs \<equiv> {(PCPTrans.UP [C1,C1]), (PCPTrans.UP [C1])}"


lemma is_stepped_configs:
  "snd (step_autconf_tile aut2_conf tile_0) = stepped_confs"
proof -

   have A1:"(Set.filter (\<lambda>(s,p). accept' aut2 s \<and> starts_with p tile_0_dn) (enumerate_splits_all tile_0_up)) = {([C1], [C1,C1,C1]), ([C1,C1], [C1,C1])}"
     apply (simp only: tile_0_up_def)
     apply auto
     apply (simp_all only: aut2_def starts_with_def tile_0_dn_def)
     by auto

   have A2:"(\<lambda> (s,p). (drop (length tile_0_dn) p)) ` ... = {[C1,C1], [C1]}"
     apply (simp only: tile_0_dn_def)
     by auto

   have "(\<lambda> (s,p). (drop (length tile_0_dn) p)) ` (Set.filter (\<lambda>(s,p). accept' aut2 s \<and> starts_with p tile_0_dn) (enumerate_splits_all tile_0_up)) = {[C1,C1], [C1]}"
     by (simp only:A1 A2)

   then show "snd (step_autconf_tile aut2_conf tile_0) = stepped_confs"
     by (simp add: aut2_conf_def tile_0_def stepped_confs_def)
 qed

end