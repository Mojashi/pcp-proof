theory aut1_append_word_01 
  imports Main "aut1" "aut9" "aut1_append_ch_0" "aut8_append_ch_1"
begin

lemma "aut1_append_word_01": "lang (append_word aut1 [C0,C1]) = lang aut9"
proof -
  have L0:"lang (append_word_rev aut1 []) = lang aut1"
    by (simp only: empty_app_word_rev[of aut1] )


  have "lang (append_word_rev aut1 [C0]) = lang (append_ch (append_word_rev aut1 []) C0)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C0 "[]"] )
  then have "lang (append_word_rev aut1 [C0]) = lang (append_ch aut1 C0)"
    by (simp only: L0 append_ch_hom[of "append_word_rev aut1 []" aut1 C0] )
  then have L1:"lang (append_word_rev aut1 [C0]) = lang aut8"
    by (simp only: aut1_append_ch_0 )

  have "lang (append_word_rev aut1 [C1,C0]) = lang (append_ch (append_word_rev aut1 [C0]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C1 "[C0]"] )
  then have "lang (append_word_rev aut1 [C1,C0]) = lang (append_ch aut8 C1)"
    by (simp only: L1 append_ch_hom[of "append_word_rev aut1 [C0]" aut8 C1] )
  then have L2:"lang (append_word_rev aut1 [C1,C0]) = lang aut9"
    by (simp only: aut8_append_ch_1 )


  have "rev [C0,C1] = [C1,C0]" by simp
  then have "append_word aut1 [C0,C1] = append_word_rev aut1 [C1,C0]" 
    by (simp only: append_word_rev_is_rev[of aut1 "[C0,C1]"])
  then show ?thesis using L2 by presburger
qed
end