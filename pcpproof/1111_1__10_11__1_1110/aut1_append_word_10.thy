theory aut1_append_word_10 
  imports Main "aut1" "aut8" "aut1_append_ch_1" "aut3_append_ch_0"
begin

lemma "aut1_append_word_10": "lang (append_word aut1 [C1,C0]) = lang aut8"
proof -
  have L0:"lang (append_word_rev aut1 []) = lang aut1"
    by (simp only: empty_app_word_rev[of aut1] )


  have "lang (append_word_rev aut1 [C1]) = lang (append_ch (append_word_rev aut1 []) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C1 "[]"] )
  then have "lang (append_word_rev aut1 [C1]) = lang (append_ch aut1 C1)"
    by (simp only: L0 append_ch_hom[of "append_word_rev aut1 []" aut1 C1] )
  then have L1:"lang (append_word_rev aut1 [C1]) = lang aut3"
    by (simp only: aut1_append_ch_1 )

  have "lang (append_word_rev aut1 [C0,C1]) = lang (append_ch (append_word_rev aut1 [C1]) C0)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C0 "[C1]"] )
  then have "lang (append_word_rev aut1 [C0,C1]) = lang (append_ch aut3 C0)"
    by (simp only: L1 append_ch_hom[of "append_word_rev aut1 [C1]" aut3 C0] )
  then have L2:"lang (append_word_rev aut1 [C0,C1]) = lang aut8"
    by (simp only: aut3_append_ch_0 )


  have "rev [C1,C0] = [C0,C1]" by simp
  then have "append_word aut1 [C1,C0] = append_word_rev aut1 [C0,C1]" 
    by (simp only: append_word_rev_is_rev[of aut1 "[C1,C0]"])
  then show ?thesis using L2 by presburger
qed
end