theory aut1_append_word_1111 
  imports Main "aut1" "aut6" "aut1_append_ch_1" "aut3_append_ch_1" "aut4_append_ch_1" "aut5_append_ch_1"
begin

lemma "aut1_append_word_1111": "lang (append_word aut1 [C1,C1,C1,C1]) = lang aut6"
proof -
  have L0:"lang (append_word_rev aut1 []) = lang aut1"
    by (simp only: empty_app_word_rev[of aut1] )


  have "lang (append_word_rev aut1 [C1]) = lang (append_ch (append_word_rev aut1 []) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C1 "[]"] )
  then have "lang (append_word_rev aut1 [C1]) = lang (append_ch aut1 C1)"
    by (simp only: L0 append_ch_hom[of "append_word_rev aut1 []" aut1 C1] )
  then have L1:"lang (append_word_rev aut1 [C1]) = lang aut3"
    by (simp only: aut1_append_ch_1 )

  have "lang (append_word_rev aut1 [C1,C1]) = lang (append_ch (append_word_rev aut1 [C1]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C1 "[C1]"] )
  then have "lang (append_word_rev aut1 [C1,C1]) = lang (append_ch aut3 C1)"
    by (simp only: L1 append_ch_hom[of "append_word_rev aut1 [C1]" aut3 C1] )
  then have L2:"lang (append_word_rev aut1 [C1,C1]) = lang aut4"
    by (simp only: aut3_append_ch_1 )

  have "lang (append_word_rev aut1 [C1,C1,C1]) = lang (append_ch (append_word_rev aut1 [C1,C1]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C1 "[C1,C1]"] )
  then have "lang (append_word_rev aut1 [C1,C1,C1]) = lang (append_ch aut4 C1)"
    by (simp only: L2 append_ch_hom[of "append_word_rev aut1 [C1,C1]" aut4 C1] )
  then have L3:"lang (append_word_rev aut1 [C1,C1,C1]) = lang aut5"
    by (simp only: aut4_append_ch_1 )

  have "lang (append_word_rev aut1 [C1,C1,C1,C1]) = lang (append_ch (append_word_rev aut1 [C1,C1,C1]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut1" C1 "[C1,C1,C1]"] )
  then have "lang (append_word_rev aut1 [C1,C1,C1,C1]) = lang (append_ch aut5 C1)"
    by (simp only: L3 append_ch_hom[of "append_word_rev aut1 [C1,C1,C1]" aut5 C1] )
  then have L4:"lang (append_word_rev aut1 [C1,C1,C1,C1]) = lang aut6"
    by (simp only: aut5_append_ch_1 )


  have "rev [C1,C1,C1,C1] = [C1,C1,C1,C1]" by simp
  then have "append_word aut1 [C1,C1,C1,C1] = append_word_rev aut1 [C1,C1,C1,C1]" 
    by (simp only: append_word_rev_is_rev[of aut1 "[C1,C1,C1,C1]"])
  then show ?thesis using L4 by presburger
qed
end