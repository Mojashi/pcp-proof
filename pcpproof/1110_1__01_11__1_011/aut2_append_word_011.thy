theory aut2_append_word_011 
  imports Main "aut2" "aut18" "aut2_append_ch_0" "aut16_append_ch_1" "aut17_append_ch_1"
begin

lemma "aut2_append_word_011": "lang (append_word aut2 [C0,C1,C1]) = lang aut18"
proof -
  have L0:"lang (append_word_rev aut2 []) = lang aut2"
    by (simp only: empty_app_word_rev[of aut2] )


  have "lang (append_word_rev aut2 [C0]) = lang (append_ch (append_word_rev aut2 []) C0)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C0 "[]"] )
  then have "lang (append_word_rev aut2 [C0]) = lang (append_ch aut2 C0)"
    by (simp only: L0 append_ch_hom[of "append_word_rev aut2 []" aut2 C0] )
  then have L1:"lang (append_word_rev aut2 [C0]) = lang aut16"
    by (simp only: aut2_append_ch_0 )

  have "lang (append_word_rev aut2 [C1,C0]) = lang (append_ch (append_word_rev aut2 [C0]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C1 "[C0]"] )
  then have "lang (append_word_rev aut2 [C1,C0]) = lang (append_ch aut16 C1)"
    by (simp only: L1 append_ch_hom[of "append_word_rev aut2 [C0]" aut16 C1] )
  then have L2:"lang (append_word_rev aut2 [C1,C0]) = lang aut17"
    by (simp only: aut16_append_ch_1 )

  have "lang (append_word_rev aut2 [C1,C1,C0]) = lang (append_ch (append_word_rev aut2 [C1,C0]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C1 "[C1,C0]"] )
  then have "lang (append_word_rev aut2 [C1,C1,C0]) = lang (append_ch aut17 C1)"
    by (simp only: L2 append_ch_hom[of "append_word_rev aut2 [C1,C0]" aut17 C1] )
  then have L3:"lang (append_word_rev aut2 [C1,C1,C0]) = lang aut18"
    by (simp only: aut17_append_ch_1 )


  have "rev [C0,C1,C1] = [C1,C1,C0]" by simp
  then have "append_word aut2 [C0,C1,C1] = append_word_rev aut2 [C1,C1,C0]" 
    by (simp only: append_word_rev_is_rev[of aut2 "[C0,C1,C1]"])
  then show ?thesis using L3 by presburger
qed
end