theory aut2_append_word_1110 
  imports Main "aut2" "aut15" "aut2_append_ch_1" "aut11_append_ch_1" "aut13_append_ch_1" "aut14_append_ch_0"
begin

lemma "aut2_append_word_1110": "lang (append_word aut2 [C1,C1,C1,C0]) = lang aut15"
proof -
  have L0:"lang (append_word_rev aut2 []) = lang aut2"
    by (simp only: empty_app_word_rev[of aut2] )


  have "lang (append_word_rev aut2 [C1]) = lang (append_ch (append_word_rev aut2 []) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C1 "[]"] )
  then have "lang (append_word_rev aut2 [C1]) = lang (append_ch aut2 C1)"
    by (simp only: L0 append_ch_hom[of "append_word_rev aut2 []" aut2 C1] )
  then have L1:"lang (append_word_rev aut2 [C1]) = lang aut11"
    by (simp only: aut2_append_ch_1 )

  have "lang (append_word_rev aut2 [C1,C1]) = lang (append_ch (append_word_rev aut2 [C1]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C1 "[C1]"] )
  then have "lang (append_word_rev aut2 [C1,C1]) = lang (append_ch aut11 C1)"
    by (simp only: L1 append_ch_hom[of "append_word_rev aut2 [C1]" aut11 C1] )
  then have L2:"lang (append_word_rev aut2 [C1,C1]) = lang aut13"
    by (simp only: aut11_append_ch_1 )

  have "lang (append_word_rev aut2 [C1,C1,C1]) = lang (append_ch (append_word_rev aut2 [C1,C1]) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C1 "[C1,C1]"] )
  then have "lang (append_word_rev aut2 [C1,C1,C1]) = lang (append_ch aut13 C1)"
    by (simp only: L2 append_ch_hom[of "append_word_rev aut2 [C1,C1]" aut13 C1] )
  then have L3:"lang (append_word_rev aut2 [C1,C1,C1]) = lang aut14"
    by (simp only: aut13_append_ch_1 )

  have "lang (append_word_rev aut2 [C0,C1,C1,C1]) = lang (append_ch (append_word_rev aut2 [C1,C1,C1]) C0)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C0 "[C1,C1,C1]"] )
  then have "lang (append_word_rev aut2 [C0,C1,C1,C1]) = lang (append_ch aut14 C0)"
    by (simp only: L3 append_ch_hom[of "append_word_rev aut2 [C1,C1,C1]" aut14 C0] )
  then have L4:"lang (append_word_rev aut2 [C0,C1,C1,C1]) = lang aut15"
    by (simp only: aut14_append_ch_0 )


  have "rev [C1,C1,C1,C0] = [C0,C1,C1,C1]" by simp
  then have "append_word aut2 [C1,C1,C1,C0] = append_word_rev aut2 [C0,C1,C1,C1]" 
    by (simp only: append_word_rev_is_rev[of aut2 "[C1,C1,C1,C0]"])
  then show ?thesis using L4 by presburger
qed
end