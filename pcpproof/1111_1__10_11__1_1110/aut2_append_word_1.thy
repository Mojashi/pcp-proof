theory aut2_append_word_1 
  imports Main "aut2" "aut11" "aut2_append_ch_1"
begin

lemma "aut2_append_word_1": "lang (append_word aut2 [C1]) = lang aut11"
proof -
  have L0:"lang (append_word_rev aut2 []) = lang aut2"
    by (simp only: empty_app_word_rev[of aut2] )


  have "lang (append_word_rev aut2 [C1]) = lang (append_ch (append_word_rev aut2 []) C1)"
    by (simp only: append_word_lang_rev_to_ch[of "aut2" C1 "[]"] )
  then have "lang (append_word_rev aut2 [C1]) = lang (append_ch aut2 C1)"
    by (simp only: L0 append_ch_hom[of "append_word_rev aut2 []" aut2 C1] )
  then have L1:"lang (append_word_rev aut2 [C1]) = lang aut11"
    by (simp only: aut2_append_ch_1 )


  have "rev [C1] = [C1]" by simp
  then have "append_word aut2 [C1] = append_word_rev aut2 [C1]" 
    by (simp only: append_word_rev_is_rev[of aut2 "[C1]"])
  then show ?thesis using L1 by presburger
qed
end