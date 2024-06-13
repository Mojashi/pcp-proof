theory inv
  imports Main "aut1_conf" "aut2_conf"
begin

definition inv :: "PCPTrans.config set" where
  "inv \<equiv>  (lang_autconf aut1_conf) \<union> (lang_autconf aut2_conf) "

end