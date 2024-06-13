theory aut1_conf
  imports Main "PCPLib.PCPAutomata" "aut1"
begin

definition aut1_conf::"State autconfig" where
 "aut1_conf \<equiv> UP aut1"

end