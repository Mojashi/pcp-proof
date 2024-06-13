theory aut9_conf
  imports Main "PCPLib.PCPAutomata" "aut9"
begin

definition aut9_conf::"State autconfig" where
 "aut9_conf \<equiv> UP aut9"

end