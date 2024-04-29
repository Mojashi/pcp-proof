theory aut11_conf
  imports Main "PCPLib.PCPAutomata" "aut11"
begin

definition aut11_conf::"State autconfig" where
 "aut11_conf \<equiv> UP aut11"

end