theory aut12_conf
  imports Main "PCPLib.PCPAutomata" "aut12"
begin

definition aut12_conf::"State autconfig" where
 "aut12_conf \<equiv> DN aut12"

end