theory aut15_conf
  imports Main "PCPLib.PCPAutomata" "aut15"
begin

definition aut15_conf::"State autconfig" where
 "aut15_conf \<equiv> DN aut15"

end