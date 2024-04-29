theory aut13_conf
  imports Main "PCPLib.PCPAutomata" "aut13"
begin

definition aut13_conf::"State autconfig" where
 "aut13_conf \<equiv> DN aut13"

end