theory aut16_conf
  imports Main "PCPLib.PCPAutomata" "aut16"
begin

definition aut16_conf::"State autconfig" where
 "aut16_conf \<equiv> DN aut16"

end