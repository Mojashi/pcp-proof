theory aut10_conf
  imports Main "PCPLib.PCPAutomata" "aut10"
begin

definition aut10_conf::"State autconfig" where
 "aut10_conf \<equiv> UP aut10"

end