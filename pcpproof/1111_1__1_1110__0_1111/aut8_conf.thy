theory aut8_conf
  imports Main "PCPLib.PCPAutomata" "aut8"
begin

definition aut8_conf::"State autconfig" where
 "aut8_conf \<equiv> UP aut8"

end