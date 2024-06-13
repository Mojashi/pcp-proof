theory aut14_conf
  imports Main "PCPLib.PCPAutomata" "aut14"
begin

definition aut14_conf::"State autconfig" where
 "aut14_conf \<equiv> DN aut14"

end