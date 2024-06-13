theory aut17_conf
  imports Main "PCPLib.PCPAutomata" "aut17"
begin

definition aut17_conf::"State autconfig" where
 "aut17_conf \<equiv> DN aut17"

end