theory aut2_conf
  imports Main "PCPLib.PCPAutomata" "aut2"
begin

definition aut2_conf::"State autconfig" where
 "aut2_conf \<equiv> DN aut2"

end