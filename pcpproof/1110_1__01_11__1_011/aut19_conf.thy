theory aut19_conf
  imports Main "PCPLib.PCPAutomata" "aut19"
begin

definition aut19_conf::"State autconfig" where
 "aut19_conf \<equiv> DN aut19"

end