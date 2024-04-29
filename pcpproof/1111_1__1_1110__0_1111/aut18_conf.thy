theory aut18_conf
  imports Main "PCPLib.PCPAutomata" "aut18"
begin

definition aut18_conf::"State autconfig" where
 "aut18_conf \<equiv> DN aut18"

end