theory aut7_conf
  imports Main "PCPLib.PCPAutomata" "aut7"
begin

definition aut7_conf::"State autconfig" where
 "aut7_conf \<equiv> UP aut7"

end