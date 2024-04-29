theory {{theory_name}}
  imports Main "PCPLib.PCPAutomata" "{{AutPath}}"
begin

definition {{theory_name}}::"State autconfig" where
 "{{theory_name}} \<equiv> {{dir}} {{aut_name}}"

end