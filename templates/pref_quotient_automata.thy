theory {{theory_name}}
  imports Main "PCPLib.PCP" "PCPLib.Automata" "{{orig_aut_path}}"
begin

type_alias State = {{orig_aut_name}}.State

alias transition = {{orig_aut_name}}.transition

definition {{theory_name}}::"(alphabet, State) da" where
 "{{theory_name}} \<equiv> da {{initial_state}} transition { {{~accept_states~}} }"
end