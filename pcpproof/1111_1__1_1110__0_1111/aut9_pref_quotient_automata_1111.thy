theory aut9_pref_quotient_automata_1111
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut9"
begin

type_alias State = aut9.State

alias transition = aut9.transition

definition aut9_pref_quotient_automata_1111::"(alphabet, State) da" where
 "aut9_pref_quotient_automata_1111 \<equiv> da (aut9.State_R aut9.state_level1_Leaf) transition {(aut9.State_L aut9.state_level1_Leaf)}"
end