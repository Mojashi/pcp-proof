theory aut12_pref_quotient_automata_1110
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut12"
begin

type_alias State = aut12.State

alias transition = aut12.transition

definition aut12_pref_quotient_automata_1110::"(alphabet, State) da" where
 "aut12_pref_quotient_automata_1110 \<equiv> da (aut12.State_R aut12.state_level1_Leaf) transition {aut12.State_Leaf}"
end