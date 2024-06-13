theory aut3_pref_quotient_automata_1110
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut3"
begin

type_alias State = aut3.State

alias transition = aut3.transition

definition aut3_pref_quotient_automata_1110::"(alphabet, State) da" where
 "aut3_pref_quotient_automata_1110 \<equiv> da aut3.State_Leaf transition {(aut3.State_R aut3.state_level1_Leaf)}"
end