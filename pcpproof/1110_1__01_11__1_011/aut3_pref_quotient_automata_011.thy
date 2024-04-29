theory aut3_pref_quotient_automata_011
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut3"
begin

type_alias State = aut3.State

alias transition = aut3.transition

definition aut3_pref_quotient_automata_011::"(alphabet, State) da" where
 "aut3_pref_quotient_automata_011 \<equiv> da (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf)) transition {(aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)), (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))), (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))), (aut3.State_L aut3.state_level1_Leaf)}"
end