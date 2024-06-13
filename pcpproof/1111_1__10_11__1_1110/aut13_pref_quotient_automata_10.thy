theory aut13_pref_quotient_automata_10
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut13"
begin

type_alias State = aut13.State

alias transition = aut13.transition

definition aut13_pref_quotient_automata_10::"(alphabet, State) da" where
 "aut13_pref_quotient_automata_10 \<equiv> da (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))) transition {(aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R aut13.state_level4_Leaf)))), (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L aut13.state_level4_Leaf)))), (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf))), (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R aut13.state_level4_Leaf)))), (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R aut13.state_level4_Leaf))))}"
end