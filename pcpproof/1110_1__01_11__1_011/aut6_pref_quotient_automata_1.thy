theory aut6_pref_quotient_automata_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut6"
begin

type_alias State = aut6.State

alias transition = aut6.transition

definition aut6_pref_quotient_automata_1::"(alphabet, State) da" where
 "aut6_pref_quotient_automata_1 \<equiv> da (aut6.State_R (aut6.state_level1_L (aut6.state_level2_R (aut6.state_level3_R aut6.state_level4_Leaf)))) transition {(aut6.State_L (aut6.state_level1_L (aut6.state_level2_L (aut6.state_level3_L aut6.state_level4_Leaf)))), (aut6.State_L (aut6.state_level1_R (aut6.state_level2_L (aut6.state_level3_R aut6.state_level4_Leaf)))), (aut6.State_R (aut6.state_level1_L (aut6.state_level2_L (aut6.state_level3_L aut6.state_level4_Leaf))))}"
end