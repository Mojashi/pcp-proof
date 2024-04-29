theory aut11_pref_quotient_automata_1111
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut11"
begin

type_alias State = aut11.State

alias transition = aut11.transition

definition aut11_pref_quotient_automata_1111::"(alphabet, State) da" where
 "aut11_pref_quotient_automata_1111 \<equiv> da (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_L aut11.state_level5_Leaf))))) transition {(aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_R (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_L (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_R (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_R (aut11.state_level3_R (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut11.State_L aut11.state_level1_Leaf), (aut11.State_L (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf))))), (aut11.State_R (aut11.state_level1_L (aut11.state_level2_L (aut11.state_level3_L (aut11.state_level4_R aut11.state_level5_Leaf))))), (aut11.State_L (aut11.state_level1_R (aut11.state_level2_L (aut11.state_level3_L (aut11.state_level4_L aut11.state_level5_Leaf)))))}"
end