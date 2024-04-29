theory aut17_pref_quotient_automata_0
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut17"
begin

type_alias State = aut17.State

alias transition = aut17.transition

definition aut17_pref_quotient_automata_0::"(alphabet, State) da" where
 "aut17_pref_quotient_automata_0 \<equiv> da (aut17.State_L (aut17.state_level1_R (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_L aut17.state_level5_Leaf))))) transition {(aut17.State_R (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_R (aut17.state_level4_R aut17.state_level5_Leaf))))), aut17.State_Leaf, (aut17.State_L (aut17.state_level1_L (aut17.state_level2_L (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_R (aut17.state_level2_R (aut17.state_level3_L (aut17.state_level4_R aut17.state_level5_Leaf))))), (aut17.State_R (aut17.state_level1_L (aut17.state_level2_R aut17.state_level3_Leaf)))}"
end