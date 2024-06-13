theory aut16_pref_quotient_automata_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut16"
begin

type_alias State = aut16.State

alias transition = aut16.transition

definition aut16_pref_quotient_automata_1::"(alphabet, State) da" where
 "aut16_pref_quotient_automata_1 \<equiv> da (aut16.State_L (aut16.state_level1_L (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))) transition {(aut16.State_R (aut16.state_level1_R (aut16.state_level2_L (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf))))), (aut16.State_R (aut16.state_level1_R (aut16.state_level2_R (aut16.state_level3_R (aut16.state_level4_L aut16.state_level5_Leaf)))))}"
end