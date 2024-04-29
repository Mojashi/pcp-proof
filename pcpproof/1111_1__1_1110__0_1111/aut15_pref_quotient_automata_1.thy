theory aut15_pref_quotient_automata_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut15"
begin

type_alias State = aut15.State

alias transition = aut15.transition

definition aut15_pref_quotient_automata_1::"(alphabet, State) da" where
 "aut15_pref_quotient_automata_1 \<equiv> da (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L (aut15.state_level4_R aut15.state_level5_Leaf))))) transition {(aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L (aut15.state_level4_R aut15.state_level5_Leaf))))), (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R (aut15.state_level4_R aut15.state_level5_Leaf))))), (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R (aut15.state_level4_R aut15.state_level5_Leaf)))))}"
end