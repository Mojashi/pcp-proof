theory aut18_pref_quotient_automata_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut18"
begin

type_alias State = aut18.State

alias transition = aut18.transition

definition aut18_pref_quotient_automata_1::"(alphabet, State) da" where
 "aut18_pref_quotient_automata_1 \<equiv> da (aut18.State_L (aut18.state_level1_R aut18.state_level2_Leaf)) transition {(aut18.State_R (aut18.state_level1_L aut18.state_level2_Leaf))}"
end