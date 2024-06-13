theory aut8_pref_quotient_automata_11
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut8"
begin

type_alias State = aut8.State

alias transition = aut8.transition

definition aut8_pref_quotient_automata_11::"(alphabet, State) da" where
 "aut8_pref_quotient_automata_11 \<equiv> da (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf)) transition {(aut8.State_R (aut8.state_level1_R aut8.state_level2_Leaf))}"
end