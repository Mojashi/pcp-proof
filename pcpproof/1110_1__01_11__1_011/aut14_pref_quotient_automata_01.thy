theory aut14_pref_quotient_automata_01
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut14"
begin

type_alias State = aut14.State

alias transition = aut14.transition

definition aut14_pref_quotient_automata_01::"(alphabet, State) da" where
 "aut14_pref_quotient_automata_01 \<equiv> da (aut14.State_R (aut14.state_level1_L aut14.state_level2_Leaf)) transition {(aut14.State_R (aut14.state_level1_R aut14.state_level2_Leaf))}"
end