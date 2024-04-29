theory aut2_append_char_automaton_0
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut2"
begin

type_synonym State = "aut2.State state_dup"

lemma aut2_append_char_automaton_0_state_split:
  obtains "s = (state_l (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))"|
"s = (state_l (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)))"|
"s = (state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))"|
"s = (state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))"|
"s = (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))"|
"s = (state_r (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)))"|
"s = (state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))"|
"s = (state_l (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))"
proof (cases s)
  case (state_l x1)
  then show ?thesis using aut2_state_split[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using aut2_state_split[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((state_l (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_l (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_l (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))|
  ((state_l (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))|
  ((state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))|
  ((state_l (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))), C0) => (state_r (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)))|
  ((state_l (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))), C1) => (state_l (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)))"

definition aut2_append_char_automaton_0::"(alphabet, State) da" where
 "aut2_append_char_automaton_0 \<equiv> da (state_l (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))) transition {(state_r (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))), (state_r (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)))}"
end