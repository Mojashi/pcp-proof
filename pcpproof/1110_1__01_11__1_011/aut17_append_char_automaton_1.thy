theory aut17_append_char_automaton_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut17"
begin

type_synonym State = "aut17.State state_dup"

lemma aut17_append_char_automaton_1_state_split:
  obtains "s = (state_r (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))"|
"s = (state_r (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf)))"|
"s = (state_l (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf)))"|
"s = (state_l (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf)))"|
"s = (state_l (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)))"|
"s = (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))"|
"s = (state_r (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)))"|
"s = (state_r (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf)))"
proof (cases s)
  case (state_l x1)
  then show ?thesis using aut17_state_split[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using aut17_state_split[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((state_l (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_l (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_l (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf)))|
  ((state_l (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)))|
  ((state_r (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))|
  ((state_l (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf))), C1) => (state_r (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf)))|
  ((state_l (aut17.State_R (aut17.state_level1_L aut17.state_level2_Leaf))), C0) => (state_l (aut17.State_L (aut17.state_level1_R aut17.state_level2_Leaf)))"

definition aut17_append_char_automaton_1::"(alphabet, State) da" where
 "aut17_append_char_automaton_1 \<equiv> da (state_l (aut17.State_L (aut17.state_level1_L aut17.state_level2_Leaf))) transition {(state_r (aut17.State_R (aut17.state_level1_R aut17.state_level2_Leaf)))}"
end