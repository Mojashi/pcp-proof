theory aut3_append_char_automaton_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut3"
begin

type_synonym State = "aut3.State state_dup"

lemma aut3_append_char_automaton_1_state_split:
  obtains "s = (state_r (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))"|
"s = (state_l (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))"|
"s = (state_l (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf)))"|
"s = (state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))"|
"s = (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)))"|
"s = (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf)))"|
"s = (state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf)))"|
"s = (state_l (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)))"|
"s = (state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))"|
"s = (state_l (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf)))"|
"s = (state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))"|
"s = (state_l (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_R aut3.state_level1_Leaf))"|
"s = (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))"|
"s = (state_l (aut3.State_L aut3.state_level1_Leaf))"|
"s = (state_l (aut3.State_R aut3.state_level1_Leaf))"|
"s = (state_r (aut3.State_L aut3.state_level1_Leaf))"|
"s = (state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))"|
"s = (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))"
proof (cases s)
  case (state_l x1)
  then show ?thesis using aut3_state_split[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using aut3_state_split[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((state_r (aut3.State_R aut3.state_level1_Leaf)), C1) => (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R aut3.state_level1_Leaf)), C0) => (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L aut3.state_level1_Leaf)), C1) => (state_r (aut3.State_L aut3.state_level1_Leaf))|
  ((state_l (aut3.State_L aut3.state_level1_Leaf)), C0) => (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))|
  ((state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L aut3.state_level1_Leaf)), C1) => (state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf)))|
  ((state_r (aut3.State_L aut3.state_level1_Leaf)), C0) => (state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))|
  ((state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf)))|
  ((state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))|
  ((state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)))|
  ((state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf)))|
  ((state_l (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))|
  ((state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)))|
  ((state_l (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L aut3.state_level1_Leaf))|
  ((state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_L (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf)))|
  ((state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_R aut3.state_level1_Leaf))|
  ((state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C1) => (state_r (aut3.State_R (aut3.state_level1_R aut3.state_level2_Leaf)))|
  ((state_r (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), C0) => (state_l (aut3.State_R (aut3.state_level1_L aut3.state_level2_Leaf)))|
  ((state_l (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf)))|
  ((state_l (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_L (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf))), C1) => (state_r (aut3.State_R (aut3.state_level1_L (aut3.state_level2_R aut3.state_level3_Leaf))))|
  ((state_r (aut3.State_L (aut3.state_level1_R aut3.state_level2_Leaf))), C0) => (state_l (aut3.State_R (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf))))|
  ((state_l (aut3.State_R aut3.state_level1_Leaf)), C1) => (state_r (aut3.State_R aut3.state_level1_Leaf))|
  ((state_l (aut3.State_R aut3.state_level1_Leaf)), C0) => (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_R aut3.state_level3_Leaf))))"

definition aut3_append_char_automaton_1::"(alphabet, State) da" where
 "aut3_append_char_automaton_1 \<equiv> da (state_l (aut3.State_R (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))) transition {(state_r (aut3.State_L (aut3.state_level1_R (aut3.state_level2_L aut3.state_level3_Leaf)))), (state_r (aut3.State_L (aut3.state_level1_L (aut3.state_level2_L aut3.state_level3_Leaf)))), (state_r (aut3.State_L aut3.state_level1_Leaf)), (state_r (aut3.State_L (aut3.state_level1_L aut3.state_level2_Leaf)))}"
end