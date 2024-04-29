theory aut12_append_char_automaton_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut12"
begin

type_synonym State = "aut12.State state_dup"

lemma aut12_append_char_automaton_1_state_split:
  obtains "s = (state_l aut12.State_Leaf)"|
"s = (state_r (aut12.State_L aut12.state_level1_Leaf))"|
"s = (state_r aut12.State_Leaf)"|
"s = (state_l (aut12.State_R aut12.state_level1_Leaf))"|
"s = (state_r (aut12.State_R aut12.state_level1_Leaf))"|
"s = (state_l (aut12.State_L aut12.state_level1_Leaf))"
proof (cases s)
  case (state_l x1)
  then show ?thesis using aut12_state_split[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using aut12_state_split[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((state_r (aut12.State_R aut12.state_level1_Leaf)), C1) => (state_r aut12.State_Leaf)|
  ((state_r (aut12.State_R aut12.state_level1_Leaf)), C0) => (state_l (aut12.State_R aut12.state_level1_Leaf))|
  ((state_l (aut12.State_L aut12.state_level1_Leaf)), C1) => (state_r (aut12.State_L aut12.state_level1_Leaf))|
  ((state_l (aut12.State_L aut12.state_level1_Leaf)), C0) => (state_l (aut12.State_L aut12.state_level1_Leaf))|
  ((state_r aut12.State_Leaf), C1) => (state_r aut12.State_Leaf)|
  ((state_r aut12.State_Leaf), C0) => (state_l (aut12.State_R aut12.state_level1_Leaf))|
  ((state_r (aut12.State_L aut12.state_level1_Leaf)), C1) => (state_r (aut12.State_R aut12.state_level1_Leaf))|
  ((state_r (aut12.State_L aut12.state_level1_Leaf)), C0) => (state_l (aut12.State_R aut12.state_level1_Leaf))|
  ((state_l (aut12.State_R aut12.state_level1_Leaf)), C1) => (state_r (aut12.State_R aut12.state_level1_Leaf))|
  ((state_l (aut12.State_R aut12.state_level1_Leaf)), C0) => (state_l (aut12.State_R aut12.state_level1_Leaf))|
  ((state_l aut12.State_Leaf), C1) => (state_r aut12.State_Leaf)|
  ((state_l aut12.State_Leaf), C0) => (state_l (aut12.State_R aut12.state_level1_Leaf))"

definition aut12_append_char_automaton_1::"(alphabet, State) da" where
 "aut12_append_char_automaton_1 \<equiv> da (state_l (aut12.State_L aut12.state_level1_Leaf)) transition {(state_r aut12.State_Leaf)}"
end