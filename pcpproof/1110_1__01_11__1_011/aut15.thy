theory aut15
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level1 = state_level1_Leaf
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut15_state_split:
obtains "s = (aut15.State_L aut15.state_level1_Leaf)" |
"s = (aut15.State_R aut15.state_level1_Leaf)" |
"s = aut15.State_Leaf"
proof -
show ?thesis proof (cases s)
case State_Leaf
then show ?thesis using  that by blast
next
case (State_L s)
show ?thesis proof (cases s)
case state_level1_Leaf
then show ?thesis using State_L that by blast
next
qed
next
case (State_R s)
show ?thesis proof (cases s)
case state_level1_Leaf
then show ?thesis using State_R that by blast
next
qed
next
qed

qed
abbreviation transition::"State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  (aut15.State_Leaf, C1) => aut15.State_Leaf|
  (aut15.State_Leaf, C0) => (aut15.State_R aut15.state_level1_Leaf)|
  ((aut15.State_L aut15.state_level1_Leaf), C1) => aut15.State_Leaf|
  ((aut15.State_L aut15.state_level1_Leaf), C0) => (aut15.State_R aut15.state_level1_Leaf)|
  ((aut15.State_R aut15.state_level1_Leaf), C1) => (aut15.State_L aut15.state_level1_Leaf)|
  ((aut15.State_R aut15.state_level1_Leaf), C0) => (aut15.State_R aut15.state_level1_Leaf)"

definition aut15::"(alphabet, State) da" where
 "aut15 \<equiv> da (aut15.State_R aut15.state_level1_Leaf) transition {aut15.State_Leaf}"
end