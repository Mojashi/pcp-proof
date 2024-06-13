theory aut3
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level1 = state_level1_Leaf
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut3_state_split:
obtains "s = aut3.State_Leaf" |
"s = (aut3.State_R aut3.state_level1_Leaf)" |
"s = (aut3.State_L aut3.state_level1_Leaf)"
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
  (aut3.State_Leaf, C1) => (aut3.State_R aut3.state_level1_Leaf)|
  (aut3.State_Leaf, C0) => aut3.State_Leaf|
  ((aut3.State_R aut3.state_level1_Leaf), C1) => (aut3.State_R aut3.state_level1_Leaf)|
  ((aut3.State_R aut3.state_level1_Leaf), C0) => aut3.State_Leaf|
  ((aut3.State_L aut3.state_level1_Leaf), C1) => aut3.State_Leaf|
  ((aut3.State_L aut3.state_level1_Leaf), C0) => aut3.State_Leaf"

definition aut3::"(alphabet, State) da" where
 "aut3 \<equiv> da (aut3.State_L aut3.state_level1_Leaf) transition {(aut3.State_R aut3.state_level1_Leaf)}"
end