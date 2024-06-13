theory aut9
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level1 = state_level1_Leaf
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut9_state_split:
obtains "s = (aut9.State_R aut9.state_level1_Leaf)" |
"s = aut9.State_Leaf" |
"s = (aut9.State_L aut9.state_level1_Leaf)"
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
  (aut9.State_Leaf, C0) => (aut9.State_R aut9.state_level1_Leaf)|
  (aut9.State_Leaf, C1) => aut9.State_Leaf|
  ((aut9.State_L aut9.state_level1_Leaf), C0) => (aut9.State_L aut9.state_level1_Leaf)|
  ((aut9.State_L aut9.state_level1_Leaf), C1) => aut9.State_Leaf|
  ((aut9.State_R aut9.state_level1_Leaf), C0) => (aut9.State_L aut9.state_level1_Leaf)|
  ((aut9.State_R aut9.state_level1_Leaf), C1) => aut9.State_Leaf"

definition aut9::"(alphabet, State) da" where
 "aut9 \<equiv> da aut9.State_Leaf transition {(aut9.State_R aut9.state_level1_Leaf)}"
end