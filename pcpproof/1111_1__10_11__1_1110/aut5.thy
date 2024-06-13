theory aut5
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level2 = state_level2_Leaf
datatype state_level1 = state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut5_state_split:
obtains "s = (aut5.State_R (aut5.state_level1_R aut5.state_level2_Leaf))" |
"s = (aut5.State_R (aut5.state_level1_L aut5.state_level2_Leaf))" |
"s = (aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf))" |
"s = aut5.State_Leaf" |
"s = (aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf))"
proof -
show ?thesis proof (cases s)
case State_Leaf
then show ?thesis using  that by blast
next
case (State_L s)
show ?thesis proof (cases s)
case (state_level1_L s)
show ?thesis proof (cases s)
case state_level2_Leaf
then show ?thesis using State_L state_level1_L that by blast
next
qed
next
case (state_level1_R s)
show ?thesis proof (cases s)
case state_level2_Leaf
then show ?thesis using State_L state_level1_R that by blast
next
qed
next
qed
next
case (State_R s)
show ?thesis proof (cases s)
case (state_level1_L s)
show ?thesis proof (cases s)
case state_level2_Leaf
then show ?thesis using State_R state_level1_L that by blast
next
qed
next
case (state_level1_R s)
show ?thesis proof (cases s)
case state_level2_Leaf
then show ?thesis using State_R state_level1_R that by blast
next
qed
next
qed
next
qed

qed
abbreviation transition::"State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf)), C1) => aut5.State_Leaf|
  ((aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf)), C0) => aut5.State_Leaf|
  ((aut5.State_R (aut5.state_level1_L aut5.state_level2_Leaf)), C1) => (aut5.State_R (aut5.state_level1_R aut5.state_level2_Leaf))|
  ((aut5.State_R (aut5.state_level1_L aut5.state_level2_Leaf)), C0) => aut5.State_Leaf|
  (aut5.State_Leaf, C1) => (aut5.State_R (aut5.state_level1_L aut5.state_level2_Leaf))|
  (aut5.State_Leaf, C0) => aut5.State_Leaf|
  ((aut5.State_R (aut5.state_level1_R aut5.state_level2_Leaf)), C1) => (aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf))|
  ((aut5.State_R (aut5.state_level1_R aut5.state_level2_Leaf)), C0) => aut5.State_Leaf|
  ((aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf)), C1) => (aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf))|
  ((aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf)), C0) => aut5.State_Leaf"

definition aut5::"(alphabet, State) da" where
 "aut5 \<equiv> da (aut5.State_L (aut5.state_level1_R aut5.state_level2_Leaf)) transition {(aut5.State_L (aut5.state_level1_L aut5.state_level2_Leaf))}"
end