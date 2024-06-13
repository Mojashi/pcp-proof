theory aut6
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level2 = state_level2_Leaf
datatype state_level1 = state_level1_Leaf | state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_L state_level1 | State_R state_level1


lemma aut6_state_split:
obtains "s = (aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf))" |
"s = (aut6.State_R (aut6.state_level1_R aut6.state_level2_Leaf))" |
"s = (aut6.State_L (aut6.state_level1_L aut6.state_level2_Leaf))" |
"s = (aut6.State_L aut6.state_level1_Leaf)" |
"s = (aut6.State_R (aut6.state_level1_L aut6.state_level2_Leaf))" |
"s = (aut6.State_R aut6.state_level1_Leaf)"
proof -
show ?thesis proof (cases s)
case (State_L s)
show ?thesis proof (cases s)
case state_level1_Leaf
then show ?thesis using State_L that by blast
next
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
case state_level1_Leaf
then show ?thesis using State_R that by blast
next
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
  ((aut6.State_R (aut6.state_level1_L aut6.state_level2_Leaf)), C1) => (aut6.State_L aut6.state_level1_Leaf)|
  ((aut6.State_R (aut6.state_level1_L aut6.state_level2_Leaf)), C0) => (aut6.State_L aut6.state_level1_Leaf)|
  ((aut6.State_L aut6.state_level1_Leaf), C1) => (aut6.State_R aut6.state_level1_Leaf)|
  ((aut6.State_L aut6.state_level1_Leaf), C0) => (aut6.State_L aut6.state_level1_Leaf)|
  ((aut6.State_R (aut6.state_level1_R aut6.state_level2_Leaf)), C1) => (aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf))|
  ((aut6.State_R (aut6.state_level1_R aut6.state_level2_Leaf)), C0) => (aut6.State_L aut6.state_level1_Leaf)|
  ((aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf)), C1) => (aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf))|
  ((aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf)), C0) => (aut6.State_L aut6.state_level1_Leaf)|
  ((aut6.State_R aut6.state_level1_Leaf), C1) => (aut6.State_L (aut6.state_level1_L aut6.state_level2_Leaf))|
  ((aut6.State_R aut6.state_level1_Leaf), C0) => (aut6.State_L aut6.state_level1_Leaf)|
  ((aut6.State_L (aut6.state_level1_L aut6.state_level2_Leaf)), C1) => (aut6.State_R (aut6.state_level1_R aut6.state_level2_Leaf))|
  ((aut6.State_L (aut6.state_level1_L aut6.state_level2_Leaf)), C0) => (aut6.State_L aut6.state_level1_Leaf)"

definition aut6::"(alphabet, State) da" where
 "aut6 \<equiv> da (aut6.State_R (aut6.state_level1_L aut6.state_level2_Leaf)) transition {(aut6.State_L (aut6.state_level1_R aut6.state_level2_Leaf))}"
end