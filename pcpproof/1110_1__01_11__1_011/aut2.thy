theory aut2
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level2 = state_level2_Leaf
datatype state_level1 = state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_L state_level1 | State_R state_level1


lemma aut2_state_split:
obtains "s = (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))" |
"s = (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf))" |
"s = (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))" |
"s = (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))"
proof -
show ?thesis proof (cases s)
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
  ((aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)), C1) => (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))|
  ((aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf)), C0) => (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))|
  ((aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)), C1) => (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))|
  ((aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)), C0) => (aut2.State_L (aut2.state_level1_R aut2.state_level2_Leaf))|
  ((aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)), C0) => (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))|
  ((aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf)), C1) => (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))|
  ((aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)), C1) => (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))|
  ((aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)), C0) => (aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf))"

definition aut2::"(alphabet, State) da" where
 "aut2 \<equiv> da (aut2.State_L (aut2.state_level1_L aut2.state_level2_Leaf)) transition {(aut2.State_R (aut2.state_level1_L aut2.state_level2_Leaf)), (aut2.State_R (aut2.state_level1_R aut2.state_level2_Leaf))}"
end