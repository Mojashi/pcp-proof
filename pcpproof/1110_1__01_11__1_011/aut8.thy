theory aut8
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level3 = state_level3_Leaf
datatype state_level2 = state_level2_Leaf | state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_Leaf | state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_L state_level1 | State_R state_level1


lemma aut8_state_split:
obtains "s = (aut8.State_R (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf)))" |
"s = (aut8.State_R (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf)))" |
"s = (aut8.State_R (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf)))" |
"s = (aut8.State_R aut8.state_level1_Leaf)" |
"s = (aut8.State_L (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf)))" |
"s = (aut8.State_R (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf)))" |
"s = (aut8.State_L aut8.state_level1_Leaf)" |
"s = (aut8.State_R (aut8.state_level1_R aut8.state_level2_Leaf))" |
"s = (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf))" |
"s = (aut8.State_L (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf)))" |
"s = (aut8.State_L (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf)))" |
"s = (aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf))" |
"s = (aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))" |
"s = (aut8.State_L (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf)))"
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
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_L state_level1_L state_level2_L that by blast
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_L state_level1_L state_level2_R that by blast
next
qed
next
qed
next
case (state_level1_R s)
show ?thesis proof (cases s)
case state_level2_Leaf
then show ?thesis using State_L state_level1_R that by blast
next
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_L state_level1_R state_level2_L that by blast
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_L state_level1_R state_level2_R that by blast
next
qed
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
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_R state_level1_L state_level2_L that by blast
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_R state_level1_L state_level2_R that by blast
next
qed
next
qed
next
case (state_level1_R s)
show ?thesis proof (cases s)
case state_level2_Leaf
then show ?thesis using State_R state_level1_R that by blast
next
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_R state_level1_R state_level2_L that by blast
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_R state_level1_R state_level2_R that by blast
next
qed
next
qed
next
qed
next
qed

qed
abbreviation transition::"State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((aut8.State_R (aut8.state_level1_R aut8.state_level2_Leaf)), C0) => (aut8.State_L aut8.state_level1_Leaf)|
  ((aut8.State_R (aut8.state_level1_R aut8.state_level2_Leaf)), C1) => (aut8.State_R (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf)))|
  ((aut8.State_L (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf))), C0) => (aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf))), C1) => (aut8.State_R (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf)))|
  ((aut8.State_R (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf))), C0) => (aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_R (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf))), C1) => (aut8.State_L (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf)))|
  ((aut8.State_L aut8.state_level1_Leaf), C0) => (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf))|
  ((aut8.State_L aut8.state_level1_Leaf), C1) => (aut8.State_L (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf)))|
  ((aut8.State_L (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf))), C0) => (aut8.State_L aut8.state_level1_Leaf)|
  ((aut8.State_L (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf))), C1) => (aut8.State_L (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf)))|
  ((aut8.State_L (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf))), C0) => (aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf))), C1) => (aut8.State_R (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf)))|
  ((aut8.State_R (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf))), C0) => (aut8.State_L aut8.state_level1_Leaf)|
  ((aut8.State_R (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf))), C1) => (aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf)), C0) => (aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf)), C1) => (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf))|
  ((aut8.State_R (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf))), C0) => (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf))|
  ((aut8.State_R (aut8.state_level1_R (aut8.state_level2_L aut8.state_level3_Leaf))), C1) => (aut8.State_R (aut8.state_level1_R aut8.state_level2_Leaf))|
  ((aut8.State_R (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf))), C0) => (aut8.State_L (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf)))|
  ((aut8.State_R (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf))), C1) => (aut8.State_R (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf)))|
  ((aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf)), C0) => (aut8.State_R (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf)))|
  ((aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf)), C1) => (aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf)), C0) => (aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf)), C1) => (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf))|
  ((aut8.State_R aut8.state_level1_Leaf), C0) => (aut8.State_L (aut8.state_level1_R (aut8.state_level2_R aut8.state_level3_Leaf)))|
  ((aut8.State_R aut8.state_level1_Leaf), C1) => (aut8.State_R (aut8.state_level1_L aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf))), C0) => (aut8.State_L (aut8.state_level1_R aut8.state_level2_Leaf))|
  ((aut8.State_L (aut8.state_level1_L (aut8.state_level2_R aut8.state_level3_Leaf))), C1) => (aut8.State_L (aut8.state_level1_L (aut8.state_level2_L aut8.state_level3_Leaf)))"

definition aut8::"(alphabet, State) da" where
 "aut8 \<equiv> da (aut8.State_R aut8.state_level1_Leaf) transition {(aut8.State_L (aut8.state_level1_L aut8.state_level2_Leaf))}"
end