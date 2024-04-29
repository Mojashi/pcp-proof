theory aut4
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level4 = state_level4_Leaf
datatype state_level3 = state_level3_L state_level4 | state_level3_R state_level4
datatype state_level2 = state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_L state_level1 | State_R state_level1


lemma aut4_state_split:
obtains "s = (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))" |
"s = (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))" |
"s = (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))" |
"s = (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))" |
"s = (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))"
proof -
show ?thesis proof (cases s)
case (State_L s)
show ?thesis proof (cases s)
case (state_level1_L s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_R that by blast
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_R that by blast
next
qed
next
qed
next
qed
next
case (state_level1_R s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_R that by blast
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_R that by blast
next
qed
next
qed
next
qed
next
qed
next
case (State_R s)
show ?thesis proof (cases s)
case (state_level1_L s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_R that by blast
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_R that by blast
next
qed
next
qed
next
qed
next
case (state_level1_R s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_R that by blast
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_L that by blast
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case state_level4_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_R that by blast
next
qed
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
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C1) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C1) => (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))|
  ((aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), C0) => (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))"

definition aut4::"(alphabet, State) da" where
 "aut4 \<equiv> da (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))) transition {(aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))), (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))), (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))}"
end