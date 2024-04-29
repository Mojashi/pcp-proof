theory aut12
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level4 = state_level4_Leaf
datatype state_level3 = state_level3_L state_level4 | state_level3_R state_level4
datatype state_level2 = state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut12_state_split:
obtains "s = (aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))" |
"s = aut12.State_Leaf" |
"s = (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))" |
"s = (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))" |
"s = (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))" |
"s = (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))" |
"s = (aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))" |
"s = (aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))" |
"s = (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))" |
"s = (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))"
proof -
show ?thesis proof (cases s)
case State_Leaf
then show ?thesis using  that by blast
next
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
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => (aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => aut12.State_Leaf|
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => (aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  (aut12.State_Leaf, C1) => (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))|
  (aut12.State_Leaf, C0) => (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))|
  ((aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), C0) => (aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C1) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf))))|
  ((aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_L aut12.state_level4_Leaf)))), C0) => (aut12.State_R (aut12.state_level1_R (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf))))"

definition aut12::"(alphabet, State) da" where
 "aut12 \<equiv> da (aut12.State_R (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))) transition {(aut12.State_L (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf)))), (aut12.State_R (aut12.state_level1_R (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), (aut12.State_L (aut12.state_level1_L (aut12.state_level2_L (aut12.state_level3_R aut12.state_level4_Leaf)))), (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_L aut12.state_level4_Leaf)))), (aut12.State_R (aut12.state_level1_L (aut12.state_level2_R (aut12.state_level3_R aut12.state_level4_Leaf))))}"
end