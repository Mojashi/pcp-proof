theory aut5
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level4 = state_level4_Leaf
datatype state_level3 = state_level3_L state_level4 | state_level3_R state_level4
datatype state_level2 = state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_Leaf | state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut5_state_split:
obtains "s = (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_R aut5.state_level1_Leaf)" |
"s = (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))" |
"s = (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = (aut5.State_L aut5.state_level1_Leaf)" |
"s = (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))" |
"s = aut5.State_Leaf"
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
case state_level1_Leaf
then show ?thesis using State_R that by blast
next
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
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  (aut5.State_Leaf, C1) => (aut5.State_R aut5.state_level1_Leaf)|
  (aut5.State_Leaf, C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_R aut5.state_level1_Leaf), C1) => (aut5.State_R aut5.state_level1_Leaf)|
  ((aut5.State_R aut5.state_level1_Leaf), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_L aut5.state_level1_Leaf)|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_L aut5.state_level1_Leaf), C1) => (aut5.State_L aut5.state_level1_Leaf)|
  ((aut5.State_L aut5.state_level1_Leaf), C0) => (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => (aut5.State_L aut5.state_level1_Leaf)|
  ((aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C1) => (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))|
  ((aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C1) => aut5.State_Leaf|
  ((aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))), C0) => (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))"

definition aut5::"(alphabet, State) da" where
 "aut5 \<equiv> da (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))) transition {(aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))), (aut5.State_R aut5.state_level1_Leaf), (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))}"
end