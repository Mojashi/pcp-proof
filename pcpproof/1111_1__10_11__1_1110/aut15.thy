theory aut15
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level4 = state_level4_Leaf
datatype state_level3 = state_level3_Leaf | state_level3_L state_level4 | state_level3_R state_level4
datatype state_level2 = state_level2_Leaf | state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_Leaf | state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_L state_level1 | State_R state_level1


lemma aut15_state_split:
obtains "s = (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))" |
"s = (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))" |
"s = (aut15.State_L aut15.state_level1_Leaf)" |
"s = (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))" |
"s = (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))" |
"s = (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf))" |
"s = (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf))" |
"s = (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))" |
"s = (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))" |
"s = (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))" |
"s = (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))" |
"s = (aut15.State_R aut15.state_level1_Leaf)" |
"s = (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))" |
"s = (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))" |
"s = (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf))" |
"s = (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))" |
"s = (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))" |
"s = (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))" |
"s = (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))" |
"s = (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))"
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
case state_level3_Leaf
then show ?thesis using State_L state_level1_L state_level2_R that by blast
next
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
case state_level2_Leaf
then show ?thesis using State_L state_level1_R that by blast
next
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_L state_level1_R state_level2_L that by blast
next
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
case state_level3_Leaf
then show ?thesis using State_L state_level1_R state_level2_R that by blast
next
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
case state_level2_Leaf
then show ?thesis using State_R state_level1_L that by blast
next
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_R state_level1_L state_level2_L that by blast
next
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
case state_level3_Leaf
then show ?thesis using State_R state_level1_L state_level2_R that by blast
next
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
case state_level2_Leaf
then show ?thesis using State_R state_level1_R that by blast
next
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_R state_level1_R state_level2_L that by blast
next
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
case state_level3_Leaf
then show ?thesis using State_R state_level1_R state_level2_R that by blast
next
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
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))), C1) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))), C0) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))), C1) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))), C0) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))|
  ((aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf)), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf)), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))), C0) => (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))|
  ((aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf)), C1) => (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf)), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))|
  ((aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))), C1) => (aut15.State_R aut15.state_level1_Leaf)|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))), C0) => (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_L aut15.state_level1_Leaf), C1) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L aut15.state_level1_Leaf), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf))|
  ((aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))), C1) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))), C0) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_L aut15.state_level1_Leaf)|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))), C1) => (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R aut15.state_level1_Leaf), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_R aut15.state_level1_Leaf), C0) => (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))|
  ((aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))|
  ((aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)), C0) => (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C1) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C1) => (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))|
  ((aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))), C0) => (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))"

definition aut15::"(alphabet, State) da" where
 "aut15 \<equiv> da (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf)) transition {(aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))), (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))), (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))), (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))}"
end