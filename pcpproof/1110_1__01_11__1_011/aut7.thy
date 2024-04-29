theory aut7
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level3 = state_level3_Leaf
datatype state_level2 = state_level2_Leaf | state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_Leaf | state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut7_state_split:
obtains "s = (aut7.State_R (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf)))" |
"s = (aut7.State_R (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf)))" |
"s = (aut7.State_L aut7.state_level1_Leaf)" |
"s = (aut7.State_L (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf)))" |
"s = (aut7.State_R (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))" |
"s = (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))" |
"s = (aut7.State_L (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf)))" |
"s = (aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf))" |
"s = (aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf))" |
"s = aut7.State_Leaf" |
"s = (aut7.State_R (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf)))" |
"s = (aut7.State_L (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf)))" |
"s = (aut7.State_R (aut7.state_level1_L aut7.state_level2_Leaf))" |
"s = (aut7.State_R aut7.state_level1_Leaf)" |
"s = (aut7.State_L (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))"
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
  ((aut7.State_L (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf))), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_L (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf))), C1) => (aut7.State_R (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))|
  ((aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf)), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf)), C1) => (aut7.State_L (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf)))|
  ((aut7.State_L (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf))), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_L (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf))), C1) => (aut7.State_L (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf)))|
  ((aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf)), C0) => (aut7.State_R (aut7.state_level1_L aut7.state_level2_Leaf))|
  ((aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf)), C1) => (aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf))|
  ((aut7.State_L aut7.state_level1_Leaf), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_L aut7.state_level1_Leaf), C1) => (aut7.State_L (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf)))|
  ((aut7.State_R (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf))), C0) => (aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_R (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf))), C1) => (aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf))|
  ((aut7.State_R (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf))), C0) => (aut7.State_R (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf)))|
  ((aut7.State_R (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf))), C1) => (aut7.State_R (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))|
  ((aut7.State_R (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf))), C0) => aut7.State_Leaf|
  ((aut7.State_R (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf))), C1) => (aut7.State_R aut7.state_level1_Leaf)|
  ((aut7.State_R (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf))), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_R (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf))), C1) => (aut7.State_L (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf)))|
  ((aut7.State_R aut7.state_level1_Leaf), C0) => (aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_R aut7.state_level1_Leaf), C1) => (aut7.State_R (aut7.state_level1_L (aut7.state_level2_R aut7.state_level3_Leaf)))|
  ((aut7.State_L (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf))), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_L (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf))), C1) => (aut7.State_R (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf)))|
  ((aut7.State_R (aut7.state_level1_L aut7.state_level2_Leaf)), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_R (aut7.state_level1_L aut7.state_level2_Leaf)), C1) => (aut7.State_L (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))|
  ((aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf)), C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  ((aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf)), C1) => (aut7.State_L (aut7.state_level1_R (aut7.state_level2_L aut7.state_level3_Leaf)))|
  ((aut7.State_L (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf))), C0) => aut7.State_Leaf|
  ((aut7.State_L (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf))), C1) => (aut7.State_L (aut7.state_level1_R (aut7.state_level2_R aut7.state_level3_Leaf)))|
  (aut7.State_Leaf, C0) => (aut7.State_L (aut7.state_level1_R aut7.state_level2_Leaf))|
  (aut7.State_Leaf, C1) => (aut7.State_L aut7.state_level1_Leaf)"

definition aut7::"(alphabet, State) da" where
 "aut7 \<equiv> da (aut7.State_L (aut7.state_level1_L aut7.state_level2_Leaf)) transition {(aut7.State_R (aut7.state_level1_L (aut7.state_level2_L aut7.state_level3_Leaf))), (aut7.State_R (aut7.state_level1_R aut7.state_level2_Leaf))}"
end