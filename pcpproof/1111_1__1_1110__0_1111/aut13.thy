theory aut13
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level5 = state_level5_Leaf
datatype state_level4 = state_level4_L state_level5 | state_level4_R state_level5
datatype state_level3 = state_level3_Leaf | state_level3_L state_level4 | state_level3_R state_level4
datatype state_level2 = state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_Leaf | State_L state_level1 | State_R state_level1


lemma aut13_state_split:
obtains "s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf)))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf)))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf)))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf)))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf)))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))" |
"s = aut13.State_Leaf" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))" |
"s = (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf)))" |
"s = (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))"
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
case state_level3_Leaf
then show ?thesis using State_L state_level1_L state_level2_L that by blast
next
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_R state_level4_R that by blast
next
qed
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
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_R state_level4_R that by blast
next
qed
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
case state_level3_Leaf
then show ?thesis using State_L state_level1_R state_level2_L that by blast
next
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_R state_level4_R that by blast
next
qed
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
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_R state_level4_R that by blast
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
next
case (State_R s)
show ?thesis proof (cases s)
case (state_level1_L s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case state_level3_Leaf
then show ?thesis using State_R state_level1_L state_level2_L that by blast
next
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_R state_level4_R that by blast
next
qed
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
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_R state_level4_R that by blast
next
qed
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
case state_level3_Leaf
then show ?thesis using State_R state_level1_R state_level2_L that by blast
next
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_R state_level4_R that by blast
next
qed
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
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_L state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_L state_level4_R that by blast
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_R state_level4_L that by blast
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case state_level5_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_R state_level4_R that by blast
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
next
qed

qed
abbreviation transition::"State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => aut13.State_Leaf|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf)))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf)))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf)))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf)))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf))), C0) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf))), C1) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf)))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  (aut13.State_Leaf, C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf)))|
  (aut13.State_Leaf, C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L aut13.state_level3_Leaf))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L aut13.state_level3_Leaf)))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf)))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf)))|
  ((aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C1) => (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))|
  ((aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), C0) => (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf)))))"

definition aut13::"(alphabet, State) da" where
 "aut13 \<equiv> da (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_R aut13.state_level5_Leaf))))) transition {(aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf))))), (aut13.State_L (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_L aut13.state_level5_Leaf))))), (aut13.State_L (aut13.state_level1_L (aut13.state_level2_R aut13.state_level3_Leaf))), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_L (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), (aut13.State_R (aut13.state_level1_L (aut13.state_level2_R (aut13.state_level3_R (aut13.state_level4_R aut13.state_level5_Leaf))))), (aut13.State_R (aut13.state_level1_R (aut13.state_level2_R aut13.state_level3_Leaf))), (aut13.State_L (aut13.state_level1_L (aut13.state_level2_L (aut13.state_level3_L (aut13.state_level4_L aut13.state_level5_Leaf)))))}"
end