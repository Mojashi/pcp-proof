theory aut2
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

datatype state_level6 = state_level6_Leaf
datatype state_level5 = state_level5_L state_level6 | state_level5_R state_level6
datatype state_level4 = state_level4_L state_level5 | state_level4_R state_level5
datatype state_level3 = state_level3_L state_level4 | state_level3_R state_level4
datatype state_level2 = state_level2_L state_level3 | state_level2_R state_level3
datatype state_level1 = state_level1_L state_level2 | state_level1_R state_level2
datatype State = State_L state_level1 | State_R state_level1


lemma aut2_state_split:
obtains "s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))" |
"s = (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))"
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
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_L state_level3_R state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_L state_level2_R state_level3_R state_level4_R state_level5_R that by blast
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
case (state_level1_R s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_L state_level3_R state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_L state_level1_R state_level2_R state_level3_R state_level4_R state_level5_R that by blast
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
next
case (State_R s)
show ?thesis proof (cases s)
case (state_level1_L s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_L state_level3_R state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_L state_level2_R state_level3_R state_level4_R state_level5_R that by blast
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
case (state_level1_R s)
show ?thesis proof (cases s)
case (state_level2_L s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_L state_level3_R state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
qed
next
case (state_level2_R s)
show ?thesis proof (cases s)
case (state_level3_L s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_L state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_L state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_L state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_L state_level4_R state_level5_R that by blast
next
qed
next
qed
next
qed
next
case (state_level3_R s)
show ?thesis proof (cases s)
case (state_level4_L s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_R state_level4_L state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_R state_level4_L state_level5_R that by blast
next
qed
next
qed
next
case (state_level4_R s)
show ?thesis proof (cases s)
case (state_level5_L s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_R state_level4_R state_level5_L that by blast
next
qed
next
case (state_level5_R s)
show ?thesis proof (cases s)
case state_level6_Leaf
then show ?thesis using State_R state_level1_R state_level2_R state_level3_R state_level4_R state_level5_R that by blast
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
next
qed

qed
abbreviation transition::"State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C0) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C1) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))|
  ((aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), C0) => (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf))))))"

definition aut2::"(alphabet, State) da" where
 "aut2 \<equiv> da (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))) transition {(aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_L (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_L (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_R (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_L (aut2.state_level3_L (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_R (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_L aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_L (aut2.state_level4_R (aut2.state_level5_R aut2.state_level6_Leaf)))))), (aut2.State_L (aut2.state_level1_R (aut2.state_level2_R (aut2.state_level3_R (aut2.state_level4_L (aut2.state_level5_R aut2.state_level6_Leaf))))))}"
end