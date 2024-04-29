theory aut4_append_char_automaton_1
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut4"
begin

type_synonym State = "aut4.State state_dup"

lemma aut4_append_char_automaton_1_state_split:
  obtains "s = (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))"|
"s = (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"
proof (cases s)
  case (state_l x1)
  then show ?thesis using aut4_state_split[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using aut4_state_split[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_R (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C1) => (state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))|
  ((state_r (aut4.State_R (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))), C0) => (state_l (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_R aut4.state_level4_Leaf)))))"

definition aut4_append_char_automaton_1::"(alphabet, State) da" where
 "aut4_append_char_automaton_1 \<equiv> da (state_l (aut4.State_L (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf))))) transition {(state_r (aut4.State_L (aut4.state_level1_L (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_L (aut4.state_level3_L aut4.state_level4_Leaf))))), (state_r (aut4.State_L (aut4.state_level1_R (aut4.state_level2_R (aut4.state_level3_R aut4.state_level4_Leaf))))), (state_r (aut4.State_R (aut4.state_level1_L (aut4.state_level2_R (aut4.state_level3_L aut4.state_level4_Leaf)))))}"
end