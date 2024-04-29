theory aut5_append_char_automaton_0
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut5"
begin

type_synonym State = "aut5.State state_dup"

lemma aut5_append_char_automaton_0_state_split:
  obtains "s = (state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_L aut5.state_level1_Leaf))"|
"s = (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L aut5.state_level1_Leaf))"|
"s = (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_l aut5.State_Leaf)"|
"s = (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R aut5.state_level1_Leaf))"|
"s = (state_r aut5.State_Leaf)"|
"s = (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R aut5.state_level1_Leaf))"|
"s = (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))"|
"s = (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))"
proof (cases s)
  case (state_l x1)
  then show ?thesis using aut5_state_split[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using aut5_state_split[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R aut5.state_level1_Leaf)), C0) => (state_r (aut5.State_R aut5.state_level1_Leaf))|
  ((state_l (aut5.State_R aut5.state_level1_Leaf)), C1) => (state_l (aut5.State_R aut5.state_level1_Leaf))|
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L aut5.state_level1_Leaf)), C0) => (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L aut5.state_level1_Leaf)), C1) => (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R aut5.state_level1_Leaf)), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R aut5.state_level1_Leaf)), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r aut5.State_Leaf), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r aut5.State_Leaf), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L aut5.state_level1_Leaf))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L aut5.state_level1_Leaf))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l aut5.State_Leaf)|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l aut5.State_Leaf), C0) => (state_r aut5.State_Leaf)|
  ((state_l aut5.State_Leaf), C1) => (state_l (aut5.State_R aut5.state_level1_Leaf))|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_L aut5.state_level1_Leaf)), C0) => (state_r (aut5.State_L aut5.state_level1_Leaf))|
  ((state_l (aut5.State_L aut5.state_level1_Leaf)), C1) => (state_l (aut5.State_L aut5.state_level1_Leaf))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_l (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_L (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C0) => (state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf)))))|
  ((state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf))))), C1) => (state_l (aut5.State_R (aut5.state_level1_L (aut5.state_level2_L (aut5.state_level3_L aut5.state_level4_Leaf)))))"

definition aut5_append_char_automaton_0::"(alphabet, State) da" where
 "aut5_append_char_automaton_0 \<equiv> da (state_l (aut5.State_L (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_L aut5.state_level4_Leaf))))) transition {(state_r (aut5.State_R (aut5.state_level1_R (aut5.state_level2_L (aut5.state_level3_R aut5.state_level4_Leaf))))), (state_r (aut5.State_R (aut5.state_level1_L (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), (state_r (aut5.State_L (aut5.state_level1_R (aut5.state_level2_R (aut5.state_level3_R aut5.state_level4_Leaf))))), (state_r (aut5.State_R aut5.state_level1_Leaf))}"
end