theory aut15_append_char_automaton_0
  imports Main "PCPLib.PCP" "PCPLib.Automata" "aut15"
begin

type_synonym State = "aut15.State state_dup"

lemma aut15_append_char_automaton_0_state_split:
  obtains "s = (state_l (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf)))"|
"s = (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L aut15.state_level1_Leaf))"|
"s = (state_r (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf)))"|
"s = (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_r (aut15.State_R aut15.state_level1_Leaf))"|
"s = (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)))"|
"s = (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf)))"|
"s = (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))"|
"s = (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_L aut15.state_level1_Leaf))"|
"s = (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_R aut15.state_level1_Leaf))"|
"s = (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf)))"|
"s = (state_l (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)))"|
"s = (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))"|
"s = (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))"|
"s = (state_l (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))"|
"s = (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))"
proof (cases s)
  case (state_l x1)
  then show ?thesis using aut15_state_split[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using aut15_state_split[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R aut15.state_level1_Leaf))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L aut15.state_level1_Leaf)), C0) => (state_r (aut15.State_L aut15.state_level1_Leaf))|
  ((state_l (aut15.State_L aut15.state_level1_Leaf)), C1) => (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L aut15.state_level1_Leaf))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_l (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_R aut15.state_level1_Leaf)), C0) => (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_R aut15.state_level1_Leaf)), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf)))|
  ((state_l (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)))|
  ((state_l (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_l (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)))|
  ((state_l (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R aut15.state_level1_Leaf)), C0) => (state_r (aut15.State_R aut15.state_level1_Leaf))|
  ((state_l (aut15.State_R aut15.state_level1_Leaf)), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_L aut15.state_level1_Leaf)), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L aut15.state_level1_Leaf)), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_L aut15.state_level2_Leaf)))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf))), C0) => (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L aut15.state_level3_Leaf))))|
  ((state_r (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf))))|
  ((state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R aut15.state_level3_Leaf)))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf)))))|
  ((state_l (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_R (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C0) => (state_r (aut15.State_R (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))|
  ((state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_R aut15.state_level4_Leaf))))), C1) => (state_l (aut15.State_L (aut15.state_level1_R aut15.state_level2_Leaf)))"

definition aut15_append_char_automaton_0::"(alphabet, State) da" where
 "aut15_append_char_automaton_0 \<equiv> da (state_l (aut15.State_R (aut15.state_level1_R aut15.state_level2_Leaf))) transition {(state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_L (aut15.state_level3_R aut15.state_level4_Leaf))))), (state_r (aut15.State_L (aut15.state_level1_L (aut15.state_level2_L aut15.state_level3_Leaf)))), (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), (state_r (aut15.State_L (aut15.state_level1_R (aut15.state_level2_R (aut15.state_level3_L aut15.state_level4_Leaf))))), (state_r (aut15.State_R (aut15.state_level1_L (aut15.state_level2_L (aut15.state_level3_L aut15.state_level4_Leaf)))))}"
end