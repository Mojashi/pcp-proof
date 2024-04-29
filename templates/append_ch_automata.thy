theory {{theory_name}}
  imports Main "PCPLib.PCP" "PCPLib.Automata" "{{orig_aut_path}}"
begin

type_synonym State = "{{orig_aut_name}}.State state_dup"

lemma {{split_lemma_name}}:
  obtains {{{split_lemma_content}}}
proof (cases s)
  case (state_l x1)
  then show ?thesis using {{orig_aut_state_split}}[of x1] that by fastforce
next
  case (state_r x1)
  then show ?thesis using {{orig_aut_state_split}}[of x1] that by fastforce
qed

abbreviation transition :: "State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
{{{transition_defs}}}"

definition {{theory_name}}::"(alphabet, State) da" where
 "{{theory_name}} \<equiv> da {{initial_state}} transition { {{~accept_states~}} }"
end