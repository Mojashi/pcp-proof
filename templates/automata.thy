theory {{theory_name}}
  imports Main "PCPLib.PCP" "PCPLib.Automata"
begin

{{{state_datatype_defs}}}


lemma {{state_split_lemma_name}}:
obtains {{{state_split_content}}}
proof -
{{{state_split_proof}}}
qed
abbreviation transition::"State \<Rightarrow> alphabet \<Rightarrow> State" where
  "transition s c \<equiv> case (s, c) of 
{{{transition_defs}}}"

definition {{theory_name}}::"(alphabet, State) da" where
 "{{theory_name}} \<equiv> da {{initial_state}} transition { {{~accept_states~}} }"
end