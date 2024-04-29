theory Automata
  imports Main
begin

datatype ('alphabet, 'state) da = da
    (initial: 'state)
    (transition: "'state \<Rightarrow> 'alphabet \<Rightarrow> 'state")
    (accepting: "'state set")

definition intersect::"('alphabet,'s1) da \<Rightarrow> ('alphabet,'s2) da \<Rightarrow> ('alphabet, ('s1 \<times> 's2)) da" where
  "intersect a1 a2 \<equiv> da (
    (initial a1), (initial a2)
  ) (
    \<lambda> (s1,s2) c. (((transition a1) s1 c), ((transition a2) s2 c))
  ) (
    (accepting a1) \<times> (accepting a2)
  )"

abbreviation complement::"('alphabet,'s) da \<Rightarrow> (('alphabet,'s) da)" where
  "complement a \<equiv> da (
    initial a
  ) (
    transition a
  ) (
     UNIV - (accepting a)
  )"

fun process_word::"'s \<Rightarrow> ('s \<Rightarrow> 'alphabet \<Rightarrow> 's) \<Rightarrow> 'alphabet list \<Rightarrow> 's" where
  "process_word s t [] = s" |
  "process_word s t (c#cs) = t (process_word s t cs) c"

lemma process_word_assoc:
  fixes t::"'s \<Rightarrow> 'alphabet \<Rightarrow> 's"
  and p::"'s"
  shows "process_word (process_word p t a) t b = process_word p t (b@a)"
proof (induct b)
  case Nil
  then show ?case by simp
next
  case (Cons a b)
  then show ?case by simp
qed

abbreviation word_to_state::"('alphabet,'s) da \<Rightarrow> 'alphabet list \<Rightarrow> 's" where
  "word_to_state a cs == process_word (initial a) (transition a) cs"

abbreviation accept::"('alphabet,'s) da \<Rightarrow> 'alphabet list \<Rightarrow> bool" where
  "accept a l == (word_to_state a l) \<in> (accepting a)"

abbreviation accept'::"('alphabet,'s) da \<Rightarrow> 'alphabet list \<Rightarrow> bool" where
  "accept' a l == accept a (rev l)"

abbreviation lang_rev::"('alphabet,'s) da \<Rightarrow> 'alphabet list set" where
  "lang_rev a == {s | s. accept a s}"

abbreviation lang::"('alphabet,'s) da \<Rightarrow> 'alphabet list set" where
  "lang a == rev ` lang_rev a"

lemma comp_word_state[simp]:
  fixes a1::"('alphabet,'s) da" and x::"'alphabet list"
  shows "word_to_state (complement a1) x = word_to_state a1 x"
proof(induct x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case by simp
qed

lemma complement_lang_rev:
  fixes a1::"('alphabet,'s) da"
  shows "lang_rev (complement a1) = UNIV - (lang_rev a1)"
proof(auto) qed

lemma intersect_state_fst:
  shows "fst(word_to_state (intersect a1 a2) x) = word_to_state a1 x"
proof(induct x)
  case Nil
  then show ?case by (simp add: intersect_def)
next
  case (Cons a x)
  then have IH:"word_to_state a1 x = fst(word_to_state (intersect a1 a2) x)" by auto
  obtain ss where A: "ss=word_to_state (intersect a1 a2) (a#x)" by auto
  then have "word_to_state (intersect a1 a2) (a#x) = (transition (intersect a1 a2)) (word_to_state (intersect a1 a2) (x)) a"
    by auto
  then have "word_to_state a1 (a#x) = (fst ss)"
    by (simp add: A IH intersect_def prod.case_eq_if)
  then show ?case using A intersect_def by auto
qed


lemma intersect_state_snd:
  shows "snd(word_to_state (intersect a1 a2) x) = word_to_state a2 x"
proof(induct x)
  case Nil
  then show ?case by (simp add: intersect_def)
next
  case (Cons a x)
  then have IH:"word_to_state a2 x = snd(word_to_state (intersect a1 a2) x)" by auto
  obtain ss where A: "ss=word_to_state (intersect a1 a2) (a#x)" by auto
  then have "word_to_state (intersect a1 a2) (a#x) = (transition (intersect a1 a2)) (word_to_state (intersect a1 a2) (x)) a"
    by auto
  then have "word_to_state a2 (a#x) = (snd ss)"
    by (simp add: A IH intersect_def prod.case_eq_if)
  then show ?case using A intersect_def by auto
qed

lemma intersect_lang_rev:
  shows "lang_rev (intersect a1 a2) = (lang_rev a1) \<inter> (lang_rev a2)"
proof(auto)
  show "\<And>x. accept (intersect a1 a2) x \<Longrightarrow> accept a1 x" proof -
    fix x
    assume "accept (intersect a1 a2) x"
    then have "word_to_state (intersect a1 a2) x \<in> (accepting (intersect a1 a2))" by auto
    then have "word_to_state (intersect a1 a2) x \<in> (accepting a1)\<times>(accepting a2)" by (simp add:intersect_def)
    then have "word_to_state a1 x \<in> (accepting a1)" 
      by (simp add: intersect_state_fst mem_Times_iff)
    then show "accept a1 x" by auto
  qed
  show "\<And>x. accept (intersect a1 a2) x \<Longrightarrow> accept a2 x" proof -
    fix x
    assume "accept (intersect a1 a2) x"
    then have "word_to_state (intersect a1 a2) x \<in> (accepting (intersect a1 a2))" by auto
    then have "word_to_state (intersect a1 a2) x \<in> (accepting a1)\<times>(accepting a2)" by (simp add:intersect_def)
    then have "word_to_state a2 x \<in> (accepting a2)" 
      by (simp add: intersect_state_snd mem_Times_iff)
    then show "accept a2 x" by auto
  qed
  show "\<And>x. accept a1 x \<Longrightarrow> accept a2 x \<Longrightarrow> accept (intersect a1 a2) x" proof -
    fix x
    assume A1:"accept a1 x"
    assume "accept a2 x"
    then show "accept (intersect a1 a2) x" 
      by (metis (no_types, lifting) A1 da.sel(3) intersect_def intersect_state_fst intersect_state_snd mem_Sigma_iff prod.collapse)
  qed
qed

lemma intersect_word_to_state:
  fixes a1::"('alphabet,'s1) da" and a2::"('alphabet,'s2) da"
  shows "\<forall>w. word_to_state (intersect a1 a2) w = ((word_to_state a1 w) , (word_to_state a2 w))"
proof (rule allI)
  fix w
  show "word_to_state (intersect a1 a2) w = ((word_to_state a1 w) , (word_to_state a2 w))" 
  proof (induct w)
    case Nil
    then show ?case by (simp add: intersect_def)
  next
    case (Cons a w)
    then have "word_to_state a1 (a#w) = transition a1 (word_to_state a1 w) a" by auto
    then have "word_to_state a2 (a#w) = transition a2 (word_to_state a2 w) a" by auto
    then have "word_to_state (intersect a1 a2) (a#w) = transition (intersect a1 a2) (word_to_state (intersect a1 a2) w) a" by auto
    then have "... = transition (intersect a1 a2) ((word_to_state a1 w), (word_to_state a2 w)) a" using Cons by auto
    then show ?case by (metis intersect_state_fst intersect_state_snd prod.collapse)
  qed
qed

lemma intersect_accept:
  fixes a1::"('alphabet,'s1) da" and a2::"('alphabet,'s2) da"
  shows "\<forall>w. accept (intersect a1 a2) w = ((accept a1 w) \<and> accept a2 w)"
proof (rule allI)
  fix w
  have "word_to_state (intersect a1 a2) w = ((word_to_state a1 w) , (word_to_state a2 w))"
    using intersect_word_to_state by auto
  then show "accept (intersect a1 a2) w = ((accept a1 w) \<and> accept a2 w)" 
    by (simp add: intersect_def)
qed

lemma comp_intersect_emp_then_includes:
  fixes a1::"('alphabet,'s1) da" and a2::"('alphabet,'s2) da"
  assumes "lang_rev (intersect (complement a1) a2) = {}"
  shows "(lang_rev a2) \<subseteq> (lang_rev a1)"
proof (auto)
  have "\<forall>w. \<not>accept (intersect (complement a1) a2) w" using assms by auto
  then have "\<forall>w. \<not>(accept (complement a1) w) \<or> \<not>accept a2 w"
    by (simp add: intersect_accept)
  then have "\<forall>w. (accept (complement a1) w) \<longrightarrow> \<not>accept a2 w" 
    by blast
  fix x
  show "accept a2 x \<Longrightarrow> accept a1 x" proof (induct x)
    case Nil
    then show ?case 
      by (metis DiffI UNIV_I \<open>\<forall>w. word_to_state (complement a1) w \<notin> accepting (complement a1) \<or> word_to_state a2 w \<notin> accepting a2\<close> comp_word_state da.sel(3))
  next
    case (Cons a x)
    then show ?case
      by (metis Diff_iff UNIV_I \<open>\<forall>w. word_to_state (complement a1) w \<notin> accepting (complement a1) \<or> word_to_state a2 w \<notin> accepting a2\<close> comp_word_state da.sel(3))
  qed
qed

fun step_state::"('alphabet,'s) da \<Rightarrow> 's \<Rightarrow> 's set" where
  "step_state a s = (transition a s) ` UNIV"

fun step_state_set::"('alphabet,'s) da \<Rightarrow> 's set \<Rightarrow> 's set" where
  "step_state_set a s = \<Union> (step_state a ` s)"

fun inv::"('alphabet,'s) da \<Rightarrow> 's set \<Rightarrow> bool" where
  "inv a r = ((step_state_set a r \<subseteq> r) \<and>  (initial a) \<in> r)"

lemma reachable_in_invariant:
  fixes a::"('alphabet,'s) da" and x::"'alphabet list"
  assumes "inv a r"
  shows "word_to_state a x \<in> r"
proof(induct x)
  case Nil
  then show ?case 
    using assms by auto
next
  case (Cons c x)
  then have IH:"word_to_state a x \<in> r" by auto
  then have "word_to_state a (c#x) = (transition a) (word_to_state a x) c" by auto  
  have T:"(transition a) (word_to_state a x) c \<in> step_state_set a {word_to_state a x}"
    by simp
  have "(step_state_set a {word_to_state a x}) \<subseteq> r" using IH assms by auto
  then show "word_to_state a (c#x) \<in> r" 
    using T by auto
qed

lemma if_invariant_exists_lang_rev_empty:
  fixes a::"('alphabet,'s) da" and r::"'s set"
  assumes "inv a r" 
  assumes "(accepting a) \<inter> r = {}"
  shows "lang_rev a = {}"
  by (metis Collect_empty_eq assms(1) assms(2) disjoint_iff_not_equal reachable_in_invariant)


theorem if_invariant_exists_lang_empty:
  fixes a::"('alphabet,'s) da" and r::"'s set"
  assumes "inv a r" 
  assumes "(accepting a) \<inter> r = {}"
  shows "lang a = {}"
  using assms(1) assms(2) if_invariant_exists_lang_rev_empty by auto



fun pref_quotient_rev::"('alphabet,'s) da \<Rightarrow> 'alphabet list \<Rightarrow> ('alphabet,'s) da" where
  "pref_quotient_rev a w = da (word_to_state a w) (transition a) (accepting a)"

fun pref_quotient::"('alphabet,'s) da \<Rightarrow> 'alphabet list \<Rightarrow> ('alphabet,'s) da" where
  "pref_quotient a w = pref_quotient_rev a (rev w)"

lemma pref_quotient_rev_lang_rev_lr:
  fixes a::"('alphabet,'s) da"
  and w::"'alphabet list"
  shows "s\<in> lang_rev(pref_quotient_rev a w) \<longleftrightarrow> s@w \<in> (lang_rev a)"
proof(auto)
  show "accept a (s @ w) \<Longrightarrow> process_word (word_to_state a w) (transition a) s \<in> accepting a"
    using process_word_assoc by metis
  show "process_word (word_to_state a w) (transition a) s \<in> accepting a \<Longrightarrow> accept a (s @ w)"
    by (simp add: process_word_assoc)
qed

value "length [2,3,4::nat]"
value "take 3 [1,2,3,4,5::nat]"

lemma pref_quotient_rev_lang_rev:
  fixes a::"('alphabet,'s) da"
  and w::"'alphabet list"
  shows "lang_rev (pref_quotient_rev a w) = {s |s. s@w \<in> lang_rev a}"
proof
  show "{s |s. s @ w \<in> lang_rev a} \<subseteq> lang_rev (pref_quotient_rev a w)"
    using pref_quotient_rev_lang_rev_lr by auto
  show "lang_rev (pref_quotient_rev a w) \<subseteq> {s |s. s @ w \<in> lang_rev a}"
    using pref_quotient_rev_lang_rev_lr by auto
qed

lemma pref_quotient_lang:
  fixes a::"('alphabet,'s) da"
  and w::"'alphabet list"
  shows "lang (pref_quotient a w) = {s |s. w@s \<in> lang a}"
proof -
  have "lang_rev (pref_quotient_rev a (rev w)) = {s |s. s@(rev w) \<in> lang_rev a}"
    using pref_quotient_rev_lang_rev by auto

  then have "lang_rev (pref_quotient a w) = {s |s. s@(rev w) \<in> lang_rev a}"
    by auto

  then have "rev `lang_rev (pref_quotient a w) = rev `{s |s. s@(rev w) \<in> lang_rev a}"
    by auto

  then have A:"lang (pref_quotient a w) = {rev s |s. s@(rev w) \<in> lang_rev a}"
    by auto

  have "rev ` lang a = lang_rev a"
  proof -
    have "\<forall> s. s \<in> rev ` lang a \<longleftrightarrow> s \<in> lang_rev a" 
      by (simp add: image_iff)
    then show ?thesis by auto
  qed
  then have "lang (pref_quotient a w) = {rev s |s. s@(rev w) \<in> (rev ` lang a)}"
    using A by auto

  then have "... = {rev s |s. rev(s@(rev w)) \<in> lang a}"
    using rev_rev_ident 
    using image_iff by fastforce
  then have "... = {s |s. rev((rev s)@(rev w)) \<in> lang a}"
    using rev_rev_ident 
    by (metis (mono_tags, lifting))

  then have "... = {s |s. w@s \<in> lang a}"
    using rev_rev_ident 
    by auto
  then show ?thesis
    using \<open>lang (pref_quotient a w) = {rev s |s. s @ rev w \<in> rev ` lang a}\<close> \<open>{rev s |s. rev (s @ rev w) \<in> lang a} = {s |s. rev (rev s @ rev w) \<in> lang a}\<close> \<open>{rev s |s. s @ rev w \<in> rev ` lang a} = {rev s |s. rev (s @ rev w) \<in> lang a}\<close> by presburger
qed

datatype 's state_dup = state_l 's | state_r 's

fun append_ch::"('alphabet,'s) da \<Rightarrow> 'alphabet \<Rightarrow> ('alphabet, 's state_dup) da" where
  "append_ch a w = da
    (state_l (initial a))
    (\<lambda>s c. let s' = (case s of state_l x \<Rightarrow> x | state_r x \<Rightarrow> (transition a x w)) in
      if c = w then state_r s' else state_l (transition a s' c)
    )
    (state_r ` (accepting a)) 
  "

lemma word_to_state_append_ch:
  fixes a::"('alphabet,'s) da" and c::"'alphabet" and s::"'alphabet list"
  shows "case (word_to_state (append_ch a c) s) of 
          state_l rs \<Rightarrow> word_to_state a s = rs | 
          state_r rs \<Rightarrow> word_to_state a s = transition a rs c"
proof (induct s)
  case Nil
  then show ?case by auto
next
  case (Cons h s)
  then show ?case proof(cases "word_to_state (append_ch a c) s")
    case (state_l x1)
    then show ?thesis using local.Cons by auto
  next
    case (state_r x2)
    then have A:"word_to_state a s = transition a x2 c" using local.Cons by force
    then show ?thesis proof (cases "h=c")
      case True
      then show ?thesis using A state_r by auto
    next
      case False
      then show ?thesis using A state_r by auto
    qed
  qed
qed

lemma append_ch_lang_rev_lr:
  fixes a::"('alphabet,'s) da" and c::"'alphabet" and s::"'alphabet list"
  shows "(s \<in> lang_rev a) = (c#s \<in> lang_rev (append_ch a c))"
proof 
  show "(s \<in> lang_rev a) \<Longrightarrow> (c#s \<in> lang_rev (append_ch a c))"
  proof -
    assume "s \<in> lang_rev a"
    then have ACC:"accept a s" by auto
    then have "word_to_state a s \<in> accepting a" by auto
    then have "\<exists> rs. word_to_state (append_ch a c) (c#s) = state_r rs"
    proof (cases "word_to_state (append_ch a c) s")
      case (state_l x1)
      then have "word_to_state a s = x1" using word_to_state_append_ch[of a s c] by simp
      then have "x1 \<in> (accepting a)" using ACC by auto
      then have "transition (append_ch a c) (state_l x1) c = state_r x1" by fastforce
      then have "word_to_state (append_ch a c) (c#s) = state_r x1" using state_l by fastforce
      then show ?thesis by auto
    next
      case (state_r x2)
      then obtain x3 where "x3 = transition a x2 c" by auto
      have ACC2:"x3 \<in> (accepting a)" 
        using ACC \<open>x3 = transition a x2 c\<close> state_dup.simps(6) state_r word_to_state_append_ch[of a s c]
        by auto
      then have "transition (append_ch a c) (state_l x3) c = state_r x3" by fastforce
      then have "word_to_state (append_ch a c) (c#s) = state_r x3" using state_r ACC2 
        by (simp add: \<open>x3 = transition a x2 c\<close> list.discI)
      then show ?thesis by auto
    qed
    then obtain rs where RS:"word_to_state (append_ch a c) (c#s) = state_r rs" by auto
    then show "c#s \<in> lang_rev (append_ch a c)"
    proof (cases "word_to_state (append_ch a c) s")
      case (state_l x1)
      then have A:"word_to_state a s = x1" using word_to_state_append_ch[of a s c] by auto
      then have "x1 = rs" 
        using RS state_l by auto
      then show ?thesis 
        using ACC RS A by auto
    next
      case (state_r x2)
      then have A:"word_to_state a s = transition a x2 c"
        using word_to_state_append_ch[of a s c] by auto
      then show ?thesis using ACC state_r by force
      qed
    qed
  show "(c#s \<in> lang_rev (append_ch a c)) \<Longrightarrow> (s \<in> lang_rev a)"
  proof -
    assume "c#s \<in> lang_rev (append_ch a c)"
    then have "word_to_state (append_ch a c) (c#s) \<in> accepting (append_ch a c)" by auto
    then obtain rs where RS:"word_to_state (append_ch a c) (c#s) = state_r rs" by simp
    then have "rs \<in> accepting a" using \<open>accept (append_ch a c) (c # s)\<close> by force
    then show "s \<in> lang_rev a" 
    proof (cases "word_to_state (append_ch a c) s")
      case (state_l x1)
      then show ?thesis
        using word_to_state_append_ch[of a s c]  \<open>rs \<in> accepting a\<close> RS
        by simp
    next
      case (state_r x2)
      then show ?thesis
        using word_to_state_append_ch[of a s c]  \<open>rs \<in> accepting a\<close> RS
        by simp
    qed
  qed
qed


lemma append_ch_lang_rev_head:
  fixes a::"('alphabet,'s) da" and c::"'alphabet" and s::"'alphabet list"
  assumes "s \<in> lang_rev (append_ch a c)"  
  shows "hd s = c"
proof -
  obtain r where R:"state_r r = word_to_state (append_ch a c) s"
    using assms by fastforce
  then have "s \<noteq> []" by auto
  then have "word_to_state a s = transition a r c" using word_to_state_append_ch[of a s c] R
    by (metis (mono_tags, lifting) state_dup.simps(6))
  then show "hd s = c" using R \<open>s \<noteq> []\<close> process_word.elims by force
qed

lemma append_ch_lang_rev:
  fixes a::"('alphabet,'s) da" and c::"'alphabet" and s::"'alphabet list"
  shows "lang_rev (append_ch a c) = {(c#s) | s. s\<in>lang_rev a}"
proof 
  show "{c # s |s. s \<in> lang_rev a} \<subseteq> lang_rev (append_ch a c)" using append_ch_lang_rev_lr by fastforce
  have "\<forall> s. c#s \<in> lang_rev (append_ch a c) \<longrightarrow>  s \<in> lang_rev a"
    using append_ch_lang_rev_lr by metis
  have A:"\<forall> s. ((hd s = c \<and> s \<in> lang_rev (append_ch a c)) \<longrightarrow>  s \<in> {(c#s) | s. s\<in>lang_rev a})"
  proof (rule allI, rule impI)
    fix s
    assume "hd s = c \<and> s \<in> lang_rev (append_ch a c)"
    then have "s \<noteq> []" by auto
    then obtain s' where "s = c#s'"
      by (metis \<open>hd s = c \<and> s \<in> lang_rev (append_ch a c)\<close> list.collapse)
    then show "s \<in> {c # s |s. s \<in> lang_rev a}"
      using \<open>\<forall>s. c # s \<in> lang_rev (append_ch a c) \<longrightarrow> s \<in> lang_rev a\<close> \<open>hd s = c \<and> s \<in> lang_rev (append_ch a c)\<close> by force
  qed
  then show "lang_rev (append_ch a c) \<subseteq> {c # s |s. s \<in> lang_rev a}"
    using append_ch_lang_rev_head by fastforce
qed

lemma append_ch_hom:
  assumes "lang a = lang b"
  shows "lang (append_ch a c) = lang (append_ch b c)"
proof -
  have A:"lang_rev (append_ch a c) = {(c#s) | s. s\<in>lang_rev a}"
    using append_ch_lang_rev[of a c] by simp
  have B:"... = {(c#s) | s. s\<in>lang_rev b}" using assms by auto
  have "... = lang_rev (append_ch b c)" 
    using append_ch_lang_rev[of b c] by simp
  then show ?thesis using A B by auto
qed

lemma pref_quotient_hom:
  assumes "lang a = lang b"
  shows "lang (pref_quotient a w) = lang (pref_quotient b w)"
proof -
  have A:"lang (pref_quotient a w) = {s |s. w@s \<in> lang a}"
    using pref_quotient_lang by simp
  have B:"lang (pref_quotient b w) = {s |s. w@s \<in> lang b}"
    using pref_quotient_lang by simp
  have C:"{s |s. w@s \<in> lang a} = {s |s. w@s \<in> lang b}"
    using assms by simp
  then show ?thesis using A B by auto
qed


fun map_state::"('s\<Rightarrow>'t) \<Rightarrow> ('t\<Rightarrow>'s) \<Rightarrow> ('alphabet,'s) da \<Rightarrow> ('alphabet,'t) da" where
  "map_state f g a = da 
    (f (initial a)) 
    (\<lambda> s c. f (transition a (g(s)) c))
    (f ` (accepting a))"


lemma biject_state_map_ws:
  fixes f::"'s\<Rightarrow>'t" and g::"'t\<Rightarrow>'s" and a::"('alphabet,'s) da"
  assumes "\<forall>s. g(f(s)) = s"
  shows "word_to_state (map_state f g a) w = f (word_to_state a w)"
proof (induct w)
  case Nil
  then show ?case by auto
next
  case (Cons c w)
  then show ?case using assms local.Cons by auto
qed
lemma biject_state_map_lang_rev:
  fixes f::"'s\<Rightarrow>'t" and g::"'t\<Rightarrow>'s" and a::"('alphabet,'s) da"
  assumes "\<forall>s. g(f(s)) = s"
  shows "lang_rev (map_state f g a) = lang_rev a"
proof - 
  have "\<forall>s. accept (map_state f g a) s = accept a s" proof (rule allI)
    fix s::"'alphabet list"
    have "accepting (map_state f g a) = f ` (accepting a)" by auto
    then show "accept (map_state f g a) s = accept a s" using biject_state_map_ws
      by (metis (no_types, lifting) assms image_iff)
  qed
  then show ?thesis by auto
qed

fun map_dup_to_lvs::"(nat \<times> 's) state_dup \<Rightarrow> (nat \<times> 's)" where
  "map_dup_to_lvs (state_l (lv,s)) = (lv * 2, s)" | 
  "map_dup_to_lvs (state_r (lv,s)) = (lv * 2 + 1, s)"

fun map_dup_to_lvs_inv::"(nat \<times> 's) \<Rightarrow> (nat \<times> 's) state_dup" where
  "map_dup_to_lvs_inv (lv, s) = (
    if (lv mod 2 = 1) then state_r (divide (lv-1) 2, s) else state_l (divide lv 2, s)
  )"


lemma map_dup_to_lvs_i_left:
  shows "map_dup_to_lvs_inv (map_dup_to_lvs (state_l (lv, s'))) = (state_l (lv, s'))"
proof -
  show ?thesis by auto
qed

lemma map_dup_to_lvs_i_right:
  shows "map_dup_to_lvs_inv (map_dup_to_lvs (state_r (lv, s'))) = (state_r (lv, s'))"
proof -
  obtain v where "v = map_dup_to_lvs (state_r (lv, s'))" by auto
  then have "v = (lv * 2 + 1, s')" by auto
  then have "(fst v) mod 2 = 1" by (metis fstI mod_mult_self3 one_mod_two_eq_one)
  then have "map_dup_to_lvs_inv v = state_r(lv, s')" 
    by (simp add: \<open>v = (lv * 2 + 1, s')\<close>)
  show ?thesis
    using \<open>map_dup_to_lvs_inv v = state_r (lv, s')\<close> \<open>v = map_dup_to_lvs (state_r (lv, s'))\<close> by blast
qed

lemma map_dup_to_lvs_i:
  shows "map_dup_to_lvs_inv (map_dup_to_lvs s) = s"
  by (metis map_dup_to_lvs_i_left map_dup_to_lvs_i_right prod.collapse state_dup.exhaust)

fun append_ch_lv::"('alphabet,nat \<times> 's) da \<Rightarrow> 'alphabet \<Rightarrow> ('alphabet,nat \<times> 's) da" where
  "append_ch_lv a w = 
    (map_state map_dup_to_lvs map_dup_to_lvs_inv (append_ch a w))
  "

fun append_word_lv_rev::"('alphabet,nat \<times> 's) da \<Rightarrow> 'alphabet list \<Rightarrow> ('alphabet,nat \<times> 's) da" where
  "append_word_lv_rev a [] = a" |
  "append_word_lv_rev a (c#w) = append_ch_lv (append_word_lv_rev a w) c"

fun append_word_lv::"('alphabet,nat \<times> 's) da \<Rightarrow> 'alphabet list \<Rightarrow> ('alphabet,nat \<times> 's) da" where
  "append_word_lv a w = append_word_lv_rev a (rev w)"

fun lift_lv_state::"('alphabet,'s) da \<Rightarrow> ('alphabet,nat\<times>'s) da" where
  "lift_lv_state a = map_state (Pair (0::nat)) snd a"

lemma lift_lv_state_lang_rev:
  "lang_rev (lift_lv_state a) = lang_rev a"
proof -
  have "\<forall> s. snd((Pair (0::nat) s)) = s" by auto
  then show ?thesis using biject_state_map_lang_rev[of snd "Pair (0::nat)" a] by auto
qed

fun append_word_rev::"('alphabet,'s) da \<Rightarrow> 'alphabet list \<Rightarrow> ('alphabet, nat \<times> 's) da" where
  "append_word_rev a w = append_word_lv_rev (lift_lv_state a) w"

fun append_word::"('alphabet,'s) da \<Rightarrow> 'alphabet list \<Rightarrow> ('alphabet, nat \<times> 's) da" where
  "append_word a w = append_word_lv (lift_lv_state a) w"

lemma append_word_rev_is_rev:
  "append_word a w = append_word_rev a (rev w)"
  by simp

lemma ch_lv_eq:
  "lang_rev (append_ch_lv a c) = lang_rev (append_ch a c)"
proof -
  have "lang_rev (map_state map_dup_to_lvs map_dup_to_lvs_inv (append_ch a c)) = lang_rev (append_ch a c)"
    by (metis biject_state_map_lang_rev map_dup_to_lvs_i)
  then show ?thesis by simp
qed

lemma append_word_lang_rev_to_ch:
  "lang_rev (append_word_rev a (c#w)) = lang_rev (append_ch (append_word_rev a w) c)"
proof -
  have "lang_rev (append_word_rev a (c#w)) = lang_rev (append_ch_lv (append_word_rev a w) c)"
  by simp
  then show ?thesis using ch_lv_eq by metis
qed

lemma empty_app_word_rev:"lang (append_word_rev a []) = lang a"
proof -
  have A:"lang (append_word_lv_rev(lift_lv_state a) []) = lang (lift_lv_state a)" by force
  then show ?thesis by (metis append_word_rev.simps lift_lv_state_lang_rev)
qed

lemma append_ch_lv_lang_rev:
  fixes a::"('alphabet,nat\<times>'s) da" and c::"'alphabet" and s::"'alphabet list"
  shows "lang_rev (append_ch_lv a c) = {(c#s) | s. s \<in> lang_rev a}"
proof -
  have "lang_rev (map_state map_dup_to_lvs map_dup_to_lvs_inv (append_ch a c)) = lang_rev (append_ch a c)"
    using biject_state_map_lang_rev map_dup_to_lvs_i by metis
  then show ?thesis by (metis append_ch_lang_rev append_ch_lv.elims)
qed


lemma append_word_lv_rev_lang_rev:
  fixes a::"('alphabet,nat\<times>'s) da" and w::"'alphabet list" and s::"'alphabet list"
  shows "lang_rev (append_word_lv_rev a w) = {w@s |s. s\<in>lang_rev a}" 
proof (induct w )
  case Nil
  then show ?case by auto
next
  case (Cons c w)
  then have IH:"lang_rev (append_word_lv_rev a w) = {w@s |s. s\<in>lang_rev a}" by auto
  then have "lang_rev (append_ch_lv (append_word_lv_rev a w) c) = {c#s |s. s\<in>lang_rev (append_word_lv_rev a w)}"
       using append_ch_lv_lang_rev[of "append_word_lv_rev a w" c] by auto
  then show ?case using append_ch_lv_lang_rev 
    using Collect_cong append_Cons append_word_lv_rev.simps(2) local.Cons mem_Collect_eq by auto
qed


lemma append_word_lv_lang_rev:
  fixes a::"('alphabet,nat\<times>'s) da" and w::"'alphabet list" and s::"'alphabet list"
  shows "lang_rev (append_word_lv a (rev w)) = {w@s |s. s\<in>lang_rev a}" 
  using append_word_lv_rev_lang_rev by auto

lemma append_word_lang_rev:
  fixes a::"('alphabet,'s) da" and w::"'alphabet list" and s::"'alphabet list"
  shows "lang_rev (append_word_rev a w) = {w@s |s. s\<in>lang_rev a}"
proof -
  have "lang_rev (append_word_rev a w) = lang_rev (append_word_lv_rev (lift_lv_state a) w)" 
    using lift_lv_state_lang_rev by auto
  then have "... = {w@s |s. s\<in>lang_rev (lift_lv_state a)}" 
    using append_word_lv_rev_lang_rev[of "lift_lv_state a" w] by auto
  then have "... = {w@s |s. s\<in>lang_rev a}" 
    using lift_lv_state_lang_rev by fastforce
  then show ?thesis using append_word_lv_rev_lang_rev
    using \<open>lang_rev (append_word_lv_rev (lift_lv_state a) w) = {w @ s |s. s \<in> lang_rev (lift_lv_state a)}\<close> by auto
qed

lemma append_word_lang:
  fixes a::"('alphabet,'s) da" and w::"'alphabet list" and s::"'alphabet list"
  shows "lang (append_word a w) = {s@w |s. s\<in>lang a}"
proof -
  have "lang_rev (append_word_rev a (rev w)) = {(rev w)@s |s. s\<in>lang_rev a}" 
    using append_word_lang_rev by auto
  then have "rev ` lang_rev (append_word_rev a (rev w)) = rev ` {(rev w)@s |s. s\<in>lang_rev a}" 
    using rev_rev_ident  by auto
  
  then have "lang (append_word_rev a (rev w)) = {rev ((rev w)@s) |s. s\<in>lang_rev a}" 
    by (metis Setcompr_eq_image image_image)

  then have "lang (append_word_rev a (rev w)) = {s@w |s. s\<in>lang a}"
    using rev_rev_ident  by auto

  then have "lang (append_word a w) = {s@w |s. s\<in>lang a}"
    by auto
  
  then show ?thesis by auto
qed
end
