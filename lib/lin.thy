theory lin
  imports Main HOL.Rat
begin

term "Fract 1 2 + Fract 2 3 = Fract 7 6"
value "Rat.zero_rat_inst.zero_rat"

type_synonym 'v LinComb = "'v \<Rightarrow> rat"
datatype Comparator = GE | LE
datatype 'v Constraint = Constraint (lhs:"'v LinComb") (op: Comparator) (rhs: rat)
type_synonym 'v MIP = "'v Constraint list"
type_synonym 'v Assign = "'v \<Rightarrow> rat"

abbreviation zero::"'v LinComb" where
  "zero \<equiv> (\<lambda>v. 0)"

fun coeff::"'v LinComb \<Rightarrow> 'v \<Rightarrow> rat" where
  "coeff lc v = lc v"

fun mult_lincomb::"'v LinComb ⇒ rat ⇒ 'v LinComb" where
  "mult_lincomb l r = (times r) o l"

lemma mult_zero_zero:
  "mult_lincomb s 0 = zero" by auto

abbreviation lincomb_to_assign::"'v LinComb \<Rightarrow> 'v \<Rightarrow> rat" where
  "lincomb_to_assign lc v \<equiv> coeff lc v"

fun add_lincomb::"'v LinComb ⇒ 'v LinComb ⇒ 'v LinComb" where
  "add_lincomb  l r  = (\<lambda>v. (l v) + (r v))"


fun sub_lincomb::"'v LinComb ⇒ 'v LinComb ⇒ 'v LinComb" where
  "sub_lincomb  l r  = (\<lambda>v. (l v) - (r v))"

lemma sub_add_exc: "sub_lincomb (add_lincomb a b) (add_lincomb c d) = add_lincomb (sub_lincomb a c) (sub_lincomb b d)"
  by auto

fun agg_lincomb::"'v LinComb list \<Rightarrow> 'v LinComb" where
  "agg_lincomb [] = zero" |
  "agg_lincomb (a#s) = add_lincomb a (agg_lincomb s)"


fun is_zero_lincomb::"'v LinComb \<Rightarrow> bool" where
  "is_zero_lincomb s = (s=zero)"

fun eq_lincomb::"'v LinComb ⇒ 'v LinComb ⇒ bool" where
  "eq_lincomb l r = (\<forall>v. coeff l v = coeff r v)"

fun assign_lincomb::"'v Assign \<Rightarrow> 'v LinComb \<Rightarrow> rat" where
  "assign_lincomb a l = sum id {(a v) * (l v) | v::'v. True}"

fun assign_constraint::"'v Assign \<Rightarrow> 'v Constraint \<Rightarrow> bool" where
  "assign_constraint a c = (let l = assign_lincomb a (lhs c) in case (op c) of 
    GE \<Rightarrow> l \<ge> (rhs c) |
    LE \<Rightarrow> l \<le> (rhs c)
  )"

fun assign_mip::"'v Assign \<Rightarrow> 'v MIP \<Rightarrow> bool" where
  "assign_mip a cs = list_all (assign_constraint a) cs"
end
