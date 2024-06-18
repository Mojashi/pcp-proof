theory lin_terms
  imports Main HOL.Rat
begin

type_synonym 'v LinComb = "('v\<times>rat) list"
datatype Comparator = GE | LE | EQ
datatype 'v Constraint = Constraint (lhs:"'v LinComb") (op: Comparator) (rhs: rat)
type_synonym 'v MIP = "'v Constraint list"
type_synonym 'v Assign = "'v \<Rightarrow> rat"

abbreviation zero::"'v LinComb" where
  "zero \<equiv> []"

fun coeff::"'v LinComb \<Rightarrow> 'v \<Rightarrow> rat" where
  "coeff lc v = sum_list (map (\<lambda>s. if fst s=v then snd s else 0) lc)"

abbreviation lincomb_eq::"'v LinComb \<Rightarrow> 'v LinComb \<Rightarrow> bool" where
  "lincomb_eq a b \<equiv> \<forall>v. coeff a v = coeff b v"


fun mult_lincomb::"'v LinComb ⇒ rat ⇒ 'v LinComb" where
  "mult_lincomb lc r = map (\<lambda>(u,c). (u, c * r)) lc"

lemma mult_zero_zero:
  "lincomb_eq (mult_lincomb s 0) zero"
  apply (induct s) apply simp by auto

fun add_lincomb::"'v LinComb ⇒ 'v LinComb ⇒ 'v LinComb" where
  "add_lincomb  l r  = l@r"

lemma add_coeff_same:
  assumes "coeff a = coeff b"
  shows "coeff (add_lincomb a c) = coeff (add_lincomb b c)"
  apply simp  
proof -
  have "\<And>s. coeff (a @ c) s = coeff (b @ c) s" proof-
    fix s
    have A:"coeff (a @ c) s = coeff a s + (coeff c s)" by auto
    have "coeff (b @ c) s = ..." using assms by auto 
    then show "coeff (a @ c) s = coeff (b @ c) s" using A by simp
  qed
  then show "coeff (a @ c) = coeff (b @ c)" by blast
qed

lemma add_coeff:
  "coeff (add_lincomb a b) s = (coeff a s) + (coeff b s)"
  by simp

fun sub_lincomb::"'v LinComb ⇒ 'v LinComb ⇒ 'v LinComb" where
  "sub_lincomb  l r  = add_lincomb l (mult_lincomb r (-1))"

lemma same_sub_zero:
  "coeff (sub_lincomb a a) = coeff zero" apply simp
proof -
  have "\<forall>s. coeff a s =  - (coeff (mult_lincomb a (-1)) s)"
    apply(induct a) apply auto[1] by auto
  then show "coeff (a @ map (λ(u, c). (u, - c)) a) = coeff zero" by auto
qed

lemma sub_add_exc: "lincomb_eq
(sub_lincomb (add_lincomb a b) (add_lincomb c d))
(add_lincomb (sub_lincomb a c) (sub_lincomb b d))"
  by simp

fun agg_lincomb::"'v LinComb list \<Rightarrow> 'v LinComb" where
  "agg_lincomb [] = zero" |
  "agg_lincomb (a#s) = add_lincomb a (agg_lincomb s)"


fun is_zero_lincomb::"'v LinComb \<Rightarrow> bool" where
  "is_zero_lincomb s = (s=zero)"

fun eq_lincomb::"'v LinComb ⇒ 'v LinComb ⇒ bool" where
  "eq_lincomb l r = (\<forall>v. coeff l v = coeff r v)"

fun assign_lincomb::"'v Assign \<Rightarrow> 'v LinComb \<Rightarrow> rat" where
  "assign_lincomb a lc = sum_list (map (\<lambda>s. (a (fst s)) * (snd s)) lc)"

lemma sum_distrib_right:
  fixes f::"'a \<Rightarrow> rat"
  shows "(∑a←as. f a) * y = (∑a←as. (f a) * y)"
  by (simp add: sum_list_mult_const)

lemma list_sum_list_sum:
  fixes f::"'a \<Rightarrow> 'b \<Rightarrow> rat"
  shows "(∑be←b. (∑ae←a. f ae be)) = (∑ae←a. (∑be←b. f ae be))"
  apply(induct a) proof simp
  fix a1 and a2
  have "(∑be←b. ∑ae←a1 # a2. f ae be) = 
        (∑be←b. f a1 be + (∑ae←a2. f ae be))" by simp
  then have A: "(∑be←b. ∑ae←a1 # a2. f ae be) = 
        (∑be←b. f a1 be) + (∑be←b. (∑ae←a2. f ae be))" 
    using sum_list_addf by force
  have "(∑ae←a1 # a2. sum_list (map (f ae) b)) =
        (∑be←b. f a1 be) + (∑ae←a2. sum_list (map (f ae) b))" 
    by simp
  then show "(∑be←b. ∑ae←a2. f ae be) = (∑ae←a2. sum_list (map (f ae) b)) ⟹
       (∑be←b. ∑ae←a1 # a2. f ae be) = (∑ae←a1 # a2. sum_list (map (f ae) b))" 
    using A by simp
qed


find_consts "'a list \<Rightarrow> 'b list \<Rightarrow> ('a\<times>'b) list"
lemma assign_lincomb_comm:
  fixes a::"'v LinComb" and b::"'v LinComb"
  shows "assign_lincomb (coeff a) b = assign_lincomb (coeff b) a"
proof(simp only: assign_lincomb.simps coeff.simps)
  have A1:"(∑be←b. (∑ae←a. if fst ae = fst be then snd ae else 0) * (snd be)) = 
        (∑be←b. (∑ae←filter (λae. fst ae = fst be) a. snd ae)* (snd be))"
    by(simp add:sum_list_map_filter'[symmetric]) 
  have A2:"... = (∑be←b. (∑ae←filter (λae. fst ae = fst be) a. snd ae * (snd be)))"  
    using sum_distrib_right by metis
  have A3:"... = (∑be←b. (∑ae←a. if fst ae = fst be then snd ae * (snd be) else 0))"
    by (simp add: sum_list_map_filter')
  have A4:"... = (∑ae←a. (∑be←b. if fst ae = fst be then snd ae * (snd be) else 0))"
    using list_sum_list_sum by force
  have A:"(∑be←b. (∑ae←a. if fst ae = fst be then snd ae else 0) * (snd be)) = 
          (∑ae←a. (∑be←b. if fst ae = fst be then snd ae * (snd be) else 0))"
    using A1 A2 A3 A4 by argo
  
  have B1:"(∑ae←a. (∑be←b. if fst be = fst ae then snd be else 0) * (snd ae)) = 
        (∑ae←a. (∑be←filter (λbe. fst be = fst ae) b. snd be)* (snd ae))"
    by(simp add:sum_list_map_filter'[symmetric]) 
  have B2:"... = (∑ae←a. (∑be←filter (λbe. fst be = fst ae) b. snd be* (snd ae)))"  
    using sum_distrib_right by metis
  have B3:"... = (∑ae←a. (∑be←b. if fst be = fst ae then snd be * (snd ae) else 0))"
    by (simp add: sum_list_map_filter')
  have B:"(∑ae←a. (∑be←b. if fst be = fst ae then snd be else 0) * (snd ae)) = 
          (∑ae←a. (∑be←b. if fst be = fst ae then snd be * (snd ae) else 0))"
    using B1 B2 B3 by argo
  have B':"... = 
          (∑ae←a. (∑be←b. if fst ae = fst be then snd ae * (snd be) else 0))"
  proof -
    define op::"'v\<times>rat\<Rightarrow>'v\<times>rat\<Rightarrow>rat" where 
      "op = (\<lambda>ae be. if fst be = fst ae then snd be * snd ae else 0)"
    then have op_comm:"\<And>ae be. op ae be = op be ae" by simp
    have A:"(∑ae←a. ∑be←b. if fst be = fst ae then snd be * snd ae else 0) = 
          (∑ae←a. ∑be←b. (op ae be))" using op_def by simp
    have "(∑ae←a. ∑be←b. if fst ae = fst be then snd ae * snd be else 0) = 
          (∑ae←a. ∑be←b. (op be ae))" using op_def by simp
    then show ?thesis using op_comm A by simp
  qed

  show "(∑be←b. (∑ae←a. if fst ae = fst be then snd ae else 0) * (snd be)) = 
        (∑ae←a. (∑be←b. if fst be = fst ae then snd be else 0) * (snd ae))"
    using A B[symmetric] B' by simp
qed

fun assign_constraint::"'v Assign \<Rightarrow> 'v Constraint \<Rightarrow> bool" where
  "assign_constraint a (Constraint lexp GE r) = (let lv = assign_lincomb a lexp in  lv \<ge> r)" |
  "assign_constraint a (Constraint lexp LE r) = (let lv = assign_lincomb a lexp in  lv \<le> r)" |
  "assign_constraint a (Constraint lexp EQ r) = (let lv = assign_lincomb a lexp in  lv = r)"

fun assign_mip::"'v Assign \<Rightarrow> 'v MIP \<Rightarrow> bool" where
  "assign_mip a cs = list_all (assign_constraint a) cs"

lemma assign_add_hom:
  shows "(assign_lincomb a (add_lincomb u v)) = ((assign_lincomb a u) + (assign_lincomb a v))"
    by auto
end
