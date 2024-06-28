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


fun mult_lincomb::"'v LinComb \<Rightarrow> rat \<Rightarrow> 'v LinComb" where
  "mult_lincomb lc r = map (\<lambda>(u,c). (u, c * r)) lc"

lemma coeff_mult:
  "coeff (mult_lincomb a r) v = coeff a v * r"
proof (induct a)
  case Nil
  then show ?case by simp
next
  case (Cons a1 a2)
  have A:"coeff (mult_lincomb (a1 # a2) r) v = (if fst a1 = v then snd a1 else 0) * r + coeff a2 v * r"
    apply simp using Cons by (simp add: case_prod_beta)
  have B:"coeff (a1 # a2) v * r = (if fst a1 = v then snd a1 else 0) * r + coeff a2 v * r"
    using distrib_right by auto
  show ?case using A B by argo
qed

lemma mult_zero_zero:
  "lincomb_eq (mult_lincomb s 0) zero"
  apply (induct s) apply simp by auto

fun add_lincomb::"'v LinComb \<Rightarrow> 'v LinComb \<Rightarrow> 'v LinComb" where
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

fun sub_lincomb::"'v LinComb \<Rightarrow> 'v LinComb \<Rightarrow> 'v LinComb" where
  "sub_lincomb  l r  = add_lincomb l (mult_lincomb r (-1))"

lemma same_sub_zero:
  "coeff (sub_lincomb a a) = coeff zero" apply simp
proof -
  have "\<forall>s. coeff a s =  - (coeff (mult_lincomb a (-1)) s)"
    apply(induct a) apply auto[1] by auto
  then show "coeff (a @ map (\<lambda>(u, c). (u, - c)) a) = coeff zero" by auto
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

fun eq_lincomb::"'v LinComb \<Rightarrow> 'v LinComb \<Rightarrow> bool" where
  "eq_lincomb l r = (\<forall>v. coeff l v = coeff r v)"

fun assign_lincomb::"'v Assign \<Rightarrow> 'v LinComb \<Rightarrow> rat" where
  "assign_lincomb a lc = sum_list (map (\<lambda>s. (a (fst s)) * (snd s)) lc)"

lemma assign_lincomb_head:
  "assign_lincomb a (h#t) = ((a (fst h)) * (snd h)) + (assign_lincomb a t)"
  by auto
lemma sum_distrib_right:
  fixes f::"'a \<Rightarrow> rat"
  shows "(\<Sum>a\<leftarrow>as. f a) * y = (\<Sum>a\<leftarrow>as. (f a) * y)"
  by (simp add: sum_list_mult_const)

lemma list_sum_list_sum:
  fixes f::"'a \<Rightarrow> 'b \<Rightarrow> rat"
  shows "(\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>a. f ae be)) = (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. f ae be))"
  apply(induct a) proof simp
  fix a1 and a2
  have "(\<Sum>be\<leftarrow>b. \<Sum>ae\<leftarrow>a1 # a2. f ae be) = 
        (\<Sum>be\<leftarrow>b. f a1 be + (\<Sum>ae\<leftarrow>a2. f ae be))" by simp
  then have A: "(\<Sum>be\<leftarrow>b. \<Sum>ae\<leftarrow>a1 # a2. f ae be) = 
        (\<Sum>be\<leftarrow>b. f a1 be) + (\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>a2. f ae be))" 
    using sum_list_addf by force
  have "(\<Sum>ae\<leftarrow>a1 # a2. sum_list (map (f ae) b)) =
        (\<Sum>be\<leftarrow>b. f a1 be) + (\<Sum>ae\<leftarrow>a2. sum_list (map (f ae) b))" 
    by simp
  then show "(\<Sum>be\<leftarrow>b. \<Sum>ae\<leftarrow>a2. f ae be) = (\<Sum>ae\<leftarrow>a2. sum_list (map (f ae) b)) \<Longrightarrow>
       (\<Sum>be\<leftarrow>b. \<Sum>ae\<leftarrow>a1 # a2. f ae be) = (\<Sum>ae\<leftarrow>a1 # a2. sum_list (map (f ae) b))" 
    using A by simp
qed


lemma assign_lincomb_comm:
  fixes a::"'v LinComb" and b::"'v LinComb"
  shows "assign_lincomb (coeff a) b = assign_lincomb (coeff b) a"
proof(simp only: assign_lincomb.simps coeff.simps)
  have A1:"(\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>a. if fst ae = fst be then snd ae else 0) * (snd be)) = 
        (\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>filter (\<lambda>ae. fst ae = fst be) a. snd ae)* (snd be))"
    by(simp add:sum_list_map_filter'[symmetric]) 
  have A2:"... = (\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>filter (\<lambda>ae. fst ae = fst be) a. snd ae * (snd be)))"  
    using sum_distrib_right by metis
  have A3:"... = (\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>a. if fst ae = fst be then snd ae * (snd be) else 0))"
    by (simp add: sum_list_map_filter')
  have A4:"... = (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst ae = fst be then snd ae * (snd be) else 0))"
    using list_sum_list_sum by force
  have A:"(\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>a. if fst ae = fst be then snd ae else 0) * (snd be)) = 
          (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst ae = fst be then snd ae * (snd be) else 0))"
    using A1 A2 A3 A4 by argo
  
  have B1:"(\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst be = fst ae then snd be else 0) * (snd ae)) = 
        (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>filter (\<lambda>be. fst be = fst ae) b. snd be)* (snd ae))"
    by(simp add:sum_list_map_filter'[symmetric]) 
  have B2:"... = (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>filter (\<lambda>be. fst be = fst ae) b. snd be* (snd ae)))"  
    using sum_distrib_right by metis
  have B3:"... = (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst be = fst ae then snd be * (snd ae) else 0))"
    by (simp add: sum_list_map_filter')
  have B:"(\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst be = fst ae then snd be else 0) * (snd ae)) = 
          (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst be = fst ae then snd be * (snd ae) else 0))"
    using B1 B2 B3 by argo
  have B':"... = 
          (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst ae = fst be then snd ae * (snd be) else 0))"
  proof -
    define op::"'v\<times>rat\<Rightarrow>'v\<times>rat\<Rightarrow>rat" where 
      "op = (\<lambda>ae be. if fst be = fst ae then snd be * snd ae else 0)"
    then have op_comm:"\<And>ae be. op ae be = op be ae" by simp
    have A:"(\<Sum>ae\<leftarrow>a. \<Sum>be\<leftarrow>b. if fst be = fst ae then snd be * snd ae else 0) = 
          (\<Sum>ae\<leftarrow>a. \<Sum>be\<leftarrow>b. (op ae be))" using op_def by simp
    have "(\<Sum>ae\<leftarrow>a. \<Sum>be\<leftarrow>b. if fst ae = fst be then snd ae * snd be else 0) = 
          (\<Sum>ae\<leftarrow>a. \<Sum>be\<leftarrow>b. (op be ae))" using op_def by simp
    then show ?thesis using op_comm A by simp
  qed

  show "(\<Sum>be\<leftarrow>b. (\<Sum>ae\<leftarrow>a. if fst ae = fst be then snd ae else 0) * (snd be)) = 
        (\<Sum>ae\<leftarrow>a. (\<Sum>be\<leftarrow>b. if fst be = fst ae then snd be else 0) * (snd ae))"
    using A B[symmetric] B' by simp
qed

lemma mult_sem:
  "assign_lincomb a (mult_lincomb l1 r) = (assign_lincomb a l1) * r"
apply(induct l1) apply simp by (simp add: case_prod_beta' distrib_right)
  
fun assign_constraint::"'v Assign \<Rightarrow> 'v Constraint \<Rightarrow> bool" where
  "assign_constraint a (Constraint lexp GE r) = (let lv = assign_lincomb a lexp in  lv \<ge> r)" |
  "assign_constraint a (Constraint lexp LE r) = (let lv = assign_lincomb a lexp in  lv \<le> r)" |
  "assign_constraint a (Constraint lexp EQ r) = (let lv = assign_lincomb a lexp in  lv = r)"

fun assign_mip::"'v Assign \<Rightarrow> 'v MIP \<Rightarrow> bool" where
  "assign_mip a cs = list_all (assign_constraint a) cs"

lemma assign_add_hom:
  shows "(assign_lincomb a (add_lincomb u v)) = ((assign_lincomb a u) + (assign_lincomb a v))"
  by auto

abbreviation have_solution_mip::"'v MIP \<Rightarrow> bool" where
  "have_solution_mip cs \<equiv> \<exists>a. assign_mip a cs"

fun add_cons::"'v Constraint \<Rightarrow> 'v Constraint \<Rightarrow> 'v Constraint" where
  "add_cons (Constraint l1 GE r1) (Constraint l2 GE r2) = (Constraint (l1@l2) GE (r1+r2))" |
  "add_cons (Constraint l1 LE r1) (Constraint l2 LE r2) = (Constraint (l1@l2) LE (r1+r2))" |
  "add_cons (Constraint l1 EQ r1) (Constraint l2 EQ r2) = (Constraint (l1@l2) EQ (r1+r2))" |
  "add_cons c1 c2 = undefined"

fun opposite_cop::"Comparator \<Rightarrow> Comparator" where 
  "opposite_cop GE = LE" |
  "opposite_cop LE = GE" |
  "opposite_cop EQ = EQ"

fun mult_cons::"'v Constraint \<Rightarrow> rat \<Rightarrow> 'v Constraint" where 
  "mult_cons (Constraint l1 cop r1) r = 
     Constraint (mult_lincomb l1 r) (if r \<ge> 0 then cop else opposite_cop cop) (r1 * r)
  "

lemma mult_cons_valid:
  assumes "assign_constraint a (Constraint l1 cop r1)"
  shows "assign_constraint a (mult_cons (Constraint l1 cop r1) r)"
proof(cases "r \<ge> 0")
  case True
  have "assign_lincomb a (mult_lincomb l1 r) = (assign_lincomb a l1) * r"
    using coeff_mult mult_sem by blast
  then show ?thesis apply(cases cop)
    using assms True using mult_right_mono apply auto[1]
    using assms True using mult_right_mono apply auto[1]
    using assms True using mult_right_mono by auto[1]
next
  case False
  have "assign_lincomb a (mult_lincomb l1 r) = (assign_lincomb a l1) * r"
    using coeff_mult mult_sem by blast
  then show ?thesis  apply(cases cop)
    using assms False using mult_right_mono apply simp
    using assms False using mult_right_mono apply simp
    using assms False using mult_right_mono by simp
qed


lemma add_cons_valid:
  assumes "assign_constraint a (Constraint l1 cop r1)"
          "assign_constraint a (Constraint l2 cop r2)"
  shows "assign_constraint a (add_cons (Constraint l1 cop r1) (Constraint l2 cop r2))"
  apply(cases cop) apply(simp_all only:assign_constraint.simps add_cons.simps)
  using assms apply auto[1] using assms apply auto[1] using assms by auto[1]

lemma weaken_eq_ge:
  assumes "assign_constraint a (Constraint l1 EQ r1)"
  shows "assign_constraint a (Constraint l1 GE r1)"
  using assms by fastforce

lemma weaken_eq_le:
  assumes "assign_constraint a (Constraint l1 EQ r1)"
  shows "assign_constraint a (Constraint l1 LE r1)"
  using assms by fastforce

end
