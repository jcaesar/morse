
theory Evasive
  imports
    Bij_betw_simplicial_complex_bool_func
    MkIfex
    Alexander
begin

section\<open>Relation between type @{typ "bool vec => bool"} and type @{typ "'a boolfunc"}\<close>

definition vec_to_boolfunc :: "nat \<Rightarrow> (bool vec => bool) => (nat boolfunc)"
  where "vec_to_boolfunc n f = (\<lambda>i. f (vec n i))"

lemma
  ris: "reads_inside_set (\<lambda>i. bool_fun_threshold_2_3 (vec 4 i)) (set [0,1,2,3])"
  unfolding reads_inside_set_def
  unfolding bool_fun_threshold_2_3_def
  unfolding count_true_def
  unfolding dim_vec
  unfolding set_list_four [symmetric] by simp 

lemma
  shows "val_ifex (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0,1,2,3])
    = vec_to_boolfunc 4 bool_fun_threshold_2_3"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  unfolding vec_to_boolfunc_def
  using ris .

text\<open>For any Boolean function in dimension @{term n},
  its ifex representation is @{const ifex_ordered} and @{const ifex_minimal}.\<close>

lemma mk_ifex_boolean_function: 
  fixes f :: "bool vec => bool"
  shows "ro_ifex (mk_ifex (vec_to_boolfunc n f) [0..<n])"
  using mk_ifex_ro by fast

text\<open>Any Boolean function in dimension @{term n} can be 
  seen as an expression over the underlying set of variables.\<close>

lemma
  reads_inside_set_boolean_function:
  fixes f :: "bool vec => bool"
  shows "reads_inside_set (vec_to_boolfunc n f) {..<n}"
  unfolding vec_to_boolfunc_def
  unfolding reads_inside_set_def
  by (simp add: mk_vec_def vec_def)

text\<open>Any Boolean function of a finite dimension
  is equal to its ifex representation
  by means of @{const mk_ifex}.\<close>

lemma
  mk_ifex_equivalence:
  fixes f :: "bool vec => bool"
  shows "val_ifex (mk_ifex (vec_to_boolfunc n f) [0..<n])
    = vec_to_boolfunc n f"
  apply (rule ext)
  apply (rule val_ifex_mk_ifex_equal)
  using reads_inside_set_boolean_function [of n f]
  unfolding reads_inside_set_def by auto

(*definition bcount_true :: "nat => (nat=> bool) => nat"
  where "bcount_true n f =  (\<Sum>i = 0..<n. if f i then 1 else (0::nat))"

definition boolfunc_threshold_2_3 :: "(nat => bool) => bool"
  where "boolfunc_threshold_2_3 = (\<lambda>v. 2 \<le> bcount_true 4 v)"

definition proj_2 :: "(nat => bool) => bool"
  where "proj_2 = (\<lambda>v. v 2)"

definition proj_2_n3 :: "(nat => bool) => bool"
  where "proj_2_n3 = (\<lambda>v. v 2 \<and> \<not> v 3)"*)

definition proj_2_bool :: "bool vec \<Rightarrow> bool"
  where "proj_2_bool v = v $ 2"

definition proj_2_n3_bool :: "bool vec \<Rightarrow> bool"
  where "proj_2_n3_bool v = (v $ 2 \<and> \<not> v $ 3)"

text\<open>The following definition computes the height of an @{typ "'a ifex"} expression.\<close>

fun height :: "'a ifex => nat"
  where "height Trueif = 0"
  | "height Falseif = 0"
  | "height (IF v va vb) = 1 + max (height va) (height vb)"  

text\<open>Both @{term mk_ifex} and @{term height} can be used in computations.\<close>

lemma "height (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0..<4]) = 4"
  by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 
        (boolean_functions.Alexander_dual bool_fun_threshold_2_3)) [0..<4]) = 4"
  by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 bool_fun_threshold_2_3) [0..<4]) = 
  height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual bool_fun_threshold_2_3)) [0..<4])"
  by eval

(*lemma "height (mk_ifex (boolfunc_threshold_2_3) [0,1,2,3]) = 4"
  by eval

lemma "height (mk_ifex (proj_2) [0,1,2,3]) = 1"
  by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0,1,2,3]) = 1"
  by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 
  (boolean_functions.Alexander_dual proj_2_bool)) [0,1,2,3]) = 1"
  by eval

(*lemma "mk_ifex (proj_2) [0] = Falseif" by eval*)

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0] = Falseif" by eval

lemma "mk_ifex (vec_to_boolfunc 4 
        (boolean_functions.Alexander_dual proj_2_bool)) [0] = Falseif" 
  by eval

(*lemma "height (mk_ifex (proj_2) [0]) = 0" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0]) = 0" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 
      (boolean_functions.Alexander_dual proj_2_bool)) [0]) = 0" 
  by eval

(*lemma "mk_ifex (proj_2) [3,2,1,0] = IF 2 Trueif Falseif"
  by eval*)

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_bool) [3,2,1,0] = IF 2 Trueif Falseif"
  by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_bool)) [3,2,1,0] 
  = IF 2 Trueif Falseif"
  by eval

(*lemma "mk_ifex (proj_2) [0,1,2,3] = IF 2 Trueif Falseif"
  by eval*)

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0,1,2,3] = IF 2 Trueif Falseif"
  by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_bool)) [0,1,2,3] 
  = IF 2 Trueif Falseif"
  by eval

(*lemma "height (mk_ifex (proj_2) [0,1,2,3]) = 1" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 proj_2_bool) [0,1,2,3]) = 1" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_bool)) 
        [0,1,2,3]) = 1" by eval

(*lemma "mk_ifex (proj_2_n3) [0,1,2,3] = IF 2 (IF 3 Falseif Trueif) Falseif" by eval*)

text\<open>Here the @{typ "nat ifex"} obtained is different for 
  @{term "boolean_functions.Alexander_dual proj_2_n3_bool"}
  and @{term "proj_2_n3_bool"}. In some sense, they are "dual"\<close>

lemma "mk_ifex (vec_to_boolfunc 4 proj_2_n3_bool) [0,1,2,3] 
    = IF 2 (IF 3 Falseif Trueif) Falseif"
   by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual proj_2_n3_bool)) [0,1,2,3]
    = IF 2 Trueif (IF 3 Falseif Trueif)"
   by eval

(*lemma "mk_ifex (bf_False::nat boolfunc) [0,1,2,3] = Falseif" by eval*)

text\<open>Here the @{typ "nat ifex"} obtained is different for 
  @{term "boolean_functions.Alexander_dual (\<lambda>x. False)"}
  and @{term "(\<lambda>x. False)"}. In some sense, they are "dual"\<close>

lemma "mk_ifex (vec_to_boolfunc 4 (\<lambda>x. False)) [0,1,2,3] = Falseif" by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. False)))
  [0,1,2,3] = Trueif" 
  by eval

(*lemma "height (mk_ifex (bf_False::nat boolfunc) [0,1,2,3]) = 0" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 (\<lambda>x. False)) [0,1,2,3]) = 0" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. False))) 
  [0,1,2,3]) = 0"
  by eval

(*lemma "mk_ifex (bf_True::nat boolfunc) [0,1,2,3] = Trueif" by eval*)

text\<open>Here the @{typ "nat ifex"} obtained is different for 
  @{term "boolean_functions.Alexander_dual (\<lambda>x. False)"}
  and @{term "(\<lambda>x. False)"}. In some sense, they are "dual"\<close>

lemma "mk_ifex (vec_to_boolfunc 4 (\<lambda>x. True)) [0,1,2,3] = Trueif" by eval

lemma "mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. True)))
  [0,1,2,3] = Falseif"
  by eval

(*lemma "height (mk_ifex (bf_True::nat boolfunc) [0,1,2,3]) = 0" by eval*)

lemma "height (mk_ifex (vec_to_boolfunc 4 (\<lambda>x. True)) [0,1,2,3]) = 0" by eval

lemma "height (mk_ifex (vec_to_boolfunc 4 (boolean_functions.Alexander_dual (\<lambda>x. True))) 
  [0,1,2,3]) = 0"
  by eval

section\<open>Definition of \emph{evasive} Boolean function\<close>

text\<open>Now we introduce the definition of evasive Boolean function. 
  It is based on the height of the ifex expression of the given function.
  The definition is inspired by the one by Scoville~\cite[Ex. 6.19]{SC19}.\<close>

definition evasive :: "nat => (bool vec => bool) => bool"
  where "evasive n f \<equiv> (height (mk_ifex (vec_to_boolfunc n f) [0..<n])) = n"

(* all right, that can't be it. *)
(* First, consider the non-evasive function "if a2 then a1 else a3" *)
(* Here's a BDT for it: *)
lemma "val_ifex (IF 2 (IF 1 Trueif Falseif) (IF 3 Trueif Falseif)) = (\<lambda>a. if a 2 then a 1 else a 3)"
  by (rule ext; simp)
(* problem? height \<circ> mk_ifex on this returns 3 *)
value "mk_ifex (\<lambda>a. if a 2 then a 1 else a 3) [3,2,1::nat]"
lemma "height (mk_ifex (\<lambda>a. if a 2 then a 1 else a 3) [2,3,1::nat]) = 3"
  by eval
(* Note that the order of the variables in the list argument does not affect the output of mk_ifex*)
lemma "reads_inside_set f (set v2) \<Longrightarrow> set v1 = set v2 \<Longrightarrow> mk_ifex f v1 = mk_ifex f v2"
  (* This actually holds without the reads_inside_set, but the argument is a lot more subtle.. *)
  by (simp add: mk_ifex_ro ro_ifex_unique val_ifex_mk_ifex_equal)
(* but in fact, the order defined on the type of the atoms (nat here) decides all. *)
(* Why am I talking about this? Because mk_ifex returns reduced, ordered BDTs, and all BDDs must be reduced and ordered,
   and thus have the same height. (I won't prove the thus part, but I'm sure. I'm not a 100% sure all BDDs must be reduced/ordered) *)
(* Now for the sad part: There are situations where reduced ordered BDTs cannot have optimal height for any variable ordering *)
definition "mieser \<equiv> (\<lambda>a. if a 0 then (if a 2 then a 1 else a 3) 
                                 else (if a 1 then a 2 else a 3)) :: nat boolfunc"
definition "Mieser \<equiv> (IF 0 (IF 2 (IF 1 Trueif Falseif) (IF 3 Trueif Falseif)) 
                           (IF 1 (IF 2 Trueif Falseif) (IF 3 Trueif Falseif))) :: nat ifex"
lemma "val_ifex Mieser = mieser" by(rule ext; simp add: Mieser_def mieser_def)
(* Our manually constructed optimal BDT has height 3 *)
lemma "height Mieser = 3" by(simp add: Mieser_def)
(* But be careful: This lemma might read to you as "any reduced ordered bdt has height 4"
   But this is only for the one fixed variable order given by nats
   You'll have to manually convince yourself that this holds true even if e.g. 2 < 1.
 *)
lemma "ro_ifex f \<Longrightarrow> val_ifex f = mieser \<Longrightarrow> height f = 4"
(* In fact, this lemma is trivial. There is only one ro bdt that expresses mieser for the given order of nats *)
proof -
  have set: "reads_inside_set mieser (set [0,1,2,3])" by(simp add: mieser_def reads_inside_set_def)
  have 4: "height (mk_ifex mieser [0,1,2,3]) = 4" by eval
  assume m: "val_ifex f = mieser"
  assume "ro_ifex f"
  from ro_ifex_unique[OF this mk_ifex_ro, unfolded m] val_ifex_mk_ifex_equal[OF set]
  have "f = mk_ifex mieser [0,1,2,3]" by meson
  thus ?thesis using 4 by meson
qed


definition bf_evasive_on :: "'a boolfunc \<Rightarrow> 'a set \<Rightarrow> bool"
  where "bf_evasive_on f vs \<equiv> (\<exists>assmt. \<forall>update \<in> vs. f assmt \<noteq> f (assmt(update := \<not>assmt update)))"

definition "all_bdts f vars = {t. ifex_var_set t \<subseteq> vars \<and> val_ifex t = f}"
(* sanity checks\<dots> *)
lemma "Falseif \<in> all_bdts (\<lambda>_. False) x"
  unfolding all_bdts_def
  by auto
lemma "Falseif \<notin> all_bdts (\<lambda>a. a b) x"
  unfolding all_bdts_def
  by (auto dest: fun_cong[where x="\<lambda>_. True"])
lemma "IF 0 Trueif Falseif \<in> all_bdts (\<lambda>a. a 0) ({0} \<union> x)"
  by(simp add: all_bdts_def; rule ext; simp)

definition "bf_blind f vars \<equiv> \<lambda>assmt. f (\<lambda>v. if v \<in> vars then assmt v else False)"
lemma "reads_inside_set f vs \<Longrightarrow> bf_blind f vs = f"
  unfolding bf_blind_def
  unfolding reads_inside_set_def
  by force
  (* guess I don't need bf_blind *)

(* This thing is unusable *)
definition "bf_significant_vars f \<equiv> \<Inter>{vars. reads_inside_set f vars}"

(* truth table. less smart than mk_ifex, easier to work with. *)
fun mk_ifex_tt :: "('a :: linorder) boolfunc \<Rightarrow> 'a list \<Rightarrow> 'a ifex" where
"mk_ifex_tt f [] = (if f (const False) then Trueif else Falseif)" |
"mk_ifex_tt f (v#vs) = (IF v
                      (mk_ifex_tt (bf_restrict v True f) vs)
                      (mk_ifex_tt (bf_restrict v False f) vs))"

lemma mk_ifex_tt_varset[simp]: "ifex_var_set (mk_ifex_tt f vs) = set vs"
  by(induction vs arbitrary: f; simp)
lemma mk_ifex_tt_height[simp]: "height (mk_ifex_tt f vs) = length vs"
  by(induction vs arbitrary: f; simp)

lemma mk_ifex_tt[simp]: "reads_inside_set f (set vs) \<Longrightarrow> val_ifex (mk_ifex_tt f vs) = f"
proof(induction vs arbitrary: f)
  case Nil
  then show ?case by(auto dest!: reads_none)
next
  case (Cons a vs)
  have "reads_inside_set (bf_restrict a t f) (set vs)" for t 
    by (metis Cons.prems member_remove reads_inside_set_restrict reads_inside_set_subset removeAll.simps(2) remove_code(1) subset_code(1))
  from Cons.IH[OF this]
  show ?case by (simp add: bf_restrict_def fun_upd_idem)
qed

lemma mk_ifex_tt_all_bdts: "reads_inside_set f (set vs) \<Longrightarrow> mk_ifex_tt f vs \<in> all_bdts f (set vs)"
  unfolding all_bdts_def by simp

definition "bf_evasive_on_alt f vs \<equiv> (let abh = height ` all_bdts f vs; c = card vs in c \<in> abh \<and> (\<forall>h \<in> abh. c \<le> h))"
(* Using Min makes things weird... *)
find_theorems "Min (_ :: nat set)" (* like, why are there so few facts on it? *)

fun ifex_vartrail where
"ifex_vartrail (IF v t e) a = v # ifex_vartrail (if a v then t else e) a" |
"ifex_vartrail _ a = []"
lemma ifex_vartrail_length_height: "length (ifex_vartrail f as) \<le> height f"
  by(induction f) auto
lemma ifex_vartrail: "p \<notin> set (ifex_vartrail f as) \<Longrightarrow> val_ifex f (as(p:=t)) = val_ifex f as"
  by(induction f) auto
lemma ifex_vartrail_subset: "set (ifex_vartrail f as) \<subseteq> ifex_var_set f"
  by(induction f) auto

lemma bf_evasive_alt:
  assumes fin: "finite vs" 
  assumes rin: "reads_inside_set f vs"
  shows "bf_evasive_on f vs \<longleftrightarrow> bf_evasive_on_alt f vs"
proof
  assume "bf_evasive_on f vs"
  then obtain a where a: "\<And>p. p \<in> vs \<Longrightarrow> f a \<noteq> f (a(p := \<not>a p))" 
    unfolding bf_evasive_on_def by blast

  obtain lvs where lvs: "set lvs = vs" "length lvs = card vs"
    by (metis fin finite_sorted_distinct_unique length_remdups_card_conv set_remdups)
  with mk_ifex_tt_all_bdts rin have "height (mk_ifex_tt f lvs) \<in> {height t |t. t \<in> all_bdts f vs}"
    by blast
  hence isin: "card vs \<in> height ` all_bdts f vs" 
    by(auto simp add: image_iff lvs)

  have ismin: "\<forall>t \<in> all_bdts f vs. card vs \<le> height t"
  proof(rule ccontr)
    assume "\<not> (\<forall>t\<in>all_bdts f vs. card vs \<le> height t)"
    then obtain t where t: "t \<in> all_bdts f vs" "height t < card vs" by force
    hence "length (ifex_vartrail t a) < card vs"
      by (meson ifex_vartrail_length_height le_trans less_le_not_le)
    then obtain p where p: "p \<notin> set (ifex_vartrail t a)" "p \<in> vs"
      by (meson List.finite_set card_length card_mono le_trans linorder_not_le subsetI)
    with a have up: "f a \<noteq> f (a(p := \<not>a p))" by presburger
    have "val_ifex t = f" using t unfolding all_bdts_def by simp
    with ifex_vartrail[OF p(1)] up
    show False by simp
  qed
    
  from isin ismin show "bf_evasive_on_alt f vs" 
    unfolding bf_evasive_on_alt_def Let_def
    by simp
next
  assume rhs: "bf_evasive_on_alt f vs"
  from rhs have ismin: "\<forall>t \<in> all_bdts f vs. card vs \<le> height t" unfolding bf_evasive_on_alt_def by simp
  from rhs have isin: "\<exists>x\<in>all_bdts f vs. card vs = height x" unfolding bf_evasive_on_alt_def by auto
  show "bf_evasive_on f vs"
  oops
  


(*definition evasive :: "nat => ((nat => bool) => bool) => bool"
  where "evasive n f \<equiv> (height (mk_ifex f [0..<n])) = n"*)

(*corollary "evasive 4 boolfunc_threshold_2_3" by eval*)

lemma "evasive 4 (bool_fun_threshold_2_3)"
  by eval

lemma "evasive 4 (boolean_functions.Alexander_dual bool_fun_threshold_2_3)"
  by eval

(*lemma "\<not> evasive 4 proj_2" by eval*)

lemma "\<not> evasive 4 proj_2_bool" by eval

(*lemma "\<not> evasive 4 proj_2_n3" by eval*)

lemma "\<not> evasive 4 proj_2_n3_bool" by eval

lemma "\<not> evasive 4 bf_True" by eval

lemma "\<not> evasive 4 bf_False" by eval

section\<open>The @{term boolean_functions.Alexander_dual} and @{typ "'a ifex"}\<close>

context boolean_functions
begin

primrec ifex_alexander_dual where
"ifex_alexander_dual Falseif = Trueif" |
"ifex_alexander_dual Trueif = Falseif" |
"ifex_alexander_dual (IF i t e) = (IF i (ifex_alexander_dual e) (ifex_alexander_dual t))"

lemma ifex_alexander_dual: "ifex_alexander_dual (mk_ifex (vec_to_boolfunc n f) [0..<n])
  = mk_ifex (vec_to_boolfunc n (Alexander_dual f)) [0..<n]"
proof -

  have ifex_alexander_dual_varset: "ifex_var_set (ifex_alexander_dual f2) = ifex_var_set f2" for f2
    by(induction f2) auto

  have ifex_alexander_dual_inj: "ifex_alexander_dual f2 = ifex_alexander_dual f1 \<Longrightarrow> f1 = f2" for f1 f2
    apply(induction f1 arbitrary: f2)
    subgoal for f2 by(cases f2; simp)
    subgoal for f2 by(cases f2; simp)
    subgoal for i t e f2 by(cases f2; simp)
    done
    
  have ifex_alexander_dual_ro: "ro_ifex f \<Longrightarrow> ro_ifex (ifex_alexander_dual f)" for f
    apply(induction f; (simp; fail)?)
    apply(simp split: ifex.splits add: ifex_alexander_dual_varset)
    apply(blast dest: ifex_alexander_dual_inj)
    done

  have val_ifex_alexander_dual: "val_ifex (ifex_alexander_dual f) assmt
    = (\<not> val_ifex f (\<lambda>i. \<not>assmt i))" for f assmt
    by(induction f; simp)

  have ifex_alexander_dual: "reads_inside_set f (set vs) \<Longrightarrow> ifex_alexander_dual (mk_ifex f vs)
    = mk_ifex (\<lambda>asmmt. \<not>f (\<lambda>i. \<not>asmmt i)) vs" for f vs
    apply(rule ro_ifex_unique)
      subgoal using ifex_alexander_dual_ro mk_ifex_ro by blast
     subgoal using mk_ifex_ro by blast
     apply(subst val_ifex_mk_ifex_equal)
      apply(simp add: reads_inside_set_def; fail)
     apply(subst val_ifex_alexander_dual)
     apply(subst val_ifex_mk_ifex_equal)
     subgoal .
     ..

   have foo: "(\<lambda>assmt. \<not> f (vec n (\<lambda>i. \<not> assmt i))) = (\<lambda>assmt. \<not> f (vec n (\<lambda>na. \<not> vec n assmt $ na)))"
     by (rule ext; smt (verit, ccfv_threshold) dim_vec eq_vecI index_vec)
  
  show ?thesis
    apply(subst ifex_alexander_dual)
     (* hgn, reads_inside_set_boolean_function is phrased just a little bit wrong for this *)
     thm reads_inside_set_boolean_function
     subgoal by(simp add: vec_to_boolfunc_def reads_inside_set_def mk_vec_def vec_def)
     subgoal by(simp add: vec_to_boolfunc_def Alexander_dual_def not_def foo)
    done
qed

end

end