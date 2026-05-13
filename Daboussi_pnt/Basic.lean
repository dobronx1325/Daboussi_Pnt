import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Order.Interval.Finset.Defs
import Init
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Int.Cast.Lemmas
namespace Daboussi_pnt.Basic
-- 双曲方法核心引理（形式化版本）

--def NonnegRealsGe1 : Type := {x : ℝ // 1 ≤ x}
--instance : Coe NonnegRealsGe1 ℝ where coe x := x.val
--noncomputable def summatory (f : ℕ → ℝ) (x : Real) : ℝ := (Finset.Ioc 0 ((⌊x⌋₊))).sum (fun n => (f n : ℝ))
--我认为定义出来一个前n项和是有必要的，因为这会让式子简洁很多，虽然我们也可以直接在式子里写成sum的形式，但是这样会让式子变得非常冗长。
--noncomputable def G (g : ℕ → ℝ) (x : NonnegRealsGe1) : ℝ := (Finset.Icc 1 ((⌊x.val⌋₊))).sum (fun n => (g n : ℝ))
--lemma dirichlet_hyperbola_method {f g : Nat → ℝ} {x y : ℝ } {F G : ℝ → ℝ}(hy:  1 ≤ y ∧ y ≤ x):
--(F = fun x : Real => summatory f x) ∧  (G = fun x : Real => summatory g x) →
-- summatory ( LSeries.convolution f  g) x = (Finset.Ioc 0 ((⌊y⌋₊))).sum (fun n =>  g n  * F (x/n)) +
-- (Finset.Ioc 0 ((⌊x/y⌋₊))).sum (fun m => f m * G (x/m))- F (x/y) * G y:= by
-- sorry
--若后面这可以行得通，就会将后面的求和换成前面的形式，现在为了稳定期间，先按照原始的模式去定义
-- have h1 :∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (toArithmeticFunction f) n * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / n), (toArithmeticFunction g) m =
--  ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / n), (toArithmeticFunction g) m +
--  ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (toArithmeticFunction f) n * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / n), (toArithmeticFunction g) m :=by
--  refine
--    Eq.symm
--      (Finset.sum_Ioc_consecutive
--        (fun i ↦
--          (toArithmeticFunction f) i * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / i), (toArithmeticFunction g) m)
--        ?_ ?_)
--  exact Nat.zero_le ⌊y⌋₊
--   refine Nat.floor_le_floor ?_
--  exact hy.2
-- rw[h1]
open Finset

lemma ArithmeticFunction.sum_Ioc_mul_eq_sum_sum_tran_order [ Semiring R] (f g : ArithmeticFunction R)  (N : ℕ) :
    ∑ n ∈ Ioc 0  N, g n * ∑ m ∈ Ioc 0 (N / n), f m  = ∑ n ∈ Ioc 0 N, f n * ∑ m ∈ Ioc 0 (N / n), g m := by
    sorry
--lemma _root_.Fintype.sum_mul_sum_rel [Semiring R] [Finset ι] [Finset κ] (f : ι → R) (g : κ → R) :
--    ∑ i, (f i * ∑ j, g j) = ∑ i, ∑ j, f i * g j := Finset.sum_congr rfl (by simp [Finset.mul_sum])

lemma sum_mul_sum_rel [Semiring R] (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    ∑ i ∈ s, (f i * ∑ j ∈ t, g j) = ∑ i ∈ s, ∑ j ∈ t, f i * g j := Finset.sum_congr rfl (by simp [Finset.mul_sum])
lemma sum_mul_sum_rel_dep [Semiring R] (s : Finset ι) (t : ι → Finset κ) (f : ι → R) (g : κ → R) :
    ∑ i ∈ s, (f i * ∑ j ∈ t i, g j) = ∑ i ∈ s, ∑ j ∈ t i, f i * g j :=
  Finset.sum_congr rfl fun i hi => by rw [Finset.mul_sum]
lemma Finset.sum_product_dep [AddCommMonoid β] (s : Finset ι) (t : ι → Finset κ) (f : ι → κ → β) :
    ∑ i ∈ s, ∑ j ∈ t i, f i j = ∑ p ∈ s.sigma t, f p.1 p.2 :=
  Finset.sum_sigma' s t f

lemma dirichlet_hyperbola_method {f g : Nat → ℝ} {x y : ℝ } (hy:  1 ≤ y ∧ y ≤ x):
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ((LSeries.convolution f  g) n : ℝ)  =
    (∑ n ∈ Ioc 0 ⌊y⌋₊, toArithmeticFunction f n * ∑ m ∈ Ioc 0 (⌊x⌋₊ / n), (toArithmeticFunction g m : ℝ)) +
    (∑ m ∈ Ioc 0 ⌊x/y⌋₊, toArithmeticFunction g m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f n : ℝ)) -
    (∑ n ∈ Ioc 0 ⌊x/y⌋₊, (toArithmeticFunction g n : ℝ)) * (∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f n : ℝ)) := by
  --证明策略：首先通过卷积定义将左边的求和展开成双层求和的形式，然后利用迪利克雷卷积换序，改变求和方式，然后通过分割求和区间，将双层求和转化成两部分求和的形式，
  --第一部分与右侧的第一部分相等，第二部分通过换序，能化成右侧部分的形式，然后把中间区间写成两区间的差值就完成（这里我们是把右侧大的区间化成了小区间和中间区间，相减做的）。
  rw [LSeries.convolution] --展开卷积
  rw[ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]  --把对角求和转化成水平或竖直求和，把卷积转化成双层求和的形式，方便和后面做对应（因为卷积是对称的，所以这个定理还可以用于水平求和和竖直求和的换序）
  rw[ Eq.symm (Finset.sum_Ioc_consecutive (fun i ↦ (toArithmeticFunction f) i * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / i), (toArithmeticFunction g) m) (Nat.zero_le ⌊y⌋₊) (Nat.floor_le_floor hy.2))]--分割求和区间，
  --但要注意，这里的分割方式是直接对外蹭进行分割，不用进入里面，所以直接用这个定理就好，但是后面有一个是对内层求和进行分割，所以就要进入里面去分割了，为什么要去里面呢？因为内层的索引是依赖于外层索引的，所以要进入里面去分割，才能正确地分割出区间来。
  --不然直接分割，会导致lean4无法识别内层求和的索引
  conv_rhs => rw [sub_eq_add_neg,  add_assoc]
  apply Mathlib.Tactic.LinearCombination.add_eq_eq --我想划掉两侧第一个项，所以要用这个定理，就把目标分解成证明两侧的第一项相等和其余部分相等，然后因为右侧是+-，并且加法是左结合，所以要用到上面这个定理
  linarith
  simp --去掉函数的fun结构

  let f_trunc (n : ℕ) := if n > ⌊y⌋₊ then f n else 0

  calc
    _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, (toArithmeticFunction f_trunc * toArithmeticFunction g) n := by
      rw[ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
      rw[ Eq.symm (Finset.sum_Ioc_consecutive (fun i ↦ (toArithmeticFunction f_trunc) i * ∑ m ∈ Ioc 0 (⌊x⌋₊ / i), (toArithmeticFunction g) m) (Nat.zero_le ⌊y⌋₊) (Nat.floor_le_floor hy.2))]
      simp
      have hzero : ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f_trunc) n *  ∑ m ∈ Ioc 0 (⌊x⌋₊ / n), (toArithmeticFunction g) m = 0 := by
       apply Finset.sum_eq_zero
       intro i hi
       have hi_mem := Finset.mem_Ioc.mp hi
       have hi_pos : 0 < i := hi_mem.1
       have hi_le : i ≤ ⌊y⌋₊ := hi_mem.2

       --have hzero1 : (toArithmeticFunction fun n ↦ if n > ⌊y⌋₊ then f n else 0) i = 0 := by
       -- split_ifs with h
       simp [toArithmeticFunction, hi_pos.ne']
       dsimp [f_trunc]
       split_ifs with h
       · exfalso; linarith
       ·simp
      rw [hzero]
      simp
      apply Finset.sum_congr
      simp
      intro x_1 hx_1
      have hx_mem := Finset.mem_Ioc.mp hx_1
      have hx_pos : ⌊y⌋₊ < x_1 := hx_mem.1
      have hx_le : x_1 ≤ ⌊x⌋₊ := hx_mem.2
      simp [toArithmeticFunction]
      dsimp [f_trunc]
      split_ifs with h
      · linarith
      ·simp
--6.了解exfalso这个策略干的是什么事情？
--8.每个证明都有很多方式，怎么样才选择最优的一个方式？要看库里有什么？最开始要尽可能地给出多的证明方式？（去zulip上提问）需不需要去了解自己操作对象的一些特征？
    _ = ∑ m ∈ Ioc 0 ⌊x⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f_trunc) n := by
    -- rw[ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
     --rw[ Eq.symm (Finset.sum_Ioc_consecutive (fun i ↦ (toArithmeticFunction g) i * ∑ m ∈ Ioc 0 (⌊x⌋₊ / i), (toArithmeticFunction f_trunc) m) (Nat.zero_le ⌊x/y⌋₊) (Nat.floor_le_floor (Nat.div_le_of_le_mul h
     conv_lhs => rw[Finset.sum_congr rfl (fun n hn => by  rw [mul_comm] )]
     rw[ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  have h'': ⌊x / y⌋₊  ≤ ⌊x⌋₊ := by
    rcases hy with ⟨hy1, hy2⟩
    have hx_nonneg : 0 ≤ x := by linarith
    refine Nat.floor_le_floor (div_le_self hx_nonneg hy1)
  rw[ Eq.symm (Finset.sum_Ioc_consecutive (fun i ↦ (toArithmeticFunction g) i * ∑ m ∈ Ioc 0 (⌊x⌋₊ / i), (toArithmeticFunction f_trunc) m) (Nat.zero_le ⌊x/y⌋₊) h'')]
  simp
  have hx1zero :∑ x_1 ∈ Ioc ⌊x / y⌋₊ ⌊x⌋₊,(toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m =0 :=by
    apply Finset.sum_eq_zero
    intro x1 hx1
    rcases Finset.mem_Ioc.mp hx1 with ⟨hx1_low, hx1_high⟩
    rcases hy with ⟨hy1, hy2⟩
    have hy_pos_real : (0 : ℝ) < y := by linarith
    have hx_nonneg_real : (0 : ℝ) ≤ x := by linarith
    have hx1_pos : 0 < x1 := by
      have h0_le_floor : (0 : ℕ) ≤ ⌊x / y⌋₊ := Nat.zero_le _
      exact Nat.lt_of_le_of_lt h0_le_floor hx1_low
    have inner_zero : ∑ m ∈ Ioc 0 (⌊x⌋₊ / x1), (toArithmeticFunction f_trunc) m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
      have hm_le_div : m ≤ ⌊x⌋₊ / x1 := hm_high
      have hm_le_yfloor : m ≤ ⌊y⌋₊ := by
        by_contra! H
        have h_mul_le : m * x1 ≤ ⌊x⌋₊ :=
          (Nat.le_div_iff_mul_le hx1_pos).mp hm_le_div
        have hy_floor_succ_le_m : (⌊y⌋₊ + 1 : ℕ) ≤ m := Nat.succ_le_of_lt H
        have h_left : ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) ≤ x := by
          calc
            ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) = ((⌊y⌋₊ + 1 : ℕ) : ℝ) * (x1 : ℝ) := by simp
            _ ≤ (m : ℝ) * (x1 : ℝ) :=
              mul_le_mul_of_nonneg_right (mod_cast hy_floor_succ_le_m) (by exact mod_cast (Nat.zero_le x1))
            _ = ((m * x1 : ℕ) : ℝ) := by simp
            _ ≤ (⌊x⌋₊ : ℝ) := mod_cast h_mul_le
            _ ≤ x := Nat.floor_le hx_nonneg_real
        have h_right : x < ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) := by
          have hx1_gt_div : (x / y : ℝ) < (x1 : ℝ) := by
            have h_floor_succ_le_x1 : (⌊x / y⌋₊ : ℝ) + 1 ≤ (x1 : ℝ) := by
              have h_nat : (⌊x / y⌋₊ : ℕ) + 1 ≤ x1 := Nat.succ_le_of_lt hx1_low
              exact mod_cast h_nat
            have h_div_lt_floor_succ : (x / y : ℝ) < (⌊x / y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
            linarith
          have hy_lt_succ : (y : ℝ) < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
          calc
            (x : ℝ) < (x1 : ℝ) * y := (div_lt_iff₀ hy_pos_real).mp hx1_gt_div
            _ < (x1 : ℝ) * ((⌊y⌋₊ : ℝ) + 1) :=
              mul_lt_mul_of_pos_left hy_lt_succ (by exact mod_cast hx1_pos)
            _ = ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) := by
              push_cast
              ring
        linarith
      have h_trunc_zero : (toArithmeticFunction f_trunc) m = 0 := by
        simp [toArithmeticFunction, hm_low.ne', f_trunc]
        intro h_not
        exfalso; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_not hm_le_yfloor)
      simp [h_trunc_zero]
    simp [inner_zero]
  rw [hx1zero]
  simp
  have h123 :∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m =
  ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 ⌊y⌋₊ , (toArithmeticFunction f_trunc) m +
  ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m :=by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x1 hx1
    rcases Finset.mem_Ioc.mp hx1 with ⟨hx1_low, hx1_high⟩
    set d := ⌊x⌋₊ / x1 with hd
    by_cases h : ⌊y⌋₊ ≤ d
    · let F : ℕ → ℝ := fun m => (toArithmeticFunction f_trunc) m
      have hsplit := (Finset.sum_Ioc_consecutive F (Nat.zero_le _) h).symm
      rw [hsplit, mul_add]
    · have h_lt : d < ⌊y⌋₊ := Nat.lt_of_not_ge h
      have inner_LHS_zero : ∑ m ∈ Ioc 0 d, (toArithmeticFunction f_trunc) m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
        have hm_lt_yfloor : m < ⌊y⌋₊ := Nat.lt_of_le_of_lt hm_high h_lt
        have hm_not_gt : ¬ (⌊y⌋₊ < m) := Nat.not_lt.mpr (Nat.le_of_lt hm_lt_yfloor)
        simp [toArithmeticFunction, hm_low.ne', f_trunc, hm_not_gt]
      have inner_RHS1_zero : ∑ m ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f_trunc) m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
        have hm_not_gt : ¬ (⌊y⌋₊ < m) := Nat.not_lt.mpr hm_high
        simp [toArithmeticFunction, hm_low.ne', f_trunc, hm_not_gt]
      have inner_RHS2_zero : ∑ m ∈ Ioc ⌊y⌋₊ d, (toArithmeticFunction f_trunc) m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
        exfalso
        have hm_lt_yfloor : m < ⌊y⌋₊ := Nat.lt_of_le_of_lt hm_high h_lt
        exact Nat.lt_irrefl _ (Nat.lt_trans hm_low hm_lt_yfloor)
      simp [inner_LHS_zero, inner_RHS1_zero, inner_RHS2_zero]
  rw[h123]
  have h123' : ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f_trunc) m =0 := by
    have inner_zero : ∑ m ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f_trunc) m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
      have hm_not_gt : ¬ (⌊y⌋₊ < m) := Nat.not_lt.mpr hm_high
      simp [toArithmeticFunction, hm_low.ne', f_trunc, hm_not_gt]
    simp [inner_zero]
  rw[h123']
  simp
  have h123'' : ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
    - ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
    = ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m := by
    rcases hy with ⟨hy1, hy2⟩
    have hy_pos_real : (0 : ℝ) < y := by linarith
    have hx_nonneg_real : (0 : ℝ) ≤ x := by linarith
    have h_split_inner (m : ℕ) (hm_pos : 0 < m) (hm_le : m ≤ ⌊x / y⌋₊) :
        ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
        = ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n
        + ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n := by
      have h_ineq : ⌊y⌋₊ ≤ ⌊x⌋₊ / m := by
        rw [Nat.le_div_iff_mul_le hm_pos]
        by_contra! H
        have h_real : ((⌊y⌋₊ * m : ℕ) : ℝ) ≤ x := by
          calc
            ((⌊y⌋₊ * m : ℕ) : ℝ) = (⌊y⌋₊ : ℝ) * (m : ℝ) := by simp
            _ ≤ (y : ℝ) * (m : ℝ) := by
              gcongr; exact Nat.floor_le (by linarith : 0 ≤ y)
            _ ≤ (y : ℝ) * (⌊x / y⌋₊ : ℝ) :=
              mul_le_mul_of_nonneg_left (mod_cast hm_le) (by linarith [hy1] : 0 ≤ (y : ℝ))
            _ ≤ (y : ℝ) * (x / y : ℝ) := by
              gcongr; exact Nat.floor_le (div_nonneg hx_nonneg_real (by linarith))
            _ = x := by field_simp [ne_of_gt hy_pos_real]
        have hx_lt_succ : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        have h_succ_real : (⌊x⌋₊ : ℝ) + 1 ≤ ((⌊y⌋₊ * m : ℕ) : ℝ) := by
          have h_nat : (⌊x⌋₊ : ℕ) + 1 ≤ ⌊y⌋₊ * m := Nat.succ_le_of_lt H
          exact mod_cast h_nat
        linarith
      rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => (toArithmeticFunction f) n) (Nat.zero_le _) h_ineq]
    have h_term2_split :
        ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
        = ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
        + ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n := by
      calc
        ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
        = ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m
            * (∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n
              + ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
          rw [h_split_inner m hm_low hm_high]
        _ = ∑ m ∈ Ioc 0 ⌊x / y⌋₊,
            ((toArithmeticFunction g) m * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n
            + (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          refine Finset.sum_congr rfl (fun m hm => by rw [mul_add])
        _ = (∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
          + (∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          rw [Finset.sum_add_distrib]
        _ = ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
          + (∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          simp [Finset.sum_mul]
    calc
      ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
          - ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
      = (((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
          + ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n)
          - ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n) := by
        rw [h_term2_split]
      _ = ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n := by
        abel
      _ = ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m := by
        refine Finset.sum_congr rfl (fun x1 _ => ?_)
        have h_inner_eq : ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x1), (toArithmeticFunction f) n
            = ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x1), (toArithmeticFunction f_trunc) n := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rcases Finset.mem_Ioc.mp hn with ⟨hn_low, hn_high⟩
          have hn_pos : n ≠ 0 := by omega
          have hn_gt_yfloor : ⌊y⌋₊ < n := hn_low
          simp [toArithmeticFunction, f_trunc, hn_pos, hn_gt_yfloor]
        rw [h_inner_eq]
  rw[ ← sub_eq_add_neg]
  rw[h123'']
--上面的内容，我主要完成了把原本的一个双重求和化成了一个卷积的形式，这个卷积中的一个函数是截断函数，然后化成卷积，就可以用卷积的换序定理来换序了
--然后后面的内容就是把卷积换序，然后展开，然后一层层去掉截断函数的壳子
--这个过程要不断删掉等于0的部分，这本质上是这样的：两（多）个finset的求和的乘积，如果在某一区间上某个函数值为0，则可以把这个区间去掉。
--还有一个就是，外层求和一致，函数一致，内层求和区间不一致，但有共同起点,就可以实现两个求和乘积的差值是外层求和一致，内层求和首尾相接的这种特点
--
--
--
--

 --  abel_nf
  --这里是怎么穿过外层求和符号的？rw [← Finset.sum_mul]有什么作用？abel_nf是什么意思？我这里想实现的就是很简单的a+b-a=b的效果，
  --但是面对这种形式一致，但是内容格式古怪的，用abel有效果是吗？这是怎么实现的？


-- 定义 von Mangoldt 函数的前缀和 ψ(x)
--noncomputable def psi (x : NonnegRealsGe1) : ℝ :=   (Finset.Icc 1 ((⌊x.val⌋₊))).sum (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))

-- 定义 Möbius 函数的前缀和 M(x)
--noncomputable def M (x : NonnegRealsGe1) : ℝ := (Finset.Icc 1 ((⌊x.val⌋₊))).sum (fun n => (ArithmeticFunction.moebius n : ℝ))

-- 核心命题：M(x) = o(x) 蕴含 ψ(x) ~ x (x → ∞)
-- 1. 对数算术函数：n>0时为log(n)，n=0时为0（满足ArithmeticFunction的f(0)=0要求）
--noncomputable def logArith : ArithmeticFunction ℝ :=
--  ⟨fun n ↦ if n = 0 then 0 else Real.log (n : ℝ), by simp⟩
--我们一般不研究这个函数，我们直接去研究他的和函数就是切比雪夫第二函数--noncomputable def Chebyshev.theta，
--如果需要这个定义，我们可以在后续章节中引入。


-- 2. 常数函数1：恒为1的算术函数（记为1）
--noncomputable def oneArith : ArithmeticFunction ℝ := 1    这就是zeta函数--def ArithmeticFunction.zeta
-- 3. 卷积单位元ArithmeticFunction.one：满足 f * one = f 的算术函数（记为1）
-- 4. 对莫比乌斯函数的值域进行类型提升，使其成为实数值函数（记为moebiusReal）
noncomputable def M (x : Real) : ℝ := (Finset.Ioc 0 ((⌊x⌋₊))).sum (fun n => (ArithmeticFunction.moebius n : ℝ))
--def moebiusReal : ArithmeticFunction ℝ := ArithmeticFunction.moebius (Int.cast : ℤ → ℝ)
--def moebiusReal : ℕ → ℝ := fun n => (Nat.moebius n : ℝ)
--def moebiusRealArith : ArithmeticFunction ℝ :=
--  (ArithmeticFunction.moebius : ArithmeticFunction ℤ).map (algebraMap ℤ ℝ)     -- 或直接用 (fun (x : ℤ) => (x : ℝ))
--    (by simp)            -- 证明 (0 : ℤ) 被映射到 (0 : ℝ)
--def moebiusRealArith' : ArithmeticFunction ℝ :=
--  ⟨fun n => (ArithmeticFunction.moebius n : ℝ), by simp⟩，看前面那个求和能不能通过，若能通过，我们下面就会做出一个相应的修改，但现在仍用
--(fun x : Real => Chebyshev.psi x) =o[Filter.atTop] (fun x : Real => (x : ℝ))
--def sigma (k : ℕ) : ArithmeticFunction ℕ :=fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩
theorem daboussi_implication :
  (fun x : ℝ  => M x) =o[Filter.atTop] (fun x :  Real => (x : ℝ)) →
  Asymptotics.IsEquivalent Filter.atTop (fun x : ℝ => Chebyshev.psi x)  (fun x : ℝ => x) := by
 intro hM
 sorry

theorem daboussi_pnt : True := by trivial

end Daboussi_pnt.Basic
