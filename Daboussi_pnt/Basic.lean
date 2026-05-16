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
import Mathlib.Algebra.Order.Floor.Defs
import  Mathlib.Order.Filter.AtTopBot.Defs
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
import  Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.AbelSummation

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
open scoped ArithmeticFunction.zeta
open scoped ArithmeticFunction.sigma
open Finset
open ArithmeticFunction
open Finset Nat
open scoped ArithmeticFunction.zeta
open scoped sigma
open Filter

syntax "simp_sum_zero" : tactic

macro_rules
| `(tactic| simp_sum_zero) =>
  `(tactic|
    repeat (
      simp (config := { singlePass := true }) only [Finset.sum_const_zero]


    )
  )
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
/-- harmonic ⌊x⌋₊ - log x - γ = O(1/x) as x → ∞, via Abel summation / sandwich bounds. -/
local notation "γ" => Real.eulerMascheroniConstant
lemma harmonic_sum_abel : (fun (x : ℝ) => (harmonic ⌊x⌋₊ : ℝ) - Real.log x - γ) =O[Filter.atTop] (fun (x : ℝ) => 1/x) := by
  rw [Asymptotics.isBigO_iff']
  refine ⟨2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith
  set n := ⌊x⌋₊ with hn_def
  have hn_nonzero : n ≠ 0 := by
    have hpos' : 0 < n := Nat.floor_pos.mpr (by linarith : 1 ≤ x)
    exact hpos'.ne'
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn_nonzero

  have h_sandwich_upper : Real.eulerMascheroniConstant < (harmonic n : ℝ) - Real.log (n : ℝ) := by
    simpa [Real.eulerMascheroniSeq', hn_nonzero] using
      Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have h_sandwich_lower : (harmonic n : ℝ) - Real.log ((n : ℝ) + 1) < Real.eulerMascheroniConstant := by
    simpa [Real.eulerMascheroniSeq] using Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n

  have h_floor_le : (n : ℝ) ≤ x := mod_cast Nat.floor_le (by linarith : 0 ≤ x)
  have h_lt_floor_add_one : x < (n : ℝ) + 1 := mod_cast Nat.lt_floor_add_one x
  have h_log_floor_le : Real.log (n : ℝ) ≤ Real.log x :=
    Real.log_le_log hnpos h_floor_le
  have h_log_le_floor_add_one : Real.log x ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hxpos (by linarith)

  have h_lower : (harmonic n : ℝ) - Real.log ((n : ℝ) + 1) - Real.eulerMascheroniConstant
      ≤ (harmonic n : ℝ) - Real.log x - Real.eulerMascheroniConstant := by linarith
  have h_upper : (harmonic n : ℝ) - Real.log x - Real.eulerMascheroniConstant
      ≤ (harmonic n : ℝ) - Real.log (n : ℝ) - Real.eulerMascheroniConstant := by linarith

  have h_log_diff_bound : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    calc
      Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) = Real.log (((n : ℝ) + 1) / (n : ℝ)) := by
        rw [Real.log_div (by positivity : (n : ℝ) + 1 ≠ 0) (by positivity : (n : ℝ) ≠ 0)]
      _ = Real.log (1 + 1 / (n : ℝ)) := by
        field_simp [hnpos.ne']
      _ ≤ (1 + 1 / (n : ℝ)) - 1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (n : ℝ))
      _ = 1 / (n : ℝ) := by ring

  have h_upper_bound : (harmonic n : ℝ) - Real.log (n : ℝ) - Real.eulerMascheroniConstant ≤ 1 / (n : ℝ) := by
    linarith
  have h_lower_bound : -(1 / (n : ℝ)) ≤ (harmonic n : ℝ) - Real.log ((n : ℝ) + 1) - Real.eulerMascheroniConstant := by
    linarith

  have h_bound : -(1 / (n : ℝ)) ≤ (harmonic n : ℝ) - Real.log x - Real.eulerMascheroniConstant ∧
      (harmonic n : ℝ) - Real.log x - Real.eulerMascheroniConstant ≤ 1 / (n : ℝ) := by
    constructor <;> linarith

  have h_abs_bound : |(harmonic n : ℝ) - Real.log x - Real.eulerMascheroniConstant| ≤ 1 / (n : ℝ) := by
    rcases h_bound with ⟨hl, hr⟩
    rw [abs_le]
    exact ⟨hl, hr⟩

  have h_n_ge_x_div_two : x / 2 ≤ (n : ℝ) := by
    nlinarith

  have h_one_div_n_le_two_div_x : 1 / (n : ℝ) ≤ 2 * (1 / x) := by
    calc
      1 / (n : ℝ) ≤ 1 / (x / 2) := by
        refine (one_div_le_one_div ?_ (by linarith : 0 < x / 2)).mpr h_n_ge_x_div_two
        exact hnpos
      _ = 2 / x := by ring
      _ = 2 * (1 / x) := by ring

  have h_calc : |(harmonic n : ℝ) - Real.log x - Real.eulerMascheroniConstant| ≤ 2 * |1 / x| :=
    calc
      |(harmonic n : ℝ) - Real.log x - Real.eulerMascheroniConstant| ≤ 1 / (n : ℝ) := h_abs_bound
      _ ≤ 2 * (1 / x) := h_one_div_n_le_two_div_x
      _ = 2 * |1 / x| := by rw [abs_of_pos (by positivity : 0 < 1 / x)]
  simpa [hn_def] using h_calc
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
lemma dirichlet_hyperbola_method' {f g : Nat → ℝ} {x y : ℝ } (hy:  1 ≤ y ∧ y ≤ x):
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ((LSeries.convolution f  g) n : ℝ)  =
    (∑ n ∈ Ioc 0 ⌊y⌋₊, toArithmeticFunction f n * ∑ m ∈ Ioc 0 (⌊x / n⌋₊), (toArithmeticFunction g m : ℝ)) +
    (∑ m ∈ Ioc 0 ⌊x/y⌋₊, toArithmeticFunction g m * ∑ n ∈ Ioc 0 (⌊x / m⌋₊), (toArithmeticFunction f n : ℝ)) -
    (∑ n ∈ Ioc 0 ⌊x/y⌋₊, (toArithmeticFunction g n : ℝ)) * (∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f n : ℝ)) := by
  have hy0 := hy
  rcases hy with ⟨hy1, hy2⟩
  have hx_nonneg : 0 ≤ x := by linarith
  have h1 (i : ℕ) : ⌊x⌋₊ / i = ⌊x / (i : ℝ)⌋₊ := by
    set n := ⌊x⌋₊ with hn
    by_cases hi : i = 0
    · subst hi; simp
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi
      have hi_pos_r : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
      have hn_le_x : (n : ℝ) ≤ x := mod_cast Nat.floor_le hx_nonneg
      have hx_lt_n1 : x < (n : ℝ) + 1 := mod_cast Nat.lt_floor_add_one x
      have hx_div_nonneg : 0 ≤ x / (i : ℝ) := div_nonneg hx_nonneg (by exact_mod_cast hi_pos.le)
      rw [eq_comm]
      apply (Nat.floor_eq_iff hx_div_nonneg).mpr
      constructor
      · have h_mul_nat : (n / i : ℕ) * i ≤ n := by
          have h := Nat.div_add_mod n i
          simpa [h, mul_comm] using Nat.le_add_right (i * (n / i)) (n % i)
        calc
          ((n / i : ℕ) : ℝ) = (((n / i : ℕ) : ℝ) * (i : ℝ)) / (i : ℝ) := by field_simp [hi_pos_r.ne']
          _ ≤ (n : ℝ) / (i : ℝ) := by gcongr; exact mod_cast h_mul_nat
          _ ≤ x / (i : ℝ) := by gcongr
      · have h_n1_le_nat : n + 1 ≤ (n / i + 1) * i := by
          have h := Nat.div_add_mod n i
          have h_succ_le : n % i + 1 ≤ i := Nat.succ_le_of_lt (Nat.mod_lt n hi_pos)
          calc
            n + 1 = (i * (n / i) + n % i) + 1 := by rw [h]
            _ = i * (n / i) + (n % i + 1) := by ring
            _ ≤ i * (n / i) + i := Nat.add_le_add_left h_succ_le _
            _ = i * (n / i + 1) := by ring
            _ = (n / i + 1) * i := by ring
        calc
          x / (i : ℝ) < ((n : ℝ) + 1) / (i : ℝ) := by gcongr
          _ ≤ (((n / i + 1 : ℕ) : ℝ) * (i : ℝ)) / (i : ℝ) := by
            gcongr; exact mod_cast h_n1_le_nat
          _ = ((n / i : ℕ) : ℝ) + 1 := by field_simp [hi_pos_r.ne']; push_cast; ring
  simpa [h1] using dirichlet_hyperbola_method hy0
lemma dirichlet_hyperbola_method'' [Semiring R][PartialOrder R] [FloorSemiring R] {f g : Nat → R} {x y : R } (hy:  1 ≤ y ∧ y ≤ x):
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ((LSeries.convolution f  g) n : R)  =
    (∑ n ∈ Ioc 0 ⌊y⌋₊, toArithmeticFunction f n * ∑ m ∈ Ioc 0 (⌊x / n⌋₊), (toArithmeticFunction g m : R)) +
    (∑ m ∈ Ioc 0 ⌊x/y⌋₊, toArithmeticFunction g m * ∑ n ∈ Ioc 0 (⌊x / m⌋₊), (toArithmeticFunction f n : R)) -
    (∑ n ∈ Ioc 0 ⌊x/y⌋₊, (toArithmeticFunction g n : R)) * (∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f n : R)) := by sorry
lemma dirichlet_hyperbola_method''' {f g : Nat → Nat} {x y : Real } (hy:  1 ≤ y ∧ y ≤ x):
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ((LSeries.convolution f  g) n : Nat)  =
    (∑ n ∈ Ioc 0 ⌊y⌋₊, toArithmeticFunction f n * ∑ m ∈ Ioc 0 (⌊x / n⌋₊), (toArithmeticFunction g m : Nat)) +
    (∑ m ∈ Ioc 0 ⌊x/y⌋₊, toArithmeticFunction g m * ∑ n ∈ Ioc 0 (⌊x / m⌋₊), (toArithmeticFunction f n : Nat)) -
    (∑ n ∈ Ioc 0 ⌊x/y⌋₊, (toArithmeticFunction g n : Nat)) * (∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f n : Nat)) := by sorry
lemma dirichlet_hyperbola_method'''' {f g : ArithmeticFunction ℕ } {x y : Real } (hy:  1 ≤ y ∧ y ≤ x):
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (( f * g) n : Nat)  =
    (∑ n ∈ Ioc 0 ⌊y⌋₊,  f n * ∑ m ∈ Ioc 0 (⌊x / n⌋₊), ( g m : Nat)) +
    (∑ m ∈ Ioc 0 ⌊x/y⌋₊,  g m * ∑ n ∈ Ioc 0 (⌊x / m⌋₊), ( f n : Nat)) -
    (∑ n ∈ Ioc 0 ⌊x/y⌋₊, ( g n : Nat)) * (∑ n ∈ Ioc 0 ⌊y⌋₊, ( f n : Nat)) := by sorry
lemma sigma_sum_estimate (x : Real) : (fun x => ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n) -x*(Real.log x + 2*γ -1)) =O[Filter.atTop] (fun x : Real => Real.sqrt x) := by
have h1 :ζ * ζ = σ  0 := by
 rw[← zeta_mul_pow_eq_sigma , pow_zero_eq_zeta]
rw[← h1]
rw [Asymptotics.isBigO_iff']
refine ⟨5, by norm_num, ?_⟩
filter_upwards  [eventually_ge_atTop 2] with x hx
have h2 : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ζ * ζ) n - x*(Real.log x + 2*γ -1) = (-2)*∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) - (Int.fract (Real.sqrt x))^ 2 + 2*(Int.fract (Real.sqrt x))*Real.sqrt x := by
 have h21 : 1 ≤ Real.sqrt x ∧ Real.sqrt x ≤ x := by
  sorry
--先把自然数情况的先声明出来，然后用这个去证明，分下去往后推进，然后搞出来证明R的情况，一定要搞清楚依赖类型关系，这里边挺复杂，并且把学习一下策略，做一些策略
 have h22 : (ζ * ζ )  = LSeries.convolution ζ ζ := by
  sorry
 --我发现了一个双事情，原本的这个双曲定理要想去使用，必须搭配算术函数的乘法后的函数在某一点的取值等于LSeries.convolution f  g在某一点的取值，然后再用如果被求和项相同，那么求和一样
 have h23 : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ζ * ζ) n = ∑ n ∈ Ioc 0 ⌊x⌋₊, (LSeries.convolution ζ ζ) n := by
  sorry


 rw[dirichlet_hyperbola_method'''' h21]
 have h24 : ∑ n ∈ Ioc 0 ⌊√x⌋₊, (ζ n * ↑(∑ m ∈ Ioc 0 ⌊x / ↑n⌋₊, ζ m))  = (∑ n ∈ Ioc 0 ⌊√x⌋₊,⌊x / n⌋):= by
  sorry
 have h25 :(∑ m ∈ Ioc 0 ⌊x / √x⌋₊, ζ m * ∑ n ∈ Ioc 0 ⌊x / ↑m⌋₊, ζ n : ℝ ) = (∑ m ∈ Ioc 0 ⌊√x⌋₊,⌊x / m⌋) := by
  sorry
 have h26 : ↑(∑ n ∈ Ioc 0 ⌊√x⌋₊, ζ n * ∑ m ∈ Ioc 0 ⌊x / ↑n⌋₊, ζ m + ∑ m ∈ Ioc 0 ⌊x / √x⌋₊, ζ m * ∑ n ∈ Ioc 0 ⌊x / ↑m⌋₊, ζ n
 -
        (∑ n ∈ Ioc 0 ⌊x / √x⌋₊, ζ n) * ∑ n ∈ Ioc 0 ⌊√x⌋₊, ζ n) = (∑ n ∈ Ioc 0 ⌊√x⌋₊,⌊x / n⌋) + (∑ m ∈ Ioc 0 ⌊√x⌋₊,⌊x / m⌋) - (∑ n ∈ Ioc 0 ⌊x / √x⌋₊, ζ n) * ∑ n ∈ Ioc 0 ⌊√x⌋₊, ζ n := by sorry
 rw[h26]
 rw [h24, h25]







rw [h2]
have h3 :2 * ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) ≤ 2 * Real.sqrt x := by
  have h_sum_le_card : ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) ≤ ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, (1 : ℝ) :=
    Finset.sum_le_sum (fun n _ => (Int.fract_lt_one _).le)
  have card_eq : ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, (1 : ℝ) = (⌊Real.sqrt x⌋₊ : ℝ) := by simp
  calc
    2 * ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) ≤ 2 * ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, (1 : ℝ) := by gcongr
    _ = 2 * (⌊Real.sqrt x⌋₊ : ℝ) := by rw [card_eq]
    _ ≤ 2 * Real.sqrt x := by
      gcongr
      exact mod_cast Nat.floor_le (Real.sqrt_nonneg x)
have h4 : (Int.fract (Real.sqrt x))^ 2 ≤ 1 := by
 have h_nonneg : 0 ≤ Int.fract (Real.sqrt x) := Int.fract_nonneg _
 have h_lt_one : Int.fract (Real.sqrt x) < 1 := Int.fract_lt_one _
 nlinarith
have h5 : 2 * (Int.fract (Real.sqrt x)) * Real.sqrt x ≤ 2 * Real.sqrt x := by
 have h_nonneg : 0 ≤ Int.fract (Real.sqrt x) := Int.fract_nonneg _
 have h_lt_one : Int.fract (Real.sqrt x) < 1 := Int.fract_lt_one _
 have h_sqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
 nlinarith
have h6 :‖-2 * ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) - (Int.fract (Real.sqrt x)) ^ 2 + 2 * (Int.fract (Real.sqrt x)) * Real.sqrt x‖ ≤ 2 * Real.sqrt x + 1 + 2 * Real.sqrt x := by
 sorry
have h7 : 2 * Real.sqrt x + 1 + 2 * Real.sqrt x ≤ 5 * Real.sqrt x := by
 have h_sqrt_ge_one : 1 ≤ Real.sqrt x := by
   rw [← Real.sqrt_one]
   exact Real.sqrt_le_sqrt (by linarith)
 nlinarith
apply le_trans h6
apply le_trans h7
have h_sqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
have h : Real.sqrt x ≤ ‖Real.sqrt x‖ := Real.le_norm_self _
gcongr
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


end Daboussi_pnt.Basic
