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

open scoped ArithmeticFunction.zeta
open scoped ArithmeticFunction.sigma

namespace Daboussi_pnt.Basic
open Finset
open ArithmeticFunction
open Finset Nat
open scoped ArithmeticFunction.zeta
open scoped sigma
open Filter
lemma dirichlet_hyperbola_method {f g : Nat → ℝ} {x y : ℝ } (hy:  1 ≤ y ∧ y ≤ x):
    ∑ n ∈ Ioc 0 ⌊x⌋₊, ((LSeries.convolution f  g) n : ℝ)  =
    (∑ n ∈ Ioc 0 ⌊y⌋₊, toArithmeticFunction f n * ∑ m ∈ Ioc 0 (⌊x⌋₊ / n), (toArithmeticFunction g m : ℝ)) +
    (∑ m ∈ Ioc 0 ⌊x/y⌋₊, toArithmeticFunction g m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f n : ℝ)) -
    (∑ n ∈ Ioc 0 ⌊x/y⌋₊, (toArithmeticFunction g n : ℝ)) * (∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f n : ℝ)) := by
   -- h'' : ⌊x / y⌋₊ ≤ ⌊x⌋₊
   -- 数学思路：由 1 ≤ y ≤ x 知 x ≥ 0。在非负实数上，除以 ≥1 的分母不会增大数值，
   -- 即 x/y ≤ x，取整后不等号保持。
   -- Lean4实现：div_le_self 给出 x/y ≤ x，再用 Nat.floor_le_floor 提升到取整。
   have h'': ⌊x / y⌋₊  ≤ ⌊x⌋₊ := by
    rcases hy with ⟨hy1, hy2⟩           -- 拆开假设 1 ≤ y 和 y ≤ x
    have hx_nonneg : 0 ≤ x := by linarith -- 由 1 ≤ y ≤ x 得 x ≥ 0
    refine Nat.floor_le_floor (div_le_self hx_nonneg hy1)
   -- f_trunc：截断函数，在 ⌊y⌋₊ 以下取 0，以上取原值 f n
   -- 这对应于 Dirichlet 双曲方法中 "F'_y"——只对 n > y 求和
   let f_trunc (n : ℕ) := if n > ⌊y⌋₊ then f n else 0
   -- hx1zero : x₁ 在"上区间" (⌊x/y⌋₊, ⌊x⌋₊] 时，对应的内层和为零
   -- 数学思路：当 x₁ > ⌊x/y⌋₊ 时，⌊x⌋₊ / x₁ ≤ ⌊y⌋₊（反证：若不然，
   -- 则 ⌊y⌋₊ + 1 ≤ ⌊x⌋₊ / x₁，乘以 x₁ 得 (⌊y⌋₊+1)·x₁ ≤ ⌊x⌋₊ ≤ x，
   -- 但由 x₁ > x/y 可推出 (⌊y⌋₊+1)·x₁ > x，矛盾）。
   -- 因此内层求和的每个 m ≤ ⌊y⌋₊，f_trunc m = 0，整个和为 0。
   -- Lean4实现：对每个 x₁，证内层和为 0（Finset.sum_eq_zero），
   -- 核心不等式用实数和 Nat 之间的 mod_cast 传递，反证法 + linarith 推出矛盾。
   have hx1zero :∑ x_1 ∈ Ioc ⌊x / y⌋₊ ⌊x⌋₊,(toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m =0 :=by
    apply Finset.sum_eq_zero            -- 外和为零 ← 每项为零
    intro x1 hx1
    rcases Finset.mem_Ioc.mp hx1 with ⟨hx1_low, hx1_high⟩  -- 取出区间条件
    rcases hy with ⟨hy1, hy2⟩
    have hy_pos_real : (0 : ℝ) < y := by linarith    -- y > 0（实数）
    have hx_nonneg_real : (0 : ℝ) ≤ x := by linarith -- x ≥ 0（实数）
    have hx1_pos : 0 < x1 := by
      have h0_le_floor : (0 : ℕ) ≤ ⌊x / y⌋₊ := Nat.zero_le _
      exact Nat.lt_of_le_of_lt h0_le_floor hx1_low -- 0 ≤ ⌊x/y⌋₊ < x1
    -- 证明内层求和为零：对每个 m ∈ Ioc 0 (⌊x⌋₊/x1)，f_trunc m = 0
    have inner_zero : ∑ m ∈ Ioc 0 (⌊x⌋₊ / x1), (toArithmeticFunction f_trunc) m = 0 := by
      apply Finset.sum_eq_zero          -- 内和为零 ← 每项为零
      intro m hm
      rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
      have hm_le_div : m ≤ ⌊x⌋₊ / x1 := hm_high  -- m 在内层求和的上界内
      -- 证明 m ≤ ⌊y⌋₊（反证法）
      have hm_le_yfloor : m ≤ ⌊y⌋₊ := by
        by_contra! H                      -- 假设 ⌊y⌋₊ < m
        have h_mul_le : m * x1 ≤ ⌊x⌋₊ :=
          (Nat.le_div_iff_mul_le hx1_pos).mp hm_le_div  -- m ≤ ⌊x⌋₊/x1 → m·x1 ≤ ⌊x⌋₊
        have hy_floor_succ_le_m : (⌊y⌋₊ + 1 : ℕ) ≤ m := Nat.succ_le_of_lt H
        -- 上界估计：(⌊y⌋₊+1)·x1 ≤ x（从 ℕ 提升到 ℝ）
        have h_left : ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) ≤ x := by
          calc
            ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) = ((⌊y⌋₊ + 1 : ℕ) : ℝ) * (x1 : ℝ) := by simp
            _ ≤ (m : ℝ) * (x1 : ℝ) :=
              mul_le_mul_of_nonneg_right (mod_cast hy_floor_succ_le_m) (by exact mod_cast (Nat.zero_le x1))
            _ = ((m * x1 : ℕ) : ℝ) := by simp
            _ ≤ (⌊x⌋₊ : ℝ) := mod_cast h_mul_le
            _ ≤ x := Nat.floor_le hx_nonneg_real   -- ⌊x⌋₊ ≤ x
        -- 下界估计：(⌊y⌋₊+1)·x1 > x（用 x1 > x/y 和 y < ⌊y⌋₊+1）
        have h_right : x < ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) := by
          -- 先证 x1 > x/y（实数不等式，从 x1 > ⌊x/y⌋₊ 提升）
          have hx1_gt_div : (x / y : ℝ) < (x1 : ℝ) := by
            have h_floor_succ_le_x1 : (⌊x / y⌋₊ : ℝ) + 1 ≤ (x1 : ℝ) := by
              have h_nat : (⌊x / y⌋₊ : ℕ) + 1 ≤ x1 := Nat.succ_le_of_lt hx1_low
              exact mod_cast h_nat               -- ℕ 不等式提升到 ℝ
            have h_div_lt_floor_succ : (x / y : ℝ) < (⌊x / y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
            linarith                              -- 链接：x/y < ⌊x/y⌋₊+1 ≤ x1
          have hy_lt_succ : (y : ℝ) < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _  -- y < ⌊y⌋₊+1
          calc
            (x : ℝ) < (x1 : ℝ) * y := (div_lt_iff₀ hy_pos_real).mp hx1_gt_div  -- 由 x/y < x1 和 y>0
            _ < (x1 : ℝ) * ((⌊y⌋₊ : ℝ) + 1) :=
              mul_lt_mul_of_pos_left hy_lt_succ (by exact mod_cast hx1_pos)       -- 乘以正的 x1
            _ = ((⌊y⌋₊ + 1 : ℕ) * x1 : ℝ) := by
              push_cast
              ring                                 -- 整理为 Nat 乘积的形式
        linarith                                  -- 上界 ≤ x < 下界，矛盾
      -- m ≤ ⌊y⌋₊ 蕴含 f_trunc m = 0
      have h_trunc_zero : (toArithmeticFunction f_trunc) m = 0 := by
        simp [toArithmeticFunction, hm_low.ne', f_trunc]  -- 展开 toArithmeticFunction 和 f_trunc
        intro h_not
        exfalso; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h_not hm_le_yfloor)  -- ⌊y⌋₊ < m 与 m ≤ ⌊y⌋₊ 矛盾
      simp [h_trunc_zero]
    simp [inner_zero]                      -- 内层和为 0 → 乘 g x₁ 后仍为 0 → 外和为 0
   -- h123 : 将下区间 (0, ⌊x/y⌋₊] 的内层求和按 ⌊y⌋₊ 剖分为两段
   -- 数学思路：对每个固定的 x₁，内层求和 ∑_{m=1}^{⌊x⌋₊/x₁} f_trunc(m)
   -- 可拆为 m ≤ ⌊y⌋₊ 的部分（f_trunc=0）和 m > ⌊y⌋₊ 的部分（f_trunc=f）。
   -- 分类：若 ⌊y⌋₊ ≤ ⌊x⌋₊/x₁，用 Finset.sum_Ioc_consecutive 直接剖分。
   -- 若 ⌊x⌋₊/x₁ < ⌊y⌋₊，则所有 m 都在零区域内，三项和均为 0。
   -- Lean4实现：by_cases 分情况；正情况用 sum_Ioc_consecutive + mul_add；
   -- 负情况用 sum_eq_zero。
   have h123 :∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m =
  ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 ⌊y⌋₊ , (toArithmeticFunction f_trunc) m +
  ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m :=by
    -- 先把 RHS 的两个求和合并为一个，便于逐项比较
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl              -- 逐项验证相等
    intro x1 hx1
    rcases Finset.mem_Ioc.mp hx1 with ⟨hx1_low, hx1_high⟩
    set d := ⌊x⌋₊ / x1 with hd              -- d = ⌊x⌋₊/x1，内层求和上界
    by_cases h : ⌊y⌋₊ ≤ d
    · -- 情况1：⌊y⌋₊ ≤ d，可以直接剖分区间
      let F : ℕ → ℝ := fun m => (toArithmeticFunction f_trunc) m
      have hsplit := (Finset.sum_Ioc_consecutive F (Nat.zero_le _) h).symm
      -- hsplit: ∑_{0<·≤d} F = ∑_{0<·≤⌊y⌋₊} F + ∑_{⌊y⌋₊<·≤d} F
      rw [hsplit, mul_add]                  -- 分配 g x₁ * (A + B) = g x₁*A + g x₁*B
    · -- 情况2：d < ⌊y⌋₊，则所有区间内的 m 都 ≤ ⌊y⌋₊，f_trunc 均为 0
      have h_lt : d < ⌊y⌋₊ := Nat.lt_of_not_ge h
      -- 左端内层和为 0（所有 m ≤ d < ⌊y⌋₊）
      have inner_LHS_zero : ∑ m ∈ Ioc 0 d, (toArithmeticFunction f_trunc) m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
        have hm_lt_yfloor : m < ⌊y⌋₊ := Nat.lt_of_le_of_lt hm_high h_lt
        have hm_not_gt : ¬ (⌊y⌋₊ < m) := Nat.not_lt.mpr (Nat.le_of_lt hm_lt_yfloor)
        simp [toArithmeticFunction, hm_low.ne', f_trunc, hm_not_gt]
      -- RHS 第一项内层和为 0（所有 m ≤ ⌊y⌋₊）
      have inner_RHS1_zero : ∑ m ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f_trunc) m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
        have hm_not_gt : ¬ (⌊y⌋₊ < m) := Nat.not_lt.mpr hm_high
        simp [toArithmeticFunction, hm_low.ne', f_trunc, hm_not_gt]
      -- RHS 第二项内层和为 0（Ioc ⌊y⌋₊ d 为空集，因 d < ⌊y⌋₊）
      have inner_RHS2_zero : ∑ m ∈ Ioc ⌊y⌋₊ d, (toArithmeticFunction f_trunc) m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
        exfalso
        have hm_lt_yfloor : m < ⌊y⌋₊ := Nat.lt_of_le_of_lt hm_high h_lt
        exact Nat.lt_irrefl _ (Nat.lt_trans hm_low hm_lt_yfloor)
      -- 三部分均为 0，等式成立
      simp [inner_LHS_zero, inner_RHS1_zero, inner_RHS2_zero]

   -- h123' : ∑ x₁∈(0,⌊x/y⌋₊] g(x₁) · ∑ m∈(0,⌊y⌋₊] f_trunc(m) = 0
   -- 数学思路：内层求和的上限是 ⌊y⌋₊，对其中的每个 m 都有 m ≤ ⌊y⌋₊，
   -- 因此 f_trunc m = 0（由截断定义）。整个二重求和恒为 0。
   -- Lean4实现：先证内层和为 0（Finset.sum_eq_zero），然后 simp 归约外层。
   have h123' : ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f_trunc) m =0 := by
    have inner_zero : ∑ m ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f_trunc) m = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
      have hm_not_gt : ¬ (⌊y⌋₊ < m) := Nat.not_lt.mpr hm_high  -- m ≤ ⌊y⌋₊ → f_trunc m = 0
      simp [toArithmeticFunction, hm_low.ne', f_trunc, hm_not_gt]
    simp [inner_zero]
   -- h123'' = 双曲方法核心恒等式：Term2 - Term3 = Σ g(m)·Σ_{n>y} f(n)
   -- 数学思路：这是 Dirichlet 双曲方法的关键代数恒等式。
   -- 对每个 m ≤ ⌊x/y⌋₊，将内层求和按 y 剖分：
   --   Σ_{n≤⌊x⌋₊/m} f(n) = Σ_{n≤⌊y⌋₊} f(n) + Σ_{⌊y⌋₊<n≤⌊x⌋₊/m} f(n)
   -- 前一项乘以 g(m) 并对 m 求和，得到 (Σ g(m))·(Σ_{n≤y} f(n)) = Term3。
   -- 后一项正是 RHS（在 n > y 时 f_trunc = f，n ≤ y 时 f_trunc = 0）。
   -- 因此 Term2 = Term3 + RHS，即 Term2 - Term3 = RHS。
   -- 关键前置条件：⌊y⌋₊ ≤ ⌊x⌋₊/m（由 m ≤ ⌊x/y⌋₊ 保证，证明用反证法+实不等式）。
   -- Lean4实现：
   --   1. h_split_inner：用 sum_Ioc_consecutive 剖分内层和（需不等式）
   --   2. h_term2_split：将剖分代入 Term2，代数展开得到 Term3 + 剩余
   --   3. calc：Term2 - Term3 = 剩余 → 替换 f 为 f_trunc 得 RHS
   have h123'' : ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
    - ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
    = ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m := by
    rcases hy with ⟨hy1, hy2⟩
    have hy_pos_real : (0 : ℝ) < y := by linarith         -- y > 0（后面除法用）
    have hx_nonneg_real : (0 : ℝ) ≤ x := by linarith      -- x ≥ 0（后面取整用）
    -- 核心子引理：对每个外层指标 m，将内层求和按 ⌊y⌋₊ 剖分
    -- 条件：m > 0，m ≤ ⌊x/y⌋₊ → ⌊y⌋₊ ≤ ⌊x⌋₊/m
    have h_split_inner (m : ℕ) (hm_pos : 0 < m) (hm_le : m ≤ ⌊x / y⌋₊) :
        ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
        = ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n
        + ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n := by
      -- 需要先证 ⌊y⌋₊ ≤ ⌊x⌋₊ / m（即 ℕ 除法不等式）
      have h_ineq : ⌊y⌋₊ ≤ ⌊x⌋₊ / m := by
        rw [Nat.le_div_iff_mul_le hm_pos]    -- 转为 ⌊y⌋₊·m ≤ ⌊x⌋₊
        by_contra! H                         -- 假设 ⌊x⌋₊ < ⌊y⌋₊·m
        -- 在实数中导出上界：⌊y⌋₊·m ≤ y·m ≤ y·⌊x/y⌋₊ ≤ y·(x/y) = x
        have h_real : ((⌊y⌋₊ * m : ℕ) : ℝ) ≤ x := by
          calc
            ((⌊y⌋₊ * m : ℕ) : ℝ) = (⌊y⌋₊ : ℝ) * (m : ℝ) := by simp
            _ ≤ (y : ℝ) * (m : ℝ) := by
              gcongr; exact Nat.floor_le (by linarith : 0 ≤ y)   -- ⌊y⌋₊ ≤ y
            _ ≤ (y : ℝ) * (⌊x / y⌋₊ : ℝ) :=
              mul_le_mul_of_nonneg_left (mod_cast hm_le) (by linarith [hy1] : 0 ≤ (y : ℝ))
            _ ≤ (y : ℝ) * (x / y : ℝ) := by
              gcongr; exact Nat.floor_le (div_nonneg hx_nonneg_real (by linarith))  -- ⌊x/y⌋₊ ≤ x/y
            _ = x := by field_simp [ne_of_gt hy_pos_real]         -- y·(x/y) = x
        -- 在实数中导出下界：x < (⌊x⌋₊ : ℝ)+1 ≤ ⌊y⌋₊·m
        have hx_lt_succ : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x  -- x < ⌊x⌋₊+1
        have h_succ_real : (⌊x⌋₊ : ℝ) + 1 ≤ ((⌊y⌋₊ * m : ℕ) : ℝ) := by
          have h_nat : (⌊x⌋₊ : ℕ) + 1 ≤ ⌊y⌋₊ * m := Nat.succ_le_of_lt H  -- ⌊x⌋₊ < ⌊y⌋₊·m
          exact mod_cast h_nat
        linarith                                 -- x < (⌊x⌋₊)+1 ≤ ⌊y⌋₊·m ≤ x，矛盾
      -- 有了不等式，用 sum_Ioc_consecutive 剖分内层求和
      rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => (toArithmeticFunction f) n) (Nat.zero_le _) h_ineq]
    -- 用 h_split_inner 展开 Term2，分解为 Term3 + 剩余
    have h_term2_split :
        ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
        = ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
        + ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n := by
      calc
        -- 步1：用 h_split_inner 替换内层求和
        ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
        = ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m
            * (∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n
              + ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          refine Finset.sum_congr rfl (fun m hm => ?_)
          rcases Finset.mem_Ioc.mp hm with ⟨hm_low, hm_high⟩
          rw [h_split_inner m hm_low hm_high]
        -- 步2：分配律 g·(A+B) = g·A + g·B
        _ = ∑ m ∈ Ioc 0 ⌊x / y⌋₊,
            ((toArithmeticFunction g) m * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n
            + (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          refine Finset.sum_congr rfl (fun m hm => by rw [mul_add])
        -- 步3：拆开求和号 Σ(A+B) = ΣA + ΣB
        _ = (∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
          + (∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          rw [Finset.sum_add_distrib]
        -- 步4：提取公因子 Σ g(m)·S = (Σ g(m))·S
        _ = ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
          + (∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n) := by
          simp [Finset.sum_mul]
    -- 主计算：用 h_term2_split 和代数简化得到最终等式
    calc
      ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc 0 (⌊x⌋₊ / m), (toArithmeticFunction f) n
          - ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
      -- 用 h_term2_split 替换 Term2
      = (((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n)
          + ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n)
          - ((∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m) * ∑ n ∈ Ioc 0 ⌊y⌋₊, (toArithmeticFunction f) n) := by
        rw [h_term2_split]
      -- (Term3 + 剩余) - Term3 = 剩余
      _ = ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) n := by
        abel
      -- 将 f 替换为 f_trunc（在 n > ⌊y⌋₊ 时二者相等）
      _ = ∑ x_1 ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) x_1 * ∑ m ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x_1), (toArithmeticFunction f_trunc) m := by
        refine Finset.sum_congr rfl (fun x1 _ => ?_)
        -- 对内层求和的每一项，f_trunc = f（因为 m > ⌊y⌋₊）
        have h_inner_eq : ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x1), (toArithmeticFunction f) n
            = ∑ n ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / x1), (toArithmeticFunction f_trunc) n := by
          refine Finset.sum_congr rfl (fun n hn => ?_)
          rcases Finset.mem_Ioc.mp hn with ⟨hn_low, hn_high⟩
          have hn_pos : n ≠ 0 := by omega              -- n > 0
          have hn_gt_yfloor : ⌊y⌋₊ < n := hn_low      -- n > ⌊y⌋₊ → f_trunc n = f n
          simp [toArithmeticFunction, f_trunc, hn_pos, hn_gt_yfloor]
        rw [h_inner_eq]
   sorry
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
local notation "γ" => Real.eulerMascheroniConstant

lemma sigma_sum_estimate (x : Real) : (fun x => ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n) -x*(Real.log x + 2*γ -1)) =O[Filter.atTop] (fun x : Real => Real.sqrt x) := by
have h1 :ζ * ζ = σ  0 := by
 rw[← zeta_mul_pow_eq_sigma , pow_zero_eq_zeta]
rw[← h1]
rw [Asymptotics.isBigO_iff']
refine ⟨5, by norm_num, ?_⟩
filter_upwards  [eventually_ge_atTop 2] with x hx
have h2 : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ζ * ζ) n - x*(Real.log x + 2*γ -1) = (-2)*∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) - (Int.fract (Real.sqrt x))^ 2 + 2*(Int.fract (Real.sqrt x))*Real.sqrt x := by
  set y := Real.sqrt x with hy
  have h_one_le_y : 1 ≤ y := by
    rw [← Real.sqrt_one, hy]
    exact Real.sqrt_le_sqrt (by linarith)
  have h_y_le_x : y ≤ x := by
    dsimp [y]
    calc
      Real.sqrt x ≤ Real.sqrt (x * x) := Real.sqrt_le_sqrt (by nlinarith)
      _ = Real.sqrt (x ^ 2) := by ring
      _ = x := Real.sqrt_sq (by linarith)
  set f : ℕ → ℝ := fun _ => 1 with hf
  set g : ℕ → ℝ := fun _ => 1 with hg
  have h_diri := dirichlet_hyperbola_method ⟨h_one_le_y, h_y_le_x⟩ (f := f) (g := g)
  have h_conv_eq (n : ℕ) : ((LSeries.convolution f g) n : ℝ) = ((ζ * ζ) n : ℝ) := by
    simp [LSeries.convolution, hf, hg, toArithmeticFunction, ζ, ArithmeticFunction.zeta_apply]
  have hIoc1 (N : ℕ) : (∑ m ∈ Ioc 0 N, (toArithmeticFunction f m : ℝ)) = (N : ℝ) := by
    simp [hf, toArithmeticFunction]
  have hIoc2 (N : ℕ) : (∑ m ∈ Ioc 0 N, (toArithmeticFunction g m : ℝ)) = (N : ℝ) := by
    simp [hg, toArithmeticFunction]
  simp_rw [h_conv_eq] at h_diri
  have h_xy_eq : ⌊x / y⌋₊ = ⌊y⌋₊ := by
    rw [hy]
    have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    field_simp [hpos.ne']
    simp
  simp [hf, hg, toArithmeticFunction, hIoc1, hIoc2, h_xy_eq] at h_diri
  -- h_diri now: ∑ (ζ*ζ)n = 2·∑_{n≤⌊√x⌋} (⌊x⌋₊/n) - (⌊√x⌋₊)²  (with Nat division)
  -- Need to convert integer division ⌊x⌋₊/n to real expression x/n - fract(x/n)
  sorry
rw[h2]
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
 set A := -2 * ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) with hA
 set B := -(Int.fract (Real.sqrt x)) ^ 2 with hB
 set C := 2 * (Int.fract (Real.sqrt x)) * Real.sqrt x with hC
 have h_norm_A : ‖A‖ ≤ 2 * Real.sqrt x := by
   rw [hA, Real.norm_eq_abs]
   have h_sum_nonneg : 0 ≤ ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) :=
     Finset.sum_nonneg (fun n _ => Int.fract_nonneg _)
   calc
     |-2 * ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n)|
         = |(-2 : ℝ)| * |∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n)| := abs_mul _ _
     _ = |(2 : ℝ)| * |∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n)| := by rw [abs_neg]
     _ = 2 * |∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n)| := by
       rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
     _ = 2 * ∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) := by
       rw [abs_of_nonneg h_sum_nonneg]
     _ ≤ 2 * Real.sqrt x := h3
 have h_norm_B : ‖B‖ ≤ 1 := by
   rw [hB, Real.norm_eq_abs, abs_neg]
   have h_sq_nonneg : 0 ≤ (Int.fract (Real.sqrt x)) ^ 2 := pow_two_nonneg _
   rw [abs_of_nonneg h_sq_nonneg]
   exact h4
 have h_norm_C : ‖C‖ ≤ 2 * Real.sqrt x := by
   rw [hC, Real.norm_eq_abs]
   have h_nonneg : 0 ≤ 2 * (Int.fract (Real.sqrt x)) * Real.sqrt x :=
     mul_nonneg (mul_nonneg (by norm_num) (Int.fract_nonneg _)) (Real.sqrt_nonneg _)
   rw [abs_of_nonneg h_nonneg]
   exact h5
 calc
   ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
   _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := by gcongr; apply norm_add_le
   _ ≤ (2 * Real.sqrt x + 1) + 2 * Real.sqrt x := by gcongr
   _ = 2 * Real.sqrt x + 1 + 2 * Real.sqrt x := by ring
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
/-- harmonic ⌊x⌋₊ - log x - γ = O(1/x) as x → ∞, via Abel summation / sandwich bounds. -/
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
