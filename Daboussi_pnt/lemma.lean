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
open Finset
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
