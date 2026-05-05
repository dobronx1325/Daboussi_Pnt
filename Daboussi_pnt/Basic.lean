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
-- summatory ( LSeries.convolution f  g) x = (Finset.Ioc 0 ((⌊y⌋₊))).sum (fun n =>  g n * F (x/n)) +
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
#check Finset.sum_congr
#check Finset.sum_bij
#check Finset.sum_image
#check Finset.sum_range_add
#check Finset.sum_Ioc_consecutive
#check  Finset.sum_product
#check  Finset.sum_comm
#check Finset.mul_sum
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
  rw [LSeries.convolution]
  rw[ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  rw[ Eq.symm (Finset.sum_Ioc_consecutive (fun i ↦ (toArithmeticFunction f) i * ∑ m ∈ Finset.Ioc 0 (⌊x⌋₊ / i), (toArithmeticFunction g) m) (Nat.zero_le ⌊y⌋₊) (Nat.floor_le_floor hy.2))]
  conv_rhs => rw [sub_eq_add_neg,  add_assoc]
  apply Mathlib.Tactic.LinearCombination.add_eq_eq
  linarith
  simp
  have h1 :∑ i ∈ Ioc ⌊y⌋₊ ⌊x⌋₊,  (toArithmeticFunction f) i * ∑ m ∈ Ioc 0 (⌊x⌋₊ / i), (toArithmeticFunction g) m=
   ∑ m ∈ Ioc 0 ⌊x / y⌋₊, (toArithmeticFunction g) m * ∑ i ∈ Ioc ⌊y⌋₊ (⌊x⌋₊ / m), (toArithmeticFunction f) i :=by
   simp_rw[sum_mul_sum_rel_dep]
   simp_rw[Finset.sum_product_dep]
   refine Finset.sum_bij ?_ ?_ ?_ ?_ ?_
   sorry
  rw[h1]
  have h2(m:Nat)(h4 :0 < m )(h3:m ∈ Ioc 0 ⌊x / y⌋₊): ⌊y⌋₊ ≤ ⌊x⌋₊ / m := by
   refine (Nat.le_div_iff_mul_le ?_).mpr ?_
   linarith
   sorry
  --rw[← (Finset.sum_Ioc_consecutive (fun n ↦ (toArithmeticFunction f) n)  (Nat.zero_le ⌊y⌋₊) (⌊y⌋₊ ≤ ⌊x⌋₊ / m ))]
  conv_rhs =>
   rw [← Finset.sum_congr rfl (fun m hm => by
   rw [← Finset.sum_Ioc_consecutive (fun i => (toArithmeticFunction f i) )
    (Nat.zero_le ⌊y⌋₊) (h2 m (Finset.mem_Ioc.mp hm).1 hm)])]
   rw [Finset.sum_congr rfl (fun m hm => by rw [mul_add])]
   rw [Finset.sum_add_distrib]
   rw [← Finset.sum_mul]
   abel_nf

















-- 手动给子类型定义 大小比较（修复 Preorder 报错）
--instance : Preorder NonnegRealsGe1 where
--  le x y := x.val ≤ y.val    -- 子类型≤ = 底层实数≤
--  le_refl x := by simp       -- 自反性
--  le_trans x y z := by
--  {intro h1 h2
--   linarith
--  }  -- 传递性

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
theorem daboussi_implication :
  (fun x : ℝ  => M x) =o[Filter.atTop] (fun x :  Real => (x : ℝ)) →
  Asymptotics.IsEquivalent Filter.atTop (fun x : ℝ => Chebyshev.psi x)  (fun x : ℝ => x) := by
 intro hM
 sorry

theorem daboussi_pnt : True := by trivial

end Daboussi_pnt.Basic
