import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.Misc
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
lemma dirichlet_hyperbola_method {f g : Nat → ℝ} {x y : ℝ } {F G : ℝ → ℝ}(hy:  1 ≤ y ∧ y ≤ x):
 (Finset.Ioc 0 ((⌊x⌋₊))).sum (fun n => (( LSeries.convolution f  g) n : ℝ))  =
 (Finset.Ioc 0 ((⌊y⌋₊))).sum (fun n =>  g n * (Finset.Ioc 0 ((⌊x/n⌋₊))).sum (fun n => (f n : ℝ))) +
 (Finset.Ioc 0 ((⌊x/y⌋₊))).sum (fun m => f m * (Finset.Ioc 0 ((⌊x/m⌋₊))).sum (fun n => (g n : ℝ)))-
 (Finset.Ioc 0 ((⌊x/y⌋₊))).sum (fun n => (f n : ℝ)) *(Finset.Ioc 0 ((⌊y⌋₊))).sum (fun n => (g n : ℝ)):= by
 sorry
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
--noncomputable def M (x : Real) : ℝ := (Finset.Ioc 0 ((⌊x⌋₊))).sum (fun n => (ArithmeticFunction.moebius n : ℝ))
--def moebiusReal : ArithmeticFunction ℝ := ArithmeticFunction.moebius (Int.cast : ℤ → ℝ)
--def moebiusReal : ℕ → ℝ := fun n => (Nat.moebius n : ℝ)
--def moebiusRealArith : ArithmeticFunction ℝ :=
--  (ArithmeticFunction.moebius : ArithmeticFunction ℤ).map (algebraMap ℤ ℝ)     -- 或直接用 (fun (x : ℤ) => (x : ℝ))
--    (by simp)            -- 证明 (0 : ℤ) 被映射到 (0 : ℝ)
--def moebiusRealArith' : ArithmeticFunction ℝ :=
--  ⟨fun n => (ArithmeticFunction.moebius n : ℝ), by simp⟩
theorem daboussi_implication :
  (fun x : Real => (Finset.Ioc 0 ((⌊x⌋₊))).sum (fun n => (ArithmeticFunction.moebius n : ℝ))) =O[Filter.atTop] (fun x :  Real => (x : ℝ)) →
  (fun x : Real => Chebyshev.psi x) =o[Filter.atTop] (fun x : Real => (x : ℝ)):= by
 let moebiusRealArith' : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ), by simp⟩

 intro hM



end Daboussi_pnt.Basic
