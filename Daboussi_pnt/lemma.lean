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
lemma dirichlet_hyperbola_method [Ring R] {f g : ArithmeticFunction R} {x y : ℝ } (hy:  1 ≤ y ∧ y ≤ x):
    ∑ n ∈ Ioc 0 ⌊x⌋₊, (f * g) n   =
    (∑ n ∈ Ioc 0 ⌊y⌋₊,  f n * ∑ m ∈ Ioc 0 (⌊x / n⌋₊),  g m ) +
    (∑ m ∈ Ioc 0 ⌊x/y⌋₊,  g m * ∑ n ∈ Ioc 0 (⌊x / m⌋₊),  f n ) -
    (∑ n ∈ Ioc 0 ⌊x/y⌋₊, g n ) * (∑ n ∈ Ioc 0 ⌊y⌋₊, f n ) := by sorry

lemma sigma_sum_estimate (x : Real) : (fun x => ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n) -x*(Real.log x + 2*γ -1)) =O[Filter.atTop] (fun x : Real => Real.sqrt x) := by
have h1 :ζ * ζ = σ  0 := by
 rw[← zeta_mul_pow_eq_sigma , pow_zero_eq_zeta]
rw[← h1]
rw [Asymptotics.isBigO_iff']
refine ⟨5, by norm_num, ?_⟩
filter_upwards  [eventually_ge_atTop 2] with x hx
have h21 : 1 ≤ Real.sqrt x ∧ Real.sqrt x ≤ x := by
  have hx_nonneg : 0 ≤ x := by linarith
  have h_sqrt_ge_one : 1 ≤ Real.sqrt x := by
     calc
       1 = Real.sqrt 1 := by norm_num
       _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
  have h_sqrt_le_x : Real.sqrt x ≤ x := by
     calc
       Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := by
         nlinarith
       _ = x := by rw [Real.mul_self_sqrt hx_nonneg]
  exact And.intro h_sqrt_ge_one h_sqrt_le_x
have h2 : ∑ n ∈ Ioc 0 ⌊x⌋₊, (ζ * ζ) n  = x*(Real.log x + 2*γ -1)+
(-2)*∑ n ∈ Ioc 0 ⌊Real.sqrt x⌋₊, Int.fract (x / n) - (Int.fract (Real.sqrt x))^ 2 + 2*(Int.fract (Real.sqrt x))*Real.sqrt x := by
 --push_cast  --两种方法，直接求变态的zeta函数卷积表示结果，但着不好。或者说明，
 rw[ dirichlet_hyperbola_method h21]








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
