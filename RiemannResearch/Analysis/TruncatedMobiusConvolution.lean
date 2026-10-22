import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact products of truncated zeta and Möbius Dirichlet polynomials

The archived source passed local Lean 4.33.0-rc2 compilation. Its recovered integration
still awaits the final project-server checkpoint. All statements are finite identities or
elementary inequalities. No analytic estimate or statement about zeta zeros is assumed.

The coefficient is the convolution of *both* truncated sequences. Consequently it agrees
with the Dirichlet identity below the cutoff and has support at most the square of the cutoff.
The cancellation uses Mathlib's `ArithmeticFunction.coe_zeta_mul_coe_moebius`, the proven
Dirichlet-convolution inverse identity in `Mathlib.NumberTheory.ArithmeticFunction.Moebius`.
These formulas implement the finite polynomial product from the zeta ordinate harmonic program.

Mathlib source (supports the imported analytic/arithmetic identity):
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open Finset

namespace RiemannResearch.Analysis.TruncatedMobiusConvolution

variable {R : Type*}

/-- Truncate an arithmetic function without changing its required value at zero. -/
def truncate [Zero R] (J : ℕ) (f : ArithmeticFunction R) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ J then f n else 0, by simp⟩

@[simp] theorem truncate_apply [Zero R] (J n : ℕ) (f : ArithmeticFunction R) :
    truncate J f n = if n ≤ J then f n else 0 := rfl

/-- Both divisor coordinates lie below `n`, so truncation leaves this convolution unchanged. -/
theorem truncate_mul_apply_of_le [Semiring R] (f g : ArithmeticFunction R)
    {J n : ℕ} (hn : n ≤ J) :
    (truncate J f * truncate J g) n = (f * g) n := by
  classical
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ : p.1 ≤ J :=
    (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)).trans hn
  have h₂ : p.2 ≤ J :=
    (Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hp)).trans hn
  simp only [truncate_apply, if_pos h₁, if_pos h₂]

/-- The exact coefficient in the product of the two truncated polynomials. -/
def coefficient (J n : ℕ) : ℂ :=
  (truncate J (ζ : ArithmeticFunction ℂ) *
    truncate J (μ : ArithmeticFunction ℂ)) n

theorem coefficient_eq_divisor_sum (J n : ℕ) :
    coefficient J n = ∑ p ∈ n.divisorsAntidiagonal,
      if p.1 ≤ J ∧ p.2 ≤ J then (μ p.2 : ℂ) else 0 := by
  classical
  rw [coefficient, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  have h₁ := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
  by_cases hd : p.1 ≤ J <;> by_cases he : p.2 ≤ J <;>
    simp [truncate_apply, hd, he, ArithmeticFunction.zeta_apply_ne h₁]

/-- Exact Möbius cancellation, including the constant coefficient. -/
theorem coefficient_eq_delta_of_le {J n : ℕ} (hn : n ≤ J) :
    coefficient J n = if n = 1 then 1 else 0 := by
  rw [coefficient, truncate_mul_apply_of_le _ _ hn,
    ArithmeticFunction.coe_zeta_mul_coe_moebius, ArithmeticFunction.one_apply]

theorem coefficient_eq_zero_of_sq_lt {J n : ℕ} (hn : J * J < n) :
    coefficient J n = 0 := by
  classical
  rw [coefficient_eq_divisor_sum]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hcut : ¬(p.1 ≤ J ∧ p.2 ≤ J) := by
    intro hc
    have h := Nat.mul_le_mul hc.1 hc.2
    rw [hprod] at h
    omega
  simp [hcut]

theorem norm_moebius_le_one (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

/-- The divisor bound needs no estimate for the size of the divisor function. -/
theorem norm_coefficient_le_card_divisors (J n : ℕ) :
    ‖coefficient J n‖ ≤ (n.divisors.card : ℝ) := by
  classical
  rw [coefficient_eq_divisor_sum]
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal,
        if p.1 ≤ J ∧ p.2 ≤ J then (μ p.2 : ℂ) else 0‖
      ≤ ∑ p ∈ n.divisorsAntidiagonal,
        ‖if p.1 ≤ J ∧ p.2 ≤ J then (μ p.2 : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _hp
      split_ifs
      · exact norm_moebius_le_one p.2
      · simp
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp
    _ = (n.divisors.card : ℝ) := by
      rw [← Nat.map_div_right_divisors]
      simp

/-- Coefficients after subtracting the constant polynomial `1`. -/
def residualCoefficient (J n : ℕ) : ℂ :=
  coefficient J n - if n = 1 then 1 else 0

theorem residualCoefficient_eq_zero_of_le {J n : ℕ} (hn : n ≤ J) :
    residualCoefficient J n = 0 := by
  simp [residualCoefficient, coefficient_eq_delta_of_le hn]

theorem residualCoefficient_eq_coefficient_of_lt {J n : ℕ}
    (hJ : 1 ≤ J) (hn : J < n) :
    residualCoefficient J n = coefficient J n := by
  have hn₁ : n ≠ 1 := by omega
  simp [residualCoefficient, hn₁]

theorem residualCoefficient_eq_zero_of_sq_lt {J n : ℕ}
    (hJ : 1 ≤ J) (hn : J * J < n) :
    residualCoefficient J n = 0 := by
  have hJJ : J ≤ J * J := by nlinarith
  rw [residualCoefficient_eq_coefficient_of_lt hJ (hJJ.trans_lt hn),
    coefficient_eq_zero_of_sq_lt hn]

theorem norm_residualCoefficient_le_card_divisors {J : ℕ} (hJ : 1 ≤ J) (n : ℕ) :
    ‖residualCoefficient J n‖ ≤ (n.divisors.card : ℝ) := by
  by_cases hn : n ≤ J
  · rw [residualCoefficient_eq_zero_of_le hn, norm_zero]
    exact Nat.cast_nonneg _
  · rw [residualCoefficient_eq_coefficient_of_lt hJ (Nat.lt_of_not_ge hn)]
    exact norm_coefficient_le_card_divisors J n

/-- Multiplicative fibers identify the clipped divisor sum with the product cutoff. -/
theorem product_fiber_eq_clipped_antidiagonal {J n : ℕ} (hn : n ≠ 0) :
    ((Finset.Icc 1 J).product (Finset.Icc 1 J)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = n) =
      n.divisorsAntidiagonal.filter (fun p => p.1 ≤ J ∧ p.2 ≤ J) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, hprod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hpP
    have hdJ := (Finset.mem_Icc.mp hd).2
    have heJ := (Finset.mem_Icc.mp he).2
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hn⟩, hdJ, heJ⟩
  · intro hp
    obtain ⟨hpA, hpJ₁, hpJ₂⟩ := Finset.mem_filter.mp hp
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hpA).1
    have hpne : p.1 ≠ 0 ∧ p.2 ≠ 0 :=
      mul_ne_zero_iff.mp (hprod.symm ▸ hn)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ?_, hprod⟩
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hpne.1, hpJ₁⟩,
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hpne.2, hpJ₂⟩⟩

theorem coefficient_eq_product_fiber {J n : ℕ} (hn : n ≠ 0) :
    coefficient J n =
      ∑ p ∈ ((Finset.Icc 1 J).product (Finset.Icc 1 J)).filter
        (fun p : ℕ × ℕ => p.1 * p.2 = n), (μ p.2 : ℂ) := by
  classical
  rw [coefficient_eq_divisor_sum, product_fiber_eq_clipped_antidiagonal hn,
    Finset.sum_filter]

/-- An exact finite product identity for any completely multiplicative weight on positive inputs.
No convergence half-plane or analytic continuation hypothesis occurs. -/
theorem weighted_truncated_product (J : ℕ) (w : ℕ → ℂ)
    (hmul : ∀ d e : ℕ, 1 ≤ d → 1 ≤ e → w (d * e) = w d * w e) :
    (∑ d ∈ Finset.Icc 1 J, w d) *
        (∑ e ∈ Finset.Icc 1 J, (μ e : ℂ) * w e) =
      ∑ n ∈ Finset.Icc 1 (J * J), coefficient J n * w n := by
  classical
  let S := (Finset.Icc 1 J).product (Finset.Icc 1 J)
  have hmap : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 (J * J) := by
    intro p hp
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hp
    obtain ⟨hd₁, hdJ⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he₁, heJ⟩ := Finset.mem_Icc.mp he
    exact Finset.mem_Icc.mpr ⟨by nlinarith, Nat.mul_le_mul hdJ heJ⟩
  calc
    _ = ∑ p ∈ S, w p.1 * ((μ p.2 : ℂ) * w p.2) := by
      exact (Finset.sum_mul_sum (Finset.Icc 1 J) (Finset.Icc 1 J)
        w (fun e => (μ e : ℂ) * w e)).trans
          (Finset.sum_product' (Finset.Icc 1 J) (Finset.Icc 1 J)
            (fun d e => w d * ((μ e : ℂ) * w e))).symm
    _ = ∑ n ∈ Finset.Icc 1 (J * J),
        ∑ p ∈ S.filter (fun p => p.1 * p.2 = n),
          w p.1 * ((μ p.2 : ℂ) * w p.2) :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ = ∑ n ∈ Finset.Icc 1 (J * J), coefficient J n * w n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn₀ : n ≠ 0 := by
        have := (Finset.mem_Icc.mp hn).1
        omega
      rw [coefficient_eq_product_fiber hn₀, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpS, hpN⟩ := Finset.mem_filter.mp hp
      obtain ⟨hd, he⟩ := Finset.mem_product.mp hpS
      have hd₁ := (Finset.mem_Icc.mp hd).1
      have he₁ := (Finset.mem_Icc.mp he).1
      rw [← hpN, hmul _ _ hd₁ he₁]
      ring

theorem weighted_truncated_product_sub_one {J : ℕ} (hJ : 1 ≤ J) (w : ℕ → ℂ)
    (h_one : w 1 = 1)
    (hmul : ∀ d e : ℕ, 1 ≤ d → 1 ≤ e → w (d * e) = w d * w e) :
    (∑ d ∈ Finset.Icc 1 J, w d) *
        (∑ e ∈ Finset.Icc 1 J, (μ e : ℂ) * w e) - 1 =
      ∑ n ∈ Finset.Icc 1 (J * J), residualCoefficient J n * w n := by
  classical
  have hJJ : 1 ≤ J * J := by nlinarith
  rw [weighted_truncated_product J w hmul]
  simp only [residualCoefficient, sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp [h_one, hJJ]

/-- All residual terms with index at most `J` vanish exactly. -/
theorem weighted_truncated_product_tail {J : ℕ} (hJ : 1 ≤ J) (w : ℕ → ℂ)
    (h_one : w 1 = 1)
    (hmul : ∀ d e : ℕ, 1 ≤ d → 1 ≤ e → w (d * e) = w d * w e) :
    (∑ d ∈ Finset.Icc 1 J, w d) *
        (∑ e ∈ Finset.Icc 1 J, (μ e : ℂ) * w e) - 1 =
      ∑ n ∈ Finset.Ioc J (J * J), coefficient J n * w n := by
  classical
  have hsub : Finset.Ioc J (J * J) ⊆ Finset.Icc 1 (J * J) := by
    intro n hn
    obtain ⟨hnJ, hnJJ⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hnJJ⟩
  calc
    _ = ∑ n ∈ Finset.Icc 1 (J * J), residualCoefficient J n * w n :=
      weighted_truncated_product_sub_one hJ w h_one hmul
    _ = ∑ n ∈ Finset.Ioc J (J * J), residualCoefficient J n * w n := by
      symm
      apply Finset.sum_subset hsub
      intro n hn hnnot
      have hnJJ := (Finset.mem_Icc.mp hn).2
      have hnJ : n ≤ J := by
        simp only [Finset.mem_Ioc] at hnnot
        omega
      simp [residualCoefficient_eq_zero_of_le hnJ]
    _ = ∑ n ∈ Finset.Ioc J (J * J), coefficient J n * w n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [residualCoefficient_eq_coefficient_of_lt hJ (Finset.mem_Ioc.mp hn).1]

/-- The analytic Dirichlet weight is completely multiplicative for every complex parameter. -/
def dirichletWeight (s : ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-s + (t : ℂ) * Complex.I)

theorem dirichletWeight_mul (s : ℂ) (t : ℝ) (d e : ℕ) :
    dirichletWeight s t (d * e) = dirichletWeight s t d * dirichletWeight s t e := by
  simpa only [dirichletWeight, Nat.cast_mul] using
    Complex.natCast_mul_natCast_cpow d e (-s + (t : ℂ) * Complex.I)

theorem analytic_truncated_product_sub_one {J : ℕ} (hJ : 1 ≤ J)
    (s : ℂ) (t : ℝ) :
    (∑ d ∈ Finset.Icc 1 J, dirichletWeight s t d) *
        (∑ e ∈ Finset.Icc 1 J, (μ e : ℂ) * dirichletWeight s t e) - 1 =
      ∑ n ∈ Finset.Icc 1 (J * J), residualCoefficient J n * dirichletWeight s t n := by
  apply weighted_truncated_product_sub_one hJ
  · simp [dirichletWeight]
  · intro d e _hd _he
    exact dirichletWeight_mul s t d e

/-- The exact error polynomial starts strictly beyond the original truncation. -/
theorem analytic_truncated_product_tail {J : ℕ} (hJ : 1 ≤ J)
    (s : ℂ) (t : ℝ) :
    (∑ d ∈ Finset.Icc 1 J, dirichletWeight s t d) *
        (∑ e ∈ Finset.Icc 1 J, (μ e : ℂ) * dirichletWeight s t e) - 1 =
      ∑ n ∈ Finset.Ioc J (J * J), coefficient J n * dirichletWeight s t n := by
  apply weighted_truncated_product_tail hJ
  · simp [dirichletWeight]
  · intro d e _hd _he
    exact dirichletWeight_mul s t d e

/-- The coefficient mass has an exact convolution envelope. Unlike a pointwise divisor bound,
this estimate incurs no factor `J^ε` and is useful in sharp polynomial Gram bounds. -/
theorem weighted_coefficient_mass_le_square (J : ℕ) (v : ℕ → ℝ)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ v n)
    (hmul : ∀ d e : ℕ, 1 ≤ d → 1 ≤ e → v (d * e) = v d * v e) :
    (∑ n ∈ Finset.Icc 1 (J * J), ‖coefficient J n‖ * v n) ≤
      (∑ d ∈ Finset.Icc 1 J, v d) ^ 2 := by
  classical
  let S := (Finset.Icc 1 J).product (Finset.Icc 1 J)
  have hmap : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 (J * J) := by
    intro p hp
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hp
    obtain ⟨hd₁, hdJ⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he₁, heJ⟩ := Finset.mem_Icc.mp he
    exact Finset.mem_Icc.mpr ⟨by nlinarith, Nat.mul_le_mul hdJ heJ⟩
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (J * J),
        ∑ p ∈ S.filter (fun p => p.1 * p.2 = n), v p.1 * v p.2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn₁ := (Finset.mem_Icc.mp hn).1
      have hn₀ : n ≠ 0 := by omega
      rw [coefficient_eq_product_fiber hn₀]
      calc
        ‖∑ p ∈ S.filter (fun p => p.1 * p.2 = n), (μ p.2 : ℂ)‖ * v n
          ≤ (∑ p ∈ S.filter (fun p => p.1 * p.2 = n), ‖(μ p.2 : ℂ)‖) * v n :=
            mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hpos n hn₁)
        _ = ∑ p ∈ S.filter (fun p => p.1 * p.2 = n), ‖(μ p.2 : ℂ)‖ * v n := by
          rw [Finset.sum_mul]
        _ ≤ ∑ p ∈ S.filter (fun p => p.1 * p.2 = n), v p.1 * v p.2 := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpS, hpN⟩ := Finset.mem_filter.mp hp
          obtain ⟨hd, he⟩ := Finset.mem_product.mp hpS
          have hd₁ := (Finset.mem_Icc.mp hd).1
          have he₁ := (Finset.mem_Icc.mp he).1
          calc
            ‖(μ p.2 : ℂ)‖ * v n ≤ 1 * v n :=
              mul_le_mul_of_nonneg_right (norm_moebius_le_one p.2) (hpos n hn₁)
            _ = v p.1 * v p.2 := by rw [one_mul, ← hpN, hmul _ _ hd₁ he₁]
    _ = ∑ p ∈ S, v p.1 * v p.2 :=
      Finset.sum_fiberwise_of_maps_to hmap _
    _ = (∑ d ∈ Finset.Icc 1 J, v d) ^ 2 := by
      rw [pow_two]
      exact (Finset.sum_product' (Finset.Icc 1 J) (Finset.Icc 1 J)
        (fun d e => v d * v e)).trans
          (Finset.sum_mul_sum (Finset.Icc 1 J) (Finset.Icc 1 J) v v).symm

end RiemannResearch.Analysis.TruncatedMobiusConvolution
