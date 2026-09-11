import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite Laguerre moment transforms

Source: user-provided RH_Ramanujan_Laguerre_Schur_Continuation_20260911.md,
Sections 3--5; the polynomial convention agrees with NIST DLMF §18.3.
This module proves the finite algebra and its Bochner-integral bridge.
It does not assume or prove completeness of Laguerre polynomials, the Mellin
identity for actual arithmetic packets, or their required norm bounds.
In the RH application, take `f t = B_d (floor (exp t)) * exp (-t)`
and restrict Lebesgue measure to `Ici 0`. The ordinary-moment vanishing
hypotheses still require an analytic provider for those actual functions.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- The coefficient of the ordinary Laguerre polynomial. -/
def laguerreCoefficient (k j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * (k.choose j : ℝ) / (j.factorial : ℝ)

/-- Ordinary Laguerre polynomial, evaluated at a real argument. -/
def laguerreValue (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), laguerreCoefficient k j * t ^ j

/-- Laguerre coefficients obtained from a sequence of ordinary moments. -/
def laguerreMomentTransform (m : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), laguerreCoefficient k j * m j

theorem laguerreMomentTransform_zero (m : ℕ → ℝ) :
    laguerreMomentTransform m 0 = m 0 := by
  simp [laguerreMomentTransform, laguerreCoefficient]

theorem laguerreCoefficient_diagonal (k : ℕ) :
    laguerreCoefficient k k = (-1 : ℝ) ^ k / (k.factorial : ℝ) := by
  simp [laguerreCoefficient]

theorem laguerreCoefficient_diagonal_ne_zero (k : ℕ) :
    laguerreCoefficient k k ≠ 0 := by
  rw [laguerreCoefficient_diagonal]
  exact div_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast Nat.factorial_ne_zero k)

theorem laguerreMomentTransform_sub_smul (u v : ℕ → ℝ) (a : ℝ) (k : ℕ) :
    laguerreMomentTransform (fun j => u j - a * v j) k =
      laguerreMomentTransform u k - a * laguerreMomentTransform v k := by
  simp only [laguerreMomentTransform, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Below the first nonzero ordinary moment, the Laguerre transform vanishes. -/
theorem laguerreMomentTransform_eq_zero_of_moments
    (m : ℕ → ℝ) {r k : ℕ} (hzero : ∀ j < r, m j = 0) (hk : k < r) :
    laguerreMomentTransform m k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp [hzero j (lt_of_le_of_lt hjk hk)]

/-- The leading Laguerre coefficient has the claimed sign when the first
nonzero ordinary moment is `r! * P`. No Mellin hypothesis is concealed here. -/
theorem laguerreMomentTransform_leading
    (m : ℕ → ℝ) (r : ℕ) (P : ℝ)
    (hzero : ∀ j < r, m j = 0)
    (hlead : m r = (r.factorial : ℝ) * P) :
    laguerreMomentTransform m r = (-1 : ℝ) ^ r * P := by
  unfold laguerreMomentTransform
  rw [Finset.sum_range_succ]
  have hz : ∑ j ∈ Finset.range r, laguerreCoefficient r j * m j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hzero j (Finset.mem_range.mp hj)]
  rw [hz, zero_add, laguerreCoefficient_diagonal, hlead]
  have hf : (r.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  field_simp

/-- An exact moment correction leaves every earlier Laguerre coefficient
unchanged. -/
theorem laguerreMomentTransform_correction_lower
    (u v : ℕ → ℝ) {r k : ℕ}
    (hv : ∀ j < r, v j = 0) (hk : k < r) (a : ℝ) :
    laguerreMomentTransform (fun j => u j - a * v j) k =
      laguerreMomentTransform u k := by
  rw [laguerreMomentTransform_sub_smul,
    laguerreMomentTransform_eq_zero_of_moments v hv hk, mul_zero, sub_zero]

/-- The same correction cancels the selected coefficient exactly. -/
theorem laguerreMomentTransform_correction_current
    (u v : ℕ → ℝ) (r : ℕ)
    (hv : laguerreMomentTransform v r ≠ 0) :
    laguerreMomentTransform
      (fun j => u j -
        (laguerreMomentTransform u r / laguerreMomentTransform v r) * v j) r = 0 := by
  rw [laguerreMomentTransform_sub_smul, div_mul_cancel₀ _ hv, sub_self]

/-- The finite triangular transform loses no ordinary-moment information. -/
theorem laguerreMomentTransform_injective :
    Function.Injective laguerreMomentTransform := by
  intro u v huv
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrFun huv n
    unfold laguerreMomentTransform at hn
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hs : (∑ j ∈ Finset.range n, laguerreCoefficient n j * u j) =
        ∑ j ∈ Finset.range n, laguerreCoefficient n j * v j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    rw [hs] at hn
    exact (mul_left_cancel₀ (laguerreCoefficient_diagonal_ne_zero n))
      (add_left_cancel hn)

/-- An actual integral bridge: a finite Laguerre integral equals the transform
of the ordinary moments. Integrability is stated explicitly for each moment. -/
theorem integral_mul_laguerreValue
    (μ : Measure ℝ) (f : ℝ → ℝ) (k : ℕ)
    (hint : ∀ j ≤ k, Integrable (fun t => f t * t ^ j) μ) :
    (∫ t, f t * laguerreValue k t ∂μ) =
      laguerreMomentTransform (fun j => ∫ t, f t * t ^ j ∂μ) k := by
  have heq : (fun t => f t * laguerreValue k t) =
      fun t => ∑ j ∈ Finset.range (k + 1),
        laguerreCoefficient k j * (f t * t ^ j) := by
    funext t
    unfold laguerreValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, integral_finsetSum]
  · unfold laguerreMomentTransform
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_const_mul _ _
  · intro j hj
    exact (hint j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).const_mul _

/-- Actual lower Laguerre integrals vanish whenever the corresponding actual
ordinary integrals vanish. -/
theorem integral_mul_laguerreValue_eq_zero
    (μ : Measure ℝ) (f : ℝ → ℝ) {r k : ℕ}
    (hint : ∀ j ≤ k, Integrable (fun t => f t * t ^ j) μ)
    (hzero : ∀ j < r, (∫ t, f t * t ^ j ∂μ) = 0) (hk : k < r) :
    (∫ t, f t * laguerreValue k t ∂μ) = 0 := by
  rw [integral_mul_laguerreValue μ f k hint]
  exact laguerreMomentTransform_eq_zero_of_moments _ hzero hk

theorem integral_mul_laguerreValue_leading
    (μ : Measure ℝ) (f : ℝ → ℝ) (r : ℕ) (P : ℝ)
    (hint : ∀ j ≤ r, Integrable (fun t => f t * t ^ j) μ)
    (hzero : ∀ j < r, (∫ t, f t * t ^ j ∂μ) = 0)
    (hlead : (∫ t, f t * t ^ r ∂μ) = (r.factorial : ℝ) * P) :
    (∫ t, f t * laguerreValue r t ∂μ) = (-1 : ℝ) ^ r * P := by
  rw [integral_mul_laguerreValue μ f r hint]
  exact laguerreMomentTransform_leading _ r P hzero hlead

end RiemannResearch.Analysis
