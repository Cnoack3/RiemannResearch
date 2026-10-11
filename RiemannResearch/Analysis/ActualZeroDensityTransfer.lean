import RiemannResearch.Analysis.ZeroDensityTransfer
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import Mathlib.Tactic.Ring

/-!
# Conditional exponential-density transfer for the actual zeta-zero sums

The exact signed correction, actual zero copies, analytic multiplicities, and
strip geometry are inherited from `ActualZeroOrdinate` and
`ActualZeroTailLayerCake`. The exponential bound on `strictTail` remains an
explicit analytic premise. No Selberg density theorem or RH premise is
manufactured by this transfer.

-/

noncomputable section
open Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate ZeroDensityTransfer

/-- Complete signed identity, before an absolute-value estimate is taken. -/
theorem ordinate_sub_landau_eq_neg_coshCorrection (T y : ℝ) :
    ordinateSum T y - landauSum T y = -coshCorrection T y := by
  rw [exact_signed_correction]
  ring

/-- Phase norm is exactly one; the horizontal correction retains every zero. -/
theorem norm_coshCorrection_le_full_coshSum (T y : ℝ) :
    ‖coshCorrection T y‖ ≤
      realSum T (fun ρ => Real.cosh (y * |ρ.re - 1 / 2|) - 1) := by
  have hpoint : ∀ ρ : ℂ,
      ‖phase y ρ.im * ((Real.cosh (y * (ρ.re - 1 / 2)) : ℂ) - 1)‖ =
        Real.cosh (y * |ρ.re - 1 / 2|) - 1 := by
    intro ρ
    have hcast : ((Real.cosh (y * (ρ.re - 1 / 2)) : ℂ) - 1) =
        ((Real.cosh (y * (ρ.re - 1 / 2)) - 1 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sub, Complex.ofReal_one]
    have hcosh : Real.cosh (y * (ρ.re - 1 / 2)) =
        Real.cosh (y * |ρ.re - 1 / 2|) := by
      by_cases hd : 0 ≤ ρ.re - 1 / 2
      · rw [abs_of_nonneg hd]
      · rw [abs_of_nonpos (le_of_not_ge hd), mul_neg, Real.cosh_neg]
    rw [norm_mul, phase_norm, one_mul, hcast, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _)), hcosh]
  unfold coshCorrection
  calc
    _ ≤ realSum T (fun ρ =>
        ‖phase y ρ.im * ((Real.cosh (y * (ρ.re - 1 / 2)) : ℂ) - 1)‖) :=
      norm_sum_le T _
    _ = _ := by
      congr 1
      funext ρ
      exact hpoint ρ

/-- The unconditional norm reduction uses the already proved signed identity. -/
theorem norm_ordinate_sub_landau_le_full_coshSum (T y : ℝ) :
    ‖ordinateSum T y - landauSum T y‖ ≤
      realSum T (fun ρ => Real.cosh (y * |ρ.re - 1 / 2|) - 1) := by
  rw [ordinate_sub_landau_eq_neg_coshCorrection, norm_neg]
  exact norm_coshCorrection_le_full_coshSum T y

/-- The actual copies specialize the generic finite density transfer exactly.
The exponential `strictTail` estimate is the sole unproved analytic input. -/
theorem actual_full_coshSum_le_of_exponential_density
    (T C L y : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hL : 0 < L) (hy : 0 ≤ y) (hyL : y < L / 4)
    (hdensity : ∀ v ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T v ≤ 2 * C * T * L * Real.exp (-(L / 4) * v)) :
    realSum T (fun ρ => Real.cosh (y * |ρ.re - 1 / 2|) - 1) ≤
      2 * C * T * L * y ^ 2 / (L ^ 2 / 16 - y ^ 2) := by
  classical
  rw [realSum_eq_copies]
  change (∑ c ∈ (Finset.univ : Finset (Copies T)),
      (Real.cosh (y * copyDisplacement T c) - 1)) ≤ _
  apply finite_cosh_density_transfer _ _ C T L y hC hT hL hy hyL
  · intro c hc
    exact ⟨abs_nonneg _, (displacement_lt_half c.1.2).le⟩
  · intro v hv
    change strictTail T v ≤ _
    exact hdensity v hv

/-- Conditional scalar correction estimate for all actual zeros, with every
multiplicity retained and the exact horizontal correction identified first. -/
theorem actual_ordinate_landau_le_of_exponential_density
    (T C L y : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hL : 0 < L) (hy : 0 ≤ y) (hyL : y < L / 4)
    (hdensity : ∀ v ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T v ≤ 2 * C * T * L * Real.exp (-(L / 4) * v)) :
    ‖ordinateSum T y - landauSum T y‖ ≤
      2 * C * T * L * y ^ 2 / (L ^ 2 / 16 - y ^ 2) :=
  (norm_ordinate_sub_landau_le_full_coshSum T y).trans
    (actual_full_coshSum_le_of_exponential_density
      T C L y hC hT hL hy hyL hdensity)

/-- The explicit `128 C/3` actual scalar rate. The density provider remains
an explicit premise and is not asserted by this theorem. -/
theorem actual_ordinate_landau_density_eighth
    (T C L y : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hL : 0 < L) (hy : 0 ≤ y) (hyL : y ≤ L / 8)
    (hdensity : ∀ v ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T v ≤ 2 * C * T * L * Real.exp (-(L / 4) * v)) :
    ‖ordinateSum T y - landauSum T y‖ ≤
      (128 * C / 3) * T * y ^ 2 / L := by
  exact (actual_ordinate_landau_le_of_exponential_density
    T C L y hC hT hL hy (by linarith) hdensity).trans
      (density_rational_eighth hC hT hL hy hyL)

end RiemannResearch.Analysis.ActualZeroOrdinate
