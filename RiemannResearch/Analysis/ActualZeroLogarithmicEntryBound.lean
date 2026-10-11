import RiemannResearch.Analysis.ActualZeroDensityTransfer
import RiemannResearch.Analysis.ActualUniformRationalLandau
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional logarithmic entry bounds for the actual zeta-zero ordinate sums

The centered rational Landau provider used below is already proved for the
actual zeta zeros. The only analytic input in the resulting ordinate estimate
is the explicitly stated exponential bound on the actual `strictTail`.

The signed coefficient is `-rationalLandauMain n m`. No prime-power term is
discarded, and the exact signed horizontal correction is retained before the
triangle inequality. The actual Landau envelope is coarser than the sharp
Ford--Meng--Zaharescu paper envelope, but is sufficient for logarithmic supports.

-/

noncomputable section
open Set

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def rationalLandauRpowEnvelope (T X : ℝ) : ℝ :=
  X ^ (5 / 2 : ℝ) + X ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
    X * Real.log (T + 3)

/-- A supplied centered Landau bound and the explicit actual density premise
give the normalized ordinate entry bound. The coefficient has its negative
Landau sign; the complete signed horizontal correction is used first. -/
theorem normalized_actual_rational_entry_le_of_density_and_landau
    (T X L C_D C_A : ℝ) (n m : ℕ)
    (hT : 0 < T) (hC_D : 0 ≤ C_D) (hL : 0 < L)
    (hy : 0 ≤ Real.log ((n : ℝ) / (m : ℝ)))
    (hyL : Real.log ((n : ℝ) / (m : ℝ)) ≤ L / 8)
    (hdensity : ∀ v ∈ Icc (0 : ℝ) (1 / 2),
      strictTail T v ≤ 2 * C_D * T * L * Real.exp (-(L / 4) * v))
    (hlandau :
      ‖landauSum T (Real.log ((n : ℝ) / (m : ℝ))) +
          ((T * rationalLandauMain n m : ℝ) : ℂ)‖ ≤
        C_A * rationalLandauRpowEnvelope T X) :
    ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) -
        (-(rationalLandauMain n m : ℂ))‖ ≤
      (128 * C_D / 3) * (Real.log ((n : ℝ) / (m : ℝ))) ^ 2 / L +
        (C_A / T) * rationalLandauRpowEnvelope T X := by
  let y : ℝ := Real.log ((n : ℝ) / (m : ℝ))
  have hcorrect : ‖coshCorrection T y‖ ≤ (128 * C_D / 3) * T * y ^ 2 / L := by
    have h := actual_ordinate_landau_density_eighth
      T C_D L y hC_D hT.le hL hy hyL hdensity
    simpa only [ordinate_sub_landau_eq_neg_coshCorrection, norm_neg] using h
  have hsigned : ordinateSum T y + ((T * rationalLandauMain n m : ℝ) : ℂ) =
      (landauSum T y + ((T * rationalLandauMain n m : ℝ) : ℂ)) -
        coshCorrection T y := by
    rw [exact_signed_correction]
    ring
  have hraw :
      ‖ordinateSum T y + ((T * rationalLandauMain n m : ℝ) : ℂ)‖ ≤
        C_A * rationalLandauRpowEnvelope T X +
          (128 * C_D / 3) * T * y ^ 2 / L := by
    rw [hsigned]
    exact (norm_sub_le _ _).trans (add_le_add hlandau hcorrect)
  have hTne : T ≠ 0 := ne_of_gt hT
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hTne
  have hnormalize :
      ordinateSum T y / (T : ℂ) - (-(rationalLandauMain n m : ℂ)) =
        (ordinateSum T y + ((T * rationalLandauMain n m : ℝ) : ℂ)) / (T : ℂ) := by
    push_cast
    field_simp [hTc]
    <;> ring
  change ‖ordinateSum T y / (T : ℂ) - (-(rationalLandauMain n m : ℂ))‖ ≤ _
  rw [hnormalize, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ (C_A * rationalLandauRpowEnvelope T X +
        (128 * C_D / 3) * T * y ^ 2 / L) / T :=
      div_le_div_of_nonneg_right hraw hT.le
    _ = (128 * C_D / 3) * y ^ 2 / L +
        (C_A / T) * rationalLandauRpowEnvelope T X := by
      field_simp [hTne, (ne_of_gt hL : L ≠ 0)]
      <;> ring

/-- The Landau constant is supplied by the unconditional actual-zero theorem.
Only the exponential density bound remains an analytic premise. -/
theorem exists_uniform_actual_rational_entry_bound_of_exponential_density :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (T X L C_D : ℝ) (n m : ℕ),
      9 ≤ T → 1 ≤ m → m < n → (n : ℝ) ≤ X →
      0 ≤ C_D → 0 < L →
      Real.log ((n : ℝ) / (m : ℝ)) ≤ L / 8 →
      (∀ v ∈ Icc (0 : ℝ) (1 / 2),
        strictTail T v ≤ 2 * C_D * T * L * Real.exp (-(L / 4) * v)) →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) -
          (-(rationalLandauMain n m : ℂ))‖ ≤
        (128 * C_D / 3) * (Real.log ((n : ℝ) / (m : ℝ))) ^ 2 / L +
          (C_A / T) * rationalLandauRpowEnvelope T X := by
  obtain ⟨C_A, hC_A, hlandau⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C_A, hC_A, ?_⟩
  intro T X L C_D n m hT hm hmn hnX hC_D hL hyL hdensity
  have hy : 0 < Real.log ((n : ℝ) / (m : ℝ)) :=
    (rational_frequency_bounds hm hmn hnX).1
  exact normalized_actual_rational_entry_le_of_density_and_landau
    T X L C_D C_A n m (by linarith) hC_D hL hy.le hyL hdensity
    (hlandau T X n m hT hm hmn hnX)

/-- Set `L = log T`; a support bound `log X ≤ log T/8` discharges every
rational frequency bound uniformly. The tail estimate is still explicit. -/
theorem exists_uniform_actual_logarithmic_entry_bound_of_exponential_density :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (T X C_D : ℝ) (n m : ℕ),
      9 ≤ T → 1 ≤ m → m < n → (n : ℝ) ≤ X → 0 ≤ C_D →
      Real.log X ≤ Real.log T / 8 →
      (∀ v ∈ Icc (0 : ℝ) (1 / 2),
        strictTail T v ≤ 2 * C_D * T * Real.log T *
          Real.exp (-(Real.log T / 4) * v)) →
      ‖ordinateSum T (Real.log ((n : ℝ) / (m : ℝ))) / (T : ℂ) -
          (-(rationalLandauMain n m : ℂ))‖ ≤
        (128 * C_D / 3) * (Real.log ((n : ℝ) / (m : ℝ))) ^ 2 / Real.log T +
          (C_A / T) * rationalLandauRpowEnvelope T X := by
  obtain ⟨C_A, hC_A, hentry⟩ :=
    exists_uniform_actual_rational_entry_bound_of_exponential_density
  refine ⟨C_A, hC_A, ?_⟩
  intro T X C_D n m hT hm hmn hnX hC_D hX hdensity
  have hL : 0 < Real.log T := Real.log_pos (by linarith : 1 < T)
  have hyX : Real.log ((n : ℝ) / (m : ℝ)) ≤ Real.log X :=
    (rational_frequency_bounds hm hmn hnX).2.1
  exact hentry T X (Real.log T) C_D n m hT hm hmn hnX hC_D hL
    (hyX.trans hX) hdensity

end RiemannResearch.Analysis.ActualZeroOrdinate
