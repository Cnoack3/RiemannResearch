import RiemannResearch.RH.MellinModeTailCauchy
import RiemannResearch.RH.MellinModeEnergyBounds
import RiemannResearch.RH.ComplexTailCoercivity

set_option autoImplicit false

/-!
# Quantitative first-coordinate tail gap forced by an off-line zero

Source: user-provided signed tail-gap argument, 2026-09-21. The actual
Mellin-mode pairing and full tail-energy bound are supplied by the imported
modules. The result is conditional only on the stated actual zeta zero,
not on a separate analytic provider or a hypothetical certificate.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.Pareto.SpectralObstruction

/-- A universal pairing estimate on the genuine complex tail combinations
supplies a lower bound for the sharp real/complex arithmetic gap. -/
theorem firstCoordinateTailGap_ge_of_complex_pairing_bound
    (A B : ℝ) (hB : 0 < B)
    (hpair : ∀ (n : ℕ) (c : Fin n → ℂ),
      A * ‖complexReciprocalSource n c‖ ^ 2 ≤ B * ‖complexTailCombination n c‖ ^ 2) :
    A / B ≤ firstCoordinateTailGap := by
  apply complex_uniform_tail_constant_le_gap (A / B)
  intro n c
  calc
    (A / B) * ‖complexReciprocalSource n c‖ ^ 2 =
        (A * ‖complexReciprocalSource n c‖ ^ 2) / B := by ring
    _ ≤ ‖complexTailCombination n c‖ ^ 2 :=
      (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hpair n c)

/-- A numerical upper bound for the actual Mellin tail energy gives a lower
bound for the gap. Arithmetic orthogonality is supplied by the actual zero. -/
theorem firstCoordinateTailGap_ge_of_mellin_tail_energy_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (B : ℝ) (hB : 0 < B)
    (henergy : (∑' k : ℕ, paretoWeight (k + 1) * ‖mellinMode s (k + 1)‖ ^ 2) ≤ B) :
    ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / B ≤ firstCoordinateTailGap := by
  apply firstCoordinateTailGap_ge_of_complex_pairing_bound _ B hB
  intro n c
  exact (mellin_zero_tail_cauchy s hs hs1 hz n c).trans
    (mul_le_mul_of_nonneg_right henergy (sq_nonneg ‖complexTailCombination n c‖))

/-- The explicit sharp-cell lower bound forced by any actual right-half-strip
zeta zero. All signed coefficient directions are controlled simultaneously. -/
theorem firstCoordinateTailGap_lower_bound_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hsupper : s.re < 1)
    (hz : riemannZeta s = 0) :
    (2 * s.re - 1) * (2 : ℝ) ^ (2 * s.re - 1) *
        ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2 ≤ firstCoordinateTailGap := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsupper
    norm_num at hsupper
  have hp : 0 < 2 * s.re - 1 := by linarith
  have hsn : 0 < ‖s‖ ^ 2 := pow_pos (norm_pos_iff.mpr hs0) 2
  let B : ℝ := ‖s‖ ^ 2 * (2 : ℝ) ^ (1 - 2 * s.re) / (2 * s.re - 1)
  have hB : 0 < B := by
    exact div_pos (mul_pos hsn (Real.rpow_pos_of_pos (by norm_num) _)) hp
  have henergy : (∑' k : ℕ, paretoWeight (k + 1) *
      ‖mellinMode s (k + 1)‖ ^ 2) ≤ B := mellinMode_tail_energy_le s hs
  have hgap := firstCoordinateTailGap_ge_of_mellin_tail_energy_bound
    s hs hs1 hz B hB henergy
  have hpne : 2 * s.re - 1 ≠ 0 := hp.ne'
  have hsne : ‖s‖ ^ 2 ≠ 0 := hsn.ne'
  have hrne : (2 : ℝ) ^ (2 * s.re - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hpow : (2 : ℝ) ^ (1 - 2 * s.re) =
      ((2 : ℝ) ^ (2 * s.re - 1))⁻¹ := by
    rw [show 1 - 2 * s.re = -(2 * s.re - 1) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have he : ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / B =
      (2 * s.re - 1) * (2 : ℝ) ^ (2 * s.re - 1) *
        ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2 := by
    dsimp only [B]
    rw [hpow]
    field_simp [hpne, hsne, hrne]
    <;> ring
  rwa [he] at hgap

private theorem one_sub_two_cpow_ne_zero (s : ℂ) (hs : 0 < s.re) :
    1 - (2 : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have he : (2 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    simpa using (Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < 2 by norm_num) (-s))
  have hl : (2 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [he, norm_one] at hn
  linarith

/-- The explicit lower bound is strictly positive; no rate or zero-existence
claim is inferred from this conditional conclusion. -/
theorem firstCoordinateTailGap_pos_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hsupper : s.re < 1)
    (hz : riemannZeta s = 0) : 0 < firstCoordinateTailGap := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hA : 0 < ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (one_sub_two_cpow_ne_zero s (by linarith))) 2
  have hp : 0 < 2 * s.re - 1 := by linarith
  apply lt_of_lt_of_le _ (firstCoordinateTailGap_lower_bound_of_zeta_zero s hs hsupper hz)
  exact div_pos (mul_pos (mul_pos hp (Real.rpow_pos_of_pos (by norm_num) _)) hA)
    (pow_pos (norm_pos_iff.mpr hs0) 2)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
