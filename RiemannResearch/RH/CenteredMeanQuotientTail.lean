import RiemannResearch.RH.CenteredMeanQuotientNorm
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ParetoWeights
import RiemannResearch.RH.ParetoStretchedAnnihilatorTail
import RiemannResearch.RH.ResidualTailPNT
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tail criterion for the metric comparison of mean-zero quotients

The sum of the coordinate losses beyond a physical cutoff is the squared
tail norm of the centered boundary vector divided by its normalization.
The canonical residual is an affine function of that vector. Its established
cofinal tail criterion therefore applies to the metric comparison itself.
-/

noncomputable section
open Filter

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization

local notation "Φ" => boundaryTargetContinuousEquivLegalQuotient

/-- The complete remaining loss from centered coordinate classes after the first
`N` physical sites. -/
def coordinateLossTail (N : ℕ) : ℝ :=
  ∑' n : ℕ, (‖centeredCoordinateClass (n + N)‖ ^ 2 -
    ‖Φ (centeredCoordinateClass (n + N))‖ ^ 2)

theorem coordinateLossTail_eq (N : ℕ) :
    coordinateLossTail N = ‖hilbertTailShift defect.val N‖ ^ 2 / (1 + ‖defect‖ ^ 2) := by
  simp only [coordinateLossTail, coordinate_quotient_norm_loss, tsum_div_const, hilbert_norm_sq]
  <;> rfl

theorem tailShift_one_norm_sq (N : ℕ) :
    ‖hilbertTailShift hilbertOne N‖ ^ 2 = 1 / ((N : ℝ) + 1) := by
  have hv (n : ℕ) : (hilbertOne n) ^ 2 = paretoWeight n := by
    simpa only [positiveWeight_succ, hilbertOne_sequence, zeroAnchor, Nat.succ_ne_zero,
      if_false, one_pow, mul_one] using (hilbertSequence_weighted_square hilbertOne n).symm
  simp only [hilbertTailShift_norm_sq, hilbertOne_norm_sq, hv, paretoWeight_partial_sum]
  ring

private theorem tailShift_residual_decomposition (N : ℕ) :
    hilbertTailShift limitResidual N = limitEnergy • hilbertTailShift hilbertOne N -
      (1 - limitEnergy) • hilbertTailShift defect.val N := by
  have hr : limitResidual = hilbertOne - (1 - limitEnergy) • normalizedScreenedTwo := by
    rw [limitResidual, limitProjection_eq_scaled_screenedTwo]
  ext n
  change limitResidual (n + N) = limitEnergy * hilbertOne (n + N) -
    (1 - limitEnergy) * (normalizedScreenedTwo (n + N) - hilbertOne (n + N))
  rw [hr]
  change hilbertOne (n + N) - (1 - limitEnergy) * normalizedScreenedTwo (n + N) = _
  ring

/-- Exact residual-tail expansion. The signed cross term captures the interaction
between the Pareto constant and the remaining centered coordinate losses. -/
theorem residualTailEnergy_eq_coordinateLossTail (N : ℕ) :
    residualTailEnergy N = limitEnergy ^ 2 / ((N : ℝ) + 1) -
      2 * limitEnergy * (1 - limitEnergy) *
        inner ℝ (hilbertTailShift hilbertOne N) (hilbertTailShift defect.val N) +
      (1 - limitEnergy) ^ 2 * (1 + ‖defect‖ ^ 2) * coordinateLossTail N := by
  have ht : (1 + ‖defect‖ ^ 2) * coordinateLossTail N = ‖hilbertTailShift defect.val N‖ ^ 2 := by
    rw [coordinateLossTail_eq]
    field_simp [show 1 + ‖defect‖ ^ 2 ≠ 0 by positivity]
  rw [mul_assoc ((1 - limitEnergy) ^ 2), ht, residualTailEnergy,
    tailShift_residual_decomposition, norm_sub_sq_real, real_inner_smul_left,
    real_inner_smul_right, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, tailShift_one_norm_sq]
  ring

private theorem normalized_residualTailEnergy_le (N : ℕ) :
    (N : ℝ) * residualTailEnergy N ≤ 2 * limitEnergy ^ 2 +
      2 * (1 - limitEnergy) ^ 2 * (1 + ‖defect‖ ^ 2) * ((N : ℝ) * coordinateLossTail N) := by
  let a := limitEnergy • hilbertTailShift hilbertOne N
  let b := (1 - limitEnergy) • hilbertTailShift defect.val N
  have htri := sq_le_sq₀ (norm_nonneg (a - b)) (add_nonneg (norm_nonneg a) (norm_nonneg b))
  have h : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith only [htri.mpr (norm_sub_le a b), sq_nonneg (‖a‖ - ‖b‖)]
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  change (N : ℝ) * ‖a - b‖ ^ 2 ≤ _ at hm
  have ha : ‖a‖ ^ 2 = limitEnergy ^ 2 / ((N : ℝ) + 1) := by
    simp only [a, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, tailShift_one_norm_sq]
    ring
  have hb : ‖b‖ ^ 2 = (1 - limitEnergy) ^ 2 * ((1 + ‖defect‖ ^ 2) * coordinateLossTail N) := by
    simp only [b, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, coordinateLossTail_eq]
    field_simp [show 1 + ‖defect‖ ^ 2 ≠ 0 by positivity]
  rw [ha, hb] at hm
  have hfirst : (N : ℝ) * (limitEnergy ^ 2 / ((N : ℝ) + 1)) ≤ limitEnergy ^ 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith only [sq_nonneg limitEnergy]
  change (N : ℝ) * ‖hilbertTailShift limitResidual N‖ ^ 2 ≤ _
  rw [tailShift_residual_decomposition]
  change (N : ℝ) * ‖a - b‖ ^ 2 ≤ _
  linarith only [hm, hfirst]

/-- Bounded normalized complete loss along any cofinal sequence of cutoffs
suffices to annihilate the centered boundary. -/
theorem boundary_zero_iff_frequently_bounded_coordinateLossTail :
    boundary = 0 ↔ ∃ C : ℝ, ∃ᶠ N : ℕ in atTop, (N : ℝ) * coordinateLossTail N ≤ C := by
  constructor
  · intro hb
    have he := boundary_zero_iff_coordinate_norms.mp hb
    refine ⟨0, (Eventually.of_forall fun N => ?_).frequently⟩
    simp [coordinateLossTail, he]
  · rintro ⟨C, hC⟩
    have hr := limitResidual_eq_zero_iff_frequently_bounded_normalized_tail.mpr
      ⟨2 * limitEnergy ^ 2 + 2 * (1 - limitEnergy) ^ 2 * (1 + ‖defect‖ ^ 2) * C,
       hC.mono (fun N hN => (normalized_residualTailEnergy_le N).trans
         (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hN (by positivity))))⟩
    exact boundary_eq_zero_iff_one_mem.mpr (limitEnergy_zero_iff_mem.mp
      (limitResidual_zero_iff_energy_zero.mp hr))

/-- Conditional RH reduction using the observable squared losses on centered
coordinate classes. The single remaining hypothesis is the cofinal tail bound. -/
theorem riemannHypothesis_of_frequently_bounded_coordinateLossTail (C : ℝ)
    (hC : ∃ᶠ N : ℕ in atTop, (N : ℝ) * coordinateLossTail N ≤ C) : RiemannHypothesis :=
  riemannHypothesis_of_boundary_eq_zero
    (boundary_zero_iff_frequently_bounded_coordinateLossTail.mpr ⟨C, hC⟩)

open RiemannResearch.Analysis in
/-- At one positive exponent the Möbius energy estimate permits a stretched
factor of slack in the cofinal tail budget. Both the exponent and this implication
are unconditional. An actual cofinal upper bound remains an arithmetic input. -/
theorem exists_boundary_zero_of_stretched_coordinateLossTail :
    ∃ b : ℝ, 0 < b ∧ ∀ C : ℝ,
      (∃ᶠ N : ℕ in atTop, (N : ℝ) * Real.exp (-b * logProductPower (1 / 11)
        (6 + Real.log (N : ℝ))) * coordinateLossTail N ≤ C) → boundary = 0 := by
  obtain ⟨b, hb, hz⟩ := exists_annihilator_inner_one_eq_zero_of_frequently_bounded_stretched_tail
  refine ⟨b, hb, fun C hC => ?_⟩
  apply boundary_eq_zero_iff_one_mem.mpr
  apply limitEnergy_zero_iff_mem.mp
  rw [← limitResidual_inner_one]
  apply hz limitResidual limitResidual_mem_orthogonal
    (2 * limitEnergy ^ 2 + 2 * (1 - limitEnergy) ^ 2 * (1 + ‖defect‖ ^ 2) * C)
  apply (hC.and_eventually (eventually_ge_atTop (1 : ℕ))).mono
  rintro N ⟨hN, hNpos⟩
  let w := Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))
  have hw : 0 ≤ w := (Real.exp_pos _).le
  have hw1 : w ≤ 1 := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn
    have hφ : 0 ≤ logProductPower (1 / 11) (6 + Real.log (N : ℝ)) :=
      (Real.rpow_nonneg (by linarith) _).trans (logProductPower_lower _ (by norm_num) (by linarith))
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) hφ)
  have h := mul_le_mul_of_nonneg_left (normalized_residualTailEnergy_le N) hw
  have hconst := mul_le_mul_of_nonneg_right hw1 (show 0 ≤ 2 * limitEnergy ^ 2 by positivity)
  let A := 2 * (1 - limitEnergy) ^ 2 * (1 + ‖defect‖ ^ 2)
  have hvar := mul_le_mul_of_nonneg_left hN (show 0 ≤ A by dsimp only [A]; positivity)
  change A * ((N : ℝ) * w * coordinateLossTail N) ≤ A * C at hvar
  change (N : ℝ) * w * residualTailEnergy N ≤ 2 * limitEnergy ^ 2 + A * C
  change w * ((N : ℝ) * residualTailEnergy N) ≤
    w * (2 * limitEnergy ^ 2 + A * ((N : ℝ) * coordinateLossTail N)) at h
  linarith only [h, hconst, hvar]

open RiemannResearch.Analysis in
/-- The stretched loss-tail budget implies Mathlib's RH without a converse assumption. -/
theorem exists_riemannHypothesis_of_stretched_coordinateLossTail :
    ∃ b : ℝ, 0 < b ∧ ∀ C : ℝ,
      (∃ᶠ N : ℕ in atTop, (N : ℝ) * Real.exp (-b * logProductPower (1 / 11)
        (6 + Real.log (N : ℝ))) * coordinateLossTail N ≤ C) → RiemannHypothesis := by
  obtain ⟨b, hb, hz⟩ := exists_boundary_zero_of_stretched_coordinateLossTail
  exact ⟨b, hb, fun C h => riemannHypothesis_of_boundary_eq_zero (hz C h)⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
