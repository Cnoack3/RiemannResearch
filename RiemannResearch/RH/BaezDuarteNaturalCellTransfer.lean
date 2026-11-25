import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.ParetoNymanPointwise
import RiemannResearch.RH.StepCorrectionConstant
import RiemannResearch.RH.StepCorrectionContinuum
import RiemannResearch.RH.ThresholdHilbertAdjoint
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Exact reciprocal-cell transfer for finite natural-dilation approximants

Reciprocal substitution identifies the literal natural error with the full
continuum correction energy. This includes the exterior coefficient charge.
The sharp transfer factor for arbitrary physical Hilbert vectors therefore
applies to every finite natural-dilation approximant.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace RiemannResearch.RH.Pareto.BaezDuarte
open StepCorrectionNorm

private theorem natural_residual_inv (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) {x : ℝ} (hx : 0 < x) :
    chi x⁻¹ - naturalSum s a x⁻¹ =
      paretoStep (hilbertSequence (hilbertOne - finiteResidueSum s a)) x -
        naturalCharge s a * Int.fract x := by
  have hchi : chi x⁻¹ = hilbertSequence hilbertOne ⌊x⌋₊ := by
    rw [hilbertOne_sequence]
    by_cases h : 1 ≤ x
    · rw [chi_eq_one ⟨inv_pos.mpr hx, (inv_le_one₀ hx).mpr h⟩]
      simp [zeroAnchor, (Nat.floor_pos.mpr h).ne']
    · rw [chi_eq_zero_of_one_lt ((one_lt_inv₀ hx).mpr (lt_of_not_ge h))]
      simp [zeroAnchor, Nat.floor_eq_zero.mpr (lt_of_not_ge h)]
  rw [hchi, paretoStep, hilbertSequence_sub, Pi.sub_apply, finiteResidueSum_sequence s a hs,
    naturalSum, naturalCharge, Finset.sum_mul]
  have harith : (∑ d ∈ s, a d * Int.fract (1 / ((d : ℝ) * x⁻¹))) =
      (∑ d ∈ s, a d * (((⌊x⌋₊ % d : ℕ) : ℝ) / (d : ℝ))) +
      ∑ d ∈ s, a d / (d : ℝ) * Int.fract x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hfrac := fract_div_sub_fract_div_eq_floor_mod x hx.le d (hs d hd)
    rw [show 1 / ((d : ℝ) * x⁻¹) = x / d by simp [div_eq_mul_inv, mul_comm]]
    rw [← hfrac]
    ring
  rw [harith]
  ring

/-- Exact natural error, including the charge on the entire exterior interval. -/
theorem naturalError_eq_continuumCorrection (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    naturalError s a = ENNReal.ofReal (∫ x in Ioi 0, continuumCorrectionDensity
      (hilbertSequence (hilbertOne - finiteResidueSum s a)) (naturalCharge s a) x) := by
  let f := hilbertOne - finiteResidueSum s a
  let A := naturalCharge s a
  have himage : (fun x : ℝ => x⁻¹) '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Set.mem_Ioi.mpr (inv_pos.mpr (Set.mem_Ioi.mp hx))
    · intro hy
      exact ⟨y⁻¹, Set.mem_Ioi.mpr (inv_pos.mpr (Set.mem_Ioi.mp hy)), inv_inv _⟩
  have hsubst := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (f := fun x : ℝ => x⁻¹) (fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt)
    inv_injective.injOn (fun y => ENNReal.ofReal ((chi y - naturalSum s a y)^2))
  rw [himage] at hsubst
  have hh : Summable (fun n : ℕ => positiveWeight (n + 1) * (hilbertSequence f (n + 1))^2) := by
    simpa only [hilbertSequence_weighted_square] using hilbert_coordinate_square_summable f
  have hi := continuumCorrection_integrable (hilbertSequence f) (hilbertSequence_zero f) hh A
  change naturalError s a = ENNReal.ofReal (∫ x in Ioi 0,
    continuumCorrectionDensity (hilbertSequence f) A x)
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (continuumCorrectionDensity_nonneg _ _)), naturalError, hsubst]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [natural_residual_inv s a hs hx, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  dsimp only [continuumCorrectionDensity, f, A]
  rw [abs_neg, abs_of_nonneg (by positivity)]
  ring

/-- The finite Nyman error as a complete signed quadratic in its coefficient charge. -/
theorem naturalError_eq_charge_quadratic (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    let f := hilbertOne - finiteResidueSum s a
    let A := naturalCharge s a
    naturalError s a = ENNReal.ofReal (‖f‖^2 -
      2 * A * correctionSource (fun n => hilbertSequence f (n+1)) + A^2 * residueEnergy) := by
  dsimp only
  rw [naturalError_eq_continuumCorrection s a hs, continuumCorrection_hilbert]

/-- The complete centered error is controlled by the ambient correction factor. -/
theorem centeredError_le_correctionFactor (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    centeredError s a ≤ ENNReal.ofReal (residueEnergy / residualEnergy) * naturalError s a := by
  rw [centeredError_eq_hilbert_norm_sq s a hs, naturalError_eq_continuumCorrection s a hs,
    ← ENNReal.ofReal_mul (div_nonneg residueEnergy_pos.le
      (le_trans (by norm_num) residualEnergy_ge_one))]
  exact ENNReal.ofReal_le_ofReal (continuumCorrection_hilbert_transfer _ _)

/-- Using the first reciprocal cell and the full tail bound gives an explicit
uniform factor below six fifths for the squared energies. -/
theorem correctionFactor_lt_six_fifths : residueEnergy / residualEnergy < 6 / 5 := by
  have hm : cellMean 0 = 2 * Real.log 2 - 1 := by norm_num [cellMean]
  have hsmall : cellMean 0 < 387 / 1000 := by rw [hm]; linarith only [Real.log_two_lt_d9]
  have hsq := mul_self_lt_mul_self (cellMean_nonneg 0) hsmall
  have hprefix := (projectionEnergy_prefix_bracket 1).2
  norm_num [Finset.sum_range_succ, positiveWeight] at hprefix
  apply (div_lt_iff₀ (lt_trans zero_lt_one residualEnergy_gt_one)).2
  nlinarith only [hprefix, hsq, residualEnergy_eq, residualEnergy_gt_one]

/-- Adding conductor one allows the coefficient charge to vary independently
of every centered packet. Here `t` is the new coefficient of conductor one. -/
private theorem insert_one_charge_and_vector (s : Finset ℕ) (a : ℕ → ℝ)
    (h1 : 1 ∉ s) (t : ℝ) :
    naturalCharge (insert 1 s) (Function.update a 1 t) = t + naturalCharge s a ∧
    finiteResidueSum (insert 1 s) (Function.update a 1 t) = finiteResidueSum s a := by
  classical
  have hsame {d : ℕ} (hd : d ∈ s) : Function.update a 1 t d = a d :=
    Function.update_of_ne (show d ≠ 1 from fun he => h1 (he ▸ hd)) ..
  have hz : residueVector 1 = 0 := by
    apply hilbertSequence_injective
    rw [residueVector, dif_pos (by decide), normalizedResidueHilbert_sequence]
    change ArithmeticCumulative.residueFraction 1 = hilbertSequenceLinear 0
    rw [map_zero]
    funext k
    simp [ArithmeticCumulative.residueFraction, Nat.mod_one]
  constructor
  · unfold naturalCharge
    rw [Finset.sum_insert h1, Function.update_self]
    simp only [Nat.cast_one, div_one]
    congr 1
    exact Finset.sum_congr rfl (fun d hd => by rw [hsame hd])
  · unfold finiteResidueSum
    rw [Finset.sum_insert h1, hz, smul_zero, zero_add]
    exact Finset.sum_congr rfl (fun d hd => by rw [hsame hd])

/-- The realized optimal adjustment at conductor one and the full excess
quadratic for every other choice, in the actual natural-dilation error. -/
theorem naturalError_insert_one_completed_square (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (h1 : 1 ∉ s) (t : ℝ) :
    let f := hilbertOne - finiteResidueSum s a
    let S := correctionSource (fun n => hilbertSequence f (n + 1))
    let t₀ := S / residueEnergy - naturalCharge s a
    naturalError (insert 1 s) (Function.update a 1 t) =
      ENNReal.ofReal (‖f‖ ^ 2 - S ^ 2 / residueEnergy + residueEnergy * (t - t₀) ^ 2) := by
  dsimp only
  have hpos : ∀ d ∈ insert 1 s, 0 < d := by
    intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · decide
    · exact hs d hd
  obtain ⟨hQ, hV⟩ := insert_one_charge_and_vector s a h1 t
  rw [naturalError_eq_charge_quadratic _ _ hpos]
  rw [hQ, hV]
  congr 1
  field_simp [residueEnergy_pos.ne']
  ring

/-- Among all first coefficients the signed cell source picks an actual minimizer. -/
theorem naturalError_insert_one_minimum (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (h1 : 1 ∉ s) :
    let f := hilbertOne - finiteResidueSum s a
    let S := correctionSource (fun n => hilbertSequence f (n + 1))
    let t₀ := S / residueEnergy - naturalCharge s a
    naturalError (insert 1 s) (Function.update a 1 t₀) = ENNReal.ofReal (‖f‖^2 - S^2 / residueEnergy) ∧
      ∀ t, naturalError (insert 1 s) (Function.update a 1 t₀) ≤
        naturalError (insert 1 s) (Function.update a 1 t) := by
  dsimp only
  constructor
  · rw [naturalError_insert_one_completed_square s a hs h1]
    simp
  · intro t
    rw [naturalError_insert_one_completed_square s a hs h1,
      naturalError_insert_one_completed_square s a hs h1]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right
      (mul_nonneg residueEnergy_pos.le (sq_nonneg _)))

end RiemannResearch.RH.Pareto.BaezDuarte
