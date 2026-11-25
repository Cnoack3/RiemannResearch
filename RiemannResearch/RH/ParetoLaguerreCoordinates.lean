import RiemannResearch.RH.ActualLaguerreParseval
import RiemannResearch.RH.ThresholdHilbertSpace

/-! # Laguerre coordinates on the complete Pareto Hilbert space -/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open RiemannResearch.Analysis

private theorem hilbertLift_square_integral (f : ThresholdHilbert) :
    (∫ t in Set.Ici (0 : ℝ), exponentialLift (hilbertSequence f) t ^ 2 * Real.exp (-t)) =
      ‖f‖ ^ 2 :=
  (exponentialLift_square_identity _ (hilbertSequence_square_summable f)).trans
    (hilbert_norm_weighted_sq f).symm

private theorem memLp_hilbertLift (f : ThresholdHilbert) :
    MemLp (exponentialLift (hilbertSequence f)) 2 laguerreMeasure := by
  apply (memLp_two_iff_integrable_sq
    (exponentialLift_measurable (hilbertSequence f)).aestronglyMeasurable).2
  rw [integrable_laguerreMeasure_iff]
  by_cases hf : f = 0
  · subst f
    have hz : hilbertSequence (0 : ThresholdHilbert) = 0 := hilbertSequenceLinear.map_zero
    simp [hz, exponentialLift]
  · by_contra hi
    have h := hilbertLift_square_integral f
    rw [integral_undef hi] at h
    exact (sq_pos_of_pos (norm_pos_iff.mpr hf)).ne' h.symm

private def liftLp (f : ThresholdHilbert) : LaguerreL2 :=
  (memLp_hilbertLift f).toLp (exponentialLift (hilbertSequence f))

private theorem liftLp_ae (f : ThresholdHilbert) :
    (liftLp f : ℝ → ℝ) =ᵐ[laguerreMeasure] exponentialLift (hilbertSequence f) :=
  (memLp_hilbertLift f).coeFn_toLp

/-- Embed the whole discrete Pareto Hilbert space as exponential step functions. -/
def laguerreRealization : ThresholdHilbert →ₗᵢ[ℝ] LaguerreL2 where
  toFun := liftLp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [liftLp_ae (f + g), liftLp_ae f, liftLp_ae g,
      Lp.coeFn_add (liftLp f) (liftLp g)] with t hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply, hf, hg, exponentialLift]
    exact congrFun (hilbertSequenceLinear.map_add f g) _
  map_smul' a f := by
    dsimp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [liftLp_ae (a • f), liftLp_ae f,
      Lp.coeFn_smul a (liftLp f)] with t haf hf ha
    rw [haf, ha]
    simp only [Pi.smul_apply, hf, exponentialLift]
    exact congrFun (hilbertSequenceLinear.map_smul a f) _
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(memLp_hilbertLift f).toLp (exponentialLift (hilbertSequence f))‖ ^ 2 = ‖f‖ ^ 2
    rw [norm_toLp_sq_laguerreMeasure, hilbertLift_square_integral]

/-- The realized function equals the exponential step profile almost everywhere. -/
theorem laguerreRealization_ae (f : ThresholdHilbert) :
    (laguerreRealization f : ℝ → ℝ) =ᵐ[laguerreMeasure] exponentialLift (hilbertSequence f) :=
  liftLp_ae f

/-- A Laguerre coordinate, including on unbounded Pareto vectors. -/
def laguerreReadout (j : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  (innerSL ℝ (laguerreVector j)).comp laguerreRealization.toContinuousLinearMap

theorem readout_coeff (j : ℕ) (f : ThresholdHilbert) :
    laguerreReadout j f = coefficient (hilbertSequence f) j := by
  change inner ℝ (laguerreVector j) (liftLp f) = _
  rw [real_inner_comm]
  exact (coefficient_eq_inner_exponentialLift (memLp_hilbertLift f) j).symm

theorem readout_bound (j : ℕ) (f : ThresholdHilbert) :
    |laguerreReadout j f| ≤ ‖f‖ := by
  change |inner ℝ (laguerreVector j) (laguerreRealization f)| ≤ ‖f‖
  simpa only [Real.norm_eq_abs, laguerreVector_orthonormal.1 j,
    laguerreRealization.norm_map, one_mul] using
    (norm_inner_le_norm (𝕜 := ℝ) (laguerreVector j) (laguerreRealization f))

/-- Parseval holds on the complete Pareto Hilbert space. -/
theorem hasSum_readout_sq (f : ThresholdHilbert) :
    HasSum (fun j => (laguerreReadout j f) ^ 2) (‖f‖ ^ 2) := by
  have h := hasSum_laguerre_inner_sq (laguerreRealization f)
  have he (j : ℕ) : inner ℝ (laguerreRealization f) (laguerreVector j) =
      laguerreReadout j f := real_inner_comm _ _
  simpa only [he, laguerreRealization.norm_map] using h

theorem laguerreCoordinates_ext {f g : ThresholdHilbert}
    (h : ∀ j, laguerreReadout j f = laguerreReadout j g) : f = g := by
  have hz (j : ℕ) : laguerreReadout j (f - g) = 0 := by rw [map_sub, h j, sub_self]
  have he := (hasSum_readout_sq (f - g)).tsum_eq
  simp only [hz, zero_pow (by decide : 2 ≠ 0), tsum_zero] at he
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm))

/--
info: 'RiemannResearch.RH.Pareto.RamanujanLaguerre.hasSum_readout_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hasSum_readout_sq

end RiemannResearch.RH.Pareto.RamanujanLaguerre
