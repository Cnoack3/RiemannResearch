import RiemannResearch.RH.ParetoMellinSchurProduct
import RiemannResearch.RH.ParetoMellinSourcePerturbation

/-!
# Exact innovation accounting for complete Mellin remainders

Source: the user's fifth Ramanujan transfer program, October 2026.
Every new probe splits the full old integral remainder into its explicit
Schur gain and the full new integral remainder. Source perturbations retain
both complex innovations and their signed cross term.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinProjectionRemainder (f : ThresholdHilbert) (s : ι → ℂ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), ‖mellinWeightedStep f x - starRingEnd ℂ
    (finiteMellinKernel s (mellinInverseCoefficients s (fun i => paretoMellin f (s i))) x)‖ ^ 2

theorem mellinProjectionRemainder_nonneg (f : ThresholdHilbert) (s : ι → ℂ) :
    0 ≤ mellinProjectionRemainder f s := integral_nonneg (fun _ => sq_nonneg _)

theorem mellinSchurInnovation_sub_source (s b e : ι → ℂ) (t β η : ℂ) :
    mellinSchurInnovation s (b - e) t (β - η) =
      mellinSchurInnovation s b t β - mellinSchurInnovation s e t η := by
  simp only [mellinSchurInnovation, mellinInverseCoefficients_sub_source,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

/-- The whole complex correction survives before taking any absolute-value bound. -/
theorem mellinSchurInnovation_sub_source_norm_sq (s b e : ι → ℂ) (t β η : ℂ) :
    ‖mellinSchurInnovation s (b - e) t (β - η)‖ ^ 2 =
      ‖mellinSchurInnovation s b t β‖ ^ 2 +
      ‖mellinSchurInnovation s e t η‖ ^ 2 -
      2 * (mellinSchurInnovation s b t β *
        starRingEnd ℂ (mellinSchurInnovation s e t η)).re := by
  rw [mellinSchurInnovation_sub_source]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Full remainder accounting for every physical Hilbert vector and every new probe. -/
theorem mellinProjectionRemainder_append (f : ThresholdHilbert) (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    mellinProjectionRemainder f s =
      (2 * t.re - 1) *
        ‖mellinSchurInnovation s (fun i => paretoMellin f (s i)) t (paretoMellin f t)‖ ^ 2 /
          mellinCenteredProduct s t +
      mellinProjectionRemainder f (mellinAppend s t) := by
  have hs' : ∀ i, (1 / 2 : ℝ) < (mellinAppend s t i).re := by
    intro i
    cases i with
    | none => exact ht
    | some i => exact hs i
  have hd := (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  have hd' := mellinCauchyGram_append_det_ne_zero s t hs ht hinj hnew
  have h := finiteMellinKernel_inverse_completion f s hs hd
  have h' := finiteMellinKernel_inverse_completion f (mellinAppend s t) hs' hd'
  change ‖f‖ ^ 2 = _ + mellinProjectionRemainder f s at h
  change ‖f‖ ^ 2 = _ + mellinProjectionRemainder f (mellinAppend s t) at h'
  have he : (fun i => paretoMellin f (mellinAppend s t i)) =
      mellinAppend (fun i => paretoMellin f (s i)) (paretoMellin f t) := by
    funext i
    cases i <;> rfl
  rw [he, mellinInverseCapacity_append_product s _ t _ hs ht hinj hnew] at h'
  linarith

theorem mellinProjectionRemainder_append_le (f : ThresholdHilbert) (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    mellinProjectionRemainder f (mellinAppend s t) ≤ mellinProjectionRemainder f s := by
  have h := mellinProjectionRemainder_append f s t hs ht hinj hnew
  have hg : 0 ≤ (2 * t.re - 1) *
      ‖mellinSchurInnovation s (fun i => paretoMellin f (s i)) t (paretoMellin f t)‖ ^ 2 /
        mellinCenteredProduct s t := by
    exact div_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mellinCenteredProduct_pos s t hs ht hnew).le
  linarith

theorem mellinProjectionRemainder_append_lt_iff (f : ThresholdHilbert)
    (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    mellinProjectionRemainder f (mellinAppend s t) < mellinProjectionRemainder f s ↔
      mellinSchurInnovation s (fun i => paretoMellin f (s i)) t (paretoMellin f t) ≠ 0 := by
  have h := mellinProjectionRemainder_append f s t hs ht hinj hnew
  constructor
  · intro hlt hz
    rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div, zero_add] at h
    exact (ne_of_lt hlt) h.symm
  · intro hn
    have hp : 0 < (2 * t.re - 1) *
        ‖mellinSchurInnovation s (fun i => paretoMellin f (s i)) t (paretoMellin f t)‖ ^ 2 /
          mellinCenteredProduct s t :=
      div_pos (mul_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hn)))
        (mellinCenteredProduct_pos s t hs ht hnew)
    linarith

end RiemannResearch.RH.Pareto
