import RiemannResearch.RH.ParetoMellinGramOptimization
import RiemannResearch.RH.ParetoMellinNonsingular
import RiemannResearch.RH.RamanujanMellinOptimization
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact complex one-point Mellin Schur update

Source: the user's third ten-transfer program, 23 October 2026.
The old target signature is arbitrary complex data. The update retains its
complete complex innovation. Invertibility hypotheses can be discharged by
the distinct-point Cauchy theorem; no zero-free assertion is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinAppend (s : ι → ℂ) (t : ℂ) : Option ι → ℂ :=
  fun i => i.elim t s

def mellinSchurCross (s : ι → ℂ) (t : ℂ) (i : ι) : ℂ :=
  mellinCauchyGram (mellinAppend s t) (some i) none

def mellinSchurCoefficients (s : ι → ℂ) (t : ℂ) : ι → ℂ :=
  mellinInverseCoefficients s (mellinSchurCross s t)

def mellinSchurResidual (s : ι → ℂ) (t : ℂ) : Option ι → ℂ :=
  mellinAppend (fun i => -mellinSchurCoefficients s t i) 1

def mellinSchurScalar (s : ι → ℂ) (t : ℂ) : ℂ :=
  mellinCauchyGram (mellinAppend s t) none none -
    ∑ i, mellinCauchyGram (mellinAppend s t) none (some i) *
      mellinSchurCoefficients s t i

def mellinSchurInnovation (s b : ι → ℂ) (t β : ℂ) : ℂ :=
  β - ∑ i, mellinCauchyGram (mellinAppend s t) none (some i) *
    mellinInverseCoefficients s b i

def mellinSchurUpdate (s b : ι → ℂ) (t β : ℂ) : Option ι → ℂ :=
  let δ := mellinSchurInnovation s b t β / mellinSchurScalar s t
  mellinAppend (fun i => mellinInverseCoefficients s b i -
    mellinSchurCoefficients s t i * δ) δ

theorem mellinInverseCoefficients_unique (s b c : ι → ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0)
    (hn : ∀ i, ∑ j, mellinCauchyGram s i j * c j = b i) :
    c = mellinInverseCoefficients s b := by
  have he : (mellinCauchyGram s).mulVec c = b := funext hn
  have h := congrArg (fun x => (mellinCauchyGram s)⁻¹.mulVec x) he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec] at h
  exact h

theorem mellinSchurResidual_normal (s : ι → ℂ) (t : ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    ∀ i, ∑ j, mellinCauchyGram (mellinAppend s t) i j *
      mellinSchurResidual s t j =
        mellinAppend (fun _ : ι => 0) (mellinSchurScalar s t) i := by
  intro i
  cases i with
  | none =>
    simp only [Fintype.sum_option, mellinSchurResidual, mellinAppend,
      Option.elim_none, Option.elim_some, mul_one, mul_neg, Finset.sum_neg_distrib]
    rfl
  | some i =>
    have h := mellinInverseCoefficients_normal s (mellinSchurCross s t) hdet i
    simpa only [Fintype.sum_option, mellinSchurResidual, mellinAppend,
      Option.elim_none, Option.elim_some, mul_one, mul_neg, Finset.sum_neg_distrib,
      mellinSchurCoefficients, mellinSchurCross, mellinCauchyGram,
      sub_eq_add_neg] using sub_eq_zero.mpr h.symm

theorem mellinSchurScalar_eq_quadratic (s : ι → ℂ) (t : ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    mellinSchurScalar s t =
      mellinGramQuadratic (mellinAppend s t) (mellinSchurResidual s t) := by
  rw [mellinGramQuadratic_eq_of_normal _ _ _ (mellinSchurResidual_normal s t hdet)]
  simp [Fintype.sum_option, mellinSchurResidual, mellinAppend]

theorem mellinSchurScalar_im (s : ι → ℂ) (t : ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    (mellinSchurScalar s t).im = 0 := by
  have h := mellinGramPairing_conj (mellinAppend s t)
    (mellinSchurResidual s t) (mellinSchurResidual s t)
  change starRingEnd ℂ (mellinGramQuadratic _ _) = mellinGramQuadratic _ _ at h
  rw [← mellinSchurScalar_eq_quadratic s t hdet] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith

theorem mellinSchurScalar_ne_zero (s : ι → ℂ) (t : ℂ)
    (hsmall : (mellinCauchyGram s).det ≠ 0)
    (hlarge : (mellinCauchyGram (mellinAppend s t)).det ≠ 0) :
    mellinSchurScalar s t ≠ 0 := by
  intro hz
  have hn := mellinSchurResidual_normal s t hsmall
  have he : (mellinCauchyGram (mellinAppend s t)).mulVec
      (mellinSchurResidual s t) = 0 := by
    funext i
    change (∑ j, mellinCauchyGram (mellinAppend s t) i j *
      mellinSchurResidual s t j) = 0
    rw [hn i]
    cases i <;> simp [mellinAppend, hz]
  have h := congrArg (fun x => (mellinCauchyGram (mellinAppend s t))⁻¹.mulVec x) he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hlarge), Matrix.one_mulVec, Matrix.mulVec_zero] at h
  have h0 := congrFun h none
  simpa [mellinSchurResidual, mellinAppend] using h0

theorem mellinSchurScalar_re_pos (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hsmall : (mellinCauchyGram s).det ≠ 0)
    (hlarge : (mellinCauchyGram (mellinAppend s t)).det ≠ 0) :
    0 < (mellinSchurScalar s t).re := by
  have hn : 0 ≤ (mellinSchurScalar s t).re := by
    rw [mellinSchurScalar_eq_quadratic s t hsmall, ← finiteMellinKernel_energy]
    · exact integral_nonneg (fun _ => sq_nonneg _)
    · intro i
      cases i with
      | none => exact ht
      | some i => exact hs i
  have hz : (mellinSchurScalar s t).re ≠ 0 := by
    intro he
    apply mellinSchurScalar_ne_zero s t hsmall hlarge
    apply Complex.ext
    · exact he
    · exact mellinSchurScalar_im s t hsmall
  exact lt_of_le_of_ne hn (Ne.symm hz)

theorem mellinSchurUpdate_normal (s b : ι → ℂ) (t β : ℂ)
    (hsmall : (mellinCauchyGram s).det ≠ 0)
    (hσ : mellinSchurScalar s t ≠ 0) :
    ∀ i, ∑ j, mellinCauchyGram (mellinAppend s t) i j *
      mellinSchurUpdate s b t β j = mellinAppend b β i := by
  let δ := mellinSchurInnovation s b t β / mellinSchurScalar s t
  have hσδ : mellinSchurScalar s t * δ = mellinSchurInnovation s b t β := by
    dsimp [δ]
    field_simp [hσ]
  intro i
  cases i with
  | none =>
    change (∑ j, mellinCauchyGram (mellinAppend s t) none j *
      mellinAppend (fun i => mellinInverseCoefficients s b i -
        mellinSchurCoefficients s t i * δ) δ j) = β
    simp only [Fintype.sum_option, mellinAppend, Option.elim_none, Option.elim_some,
      mul_sub, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.sum_mul]
    dsimp [mellinSchurScalar, mellinSchurInnovation] at hσδ
    linear_combination hσδ
  | some i =>
    have ha := mellinInverseCoefficients_normal s b hsmall i
    have hv := mellinInverseCoefficients_normal s (mellinSchurCross s t) hsmall i
    rw [Fintype.sum_option]
    change mellinSchurCross s t i * δ +
      (∑ j, mellinCauchyGram s i j *
        (mellinInverseCoefficients s b j - mellinSchurCoefficients s t j * δ)) = b i
    simp only [mul_sub, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.sum_mul,
      mellinSchurCoefficients]
    rw [ha, hv]
    ring

theorem mellinInverseCoefficients_append (s b : ι → ℂ) (t β : ℂ)
    (hsmall : (mellinCauchyGram s).det ≠ 0)
    (hlarge : (mellinCauchyGram (mellinAppend s t)).det ≠ 0) :
    mellinInverseCoefficients (mellinAppend s t) (mellinAppend b β) =
      mellinSchurUpdate s b t β :=
  (mellinInverseCoefficients_unique _ _ _ hlarge
    (mellinSchurUpdate_normal s b t β hsmall
      (mellinSchurScalar_ne_zero s t hsmall hlarge))).symm

theorem mellinSchur_cross_pairing (s b : ι → ℂ) (t : ℂ)
    (hsmall : (mellinCauchyGram s).det ≠ 0) :
    (∑ i, starRingEnd ℂ (mellinSchurCoefficients s t i) * b i) =
      ∑ i, mellinCauchyGram (mellinAppend s t) none (some i) *
        mellinInverseCoefficients s b i := by
  have ha := mellinInverseCoefficients_normal s b hsmall
  have hv := mellinInverseCoefficients_normal s (mellinSchurCross s t) hsmall
  have hc (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  calc
    _ = mellinGramPairing s (mellinSchurCoefficients s t)
        (mellinInverseCoefficients s b) :=
      (mellinGramPairing_eq_of_normal _ _ _ _ ha).symm
    _ = starRingEnd ℂ (mellinGramPairing s (mellinInverseCoefficients s b)
        (mellinSchurCoefficients s t)) :=
      (mellinGramPairing_conj _ _ _).symm
    _ = starRingEnd ℂ (∑ i, starRingEnd ℂ (mellinInverseCoefficients s b i) *
        mellinSchurCross s t i) := by
      unfold mellinSchurCoefficients
      rw [mellinGramPairing_eq_of_normal _ _ _ _ hv]
    _ = _ := by
      simp only [map_sum, map_mul, hc, mellinSchurCross, mellinCauchyGram_conj]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Complete complex innovation formula, valid for arbitrary target signatures. -/
theorem mellinInverseCapacity_schur_complex (s b : ι → ℂ) (t β : ℂ)
    (hsmall : (mellinCauchyGram s).det ≠ 0)
    (hlarge : (mellinCauchyGram (mellinAppend s t)).det ≠ 0) :
    mellinInverseCapacity (mellinAppend s t) (mellinAppend b β) =
      mellinInverseCapacity s b +
        (starRingEnd ℂ (mellinSchurInnovation s b t β / mellinSchurScalar s t) *
          mellinSchurInnovation s b t β).re := by
  let δ := mellinSchurInnovation s b t β / mellinSchurScalar s t
  have hc := mellinSchur_cross_pairing s b t hsmall
  have hdot : (∑ i, starRingEnd ℂ (mellinSchurUpdate s b t β i) *
      mellinAppend b β i) =
      (∑ i, starRingEnd ℂ (mellinInverseCoefficients s b i) * b i) +
        starRingEnd ℂ δ * mellinSchurInnovation s b t β := by
    change (∑ i, starRingEnd ℂ (mellinAppend
      (fun i => mellinInverseCoefficients s b i - mellinSchurCoefficients s t i * δ)
      δ i) * mellinAppend b β i) = _
    simp only [Fintype.sum_option, mellinAppend, Option.elim_none, Option.elim_some,
      map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
    have hf : (∑ i, starRingEnd ℂ (mellinSchurCoefficients s t i) *
        starRingEnd ℂ δ * b i) =
        starRingEnd ℂ δ * (∑ i, starRingEnd ℂ (mellinSchurCoefficients s t i) * b i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hf, hc]
    dsimp [mellinSchurInnovation]
    ring
  unfold mellinInverseCapacity
  rw [mellinInverseCoefficients_append s b t β hsmall hlarge, hdot, Complex.add_re]

theorem mellinInverseCapacity_schur (s b : ι → ℂ) (t β : ℂ)
    (hsmall : (mellinCauchyGram s).det ≠ 0)
    (hlarge : (mellinCauchyGram (mellinAppend s t)).det ≠ 0) :
    mellinInverseCapacity (mellinAppend s t) (mellinAppend b β) =
      mellinInverseCapacity s b +
        ‖mellinSchurInnovation s b t β‖ ^ 2 / (mellinSchurScalar s t).re := by
  rw [mellinInverseCapacity_schur_complex s b t β hsmall hlarge]
  congr 1
  have hreal : ((mellinSchurScalar s t).re : ℂ) = mellinSchurScalar s t := by
    apply Complex.ext
    · rfl
    · simpa using (mellinSchurScalar_im s t hsmall).symm
  rw [← hreal]
  calc
    _ = ((mellinSchurInnovation s b t β *
        starRingEnd ℂ (mellinSchurInnovation s b t β)) /
          ((mellinSchurScalar s t).re : ℂ)).re := by
      congr 1
      simp only [map_div₀, Complex.conj_ofReal]
      ring
    _ = _ := by rw [Complex.mul_conj]; simp [Complex.sq_norm]

theorem mellinInverseCapacity_schur_strict_iff (s b : ι → ℂ) (t β : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hsmall : (mellinCauchyGram s).det ≠ 0)
    (hlarge : (mellinCauchyGram (mellinAppend s t)).det ≠ 0) :
    mellinInverseCapacity s b <
      mellinInverseCapacity (mellinAppend s t) (mellinAppend b β) ↔
        mellinSchurInnovation s b t β ≠ 0 := by
  rw [mellinInverseCapacity_schur s b t β hsmall hlarge, lt_add_iff_pos_right,
    div_pos_iff_of_pos_right (mellinSchurScalar_re_pos s t hs ht hsmall hlarge),
    sq_pos_iff, norm_ne_zero_iff]

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A new actual zero contributes its exact screened innovation, while the
complete Mellin remainder of the enlarged certificate remains present. -/
theorem packet_zeroInverse_schur_energy_exact (z : ι → ℂ) (t : ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (htre : (1 / 2 : ℝ) < t.re)
    (hz1 : ∀ i, z i ≠ 1) (ht1 : t ≠ 1)
    (hz0 : ∀ i, riemannZeta (z i) = 0) (ht0 : riemannZeta t = 0)
    (hinj : Function.Injective z) (hnew : ∀ i, z i ≠ t) (n : ℕ) :
    1 - packetMass n = mellinInverseCapacity z (fun i => 1 / z i) +
      ‖mellinSchurInnovation z (fun i => 1 / z i) t (1 / t)‖ ^ 2 /
        (mellinSchurScalar z t).re +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel (mellinAppend z t)
            (mellinInverseCoefficients (mellinAppend z t)
              (mellinAppend (fun i => 1 / z i) (1 / t))) x)‖ ^ 2 := by
  have hsmall := (mellinCauchyGram_det_ne_zero_iff_injective z hzre).mpr hinj
  have hlarge : (mellinCauchyGram (mellinAppend z t)).det ≠ 0 := by
    apply (mellinCauchyGram_det_ne_zero_iff_injective _
      (by intro i; cases i with | none => exact htre | some i => exact hzre i)).mpr
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (hnew j hij.symm).elim
    | some i =>
      cases j with
      | none => exact (hnew i hij).elim
      | some j => exact congrArg some (hinj hij)
  have hsig : (fun i => 1 / mellinAppend z t i) =
      mellinAppend (fun i => 1 / z i) (1 / t) := by
    funext i
    cases i <;> rfl
  have h := packet_zeroInverse_energy_exact (mellinAppend z t)
    (by intro i; cases i with | none => exact htre | some i => exact hzre i)
    (by intro i; cases i with | none => exact ht1 | some i => exact hz1 i)
    (by intro i; cases i with | none => exact ht0 | some i => exact hz0 i)
    hlarge n
  rw [hsig, mellinInverseCapacity_schur z (fun i => 1 / z i) t (1 / t)
    hsmall hlarge] at h
  exact h

end RiemannResearch.RH.RamanujanZeroCertificates
