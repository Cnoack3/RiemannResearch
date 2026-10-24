import RiemannResearch.RH.ParetoMellinSchur
import RiemannResearch.RH.ParetoMellinCenteredProduct
import RiemannResearch.LinearAlgebra.OptionSchurDeterminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Closed finite products for the Mellin Schur denominator

Source: user-requested fourth Ramanujan transfer program, October 2026.
The centered Cauchy product eliminates the inverse matrix from the Schur
denominator. The exact scalar formula permits the new point to repeat an
old point; it then gives zero. Coefficient and capacity updates use the
nonrepeated-point branch and retain the complete complex innovation.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mellinCenteredProduct_pos (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hnew : ∀ i, s i ≠ t) : 0 < mellinCenteredProduct s t := by
  unfold mellinCenteredProduct
  apply Finset.prod_pos
  intro i _
  have hden : t + starRingEnd ℂ (s i) - 1 ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re,
      Complex.one_re, Complex.zero_re] at h
    linarith [hs i]
  exact sq_pos_of_pos (norm_pos_iff.mpr
    (div_ne_zero (sub_ne_zero.mpr (Ne.symm (hnew i))) hden))

theorem mellinCenteredProduct_eq_zero_of_mem (s : ι → ℂ) (t : ℂ)
    (hmem : ∃ i, s i = t) : mellinCenteredProduct s t = 0 := by
  obtain ⟨i, hi⟩ := hmem
  unfold mellinCenteredProduct
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [hi, sub_self, zero_div, norm_zero, zero_pow (by decide : 2 ≠ 0)]

theorem mellinCenteredProduct_eq_zero_iff (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re) :
    mellinCenteredProduct s t = 0 ↔ ∃ i, s i = t := by
  constructor
  · intro hz
    by_contra hmem
    have hnew : ∀ i, s i ≠ t := fun i hi => hmem ⟨i, hi⟩
    have hp := mellinCenteredProduct_pos s t hs ht hnew
    linarith
  · exact mellinCenteredProduct_eq_zero_of_mem s t

/-- The scalar formula remains valid when the appended point repeats a test. -/
theorem mellinSchurScalar_re_product (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) :
    (mellinSchurScalar s t).re = mellinCenteredProduct s t / (2 * t.re - 1) := by
  have hdet := (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  have hdot : mellinInverseCapacity s (mellinSchurCross s t) =
      (∑ i, mellinCauchyGram (mellinAppend s t) none (some i) *
        mellinSchurCoefficients s t i).re := by
    exact congrArg Complex.re
      (mellinSchur_cross_pairing s (mellinSchurCross s t) t hdet)
  have hreal : t + starRingEnd ℂ t - 1 = ((2 * t.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.conj_re,
        Complex.one_re, Complex.ofReal_re]
      ring
    · simp only [Complex.sub_im, Complex.add_im, Complex.conj_im,
        Complex.one_im, Complex.ofReal_im]
      ring
  have hdiag : (mellinCauchyGram (mellinAppend s t) none none).re =
      1 / (2 * t.re - 1) := by
    change (1 / (t + starRingEnd ℂ t - 1)).re = _
    rw [hreal, Complex.div_ofReal_re, Complex.one_re]
  have hcap := mellinInverseCapacity_centered_product s t hs ht hinj
  change mellinInverseCapacity s (mellinSchurCross s t) = _ at hcap
  unfold mellinSchurScalar
  rw [Complex.sub_re, hdiag, ← hdot, hcap]
  ring

theorem mellinSchurScalar_product (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) :
    mellinSchurScalar s t =
      ((mellinCenteredProduct s t / (2 * t.re - 1) : ℝ) : ℂ) := by
  have hdet := (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  apply Complex.ext
  · exact mellinSchurScalar_re_product s t hs ht hinj
  · simpa only [Complex.ofReal_im] using mellinSchurScalar_im s t hdet

theorem mellinSchurScalar_eq_zero_iff (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) :
    mellinSchurScalar s t = 0 ↔ ∃ i, s i = t := by
  have hden : 2 * t.re - 1 ≠ 0 := ne_of_gt (by linarith : 0 < 2 * t.re - 1)
  rw [mellinSchurScalar_product s t hs ht hinj]
  simpa only [Complex.ofReal_eq_zero, div_eq_zero_iff, hden, or_false] using
    mellinCenteredProduct_eq_zero_iff s t hs ht

theorem mellinSchurScalar_ne_zero_iff (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) :
    mellinSchurScalar s t ≠ 0 ↔ ∀ i, s i ≠ t := by
  constructor
  · intro hn i hi
    exact hn ((mellinSchurScalar_eq_zero_iff s t hs ht hinj).mpr ⟨i, hi⟩)
  · intro hn hz
    obtain ⟨i, hi⟩ := (mellinSchurScalar_eq_zero_iff s t hs ht hinj).mp hz
    exact hn i hi

theorem mellinSchurScalar_re_pos_of_new (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    0 < (mellinSchurScalar s t).re := by
  rw [mellinSchurScalar_re_product s t hs ht hinj]
  exact div_pos (mellinCenteredProduct_pos s t hs ht hnew) (by linarith)

/-- Exact determinant factorization needs only nonsingularity of the old Gram matrix. -/
theorem mellinCauchyGram_det_append (s : ι → ℂ) (t : ℂ)
    (hdet : (mellinCauchyGram s).det ≠ 0) :
    (mellinCauchyGram (mellinAppend s t)).det =
      (mellinCauchyGram s).det * mellinSchurScalar s t := by
  have h := RiemannResearch.LinearAlgebra.det_option_schur
    (mellinCauchyGram (mellinAppend s t)) (isUnit_iff_ne_zero.mpr hdet)
  exact h

theorem mellinCauchyGram_det_append_product (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) :
    (mellinCauchyGram (mellinAppend s t)).det =
      (mellinCauchyGram s).det *
        ((mellinCenteredProduct s t / (2 * t.re - 1) : ℝ) : ℂ) := by
  rw [mellinCauchyGram_det_append s t
    ((mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj),
    mellinSchurScalar_product s t hs ht hinj]

theorem mellinCauchyGram_det_append_ratio (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) :
    (mellinCauchyGram (mellinAppend s t)).det / (mellinCauchyGram s).det =
      ((mellinCenteredProduct s t / (2 * t.re - 1) : ℝ) : ℂ) := by
  apply (div_eq_iff ((mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj)).mpr
  rw [mellinCauchyGram_det_append_product s t hs ht hinj]
  ring

theorem mellinCauchyGram_append_det_ne_zero (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    (mellinCauchyGram (mellinAppend s t)).det ≠ 0 := by
  have hdet := (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  rw [mellinCauchyGram_det_append s t hdet]
  exact mul_ne_zero hdet ((mellinSchurScalar_ne_zero_iff s t hs ht hinj).mpr hnew)

/-- The correction uses a closed finite product denominator and the full complex innovation. -/
theorem mellinInverseCoefficients_append_product (s b : ι → ℂ) (t β : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    let δ : ℂ := ((2 * t.re - 1 : ℝ) : ℂ) * mellinSchurInnovation s b t β /
      (mellinCenteredProduct s t : ℂ)
    mellinInverseCoefficients (mellinAppend s t) (mellinAppend b β) =
      mellinAppend (fun i => mellinInverseCoefficients s b i -
        mellinSchurCoefficients s t i * δ) δ := by
  have hsmall := (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  have hlarge := mellinCauchyGram_append_det_ne_zero s t hs ht hinj hnew
  have hδ : mellinSchurInnovation s b t β / mellinSchurScalar s t =
      ((2 * t.re - 1 : ℝ) : ℂ) * mellinSchurInnovation s b t β /
        (mellinCenteredProduct s t : ℂ) := by
    rw [mellinSchurScalar_product s t hs ht hinj]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_inv,
      div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  dsimp only
  rw [mellinInverseCoefficients_append s b t β hsmall hlarge]
  simp only [mellinSchurUpdate, hδ]

theorem mellinSchur_gain_product (s b : ι → ℂ) (t β : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) :
    ‖mellinSchurInnovation s b t β‖ ^ 2 / (mellinSchurScalar s t).re =
      (2 * t.re - 1) * ‖mellinSchurInnovation s b t β‖ ^ 2 /
        mellinCenteredProduct s t := by
  rw [mellinSchurScalar_re_product s t hs ht hinj]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem mellinInverseCapacity_append_product (s b : ι → ℂ) (t β : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    mellinInverseCapacity (mellinAppend s t) (mellinAppend b β) =
      mellinInverseCapacity s b +
        (2 * t.re - 1) * ‖mellinSchurInnovation s b t β‖ ^ 2 /
          mellinCenteredProduct s t := by
  rw [mellinInverseCapacity_schur s b t β
    ((mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj)
    (mellinCauchyGram_append_det_ne_zero s t hs ht hinj hnew),
    mellinSchur_gain_product s b t β hs ht hinj]

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto RamanujanCanonicalOptimizer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Closed Schur denominator, complete complex innovation, and the full enlarged
Mellin remainder for actual Ramanujan approximation errors. -/
theorem packet_zeroInverse_schur_product_energy_exact (z : ι → ℂ) (t : ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (htre : (1 / 2 : ℝ) < t.re)
    (hz1 : ∀ i, z i ≠ 1) (ht1 : t ≠ 1)
    (hz0 : ∀ i, riemannZeta (z i) = 0) (ht0 : riemannZeta t = 0)
    (hinj : Function.Injective z) (hnew : ∀ i, z i ≠ t) (n : ℕ) :
    1 - packetMass n = mellinInverseCapacity z (fun i => 1 / z i) +
      (2 * t.re - 1) * ‖mellinSchurInnovation z (fun i => 1 / z i) t (1 / t)‖ ^ 2 /
        mellinCenteredProduct z t +
      ∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel (mellinAppend z t)
            (mellinInverseCoefficients (mellinAppend z t)
              (mellinAppend (fun i => 1 / z i) (1 / t))) x)‖ ^ 2 := by
  have h := packet_zeroInverse_schur_energy_exact z t hzre htre hz1 ht1
    hz0 ht0 hinj hnew n
  rwa [mellinSchur_gain_product z (fun i => 1 / z i) t (1 / t) hzre htre hinj] at h

/-- The same closed-product increment retains the full Gram displacement of
every legal packet competitor, in addition to the full Mellin remainder. -/
theorem packet_zeroInverse_schur_product_completion (z : ι → ℂ) (t : ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (htre : (1 / 2 : ℝ) < t.re)
    (hz1 : ∀ i, z i ≠ 1) (ht1 : t ≠ 1)
    (hz0 : ∀ i, riemannZeta (z i) = 0) (ht0 : riemannZeta t = 0)
    (hinj : Function.Injective z) (hnew : ∀ i, z i ≠ t)
    (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)) a‖ ^ 2 =
      mellinInverseCapacity z (fun i => 1 / z i) +
      (2 * t.re - 1) * ‖mellinSchurInnovation z (fun i => 1 / z i) t (1 / t)‖ ^ 2 /
        mellinCenteredProduct z t +
      (∫ x in Ioi (1 : ℝ),
        ‖mellinWeightedStep (hilbertOne - packetCandidate n) x -
          starRingEnd ℂ (finiteMellinKernel (mellinAppend z t)
            (mellinInverseCoefficients (mellinAppend z t)
              (mellinAppend (fun i => 1 / z i) (1 / t))) x)‖ ^ 2) +
      ‖Fintype.linearCombination ℝ
        (fun j : Fin n => ramanujanPacketHilbert (j.val + 2))
        (a - packetCoefficients n)‖ ^ 2 := by
  rw [packet_completion,
    packet_zeroInverse_schur_product_energy_exact z t hzre htre hz1 ht1 hz0 ht0 hinj hnew n]

end RiemannResearch.RH.RamanujanZeroCertificates
