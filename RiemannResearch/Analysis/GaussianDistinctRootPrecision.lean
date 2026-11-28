/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GaussianDistinctRootCollision
import RiemannResearch.Analysis.FiniteCollisionCertificates
import RiemannResearch.Analysis.GaussianCollisionBandwidth
import RiemannResearch.Analysis.GaussianAbsoluteCollision
import RiemannResearch.Analysis.SineGaussianMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Recovering the cross-root collision count at a prescribed Gaussian precision

The precision depends only on the observed positive gaps and total count.
The signed statistic subtracts both the analytic repeat diagonal and the GUE
Palm prediction. Its nearest integer recovers the exact cross-root atom.
-/

noncomputable section
open MeasureTheory Zeta23
open scoped BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open FiniteCollisionCertificates OrdinateCollisionCertificate MontgomeryPositiveGap

private def unfoldedSampleGaps (T : ℝ) : Finset ℝ :=
  sampleGaps (fun i : Copies T => (Real.log T / (2 * Real.pi)) * copyOrdinate T i)

/-- The least positive unfolded gap capped at one, with value one for an empty gap set. -/
def gaussianGapFloor (T : ℝ) : ℝ := by
  classical
  exact (insert 1 (unfoldedSampleGaps T)).min' (Finset.insert_nonempty _ _)

theorem gaussianGapFloor_pos (T : ℝ) : 0 < gaussianGapFloor T := by
  classical
  have h : gaussianGapFloor T ∈ insert 1 (unfoldedSampleGaps T) := Finset.min'_mem _ _
  rcases Finset.mem_insert.mp h with he | hd
  · rw [he]
    norm_num
  · change gaussianGapFloor T ∈ ((Finset.univ.product Finset.univ).image
      (fun ij : Copies T × Copies T =>
        |Real.log T / (2 * Real.pi) * copyOrdinate T ij.1 -
         Real.log T / (2 * Real.pi) * copyOrdinate T ij.2|)).erase 0 at hd
    obtain ⟨hne, hv⟩ := Finset.mem_erase.mp hd
    obtain ⟨ij, _, he⟩ := Finset.mem_image.mp hv
    exact lt_of_le_of_ne (he ▸ abs_nonneg _) hne.symm

theorem gaussianGapFloor_le_separation {T : ℝ} (hT : 1 < T) (i j : Copies T)
    (h : copyOrdinate T i ≠ copyOrdinate T j) :
    gaussianGapFloor T ≤ |gaussianSeparation T i j| := by
  classical
  let L := Real.log T / (2 * Real.pi)
  let f := fun i : Copies T => L * copyOrdinate T i
  have hL : L ≠ 0 := (div_pos (Real.log_pos hT) (by positivity)).ne'
  have hne : f i ≠ f j := fun he => h (mul_left_cancel₀ hL he)
  have hmem : |gaussianSeparation T i j| ∈ unfoldedSampleGaps T := by
    simpa only [gaussianSeparation, unfoldedSampleGaps, mul_sub, f, L] using
      abs_sub_mem_sampleGaps f i j hne
  exact Finset.min'_le _ _ (Finset.mem_insert_of_mem hmem)

/-- The first bandwidth term controls model repulsion and the second controls unequal gaps. -/
def distinctRootGaussianPrecision (T : ℝ) : ℝ :=
  max 1 (max (((4 / 3 : ℝ) * (Ncount 0 T : ℝ) * Real.pi ^ (5 / 2 : ℝ)) ^ (2 / 3 : ℝ))
    (Real.log (8 * (Ncount 0 T : ℝ)^2) / (gaussianGapFloor T)^2))

/-- Each nonnegative contribution is bounded by one eighth of an ordered pair. -/
theorem distinctRootGaussianPrecision_bounds {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    (Ncount 0 T : ℝ) * sinePalmGaussianMass (distinctRootGaussianPrecision T) ≤ 1 / 8 ∧
    unequalGaussianTotal (distinctRootGaussianPrecision T) T ≤ 1 / 8 := by
  let M := (Ncount 0 T : ℝ)
  let d := gaussianGapFloor T
  let b := (4 / 3 : ℝ) * M * Real.pi ^ (5 / 2 : ℝ)
  let a := distinctRootGaussianPrecision T
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast hN
  have hd : 0 < d := gaussianGapFloor_pos T
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hband : b ^ (2 / 3 : ℝ) ≤ a := (le_max_left _ _).trans (le_max_right _ _)
  have hprec : Real.log (8 * M^2) / d^2 ≤ a := (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hb _) hband
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [← Real.rpow_mul hb, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num,
      Real.rpow_one] at hpow
    have he := mul_le_mul_of_nonneg_left (GaussianGapTests.sine_gaussian_moment_le ha) hM.le
    apply he.trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp only [b] at hpow
    linarith only [hpow]
  · have hc := (div_le_iff₀ (sq_pos_of_pos hd)).mp hprec
    have he : Real.exp (-a * d^2) ≤ (8 * M^2)⁻¹ := by
      calc
        _ ≤ Real.exp (-Real.log (8 * M^2)) := Real.exp_le_exp.mpr (by linarith only [hc])
        _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
    apply (unequalGaussianTotal_le_of_separation hN ha.le hd.le
      (gaussianGapFloor_le_separation hT)).trans
    apply (mul_le_mul_of_nonneg_left he (sq_nonneg M)).trans_eq
    field_simp [hM.ne']
    <;> ring

/-- The reconstructed count with its analytic repeats and its sine prediction removed. -/
def calibratedSineRootExcess (T : ℝ) : ℝ :=
  reconstructedDistinctRootMass (distinctRootGaussianPrecision T) T -
    (Ncount 0 T : ℝ) * sinePalmGaussianMass (distinctRootGaussianPrecision T)

/-- All cross terms and both subtractions in the signed arithmetic comparison. -/
theorem calibratedSineRootExcess_eq_landau_integral {T : ℝ} (hN : 0 < Ncount 0 T) :
    let a := distinctRootGaussianPrecision T
    let b := gaussianCollisionAllowance T
    calibratedSineRootExcess T =
      (∫ h : ℝ, (let u := h * Real.log T
                 let J := gapReconstructionOrder T u b
                 let H := ∑ j ∈ Finset.range J,
                   ((u : ℂ)^(2*(j+1)) / ((2*(j+1)).factorial : ℂ)) *
                     evenHorizontalMoment T u (j+1)
                 ‖landauSum T u‖^2 - 2 * inner ℝ (landauSum T u) H + ‖H‖^2) *
                   gaussianFrequencyWeight a h) -
        (multiplicityCollision (cutoff T) zeroMult : ℝ) -
        (Ncount 0 T : ℝ) * sinePalmGaussianMass a := by
  dsimp only
  rw [calibratedSineRootExcess, reconstructedDistinctRootMass_eq_power_sub_rootDiagonal,
    gaussian_power_signed_landau_integral hN]

/-- Signed comparison with the integer atom at the single prescribed precision. -/
theorem calibratedSineRootExcess_error {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    |calibratedSineRootExcess T - (distinctRootCollisionCount T : ℝ)| ≤ 3 / 8 := by
  let a := distinctRootGaussianPrecision T
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨hm, hu⟩ := distinctRootGaussianPrecision_bounds hT hN
  obtain ⟨hl, hr⟩ := abs_le.mp (reconstructedDistinctRoot_quarter_error hN ha)
  rw [distinctRootGaussianMass] at hl hr
  have hm0 := mul_nonneg (Nat.cast_nonneg (Ncount 0 T) : 0 ≤ (Ncount 0 T : ℝ))
    (sinePalmGaussianMass_nonneg a)
  have hu0 := unequalGaussianTotal_nonneg a T
  change |reconstructedDistinctRootMass a T - _ - _| ≤ _
  change (Ncount 0 T : ℝ) * sinePalmGaussianMass a ≤ 1 / 8 at hm
  change unequalGaussianTotal a T ≤ 1 / 8 at hu
  exact abs_le.mpr ⟨by linarith only [hr, hu0, hm], by linarith only [hl, hu, hm0]⟩

/-- Rounding the signed excess recovers the integer count exactly. -/
theorem calibratedSineRootExcess_round {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    ⌊calibratedSineRootExcess T + 1 / 2⌋₊ = distinctRootCollisionCount T := by
  obtain ⟨hl, hr⟩ := abs_le.mp (calibratedSineRootExcess_error hT hN)
  have hp : 0 ≤ (distinctRootCollisionCount T : ℝ) := Nat.cast_nonneg _
  apply (Nat.floor_eq_iff (by linarith only [hl, hp])).mpr
  constructor <;> linarith only [hl, hr]

theorem calibratedSineRootExcess_lt_one_iff {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    calibratedSineRootExcess T < 1 ↔ ∀ p ∈ cutoff T, p.re = 1 / 2 := by
  obtain ⟨hl, hr⟩ := abs_le.mp (calibratedSineRootExcess_error hT hN)
  constructor
  · intro h
    apply (distinctRootCollision_lt_two_iff T).mp
    have hlt : (distinctRootCollisionCount T : ℝ) < 2 := by linarith only [hl, h]
    exact_mod_cast hlt
  · intro h
    rw [distinctRootCollision_zero_of_critical h, Nat.cast_zero, sub_zero] at hr
    linarith

end RiemannResearch.Analysis.ActualZeroOrdinate
