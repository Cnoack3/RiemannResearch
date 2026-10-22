/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSievePrimeStep
import RiemannResearch.RH.QPrimePowerTwoStage
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.PrimeSieveSecantAlgebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual two-stage corrections for every prime-power target

Source: user-provided TwoStageSieveObstructionResearch20261020.md.
Legality, exact physical heads, and exact complete-Q Mellin formulas.
The p = 2 construction agrees with the original twoStageVector.
-/

noncomputable section
namespace RiemannResearch.RH.QMellinTransfer
open ZetaTwoHilbert

/-- Real part of the normalized physical Mellin probe at a real exponent. -/
def normalizedMellinReal (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) : QHilbert →L[ℝ] ℝ :=
  Complex.reCLM.comp ((σ : ℂ) • qMellinContinuous σ (by simpa using hσ))

@[simp] theorem normalizedMellinReal_apply (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ)
    (f : QHilbert) : normalizedMellinReal σ hσ f = ((σ : ℂ) * qMellin f σ).re := rfl

end RiemannResearch.RH.QMellinTransfer

namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets QMellinTransfer
open PrimeSieveSecant

/-- The drift-cancelling two-stage vector for an arbitrary prime-power target. -/
def sieveTwoStageVector (p H K : ℕ) : QHilbert :=
  (sieveSlope (primorial H) p - sieveSlope (primorial K) p)⁻¹ •
    (sieveSlope (primorial H) p • sieveVector (primorial K) p -
      sieveSlope (primorial K) p • sieveVector (primorial H) p)

theorem sieveTwoStageVector_mem_squarefreeSpan (p H K : ℕ) :
    sieveTwoStageVector p H K ∈ qSquarefreeCRTSpan := by
  apply qSquarefreeCRTSpan.smul_mem
  apply qSquarefreeCRTSpan.sub_mem
  · exact qSquarefreeCRTSpan.smul_mem _
      (sieveVector_mem_squarefreeSpan _ _ (primorial_pos K) (squarefree_primorial K))
  · exact qSquarefreeCRTSpan.smul_mem _
      (sieveVector_mem_squarefreeSpan _ _ (primorial_pos H) (squarefree_primorial H))

theorem qSequence_sieveTwoStageVector (p H K n : ℕ) :
    qSequence (sieveTwoStageVector p H K) n =
      (sieveSlope (primorial H) p * qSequence (sieveVector (primorial K) p) n -
        sieveSlope (primorial K) p * qSequence (sieveVector (primorial H) p) n) /
          (sieveSlope (primorial H) p - sieveSlope (primorial K) p) := by
  change qSequenceLinear ((_ : ℝ) • (_ - _)) n = _
  simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  change (sieveSlope (primorial H) p - sieveSlope (primorial K) p)⁻¹ *
    (sieveSlope (primorial H) p * qSequence (sieveVector (primorial K) p) n -
      sieveSlope (primorial K) p * qSequence (sieveVector (primorial H) p) n) = _
  ring

theorem qSequence_sieveTwoStageVector_head (p H K n : ℕ) (hp : p.Prime)
    (hpH : p ≤ H) (hHK : H ≤ K) (hnH : n ≤ H)
    (hgap : sieveSlope (primorial H) p ≠ sieveSlope (primorial K) p) :
    qSequence (sieveTwoStageVector p H K) n = (Nat.log p n : ℝ) := by
  have hhead (J : ℕ) (hHJ : H ≤ J) :
      qSequence (sieveVector (primorial J) p) n =
        (Nat.log p n : ℝ) - sieveSlope (primorial J) p * (n : ℝ) := by
    exact qSequence_sieveVector_head (primorial J) p J n (primorial_pos J) hp
      (squarefree_primorial J) (hp.dvd_primorial_iff.mpr (hpH.trans hHJ))
      (fun q hq hqJ => hq.dvd_primorial_iff.mpr hqJ) (hnH.trans hHJ)
  rw [qSequence_sieveTwoStageVector, hhead K hHK, hhead H le_rfl]
  apply (div_eq_iff (sub_ne_zero.mpr hgap)).mpr
  ring

theorem linear_sieveTwoStage_intercept (L : QHilbert →ₗ[ℝ] ℝ) (p H K : ℕ) :
    L (sieveTwoStageVector p H K) =
      intercept (sieveSlope (primorial H) p) (sieveSlope (primorial K) p)
        (L (sieveVector (primorial H) p)) (L (sieveVector (primorial K) p)) := by
  simp only [sieveTwoStageVector, map_smul, map_sub, smul_eq_mul]
  unfold intercept
  ring

/-- Exact drift cancellation in the normalized Mellin transform. -/
theorem sieveTwoStageVector_mellin_exact (p H K : ℕ) (hp : p.Prime)
    (hpH : p ≤ H) (hpK : p ≤ K)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    normalizedMellinReal σ hσ (sieveTwoStageVector p H K) =
      (riemannZeta σ).re *
        intercept (sieveSlope (primorial H) p) (sieveSlope (primorial K) p)
          (primePowerEulerFactor p H σ) (primePowerEulerFactor p K σ) := by
  rw [show normalizedMellinReal σ hσ (sieveTwoStageVector p H K) =
    (normalizedMellinReal σ hσ).toLinearMap (sieveTwoStageVector p H K) from rfl,
    linear_sieveTwoStage_intercept]
  simp only [ContinuousLinearMap.coe_coe, normalizedMellinReal_apply]
  rw [sieveVector_primorial_real_mellin_exact p H hp hpH σ hσ hσ1,
    sieveVector_primorial_real_mellin_exact p K hp hpK σ hσ hσ1]
  simp only [intercept, div_eq_mul_inv]
  ring

/-- The complex formula retains the zeta factor, so norm estimates do not need
an additional real-valuedness theorem for zeta on the real axis. -/
theorem sieveTwoStageVector_complex_mellin_exact (p H K : ℕ) (hp : p.Prime)
    (hpH : p ≤ H) (hpK : p ≤ K)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    (σ : ℂ) * qMellin (sieveTwoStageVector p H K) σ =
      riemannZeta σ *
        ((intercept (sieveSlope (primorial H) p) (sieveSlope (primorial K) p)
          (primePowerEulerFactor p H σ) (primePowerEulerFactor p K σ) : ℝ) : ℂ) := by
  have hm : qMellin (sieveTwoStageVector p H K) σ =
      (((sieveSlope (primorial H) p - sieveSlope (primorial K) p)⁻¹ : ℝ) : ℂ) *
        ((sieveSlope (primorial H) p : ℂ) * qMellin (sieveVector (primorial K) p) σ -
          (sieveSlope (primorial K) p : ℂ) * qMellin (sieveVector (primorial H) p) σ) := by
    change qMellinContinuous σ (by simpa using hσ) (_ • (_ - _)) = _
    simp only [map_smul, map_sub, qMellinContinuous_apply, Complex.real_smul]
  calc
    _ = (((sieveSlope (primorial H) p - sieveSlope (primorial K) p)⁻¹ : ℝ) : ℂ) *
        ((sieveSlope (primorial H) p : ℂ) *
          ((σ : ℂ) * qMellin (sieveVector (primorial K) p) σ) -
         (sieveSlope (primorial K) p : ℂ) *
          ((σ : ℂ) * qMellin (sieveVector (primorial H) p) σ)) := by rw [hm]; ring
    _ = _ := by
      rw [sieveVector_primorial_mellin_exact p K hp hpK σ hσ hσ1,
        sieveVector_primorial_mellin_exact p H hp hpH σ hσ hσ1]
      simp only [intercept, Complex.ofReal_sub,
        Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
      ring

theorem sieveTwoStageVector_mellin_norm_exact (p H K : ℕ) (hp : p.Prime)
    (hpH : p ≤ H) (hpK : p ≤ K)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    ‖(σ : ℂ) * qMellin (sieveTwoStageVector p H K) σ‖ =
      ‖riemannZeta σ‖ *
        |intercept (sieveSlope (primorial H) p) (sieveSlope (primorial K) p)
          (primePowerEulerFactor p H σ) (primePowerEulerFactor p K σ)| := by
  rw [sieveTwoStageVector_complex_mellin_exact p H K hp hpH hpK σ hσ hσ1,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The new all-prime construction agrees with the original gcd-two vector. -/
theorem sieveTwoStageVector_two (H K : ℕ) (hH : 2 ≤ H) (hK : 2 ≤ K) :
    sieveTwoStageVector 2 H K = twoStageVector H K := by
  simp only [sieveTwoStageVector, sieveSlope_primorial_two H hH,
    sieveSlope_primorial_two K hK, twoStageVector, primePowerTwoVector]

end RiemannResearch.RH.QPrimePowerSieve
