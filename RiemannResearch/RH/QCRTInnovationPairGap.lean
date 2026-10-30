/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTPrimeInnovation
import RiemannResearch.RH.QCompensatedResidueGap
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Complete-Q near-dependence of actual screened prime columns

Source: user-provided innovation-space research agenda and CRT inverse-Gram
question, 29 October 2026. Exact cancellation removes the common anchor.
The conductor-gap estimate includes the full physical tail. The pair
coercivity theorem is a necessary restriction on a normalized lower bound;
the divisor-pigeonhole asymptotic consequence is recorded separately on paper.
-/

noncomputable section
namespace RiemannResearch.RH.QCRTInnovationPairGap
open ZetaTwoHilbert ZetaTwoProbability QResidueHeadSpace QCRTPrimeInnovation
open QSquarefreeLatticePackets
open QCompensatedResidueGap
open RiemannResearch.Analysis.OrthogonalObservationInnovation

theorem screened_pair_identity (i d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    screenedDirection i d - ((e : ℝ) / d) • screenedDirection i e =
      innovation (QCRTInnovationGain.oldTangent i)
        (compensatedResidue ((2 * i + 3) * d) ((2 * i + 3) * e)) := by
  have hp : ((2 * i + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have he0 : (e : ℝ) ≠ 0 := by positivity
  have hratio : (((2 * i + 3) * e : ℕ) : ℝ) /
      (((2 * i + 3) * d : ℕ) : ℝ) = (e : ℝ) / d := by
    push_cast
    field_simp
  have ha : (e : ℝ) / d * ((oldPeriod i : ℝ) /
      (((2 * i + 3) * e : ℕ) : ℝ)) =
      (oldPeriod i : ℝ) / (((2 * i + 3) * d : ℕ) : ℝ) := by
    push_cast
    field_simp
  have hr : rawDirection i d - ((e : ℝ) / d) • rawDirection i e =
      compensatedResidue ((2 * i + 3) * d) ((2 * i + 3) * e) := by
    simp only [rawDirection, compensatedResidue, smul_sub, smul_smul, ha, hratio]
    module
  change innovation (QCRTInnovationGain.oldTangent i) (rawDirection i d) -
      ((e : ℝ) / d) • innovation (QCRTInnovationGain.oldTangent i) (rawDirection i e) = _
  rw [← hr]
  simp only [innovation, map_sub, map_smul]
  module

theorem screened_pair_gap_bound (i d e : ℕ) (hd : 0 < d)
    (hde : d < e) (he2 : e ≤ 2 * d) :
    ‖screenedDirection i d - ((e : ℝ) / d) • screenedDirection i e‖ ^ 2 ≤
      (1 / zetaTwo) *
        (((((2 * i + 3) * e : ℕ) : ℝ) - (((2 * i + 3) * d : ℕ) : ℝ)) /
          (((2 * i + 3) * d : ℕ) : ℝ) ^ 2 *
          ((21 / 4 : ℝ) + Real.log
            ((((2 * i + 3) * d : ℕ) : ℝ) /
             ((((2 * i + 3) * e : ℕ) : ℝ) - (((2 * i + 3) * d : ℕ) : ℝ))))) := by
  rw [screened_pair_identity i d e hd (by omega)]
  exact (innovation_energy_le _ _).trans
    (compensatedResidue_gap_log_bound _ _ (by nlinarith) (by nlinarith) (by nlinarith))


/-- Cancellation of the conductor scale leaves a dimensionless gap bound. -/
theorem scaled_pair_gap_bound (i d e : ℕ) (hd : 0 < d)
    (hde : d < e) (he2 : e ≤ 2 * d) :
    (((2 * i + 3) * d : ℕ) : ℝ) *
      ‖screenedDirection i d - ((e : ℝ) / d) • screenedDirection i e‖ ^ 2 ≤
      ((e : ℝ) - d) / (zetaTwo * d) *
        ((21 / 4 : ℝ) + Real.log ((d : ℝ) / ((e : ℝ) - d))) := by
  have hp : ((2 * i + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hgap : (e : ℝ) - d ≠ 0 := by
    have h : (d : ℝ) < e := by exact_mod_cast hde
    linarith
  have hlog : ((((2 * i + 3) * d : ℕ) : ℝ) /
      ((((2 * i + 3) * e : ℕ) : ℝ) - (((2 * i + 3) * d : ℕ) : ℝ))) =
      (d : ℝ) / ((e : ℝ) - d) := by
    simp only [Nat.cast_mul]
    rw [← mul_sub]
    field_simp
  have hb := mul_le_mul_of_nonneg_left (screened_pair_gap_bound i d e hd hde he2)
    (show (0 : ℝ) ≤ (((2 * i + 3) * d : ℕ) : ℝ) by positivity)
  rw [hlog] at hb
  calc
    _ ≤ _ := hb
    _ = _ := by
      simp only [Nat.cast_mul]
      field_simp
      <;> ring

/-- Any lower coefficient bound tested on this pair must collapse with the gap.
The hypothesis is the restriction of normalized Gram coercivity to the two
coefficients 1 and -e/d, in the original unnormalized columns. -/
theorem pair_coercivity_bound (i d e : ℕ) (hd : 0 < d)
    (hde : d < e) (he2 : e ≤ 2 * d) (lam : ℝ)
    (hcoer : lam * (1 + (e : ℝ) / d) ≤
      (((2 * i + 3) * d : ℕ) : ℝ) *
        ‖screenedDirection i d - ((e : ℝ) / d) • screenedDirection i e‖ ^ 2) :
    lam ≤ ((e : ℝ) - d) / (zetaTwo * (d + e)) *
      ((21 / 4 : ℝ) + Real.log ((d : ℝ) / ((e : ℝ) - d))) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hsum : (0 : ℝ) < 1 + (e : ℝ) / d := by positivity
  have h := (le_div_iff₀ hsum).mpr
    (hcoer.trans (scaled_pair_gap_bound i d e hd hde he2))
  calc
    lam ≤ _ := h
    _ = _ := by
      field_simp
      <;> ring

end RiemannResearch.RH.QCRTInnovationPairGap
