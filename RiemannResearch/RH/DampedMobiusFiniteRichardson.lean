/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusSecondOrderHilbert
import RiemannResearch.RH.DampedMobiusSmoothedSeries
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QReciprocalPowerRateCriterion

/-!
# Actual finite Richardson approximants with quadratic reciprocal error

Every vector here is a literal finite squarefree legal combination. All norm
estimates retain the complete Hilbert tail. The explicit common cutoff is
(j+2)^(3(j+2)), with outer damping 2/(j+2).
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.DampedMobiusFiniteRichardson
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open DampedMobiusSquarefreeClosure DampedMobiusSmoothedSeries
open DampedMobiusReciprocalHilbert DampedMobiusSecondOrderHilbert

/-- Two literal finite unsmoothed arithmetic vectors with their signed weights. -/
def qRichardsonPartial (ε : ℝ) (Nhalf Nfull : ℕ) : QHilbert :=
  (2 : ℝ) • qDampedMobiusPartial (ε / 2) Nhalf - qDampedMobiusPartial ε Nfull

theorem qRichardsonPartial_mem_squarefreeSpan (ε : ℝ) (Nhalf Nfull : ℕ) :
    qRichardsonPartial ε Nhalf Nfull ∈ qSquarefreeCRTSpan :=
  qSquarefreeCRTSpan.sub_mem
    (qSquarefreeCRTSpan.smul_mem 2 (qDampedMobiusPartial_mem_squarefreeSpan _ _))
    (qDampedMobiusPartial_mem_squarefreeSpan _ _)

/-- The same concrete finite vector also lies in the full residue legal span. -/
theorem qRichardsonPartial_mem_legalSpan (ε : ℝ) (Nhalf Nfull : ℕ) :
    qRichardsonPartial ε Nhalf Nfull ∈ QFullResidueProjection.legalSpan := by
  have hspan : qSquarefreeCRTSpan ≤ QFullResidueProjection.legalSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    apply Submodule.subset_span
    refine ⟨d.val - 2, ?_⟩
    have he : d.val - 2 + 2 = d.val := Nat.sub_add_cancel d.property.1
    exact congrArg qResidue he
  exact hspan (qRichardsonPartial_mem_squarefreeSpan ε Nhalf Nfull)

/-- Complete truncation error for the Richardson combination at two cutoffs. -/
theorem qRichardsonPartial_truncation_error_le {ε : ℝ} (hε : 0 < ε)
    {Nhalf Nfull : ℕ} (hhalf : 1 ≤ Nhalf) (hfull : 1 ≤ Nfull) :
    ‖B (qRichardsonPartial ε Nhalf Nfull) - qRichardsonMobius ε hε‖ ≤
      2 * ((Nhalf : ℝ)^(-(ε / 2)) / (ε / 2)) + (Nfull : ℝ)^(-ε) / ε := by
  have he : 0 < ε / 2 := by positivity
  have htHalf := qDampedMobiusSmoothed_partial_error_le he hhalf
  have htFull := qDampedMobiusSmoothed_partial_error_le hε hfull
  rw [qDampedMobiusSmoothed_eq_reciprocalQ he, norm_sub_rev] at htHalf
  rw [qDampedMobiusSmoothed_eq_reciprocalQ hε, norm_sub_rev] at htFull
  have hid : B (qRichardsonPartial ε Nhalf Nfull) - qRichardsonMobius ε hε =
      (2 : ℝ) • (B (qDampedMobiusPartial (ε / 2) Nhalf) -
        dampedMobiusReciprocalQ (ε / 2) he) -
      (B (qDampedMobiusPartial ε Nfull) - dampedMobiusReciprocalQ ε hε) := by
    simp only [qRichardsonPartial, qRichardsonMobius, map_sub, map_smul]
    module
  rw [hid]
  calc
    _ ≤ ‖(2 : ℝ) • (B (qDampedMobiusPartial (ε / 2) Nhalf) -
        dampedMobiusReciprocalQ (ε / 2) he)‖ +
      ‖B (qDampedMobiusPartial ε Nfull) - dampedMobiusReciprocalQ ε hε‖ :=
      norm_sub_le _ _
    _ = 2 * ‖B (qDampedMobiusPartial (ε / 2) Nhalf) -
        dampedMobiusReciprocalQ (ε / 2) he‖ +
      ‖B (qDampedMobiusPartial ε Nfull) - dampedMobiusReciprocalQ ε hε‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left htHalf (by norm_num)) htFull

/-- The finite legal approximant inherits the quadratic damping law and pays
both actual omitted-conductor tails. -/
theorem qRichardsonPartial_reciprocal_error_le {ε : ℝ} (hε : 0 < ε)
    {Nhalf Nfull : ℕ} (hhalf : 1 ≤ Nhalf) (hfull : 1 ≤ Nfull) :
    ‖B (qRichardsonPartial ε Nhalf Nfull - qOne)‖ ≤
      (3 / 2 : ℝ) * ‖qLogSquareEnvelope‖ * ε^2 +
        2 * ((Nhalf : ℝ)^(-(ε / 2)) / (ε / 2)) + (Nfull : ℝ)^(-ε) / ε := by
  have ht := qRichardsonPartial_truncation_error_le hε hhalf hfull
  have hr := qRichardsonMobius_error_norm_le hε
  rw [map_sub]
  calc
    _ = ‖(B (qRichardsonPartial ε Nhalf Nfull) - qRichardsonMobius ε hε) +
        (qRichardsonMobius ε hε - B qOne)‖ := by congr 1; module
    _ ≤ ‖B (qRichardsonPartial ε Nhalf Nfull) - qRichardsonMobius ε hε‖ +
        ‖qRichardsonMobius ε hε - B qOne‖ := norm_add_le _ _
    _ ≤ (2 * ((Nhalf : ℝ)^(-(ε / 2)) / (ε / 2)) + (Nfull : ℝ)^(-ε) / ε) +
        (3 / 2 : ℝ) * ‖qLogSquareEnvelope‖ * ε^2 := add_le_add ht hr
    _ = _ := by ring

/-- Enlarging positive damping reduces the elementary complete-tail budget. -/
theorem reciprocalTail_antitone_damping {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ)^(-b) / b ≤ (N : ℝ)^(-a) / a := by
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  calc
    _ ≤ (N : ℝ)^(-a) / b :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hNR (neg_le_neg hab)) (ha.le.trans hab)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      ha hab

/-- Natural cutoffs of exponent 3n exactly pay a quadratic reciprocal budget. -/
theorem nat_cutoff_quadratic_budget (n : ℕ) (hn : 0 < n) :
    (((n ^ (3 * n) : ℕ) : ℝ)^(-(1 / (n : ℝ)))) / (1 / (n : ℝ)) =
      1 / (n : ℝ)^2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : ((3 * n : ℕ) : ℝ) * (-(1 / (n : ℝ))) = (-3 : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt hnR] <;> ring
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hnR.le, he,
    Real.rpow_neg hnR.le]
  norm_num only [Real.rpow_natCast, Real.rpow_ofNat]
  field_simp [ne_of_gt hnR] <;> ring

def richardsonDamping (j : ℕ) : ℝ := 2 / ((j : ℝ) + 2)

def richardsonCutoff (j : ℕ) : ℕ := (j + 2) ^ (3 * (j + 2))

def richardsonApproximant (j : ℕ) : QHilbert :=
  qRichardsonPartial (richardsonDamping j) (richardsonCutoff j) (richardsonCutoff j)

theorem richardsonDamping_pos (j : ℕ) : 0 < richardsonDamping j := by
  unfold richardsonDamping
  positivity

theorem richardsonCutoff_pos (j : ℕ) : 0 < richardsonCutoff j := by
  unfold richardsonCutoff
  positivity

theorem richardsonCutoff_half_budget (j : ℕ) :
    (richardsonCutoff j : ℝ)^(-(richardsonDamping j / 2)) /
      (richardsonDamping j / 2) = 1 / ((j : ℝ) + 2)^2 := by
  have he : richardsonDamping j / 2 = 1 / ((j : ℝ) + 2) := by
    unfold richardsonDamping
    ring
  rw [he]
  simpa only [richardsonCutoff, Nat.cast_add, Nat.cast_ofNat] using
    nat_cutoff_quadratic_budget (j + 2) (by omega)

theorem richardsonCutoff_full_budget (j : ℕ) :
    (richardsonCutoff j : ℝ)^(-(richardsonDamping j)) / richardsonDamping j ≤
      1 / ((j : ℝ) + 2)^2 := by
  have hp := richardsonDamping_pos j
  have he := reciprocalTail_antitone_damping
    (show 0 < richardsonDamping j / 2 by positivity)
    (show richardsonDamping j / 2 ≤ richardsonDamping j by linarith)
    (show 1 ≤ richardsonCutoff j from richardsonCutoff_pos j)
  rwa [richardsonCutoff_half_budget j] at he

theorem richardsonApproximant_mem_squarefreeSpan (j : ℕ) :
    richardsonApproximant j ∈ qSquarefreeCRTSpan :=
  qRichardsonPartial_mem_squarefreeSpan _ _ _

theorem richardsonApproximant_mem_legalSpan (j : ℕ) :
    richardsonApproximant j ∈ QFullResidueProjection.legalSpan :=
  qRichardsonPartial_mem_legalSpan _ _ _

/-- A fully explicit quadratic reciprocal rate for literal finite legal vectors. -/
theorem richardsonApproximant_reciprocal_error_le (j : ℕ) :
    ‖B (richardsonApproximant j - qOne)‖ ≤
      (6 * ‖qLogSquareEnvelope‖ + 3) / ((j : ℝ) + 2)^2 := by
  have hb := qRichardsonPartial_reciprocal_error_le (richardsonDamping_pos j)
    (show 1 ≤ richardsonCutoff j from richardsonCutoff_pos j)
    (show 1 ≤ richardsonCutoff j from richardsonCutoff_pos j)
  change ‖B (richardsonApproximant j - qOne)‖ ≤ _ at hb
  rw [richardsonCutoff_half_budget j] at hb
  calc
    _ ≤ (3 / 2 : ℝ) * ‖qLogSquareEnvelope‖ * (richardsonDamping j)^2 +
        2 * (1 / ((j : ℝ) + 2)^2) + 1 / ((j : ℝ) + 2)^2 :=
      hb.trans (add_le_add le_rfl (richardsonCutoff_full_budget j))
    _ = _ := by
      unfold richardsonDamping
      field_simp [ne_of_gt (by positivity : (0 : ℝ) < (j : ℝ) + 2)] <;> ring

/-- The finite Richardson family converges reciprocally with every tail included. -/
theorem richardsonApproximant_reciprocal_tendsto :
    Tendsto (fun j => B (richardsonApproximant j)) atTop (𝓝 (B qOne)) := by
  have hbase : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ =>
      show (j : ℝ) ≤ (j : ℝ) + 2 by linarith) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun j : ℕ => ((j : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hbase
  have hu : Tendsto (fun j : ℕ =>
      (6 * ‖qLogSquareEnvelope‖ + 3) / ((j : ℝ) + 2)^2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      using (hi.pow 2).const_mul (6 * ‖qLogSquareEnvelope‖ + 3)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hu
  intro j
  simpa only [map_sub] using richardsonApproximant_reciprocal_error_le j

/-- The accelerated finite family has a checked quadratic reciprocal rate;
only its complete unsmoothed subpower energy remains an arithmetic provider. -/
theorem riemannHypothesis_of_richardson_subpower_energy
    (henergy : ∀ a : ℝ, 0 < a → Tendsto
      (fun j : ℕ => ((j : ℝ) + 1) ^ (-a) * ‖richardsonApproximant j‖ ^ 2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply QReciprocalMellinCriterion.riemannHypothesis_of_reciprocal_power_rate_subpower_norm
    richardsonApproximant richardsonApproximant_mem_legalSpan
    (6 * ‖qLogSquareEnvelope‖ + 3) 2 (by norm_num) _ henergy
  intro j
  rw [Real.rpow_two, map_sub, norm_sub_rev, ← map_sub]
  exact (richardsonApproximant_reciprocal_error_le j).trans
    (div_le_div_of_nonneg_left (by positivity)
      (by positivity : 0 < ((j : ℝ) + 1)^2)
      (by nlinarith [Nat.cast_nonneg (α := ℝ) j]))

end RiemannResearch.RH.DampedMobiusFiniteRichardson
