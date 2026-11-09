/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DampedMobiusSmoothedSeries
import RiemannResearch.RH.QReciprocalMellinCriterion

/-!
# An explicit finite Mobius reciprocal family and its open energy criterion

Source: Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf, formula (14),
Theorem 6.2 and the research agenda. Indexing begins at physical j+2.
The full reciprocal approximation is unconditional. The complete unsmoothed
subpower-energy hypothesis in the final theorem remains Open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.DampedMobiusExplicitReciprocalCriterion
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open DampedMobiusSquarefreeClosure DampedMobiusSmoothedSeries
open DampedMobiusReciprocalHilbert QReciprocalMellinCriterion

def damping (j : ℕ) : ℝ := 1 / ((j : ℝ) + 2)

def conductorCutoff (j : ℕ) : ℕ := (j + 2) ^ (2 * (j + 2))

/-- The literal finite signed arithmetic vector from the PDF. -/
def approximant (j : ℕ) : QHilbert :=
  qDampedMobiusPartial (damping j) (conductorCutoff j)

theorem damping_pos (j : ℕ) : 0 < damping j := by
  unfold damping
  positivity

theorem conductorCutoff_pos (j : ℕ) : 0 < conductorCutoff j := by
  unfold conductorCutoff
  positivity

/-- The huge natural-number cutoff pays exactly the reciprocal tail budget. -/
theorem nat_cutoff_reciprocal_budget (n : ℕ) (hn : 0 < n) :
    (((n ^ (2 * n) : ℕ) : ℝ) ^ (-(1 / (n : ℝ)))) / (1 / (n : ℝ)) =
      1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : ((2 * n : ℕ) : ℝ) * (-(1 / (n : ℝ))) = (-2 : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp [ne_of_gt hnR] <;> ring
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hnR.le, he,
    Real.rpow_neg hnR.le, Real.rpow_two]
  field_simp [ne_of_gt hnR] <;> ring

theorem conductorCutoff_reciprocal_budget (j : ℕ) :
    (conductorCutoff j : ℝ) ^ (-(damping j)) / damping j =
      1 / ((j : ℝ) + 2) := by
  simpa only [conductorCutoff, damping, Nat.cast_add, Nat.cast_ofNat] using
    nat_cutoff_reciprocal_budget (j + 2) (by omega)

theorem approximant_mem_squarefreeSpan (j : ℕ) :
    approximant j ∈ qSquarefreeCRTSpan :=
  qDampedMobiusPartial_mem_squarefreeSpan (damping j) (conductorCutoff j)

theorem approximant_mem_legalSpan (j : ℕ) :
    approximant j ∈ QFullResidueProjection.legalSpan := by
  have hspan : qSquarefreeCRTSpan ≤ QFullResidueProjection.legalSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    apply Submodule.subset_span
    refine ⟨d.val - 2, ?_⟩
    have he : d.val - 2 + 2 = d.val := Nat.sub_add_cancel d.property.1
    exact congrArg qResidue he
  exact hspan (approximant_mem_squarefreeSpan j)

/-- Explicit complete reciprocal error, including every physical tail site. -/
theorem approximant_reciprocal_error_le (j : ℕ) :
    ‖B (qOne - approximant j)‖ ≤ (‖qLogEnvelope‖ + 1) / ((j : ℝ) + 2) := by
  rw [map_sub, norm_sub_rev, ← map_sub]
  have hb := qDampedMobiusPartial_reciprocal_error_le (damping_pos j)
    (show 1 ≤ conductorCutoff j from conductorCutoff_pos j)
  change ‖B (approximant j - qOne)‖ ≤ _ at hb
  rw [conductorCutoff_reciprocal_budget j] at hb
  calc
    _ ≤ damping j * ‖qLogEnvelope‖ + 1 / ((j : ℝ) + 2) := hb
    _ = _ := by unfold damping; ring

theorem approximant_reciprocal_tendsto :
    Tendsto (fun j => B (approximant j)) atTop (𝓝 (B qOne)) := by
  have hbase : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun j : ℕ =>
      show (j : ℝ) ≤ (j : ℝ) + 2 by linarith) tendsto_natCast_atTop_atTop
  have hzero : Tendsto damping atTop (𝓝 0) := by
    change Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (𝓝 0)
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp hbase
  have htail : Tendsto (fun j => (conductorCutoff j : ℝ) ^ (-(damping j)) / damping j)
      atTop (𝓝 0) := by
    simp_rw [conductorCutoff_reciprocal_budget]
    exact hzero
  exact qDampedMobiusPartial_reciprocal_tendsto damping conductorCutoff damping_pos
    (fun j => show 1 ≤ conductorCutoff j from conductorCutoff_pos j) hzero htail

/-- The explicit family reduces RH to one complete unsmoothed-energy provider.
Subpower growth is weaker than a uniform norm bound; it is not proved here. -/
theorem riemannHypothesis_of_explicit_subpower_energy
    (henergy : ∀ a : ℝ, 0 < a → Tendsto
      (fun j : ℕ => ((j : ℝ) + 1) ^ (-a) * ‖approximant j‖ ^ 2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_reciprocal_rate_subpower_norm approximant
    approximant_mem_legalSpan (‖qLogEnvelope‖ + 1) _ henergy
  intro j
  exact (approximant_reciprocal_error_le j).trans
    (div_le_div_of_nonneg_left (by positivity)
      (by positivity : 0 < (j : ℝ) + 1) (by linarith))

end RiemannResearch.RH.DampedMobiusExplicitReciprocalCriterion
