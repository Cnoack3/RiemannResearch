import RiemannResearch.RH.ParetoTailCapacityDuality

/-!
# Canonical tail capacity: limits and dilation orthogonality

Source: user-provided first-coordinate/tail-capacity continuation,
Sections 15 and 31, and the present contradiction analysis (2026-09-19).
These are exact Hilbert-space consequences, not an arithmetic regularity
provider and not an unconditional proof of RH.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The actual point projection, before normalizing its first coordinate. -/
def projectedPoint : ThresholdHilbert :=
  closedSpace.starProjection (paretoPointHilbert 0)

theorem projectedPoint_mem : projectedPoint ∈ closedSpace :=
  closedSpace.starProjection_apply_mem _

/-- The point projection is orthogonal to every legal direction with zero
first coordinate. This is the variational condition for the point problem. -/
theorem projectedPoint_orthogonal_zeroHead {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) (hfirst : anchoredEvaluationCLM 1 f = 0) :
    inner ℝ projectedPoint f = 0 := by
  have hr : inner ℝ pointDualResidual f = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp pointDualResidual_mem_orthogonal _ hf
  have hp : inner ℝ (paretoPointHilbert 0) f = 0 := by
    rw [real_inner_comm, inner_firstPoint, hfirst, mul_zero]
  change inner ℝ (paretoPointHilbert 0 - projectedPoint) f = 0 at hr
  rw [inner_sub_left, hp] at hr
  linarith

/-- Every nontrivial integer dilation is an exact zero-correlation direction.
The repository's dilation includes the scalar factor m. -/
theorem projectedPoint_inner_dilation (m : ℕ) (hm : 2 ≤ m) :
    inner ℝ projectedPoint (hilbertDilation m (by omega) projectedPoint) = 0 := by
  apply projectedPoint_orthogonal_zeroHead
  · exact closedSpace_dilation projectedPoint_mem m (by omega)
  · rw [anchoredEvaluationCLM_apply, hilbertDilation_sequence]
    simp [dilation, Nat.div_eq_of_lt (by omega : 1 < m)]

/-- The actual finite point errors converge to the squared closed residual. -/
theorem pointError_tendsto_residual :
    Tendsto pointError atTop (𝓝 (‖pointDualResidual‖ ^ 2)) :=
  walkError_tendsto residueAtom id Function.surjective_id (paretoPointHilbert 0)

/-- In the obstruction case the capacity has this exact finite limit. -/
theorem tailCapacity_tendsto_canonical_energy (hr : pointDualResidual ≠ 0) :
    Tendsto tailCapacity atTop (𝓝 (‖canonicalTailCertificate‖ ^ 2)) := by
  have hδ : ‖pointDualResidual‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).div pointError_tendsto_residual hδ).sub
    (tendsto_const_nhds (x := (2 : ℝ)))
  have he (n : ℕ) : 1 / pointError n - 2 = tailCapacity n := by
    rw [pointError_eq_inv_capacity, one_div_one_div]
    ring
  simpa only [Pi.div_apply, he, ← canonicalTailCertificate_norm_sq hr] using ht

/-- The finite dual vectors converge strongly to the actual canonical
certificate; this establishes its minimum-norm interpretation. -/
theorem tailMinimum_tendsto_canonical (hr : pointDualResidual ≠ 0) :
    Tendsto tailMinimum atTop (𝓝 canonicalTailCertificate) := by
  have hc := canonicalTailCertificate_isCertificate hr
  have he (n : ℕ) : ‖tailMinimum n - canonicalTailCertificate‖ ^ 2 =
      ‖canonicalTailCertificate‖ ^ 2 - tailCapacity n := by
    rw [norm_sub_rev]
    linarith [tailCertificate_energy_completion canonicalTailCertificate hc n]
  have ht : Tendsto (fun n => ‖tailMinimum n - canonicalTailCertificate‖ ^ 2)
      atTop (𝓝 0) := by
    have hh : Tendsto (fun n => ‖canonicalTailCertificate‖ ^ 2 - tailCapacity n)
        atTop (𝓝 (‖canonicalTailCertificate‖ ^ 2 - ‖canonicalTailCertificate‖ ^ 2)) :=
      (tendsto_const_nhds (x := ‖canonicalTailCertificate‖ ^ 2)).sub
        (tailCapacity_tendsto_canonical_energy hr)
    rw [sub_self] at hh
    simpa only [he] using hh
  have hn : Tendsto (fun n => ‖tailMinimum n - canonicalTailCertificate‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp ht
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- Exact Pythagoras for every other certificate: canonical minimality supplies
an energy identity, without supplying any stronger summability. -/
theorem certificate_canonical_energy_split (hr : pointDualResidual ≠ 0)
    (z : ThresholdHilbert) (hz : IsResidueTailCertificate z) :
    ‖z‖ ^ 2 = ‖canonicalTailCertificate‖ ^ 2 +
      ‖z - canonicalTailCertificate‖ ^ 2 := by
  have ht := (tailCapacity_tendsto_canonical_energy hr).add
    (((tendsto_const_nhds (x := z)).sub (tailMinimum_tendsto_canonical hr)).norm.pow 2)
  have he (n : ℕ) : tailCapacity n + ‖z - tailMinimum n‖ ^ 2 = ‖z‖ ^ 2 :=
    (tailCertificate_energy_completion z hz n).symm
  have ht' : Tendsto (fun _ : ℕ => ‖z‖ ^ 2) atTop
      (𝓝 (‖canonicalTailCertificate‖ ^ 2 + ‖z - canonicalTailCertificate‖ ^ 2)) := by
    simpa only [he] using ht
  exact tendsto_nhds_unique tendsto_const_nhds ht'

/-- Every right-half-plane zeta zero imposes an exact interpolation condition
on the same canonical certificate and its actual energy. -/
theorem canonicalTailCertificate_mellin_at_zero (hr : pointDualResidual ≠ 0)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    paretoMellin canonicalTailCertificate s =
      (-(‖canonicalTailCertificate‖ ^ 2) : ℝ) •
        paretoMellin (paretoPointHilbert 0) s := by
  have hδ : ‖pointDualResidual‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  have hp : paretoMellin projectedPoint s = 0 :=
    paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
      (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure projectedPoint_mem)
  have hq : paretoMellin pointDualResidual s =
      paretoMellin (paretoPointHilbert 0) s := by
    change paretoMellinContinuous s hs (paretoPointHilbert 0 - projectedPoint) = _
    rw [map_sub]
    change paretoMellin (paretoPointHilbert 0) s - paretoMellin projectedPoint s = _
    rw [hp, sub_zero]
  have ht : paretoMellin (tailMap pointDualResidual) s =
      (1 - 2 * ‖pointDualResidual‖ ^ 2 : ℝ) •
        paretoMellin (paretoPointHilbert 0) s := by
    change paretoMellinContinuous s hs (pointDualResidual -
      anchoredEvaluationCLM 1 pointDualResidual • paretoPointHilbert 0) = _
    rw [map_sub, map_smul]
    change paretoMellin pointDualResidual s -
      anchoredEvaluationCLM 1 pointDualResidual • paretoMellin (paretoPointHilbert 0) s = _
    rw [hq, pointDualResidual_evaluation, sub_smul, one_smul]
  have ha : -(‖pointDualResidual‖ ^ 2)⁻¹ * (1 - 2 * ‖pointDualResidual‖ ^ 2) =
      -(‖canonicalTailCertificate‖ ^ 2) := by
    rw [canonicalTailCertificate_norm_sq hr]
    field_simp [hδ]
  change paretoMellinContinuous s hs
    ((-(‖pointDualResidual‖ ^ 2)⁻¹) • tailMap pointDualResidual) = _
  rw [map_smul]
  change (-(‖pointDualResidual‖ ^ 2)⁻¹) • paretoMellin (tailMap pointDualResidual) s = _
  rw [ht, smul_smul, ha]

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
