import RiemannResearch.RH.ParetoTailCapacity
import RiemannResearch.RH.ResidueTailCertificateRegularity

/-!
# Actual dual tail certificates and nested minimum-energy vectors

Source: user-provided argument,
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`, Section 15,
for the bounded-capacity alternative and exact norm increments. The certificate
is constructed from the actual closed-space point residual. No divergence,
nonexistence of a certificate, or unconditional RH is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.RH.ArithmeticCumulative

local notation "e₁" => paretoPointHilbert 0

/-- The actual minimum vector realizing the reciprocal observations on the
first n tail atoms. -/
def tailMinimum (n : ℕ) : ThresholdHilbert :=
  minimumVector (finiteTailAtom_independent n) (reciprocalSource n)

theorem tailMinimum_observation (n : ℕ) (i : Fin n) :
    inner ℝ (tailAtom i.val) (tailMinimum n) = reciprocalSource n i :=
  minimumVector_observation (finiteTailAtom_independent n) (reciprocalSource n) i

theorem tailMinimum_norm_sq (n : ℕ) :
    ‖tailMinimum n‖ ^ 2 = tailCapacity n :=
  (capacity_eq_norm_sq (finiteTailAtom_independent n) (reciprocalSource n)).symm

theorem tailMinimum_evaluation (n : ℕ) :
    anchoredEvaluationCLM 1 (tailMinimum n) = 0 := by
  simp only [tailMinimum, minimumVector, Fintype.linearCombination_apply,
    map_sum, map_smul, tailAtom, tailMap_evaluation, smul_zero,
    Finset.sum_const_zero]

/-- Exact Pythagoras for the nested reciprocal-observation problems. -/
theorem tailMinimum_increment (m n : ℕ) (hmn : m ≤ n) :
    ‖tailMinimum n - tailMinimum m‖ ^ 2 = tailCapacity n - tailCapacity m := by
  have hfeas (i : Fin m) :
      inner ℝ (tailAtom i.val) (tailMinimum n) = reciprocalSource m i := by
    simpa only [reciprocalSource, Fin.val_castLE] using
      tailMinimum_observation n (Fin.castLE hmn i)
  have h := feasible_norm_sq_completion (finiteTailAtom_independent m)
    (reciprocalSource m) (tailMinimum n) hfeas
  change ‖tailMinimum n‖ ^ 2 =
    ‖tailMinimum m‖ ^ 2 + ‖tailMinimum n - tailMinimum m‖ ^ 2 at h
  rw [tailMinimum_norm_sq, tailMinimum_norm_sq] at h
  linarith

theorem tailCapacity_monotone : Monotone tailCapacity := by
  intro m n hmn
  have h := tailMinimum_increment m n hmn
  nlinarith [sq_nonneg ‖tailMinimum n - tailMinimum m‖]

theorem tailCertificate_observation (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (n : ℕ) (i : Fin n) :
    inner ℝ (tailAtom i.val) z = reciprocalSource n i := by
  have he : anchoredEvaluationCLM 1 z = 0 := by
    simpa only [anchoredEvaluationCLM_apply] using hz.1
  have hpoint : inner ℝ e₁ z = 0 := by
    rw [real_inner_comm, inner_firstPoint, he, mul_zero]
  change inner ℝ (residueAtom i.val -
    (anchoredEvaluationCLM 1 (residueAtom i.val)) • e₁) z = _
  rw [inner_sub_left, real_inner_smul_left, hpoint, mul_zero, sub_zero,
    real_inner_comm]
  exact hz.2 (i.val + 2) (by omega)

/-- Every infinite certificate satisfies an exact finite energy decomposition. -/
theorem tailCertificate_energy_completion (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (n : ℕ) :
    ‖z‖ ^ 2 = tailCapacity n + ‖z - tailMinimum n‖ ^ 2 := by
  have h := feasible_norm_sq_completion (finiteTailAtom_independent n)
    (reciprocalSource n) z (tailCertificate_observation z hz n)
  change ‖z‖ ^ 2 = ‖tailMinimum n‖ ^ 2 + ‖z - tailMinimum n‖ ^ 2 at h
  simpa only [tailMinimum_norm_sq] using h

theorem tailCapacity_le_certificate_energy (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (n : ℕ) :
    tailCapacity n ≤ ‖z‖ ^ 2 := by
  rw [tailCertificate_energy_completion z hz n]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The actual residual of the single physical point after closed projection. -/
def pointDualResidual : ThresholdHilbert := e₁ - closedSpace.starProjection e₁

theorem pointDualResidual_mem_orthogonal : pointDualResidual ∈ closedSpaceᗮ :=
  Submodule.sub_starProjection_mem_orthogonal e₁

theorem pointDualResidual_orthogonal (d : ℕ) (hd : 0 < d) :
    inner ℝ pointDualResidual (normalizedResidueHilbert d hd) = 0 := by
  rw [real_inner_comm]
  apply (closedSpace.mem_orthogonal _).mp pointDualResidual_mem_orthogonal
  exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
    (normalizedResidue_mem_atomSpan d hd)

theorem pointDualResidual_inner_point :
    inner ℝ pointDualResidual e₁ = ‖pointDualResidual‖ ^ 2 := by
  have ho : inner ℝ pointDualResidual (closedSpace.starProjection e₁) = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp pointDualResidual_mem_orthogonal _
      (closedSpace.starProjection_apply_mem e₁)
  have he : e₁ = pointDualResidual + closedSpace.starProjection e₁ := by
    unfold pointDualResidual
    abel
  rw [he, inner_add_right, ho, add_zero, real_inner_self_eq_norm_sq]

theorem pointDualResidual_evaluation :
    anchoredEvaluationCLM 1 pointDualResidual = 2 * ‖pointDualResidual‖ ^ 2 := by
  have h := pointDualResidual_inner_point
  rw [inner_firstPoint] at h
  linarith

/-- The canonical certificate is meaningful as a certificate precisely when
the point residual is nonzero. Its definition alone assumes nothing. -/
def canonicalTailCertificate : ThresholdHilbert :=
  (-(‖pointDualResidual‖ ^ 2)⁻¹) • tailMap pointDualResidual

theorem canonicalTailCertificate_isCertificate (hr : pointDualResidual ≠ 0) :
    IsResidueTailCertificate canonicalTailCertificate := by
  have hE : ‖pointDualResidual‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  constructor
  · rw [← anchoredEvaluationCLM_apply]
    simp only [canonicalTailCertificate, map_smul, tailMap_evaluation, smul_zero]
  · intro d hd
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hpoint : inner ℝ e₁ (normalizedResidueHilbert d (by omega)) =
        (1 / 2 : ℝ) * (1 / (d : ℝ)) := by
      rw [real_inner_comm, inner_firstPoint, anchoredEvaluationCLM_apply,
        normalizedResidueHilbert_sequence]
      simp [residueFraction, Nat.mod_eq_of_lt hd]
    change inner ℝ ((-(‖pointDualResidual‖ ^ 2)⁻¹) •
      (pointDualResidual - (anchoredEvaluationCLM 1 pointDualResidual) • e₁))
        (normalizedResidueHilbert d _) = _
    rw [real_inner_smul_left, inner_sub_left, real_inner_smul_left,
      pointDualResidual_orthogonal, pointDualResidual_evaluation, hpoint]
    field_simp [hE, hd0]
    <;> ring

theorem canonicalTailCertificate_norm_sq (hr : pointDualResidual ≠ 0) :
    ‖canonicalTailCertificate‖ ^ 2 = 1 / ‖pointDualResidual‖ ^ 2 - 2 := by
  have hE : ‖pointDualResidual‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  rw [canonicalTailCertificate, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    tailMap_norm_sq, pointDualResidual_evaluation]
  field_simp [hE]

theorem pointDualResidual_ne_zero_of_point_not_mem
    (he : e₁ ∉ closedSpace) : pointDualResidual ≠ 0 := by
  intro hz
  have hp : e₁ = closedSpace.starProjection e₁ := sub_eq_zero.mp hz
  exact he (hp.symm ▸ closedSpace.starProjection_apply_mem e₁)

/-- Non-membership yields an explicit genuine Hilbert certificate. -/
theorem exists_tailCertificate_of_point_not_mem (he : e₁ ∉ closedSpace) :
    ∃ z : ThresholdHilbert, IsResidueTailCertificate z :=
  ⟨canonicalTailCertificate, canonicalTailCertificate_isCertificate
    (pointDualResidual_ne_zero_of_point_not_mem he)⟩

/-- This identifies the remaining obstruction exactly. It does not exclude it. -/
theorem tailCapacity_bounded_iff_exists_certificate :
    (∃ C : ℝ, ∀ n : ℕ, tailCapacity n ≤ C) ↔
      ∃ z : ThresholdHilbert, IsResidueTailCertificate z := by
  constructor
  · rintro ⟨C, hC⟩
    apply exists_tailCertificate_of_point_not_mem
    intro he
    have herr : Tendsto pointError atTop (𝓝 0) :=
      (walkError_tendsto_zero_iff residueAtom id Function.surjective_id e₁).mpr he
    have ht := tailCapacity_tendsto_iff.mpr herr
    have hev : ∀ᶠ n in atTop, C + 1 ≤ tailCapacity n :=
      (tendsto_atTop.1 ht) (C + 1)
    obtain ⟨n, hn⟩ := eventually_atTop.1 hev
    have hn' := hn n le_rfl
    have hc := hC n
    linarith
  · rintro ⟨z, hz⟩
    exact ⟨‖z‖ ^ 2, tailCapacity_le_certificate_energy z hz⟩

/-- The domain-specific premise is the exclusion of every Hilbert tail
certificate. The regularity obstruction alone does not supply this premise. -/
theorem riemannHypothesis_of_no_tailCertificate
    (h : ¬ ∃ z : ThresholdHilbert, IsResidueTailCertificate z) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_firstPoint_error_tendsto_zero
  apply (walkError_tendsto_zero_iff residueAtom id Function.surjective_id e₁).mpr
  by_contra he
  exact h (exists_tailCertificate_of_point_not_mem he)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
