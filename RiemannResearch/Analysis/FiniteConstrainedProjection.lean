import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteHilbertConstraints
import Mathlib.Tactic.Linarith

/-!
# Exact finite projection under head observations

Source: the user-provided Green--Pareto--Schur continuation, Appendix B;
finite constrained projection and exact repair comparison.
This extends the actual inverse-Gram projection by an explicit minimum-energy
correction. Independence is required only of the projected finite observation
rows, and no asymptotic head estimate is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteConstrainedProjection

open FiniteHilbertGram FiniteHilbertConstraints

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def projectedRow {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (i : κ) : H :=
  Fintype.linearCombination ℝ v (inverseCoeff hv (h i))

def projectionResidual {v : ι → H} (hv : LinearIndependent ℝ v) (x : H) : H :=
  x - Fintype.linearCombination ℝ v (inverseCoeff hv x)

def headMismatch {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (x : H) (i : κ) : ℝ :=
  inner ℝ (h i) (projectionResidual hv x)

def correction {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) : H :=
  minimumVector hr (headMismatch hv h x)

def correctedProjection {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) : H :=
  Fintype.linearCombination ℝ v (inverseCoeff hv x) + correction hv h hr x

omit [Fintype κ] in
theorem projectedRow_pairing {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (c : ι → ℝ) (i : κ) :
    inner ℝ (h i) (Fintype.linearCombination ℝ v c) =
      inner ℝ (projectedRow hv h i) (Fintype.linearCombination ℝ v c) := by
  apply sub_eq_zero.mp
  simpa only [projectedRow, inner_sub_left] using residual_orthogonal hv (h i) c

/-- A concrete legal interpolation of the coordinate unit heads proves the
projected observation rows independent. No Gram invertibility is assumed. -/
theorem projectedRow_independent_of_interpolants [DecidableEq κ] {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (d : κ → ι → ℝ)
    (hdual : ∀ i j, inner ℝ (h j) (Fintype.linearCombination ℝ v (d i)) =
      if j = i then 1 else 0) : LinearIndependent ℝ (projectedRow hv h) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  change Fintype.linearCombination ℝ (projectedRow hv h) a = 0 at ha
  have hz : inner ℝ (Fintype.linearCombination ℝ (projectedRow hv h) a)
      (Fintype.linearCombination ℝ v (d i)) = 0 := by rw [ha, inner_zero_left]
  rw [inner_synthesis_left] at hz
  simp_rw [← projectedRow_pairing hv h (d i), hdual i] at hz
  simpa using hz

theorem residual_inner_rowSynthesis {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (x : H) (d : κ → ℝ) :
    inner ℝ (projectionResidual hv x)
      (Fintype.linearCombination ℝ (projectedRow hv h) d) = 0 := by
  rw [Fintype.linearCombination_apply, inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_right]
  have hz := residual_orthogonal hv x (inverseCoeff hv (h i))
  change inner ℝ (projectionResidual hv x) (projectedRow hv h i) = 0 at hz
  rw [hz, mul_zero]

theorem projectedRow_pairing_rowSynthesis {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H) (d : κ → ℝ) (i : κ) :
    inner ℝ (h i) (Fintype.linearCombination ℝ (projectedRow hv h) d) =
      inner ℝ (projectedRow hv h i)
        (Fintype.linearCombination ℝ (projectedRow hv h) d) := by
  apply sub_eq_zero.mp
  have hz := residual_inner_rowSynthesis hv h (h i) d
  simpa only [projectionResidual, projectedRow, inner_sub_left] using hz

theorem correction_observation {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (hr : LinearIndependent ℝ (projectedRow hv h))
    (x : H) (i : κ) :
    inner ℝ (h i) (correction hv h hr x) = headMismatch hv h x i := by
  unfold correction
  unfold minimumVector
  rw [projectedRow_pairing_rowSynthesis]
  exact minimumVector_observation hr (headMismatch hv h x) i

theorem correctedProjection_observation {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H)
    (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) (i : κ) :
    inner ℝ (h i) (correctedProjection hv h hr x) = inner ℝ (h i) x := by
  rw [correctedProjection, inner_add_right, correction_observation]
  simp only [headMismatch, projectionResidual, inner_sub_right]
  ring

theorem correctedProjection_error {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) :
    ‖x - correctedProjection hv h hr x‖ ^ 2 =
      ‖projectionResidual hv x‖ ^ 2 + ‖correction hv h hr x‖ ^ 2 := by
  have he : x - correctedProjection hv h hr x =
      projectionResidual hv x - correction hv h hr x := by
    unfold correctedProjection projectionResidual
    abel
  rw [he, norm_sub_sq_real]
  have hz : inner ℝ (projectionResidual hv x) (correction hv h hr x) = 0 := by
    unfold correction minimumVector
    exact residual_inner_rowSynthesis hv h x _
  rw [hz]
  ring

/-- Exact constrained inverse correction, with every mixed term retained. -/
theorem correctedProjection_error_inverseGram {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H)
    (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) :
    ‖x - correctedProjection hv h hr x‖ ^ 2 =
      ‖projectionResidual hv x‖ ^ 2 +
        ∑ i, (gramEquiv hr).symm (headMismatch hv h x) i * headMismatch hv h x i := by
  rw [correctedProjection_error]
  exact congrArg (fun t => ‖projectionResidual hv x‖ ^ 2 + t)
    (minimumVector_norm_sq hr (headMismatch hv h x))

/-- A legal exact-head competitor differs from the constrained optimum by
one nonnegative complete norm square. -/
theorem constrained_error_completion {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H)
    (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ v c) = inner ℝ (h i) x) :
    ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖x - correctedProjection hv h hr x‖ ^ 2 +
        ‖Fintype.linearCombination ℝ v c - correctedProjection hv h hr x‖ ^ 2 := by
  let d := c - inverseCoeff hv x
  have hd : ∀ i, inner ℝ (projectedRow hv h i)
      (Fintype.linearCombination ℝ v d) = headMismatch hv h x i := by
    intro i
    rw [← projectedRow_pairing hv h d i]
    change inner ℝ (h i)
      (Fintype.linearCombination ℝ v (c - inverseCoeff hv x)) = _
    rw [map_sub, inner_sub_right, hc i]
    simp only [headMismatch, projectionResidual, inner_sub_right]
  have hdiff : Fintype.linearCombination ℝ v c - correctedProjection hv h hr x =
      Fintype.linearCombination ℝ v d - correction hv h hr x := by
    dsimp [d, correctedProjection]
    rw [map_sub]
    abel
  rw [residual_completion hv x c, correctedProjection_error, hdiff]
  change ‖projectionResidual hv x‖ ^ 2 + ‖Fintype.linearCombination ℝ v d‖ ^ 2 = _
  have hm := feasible_norm_sq_completion hr (headMismatch hv h x)
    (Fintype.linearCombination ℝ v d) hd
  change ‖Fintype.linearCombination ℝ v d‖ ^ 2 =
    ‖correction hv h hr x‖ ^ 2 +
      ‖Fintype.linearCombination ℝ v d - correction hv h hr x‖ ^ 2 at hm
  rw [hm]
  ring

theorem constrained_error_minimizes {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H)
    (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ v c) = inner ℝ (h i) x) :
    ‖x - correctedProjection hv h hr x‖ ^ 2 ≤
      ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 := by
  rw [constrained_error_completion hv h hr x c hc]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem correction_mem {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) :
    correction hv h hr x ∈ synthesisSpan v := by
  unfold correction minimumVector
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (synthesis_mem v (inverseCoeff hv (h i)))

theorem correctedProjection_mem {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) :
    correctedProjection hv h hr x ∈ synthesisSpan v :=
  Submodule.add_mem _ (synthesis_mem v _) (correction_mem hv h hr x)

/-- The corrected projection attains the constrained minimum on the entire
finite legal span. Its definition uses two actual Gram inverses. -/
theorem correctedProjection_isLeast {v : ι → H} (hv : LinearIndependent ℝ v)
    (h : κ → H) (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) :
    IsLeast {E : ℝ | ∃ y : H, y ∈ synthesisSpan v ∧
      (∀ i, inner ℝ (h i) y = inner ℝ (h i) x) ∧ ‖x - y‖ ^ 2 = E}
      (‖x - correctedProjection hv h hr x‖ ^ 2) := by
  constructor
  · exact ⟨correctedProjection hv h hr x, correctedProjection_mem hv h hr x,
      correctedProjection_observation hv h hr x, rfl⟩
  · rintro E ⟨y, hy, hhead, rfl⟩
    rw [synthesisSpan, ← Fintype.range_linearCombination] at hy
    obtain ⟨c, rfl⟩ := hy
    exact constrained_error_minimizes hv h hr x c hhead

theorem constrained_error_eq_minimum_iff {v : ι → H}
    (hv : LinearIndependent ℝ v) (h : κ → H)
    (hr : LinearIndependent ℝ (projectedRow hv h)) (x : H) (c : ι → ℝ)
    (hc : ∀ i, inner ℝ (h i) (Fintype.linearCombination ℝ v c) = inner ℝ (h i) x) :
    ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖x - correctedProjection hv h hr x‖ ^ 2 ↔
        Fintype.linearCombination ℝ v c = correctedProjection hv h hr x := by
  constructor
  · intro he
    have hp := constrained_error_completion hv h hr x c hc
    have hn : ‖Fintype.linearCombination ℝ v c -
        correctedProjection hv h hr x‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))
  · intro he
    rw [he]

section HeadMapBounds

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Every exact-head competitor pays at least the original projection
distance plus the actual projected-residual head square. -/
theorem constrained_error_lower_bound {v : ι → H} (hv : LinearIndependent ℝ v)
    (x : H) (Q : H →ₗ[ℝ] K) (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖)
    (c : ι → ℝ) (hc : Q (Fintype.linearCombination ℝ v c) = Q x) :
    ‖projectionResidual hv x‖ ^ 2 + ‖Q (projectionResidual hv x)‖ ^ 2 ≤
      ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 := by
  let d := c - inverseCoeff hv x
  have hd : Q (Fintype.linearCombination ℝ v d) = Q (projectionResidual hv x) := by
    dsimp [d, projectionResidual]
    rw [map_sub, map_sub, hc, map_sub]
  have hn := hQ (Fintype.linearCombination ℝ v d)
  rw [hd] at hn
  have hs : ‖Q (projectionResidual hv x)‖ ^ 2 ≤
      ‖Fintype.linearCombination ℝ v d‖ ^ 2 := by
    nlinarith [norm_nonneg (Q (projectionResidual hv x)),
      norm_nonneg (Fintype.linearCombination ℝ v d)]
  rw [residual_completion hv x c]
  simpa only [projectionResidual, d, add_comm] using
    add_le_add_left hs (‖projectionResidual hv x‖ ^ 2)

/-- An explicit legal head repair yields a complete norm upper certificate. -/
theorem repaired_projection_head_and_error {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (Q : H →ₗ[ℝ] K)
    (d : ι → ℝ) (C : ℝ)
    (hd : Q (Fintype.linearCombination ℝ v d) = Q (projectionResidual hv x))
    (hrepair : ‖Fintype.linearCombination ℝ v d‖ ≤ C * ‖Q (projectionResidual hv x)‖) :
    Q (Fintype.linearCombination ℝ v (inverseCoeff hv x + d)) = Q x ∧
      ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x + d)‖ ^ 2 ≤
        ‖projectionResidual hv x‖ ^ 2 + C ^ 2 * ‖Q (projectionResidual hv x)‖ ^ 2 := by
  constructor
  · rw [map_add, map_add, hd]
    simp only [projectionResidual, map_sub]
    abel
  · rw [residual_completion hv x (inverseCoeff hv x + d)]
    have hc : inverseCoeff hv x + d - inverseCoeff hv x = d := by abel
    rw [hc]
    have hs : ‖Fintype.linearCombination ℝ v d‖ ^ 2 ≤
        C ^ 2 * ‖Q (projectionResidual hv x)‖ ^ 2 := by
      have hnonneg : 0 ≤ C * ‖Q (projectionResidual hv x)‖ :=
        (norm_nonneg _).trans hrepair
      simpa only [mul_pow] using
        (sq_le_sq₀ (norm_nonneg (Fintype.linearCombination ℝ v d)) hnonneg).mpr hrepair
    simpa only [projectionResidual, add_comm] using
      add_le_add_left hs (‖projectionResidual hv x‖ ^ 2)

/-- Complete comparison for an attained exact-head optimum. Instantiating
the repair constant by the actual Möbius operator gives the paper comparison;
the original projection distance and the head defect are never omitted. -/
theorem constrained_minimum_comparison {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (Q : H →ₗ[ℝ] K)
    (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖) (E : ℝ)
    (hminimum : IsLeast {E' : ℝ | ∃ c : ι → ℝ,
      Q (Fintype.linearCombination ℝ v c) = Q x ∧
        ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 = E'} E)
    (d : ι → ℝ) (C : ℝ)
    (hd : Q (Fintype.linearCombination ℝ v d) = Q (projectionResidual hv x))
    (hrepair : ‖Fintype.linearCombination ℝ v d‖ ≤ C * ‖Q (projectionResidual hv x)‖) :
    ‖projectionResidual hv x‖ ^ 2 + ‖Q (projectionResidual hv x)‖ ^ 2 ≤ E ∧
      E ≤ ‖projectionResidual hv x‖ ^ 2 + C ^ 2 * ‖Q (projectionResidual hv x)‖ ^ 2 := by
  constructor
  · obtain ⟨c, hc, he⟩ := hminimum.1
    rw [← he]
    exact constrained_error_lower_bound hv x Q hQ c hc
  · have htrial := repaired_projection_head_and_error hv x Q d C hd hrepair
    have hle : E ≤ ‖x - Fintype.linearCombination ℝ v (inverseCoeff hv x + d)‖ ^ 2 :=
      hminimum.2 ⟨inverseCoeff hv x + d, htrial.1, rfl⟩
    exact hle.trans htrial.2

/-- The complete exact-head optimum has the sharper Pythagorean ceiling
`(1+C²)δ`; no triangle-inequality factor is introduced. -/
theorem constrained_minimum_le_projection_cost {v : ι → H}
    (hv : LinearIndependent ℝ v) (x : H) (Q : H →ₗ[ℝ] K)
    (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖) (E : ℝ)
    (hminimum : IsLeast {E' : ℝ | ∃ c : ι → ℝ,
      Q (Fintype.linearCombination ℝ v c) = Q x ∧
        ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 = E'} E)
    (d : ι → ℝ) (C : ℝ)
    (hd : Q (Fintype.linearCombination ℝ v d) = Q (projectionResidual hv x))
    (hrepair : ‖Fintype.linearCombination ℝ v d‖ ≤ C * ‖Q (projectionResidual hv x)‖) :
    E ≤ (1 + C ^ 2) * ‖projectionResidual hv x‖ ^ 2 := by
  have hup := (constrained_minimum_comparison hv x Q hQ E hminimum d C hd hrepair).2
  have hcontract := hQ (projectionResidual hv x)
  have hs : ‖Q (projectionResidual hv x)‖ ^ 2 ≤ ‖projectionResidual hv x‖ ^ 2 := by
    nlinarith [norm_nonneg (Q (projectionResidual hv x)), norm_nonneg (projectionResidual hv x)]
  have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg C)
  nlinarith

end HeadMapBounds
end RiemannResearch.Analysis.FiniteConstrainedProjection
