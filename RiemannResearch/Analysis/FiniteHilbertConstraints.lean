import RiemannResearch.Analysis.FiniteHilbertGram

/-!
# Minimum energy under independent finite Hilbert observations

Source: user-provided argument,
`Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`, Section 11,
equations (11.3)--(11.4). The source supports the signed constrained
minimum and the exact completion of its norm square.

The observation rows are actual Hilbert vectors. Their linear independence
constructs the Gram inverse through `FiniteHilbertGram.gramEquiv`; neither
invertibility nor the desired minimizing conclusion is assumed. In the
manuscript's coefficient Hilbert space with metric `G`, these rows are the
Riesz vectors `G⁻¹ Aᵀ eᵢ`, so their Gram operator is `AG⁻¹Aᵀ`.
The present theorem does not provide that arithmetic specialization.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertConstraints
noncomputable section

open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual least-norm vector with prescribed finite observations. -/
def minimumVector {v : ι → H} (hv : LinearIndependent ℝ v) (b : ι → ℝ) : H :=
  Fintype.linearCombination ℝ v ((gramEquiv hv).symm b)

theorem minimumVector_observation {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (i : ι) :
    inner ℝ (v i) (minimumVector hv b) = b i := by
  exact congrFun ((gramEquiv hv).apply_symm_apply b) i

/-- The exact inverse-Gram quadratic form, retaining all signed terms. -/
theorem minimumVector_norm_sq {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) :
    ‖minimumVector hv b‖ ^ 2 = ∑ i, (gramEquiv hv).symm b i * b i := by
  rw [minimumVector, gram_quadratic]
  apply Finset.sum_congr rfl
  intro i _
  change (gramEquiv hv).symm b i *
    inner ℝ (v i) (minimumVector hv b) = _
  rw [minimumVector_observation]

theorem minimumVector_inner_feasible {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (x : H) (hx : ∀ i, inner ℝ (v i) x = b i) :
    inner ℝ (minimumVector hv b) x = ‖minimumVector hv b‖ ^ 2 := by
  rw [minimumVector_norm_sq]
  unfold minimumVector
  rw [inner_synthesis_left]
  simp only [hx]

/-- Exact completion at the constrained minimum; no mixed term is bounded
or discarded. -/
theorem feasible_norm_sq_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (x : H) (hx : ∀ i, inner ℝ (v i) x = b i) :
    ‖x‖ ^ 2 = ‖minimumVector hv b‖ ^ 2 + ‖x - minimumVector hv b‖ ^ 2 := by
  have hpair : inner ℝ x (minimumVector hv b) = ‖minimumVector hv b‖ ^ 2 := by
    rw [real_inner_comm]
    exact minimumVector_inner_feasible hv b x hx
  rw [norm_sub_sq_real, hpair]
  ring

theorem minimumVector_minimizes {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (x : H) (hx : ∀ i, inner ℝ (v i) x = b i) :
    ‖minimumVector hv b‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [feasible_norm_sq_completion hv b x hx]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem feasible_norm_sq_eq_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (x : H) (hx : ∀ i, inner ℝ (v i) x = b i) :
    ‖x‖ ^ 2 = ‖minimumVector hv b‖ ^ 2 ↔ x = minimumVector hv b := by
  constructor
  · intro he
    have hc := feasible_norm_sq_completion hv b x hx
    have hn : ‖x - minimumVector hv b‖ = 0 := by
      nlinarith [norm_nonneg (x - minimumVector hv b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  · rintro rfl
    rfl

/-- The inverse-Gram number is an attained minimum over the full affine
constraint set, not merely over the observation-row span. -/
theorem inverseGram_isLeast {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) :
    IsLeast {E : ℝ | ∃ x : H, (∀ i, inner ℝ (v i) x = b i) ∧ ‖x‖ ^ 2 = E}
      (∑ i, (gramEquiv hv).symm b i * b i) := by
  constructor
  · exact ⟨minimumVector hv b, minimumVector_observation hv b,
      minimumVector_norm_sq hv b⟩
  · rintro E ⟨x, hx, rfl⟩
    rw [← minimumVector_norm_sq]
    exact minimumVector_minimizes hv b x hx

theorem minimumVector_norm_sq_pos {v : ι → H} (hv : LinearIndependent ℝ v)
    (b : ι → ℝ) (hb : b ≠ 0) : 0 < ‖minimumVector hv b‖ ^ 2 := by
  apply pow_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hb
  funext i
  have h := minimumVector_observation hv b i
  simpa only [hz, inner_zero_right, Pi.zero_apply] using h.symm

end
end RiemannResearch.Analysis.FiniteHilbertConstraints
