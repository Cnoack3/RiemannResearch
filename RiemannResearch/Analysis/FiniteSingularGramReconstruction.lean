import RiemannResearch.Analysis.FiniteMoorePenrose
import RiemannResearch.Analysis.FiniteGramRange
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Data.ENNReal.Real

/-!
# Singular finite Gram reconstruction and exact target energy

Source: the user-provided categorical CRT and energy note (14 November 2026),
Theorem E. The Gram map is formed from the actual vectors. Feasibility is
proved equivalent to membership in its range, without linear independence.
The exact optimum is the Moore–Penrose quadratic value, or infinity for
incompatible data. The finite dual inequality is equivalent to a bounded
feasible reconstruction and is used for arbitrary-family Hilbert gluing.
-/

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace RiemannResearch.Analysis.FiniteHilbertGram
noncomputable section
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem exists_gram_eq_of_null_compatible (v : ι → H) (b : ι → ℝ)
    (hb : ∀ c : ι → ℝ, Fintype.linearCombination ℝ v c = 0 →
      ∑ i, c i * b i = 0) :
    ∃ c : ι → ℝ, gram v c = b := by
  let B : EuclideanSpace ℝ ι := WithLp.toLp 2 b
  have hsym : ∀ x y, inner ℝ (gramEuclidean v x) y =
      inner ℝ x (gramEuclidean v y) := by
    intro x y
    calc
      _ = inner ℝ y (gramEuclidean v x) := real_inner_comm _ _
      _ = inner ℝ (Fintype.linearCombination ℝ v y.ofLp)
          (Fintype.linearCombination ℝ v x.ofLp) := gramEuclidean_pairing v y x
      _ = inner ℝ (Fintype.linearCombination ℝ v x.ofLp)
          (Fintype.linearCombination ℝ v y.ofLp) := real_inner_comm _ _
      _ = _ := (gramEuclidean_pairing v x y).symm
  have hB : ∀ x, gramEuclidean v x = 0 → inner ℝ x B = 0 := by
    intro x hx
    have he := gramEuclidean_pairing v x x
    rw [hx, inner_zero_right, real_inner_self_eq_norm_sq] at he
    have hz : Fintype.linearCombination ℝ v x.ofLp = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (Fintype.linearCombination ℝ v x.ofLp)]
    have hs := hb x.ofLp hz
    rw [PiLp.inner_apply]
    simpa [RCLike.inner_apply', B, mul_comm] using hs
  obtain ⟨c, hc⟩ := exists_preimage_of_kernel_orthogonal (gramEuclidean v) hsym B hB
  exact ⟨c.ofLp, congrArg WithLp.ofLp hc⟩

theorem finite_feasible_iff_gram_range (v : ι → H) (b : ι → ℝ) :
    (∃ x : H, ∀ i, inner ℝ (v i) x = b i) ↔
      ∃ c : ι → ℝ, gram v c = b := by
  constructor
  · rintro ⟨x, hx⟩
    apply exists_gram_eq_of_null_compatible v b
    intro c hc
    have h := inner_synthesis_left v c x
    rw [hc, inner_zero_left] at h
    simpa only [hx] using h.symm
  · rintro ⟨c, hc⟩
    exact ⟨Fintype.linearCombination ℝ v c, fun i => congrFun hc i⟩

theorem gram_solution_energy (v : ι → H) (b c : ι → ℝ)
    (hc : gram v c = b) :
    ‖Fintype.linearCombination ℝ v c‖ ^ 2 = ∑ i, c i * b i := by
  rw [gram_quadratic, hc]

theorem gram_solution_completion (v : ι → H) (b c : ι → ℝ)
    (hc : gram v c = b) (x : H) (hx : ∀ i, inner ℝ (v i) x = b i) :
    ‖x‖ ^ 2 = (∑ i, c i * b i) +
      ‖x - Fintype.linearCombination ℝ v c‖ ^ 2 := by
  have hi : inner ℝ x (Fintype.linearCombination ℝ v c) = ∑ i, c i * b i := by
    rw [real_inner_comm, inner_synthesis_left]
    simp only [hx]
  rw [norm_sub_sq_real, gram_solution_energy v b c hc, hi]
  ring

theorem finite_dual_bound_iff (v : ι → H) (b : ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C) :
    (∃ x : H, (∀ i, inner ℝ (v i) x = b i) ∧ ‖x‖ ^ 2 ≤ C) ↔
      ∀ c : ι → ℝ, |∑ i, c i * b i| ^ 2 ≤
        C * ‖Fintype.linearCombination ℝ v c‖ ^ 2 := by
  constructor
  · rintro ⟨x, hx, hn⟩ c
    have h := abs_real_inner_le_norm (Fintype.linearCombination ℝ v c) x
    rw [inner_synthesis_left] at h
    simp only [hx] at h
    have hs := mul_self_le_mul_self (abs_nonneg (∑ i, c i * b i)) h
    have hm := mul_le_mul_of_nonneg_left hn
      (sq_nonneg ‖Fintype.linearCombination ℝ v c‖)
    nlinarith [sq_nonneg (∑ i, c i * b i)]
  · intro hd
    have hnull : ∀ c : ι → ℝ, Fintype.linearCombination ℝ v c = 0 →
        ∑ i, c i * b i = 0 := by
      intro c hc
      have hh := hd c
      rw [hc, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hh
      nlinarith [sq_abs (∑ i, c i * b i)]
    obtain ⟨c, hc⟩ := exists_gram_eq_of_null_compatible v b hnull
    refine ⟨Fintype.linearCombination ℝ v c, fun i => congrFun hc i, ?_⟩
    have hh := hd c
    have he := gram_solution_energy v b c hc
    rw [← he, abs_of_nonneg (sq_nonneg _)] at hh
    nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ v c‖]
/-- Canonical Moore–Penrose coefficient array for the actual finite Gram map.
The coefficient Euclidean structure is used even when the original vectors
are linearly dependent. -/
def gramPseudoinverse (v : ι → H) (b : ι → ℝ) : ι → ℝ :=
  (LinearMap.moorePenrose (gramEuclidean v) (WithLp.toLp 2 b)).ofLp

theorem gramPseudoinverse_normal (v : ι → H) (b : ι → ℝ)
    (hb : ∃ c : ι → ℝ, gram v c = b) :
    gram v (gramPseudoinverse v b) = b := by
  have hB : WithLp.toLp 2 b ∈ LinearMap.range (gramEuclidean v) := by
    rcases hb with ⟨c, hc⟩
    refine ⟨WithLp.toLp 2 c, ?_⟩
    exact congrArg (WithLp.toLp 2) hc
  have h := LinearMap.moorePenrose_normal (gramEuclidean v) (WithLp.toLp 2 b)
  rw [Submodule.starProjection_eq_self_iff.mpr hB] at h
  exact congrArg WithLp.ofLp h

/-- Actual least-energy reconstruction, with the Moore–Penrose coefficient. -/
def gramMinimumVector (v : ι → H) (b : ι → ℝ) : H :=
  Fintype.linearCombination ℝ v (gramPseudoinverse v b)

theorem gramMinimumVector_observation (v : ι → H) (b : ι → ℝ)
    (hb : ∃ c : ι → ℝ, gram v c = b) (i : ι) :
    inner ℝ (v i) (gramMinimumVector v b) = b i :=
  congrFun (gramPseudoinverse_normal v b hb) i

theorem gramMinimumVector_energy (v : ι → H) (b : ι → ℝ)
    (hb : ∃ c : ι → ℝ, gram v c = b) :
    ‖gramMinimumVector v b‖ ^ 2 = ∑ i, b i * gramPseudoinverse v b i := by
  unfold gramMinimumVector
  rw [gram_solution_energy v b _ (gramPseudoinverse_normal v b hb)]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gramMinimumVector_completion (v : ι → H) (b : ι → ℝ)
    (hb : ∃ c : ι → ℝ, gram v c = b) (x : H)
    (hx : ∀ i, inner ℝ (v i) x = b i) :
    ‖x‖ ^ 2 = ‖gramMinimumVector v b‖ ^ 2 +
      ‖x - gramMinimumVector v b‖ ^ 2 := by
  have h := gram_solution_completion v b (gramPseudoinverse v b)
    (gramPseudoinverse_normal v b hb) x hx
  rw [← gram_solution_energy v b _ (gramPseudoinverse_normal v b hb)] at h
  exact h

theorem gramMinimumVector_unique (v : ι → H) (b : ι → ℝ)
    (hb : ∃ c : ι → ℝ, gram v c = b) (x : H)
    (hx : ∀ i, inner ℝ (v i) x = b i) :
    ‖x‖ ^ 2 = ‖gramMinimumVector v b‖ ^ 2 ↔ x = gramMinimumVector v b := by
  constructor
  · intro he
    have h := gramMinimumVector_completion v b hb x hx
    have hz : x - gramMinimumVector v b = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (x - gramMinimumVector v b)]
    exact sub_eq_zero.mp hz
  · rintro rfl
    rfl

/-- Extended-real optimum, including infinity for inconsistent finite data. -/
def finiteConstraintEnergy (v : ι → H) (b : ι → ℝ) : ℝ≥0∞ :=
  ⨅ x : H, ⨅ (_ : ∀ i, inner ℝ (v i) x = b i), ENNReal.ofReal (‖x‖ ^ 2)

theorem finiteConstraintEnergy_feasible (v : ι → H) (b : ι → ℝ)
    (hb : ∃ c : ι → ℝ, gram v c = b) :
    finiteConstraintEnergy v b =
      ENNReal.ofReal (∑ i, b i * gramPseudoinverse v b i) := by
  rw [← gramMinimumVector_energy v b hb]
  apply le_antisymm
  · apply iInf_le_of_le (gramMinimumVector v b)
    exact iInf_le _ (gramMinimumVector_observation v b hb)
  · apply le_iInf
    intro x
    apply le_iInf
    intro hx
    apply ENNReal.ofReal_le_ofReal
    have h := gramMinimumVector_completion v b hb x hx
    nlinarith [sq_nonneg ‖x - gramMinimumVector v b‖]

theorem finiteConstraintEnergy_infeasible (v : ι → H) (b : ι → ℝ)
    (hb : ¬ ∃ c : ι → ℝ, gram v c = b) :
    finiteConstraintEnergy v b = ⊤ := by
  apply top_unique
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  exact False.elim (hb ((finite_feasible_iff_gram_range v b).mp ⟨x, hx⟩))

theorem finiteConstraintEnergy_eq (v : ι → H) (b : ι → ℝ) :
    finiteConstraintEnergy v b =
      if ∃ c : ι → ℝ, gram v c = b then
        ENNReal.ofReal (∑ i, b i * gramPseudoinverse v b i) else ⊤ := by
  split_ifs with hb
  · exact finiteConstraintEnergy_feasible v b hb
  · exact finiteConstraintEnergy_infeasible v b hb

end
end RiemannResearch.Analysis.FiniteHilbertGram
