import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Tactic.FieldSimp

/-!
# Affine normalization of a possibly singular finite Gram form

Source: user-provided Pareto direct-attempt handoff, Section 7, for the
signed-average optimization problem. This module proves the exact minimum
from a Gram normal solution without assuming linear independence.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem normal_mass_pos (v : ι → H) (z : ι → ℝ)
    (hz : gram v z = fun _ => 1) : 0 < ∑ i, z i := by
  have he : ‖Fintype.linearCombination ℝ v z‖ ^ 2 = ∑ i, z i := by
    rw [gram_quadratic, hz]
    simp only [mul_one]
  rw [← he]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hzero
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi := congrFun hz i
  change inner ℝ (v i) (Fintype.linearCombination ℝ v z) = 1 at hi
  rw [hzero, inner_zero_right] at hi
  norm_num at hi

/-- Normalized normal-solution coefficients; kernel ambiguities are allowed. -/
def affineCoefficients (z : ι → ℝ) : ι → ℝ :=
  fun i => (∑ j, z j)⁻¹ * z i

theorem affineCoefficients_sum (v : ι → H) (z : ι → ℝ)
    (hz : gram v z = fun _ => 1) : ∑ i, affineCoefficients z i = 1 := by
  simp only [affineCoefficients, ← Finset.mul_sum]
  exact inv_mul_cancel₀ (ne_of_gt (normal_mass_pos v z hz))

theorem affineCoefficients_energy (v : ι → H) (z : ι → ℝ)
    (hz : gram v z = fun _ => 1) :
    ‖Fintype.linearCombination ℝ v (affineCoefficients z)‖ ^ 2 =
      (∑ i, z i)⁻¹ := by
  have hn : gram v (affineCoefficients z) = fun _ => (∑ i, z i)⁻¹ := by
    change gram v ((∑ i, z i)⁻¹ • z) = _
    rw [map_smul, hz]
    ext i
    simp
  rw [gram_quadratic, hn, ← Finset.sum_mul, affineCoefficients_sum v z hz, one_mul]

/-- Exact completion retains the complete signed Gram remainder. -/
theorem affineCoefficients_completion (v : ι → H) (z c : ι → ℝ)
    (hz : gram v z = fun _ => 1) (hc : ∑ i, c i = 1) :
    ‖Fintype.linearCombination ℝ v c‖ ^ 2 = (∑ i, z i)⁻¹ +
      ‖Fintype.linearCombination ℝ v (c - affineCoefficients z)‖ ^ 2 := by
  have hcross : inner ℝ (Fintype.linearCombination ℝ v c)
      (Fintype.linearCombination ℝ v (affineCoefficients z)) = (∑ i, z i)⁻¹ := by
    rw [inner_synthesis_left]
    change (∑ i, c i * gram v (affineCoefficients z) i) = _
    have hn : gram v (affineCoefficients z) = fun _ => (∑ i, z i)⁻¹ := by
      change gram v ((∑ i, z i)⁻¹ • z) = _
      rw [map_smul, hz]
      ext i
      simp
    rw [hn, ← Finset.sum_mul, hc, one_mul]
  rw [map_sub, norm_sub_sq_real, hcross, affineCoefficients_energy v z hz]
  ring

theorem affineCoefficients_isLeast (v : ι → H) (z : ι → ℝ)
    (hz : gram v z = fun _ => 1) :
    IsLeast {E : ℝ | ∃ c : ι → ℝ, (∑ i, c i) = 1 ∧
      ‖Fintype.linearCombination ℝ v c‖ ^ 2 = E} (∑ i, z i)⁻¹ := by
  constructor
  · exact ⟨affineCoefficients z, affineCoefficients_sum v z hz,
      affineCoefficients_energy v z hz⟩
  · rintro E ⟨c, hc, rfl⟩
    rw [affineCoefficients_completion v z c hz hc]
    exact le_add_of_nonneg_right (sq_nonneg _)

/-- All minimizers synthesize the same Hilbert vector, even for singular Gram. -/
theorem affineCoefficients_minimum_iff (v : ι → H) (z c : ι → ℝ)
    (hz : gram v z = fun _ => 1) (hc : ∑ i, c i = 1) :
    ‖Fintype.linearCombination ℝ v c‖ ^ 2 = (∑ i, z i)⁻¹ ↔
      Fintype.linearCombination ℝ v c =
        Fintype.linearCombination ℝ v (affineCoefficients z) := by
  constructor
  · intro he
    have ht := affineCoefficients_completion v z c hz hc
    have hn : ‖Fintype.linearCombination ℝ v (c - affineCoefficients z)‖ ^ 2 = 0 := by
      linarith
    have hzero := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    rw [map_sub] at hzero
    exact sub_eq_zero.mp hzero
  · intro he
    rw [he, affineCoefficients_energy v z hz]

omit [Nonempty ι] in
/-- The scalar normal mass is independent of the chosen solution, including
when coefficient solutions differ by a Gram-kernel vector. -/
theorem normal_mass_unique (v : ι → H) (z w : ι → ℝ)
    (hz : gram v z = fun _ => 1) (hw : gram v w = fun _ => 1) :
    (∑ i, z i) = ∑ i, w i := by
  have hzw : inner ℝ (Fintype.linearCombination ℝ v z)
      (Fintype.linearCombination ℝ v w) = ∑ i, z i := by
    rw [inner_synthesis_left]
    change (∑ i, z i * gram v w i) = _
    rw [hw]
    simp only [mul_one]
  have hwz : inner ℝ (Fintype.linearCombination ℝ v w)
      (Fintype.linearCombination ℝ v z) = ∑ i, w i := by
    rw [inner_synthesis_left]
    change (∑ i, w i * gram v z i) = _
    rw [hz]
    simp only [mul_one]
  exact hzw.symm.trans ((real_inner_comm _ _).trans hwz)


section FamilyMonotonicity
variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- Enlarging the admissible affine synthesis set increases normal mass. -/
theorem normal_mass_mono_of_affine_transfer
    (v : ι → H) (w : κ → H) (z : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (htransfer : ∀ c : ι → ℝ, (∑ i, c i) = 1 →
      ∃ d : κ → ℝ, (∑ j, d j) = 1 ∧
        Fintype.linearCombination ℝ w d = Fintype.linearCombination ℝ v c) :
    (∑ i, z i) ≤ ∑ j, u j := by
  obtain ⟨d, hd, he⟩ := htransfer (affineCoefficients z)
    (affineCoefficients_sum v z hz)
  have henergy : ‖Fintype.linearCombination ℝ w d‖ ^ 2 = (∑ i, z i)⁻¹ := by
    rw [he, affineCoefficients_energy v z hz]
  have hmin : (∑ j, u j)⁻¹ ≤ (∑ i, z i)⁻¹ :=
    (affineCoefficients_isLeast w u hu).2 ⟨d, hd, henergy⟩
  exact (inv_le_inv₀ (normal_mass_pos w u hu) (normal_mass_pos v z hz)).mp hmin

/-- A map into a larger family transfers every synthesis by summing coefficient
fibers. The map need not be injective, so duplicates are handled as well. -/
theorem normal_mass_mono_of_family_map
    (v : ι → H) (w : κ → H) (z : ι → ℝ) (u : κ → ℝ)
    (hz : gram v z = fun _ => 1) (hu : gram w u = fun _ => 1)
    (e : ι → κ) (he : ∀ i, v i = w (e i)) :
    (∑ i, z i) ≤ ∑ j, u j := by
  apply normal_mass_mono_of_affine_transfer v w z u hz hu
  intro c hc
  classical
  let d : κ → ℝ := fun j => ∑ i, if e i = j then c i else 0
  have hsum : (∑ j, d j) = ∑ i, c i := by
    change (∑ j, ∑ i, if e i = j then c i else 0) = _
    rw [Finset.sum_comm]
    simp
  refine ⟨d, hsum.trans hc, ?_⟩
  simp only [Fintype.linearCombination_apply]
  change (∑ j, (∑ i, if e i = j then c i else 0) • w j) = ∑ i, c i • v i
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j, (if e i = j then c i else 0) • w j) =
        ∑ j, if e i = j then c i • w j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : e i = j <;> simp [hij]
    _ = c i • w (e i) := by simp
    _ = c i • v i := by rw [← he i]

end FamilyMonotonicity
end RiemannResearch.Analysis.FiniteHilbertGram
