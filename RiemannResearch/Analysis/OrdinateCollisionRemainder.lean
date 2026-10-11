import RiemannResearch.Analysis.OrdinateCollisionCertificate

/-!
# Explicit finite sinc-kernel collision remainder

This supplements the collision certificate with a finite separation estimate.
The upper bound retains the exact number of noncollision ordered pairs. It is
weaker than an ordered-spacing estimate using the Basel series, but its proof
needs only the specified positive minimum separation.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

variable {ι : Type*} [Fintype ι]

def occurrenceNoncollision (frequency : ι → ℝ) : ℕ := by
  classical
  exact ∑ i, ∑ j, if frequency i ≠ frequency j then 1 else 0

theorem collision_add_noncollision (frequency : ι → ℝ) :
    occurrenceCollision frequency + occurrenceNoncollision frequency =
      (Fintype.card ι) ^ 2 := by
  classical
  have hp : ∀ i j : ι,
      (if frequency i = frequency j then (1 : ℕ) else 0) +
      (if frequency i ≠ frequency j then 1 else 0) = 1 := by
    intro i j
    by_cases hf : frequency i = frequency j <;> simp [hf]
  unfold occurrenceCollision occurrenceNoncollision
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, hp]
  simp [pow_two]

theorem sincSquared_le_inverse_square {R v : ℝ} (hR : R ≠ 0) (hv : v ≠ 0) :
    sincSquared R v ≤ 4 / (R ^ 2 * v ^ 2) := by
  have hx : R * v / 2 ≠ 0 := div_ne_zero (mul_ne_zero hR hv) (by norm_num)
  unfold sincSquared
  rw [Real.sinc_of_ne_zero hx, div_pow]
  calc
    _ ≤ 1 / (R * v / 2) ^ 2 :=
      div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (sq_nonneg _)
    _ = _ := by field_simp; ring

theorem sincSquared_le_gap {R δ v : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hgap : δ ≤ |v|) :
    sincSquared R v ≤ 4 / (R ^ 2 * δ ^ 2) := by
  have hv : v ≠ 0 := by intro hv; simp [hv] at hgap; linarith
  have hv2 : δ ^ 2 ≤ v ^ 2 := by
    nlinarith [sq_abs v, abs_nonneg v]
  refine (sincSquared_le_inverse_square hR.ne' hv).trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hv2 (sq_nonneg R)]

theorem sincEnergy_collision_remainder (frequency : ι → ℝ) (R : ℝ) :
    sincEnergy frequency R - (occurrenceCollision frequency : ℝ) =
      ∑ i, ∑ j, if frequency i = frequency j then 0 else
        sincSquared R (frequency i - frequency j) := by
  classical
  have heq : sincEnergy frequency R =
      (occurrenceCollision frequency : ℝ) +
      ∑ i, ∑ j, if frequency i = frequency j then 0 else
        sincSquared R (frequency i - frequency j) := by
    unfold sincEnergy kernelEnergy occurrenceCollision
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hf : frequency i = frequency j <;> simp [hf]
  linarith

/-- Explicit `R⁻²` convergence to the full ordered collision count at fixed cutoff. -/
theorem sincEnergy_gap_remainder (frequency : ι → ℝ) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ)
    (hgap : ∀ i j, frequency i ≠ frequency j → δ ≤ |frequency i - frequency j|) :
    0 ≤ sincEnergy frequency R - (occurrenceCollision frequency : ℝ) ∧
    sincEnergy frequency R - (occurrenceCollision frequency : ℝ) ≤
      4 * ((Fintype.card ι : ℝ) ^ 2 - occurrenceCollision frequency) /
        (R ^ 2 * δ ^ 2) := by
  classical
  refine ⟨sub_nonneg.mpr (collision_le_sincEnergy frequency R), ?_⟩
  rw [sincEnergy_collision_remainder]
  have hbound :
      (∑ i, ∑ j, if frequency i = frequency j then 0 else
        sincSquared R (frequency i - frequency j)) ≤
      (4 / (R ^ 2 * δ ^ 2)) * (occurrenceNoncollision frequency : ℝ) := by
    calc
      _ ≤ ∑ i, ∑ j,
          (4 / (R ^ 2 * δ ^ 2)) *
          (if frequency i ≠ frequency j then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hf : frequency i = frequency j
        · simp [hf]
        · simpa [hf] using sincSquared_le_gap hR hδ (hgap i j hf)
      _ = _ := by
        simp only [occurrenceNoncollision, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  have hc := collision_add_noncollision frequency
  have hcR : (occurrenceCollision frequency : ℝ) +
      (occurrenceNoncollision frequency : ℝ) = (Fintype.card ι : ℝ) ^ 2 := by
    exact_mod_cast hc
  calc
    _ ≤ (4 / (R ^ 2 * δ ^ 2)) * (occurrenceNoncollision frequency : ℝ) := hbound
    _ = _ := by rw [← hcR]; ring

end RiemannResearch.Analysis.OrdinateCollisionCertificate
