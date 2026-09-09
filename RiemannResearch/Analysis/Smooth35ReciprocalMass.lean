import RiemannResearch.Analysis.SmoothScaleReciprocal

/-!
# Complete reciprocal mass of the two-prime smooth scale grid

Source: `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`, elementary
replacement of the diagonal summability argument. This is an unconditional
geometric-series evaluation, including all scales `3^a * 5^b`.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.SmoothScale
noncomputable section

/-- The reciprocal mass at the smooth scale represented by an exponent pair. -/
def inverseSmooth35 (j : ℕ × ℕ) : ℝ :=
  1 / ((3 : ℝ)^j.1 * (5 : ℝ)^j.2)

theorem inverseSmooth35_eq_geometric (j : ℕ × ℕ) :
    inverseSmooth35 j = (1 / 3 : ℝ)^j.1 * (1 / 5 : ℝ)^j.2 := by
  simp only [inverseSmooth35, one_div, mul_inv_rev, inv_pow]
  ring

/-- The complete two-dimensional reciprocal series is summable. -/
theorem inverseSmooth35_summable : Summable inverseSmooth35 := by
  have h3 : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have h5 : ‖(1 / 5 : ℝ)‖ < 1 := by norm_num
  have hs := (summable_geometric_of_norm_lt_one h3).mul_of_nonneg
    (summable_geometric_of_norm_lt_one h5) (fun _ => by positivity)
    (fun _ => by positivity)
  exact hs.congr (fun j => (inverseSmooth35_eq_geometric j).symm)

/-- Exact infinite reciprocal mass: no smooth-number spacing result is involved. -/
theorem inverseSmooth35_tsum : ∑' j : ℕ × ℕ, inverseSmooth35 j = 15 / 8 := by
  have h3 : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have h5 : ‖(1 / 5 : ℝ)‖ < 1 := by norm_num
  have hs3 := summable_geometric_of_norm_lt_one h3
  have hs5 := summable_geometric_of_norm_lt_one h5
  have hs := hs3.mul_of_nonneg hs5 (fun _ => by positivity) (fun _ => by positivity)
  calc
    _ = ∑' j : ℕ × ℕ, (1 / 3 : ℝ)^j.1 * (1 / 5 : ℝ)^j.2 := by
      apply tsum_congr
      exact inverseSmooth35_eq_geometric
    _ = (∑' a : ℕ, (1 / 3 : ℝ)^a) * (∑' b : ℕ, (1 / 5 : ℝ)^b) :=
      (hs3.tsum_mul_tsum hs5 hs).symm
    _ = 15 / 8 := by
      rw [tsum_geometric_of_norm_lt_one h3, tsum_geometric_of_norm_lt_one h5]
      norm_num

/-- A shifted quadrant has its exact geometric tail mass. -/
theorem inverseSmooth35_shift_tsum (A B : ℕ) :
    (∑' j : ℕ × ℕ, inverseSmooth35 (A + j.1, B + j.2)) =
      (15 / 8 : ℝ) / ((3 : ℝ)^A * (5 : ℝ)^B) := by
  have he (j : ℕ × ℕ) : inverseSmooth35 (A + j.1, B + j.2) =
      inverseSmooth35 (A, B) * inverseSmooth35 j := by
    simp only [inverseSmooth35, pow_add]
    ring
  simp_rw [he]
  rw [tsum_mul_left, inverseSmooth35_tsum]
  unfold inverseSmooth35
  ring

/-- Finite terminal-scale contributions with no repeated exponent pair are
bounded by the entire geometric mass. This is the finite terminal part of the
equivalent repair family argument. -/
theorem terminal_smooth35_energy_sum_le {ι : Type*} (s : Finset ι)
    (exponents : ι → ℕ × ℕ) (energy : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hinj : Set.InjOn exponents (↑s : Set ι))
    (hbound : ∀ i ∈ s, energy i ≤ C * inverseSmooth35 (exponents i)) :
    (∑ i ∈ s, energy i) ≤ C * (15 / 8 : ℝ) := by
  classical
  calc
    _ ≤ ∑ i ∈ s, C * inverseSmooth35 (exponents i) :=
      Finset.sum_le_sum hbound
    _ = C * ∑ i ∈ s, inverseSmooth35 (exponents i) := by rw [Finset.mul_sum]
    _ = C * ∑ j ∈ s.image exponents, inverseSmooth35 j := by
      congr 1
      exact (Finset.sum_image (fun i hi j hj hij => hinj hi hj hij)).symm
    _ ≤ C * ∑' j : ℕ × ℕ, inverseSmooth35 j := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact inverseSmooth35_summable.sum_le_tsum _ (fun j _ => by
        unfold inverseSmooth35
        positivity)
    _ = _ := by rw [inverseSmooth35_tsum]

/-- Consequently any terminal family with distinct smooth labels and the
displayed full-energy estimate has summable energy. -/
theorem summable_terminal_smooth35_energy {ι : Type*}
    (exponents : ι → ℕ × ℕ) (energy : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hinj : Function.Injective exponents) (he0 : ∀ i, 0 ≤ energy i)
    (hbound : ∀ i, energy i ≤ C * inverseSmooth35 (exponents i)) :
    Summable energy := by
  apply summable_of_sum_le (c := C * (15 / 8 : ℝ)) he0
  intro s
  exact terminal_smooth35_energy_sum_le s exponents energy C hC
    hinj.injOn (fun i _ => hbound i)

end
end RiemannResearch.Analysis.SmoothScale
