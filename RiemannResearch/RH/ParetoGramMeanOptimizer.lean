import RiemannResearch.RH.ParetoFiniteSchur

/-!
# Mean-one optimization from the complete Pareto Gram normal equations

Source: user-provided legal-sequence and linear-independence discussion,
11 September 2026. The Gram action is the actual infinite Pareto inner product.
An inverse provider is explicit; no uniform bound on growing inverses is asserted.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.FiniteSchur
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem projection_mean_eq_energy {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (c : ι → ℝ)
    (hn : ∀ i, paretoInner (z i) (combination z c) = paretoMean (z i)) :
    paretoInner (combination z c) (combination z c) =
      paretoMean (combination z c) := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  rw [inner_combination_left hz (combination_bounded hz c),
    ← paretoInner_one_right, inner_combination_left hz h1]
  simp_rw [hn, paretoInner_one_right]

theorem projection_error_exact {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (c : ι → ℝ)
    (hn : ∀ i, paretoInner (z i) (combination z c) = paretoMean (z i)) :
    paretoError (combination z c) = 1 - paretoMean (combination z c) := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  have h := paretoInner_residual_polynomial h1 (combination_bounded hz c) (1 : ℝ)
  simp only [one_mul, one_pow, paretoInner_one_left, paretoMean_one,
    projection_mean_eq_energy hz c hn] at h
  change paretoInner _ _ = _
  rw [h]
  ring

theorem projection_pairing {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (c b : ι → ℝ)
    (hn : ∀ i, paretoInner (z i) (combination z c) = paretoMean (z i)) :
    paretoInner (combination z b) (combination z c) =
      paretoMean (combination z b) := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  rw [inner_combination_left hz (combination_bounded hz c),
    ← paretoInner_one_right, inner_combination_left hz h1]
  simp_rw [hn, paretoInner_one_right]

/-- The inverse Gram vector, normalized by its actual mean. -/
def normalizedProjection (z : ι → ℕ → ℝ) (c : ι → ℝ) (k : ℕ) : ℝ :=
  (paretoMean (combination z c))⁻¹ * combination z c k

theorem normalizedProjection_mean {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (c : ι → ℝ)
    (hq : paretoMean (combination z c) ≠ 0) :
    paretoMean (normalizedProjection z c) = 1 := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  rw [← paretoInner_one_right]
  unfold normalizedProjection
  rw [paretoInner_const_mul_left (combination_bounded hz c) h1,
    paretoInner_one_right, inv_mul_cancel₀ hq]

theorem normalizedProjection_variance {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (c : ι → ℝ)
    (hn : ∀ i, paretoInner (z i) (combination z c) = paretoMean (z i))
    (hq : paretoMean (combination z c) ≠ 0) :
    paretoVariance (normalizedProjection z c) =
      (paretoMean (combination z c))⁻¹ - 1 := by
  have hbound : ∀ k, |normalizedProjection z c k| ≤
      |(paretoMean (combination z c))⁻¹| * ∑ i, |c i| * B i :=
    bounded_const_mul (combination_bounded hz c) _
  rw [paretoVariance_eq hbound, normalizedProjection_mean hz c hq]
  unfold normalizedProjection
  rw [paretoInner_const_mul_left (combination_bounded hz c)
    (bounded_const_mul (combination_bounded hz c) _),
    paretoInner_const_mul_right (combination_bounded hz c) (combination_bounded hz c),
    projection_mean_eq_energy hz c hn]
  field_simp

/-- Exact excess variance for every mean-one competitor. All mixed terms are retained. -/
theorem normalizedProjection_completion {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (c b : ι → ℝ)
    (hn : ∀ i, paretoInner (z i) (combination z c) = paretoMean (z i))
    (hq : paretoMean (combination z c) ≠ 0)
    (hb : paretoMean (combination z b) = 1) :
    paretoVariance (combination z b) =
      (paretoMean (combination z c))⁻¹ - 1 +
      paretoInner (fun k => combination z b k - normalizedProjection z c k)
        (fun k => combination z b k - normalizedProjection z c k) := by
  have h := paretoInner_residual_polynomial (combination_bounded hz b)
    (combination_bounded hz c) ((paretoMean (combination z c))⁻¹)
  rw [projection_pairing hz c b hn, hb, projection_mean_eq_energy hz c hn] at h
  rw [paretoVariance_eq (combination_bounded hz b), hb]
  unfold normalizedProjection
  rw [h]
  field_simp
  <;> ring

theorem normalizedProjection_minimizes {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (c b : ι → ℝ)
    (hn : ∀ i, paretoInner (z i) (combination z c) = paretoMean (z i))
    (hq : paretoMean (combination z c) ≠ 0)
    (hb : paretoMean (combination z b) = 1) :
    paretoVariance (normalizedProjection z c) ≤ paretoVariance (combination z b) := by
  rw [normalizedProjection_variance hz c hn hq,
    normalizedProjection_completion hz c b hn hq hb]
  exact le_add_of_nonneg_right (paretoInner_self_nonneg _)

end
end RiemannResearch.RH.Pareto.FiniteSchur
