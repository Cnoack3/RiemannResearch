import RiemannResearch.LinearAlgebra.OrthogonalSchurRepair

/-!
# Far-support gain bound after old-space reoptimization

Source: user-provided manuscript
`RH_Exact_Signed_Schur_Remainder_2026-09-16.tex`, far-support projection lemma.
The statements below formalize its Hilbert-space algebraic core.  In an
application, `p = P_K q`, `q - p = (I - P_K) q`, and `z` is the old packet's
far tail.  The arithmetic support and uniform tail-capture estimates are
explicit hypotheses; they are not asserted here.
-/

namespace RiemannResearch.LinearAlgebra
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Squared Cauchy--Schwarz, obtained from the existing exact Schur identity. -/
theorem schur_pairing_sq_le (x y : H) :
    (inner ℝ x y) ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  by_cases hy : y = 0
  · simp [hy]
  have hypos : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy) _
  have hnonneg := sq_nonneg ‖schurRemove y x‖
  rw [schurRemove_norm_sq x y hy] at hnonneg
  apply (div_le_iff₀ hypos).mp
  linarith

/-- Pythagoras for an explicitly supplied orthogonal old-space component. -/
theorem orthogonal_component_residual_norm_sq (q p : H)
    (hp : inner ℝ (q - p) p = 0) :
    ‖q - p‖ ^ 2 = ‖q‖ ^ 2 - ‖p‖ ^ 2 := by
  have hpair : inner ℝ q p = ‖p‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hp
    linarith
  have he := norm_add_smul_sq_exact q p (-1)
  simp only [neg_one_smul, ← sub_eq_add_neg] at he
  rw [hpair] at he
  linarith

/-- The full residualized Gram quadratic form retains at least `1 - τ`
of the raw quadratic form when the old-space capture is at most `τ`. -/
theorem orthogonal_component_residual_lower (q p : H) (τ : ℝ)
    (hp : inner ℝ (q - p) p = 0)
    (hcapture : ‖p‖ ^ 2 ≤ τ * ‖q‖ ^ 2) :
    (1 - τ) * ‖q‖ ^ 2 ≤ ‖q - p‖ ^ 2 := by
  rw [orthogonal_component_residual_norm_sq q p hp]
  nlinarith

/-- Tail concentration in the old component implies the required capture
bound. `tailP` models the old component restricted to the new support;
`hsupport` is the exact support-induced pairing identity. -/
theorem orthogonal_component_capture_of_tail (q p tailP : H) (τ : ℝ)
    (hτ : 0 ≤ τ) (hp : inner ℝ (q - p) p = 0)
    (hsupport : inner ℝ q p = inner ℝ q tailP)
    (htail : ‖tailP‖ ^ 2 ≤ τ * ‖p‖ ^ 2) :
    ‖p‖ ^ 2 ≤ τ * ‖q‖ ^ 2 := by
  by_cases hpzero : p = 0
  · simpa [hpzero] using mul_nonneg hτ (sq_nonneg ‖q‖)
  have hpPos : 0 < ‖p‖ ^ 2 := pow_pos (norm_pos_iff.mpr hpzero) _
  have hpair : inner ℝ q p = ‖p‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hp
    linarith
  have hcs := schur_pairing_sq_le q tailP
  rw [← hsupport, hpair] at hcs
  have hmul := mul_le_mul_of_nonneg_left htail (sq_nonneg ‖q‖)
  apply (mul_le_mul_iff_right₀ hpPos).mp
  nlinarith [hcs, hmul]

/-- Signed projection quotient after reoptimizing the old coefficients.
The hypotheses concern the actual full pairings, not absolute covariance
entry sums. -/
theorem orthogonal_component_gain_le (r q p : H) (τ A : ℝ)
    (hq : q ≠ 0) (hτ : τ < 1) (hA : 0 ≤ A)
    (hp : inner ℝ (q - p) p = 0)
    (hrp : inner ℝ r p = 0)
    (hcapture : ‖p‖ ^ 2 ≤ τ * ‖q‖ ^ 2)
    (hpair : (inner ℝ r q) ^ 2 ≤ A * ‖q‖ ^ 2) :
    (inner ℝ r (q - p)) ^ 2 / ‖q - p‖ ^ 2 ≤ A / (1 - τ) := by
  have ht : 0 < 1 - τ := sub_pos.mpr hτ
  have hnq : 0 < ‖q‖ ^ 2 := pow_pos (norm_pos_iff.mpr hq) _
  have hlower := orthogonal_component_residual_lower q p τ hp hcapture
  have hden : 0 < ‖q - p‖ ^ 2 := lt_of_lt_of_le (mul_pos ht hnq) hlower
  have hcorr : inner ℝ r (q - p) = inner ℝ r q := by
    rw [inner_sub_right, hrp, sub_zero]
  rw [hcorr]
  apply (div_le_div_iff₀ hden ht).mpr
  have hscaled := mul_le_mul_of_nonneg_left hpair (le_of_lt ht)
  have hAden := mul_le_mul_of_nonneg_left hlower hA
  nlinarith [hscaled, hAden]

/-- Energy removed by the exact optimized direction is bounded by the
far-tail energy, with the old-space reoptimization factor preserved. -/
theorem orthogonal_component_energy_gain_le (r q p z : H) (τ : ℝ)
    (hq : q ≠ 0) (hτ : τ < 1)
    (hp : inner ℝ (q - p) p = 0)
    (hrp : inner ℝ r p = 0)
    (hcapture : ‖p‖ ^ 2 ≤ τ * ‖q‖ ^ 2)
    (hsupport : inner ℝ r q = inner ℝ z q) :
    ‖r‖ ^ 2 - ‖schurRemove (q - p) r‖ ^ 2 ≤ ‖z‖ ^ 2 / (1 - τ) := by
  have ht : 0 < 1 - τ := sub_pos.mpr hτ
  have hnq : 0 < ‖q‖ ^ 2 := pow_pos (norm_pos_iff.mpr hq) _
  have hlower := orthogonal_component_residual_lower q p τ hp hcapture
  have hden : 0 < ‖q - p‖ ^ 2 := lt_of_lt_of_le (mul_pos ht hnq) hlower
  have hres : q - p ≠ 0 := by
    intro hz
    simp [hz] at hden
  have hpair : (inner ℝ r q) ^ 2 ≤ ‖z‖ ^ 2 * ‖q‖ ^ 2 := by
    rw [hsupport]
    exact schur_pairing_sq_le z q
  have hgain := orthogonal_component_gain_le r q p τ (‖z‖ ^ 2)
    hq hτ (sq_nonneg _) hp hrp hcapture hpair
  rw [schurRemove_norm_sq r (q - p) hres]
  linarith

end
end RiemannResearch.LinearAlgebra
