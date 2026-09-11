import RiemannResearch.RH.DyadicArithmeticFourierBridge

/-!
# Exact signed mixtures of actual damped arithmetic remainders

Source: user-provided FourierZeroDampingVerification20260911(1).md;
independently developed application of the established physical Parseval
and actual arithmetic Fourier bridge. This continuation of FourierZeroDampingVerification20260911(1).md identifies
the complete energy of finite real linear combinations of actual remainders.
All damping and Fourier interactions remain inside exact signed expressions.
Only positivity of the finitely many used dampings is required. No uniform
estimate, small mixture, or legal-recovery assertion is made here.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
noncomputable section

/-- The signed boundary Gram series of two actual dampings converges. -/
theorem dyadicNormalizationBoundaryCoefficient_mixed_summable
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    Summable (fun i : ℕ => (1 / 4 : ℝ) *
      dyadicNormalizationBoundaryCoefficient ε i *
      dyadicNormalizationBoundaryCoefficient δ i) := by
  apply (dyadicBoundary_mixed_pairings_summable
    (dyadicNormalizationRemainder ε) (dyadicNormalizationRemainder δ)).congr
  intro i
  rw [← dyadicNormalizationRemainder_boundaryCoordinate hε,
    ← dyadicNormalizationRemainder_boundaryCoordinate hδ]
  dsimp [dyadicBoundaryCoordinate, dyadicBoundaryVector]
  ring

/-- Exact mixed damping energy, with all signed arithmetic coefficients intact. -/
theorem dyadicNormalizationRemainder_inner_eq_signed_boundary
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    inner ℝ (dyadicNormalizationRemainder ε) (dyadicNormalizationRemainder δ) =
      ∑' i : ℕ, (1 / 4 : ℝ) *
        dyadicNormalizationBoundaryCoefficient ε i *
        dyadicNormalizationBoundaryCoefficient δ i := by
  have hp := dyadicBoundary_parseval_inner
    (dyadicNormalizationRemainder ε) (dyadicNormalizationRemainder δ)
  have hm : inner ℝ hilbertOne (dyadicNormalizationRemainder ε) = 0 := by
    rw [real_inner_comm]
    exact dyadicNormalizationRemainder_inner_one ε hε
  rw [dyadicNormalizationRemainder_projection ε hε,
    dyadicNormalizationRemainder_projection δ hδ,
    hm, zero_mul, zero_add] at hp
  rw [hp]
  apply tsum_congr
  intro i
  rw [← dyadicNormalizationRemainder_boundaryCoordinate hε,
    ← dyadicNormalizationRemainder_boundaryCoordinate hδ]
  dsimp [dyadicBoundaryCoordinate, dyadicBoundaryVector]
  ring

/-- Coordinates of a finite signed damping mixture are its signed scalar sums. -/
theorem dyadicNormalizationRemainder_finite_boundaryCoordinate
    {κ : Type*} (s : Finset κ) (a ε : κ → ℝ)
    (hε : ∀ k ∈ s, 0 < ε k) (i : ℕ) :
    dyadicBoundaryCoordinate
      (∑ k ∈ s, a k • dyadicNormalizationRemainder (ε k)) i =
      ∑ k ∈ s, a k * dyadicNormalizationBoundaryCoefficient (ε k) i := by
  unfold dyadicBoundaryCoordinate
  rw [inner_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [real_inner_smul_right]
  calc
    _ = a k * dyadicBoundaryCoordinate (dyadicNormalizationRemainder (ε k)) i := by
      unfold dyadicBoundaryCoordinate
      ring
    _ = _ := by rw [dyadicNormalizationRemainder_boundaryCoordinate (hε k hk)]

/-- The complete squared-coordinate series of every finite signed mixture converges. -/
theorem dyadicNormalizationRemainder_finite_boundaryEnergy_summable
    {κ : Type*} (s : Finset κ) (a ε : κ → ℝ)
    (hε : ∀ k ∈ s, 0 < ε k) :
    Summable (fun i : ℕ => (1 / 4 : ℝ) *
      (∑ k ∈ s, a k * dyadicNormalizationBoundaryCoefficient (ε k) i) ^ 2) := by
  let f := ∑ k ∈ s, a k • dyadicNormalizationRemainder (ε k)
  apply (dyadicBoundary_mixed_pairings_summable f f).congr
  intro i
  rw [← dyadicNormalizationRemainder_finite_boundaryCoordinate s a ε hε]
  dsimp [f, dyadicBoundaryCoordinate, dyadicBoundaryVector]
  ring

/-- Exact norm of a finite real mixture. Negative weights are allowed; every
cross term between dampings stays inside the full boundary square. -/
theorem dyadicNormalizationRemainder_finite_norm_sq_eq_signed_boundary
    {κ : Type*} (s : Finset κ) (a ε : κ → ℝ)
    (hε : ∀ k ∈ s, 0 < ε k) :
    ‖∑ k ∈ s, a k • dyadicNormalizationRemainder (ε k)‖ ^ 2 =
      ∑' i : ℕ, (1 / 4 : ℝ) *
        (∑ k ∈ s, a k * dyadicNormalizationBoundaryCoefficient (ε k) i) ^ 2 := by
  let f := ∑ k ∈ s, a k • dyadicNormalizationRemainder (ε k)
  have hfix : dyadicQuotientProjection f = f := by
    dsimp [f]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul, dyadicNormalizationRemainder_projection (ε k) (hε k hk)]
  have hmean : inner ℝ f hilbertOne = 0 := by
    dsimp [f]
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro k hk
    rw [real_inner_smul_left,
      dyadicNormalizationRemainder_inner_one (ε k) (hε k hk), mul_zero]
  have hp := dyadicBoundary_parseval_norm_sq f
  have hmean' : inner ℝ hilbertOne f = 0 := by rw [real_inner_comm]; exact hmean
  rw [hfix, hmean',
    zero_pow (by norm_num : 2 ≠ 0), zero_add] at hp
  change ‖f‖ ^ 2 = _
  rw [hp]
  apply tsum_congr
  intro i
  rw [← dyadicNormalizationRemainder_finite_boundaryCoordinate s a ε hε]
  dsimp [f, dyadicBoundaryCoordinate, dyadicBoundaryVector]
  ring

/-- The complete Fourier row of a finite mixture is the actual real coefficient.
The frequency sum is complete before the finite damping mixture is formed. -/
theorem dyadicNormalizationRemainder_finite_fourierRow_eq_coefficient
    {κ : Type*} (s : Finset κ) (a ε : κ → ℝ)
    (hε : ∀ k ∈ s, 0 < ε k) (i : ℕ) :
    (∑ k ∈ s, (a k : ℂ) * (∑' h, dyadicSignedFourierTerm (ε k) i h)) =
      ((∑ k ∈ s, a k * dyadicNormalizationBoundaryCoefficient (ε k) i : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  simp only [Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(dyadicSignedFourierBridge_proved (ε k) (hε k hk) i).tsum_eq]

/-- Exact mixture energy in full signed Fourier rows, retaining both all
frequency interactions and all interactions between different dampings. -/
theorem dyadicNormalizationRemainder_finite_norm_sq_eq_signed_fourier
    {κ : Type*} (s : Finset κ) (a ε : κ → ℝ)
    (hε : ∀ k ∈ s, 0 < ε k) :
    ‖∑ k ∈ s, a k • dyadicNormalizationRemainder (ε k)‖ ^ 2 =
      ∑' i : ℕ, (1 / 4 : ℝ) *
        ‖∑ k ∈ s, (a k : ℂ) * (∑' h, dyadicSignedFourierTerm (ε k) i h)‖ ^ 2 := by
  rw [dyadicNormalizationRemainder_finite_norm_sq_eq_signed_boundary s a ε hε]
  apply tsum_congr
  intro i
  rw [dyadicNormalizationRemainder_finite_fourierRow_eq_coefficient s a ε hε]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The full Fourier energy of a finite signed damping mixture is summable. -/
theorem dyadicNormalizationRemainder_finite_fourierEnergy_summable
    {κ : Type*} (s : Finset κ) (a ε : κ → ℝ)
    (hε : ∀ k ∈ s, 0 < ε k) :
    Summable (fun i : ℕ => (1 / 4 : ℝ) *
      ‖∑ k ∈ s, (a k : ℂ) * (∑' h, dyadicSignedFourierTerm (ε k) i h)‖ ^ 2) := by
  apply (dyadicNormalizationRemainder_finite_boundaryEnergy_summable s a ε hε).congr
  intro i
  rw [dyadicNormalizationRemainder_finite_fourierRow_eq_coefficient s a ε hε]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end
end RiemannResearch.RH.Pareto
