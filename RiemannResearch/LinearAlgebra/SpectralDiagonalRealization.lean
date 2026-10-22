import RiemannResearch.LinearAlgebra.SpectralRepeatedFit

/-!
# Diagonal realization of the spectral cutoff formulas

Source: user-provided argument, `RH_Two_Seed_Threshold.tex`, Section 11.

The cutoff sums are derived from the diagonal quadratic model, rather than
postulated as norm identities. A positive threshold forces every inverted
coordinate to have strictly positive eigenvalue. The missing provider for
the application is the identification of this quadratic model with the
actual weighted CRT covariance and its legal synthesis map.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.SpectralCutoff

noncomputable section

/-- The coefficient used to synthesize a retained eigendirection. -/
def cutoffAmplitude (τ lam : ℝ) : ℝ := if τ ≤ lam then lam⁻¹ else 0

/-- The quadratic squared norm in an information mode. -/
def modalNorm (lam μ t : ℝ) : ℝ := lam * t ^ 2 * μ

/-- Retained modes fit exactly; omitted modes receive coefficient zero. -/
theorem cutoffAmplitude_profile {τ : ℝ} (lam : ℝ) (hτ : 0 < τ) :
    lam * cutoffAmplitude τ lam = if τ ≤ lam then 1 else 0 := by
  unfold cutoffAmplitude
  split_ifs with h
  · exact mul_inv_cancel₀ (ne_of_gt (lt_of_lt_of_le hτ h))
  · ring

/-- Derivation of the exact error formula from the modal quadratic. -/
theorem modalError_cutoffAmplitude {τ : ℝ} (lam μ : ℝ) (hτ : 0 < τ) :
    modalError lam μ (cutoffAmplitude τ lam) = errorTerm τ lam μ := by
  unfold modalError cutoffAmplitude errorTerm
  split_ifs with h
  · have hn : lam ≠ 0 := ne_of_gt (lt_of_lt_of_le hτ h)
    field_simp [hn]
    <;> ring
  · ring

/-- Derivation of the exact norm formula from the modal quadratic. -/
theorem modalNorm_cutoffAmplitude {τ : ℝ} (lam μ : ℝ) (hτ : 0 < τ) :
    modalNorm lam μ (cutoffAmplitude τ lam) = normTerm τ lam μ := by
  unfold modalNorm cutoffAmplitude normTerm
  split_ifs with h
  · have hn : lam ≠ 0 := ne_of_gt (lt_of_lt_of_le hτ h)
    field_simp [hn]
    <;> ring
  · ring

variable {ι : Type*}

def diagonalError (s : Finset ι) (lam μ t : ι → ℝ) : ℝ :=
  ∑ i ∈ s, modalError (lam i) (μ i) (t i)

def diagonalNorm (s : Finset ι) (baseline : ℝ) (lam μ t : ι → ℝ) : ℝ :=
  baseline + ∑ i ∈ s, modalNorm (lam i) (μ i) (t i)

/-- Exact diagonal error relative to its optimizer; no mixed term is discarded. -/
theorem diagonalError_exact (s : Finset ι) (lam μ t : ι → ℝ) :
    diagonalError s lam μ t = optimalError s lam μ +
      ∑ i ∈ s, lam i * (t i - 1) ^ 2 * μ i := by
  simp only [diagonalError, optimalError, modalError_exact, Finset.sum_add_distrib]

theorem diagonalError_cutoff (s : Finset ι) {τ : ℝ} (lam μ : ι → ℝ)
    (hτ : 0 < τ) :
    diagonalError s lam μ (fun i => cutoffAmplitude τ (lam i)) =
      cutoffError s τ lam μ := by
  apply Finset.sum_congr rfl
  intro i _
  exact modalError_cutoffAmplitude (lam i) (μ i) hτ

theorem diagonalNorm_cutoff (s : Finset ι) (baseline : ℝ) {τ : ℝ} (lam μ : ι → ℝ)
    (hτ : 0 < τ) :
    diagonalNorm s baseline lam μ (fun i => cutoffAmplitude τ (lam i)) =
      cutoffNorm s baseline τ lam μ := by
  unfold diagonalNorm cutoffNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact modalNorm_cutoffAmplitude (lam i) (μ i) hτ

/-- The explicit finite coefficient vector realizes the factor-two bounds. -/
theorem diagonal_half_cutoff (s : Finset ι) (baseline : ℝ) (lam μ : ι → ℝ)
    (hlam : ∀ i ∈ s, lam i ≤ 1) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hnorm : baseline + targetMass s μ = 1) :
    diagonalError s lam μ (fun i => cutoffAmplitude (1 / 2) (lam i)) ≤
        2 * optimalError s lam μ ∧
      diagonalNorm s baseline lam μ (fun i => cutoffAmplitude (1 / 2) (lam i)) ≤
        1 + 2 * optimalError s lam μ := by
  rw [diagonalError_cutoff s lam μ (by norm_num),
    diagonalNorm_cutoff s baseline lam μ (by norm_num)]
  exact half_cutoff_bounds s baseline lam μ hlam hμ hnorm

end

end RiemannResearch.LinearAlgebra.SpectralCutoff
