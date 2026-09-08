import RiemannResearch.LinearAlgebra.SpectralCutoffRepair

/-!
# Exact spectral cost of repeated coarse fitting

Source: user-provided argument, `RH_Two_Seed_Threshold.tex`, Section 11,
equation on the nondecreasing cost of repeatedly fitting a fixed coarse
profile inside an unchanged legal space.

The finite modal polynomial is proved exactly before any inequality.
The geometric amplitude improves the coarse residual but increases full
error once the first step has reached the full-error optimizer.
This module does not identify an abstract spectral tuple with the actual
weighted CRT operator; that provider remains separate.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.SpectralCutoff

noncomputable section

/-- Full squared error in one information eigenmode for synthesis amplitude `t`. -/
def modalError (lam μ t : ℝ) : ℝ := μ * (1 - 2 * lam * t + lam * t ^ 2)

/-- The exact square exposes every correction to the optimum `t = 1`. -/
theorem modalError_exact (lam μ t : ℝ) :
    modalError lam μ t = optimalTerm lam μ + lam * (t - 1) ^ 2 * μ := by
  unfold modalError optimalTerm
  ring

theorem modalError_ge_optimal {lam μ : ℝ} (t : ℝ) (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) :
    optimalTerm lam μ ≤ modalError lam μ t := by
  rw [modalError_exact]
  have hp := mul_nonneg (mul_nonneg hlam (sq_nonneg (t - 1))) hμ
  linarith

/-- Amplitude after `j` repeated coarse corrections. -/
def geometricAmplitude (j : ℕ) (lam : ℝ) : ℝ :=
  ∑ r ∈ Finset.range j, (1 - lam) ^ r

theorem geometricAmplitude_succ (j : ℕ) (lam : ℝ) :
    geometricAmplitude (j + 1) lam = geometricAmplitude j lam + (1 - lam) ^ j := by
  exact Finset.sum_range_succ _ _

theorem geometricAmplitude_residual (j : ℕ) (lam : ℝ) :
    1 - lam * geometricAmplitude j lam = (1 - lam) ^ j := by
  induction j with
  | zero => simp [geometricAmplitude]
  | succ j ih =>
      rw [geometricAmplitude_succ, pow_succ]
      nlinarith

/-- The excess amplitude beyond the first, already optimal correction. -/
def correctionSeries (j : ℕ) (lam : ℝ) : ℝ :=
  ∑ r ∈ Finset.range j, (1 - lam) ^ (r + 1)

theorem correctionSeries_succ (j : ℕ) (lam : ℝ) :
    correctionSeries (j + 1) lam = correctionSeries j lam + (1 - lam) ^ (j + 1) := by
  exact Finset.sum_range_succ _ _

theorem geometricAmplitude_after_first (j : ℕ) (lam : ℝ) :
    geometricAmplitude (j + 1) lam = 1 + correctionSeries j lam := by
  induction j with
  | zero => simp [geometricAmplitude, correctionSeries]
  | succ j ih =>
      rw [geometricAmplitude_succ, correctionSeries_succ, ih]
      ring

theorem correctionSeries_nonneg (j : ℕ) {lam : ℝ} (hlam : lam ≤ 1) :
    0 ≤ correctionSeries j lam := by
  exact Finset.sum_nonneg fun r _ => pow_nonneg (sub_nonneg.mpr hlam) _

/-- Exact one-mode full error after the first step and `j` further corrections. -/
theorem repeated_modal_error_exact (j : ℕ) (lam μ : ℝ) :
    modalError lam μ (geometricAmplitude (j + 1) lam) =
      optimalTerm lam μ + lam * (correctionSeries j lam) ^ 2 * μ := by
  rw [modalError_exact, geometricAmplitude_after_first]
  ring

/-- An exact signed formula for the price of one additional coarse correction. -/
theorem repeated_modal_error_increment (j : ℕ) (lam μ : ℝ) :
    modalError lam μ (geometricAmplitude (j + 2) lam) -
      modalError lam μ (geometricAmplitude (j + 1) lam) =
      lam * μ * (2 * correctionSeries j lam * (1 - lam) ^ (j + 1) +
        ((1 - lam) ^ (j + 1)) ^ 2) := by
  rw [show j + 2 = (j + 1) + 1 from rfl]
  rw [repeated_modal_error_exact, repeated_modal_error_exact, correctionSeries_succ]
  ring

theorem repeated_modal_error_nondecreasing (j : ℕ) {lam μ : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hμ : 0 ≤ μ) :
    modalError lam μ (geometricAmplitude (j + 1) lam) ≤
      modalError lam μ (geometricAmplitude (j + 2) lam) := by
  have hc := correctionSeries_nonneg j hlam1
  have hp : 0 ≤ (1 - lam) ^ (j + 1) := pow_nonneg (sub_nonneg.mpr hlam1) _
  have hs : 0 ≤ 2 * correctionSeries j lam * (1 - lam) ^ (j + 1) +
      ((1 - lam) ^ (j + 1)) ^ 2 := by
    have hm := mul_nonneg hc hp
    nlinarith [sq_nonneg ((1 - lam) ^ (j + 1))]
  have hi := mul_nonneg (mul_nonneg hlam0 hμ) hs
  rw [← repeated_modal_error_increment j lam μ] at hi
  linarith

variable {ι : Type*}

/-- Actual finite sum of modal quadratic errors, not an assumed optimizer identity. -/
def repeatedError (s : Finset ι) (j : ℕ) (lam μ : ι → ℝ) : ℝ :=
  ∑ i ∈ s, modalError (lam i) (μ i) (geometricAmplitude (j + 1) (lam i))

theorem repeatedError_exact (s : Finset ι) (j : ℕ) (lam μ : ι → ℝ) :
    repeatedError s j lam μ = optimalError s lam μ +
      ∑ i ∈ s, lam i * (correctionSeries j (lam i)) ^ 2 * μ i := by
  simp only [repeatedError, optimalError, repeated_modal_error_exact,
    Finset.sum_add_distrib]

theorem repeatedError_first (s : Finset ι) (lam μ : ι → ℝ) :
    repeatedError s 0 lam μ = optimalError s lam μ := by
  simp [repeatedError_exact, correctionSeries]

theorem repeatedError_nondecreasing (s : Finset ι) (j : ℕ) (lam μ : ι → ℝ)
    (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    repeatedError s j lam μ ≤ repeatedError s (j + 1) lam μ := by
  exact Finset.sum_le_sum fun i hi =>
    repeated_modal_error_nondecreasing j (hlam0 i hi) (hlam1 i hi) (hμ i hi)

/-- Simultaneously, each squared coarse residual decreases. -/
theorem coarse_residual_nonincreasing_step (j : ℕ) {lam μ : ℝ}
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hμ : 0 ≤ μ) :
    ((1 - lam) ^ (j + 1)) ^ 2 * μ ≤ ((1 - lam) ^ j) ^ 2 * μ := by
  have ht0 : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  have ht1 : 1 - lam ≤ 1 := by linarith
  have ht2 : (1 - lam) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hp := mul_nonneg (sq_nonneg ((1 - lam) ^ j)) hμ
  have hm := mul_nonneg (sub_nonneg.mpr ht2) hp
  have he : ((1 - lam) ^ (j + 1)) ^ 2 =
      (1 - lam) ^ 2 * ((1 - lam) ^ j) ^ 2 := by
    rw [pow_succ (1 - lam) j]
    ring
  rw [he]
  nlinarith

end

end RiemannResearch.LinearAlgebra.SpectralCutoff
