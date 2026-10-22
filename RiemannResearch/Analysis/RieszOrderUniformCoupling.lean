import RiemannResearch.Analysis.TwistedRieszFilterOrder
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Uniform coupling of ordinates at every finite Riesz order

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

API source reviewed during preparation: mathlib commit
51e6992efd06126df61a496bebf8f49482a4e129.

This is finite real algebra and elementary exponential comparison. It uses
no hypothesis about the location, separation, simplicity, or distribution of
zeta zeros. In particular the hypothesis `1 / 2 ≤ β` is a parameter range,
not an assertion of RH. No Fourier-integral identity is asserted here.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.TwistedRieszFilter

def reciprocalSquareSum (r : ℕ) (β : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), 1 / (β + (j : ℝ)) ^ 2

def frequencyRatioDenominator (r : ℕ) (β t : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (r + 1), (1 + t ^ 2 / (β + (j : ℝ)) ^ 2)

def normalizedFrequencyKernel (r : ℕ) (β t : ℝ) : ℝ :=
  1 / frequencyRatioDenominator r β t

def spectralDenominator (r : ℕ) (β t : ℝ) : ℝ :=
  ∏ j ∈ Finset.range (r + 1), ((β + (j : ℝ)) ^ 2 + t ^ 2)

def spectralKernel (r : ℕ) (β t : ℝ) : ℝ :=
  (r.factorial : ℝ) ^ 2 / spectralDenominator r β t

lemma reciprocal_square_step {u : ℝ} (hu : 0 < u) :
    1 / (u + 1) ^ 2 ≤ 1 / u - 1 / (u + 1) := by
  have hu1 : 0 < u + 1 := by linarith
  have hid : 1 / u - 1 / (u + 1) = 1 / (u * (u + 1)) := by
    field_simp [ne_of_gt hu, ne_of_gt hu1]
    <;> ring
  rw [hid]
  apply one_div_le_one_div_of_le (mul_pos hu hu1)
  nlinarith

/-- The remainder term is retained, so this is a finite estimate with no
summability theorem or passage to infinite order. -/
theorem reciprocalSquareSum_telescoping (r : ℕ) {β : ℝ} (hβ : 0 < β) :
    reciprocalSquareSum r β ≤
      1 / β ^ 2 + 1 / β - 1 / (β + (r : ℝ)) := by
  induction r with
  | zero =>
    simp [reciprocalSquareSum]
  | succ r ih =>
    have hu : 0 < β + (r : ℝ) := by positivity
    have hs := reciprocal_square_step hu
    unfold reciprocalSquareSum at ih ⊢
    rw [show r.succ + 1 = (r + 1) + 1 from rfl, Finset.sum_range_succ]
    simp only [Nat.cast_succ, ← add_assoc]
    calc
      (∑ j ∈ Finset.range (r + 1), 1 / (β + (j : ℝ)) ^ 2) +
          1 / (β + (r : ℝ) + 1) ^ 2 ≤
          (1 / β ^ 2 + 1 / β - 1 / (β + (r : ℝ))) +
            (1 / (β + (r : ℝ)) - 1 / (β + (r : ℝ) + 1)) :=
        add_le_add ih hs
      _ = 1 / β ^ 2 + 1 / β - 1 / (β + (r : ℝ) + 1) := by ring

theorem reciprocalSquareSum_le (r : ℕ) {β : ℝ} (hβ : 0 < β) :
    reciprocalSquareSum r β ≤ 1 / β ^ 2 + 1 / β := by
  have hr : 0 ≤ 1 / (β + (r : ℝ)) := by positivity
  linarith [reciprocalSquareSum_telescoping r hβ]

theorem reciprocalSquareSum_le_six (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) :
    reciprocalSquareSum r β ≤ 6 := by
  have hb : 0 < β := by linarith
  have h1 : 1 / β ≤ 2 := by
    apply (div_le_iff₀ hb).mpr
    linarith
  have h2 : 1 / β ^ 2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hb)).mpr
    nlinarith [sq_nonneg (β - 1 / 2)]
  linarith [reciprocalSquareSum_le r hb]

theorem frequencyRatioDenominator_pos (r : ℕ) (β t : ℝ) :
    0 < frequencyRatioDenominator r β t := by
  unfold frequencyRatioDenominator
  apply Finset.prod_pos
  intro j hj
  have h : 0 ≤ t ^ 2 / (β + (j : ℝ)) ^ 2 :=
    div_nonneg (sq_nonneg t) (sq_nonneg _)
  linarith

theorem frequencyRatioDenominator_one_le (r : ℕ) (β t : ℝ) :
    1 ≤ frequencyRatioDenominator r β t := by
  unfold frequencyRatioDenominator
  calc
    (1 : ℝ) = ∏ j ∈ Finset.range (r + 1), (1 : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.range (r + 1), (1 + t ^ 2 / (β + (j : ℝ)) ^ 2) := by
      apply Finset.prod_le_prod
      · intro j hj
        norm_num
      · intro j hj
        have h : 0 ≤ t ^ 2 / (β + (j : ℝ)) ^ 2 :=
          div_nonneg (sq_nonneg t) (sq_nonneg _)
        linarith

theorem normalizedFrequencyKernel_le_one (r : ℕ) (β t : ℝ) :
    normalizedFrequencyKernel r β t ≤ 1 := by
  unfold normalizedFrequencyKernel
  apply (div_le_iff₀ (frequencyRatioDenominator_pos r β t)).mpr
  simpa using frequencyRatioDenominator_one_le r β t

theorem frequencyRatioDenominator_le_exp (r : ℕ) (β t : ℝ) :
    frequencyRatioDenominator r β t ≤
      Real.exp (t ^ 2 * reciprocalSquareSum r β) := by
  have h := Real.prod_one_add_le_exp_sum (Finset.range (r + 1))
    (f := fun j : ℕ => t ^ 2 / (β + (j : ℝ)) ^ 2)
    (fun j => div_nonneg (sq_nonneg t) (sq_nonneg _))
  have hs : (∑ j ∈ Finset.range (r + 1), t ^ 2 / (β + (j : ℝ)) ^ 2) =
      t ^ 2 * reciprocalSquareSum r β := by
    simp [reciprocalSquareSum, Finset.mul_sum, div_eq_mul_inv]
  simpa only [frequencyRatioDenominator, hs] using h

/-- The exact positive-kernel inverse estimate. -/
theorem normalizedFrequencyKernel_gaussian_exact (r : ℕ) (β t : ℝ) :
    Real.exp (-(t ^ 2 * reciprocalSquareSum r β)) ≤
      normalizedFrequencyKernel r β t := by
  have h := one_div_le_one_div_of_le
    (frequencyRatioDenominator_pos r β t)
    (frequencyRatioDenominator_le_exp r β t)
  simpa only [normalizedFrequencyKernel, Real.exp_neg, one_div] using h

theorem normalizedFrequencyKernel_gaussian (r : ℕ) {β : ℝ}
    (hβ : 0 < β) (t : ℝ) :
    Real.exp (-((1 / β ^ 2 + 1 / β) * t ^ 2)) ≤
      normalizedFrequencyKernel r β t := by
  have hs := reciprocalSquareSum_le r hβ
  calc
    Real.exp (-((1 / β ^ 2 + 1 / β) * t ^ 2)) ≤
        Real.exp (-(t ^ 2 * reciprocalSquareSum r β)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg t]
    _ ≤ normalizedFrequencyKernel r β t :=
      normalizedFrequencyKernel_gaussian_exact r β t

/-- Increasing the finite smoothing order cannot make the normalized
kernel arbitrarily narrow near its center. The bound is uniform in order,
and throughout the entire real parameter half-line `β ≥ 1/2`. -/
theorem normalizedFrequencyKernel_uniform_coupling (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (t : ℝ) :
    Real.exp (-6 * t ^ 2) ≤ normalizedFrequencyKernel r β t := by
  have hs := reciprocalSquareSum_le_six r hβ
  calc
    Real.exp (-6 * t ^ 2) ≤
        Real.exp (-(t ^ 2 * reciprocalSquareSum r β)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg t]
    _ ≤ normalizedFrequencyKernel r β t :=
      normalizedFrequencyKernel_gaussian_exact r β t

theorem spectralDenominator_pos (r : ℕ) {β : ℝ}
    (hβ : 0 < β) (t : ℝ) :
    0 < spectralDenominator r β t := by
  unfold spectralDenominator
  apply Finset.prod_pos
  intro j hj
  have hjb : 0 < β + (j : ℝ) := by positivity
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hjb) (sq_nonneg t)

theorem spectralKernel_pos (r : ℕ) {β : ℝ}
    (hβ : 0 < β) (t : ℝ) :
    0 < spectralKernel r β t := by
  unfold spectralKernel
  exact div_pos (sq_pos_of_pos (by exact_mod_cast Nat.factorial_pos r))
    (spectralDenominator_pos r hβ t)

theorem spectralDenominator_factorization (r : ℕ) {β : ℝ}
    (hβ : 0 < β) (t : ℝ) :
    spectralDenominator r β t =
      spectralDenominator r β 0 * frequencyRatioDenominator r β t := by
  unfold spectralDenominator frequencyRatioDenominator
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hjb : β + (j : ℝ) ≠ 0 := ne_of_gt (by positivity)
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
  field_simp [hjb]
  <;> ring

/-- This connects the positive inverse-product definition to the actual
finite-order rational spectral kernel, with its factorial normalization. -/
theorem spectralKernel_ratio (r : ℕ) {β : ℝ}
    (hβ : 0 < β) (t : ℝ) :
    spectralKernel r β t / spectralKernel r β 0 =
      normalizedFrequencyKernel r β t := by
  have hd : spectralDenominator r β 0 ≠ 0 :=
    ne_of_gt (spectralDenominator_pos r hβ 0)
  have hf : frequencyRatioDenominator r β t ≠ 0 :=
    ne_of_gt (frequencyRatioDenominator_pos r β t)
  have hn : (r.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r
  unfold spectralKernel normalizedFrequencyKernel
  rw [spectralDenominator_factorization r hβ t]
  field_simp [hd, hf, hn]
  <;> ring

theorem spectralKernel_peak (r : ℕ) (β : ℝ) :
    spectralKernel r β 0 = realAmplitude r β ^ 2 := by
  unfold spectralKernel spectralDenominator realAmplitude realDenominator
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
    Finset.prod_pow, div_pow]

/-- The requested coupling inequality for the exact kernel. It makes no
assumption about zeta zeros or RH. -/
theorem spectralKernel_uniform_coupling (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (t : ℝ) :
    Real.exp (-6 * t ^ 2) ≤
      spectralKernel r β t / spectralKernel r β 0 := by
  rw [spectralKernel_ratio r (by linarith : 0 < β) t]
  exact normalizedFrequencyKernel_uniform_coupling r hβ t

theorem spectralKernel_peak_bounds (r : ℕ) {β : ℝ}
    (hβ : (1 / 2 : ℝ) ≤ β) (t : ℝ) :
    Real.exp (-6 * t ^ 2) * spectralKernel r β 0 ≤ spectralKernel r β t ∧
      spectralKernel r β t ≤ spectralKernel r β 0 := by
  have hb : 0 < β := by linarith
  have hp := spectralKernel_pos r hb 0
  constructor
  · exact (le_div_iff₀ hp).mp (spectralKernel_uniform_coupling r hβ t)
  · have hu := normalizedFrequencyKernel_le_one r β t
    rw [← spectralKernel_ratio r hb t] at hu
    simpa using (div_le_iff₀ hp).mp hu

end RiemannResearch.Analysis.TwistedRieszFilter
