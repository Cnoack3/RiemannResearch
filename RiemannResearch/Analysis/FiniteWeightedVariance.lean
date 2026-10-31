/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite weighted variance and scalar offset completion

Source: independently developed from the user-requested common-cell arithmetic
investigation on October 15, 2026. The concrete RH consumer is
`CanonicalMobiusPrimeCells`.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedVariance
noncomputable section
variable {ι : Type*}
def mass (s : Finset ι) (w : ι → ℝ) : ℝ := ∑ i ∈ s, w i
def mean (s : Finset ι) (w f : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i * f i) / mass s w
def variance (s : Finset ι) (w f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * (f i - mean s w f) ^ 2

/-- Exact pairwise moment identity, including zero total mass and signed weights.
The canonical squarefree prefix response is an additional RH consumer. -/
theorem pairwise_moment_exact {ι : Type*} (s : Finset ι) (w f : ι → ℝ) :
    (∑ i ∈ s, w i * f i) ^ 2 +
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i - f j) ^ 2) / 2 =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * f i ^ 2) := by
  have ht : ∀ i j, w i * w j * (f i - f j) ^ 2 =
      (w i * f i ^ 2) * w j + w i * (w j * f j ^ 2) -
        2 * (w i * f i) * (w j * f j) := by
    intro i j
    ring
  simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  ring

theorem centered_sum (s : Finset ι) (w f : ι → ℝ) (hW : mass s w ≠ 0) :
    (∑ i ∈ s, w i * (f i - mean s w f)) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change (∑ i ∈ s, w i * f i) - mass s w * mean s w f = 0
  rw [mean, mul_div_cancel₀ _ hW, sub_self]

theorem translation_energy (s : Finset ι) (w f : ι → ℝ) (b : ℝ)
    (hW : mass s w ≠ 0) :
    (∑ i ∈ s, w i * (f i + b) ^ 2) =
      variance s w f + mass s w * (mean s w f + b) ^ 2 := by
  have hc := centered_sum s w f hW
  calc
    _ = ∑ i ∈ s, (w i * (f i - mean s w f) ^ 2 +
        (2 * (mean s w f + b)) * (w i * (f i - mean s w f)) +
        w i * (mean s w f + b) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hc, ← Finset.sum_mul]
      simp [variance, mass]

theorem moment_identity (s : Finset ι) (w f : ι → ℝ) (hW : mass s w ≠ 0) :
    mass s w * variance s w f =
      mass s w * (∑ i ∈ s, w i * f i ^ 2) -
        (∑ i ∈ s, w i * f i) ^ 2 := by
  have ht := translation_energy s w f 0 hW
  have hm : mass s w * mean s w f = ∑ i ∈ s, w i * f i := by
    exact mul_div_cancel₀ _ hW
  simp only [add_zero] at ht
  have hmul := congrArg (fun x : ℝ => mass s w * x) ht
  have hsq := congrArg (fun x : ℝ => x ^ 2) hm
  nlinarith only [hmul, hsq]

theorem pairwise_identity (s : Finset ι) (w f : ι → ℝ) (hW : mass s w ≠ 0) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i - f j) ^ 2) =
      2 * mass s w * variance s w f := by
  have ht : ∀ i j, w i * w j * (f i - f j) ^ 2 =
      (w i * f i ^ 2) * w j + w i * (w j * f j ^ 2) -
        2 * (w i * f i) * (w j * f j) := by
    intro i j
    ring
  simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  have hm := moment_identity s w f hW
  unfold mass at hm ⊢
  nlinarith

theorem variance_nonneg (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ variance s w f :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))

theorem variance_le_translation (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : mass s w ≠ 0) (b : ℝ) :
    variance s w f ≤ ∑ i ∈ s, w i * (f i + b) ^ 2 := by
  rw [translation_energy s w f b hW]
  exact le_add_of_nonneg_right (mul_nonneg (Finset.sum_nonneg hw) (sq_nonneg _))

theorem variance_mono (s t : Finset ι) (w f : ι → ℝ) (hst : s ⊆ t)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hs : mass s w ≠ 0) :
    variance s w f ≤ variance t w f := by
  calc
    _ ≤ ∑ i ∈ s, w i * (f i + -mean t w f) ^ 2 :=
      variance_le_translation s w f (fun i hi => hw i (hst hi)) hs _
    _ ≤ ∑ i ∈ t, w i * (f i + -mean t w f) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hst (fun i hi _ =>
        mul_nonneg (hw i hi) (sq_nonneg _))
    _ = _ := by simp [variance, sub_eq_add_neg]

theorem variance_le_of_pairwise (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : 0 < mass s w)
    (hfg : ∀ i ∈ s, ∀ j ∈ s, (f i - f j) ^ 2 ≤ (g i - g j) ^ 2) :
    variance s w f ≤ variance s w g := by
  have h : (∑ i ∈ s, ∑ j ∈ s, w i * w j * (f i - f j) ^ 2) ≤
      ∑ i ∈ s, ∑ j ∈ s, w i * w j * (g i - g j) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hfg i hi j hj) (mul_nonneg (hw i hi) (hw j hj))
  rw [pairwise_identity s w f hW.ne', pairwise_identity s w g hW.ne'] at h
  nlinarith
theorem variance_le_of_bounds (s : Finset ι) (w f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : mass s w ≠ 0) (lo hi : ℝ)
    (hlo : ∀ i ∈ s, lo ≤ f i) (hhi : ∀ i ∈ s, f i ≤ hi) :
    variance s w f ≤ mass s w * (hi - lo) ^ 2 / 4 := by
  calc
    _ ≤ ∑ i ∈ s, w i * (f i + -(lo + hi) / 2) ^ 2 :=
      variance_le_translation s w f hw hW _
    _ ≤ ∑ i ∈ s, w i * ((hi - lo) ^ 2 / 4) := by
      apply Finset.sum_le_sum
      intro i hi'
      apply mul_le_mul_of_nonneg_left _ (hw i hi')
      nlinarith [mul_nonneg (sub_nonneg.mpr (hlo i hi')) (sub_nonneg.mpr (hhi i hi'))]
    _ = _ := by rw [← Finset.sum_mul]; unfold mass; ring

/-- Exact minimum of two offset-dependent cell mean energies. -/
private theorem scalar_completion (K J S B : ℝ) (hK : K ≠ 0) :
    S + 2 * J * B + K * B ^ 2 =
      (K * S - J ^ 2) / K + K * (B + J / K) ^ 2 := by
  field_simp
  ring

theorem two_offset_completion (w v q r x y b : ℝ)
    (hK : w * q ^ 2 + v * r ^ 2 ≠ 0) :
    w * (x + q * b) ^ 2 + v * (y + r * b) ^ 2 =
      w * v * (r * x - q * y) ^ 2 / (w * q ^ 2 + v * r ^ 2) +
      (w * q ^ 2 + v * r ^ 2) *
        (b + (w * q * x + v * r * y) / (w * q ^ 2 + v * r ^ 2)) ^ 2 := by
  have h := scalar_completion (w * q ^ 2 + v * r ^ 2)
    (w * q * x + v * r * y) (w * x ^ 2 + v * y ^ 2) b hK
  have hd : (w * q ^ 2 + v * r ^ 2) * (w * x ^ 2 + v * y ^ 2) -
      (w * q * x + v * r * y) ^ 2 = w * v * (r * x - q * y) ^ 2 := by ring
  rw [hd] at h
  convert h using 1
  ring

theorem two_offset_lower (w v q r x y b : ℝ)
    (hK : 0 < w * q ^ 2 + v * r ^ 2) :
    w * v * (r * x - q * y) ^ 2 / (w * q ^ 2 + v * r ^ 2) ≤
      w * (x + q * b) ^ 2 + v * (y + r * b) ^ 2 := by
  rw [two_offset_completion w v q r x y b hK.ne']
  exact le_add_of_nonneg_right (mul_nonneg hK.le (sq_nonneg _))

/-- Any two coordinates give a certified local variance lower bound. -/
theorem pair_lower (s : Finset ι) (w f : ι → ℝ) (i j : ι)
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hw : ∀ k ∈ s, 0 ≤ w k) (hp : 0 < w i + w j) :
    w i * w j * (f i - f j) ^ 2 / (w i + w j) ≤ variance s w f := by
  classical
  have htwo := two_offset_lower (w i) (w j) 1 1 (f i) (f j)
    (-mean s w f) (by simpa using hp)
  simp only [one_pow, mul_one, one_mul] at htwo
  have hsubset : ({i, j} : Finset ι) ⊆ s := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> assumption
  have hsum : w i * (f i - mean s w f) ^ 2 +
      w j * (f j - mean s w f) ^ 2 ≤ variance s w f := by
    calc
      _ = ∑ k ∈ ({i, j} : Finset ι), w k * (f k - mean s w f) ^ 2 := by
        simp [hij]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k hk _ => mul_nonneg (hw k hk) (sq_nonneg _))
  have htwo' : w i * w j * (f i - f j) ^ 2 / (w i + w j) ≤
      w i * (f i - mean s w f) ^ 2 + w j * (f j - mean s w f) ^ 2 := by
    simpa [sub_eq_add_neg] using htwo
  exact htwo'.trans hsum

/-- Infimizing over constants preserves pointwise comparison of weights. -/
theorem variance_le_of_weights (s : Finset ι) (w v f : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : mass s w ≠ 0)
    (hwv : ∀ i ∈ s, w i ≤ v i) :
    variance s w f ≤ variance s v f := by
  calc
    _ ≤ ∑ i ∈ s, w i * (f i + -mean s v f) ^ 2 :=
      variance_le_translation s w f hw hW _
    _ ≤ ∑ i ∈ s, v i * (f i + -mean s v f) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hwv i hi) (sq_nonneg _)
    _ = _ := by simp [variance, sub_eq_add_neg]

theorem variance_le_mul_of_weights (s : Finset ι) (w v f : ι → ℝ) (C : ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hV : mass s v ≠ 0)
    (hvw : ∀ i ∈ s, v i ≤ C * w i) :
    variance s v f ≤ C * variance s w f := by
  calc
    _ ≤ ∑ i ∈ s, v i * (f i + -mean s w f) ^ 2 :=
      variance_le_translation s v f hv hV _
    _ ≤ ∑ i ∈ s, C * (w i * (f i + -mean s w f) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hvw i hi) (sq_nonneg (f i + -mean s w f))
    _ = _ := by simp [variance, sub_eq_add_neg, Finset.mul_sum]

/-- Exact scalar-affine completion, including the zero-slope case. -/
theorem affine_energy (s : Finset ι) (w f : ι → ℝ) (a b : ℝ)
    (hW : mass s w ≠ 0) :
    (∑ i ∈ s, w i * (a * f i + b) ^ 2) =
      a ^ 2 * variance s w f + mass s w * (a * mean s w f + b) ^ 2 := by
  have hc := centered_sum s w f hW
  calc
    _ = ∑ i ∈ s, (a ^ 2 * (w i * (f i - mean s w f) ^ 2) +
        (2 * a * (a * mean s w f + b)) * (w i * (f i - mean s w f)) +
        w i * (a * mean s w f + b) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hc, ← Finset.sum_mul]
      simp [variance, mass]

end
end RiemannResearch.Analysis.FiniteWeightedVariance
