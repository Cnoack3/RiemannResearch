import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Finite spectral cutoff repair

Source: user-provided argument, `RH_Two_Seed_Threshold.tex`, Section 11,
especially the spectral cutoff theorem and repeated-fit identity.

This module proves the finite spectral arithmetic without a spectral-gap
assumption. `eigenvalue i` is an information eigenvalue in `[0,1]`, while
`mass i` is the squared coefficient of the target in its eigendirection.
Zero eigenvalues are allowed and are never inverted by a positive cutoff.

The paper's application additionally requires a provider identifying these
finite data with the weighted CRT covariance and realizing the stated sums
as the norm and error of a legal two-seed vector. That analytic/operator
identification is not supplied by this module. The inequalities here have
no unresolved arithmetic hypotheses and assert no approximation convergence.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.SpectralCutoff

noncomputable section

/-- Error of the unrestricted legal optimizer in one information mode. -/
def optimalTerm (eigenvalue mass : ℝ) : ℝ := (1 - eigenvalue) * mass

/-- Exact error when the mode is fitted above the cutoff and omitted below it. -/
def errorTerm (cutoff eigenvalue mass : ℝ) : ℝ :=
  if cutoff ≤ eigenvalue then (eigenvalue⁻¹ - 1) * mass else mass

/-- Squared norm charged by a retained information mode. -/
def normTerm (cutoff eigenvalue mass : ℝ) : ℝ :=
  if cutoff ≤ eigenvalue then eigenvalue⁻¹ * mass else 0

/-- Target mass deliberately omitted by the partial repair. -/
def omittedTerm (cutoff eigenvalue mass : ℝ) : ℝ :=
  if cutoff ≤ eigenvalue then 0 else mass

theorem errorTerm_of_below {τ lam μ : ℝ} (h : lam < τ) :
    errorTerm τ lam μ = μ := by
  simp [errorTerm, not_le.mpr h]

theorem normTerm_of_below {τ lam μ : ℝ} (h : lam < τ) :
    normTerm τ lam μ = 0 := by
  simp [normTerm, not_le.mpr h]

/-- Exact one-mode accounting: omitted mass is retained with its full sign. -/
theorem normTerm_exact (τ lam μ : ℝ) :
    normTerm τ lam μ = μ + errorTerm τ lam μ - 2 * omittedTerm τ lam μ := by
  unfold normTerm errorTerm omittedTerm
  split_ifs <;> ring

private theorem inverse_error_identity {lam μ : ℝ} (hlam : lam ≠ 0) :
    lam * ((lam⁻¹ - 1) * μ) = (1 - lam) * μ := by
  field_simp [hlam]
  <;> ring

private theorem inverse_error_nonneg {lam μ : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hμ : 0 ≤ μ) :
    0 ≤ (lam⁻¹ - 1) * μ := by
  have hi : 0 ≤ lam⁻¹ - 1 := by
    by_contra hn
    have hn' : lam⁻¹ - 1 < 0 := lt_of_not_ge hn
    have hp := mul_neg_of_pos_of_neg hlam hn'
    have he := inverse_error_identity (μ := (1 : ℝ)) (ne_of_gt hlam)
    nlinarith
  exact mul_nonneg hi hμ

theorem optimalTerm_nonneg {lam μ : ℝ} (hlam : lam ≤ 1) (hμ : 0 ≤ μ) :
    0 ≤ optimalTerm lam μ :=
  mul_nonneg (sub_nonneg.mpr hlam) hμ

theorem errorTerm_nonneg {τ lam μ : ℝ}
    (hτ : 0 < τ) (hlam : lam ≤ 1) (hμ : 0 ≤ μ) :
    0 ≤ errorTerm τ lam μ := by
  unfold errorTerm
  split_ifs with ht
  · exact inverse_error_nonneg (lt_of_lt_of_le hτ ht) hlam hμ
  · exact hμ

/-- Pointwise cutoff estimate, before summation or division. -/
theorem scaled_errorTerm_le {τ lam μ : ℝ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hlam : lam ≤ 1) (hμ : 0 ≤ μ) :
    min τ (1 - τ) * errorTerm τ lam μ ≤ optimalTerm lam μ := by
  unfold errorTerm optimalTerm
  split_ifs with ht
  · have hlampos := lt_of_lt_of_le hτ ht
    have hr := inverse_error_nonneg hlampos hlam hμ
    have hd : min τ (1 - τ) ≤ lam := le_trans (min_le_left _ _) ht
    have hp := mul_nonneg (sub_nonneg.mpr hd) hr
    have he := inverse_error_identity (μ := μ) (ne_of_gt hlampos)
    nlinarith
  · have hd : min τ (1 - τ) ≤ 1 - lam := by
      have hm := min_le_right τ (1 - τ)
      have ht' : lam < τ := lt_of_not_ge ht
      linarith
    exact mul_le_mul_of_nonneg_right hd hμ

/-- The norm comparison charges only the excess over the original target mass. -/
theorem scaled_normTerm_excess_le {τ lam μ : ℝ}
    (hτ : 0 < τ) (hlam : lam ≤ 1) (hμ : 0 ≤ μ) :
    τ * (normTerm τ lam μ - μ) ≤ optimalTerm lam μ := by
  unfold normTerm optimalTerm
  split_ifs with ht
  · have hlampos := lt_of_lt_of_le hτ ht
    have hr := inverse_error_nonneg hlampos hlam hμ
    have hp := mul_nonneg (sub_nonneg.mpr ht) hr
    have he := inverse_error_identity (μ := μ) (ne_of_gt hlampos)
    nlinarith
  · have hp := mul_nonneg hτ.le hμ
    have he := mul_nonneg (sub_nonneg.mpr hlam) hμ
    nlinarith

variable {ι : Type*}

def optimalError (s : Finset ι) (lam μ : ι → ℝ) : ℝ :=
  ∑ i ∈ s, optimalTerm (lam i) (μ i)

def cutoffError (s : Finset ι) (τ : ℝ) (lam μ : ι → ℝ) : ℝ :=
  ∑ i ∈ s, errorTerm τ (lam i) (μ i)

def cutoffNorm (s : Finset ι) (baseline τ : ℝ) (lam μ : ι → ℝ) : ℝ :=
  baseline + ∑ i ∈ s, normTerm τ (lam i) (μ i)

def targetMass (s : Finset ι) (μ : ι → ℝ) : ℝ := ∑ i ∈ s, μ i

def omittedMass (s : Finset ι) (τ : ℝ) (lam μ : ι → ℝ) : ℝ :=
  ∑ i ∈ s, omittedTerm τ (lam i) (μ i)

/-- Finite exact accounting, including the omitted mass and its coefficient. -/
theorem cutoffNorm_exact (s : Finset ι) (baseline τ : ℝ) (lam μ : ι → ℝ) :
    cutoffNorm s baseline τ lam μ = baseline + targetMass s μ +
      cutoffError s τ lam μ - 2 * omittedMass s τ lam μ := by
  simp only [cutoffNorm, targetMass, cutoffError, omittedMass, normTerm_exact,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem cutoffError_le (s : Finset ι) {τ : ℝ} (lam μ : ι → ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hlam : ∀ i ∈ s, lam i ≤ 1) (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    cutoffError s τ lam μ ≤ optimalError s lam μ / min τ (1 - τ) := by
  apply (le_div_iff₀ (lt_min hτ (sub_pos.mpr hτ1))).2
  rw [mul_comm]
  unfold cutoffError optimalError
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    scaled_errorTerm_le hτ hτ1 (hlam i hi) (hμ i hi)

theorem cutoffNorm_le (s : Finset ι) (baseline : ℝ) {τ : ℝ} (lam μ : ι → ℝ)
    (hτ : 0 < τ) (hlam : ∀ i ∈ s, lam i ≤ 1)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    cutoffNorm s baseline τ lam μ ≤ baseline + targetMass s μ +
      optimalError s lam μ / τ := by
  have hs : τ * (cutoffNorm s baseline τ lam μ - (baseline + targetMass s μ)) ≤
      optimalError s lam μ := by
    calc
      _ = ∑ i ∈ s, τ * (normTerm τ (lam i) (μ i) - μ i) := by
        simp only [cutoffNorm, targetMass, mul_sub, mul_add,
          Finset.mul_sum, Finset.sum_sub_distrib]
        ring
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        scaled_normTerm_excess_le hτ (hlam i hi) (hμ i hi)
  have hd : cutoffNorm s baseline τ lam μ - (baseline + targetMass s μ) ≤
      optimalError s lam μ / τ := by
    apply (le_div_iff₀ hτ).2
    simpa [mul_comm] using hs
  linarith

/-- The factor-two theorem permits zero eigenvalues and imposes no lower gap. -/
theorem half_cutoff_bounds (s : Finset ι) (baseline : ℝ) (lam μ : ι → ℝ)
    (hlam : ∀ i ∈ s, lam i ≤ 1) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hnorm : baseline + targetMass s μ = 1) :
    cutoffError s (1 / 2) lam μ ≤ 2 * optimalError s lam μ ∧
      cutoffNorm s baseline (1 / 2) lam μ ≤ 1 + 2 * optimalError s lam μ := by
  have he := cutoffError_le s lam μ (τ := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num) hlam hμ
  have hn := cutoffNorm_le s baseline lam μ (τ := (1 / 2 : ℝ)) (by norm_num) hlam hμ
  norm_num at he hn
  constructor
  · nlinarith
  · rw [hnorm] at hn
    nlinarith

/-- Exact fitting is the full negative moment when every target mode is retained. -/
theorem cutoffError_of_all_retained (s : Finset ι) (τ : ℝ) (lam μ : ι → ℝ)
    (h : ∀ i ∈ s, τ ≤ lam i) :
    cutoffError s τ lam μ = ∑ i ∈ s, ((lam i)⁻¹ - 1) * μ i := by
  apply Finset.sum_congr rfl
  intro i hi
  simp [errorTerm, h i hi]

/-- Fitting below-threshold modes is not silently included in partial repair. -/
theorem cutoffNorm_of_all_retained (s : Finset ι) (baseline τ : ℝ) (lam μ : ι → ℝ)
    (h : ∀ i ∈ s, τ ≤ lam i) :
    cutoffNorm s baseline τ lam μ = baseline + ∑ i ∈ s, (lam i)⁻¹ * μ i := by
  unfold cutoffNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp [normTerm, h i hi]

/-- The numerical implication uses the strict certificate as an explicit input. -/
theorem certified_half_cutoff_bounds (s : Finset ι) (baseline : ℝ) (lam μ : ι → ℝ)
    (hlam : ∀ i ∈ s, lam i ≤ 1) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hnorm : baseline + targetMass s μ = 1)
    (hcert : optimalError s lam μ < 53 / 1000) :
    cutoffError s (1 / 2) lam μ < 106 / 1000 ∧
      cutoffNorm s baseline (1 / 2) lam μ < 1106 / 1000 := by
  obtain ⟨he, hn⟩ := half_cutoff_bounds s baseline lam μ hlam hμ hnorm
  constructor <;> linarith

end

end RiemannResearch.LinearAlgebra.SpectralCutoff
