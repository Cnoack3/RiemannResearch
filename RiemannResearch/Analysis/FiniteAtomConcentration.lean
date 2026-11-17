import RiemannResearch.Analysis.FiniteAtomDispersion

/-!
# Correct concentration with a shared atom error budget

Source: repair of Lemma 14.6 in Christian Noack, `sdf_modified.pdf`,
21 July 2026. The exact Cauchy remainder comes first. Per-atom bounds
must be summed before applying the shell cardinality bound. Shell-local
means may not replace the one shared atom vector without its bias cost.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteAtomDispersion
variable {ι κ : Type*} [DecidableEq κ]

omit [DecidableEq κ] in
/-- Exact Cauchy identity; the full nonnegative pairwise remainder is retained. -/
theorem l1_sq_add_pairwise_eq_card_mul_loss (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u : κ → ℝ) :
    (∑ i ∈ s, |a i - u (label i)|) ^ 2 +
      (∑ i ∈ s, ∑ j ∈ s,
        (|a i - u (label i)| - |a j - u (label j)|) ^ 2) / 2 =
      s.card * loss s label a u := by
  simpa [loss, sq_abs] using FiniteWeightedVariance.pairwise_moment_exact
    s (fun _ => 1) (fun i => |a i - u (label i)|)

/-- Allocate a total budget; no fiber count or shell scale is discarded. -/
theorem loss_le_fiber_budgets (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u b : κ → ℝ)
    (hb : ∀ d ∈ s.image label,
      (∑ i ∈ fiber s label d, (a i - u d) ^ 2) ≤ b d) :
    loss s label a u ≤ ∑ d ∈ s.image label, b d := by
  rw [loss_eq_fiber_sum]
  exact Finset.sum_le_sum hb

theorem l1_sq_le_fiber_budgets (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u b : κ → ℝ)
    (hb : ∀ d ∈ s.image label,
      (∑ i ∈ fiber s label d, (a i - u d) ^ 2) ≤ b d) :
    (∑ i ∈ s, |a i - u (label i)|) ^ 2 ≤
      s.card * ∑ d ∈ s.image label, b d := by
  exact (l1_sq_le_card_mul_loss s label a u).trans
    (mul_le_mul_of_nonneg_left (loss_le_fiber_budgets s label a u b hb) (by positivity))

/-- The valid conclusion from the manuscript's original uniform fiber premise. -/
theorem l1_sq_le_uniform_fiber_bound (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u : κ → ℝ) (E H : ℝ)
    (hb : ∀ d ∈ s.image label,
      (∑ i ∈ fiber s label d, (a i - u d) ^ 2) ≤ E ^ 2 * H) :
    (∑ i ∈ s, |a i - u (label i)|) ^ 2 ≤
      s.card * (s.image label).card * (E ^ 2 * H) := by
  simpa [mul_assoc] using
    l1_sq_le_fiber_budgets s label a u (fun _ => E ^ 2 * H) hb

/-- A normalized allocation is a sufficient replacement for equation (136). -/
theorem l1_sq_le_normalized_fiber_budgets (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u b : κ → ℝ) (C H E : ℝ)
    (hcard : (s.card : ℝ) ≤ C * H)
    (hb : ∀ d ∈ s.image label,
      (∑ i ∈ fiber s label d, (a i - u d) ^ 2) ≤ b d * E ^ 2)
    (htotal : (∑ d ∈ s.image label, b d) ≤ 1) :
    (∑ i ∈ s, |a i - u (label i)|) ^ 2 ≤ C * H * E ^ 2 := by
  apply l1_sq_le_of_total_loss s label a u C H E hcard
  calc
    loss s label a u ≤ ∑ d ∈ s.image label, b d * E ^ 2 :=
      loss_le_fiber_budgets s label a u (fun d => b d * E ^ 2) hb
    _ = (∑ d ∈ s.image label, b d) * E ^ 2 := (Finset.sum_mul ..).symm
    _ ≤ 1 * E ^ 2 := mul_le_mul_of_nonneg_right htotal (sq_nonneg E)
    _ = E ^ 2 := one_mul _

/-- All shell-to-global mean shifts must be charged to the same atom vector. -/
theorem loss_le_of_dispersion_and_bias_budget (s : Finset ι) (label : ι → κ)
    (a : ι → ℝ) (u b : κ → ℝ)
    (hb : ∀ d ∈ s.image label,
      FiniteWeightedVariance.variance (fiber s label d) (fun _ => 1) a +
        (fiber s label d).card * (atomMean s label a d - u d) ^ 2 ≤ b d) :
    loss s label a u ≤ ∑ d ∈ s.image label, b d := by
  rw [loss_eq_pooled_add_bias, pooledDispersion, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum hb

end RiemannResearch.Analysis.FiniteAtomDispersion
