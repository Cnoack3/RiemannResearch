/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusTruncatedCeiling
import RiemannResearch.RH.CanonicalMobiusQuotientCells
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Common-cell lower and upper certificates for truncated inverse-Gram ceilings

Source: user-requested finite-ceiling comparison, October 15, 2026.
The finite certificates retain their complete complementary contributions.
No arithmetic uniform upper provider is asserted.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
namespace CanonicalTruncated
open RiemannResearch.Analysis.TruncatedGramEnvelope
open CoefficientStabilization.SignedCovariance
variable {ι : Type*} [Fintype ι]

theorem residual_combination_quotient (k : ι → ℕ) (α : ι → ℝ) (q n : ℕ)
    (hn : 0 < n) (hα : ∑ i, α i = 1) (hcell : ∀ i, n / (k i + 1) = q) :
    (∑ i, α i * residual k i n) =
      mobiusQuotientProfile q n + (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i) := by
  simp only [residual]
  simp_rw [canonicalMobiusResidual_quotient_identity _ n hn, hcell, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hα, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every complete-energy ceiling dominates every common-cell variance. -/
theorem quotient_variance_le_full_energy (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (α : ι → ℝ) (hα : ∑ i, α i = 1) (t : Finset ℕ) (q : ℕ)
    (ht : ∀ n ∈ t, 0 < n) (hcell : ∀ n ∈ t, ∀ i, n / (k i + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    mobiusQuotientVariance t q ≤ ‖hilbertOne - combination k α‖ ^ 2 := by
  rw [residual_norm_eq k α hα,
    ← (residual_energy_summable k hk α).sum_add_tsum_subtype_compl t]
  have hfinite :
      (∑ n ∈ t, positiveWeight n * (∑ i, α i * residual k i n) ^ 2) =
        mobiusQuotientVariance t q + (∑ n ∈ t, positiveWeight n) *
          (mobiusQuotientMean t q +
            (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i)) ^ 2 := by
    calc
      _ = ∑ n ∈ t, positiveWeight n *
          (mobiusQuotientProfile q n +
            (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [residual_combination_quotient k α q n (ht n hn) hα (hcell n hn)]
      _ = _ := mobiusQuotientProfile_translation_energy t q _ hW
  rw [hfinite]
  have hm := mul_nonneg (Finset.sum_nonneg (s := t) (fun n _ => positiveWeight_nonneg n))
    (sq_nonneg (mobiusQuotientMean t q +
      (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i)))
  have hc : 0 ≤ ∑' n : {n : ℕ // n ∉ t},
      positiveWeight n.val * (∑ i, α i * residual k i n.val) ^ 2 :=
    tsum_nonneg (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
  linarith

/- The finite complement is explicit; no omitted coordinate is declared zero. -/
theorem envelope_common_cell_identity (k : ι → ℕ) (α : ι → ℝ)
    (R : ℕ) (t : Finset ℕ) (q : ℕ) (hα : ∑ i, α i = 1)
    (htR : t ⊆ Finset.range R) (ht : ∀ n ∈ t, 0 < n)
    (hcell : ∀ n ∈ t, ∀ i, n / (k i + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    envelope k R α =
      mobiusQuotientVariance t q + (∑ n ∈ t, positiveWeight n) *
        (mobiusQuotientMean t q +
          (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i)) ^ 2 +
      (∑ n ∈ Finset.range R, if n ∈ t then 0 else
        positiveWeight n * (∑ i, α i * residual k i n) ^ 2) +
      budget k / (R : ℝ) * ∑ i, α i ^ 2 := by
  classical
  have hf : (Finset.range R).filter (fun n => n ∈ t) = t := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨htR h, h⟩⟩
  have hsplit :
      (∑ n ∈ Finset.range R, positiveWeight n * (∑ i, α i * residual k i n) ^ 2) =
      (∑ n ∈ t, positiveWeight n * (∑ i, α i * residual k i n) ^ 2) +
      ∑ n ∈ Finset.range R, if n ∈ t then 0 else
        positiveWeight n * (∑ i, α i * residual k i n) ^ 2 := by
    calc
      _ = ∑ n ∈ Finset.range R,
          ((if n ∈ t then positiveWeight n * (∑ i, α i * residual k i n) ^ 2 else 0) +
           (if n ∈ t then 0 else positiveWeight n * (∑ i, α i * residual k i n) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hnt : n ∈ t <;> simp [hnt]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_filter, hf]
  have hprofile :
      (∑ n ∈ t, positiveWeight n * (∑ i, α i * residual k i n) ^ 2) =
      mobiusQuotientVariance t q + (∑ n ∈ t, positiveWeight n) *
        (mobiusQuotientMean t q +
          (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i)) ^ 2 := by
    calc
      _ = ∑ n ∈ t, positiveWeight n *
          (mobiusQuotientProfile q n +
            (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [residual_combination_quotient k α q n (ht n hn) hα (hcell n hn)]
      _ = _ := mobiusQuotientProfile_translation_energy t q _ hW
  unfold envelope energy
  rw [hsplit, hprofile]

variable [Nonempty ι]
theorem quotient_variance_le_inverseCeiling (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R : ℕ) (hR : 0 < R) (t : Finset ℕ) (q : ℕ)
    (ht : ∀ n ∈ t, 0 < n) (hcell : ∀ n ∈ t, ∀ i, n / (k i + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    mobiusQuotientVariance t q ≤ inverseCeiling k R hR :=
  (quotient_variance_le_full_energy k hk (selectedCoefficients k R hR)
    (selectedCoefficients_sum k R hR) t q ht hcell hW).trans
      (selected_full_residual_le k hk R hR)

/-- A four-term upper certificate, with no arithmetic provider hidden in it. -/
theorem inverseCeiling_le_cell_certificate (k : ι → ℕ) (α : ι → ℝ)
    (R : ℕ) (hR : 0 < R) (t : Finset ℕ) (q : ℕ)
    (hα : ∑ i, α i = 1) (htR : t ⊆ Finset.range R)
    (ht : ∀ n ∈ t, 0 < n) (hcell : ∀ n ∈ t, ∀ i, n / (k i + 1) = q)
    (hW : (∑ n ∈ t, positiveWeight n) ≠ 0) :
    inverseCeiling k R hR ≤
      mobiusQuotientVariance t q + (∑ n ∈ t, positiveWeight n) *
        (mobiusQuotientMean t q +
          (q : ℝ) * ∑ i, α i * mobiusCellOffset (k i)) ^ 2 +
      (∑ n ∈ Finset.range R, if n ∈ t then 0 else
        positiveWeight n * (∑ i, α i * residual k i n) ^ 2) +
      budget k / (R : ℝ) * ∑ i, α i ^ 2 := by
  have h := ceiling_le_energy positiveWeight (residual k) (budget k / (R : ℝ)) R
    (div_pos (budget_pos k) (by exact_mod_cast hR)) positiveWeight_nonneg α hα
  change inverseCeiling k R hR ≤ envelope k R α at h
  rw [envelope_common_cell_identity k α R t q hα htR ht hcell hW] at h
  exact h

end CanonicalTruncated
end RiemannResearch.RH.Pareto
