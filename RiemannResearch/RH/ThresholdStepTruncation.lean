import Mathlib.Analysis.Normed.Group.Tannery
import RiemannResearch.RH.DyadicStepBoundary
import RiemannResearch.RH.NearbyDilationGram

/-!
# Frozen physical step-jump approximants

Source: user-provided DyadicSignedBoundaryAbelVerification20260910(1).md
and the retained DyadicBoundaryFourierResearchNote20260910.md, September 10, 2026.
The present proofs establish the stated bounded continuation targets.

The finite prefix equals the original physical sequence up to the cutoff
and is constant afterward. Its full weighted tail is retained exactly.
Bounded physical sequences have genuine Hilbert-norm convergence.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

def hilbertStepJumpPrefix (f : ThresholdHilbert) (K : ℕ) : ThresholdHilbert :=
  ∑ j ∈ Finset.range K,
    ((hilbertSequence f (j+1) - hilbertSequence f j) / (j+1 : ℝ)) •
      hilbertDilation (j+1) (by positivity) hilbertOne

theorem hilbertStepJumpPrefix_sequence (f : ThresholdHilbert) (K n : ℕ) :
    hilbertSequence (hilbertStepJumpPrefix f K) n = hilbertSequence f (min n K) := by
  induction K with
  | zero => cases n <;> simp [hilbertStepJumpPrefix, hilbertSequence]
  | succ K ih =>
    have hs : hilbertStepJumpPrefix f (K+1) = hilbertStepJumpPrefix f K +
        ((hilbertSequence f (K+1) - hilbertSequence f K) / (K+1 : ℝ)) •
          hilbertDilation (K+1) (by positivity) hilbertOne := by
      exact Finset.sum_range_succ _ _
    rw [hs, hilbertSequence_add, hilbertSequence_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      hilbertDilation_one_sequence, ih]
    by_cases hn : K+1 ≤ n
    · rw [if_pos hn, Nat.min_eq_right (by omega), Nat.min_eq_right hn]
      have hk : (K+1 : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · rw [if_neg hn, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
      ring

theorem hilbertStepJumpPrefix_error_sq (f : ThresholdHilbert) (K : ℕ) :
    ‖hilbertStepJumpPrefix f K - f‖^2 =
      ∑' j : ℕ, positiveWeight (j+(K+1)) *
        (hilbertSequence f K - hilbertSequence f (j+(K+1)))^2 := by
  rw [hilbert_norm_weighted_sq]
  have hs := hilbertSequence_square_summable (hilbertStepJumpPrefix f K - f)
  rw [← hs.sum_add_tsum_nat_add (K+1)]
  have hz : (∑ k ∈ Finset.range (K+1), positiveWeight k *
      hilbertSequence (hilbertStepJumpPrefix f K - f) k ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hilbertSequence_sub]
    simp only [Pi.sub_apply, hilbertStepJumpPrefix_sequence,
      Nat.min_eq_left (by simpa using Finset.mem_range.mp hk), sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  rw [hz, zero_add]
  apply tsum_congr
  intro j
  rw [hilbertSequence_sub]
  simp only [Pi.sub_apply, hilbertStepJumpPrefix_sequence,
    Nat.min_eq_right (by omega : K ≤ j+(K+1))]

theorem hilbertStepJumpPrefix_error_sq_le (f : ThresholdHilbert) (K : ℕ)
    (B : ℝ)
    (hosc : ∀ n, |hilbertSequence f K - hilbertSequence f n| ≤ B) :
    ‖hilbertStepJumpPrefix f K - f‖^2 ≤ B^2 / (K+1 : ℝ) := by
  rw [hilbertStepJumpPrefix_error_sq]
  have hs : Summable (fun j => positiveWeight (j+(K+1)) *
      (hilbertSequence f K - hilbertSequence f (j+(K+1)))^2) := by
    have ht := (hilbertSequence_square_summable
      (hilbertStepJumpPrefix f K - f)).comp_injective
        (fun a b h => Nat.add_right_cancel h : Function.Injective (fun j : ℕ => j+(K+1)))
    apply ht.congr
    intro j
    simp only [Function.comp_apply]
    rw [hilbertSequence_sub]
    simp only [Pi.sub_apply, hilbertStepJumpPrefix_sequence,
      Nat.min_eq_right (by omega : K ≤ j+(K+1))]
  have hm := (positiveWeight_summable.comp_injective
    (fun a b h => Nat.add_right_cancel h : Function.Injective (fun j : ℕ => j+(K+1)))).mul_right (B^2)
  calc
    _ ≤ ∑' j : ℕ, positiveWeight (j+(K+1)) * B^2 := by
      apply Summable.tsum_le_tsum _ hs hm
      intro j
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
      have h := hosc (j+(K+1))
      have hh := mul_self_le_mul_self (abs_nonneg _) h
      simpa only [← pow_two, sq_abs] using hh
    _ = _ := by
      rw [tsum_mul_right, positiveWeight_tail_tsum (K+1) (by omega)]
      push_cast
      ring

open Filter

theorem hilbertStepJumpPrefix_tendsto_of_bounded (f : ThresholdHilbert)
    (B : ℝ) (hbound : ∀ n, |hilbertSequence f n| ≤ B) :
    Tendsto (hilbertStepJumpPrefix f) atTop (nhds f) := by
  have hlim : Tendsto (fun K => ‖hilbertStepJumpPrefix f K - f‖^2)
      atTop (nhds 0) := by
    simp_rw [hilbert_norm_weighted_sq, hilbertSequence_sub]
    simp only [Pi.sub_apply, hilbertStepJumpPrefix_sequence]
    have hs := positiveWeight_summable.mul_right ((2*B)^2)
    have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hs
      (f := fun K k => positiveWeight k *
        (hilbertSequence f (min k K) - hilbertSequence f k)^2)
      (g := fun _ => (0 : ℝ))
    have hpoint : ∀ k, Tendsto (fun K => positiveWeight k *
        (hilbertSequence f (min k K) - hilbertSequence f k)^2) atTop (nhds 0) := by
      intro k
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop k] with K hK
      simp [Nat.min_eq_left hK]
    have hmajor : ∀ᶠ K in atTop, ∀ k,
        ‖positiveWeight k * (hilbertSequence f (min k K) - hilbertSequence f k)^2‖ ≤
          positiveWeight k * (2*B)^2 := by
      apply Eventually.of_forall
      intro K k
      have hd : |hilbertSequence f (min k K) - hilbertSequence f k| ≤ 2*B := by
        calc
          _ ≤ |hilbertSequence f (min k K)| + |hilbertSequence f k| := abs_sub _ _
          _ ≤ 2*B := by linarith [hbound (min k K), hbound k]
      have hd2 := mul_self_le_mul_self (abs_nonneg _) hd
      have hs2 : (hilbertSequence f (min k K) - hilbertSequence f k)^2 ≤ (2*B)^2 := by
        simpa only [← pow_two, sq_abs] using hd2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left hs2 (positiveWeight_nonneg k)
    simpa only [tsum_zero] using hdom hpoint hmajor
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hlim.sqrt

end
end RiemannResearch.RH.Pareto
